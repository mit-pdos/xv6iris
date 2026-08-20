(* ProofReadi.v -- readi over the SIE-agnostic sconf world.

     int readi(struct inode *ip, int user_dst, uint64 dst, uint off, uint n)
     {
       uint tot, m;  struct buf *bp;
       if(off > ip->size || off + n < off)  return 0;
       if(off + n > ip->size)               n = ip->size - off;
       for(tot = 0; tot < n; tot += m, off += m, dst += m){
         uint addr = bmap(ip, off/BSIZE);
         if(addr == 0) break;
         bp = bread(ip->dev, addr);
         m = min(n - tot, BSIZE - off%BSIZE);
         if(either_copyout(user_dst, dst, bp->data + (off % BSIZE), m) == -1) {
           brelse(bp);  tot = -1;  break; }
         brelse(bp);
       }
       return tot;
     }

   ===================================================================
   THE SHAPE OF THE PROOF.  Five lemmas, entered right to left in the
   file and left to right at run time:

     rd_ret   +0xdc .. +0xec   pop the seven unconditionally-saved
                               registers, ret, discharge the contract.
     rd_join  +0xd8 .. +0xda   a0 := s3, restore s3.  THREE paths join
                               here (both loop exits and the n = 0 arm).
     rd_exit  <five pops> + <c.j +0xd8>, PARAMETERISED BY ITS PCs --
                               gcc emitted this block twice (+0xb2 and
                               +0xbe) and it is one lemma, per
                               claude-notes/durable-notes.md's
                               "a code block gcc emitted twice" recipe.
     rd_loop  +0x7c head, +0x4c body, +0xaa failure tail.  Fuel
                               induction on the straddled-block count.
     wp_readi_sconf            +0x00 .. +0x4a, the PRE-FRAME exit at
                               +0xee, the clamp and the n = 0 arm.

   EVERY CALLEE-SAVED REGISTER IS SAVED (ra + s0..s11 in a 112-byte,
   14-slot frame), so there is no register-threading invariant at all:
   [callee_saved m mf] falls out of the thirteen restores plus the
   [addi sp,sp,112].  What replaces it is the frame in three strengths --
   [rd_fr7] (the seven unconditional slots pinned: ra/s0/s1/s4..s7),
   [rd_fr8] (s3's slot too, after +0x02a) and [rd_fr13] (all thirteen,
   inside the loop).  bmap's s4 lesson applies verbatim: every restore
   precedes the join at +0xd8.

   TWO ARMS ARE DEAD, and both are dead by a PREMISE rather than by code:
     - +0x026 [bltu a4,a3], xv6's [off + n < off] overflow test, by the
       joint numeric premise (SpecReadi.v);
     - +0x088 [c.beqz a0], the "bmap found no block" break, by
       [bm_covers] -- which is the whole reason readi can call
       BMAP_NOALLOC and stay out of the log.  Its target (+0xce..+0xd6,
       a third copy of the five pops) is therefore unreachable and never
       proved.

   THE COUPLING THAT MAKES THE LOOP WORK is [rd_held_content]: the
   block's own [fsblock] half, borrowed out of [inode_blocks] with
   [inode_blocks_acc], against the bio handle's machinery half pins the
   buffer's bytes to [data fbn].  either_copyout then reads exactly the
   window [o, o+m) of that list, so the byte it delivered at destination
   index [tot+jj] IS [file_byte data (off+tot+jj)]
   ([ProofReadiParts.rd_deliver_mid]).  The buffer is handed back
   UNCHANGED, which is what re-forms the [bio_locked] brelse wants -- no
   log_write is involved anywhere. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import CodeReadi.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import SpecBmap SpecBread SpecBrelse SpecEitherCopyout.
Require Import ProofReadiParts.
Require Import SpecReadi.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

Module ReadiProof (BM : BMAP_NOALLOC) (BR : BREAD) (BL : BRELSE)
                  (EC : EITHER_COPYOUT) : READI.

Notation RI := KernelSyms.readi.

Notation Rra  := (mword_of_int 1  : mword 5).
Notation Rs0  := (mword_of_int 8  : mword 5).
Notation Rs1  := (mword_of_int 9  : mword 5).
Notation Rs2  := (mword_of_int 18 : mword 5).
Notation Rs3  := (mword_of_int 19 : mword 5).
Notation Rs4  := (mword_of_int 20 : mword 5).
Notation Rs5  := (mword_of_int 21 : mword 5).
Notation Rs6  := (mword_of_int 22 : mword 5).
Notation Rs7  := (mword_of_int 23 : mword 5).
Notation Rs8  := (mword_of_int 24 : mword 5).
Notation Rs9  := (mword_of_int 25 : mword 5).
Notation Rs10 := (mword_of_int 26 : mword 5).
Notation Rs11 := (mword_of_int 27 : mword 5).
Notation Ra0  := (mword_of_int 10 : mword 5).
Notation Ra1  := (mword_of_int 11 : mword 5).
Notation Ra2  := (mword_of_int 12 : mword 5).
Notation Ra3  := (mword_of_int 13 : mword 5).
Notation Ra4  := (mword_of_int 14 : mword 5).
Notation Ra5  := (mword_of_int 15 : mword 5).

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

(* ===================================================================== *)
(*  Vocabulary: the frame in three strengths, and the continuation.       *)
(* ===================================================================== *)
Section ReadiDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  (* readi's 112-byte frame.  Slot k sits at [sp0 - 8k], i.e. at
     [sp_new + (112 - 8k)]:
       1 ra@104   2 s0@96   3 s1@88   4 s2@80   5 s3@72   6 s4@64
       7 s5@56    8 s6@48   9 s7@40  10 s8@32  11 s9@24  12 s10@16
      13 s11@8   14 (offset 0, never written)                          *)

  (* the SEVEN unconditional saves (+0x008..+0x014), which is all the
     return block may assume. *)
  Definition rd_fr7 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] v) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈[KT1] v))%I.

  (* ...plus s3's slot, pinned from +0x02a to the [c.ldsp s3] at +0xda *)
  Definition rd_fr8 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] v) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈[KT1] v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈[KT1] v))%I.

  (* ...and all thirteen, which is what the loop holds (+0x038..+0x040) *)
  Definition rd_fr13 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈[KT1] (m !!! Regidx Rs8 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈[KT1] (m !!! Regidx Rs9 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈[KT1] (m !!! Regidx Rs10 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈[KT1] (m !!! Regidx Rs11 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈[KT1] v))%I.

  (* THE DESTINATION AND THE PID SHARE THAT RIDES WITH IT -- SpecReadi's
     [if user then … else …] premise, named once.

     THE PID FRACTION IS THE KERNEL ARM'S.  On the user arm readi holds the
     whole [proc_priv] block instead and BORROWS the quarter out of it at
     each of bmap/bread/brelse ([rd_dst_pid] below, over
     [ProcInv.proc_priv_pid]); it has to, because that accessor consumes the
     block and returns a wand, so nobody can hold both at once.  The three
     bio callees take the fraction at a universally quantified dfrac, which
     is what makes one borrow serve both arms ([rd_q]); either_copyout takes
     the block and never the fraction, so the borrow is always closed before
     the copy. *)
  Definition rd_dst (γf : gname) (j : nat) (pidv : mword 32) (dq : dfrac)
      (user : bool) (Vc : pprivate) (dstb : mword 64) (n : nat)
      (bytes : nat -> bv 8) : iProp Σ :=
    (if user
     then proc_priv_core (proc_addr j) pidv Vc
     else ([∗ list] i ∈ seq 0 n, pa_add dstb i ↦ₘ[ktb] bytes i) ∗
          p_pid (proc_addr j) ↦₄{dq} pidv)%I.

  (* the dfrac the borrowed share carries: [proc_priv]'s own quarter on the
     user arm, the caller's whole share on the kernel one *)
  Definition rd_q (user : bool) (dq : dfrac) : dfrac :=
    if user then DfracOwn (1/4) else dq.

  Lemma rd_dst_pid (γf : gname) (j : nat) (pidv : mword 32) (dq : dfrac)
      (user : bool) (Vc : pprivate) (dstb : mword 64) (n : nat)
      (bytes : nat -> bv 8) :
    rd_dst γf j pidv dq user Vc dstb n bytes -∗
      p_pid (proc_addr j) ↦₄{rd_q user dq} pidv ∗
      (p_pid (proc_addr j) ↦₄{rd_q user dq} pidv -∗
         rd_dst γf j pidv dq user Vc dstb n bytes).
  Proof.
    rewrite /rd_dst /rd_q. destruct user.
    - iIntros "Hp". iDestruct (proc_priv_core_pid with "Hp") as "[Hq Hback]".
      iSplitL "Hq"; [iExact "Hq"|]. iIntros "Hq". iApply ("Hback" with "Hq").
    - iIntros "Hd". iDestruct "Hd" as "[Hb Hq]". iSplitL "Hq"; [iExact "Hq"|].
      iIntros "Hq". iSplitL "Hb"; [iExact "Hb"|]. iExact "Hq".
  Qed.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition rd_cont `{GEN : GenId} `{CID0 : CpuId}
      (γfs : fs_names) (bn : bio_names) (γf : gname) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (dn : dinode)
      (user : bool) (off n : nat) (dst_olds : nat -> bv 8)
      (V : pprivate)
      (pidv : mword 32) (dq dqd : dfrac) (j : nat)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (tot : nat) (P' : uptd),
        ⌜callee_saved m mf⌝ -∗
        ⌜uptd_ext (pv_upt V) P'⌝ -∗
        ⌜(tot <= rd_clamp (di_size dn) off n)%nat⌝ -∗
        ⌜(mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64) /\ user = true)
         \/ (mf !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)
             /\ tot = rd_clamp (di_size dn) off n)⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        i_dev ip ↦₄{dqd} dev -∗
        inode_meta ip dn -∗
        inode_map γfs ip bm -∗
        inode_blocks γfs bm data -∗
        rd_dst γf j pidv dq user (upd_upt V P')
               (m !!! Regidx Ra2 : mword 64) n
               (rd_delivered data dst_olds off tot) -∗
        bslot bn -∗
        WP (Loop : expr riscv_lang))%I.

End ReadiDefs.

(* the sp relation: inside the frame sp is 112 below its entry value *)
Definition rd_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))).

(* ===================================================================== *)
(*  +0xdc .. +0xec : THE RETURN.                                          *)
(* ===================================================================== *)
Section ReadiRet.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Lemma rd_ret `{GEN : GenId} `{CID0 : CpuId} 
      (γfs : fs_names) (bn : bio_names) (γf : gname) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (dn : dinode)
      (user : bool) (off n tot : nat) (dst_olds : nat -> bv 8)
      (V : pprivate) (P' : uptd)
      (pidv : mword 32) (dq dqd : dfrac) (j : nat)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    (K_readi <= K)%nat ->
    rd_sp m M ->
    (* the six registers this block does NOT restore are already back *)
    M !!! Regidx Rs2  = (m !!! Regidx Rs2  : mword 64) ->
    M !!! Regidx Rs3  = (m !!! Regidx Rs3  : mword 64) ->
    M !!! Regidx Rs8  = (m !!! Regidx Rs8  : mword 64) ->
    M !!! Regidx Rs9  = (m !!! Regidx Rs9  : mword 64) ->
    M !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64) ->
    M !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64) ->
    uptd_ext (pv_upt V) P' ->
    (tot <= rd_clamp (di_size dn) off n)%nat ->
    ((M !!! Regidx Ra0 = (mword_of_int (-1) : mword 64) /\ user = true)
     \/ (M !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)
         /\ tot = rd_clamp (di_size dn) off n)) ->
    sie_cap_gpr KT1 M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (RI + 0xdc) : mword 64) -∗
    rd_fr7 m -∗
    i_dev ip ↦₄{dqd} dev -∗
    inode_meta ip dn -∗
    inode_map γfs ip bm -∗
    inode_blocks γfs bm data -∗
    rd_dst (ktb := ktb) γf j pidv dq user (upd_upt V P')
           (m !!! Regidx Ra2 : mword 64) n
           (rd_delivered data dst_olds off tot) -∗
    bslot bn -∗
    rd_cont (ktb := ktb) (CID0 := CID0) γfs bn γf dev ip bm data dn user off n dst_olds V
            pidv dq dqd j m K eb b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hs2 Hs3 Hs8 Hs9 Hs10 Hs11 Hext Htotle Harm.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc Hframe Hidev
              Hmeta Hmap Hblocks Hdst Hsl Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb2b. cbn in Heb2b.
    iPoseProof (rdi_0dc with "Htext") as "Hidc".
    iPoseProof (rdi_0de with "Htext") as "Hide".
    iPoseProof (rdi_0e0 with "Htext") as "Hie0".
    iPoseProof (rdi_0e2 with "Htext") as "Hie2".
    iPoseProof (rdi_0e4 with "Htext") as "Hie4".
    iPoseProof (rdi_0e6 with "Htext") as "Hie6".
    iPoseProof (rdi_0e8 with "Htext") as "Hie8".
    iPoseProof (rdi_0ea with "Htext") as "Hiea".
    iPoseProof (rdi_0ec with "Htext") as "Hiec".
    rewrite /rd_fr7.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc7 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc8 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc9 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    (* ===== +0xdc c.ldsp ra,104(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0xdc)) (mword_of_int 13 : mword 6) Rra
              M (K - 14)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hidc [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1sp : rd_sp m P1)
      by (rewrite /rd_sp /P1 upd_ne; [exact Hsp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xdc) : mword 64) 2
                  = mword_of_int (RI + 0xde)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xde c.ldsp s0,96(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0xde)) (mword_of_int 12 : mword 6) Rs0
              P1 (K - 14)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hide [Hf2]").
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : rd_sp m P2)
      by (rewrite /rd_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xde) : mword 64) 2
                  = mword_of_int (RI + 0xe0)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe0 c.ldsp s1,88(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0xe0)) (mword_of_int 11 : mword 6) Rs1
              P2 (K - 14)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie0 [Hf3]").
    { iEval (rewrite HP2sp -Hsp Hc3). iExact "Hf3". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -Hsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : rd_sp m P3)
      by (rewrite /rd_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xe0) : mword 64) 2
                  = mword_of_int (RI + 0xe2)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe2 c.ldsp s4,64(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0xe2)) (mword_of_int 8 : mword 6) Rs4
              P3 (K - 14)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie2 [Hf6]").
    { iEval (rewrite HP3sp -Hsp Hc6). iExact "Hf6". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf6".
    iEval (rewrite HP3sp -Hsp Hc6) in "Hf6".
    set (P4 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P3).
    assert (HP4sp : rd_sp m P4)
      by (rewrite /rd_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xe2) : mword 64) 2
                  = mword_of_int (RI + 0xe4)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe4 c.ldsp s5,56(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0xe4)) (mword_of_int 7 : mword 6) Rs5
              P4 (K - 14)%nat (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie4 [Hf7]").
    { iEval (rewrite HP4sp -Hsp Hc7). iExact "Hf7". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf7".
    iEval (rewrite HP4sp -Hsp Hc7) in "Hf7".
    set (P5 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P4).
    assert (HP5sp : rd_sp m P5)
      by (rewrite /rd_sp /P5 upd_ne; [exact HP4sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xe4) : mword 64) 2
                  = mword_of_int (RI + 0xe6)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe6 c.ldsp s6,48(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0xe6)) (mword_of_int 6 : mword 6) Rs6
              P5 (K - 14)%nat (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie6 [Hf8]").
    { iEval (rewrite HP5sp -Hsp Hc8). iExact "Hf8". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf8".
    iEval (rewrite HP5sp -Hsp Hc8) in "Hf8".
    set (P6 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P5).
    assert (HP6sp : rd_sp m P6)
      by (rewrite /rd_sp /P6 upd_ne; [exact HP5sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xe6) : mword 64) 2
                  = mword_of_int (RI + 0xe8)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe8 c.ldsp s7,40(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0xe8)) (mword_of_int 5 : mword 6) Rs7
              P6 (K - 14)%nat (m !!! Regidx Rs7 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie8 [Hf9]").
    { iEval (rewrite HP6sp -Hsp Hc9). iExact "Hf9". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf9".
    iEval (rewrite HP6sp -Hsp Hc9) in "Hf9".
    set (P7 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> P6).
    assert (HP7sp : rd_sp m P7)
      by (rewrite /rd_sp /P7 upd_ne; [exact HP6sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xe8) : mword 64) 2
                  = mword_of_int (RI + 0xea)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xea c.addi16sp sp,112 : pop ===== *)
    assert (Hwv : add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP7sp. apply bv_eq.
      rewrite !add_vec64_unsigned bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6)) : mword 64)
                   = 18446744073709551504) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6)) : mword 64)
                    = 112) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551504 + 112)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0) by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P7 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6)))) 14).
    { rewrite Hwv HP7sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 14)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1"|].
      iSplitL "Hf2"; [iExists _; iExact "Hf2"|].
      iSplitL "Hf3"; [iExists _; iExact "Hf3"|].
      iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|].
      iSplitL "Hf6"; [iExists _; iExact "Hf6"|].
      iSplitL "Hf7"; [iExists _; iExact "Hf7"|].
      iSplitL "Hf8"; [iExists _; iExact "Hf8"|].
      iSplitL "Hf9"; [iExists _; iExact "Hf9"|].
      iSplitL "HfA"; [iExact "HfA"|].
      iSplitL "HfB"; [iExact "HfB"|].
      iSplitL "HfC"; [iExact "HfC"|].
      iSplitL "HfD"; [iExact "HfD"|].
      iSplitL "HfE"; [iExact "HfE"|].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (RI + 0xea))
              (mword_of_int 7 : mword 6) P7 (K - 14)%nat 14 b Hpop
              with "Hcg Hpc Hiea Hstk").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (P8 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6))))]> P7).
    assert (Hnk : ((K - 14) + 14)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xea) : mword 64) 2
                  = mword_of_int (RI + 0xec)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xec c.ret ===== *)
    assert (HP8ra : P8 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (RI + 0xec)) Rra P8 K b ltac:(nz)
              with "Hcg Hpc Hiec").
    iIntros (CID9 Hq9) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P8 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP8ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P8 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P8 upd_eq; exact Hwv).
    assert (Cs0 : P8 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P8 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    assert (Cs4 : P8 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_eq. reflexivity. }
    assert (Cs5 : P8 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_eq. reflexivity. }
    assert (Cs6 : P8 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_eq. reflexivity. }
    assert (Cs7 : P8 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_eq. reflexivity. }
    assert (Cother : forall c : mword 5,
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> c <> Rs5 ->
              c <> Rs6 -> c <> Rs7 -> c <> Rra ->
              P8 !!! Regidx c = (M !!! Regidx c : mword 64)).
    { intros c N2 N8 N9 N20 N21 N22 N23 N1.
      rewrite /P8 upd_ne; [| congruence]. rewrite /P7 upd_ne; [| congruence].
      rewrite /P6 upd_ne; [| congruence]. rewrite /P5 upd_ne; [| congruence].
      rewrite /P4 upd_ne; [| congruence]. rewrite /P3 upd_ne; [| congruence].
      rewrite /P2 upd_ne; [| congruence]. rewrite /P1 upd_ne; [| congruence].
      reflexivity. }
    assert (Cs2 : P8 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (Cother Rs2); [exact Hs2 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs3 : P8 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (Cother Rs3); [exact Hs3 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs8 : P8 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64)).
    { rewrite (Cother Rs8); [exact Hs8 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs9 : P8 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64)).
    { rewrite (Cother Rs9); [exact Hs9 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs10 : P8 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64)).
    { rewrite (Cother Rs10); [exact Hs10 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Cs11 : P8 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64)).
    { rewrite (Cother Rs11); [exact Hs11 | nz | nz | nz | nz | nz | nz | nz | nz]. }
    assert (Ca0 : P8 !!! Regidx Ra0 = (M !!! Regidx Ra0 : mword 64)).
    { rewrite (Cother Ra0); [reflexivity | nz | nz | nz | nz | nz | nz | nz | nz]. }
   iDestruct (cpu_own_transport CID0 CID9 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID9 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID9 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    rewrite /rd_cont.
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P8 tot P'
              with "[%] [%] [%] [%] Hcg Hcnt Hextc Hextm Hpc Hidev Hmeta Hmap Hblocks Hdst Hsl").
    { unfold callee_saved. split_and!; assumption. }
    { exact Hext. }
    { exact Htotle. }
    { rewrite Ca0. exact Harm. }
  Qed.

End ReadiRet.

(* ===================================================================== *)
(*  +0xd8 .. +0xda : a0 := s3, restore s3.  THREE PATHS JOIN HERE.        *)
(* ===================================================================== *)
Section ReadiJoin.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Lemma rd_join `{GEN : GenId} `{CID0 : CpuId} 
      (γfs : fs_names) (bn : bio_names) (γf : gname) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (dn : dinode)
      (user : bool) (off n tot : nat) (dst_olds : nat -> bv 8)
      (V : pprivate) (P' : uptd) (ans : mword 64)
      (pidv : mword 32) (dq dqd : dfrac) (j : nat)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    (K_readi <= K)%nat ->
    rd_sp m M ->
    M !!! Regidx Rs3 = ans ->
    M !!! Regidx Rs2  = (m !!! Regidx Rs2  : mword 64) ->
    M !!! Regidx Rs8  = (m !!! Regidx Rs8  : mword 64) ->
    M !!! Regidx Rs9  = (m !!! Regidx Rs9  : mword 64) ->
    M !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64) ->
    M !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64) ->
    uptd_ext (pv_upt V) P' ->
    (tot <= rd_clamp (di_size dn) off n)%nat ->
    ((ans = (mword_of_int (-1) : mword 64) /\ user = true)
     \/ (ans = (mword_of_int (Z.of_nat tot) : mword 64)
         /\ tot = rd_clamp (di_size dn) off n)) ->
    sie_cap_gpr KT1 M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (RI + 0xd8) : mword 64) -∗
    rd_fr8 m -∗
    i_dev ip ↦₄{dqd} dev -∗
    inode_meta ip dn -∗
    inode_map γfs ip bm -∗
    inode_blocks γfs bm data -∗
    rd_dst (ktb := ktb) γf j pidv dq user (upd_upt V P')
           (m !!! Regidx Ra2 : mword 64) n
           (rd_delivered data dst_olds off tot) -∗
    bslot bn -∗
    rd_cont (ktb := ktb) (CID0 := CID0) γfs bn γf dev ip bm data dn user off n dst_olds V
            pidv dq dqd j m K eb b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hs3v Hs2 Hs8 Hs9 Hs10 Hs11 Hext Htotle Harm.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc Hframe Hidev
              Hmeta Hmap Hblocks Hdst Hsl Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb2b. cbn in Heb2b.
    iPoseProof (rdi_0d8 with "Htext") as "Hid8".
    iPoseProof (rdi_0da with "Htext") as "Hida".
    (* ===== +0xd8 c.mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0xd8)) Ra0 Rs3
              M (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hid8").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs3))]> M).
    assert (HT0a0 : T0 !!! Regidx Ra0 = ans).
    { rewrite /T0 upd_eq. rgne. rewrite Hs3v. apply add_vec_zero_l. }
    assert (HT0sp : rd_sp m T0) by (rewrite /rd_sp /T0 upd_ne; [exact Hsp | nz]).
    assert (HT0s2 : T0 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs2 | nz]).
    assert (HT0s8 : T0 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs8 | nz]).
    assert (HT0s9 : T0 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs9 | nz]).
    assert (HT0s10 : T0 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs10 | nz]).
    assert (HT0s11 : T0 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs11 | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xd8) : mword 64) 2
                  = mword_of_int (RI + 0xda)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xda c.ldsp s3,72(sp) ===== *)
    rewrite /rd_fr8.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    assert (Hc5 : add_vec (T0 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HT0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0xda)) (mword_of_int 9 : mword 6) Rs3
              T0 (K - 14)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hida [Hf5]").
    { iEval (rewrite Hc5). iExact "Hf5". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf5".
    iEval (rewrite Hc5) in "Hf5".
    set (T1 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> T0).
    assert (HT1sp : rd_sp m T1) by (rewrite /rd_sp /T1 upd_ne; [exact HT0sp | nz]).
    assert (HT1s3 : T1 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /T1; apply upd_eq).
    assert (HT1a0 : T1 !!! Regidx Ra0 = ans)
      by (rewrite /T1 upd_ne; [exact HT0a0 | nz]).
    assert (HT1s2 : T1 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s2 | nz]).
    assert (HT1s8 : T1 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s8 | nz]).
    assert (HT1s9 : T1 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s9 | nz]).
    assert (HT1s10 : T1 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s10 | nz]).
    assert (HT1s11 : T1 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s11 | nz]).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xda) : mword 64) 2
                  = mword_of_int (RI + 0xdc)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    iAssert (rd_fr7 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
      as "Hframe".
    { rewrite /rd_fr7.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExists _; iExact "Hf5"|].
      iSplitL "Hf6"; [iExact "Hf6"|]. iSplitL "Hf7"; [iExact "Hf7"|].
      iSplitL "Hf8"; [iExact "Hf8"|]. iSplitL "Hf9"; [iExact "Hf9"|].
      iSplitL "HfA"; [iExact "HfA"|]. iSplitL "HfB"; [iExact "HfB"|].
      iSplitL "HfC"; [iExact "HfC"|]. iSplitL "HfD"; [iExact "HfD"|].
      iExact "HfE". }
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    iApply (rd_ret (CID0 := CID2)  γfs bn γf dev ip bm data dn
              user off n tot dst_olds V P' pidv dq dqd j m T1 K eb b lks
              HK HT1sp HT1s2 HT1s3 HT1s8 HT1s9 HT1s10 HT1s11 Hext Htotle
              ltac:(rewrite HT1a0; exact Harm)
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hidev
                    Hmeta Hmap Hblocks Hdst Hsl [Hcont]").
    iApply (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID2) ltac:(wp_next_chain)
              with "Hcont").
  Qed.

End ReadiJoin.

(* ===================================================================== *)
(*  THE FIVE-POP BLOCK, emitted twice (+0xb2 and +0xbe) and proved once.  *)
(*  Parameterised by its own pcs as literals -- never by an entry offset  *)
(*  plus arithmetic (claude-notes/durable-notes.md).                      *)
(* ===================================================================== *)
Section ReadiExit.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Lemma rd_exit `{GEN : GenId} `{CID0 : CpuId} 
      (γfs : fs_names) (bn : bio_names) (γf : gname) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (dn : dinode)
      (user : bool) (off n tot : nat) (dst_olds : nat -> bv 8)
      (V : pprivate) (P' : uptd) (ans : mword 64)
      (pidv : mword 32) (dq dqd : dfrac) (j : nat)
      (za zb zc zd ze zf : Z) (jimm : mword 21)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    (K_readi <= K)%nat ->
    rd_sp m M ->
    M !!! Regidx Rs3 = ans ->
    uptd_ext (pv_upt V) P' ->
    (tot <= rd_clamp (di_size dn) off n)%nat ->
    ((ans = (mword_of_int (-1) : mword 64) /\ user = true)
     \/ (ans = (mword_of_int (Z.of_nat tot) : mword 64)
         /\ tot = rd_clamp (di_size dn) off n)) ->
    (* the block's own pc chain, as LITERALS *)
    add_vec_int (mword_of_int za : mword 64) 2 = mword_of_int zb ->
    add_vec_int (mword_of_int zb : mword 64) 2 = mword_of_int zc ->
    add_vec_int (mword_of_int zc : mword 64) 2 = mword_of_int zd ->
    add_vec_int (mword_of_int zd : mword 64) 2 = mword_of_int ze ->
    add_vec_int (mword_of_int ze : mword 64) 2 = mword_of_int zf ->
    add_vec (mword_of_int zf : mword 64) (sign_extend' 64 jimm)
      = (mword_of_int (RI + 0xd8) : mword 64) ->
    eq_vec (access_vec_dec
              (add_vec (mword_of_int zf : mword 64) (sign_extend' 64 jimm)) 0)
      ('b"0") = true ->
    sie_cap_gpr KT1 M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int za : mword 64) -∗
    instr (mword_of_int za : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")),
             sp, Regidx Rs2, false, 8)) -∗
    instr (mword_of_int zb : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")),
             sp, Regidx Rs8, false, 8)) -∗
    instr (mword_of_int zc : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")),
             sp, Regidx Rs9, false, 8)) -∗
    instr (mword_of_int zd : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")),
             sp, Regidx Rs10, false, 8)) -∗
    instr (mword_of_int ze : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")),
             sp, Regidx Rs11, false, 8)) -∗
    instr (mword_of_int zf : mword 64) true (JAL (jimm, zreg)) -∗
    rd_fr13 m -∗
    i_dev ip ↦₄{dqd} dev -∗
    inode_meta ip dn -∗
    inode_map γfs ip bm -∗
    inode_blocks γfs bm data -∗
    rd_dst (ktb := ktb) γf j pidv dq user (upd_upt V P')
           (m !!! Regidx Ra2 : mword 64) n
           (rd_delivered data dst_olds off tot) -∗
    bslot bn -∗
    rd_cont (ktb := ktb) (CID0 := CID0) γfs bn γf dev ip bm data dn user off n dst_olds V
            pidv dq dqd j m K eb b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hs3v Hext Htotle Harm Hab Hbc Hcd Hde Hef Htgt Hal.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc Hia Hib Hic Hid Hie Hif Hframe
              Hidev Hmeta Hmap Hblocks Hdst Hsl Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb2b. cbn in Heb2b.
    rewrite /rd_fr13.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    (* ===== c.ldsp s2,80(sp) ===== *)
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int za) (mword_of_int 10 : mword 6) Rs2
              M (K - 14)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hia [Hf4]").
    { iEval (rewrite Hc4). iExact "Hf4". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf4".
    iEval (rewrite Hc4) in "Hf4".
    set (Q1 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> M).
    assert (HQ1sp : rd_sp m Q1) by (rewrite /rd_sp /Q1 upd_ne; [exact Hsp | nz]).
    assert (HQ1s3 : Q1 !!! Regidx Rs3 = ans)
      by (rewrite /Q1 upd_ne; [exact Hs3v | nz]).
    assert (HQ1s2 : Q1 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /Q1; apply upd_eq).
    iEval (rewrite Hab) in "Hpc".
    (* ===== c.ldsp s8,32(sp) ===== *)
    assert (Hc10 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite HQ1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int zb) (mword_of_int 4 : mword 6) Rs8
              Q1 (K - 14)%nat (m !!! Regidx Rs8 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib [HfA]").
    { iEval (rewrite Hc10). iExact "HfA". }
    iIntros (CID2 Hq2) "Hcg Hpc HfA".
    iEval (rewrite Hc10) in "HfA".
    set (Q2 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> Q1).
    assert (HQ2sp : rd_sp m Q2) by (rewrite /rd_sp /Q2 upd_ne; [exact HQ1sp | nz]).
    assert (HQ2s3 : Q2 !!! Regidx Rs3 = ans)
      by (rewrite /Q2 upd_ne; [exact HQ1s3 | nz]).
    assert (HQ2s2 : Q2 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /Q2 upd_ne; [exact HQ1s2 | nz]).
    assert (HQ2s8 : Q2 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /Q2; apply upd_eq).
    iEval (rewrite Hbc) in "Hpc".
    (* ===== c.ldsp s9,24(sp) ===== *)
    assert (Hc11 : add_vec (Q2 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 11).
    { rewrite HQ2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int zc) (mword_of_int 3 : mword 6) Rs9
              Q2 (K - 14)%nat (m !!! Regidx Rs9 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hic [HfB]").
    { iEval (rewrite Hc11). iExact "HfB". }
    iIntros (CID3 Hq3) "Hcg Hpc HfB".
    iEval (rewrite Hc11) in "HfB".
    set (Q3 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9 : mword 64)]> Q2).
    assert (HQ3sp : rd_sp m Q3) by (rewrite /rd_sp /Q3 upd_ne; [exact HQ2sp | nz]).
    assert (HQ3s3 : Q3 !!! Regidx Rs3 = ans)
      by (rewrite /Q3 upd_ne; [exact HQ2s3 | nz]).
    assert (HQ3s2 : Q3 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /Q3 upd_ne; [exact HQ2s2 | nz]).
    assert (HQ3s8 : Q3 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /Q3 upd_ne; [exact HQ2s8 | nz]).
    assert (HQ3s9 : Q3 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /Q3; apply upd_eq).
    iEval (rewrite Hcd) in "Hpc".
    (* ===== c.ldsp s10,16(sp) ===== *)
    assert (Hc12 : add_vec (Q3 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12).
    { rewrite HQ3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int zd) (mword_of_int 2 : mword 6) Rs10
              Q3 (K - 14)%nat (m !!! Regidx Rs10 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid [HfC]").
    { iEval (rewrite Hc12). iExact "HfC". }
    iIntros (CID4 Hq4) "Hcg Hpc HfC".
    iEval (rewrite Hc12) in "HfC".
    set (Q4 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10 : mword 64)]> Q3).
    assert (HQ4sp : rd_sp m Q4) by (rewrite /rd_sp /Q4 upd_ne; [exact HQ3sp | nz]).
    assert (HQ4s3 : Q4 !!! Regidx Rs3 = ans)
      by (rewrite /Q4 upd_ne; [exact HQ3s3 | nz]).
    assert (HQ4s2 : Q4 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /Q4 upd_ne; [exact HQ3s2 | nz]).
    assert (HQ4s8 : Q4 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /Q4 upd_ne; [exact HQ3s8 | nz]).
    assert (HQ4s9 : Q4 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /Q4 upd_ne; [exact HQ3s9 | nz]).
    assert (HQ4s10 : Q4 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /Q4; apply upd_eq).
    iEval (rewrite Hde) in "Hpc".
    (* ===== c.ldsp s11,8(sp) ===== *)
    assert (Hc13 : add_vec (Q4 !!! Regidx csp_rs1 : mword 64)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk (m !!! Regidx csp_rs1 : mword 64) 13).
    { rewrite HQ4sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int ze) (mword_of_int 1 : mword 6) Rs11
              Q4 (K - 14)%nat (m !!! Regidx Rs11 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie [HfD]").
    { iEval (rewrite Hc13). iExact "HfD". }
    iIntros (CID5 Hq5) "Hcg Hpc HfD".
    iEval (rewrite Hc13) in "HfD".
    set (Q5 := <[Regidx Rs11 := regval_into_reg (m !!! Regidx Rs11 : mword 64)]> Q4).
    assert (HQ5sp : rd_sp m Q5) by (rewrite /rd_sp /Q5 upd_ne; [exact HQ4sp | nz]).
    assert (HQ5s3 : Q5 !!! Regidx Rs3 = ans)
      by (rewrite /Q5 upd_ne; [exact HQ4s3 | nz]).
    assert (HQ5s2 : Q5 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /Q5 upd_ne; [exact HQ4s2 | nz]).
    assert (HQ5s8 : Q5 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /Q5 upd_ne; [exact HQ4s8 | nz]).
    assert (HQ5s9 : Q5 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /Q5 upd_ne; [exact HQ4s9 | nz]).
    assert (HQ5s10 : Q5 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /Q5 upd_ne; [exact HQ4s10 | nz]).
    assert (HQ5s11 : Q5 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /Q5; apply upd_eq).
    iEval (rewrite Hef) in "Hpc".
    (* ===== c.j +0xd8 ===== *)
    iApply (wp_cj_s_sconf (mword_of_int zf) jimm Q5 (K - 14)%nat b Hal
              with "Hcg Hpc Hif").
    iIntros (CID6 Hq6). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt) in "Hpc".
    iAssert (rd_fr8 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
      as "Hframe".
    { rewrite /rd_fr8.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|].
      iSplitL "Hf4"; [iExists _; iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
      iSplitL "Hf9"; [iExact "Hf9"|].
      iSplitL "HfA"; [iExists _; iExact "HfA"|].
      iSplitL "HfB"; [iExists _; iExact "HfB"|].
      iSplitL "HfC"; [iExists _; iExact "HfC"|].
      iSplitL "HfD"; [iExists _; iExact "HfD"|]. iExact "HfE". }
    iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID6 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID6 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    iApply (rd_join (CID0 := CID6)  γfs bn γf dev ip bm data dn
              user off n tot dst_olds V P' ans pidv dq dqd j m Q5 K eb b lks
              HK HQ5sp HQ5s3 HQ5s2 HQ5s8 HQ5s9 HQ5s10 HQ5s11 Hext Htotle Harm
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hidev
                    Hmeta Hmap Hblocks Hdst Hsl [Hcont]").
    iApply (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID6) ltac:(wp_next_chain)
              with "Hcont").
  Qed.

End ReadiExit.

(* ===================================================================== *)
(*  +0x7c (head) / +0x4c (body) : THE LOOP, by induction on FUEL.         *)
(*                                                                        *)
(*  The head runs bmap and bread, computes the chunk length, and joins    *)
(*  the body at +0x4c through an [iAssert] (the two [m = min(...)] arms   *)
(*  differ only in which register the length came from -- ProofCopyin's   *)
(*  CHUNK/BODY pattern: everything linear is BAKED IN, since a case split *)
(*  uses each branch's copy exclusively, and only the register file, the  *)
(*  chunk length and the hart travel as wands).                           *)
(*                                                                        *)
(*  [bm], [data] and [dn] do NOT travel: readi modifies nothing, and      *)
(*  BMAP_NOALLOC hands both bundles back at the same indices.  So the     *)
(*  only moving parts are [tot], the page-table descriptor and the        *)
(*  register file.                                                        *)
(*                                                                        *)
(*  THE FUEL is the number of blocks the remaining range straddles.  An   *)
(*  iteration that does NOT exit filled its block to the boundary, and    *)
(*  [rd_blocks_step] is exactly the decrease that pays for it.            *)
(* ===================================================================== *)
Section ReadiLoop.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Ltac reg_neq := vm_compute; discriminate.

  (* peel a chain of [<[Regidx k := v]>]s down to the fact that names the
     register -- ProofCopyin's [lkp] *)
  Local Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | rgne
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  (* RULE ONE (claude-notes/optimization.md): the +0x4c chunk body both
     arms of [rd_loop]'s [bgeu a3,a4] branch to (a full block copies
     linearly either way) -- named so the walk's proofmode steps stop
     re-embedding ~20 lines of ∀/wands per step.  The ∀ binders stay
     visible at the [iAssert] below; only what they quantify over is
     folded here. *)
  Definition rd_chunk_body `{GEN : GenId}
      (j : nat) (b : bool) (K : nat) (m : regfile) (nc tot o : nat)
      (kkb : nat) (usv ip : mword 64) (off : nat) (CIDa14 : CpuId)
      (CIDb : CpuId) (Mb : regfile) (mm : nat) : iProp Σ :=
    (⌜b = false \/ proc_addr j = zero_reg -> (CIDb : CPU) = (CIDa14 : CPU)⌝ -∗
     ⌜mm = Nat.min (nc - tot) (BSIZE - o)⌝ -∗
     ⌜rd_sp m Mb⌝ -∗
     ⌜Mb !!! Regidx Rs10 = (mword_of_int (Z.of_nat mm) : mword 64)⌝ -∗
     ⌜Mb !!! Regidx Ra5 = (mword_of_int (Z.of_nat o) : mword 64)⌝ -∗
     ⌜Mb !!! Regidx Rs2 = bnode kkb⌝ -∗
     ⌜Mb !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) tot⌝ -∗
     ⌜Mb !!! Regidx Rs7 = usv⌝ -∗
     ⌜Mb !!! Regidx Rs6 = ip⌝ -∗
     ⌜Mb !!! Regidx Rs1 = (mword_of_int (Z.of_nat (off + tot)) : mword 64)⌝ -∗
     ⌜Mb !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64)⌝ -∗
     ⌜Mb !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64)⌝ -∗
     ⌜Mb !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)⌝ -∗
     ⌜Mb !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)⌝ -∗
     sie_cap_gpr KT1 Mb (K - 14)%nat b (proc_addr j) -∗
     pc_is (mword_of_int (RI + 0x4c) : mword 64) -∗
     WP (Loop : expr riscv_lang))%I.

  Local Lemma rd_loop `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (bn : bio_names) (γf γa : gname)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8)) (dn : dinode)
      (user : bool) (off n nc szn : nat) (dst_olds : nat -> bv 8)
      (V : pprivate) (usv : mword 64)
      (pidv : mword 32) (dq dqd : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    (K_readi <= K)%nat ->
    log_geom_ok cov logstart ->
    blkmap_wf cov logstart bm ->
    bm_covers bm (Z.of_nat szn) ->
    (szn <= MAXFILE * BSIZE)%nat ->
    (Z.of_nat off + Z.of_nat n < 2 ^ 32) ->
    (nc <= n)%nat ->
    (off + nc <= szn)%nat ->
    nc = rd_clamp (di_size dn) off n ->
    eq_vec usv zero_reg = negb user ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (* readi's cone: its own bread and brelse both directly acquire
       "bcache" (rank 4) -- see SpecReadi.v. *)
    locks_below lks "bcache" ->
    forall (W tot : nat) (PI : uptd) (M : regfile),
    (tot < nc)%nat ->
    uptd_ext (pv_upt V) PI ->
    (rd_blocks (off + tot) (nc - tot) <= W)%nat ->
    rd_sp m M ->
    M !!! Regidx Rs6 = ip ->
    M !!! Regidx Rs7 = usv ->
    M !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) tot ->
    M !!! Regidx Rs1 = (mword_of_int (Z.of_nat (off + tot)) : mword 64) ->
    M !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64) ->
    M !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64) ->
    M !!! Regidx Rs9 = (mword_of_int 1024 : mword 64) ->
    M !!! Regidx Rs8 = (mword_of_int (-1) : mword 64) ->
    sie_cap_gpr KT1 M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (RI + 0x7c) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    kalloc_env γa None -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    rd_fr13 m -∗
    i_dev ip ↦₄{dqd} dev -∗
    inode_meta ip dn -∗
    inode_map γfs ip bm -∗
    inode_blocks γfs bm data -∗
    rd_dst (ktb := ktb) γf j pidv dq user (upd_upt V PI)
           (m !!! Regidx Ra2 : mword 64) n
           (rd_delivered data dst_olds off tot) -∗
    bslot bn -∗
    rd_cont (ktb := ktb) (CID0 := CID0) γfs bn γf dev ip bm data dn user off n dst_olds V
            pidv dq dqd j m K eb b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hwf Hcov Hszmax Hsum Hncn Hoffnc Hncdef Husv Hj Hgl Hbelow.
    pose proof HK as HK'. 
    change (2 ^ 32)%Z with 4294967296%Z in Hsum.
    assert (Hgeom0 : log_geom_ok cov logstart) by exact Hgeom.
    destruct Hgeom as [Hcovok Hlogsub].
    pose proof Hszmax as Hszmax2.
    rewrite rd_maxfile_val rd_bsize_val in Hszmax2.
    assert (HmbZ : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hbsz : BSIZE = 1024%nat) by exact rd_bsize_val.
    intro W. revert CID0.
    induction W as [| W IH];
      intros CID0 tot PI M Htotlt HextI HW1
             Hsp Hs6 Hs7 Hs4 Hs1 Hs5 Hs3 Hs9 Hs8;
      [ exfalso; pose proof (rd_blocks_pos (off + tot) (nc - tot) ltac:(lia)); lia |].
    remember ((off + tot) `div` BSIZE)%nat as fbn eqn:Hfbne.
    remember ((off + tot) `mod` BSIZE)%nat as o eqn:Hoe.
    assert (Holt : (o < BSIZE)%nat) by (rewrite Hoe; apply rd_mod_lt).
    assert (Hdm : (fbn * BSIZE + o = off + tot)%nat).
    { rewrite Hfbne Hoe. pose proof (rd_divmod (off + tot)). lia. }
    assert (Hcovpair : (fbn < MAXFILE)%nat
                       /\ bv_unsigned (blkmap_get bm fbn) <> 0).
    { destruct (bm_covers_off bm (Z.of_nat szn) (Z.of_nat (off + tot)) Hcov
                  ltac:(lia) ltac:(lia) ltac:(rewrite HmbZ; lia)) as [H1 H2].
      rewrite rd_todiv in H1. rewrite rd_todiv in H2.
      rewrite -Hfbne in H1. rewrite -Hfbne in H2. split; assumption. }
    destruct Hcovpair as [Hfbnlt Hbnzz].
    pose proof Hfbnlt as Hfbn268. rewrite rd_maxfile_val in Hfbn268.
    destruct (blkmap_wf_get_cov cov logstart bm fbn Hwf Hfbnlt Hbnzz)
      as [Hbcov Hblog].
    destruct (Hcovok _ Hbcov) as [Hbpos Hblt].
    change (2 ^ 31)%Z with 2147483648%Z in Hblt.
    assert (Hubno : uint (blkmap_get bm fbn : mword 32)
                    = bv_unsigned (blkmap_get bm fbn)) by apply bb_uint32.
    assert (Hbcov' : uint (blkmap_get bm fbn : mword 32)
                     ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite Hubno; exact Hbcov).
    assert (Hblt' : (uint (blkmap_get bm fbn : mword 32) < 2147483648)%Z)
      by (rewrite Hubno; exact Hblt).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hkenv #Hprocs
              #Hdevi #Hdgeom #Hdlock Hframe Hidev
              Hmeta Hmap Hblocks Hdst Hsl Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb2b. cbn in Heb2b.
    (* BORROW the pid share for bmap and bread; it goes back into [Hdst]
       before either_copyout, which wants the block whole. *)
    iDestruct (rd_dst_pid γf j pidv dq user (upd_upt V PI)
                 (m !!! Regidx Ra2 : mword 64) n
                 (rd_delivered data dst_olds off tot) with "Hdst")
      as "[Hppid Hdstback]".
    iPoseProof (rdi_07c with "Htext") as "Hi7c".
    iPoseProof (rdi_080 with "Htext") as "Hi80".
    iPoseProof (rdi_082 with "Htext") as "Hi82".
    iPoseProof (rdi_086 with "Htext") as "Hi86".
    iPoseProof (rdi_088 with "Htext") as "Hi88".
    (* ===== +0x7c srliw a1,s1,0xa : a1 := off / BSIZE ===== *)
    assert (Hsrlv : sign_extend' 64
                      (shift_bits_right (subrange_vec_dec (rget M Rs1) 31 0 : mword 32)
                         (mword_of_int 10 : mword 5))
                    = (mword_of_int (Z.of_nat fbn) : mword 64)).
    { rgne. rewrite Hs1.
      rewrite (rd_srliw10 (Z.of_nat (off + tot)) ltac:(lia) ltac:(lia)).
      rewrite Hfbne rd_div_z. reflexivity. }
    iApply (wp_srliw_s_sconf (mword_of_int (RI + 0x7c)) Ra1 Rs1
              (mword_of_int 10 : mword 5) (mword_of_int (Z.of_nat fbn) : mword 64)
              M (K - 14)%nat b ltac:(nz) ltac:(rdok) Hsrlv with "Hcg Hpc Hi7c").
    iIntros (CIDa1 Hqa1) "Hcg Hpc".
    set (A1 := <[Regidx Ra1 :=
                 regval_into_reg (mword_of_int (Z.of_nat fbn) : mword 64)]> M).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x7c) : mword 64) 4
                  = mword_of_int (RI + 0x80)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x80 c.mv a0,s6 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x80)) Ra0 Rs6
              A1 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi80").
    iIntros (CIDa2 Hqa2) "Hcg Hpc".
    set (A2 := <[Regidx Ra0 :=
                 regval_into_reg (add_vec (zero_reg : mword 64) (rget A1 Rs6))]> A1).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x80) : mword 64) 2
                  = mword_of_int (RI + 0x82)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x82 jal ra,bmap ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (RI + 0x82)) Rra
              (mword_of_int 2095388 : mword 21) A2 (K - 14)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi82").
    iIntros (CIDa3 Hqa3) "Hcg Hpc".
    set (A3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (RI + 0x82) : mword 64) 4)]> A2).
    assert (Htgtbm : add_vec (mword_of_int (RI + 0x82) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095388 : mword 21))
                     = mword_of_int KernelSyms.bmap) by pcw.
    iEval (rewrite Htgtbm) in "Hpc".
    assert (HA3ra : A3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (RI + 0x82) : mword 64) 4)
      by (rewrite /A3; apply upd_eq).
    assert (HA3a0 : A3 !!! Regidx Ra0 = ip) by lkp.
    assert (HA3a1v : A3 !!! Regidx Ra1 = (mword_of_int (Z.of_nat fbn) : mword 64))
      by lkp.
    assert (HA3a1 : A3 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int (Z.of_nat fbn) : mword 32)).
    { rewrite HA3a1v. symmetry. apply rd_sext32; lia. }
    assert (HA3sp : rd_sp m A3) by (rewrite /rd_sp; lkp).
    assert (HA3s6 : A3 !!! Regidx Rs6 = ip) by lkp.
    assert (HA3s7 : A3 !!! Regidx Rs7 = usv) by lkp.
    assert (HA3s4 : A3 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
    assert (HA3s1 : A3 !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
    assert (HA3s5 : A3 !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64))
      by lkp.
    assert (HA3s3 : A3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by lkp.
    assert (HA3s9 : A3 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
    assert (HA3s8 : A3 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
    iDestruct (cpu_own_transport CID0 CIDa3 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDa3 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDa3 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDa3) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbm : (K_bmap <= K - 14)%nat) by (lia).
    iApply (BM.wp_bmap_noalloc_sconf γs j γl γu γd γk pd pav pu bn γfs
              cov logstart dev ip bm data fbn pidv (rd_q user dq) dqd
              A3 (K - 14)%nat eb b
              _ HKbm Hgeom0 Hfbnlt Hwf Hbnzz Hj Hgl HA3a0 HA3a1
              with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hidev Hmap Hblocks Hppid
                    Hprocs Hdevi Hdgeom Hdlock Hsl").
    all: try lkbelow.
    iIntros (CIDa4 Hqa4 mB)
      "%Hcs1 %Ha0v Hcg Hcnt Hextc Hextm Hpc Hppid Hidev Hmap Hblocks Hsl".
    assert (Hpc86 : ret_pc (A3 !!! Regidx Rra : mword 64)
                    = mword_of_int (RI + 0x86)) by (rewrite HA3ra; pcw).
    iEval (rewrite Hpc86) in "Hpc".
    pose proof Hcs1 as Hcs1c.
    assert (HmBsp : rd_sp m mB).
    { rewrite /rd_sp
        (callee_saved_lookup Hcs1c csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HA3sp. }
    assert (HmBs6 : mB !!! Regidx Rs6 = ip)
      by (rewrite (callee_saved_lookup Hcs1c Rs6 ltac:(vm_compute; reflexivity));
          exact HA3s6).
    assert (HmBs7 : mB !!! Regidx Rs7 = usv)
      by (rewrite (callee_saved_lookup Hcs1c Rs7 ltac:(vm_compute; reflexivity));
          exact HA3s7).
    assert (HmBs4 : mB !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) tot)
      by (rewrite (callee_saved_lookup Hcs1c Rs4 ltac:(vm_compute; reflexivity));
          exact HA3s4).
    assert (HmBs1 : mB !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs1 ltac:(vm_compute; reflexivity));
          exact HA3s1).
    assert (HmBs5 : mB !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs5 ltac:(vm_compute; reflexivity));
          exact HA3s5).
    assert (HmBs3 : mB !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs3 ltac:(vm_compute; reflexivity));
          exact HA3s3).
    assert (HmBs9 : mB !!! Regidx Rs9 = (mword_of_int 1024 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs9 ltac:(vm_compute; reflexivity));
          exact HA3s9).
    assert (HmBs8 : mB !!! Regidx Rs8 = (mword_of_int (-1) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1c Rs8 ltac:(vm_compute; reflexivity));
          exact HA3s8).
    (* ===== +0x86 c.mv a1,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x86)) Ra1 Ra0
              mB (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi86").
    iIntros (CIDa5 Hqa5) "Hcg Hpc".
    set (B1 := <[Regidx Ra1 :=
                 regval_into_reg (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x86) : mword 64) 2
                  = mword_of_int (RI + 0x88)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HB1a0 : B1 !!! Regidx Ra0 = (mB !!! Regidx Ra0 : mword 64)) by lkp.
    assert (HB1sp : rd_sp m B1) by (rewrite /rd_sp; lkp).
    assert (HB1s6 : B1 !!! Regidx Rs6 = ip) by lkp.
    assert (HB1s7 : B1 !!! Regidx Rs7 = usv) by lkp.
    assert (HB1s4 : B1 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
    assert (HB1s1 : B1 !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
    assert (HB1s5 : B1 !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64))
      by lkp.
    assert (HB1s3 : B1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by lkp.
    assert (HB1s9 : B1 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
    assert (HB1s8 : B1 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
    (* ===== +0x88 c.beqz a0 : DEAD -- [bm_covers] says the block exists ===== *)
    assert (Hbeqz : eq_vec (B1 !!! Regidx Ra0) zero_reg = false).
    { rewrite HB1a0 Ha0v. apply rd_sext_nonzero; [exact Hbnzz | exact Hblt]. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (RI + 0x88))
              (mword_of_int 35 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              B1 (K - 14)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; exact Hbeqz) with "Hcg Hpc Hi88").
    iIntros (CIDa6 Hqa6) "Hcg Hpc".
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x88) : mword 64) 2
                  = mword_of_int (RI + 0x8a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    iPoseProof (rdi_08a with "Htext") as "Hi8a".
    iPoseProof (rdi_08e with "Htext") as "Hi8e".
    iPoseProof (rdi_092 with "Htext") as "Hi92".
    iPoseProof (rdi_094 with "Htext") as "Hi94".
    iPoseProof (rdi_098 with "Htext") as "Hi98".
    iPoseProof (rdi_09c with "Htext") as "Hi9c".
    iPoseProof (rdi_0a0 with "Htext") as "Hia0".
    iPoseProof (rdi_0a2 with "Htext") as "Hia2".
    iPoseProof (rdi_0a6 with "Htext") as "Hia6".
    iPoseProof (rdi_0a8 with "Htext") as "Hia8".
    (* ===== +0x8a lw a0,0(s6) : a0 := ip->dev ===== *)
    assert (Hdadr : add_vec (rget B1 Rs6) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = i_dev ip) by (rgne; rewrite HB1s6; reflexivity).
    iEval (rewrite -Hdadr) in "Hidev".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (RI + 0x8a)) Ra0 Rs6
              (mword_of_int 0 : mword 12) B1 (K - 14)%nat dev b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a Hidev").
    iIntros (CIDa7 Hqa7) "Hcg Hpc Hidev".
    iEval (rewrite Hdadr) in "Hidev".
    set (B2 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> B1).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x8a) : mword 64) 4
                  = mword_of_int (RI + 0x8e)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x8e jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (RI + 0x8e)) Rra
              (mword_of_int 2094336 : mword 21) B2 (K - 14)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi8e").
    iIntros (CIDa8 Hqa8) "Hcg Hpc".
    set (B3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (RI + 0x8e) : mword 64) 4)]> B2).
    assert (Htgtbr : add_vec (mword_of_int (RI + 0x8e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094336 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HB3ra : B3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (RI + 0x8e) : mword 64) 4)
      by (rewrite /B3; apply upd_eq).
    assert (HB3a0 : B3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)) by lkp.
    assert (HB3a1 : B3 !!! Regidx Ra1
                    = (sign_extend' 64 (blkmap_get bm fbn : mword 32) : mword 64)).
    { rewrite (_ : B3 !!! Regidx Ra1 = (mB !!! Regidx Ra0 : mword 64));
        [exact Ha0v | lkp]. }
    assert (HB3sp : rd_sp m B3) by (rewrite /rd_sp; lkp).
    assert (HB3s6 : B3 !!! Regidx Rs6 = ip) by lkp.
    assert (HB3s7 : B3 !!! Regidx Rs7 = usv) by lkp.
    assert (HB3s4 : B3 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
    assert (HB3s1 : B3 !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
    assert (HB3s5 : B3 !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64))
      by lkp.
    assert (HB3s3 : B3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by lkp.
    assert (HB3s9 : B3 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
    assert (HB3s8 : B3 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
    iDestruct (cpu_own_transport CIDa4 CIDa8 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDa4 CIDa8 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDa4 CIDa8 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    assert (HKbr : (K_bread <= K - 14)%nat) by (lia).
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev (blkmap_get bm fbn)
              (rd_q user dq)
              B3 (K - 14)%nat eb b lks
              HKbr Hblt' eq_refl Hbcov'
              eq_refl Hj Hgl HB3a0 HB3a1 Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hppid Hprocs Hdevi Hdgeom Hdlock Hsl").
    all: try lkbelow.
    iIntros (CIDa9 Hqa9 mBr kkb bsB bsdB dB)
      "%Hfacts Hcg Hcnt Hextc Hextm Hpc Hppid Hheld".
    (* the borrow closes: either_copyout wants the block whole *)
    iDestruct ("Hdstback" with "Hppid") as "Hdst".
    destruct Hfacts as [Hcs2 HmBra0].
    assert (Hpc92 : ret_pc (B3 !!! Regidx Rra : mword 64)
                    = mword_of_int (RI + 0x92)) by (rewrite HB3ra; pcw).
    iEval (rewrite Hpc92) in "Hpc".
    pose proof Hcs2 as Hcs2c.
    assert (HmRsp : rd_sp m mBr).
    { rewrite /rd_sp
        (callee_saved_lookup Hcs2c csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB3sp. }
    assert (HmRs6 : mBr !!! Regidx Rs6 = ip)
      by (rewrite (callee_saved_lookup Hcs2c Rs6 ltac:(vm_compute; reflexivity));
          exact HB3s6).
    assert (HmRs7 : mBr !!! Regidx Rs7 = usv)
      by (rewrite (callee_saved_lookup Hcs2c Rs7 ltac:(vm_compute; reflexivity));
          exact HB3s7).
    assert (HmRs4 : mBr !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) tot)
      by (rewrite (callee_saved_lookup Hcs2c Rs4 ltac:(vm_compute; reflexivity));
          exact HB3s4).
    assert (HmRs1 : mBr !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64))
      by (rewrite (callee_saved_lookup Hcs2c Rs1 ltac:(vm_compute; reflexivity));
          exact HB3s1).
    assert (HmRs5 : mBr !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64))
      by (rewrite (callee_saved_lookup Hcs2c Rs5 ltac:(vm_compute; reflexivity));
          exact HB3s5).
    assert (HmRs3 : mBr !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite (callee_saved_lookup Hcs2c Rs3 ltac:(vm_compute; reflexivity));
          exact HB3s3).
    assert (HmRs9 : mBr !!! Regidx Rs9 = (mword_of_int 1024 : mword 64))
      by (rewrite (callee_saved_lookup Hcs2c Rs9 ltac:(vm_compute; reflexivity));
          exact HB3s9).
    assert (HmRs8 : mBr !!! Regidx Rs8 = (mword_of_int (-1) : mword 64))
      by (rewrite (callee_saved_lookup Hcs2c Rs8 ltac:(vm_compute; reflexivity));
          exact HB3s8).
    (* THE COUPLING: the buffer's bytes ARE the block's logical content *)
    iDestruct (inode_blocks_acc γfs bm data fbn Hfbnlt Hbnzz with "Hblocks")
      as "[[Hfsb1 Htok1] Hblback]".
    iEval (rewrite -Hubno) in "Hfsb1".
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (rd_held_k with "Hheld") as %Hkklt.
    iDestruct (rd_held_content with "Hfsb1 Hheld") as %Hbs0eq.
    subst bsB.
    iDestruct (rd_held_swap with "Hheld") as "[Hbuf Hheldback]".
    (* ===== +0x92 c.mv s2,a0 : s2 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x92)) Rs2 Ra0
              mBr (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi92").
    iIntros (CIDa10 Hqa10) "Hcg Hpc".
    set (E1 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mBr Ra0))]> mBr).
    assert (HE1s2 : E1 !!! Regidx Rs2 = bnode kkb).
    { rewrite /E1 upd_eq. rgne. rewrite HmBra0. apply add_vec_zero_l. }
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x92) : mword 64) 2
                  = mword_of_int (RI + 0x94)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x94 andi a5,s1,1023 : a5 := off % BSIZE ===== *)
    assert (Handv : and_vec (rget E1 Rs1)
                      (sign_extend' 64 (mword_of_int 1023 : mword 12))
                    = (mword_of_int (Z.of_nat o) : mword 64)).
    { rgne. rewrite (_ : E1 !!! Regidx Rs1
                         = (mword_of_int (Z.of_nat (off + tot)) : mword 64)); [| lkp].
      rewrite (rd_andi1023 (Z.of_nat (off + tot)) ltac:(lia) ltac:(lia)).
      rewrite Hoe rd_mod_z. reflexivity. }
    iApply (wp_andi_s_sconf (mword_of_int (RI + 0x94)) Ra5 Rs1
              (mword_of_int 1023 : mword 12) (mword_of_int (Z.of_nat o) : mword 64)
              E1 (K - 14)%nat b ltac:(nz) ltac:(rdok) Handv with "Hcg Hpc Hi94").
    iIntros (CIDa11 Hqa11) "Hcg Hpc".
    set (E2 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (Z.of_nat o) : mword 64)]> E1).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x94) : mword 64) 4
                  = mword_of_int (RI + 0x98)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x98 subw a4,s9,a5 : a4 := BSIZE - off%BSIZE ===== *)
    assert (Hsubv1 : sign_extend' 64
              (sub_vec (subrange_vec_dec (rget E2 Rs9) 31 0 : mword 32)
                       (subrange_vec_dec (rget E2 Ra5) 31 0 : mword 32))
              = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64)).
    { rgne; rgne.
      rewrite (_ : E2 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)); [| lkp].
      rewrite (_ : E2 !!! Regidx Ra5
                   = (mword_of_int (Z.of_nat o) : mword 64)); [| lkp].
      rewrite (rd_subw 1024 (Z.of_nat o) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite Nat2Z.inj_sub; [| lia]. rewrite Hbsz. reflexivity. }
    iApply (wp_subw_s_sconf (mword_of_int (RI + 0x98)) Ra4 Rs9 Ra5
              E2 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi98").
    iIntros (CIDa12 Hqa12) "Hcg Hpc".
    set (E3 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64
                    (sub_vec (subrange_vec_dec (rget E2 Rs9) 31 0 : mword 32)
                             (subrange_vec_dec (rget E2 Ra5) 31 0 : mword 32)))]> E2).
    assert (HE3a4 : E3 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64))
      by (rewrite /E3 upd_eq; exact Hsubv1).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x98) : mword 64) 4
                  = mword_of_int (RI + 0x9c)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x9c subw a3,s5,s3 : a3 := n - tot ===== *)
    assert (Hsubv2 : sign_extend' 64
              (sub_vec (subrange_vec_dec (rget E3 Rs5) 31 0 : mword 32)
                       (subrange_vec_dec (rget E3 Rs3) 31 0 : mword 32))
              = (mword_of_int (Z.of_nat (nc - tot)) : mword 64)).
    { rgne; rgne.
      rewrite (_ : E3 !!! Regidx Rs5
                   = (mword_of_int (Z.of_nat nc) : mword 64)); [| lkp].
      rewrite (_ : E3 !!! Regidx Rs3
                   = (mword_of_int (Z.of_nat tot) : mword 64)); [| lkp].
      rewrite (rd_subw (Z.of_nat nc) (Z.of_nat tot) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite Nat2Z.inj_sub; [reflexivity | lia]. }
    iApply (wp_subw_s_sconf (mword_of_int (RI + 0x9c)) Ra3 Rs5 Rs3
              E3 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9c").
    iIntros (CIDa13 Hqa13) "Hcg Hpc".
    set (E4 := <[Regidx Ra3 := regval_into_reg
                  (sign_extend' 64
                    (sub_vec (subrange_vec_dec (rget E3 Rs5) 31 0 : mword 32)
                             (subrange_vec_dec (rget E3 Rs3) 31 0 : mword 32)))]> E3).
    assert (HE4a3 : E4 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat (nc - tot)) : mword 64))
      by (rewrite /E4 upd_eq; exact Hsubv2).
    assert (HE4a4 : E4 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64)) by lkp.
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x9c) : mword 64) 4
                  = mword_of_int (RI + 0xa0)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xa0 c.mv s10,a4 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0xa0)) Rs10 Ra4
              E4 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia0").
    iIntros (CIDa14 Hqa14) "Hcg Hpc".
    set (E5 := <[Regidx Rs10 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget E4 Ra4))]> E4).
    assert (HE5s10 : E5 !!! Regidx Rs10
                     = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64)).
    { rewrite /E5 upd_eq. rgne. rewrite HE4a4. apply add_vec_zero_l. }
    assert (Hpp : add_vec_int (mword_of_int (RI + 0xa0) : mword 64) 2
                  = mword_of_int (RI + 0xa2)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    iDestruct (cpu_own_transport CIDa9 CIDa14 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDa9 CIDa14 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDa9 CIDa14 eb (proc_addr j)
                 ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CIDa3) (CIDb := CIDa14)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".

    (* ================================================================ *)
    (*  THE +0x4c BODY.  Everything linear is BAKED IN -- the two arms   *)
    (*  of the [bgeu a3,a4] below are alternatives, so one copy serves    *)
    (*  both; only the register file, the chunk length and the hart      *)
    (*  travel as wands.                                                 *)
    (* ================================================================ *)
    iAssert (∀ (CIDb : CpuId) (Mb : regfile) (mm : nat),
        rd_chunk_body j b K m nc tot o kkb usv ip off CIDa14 CIDb Mb mm)%I
      with "[Hcnt Hextc Hextm Hcont Hframe Hidev Hmeta Hmap Hdst
             Hbuf Hheldback Hfsb1 Htok1 Hblback]" as "BODY".
    { iIntros (CIDb Mb mm) "%Hanch %Hmmd %Hbsp %Hbs10 %Hba5 %Hbs2 %Hbs4 %Hbs7
                            %Hbs6 %Hbs1 %Hbs5 %Hbs3 %Hbs9 %Hbs8 Hcg Hpc".
      assert (Hmm1 : (1 <= mm)%nat) by (rewrite Hmmd; rewrite Hbsz in Holt |- *; lia).
      assert (Hmmn : (mm <= nc - tot)%nat) by (rewrite Hmmd; lia).
      assert (Hmmo : (o + mm <= BSIZE)%nat) by (rewrite Hmmd; lia).
      iPoseProof (rdi_04c with "Htext") as "Hi4c".
      iPoseProof (rdi_050 with "Htext") as "Hi50".
      iPoseProof (rdi_054 with "Htext") as "Hi54".
      iPoseProof (rdi_058 with "Htext") as "Hi58".
      iPoseProof (rdi_05a with "Htext") as "Hi5a".
      iPoseProof (rdi_05c with "Htext") as "Hi5c".
      iPoseProof (rdi_05e with "Htext") as "Hi5e".
      iPoseProof (rdi_060 with "Htext") as "Hi60".
      iPoseProof (rdi_064 with "Htext") as "Hi64".
      (* ===== +0x4c slli s11,s10,0x20 ===== *)
      iApply (wp_slli_s_sconf (mword_of_int (RI + 0x4c)) Rs11 Rs10
                (mword_of_int 32 : mword 6)
                (shift_bits_left (mword_of_int (Z.of_nat mm) : mword 64)
                   (subrange_vec_dec (mword_of_int 32 : mword 6)
                      (Z.sub log2_xlen 1) 0))
                Mb (K - 14)%nat b ltac:(nz) ltac:(rdok)
                ltac:(rgne; rewrite Hbs10; reflexivity) with "Hcg Hpc Hi4c").
      iIntros (CIDb1 Hqb1) "Hcg Hpc".
      set (D1 := <[Regidx Rs11 := regval_into_reg
                    (shift_bits_left (mword_of_int (Z.of_nat mm) : mword 64)
                       (subrange_vec_dec (mword_of_int 32 : mword 6)
                          (Z.sub log2_xlen 1) 0))]> Mb).
      assert (HD1s11 : D1 !!! Regidx Rs11
                = shift_bits_left (mword_of_int (Z.of_nat mm) : mword 64)
                    (subrange_vec_dec (mword_of_int 32 : mword 6)
                       (Z.sub log2_xlen 1) 0))
        by (rewrite /D1; apply upd_eq).
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x4c) : mword 64) 4
                    = mword_of_int (RI + 0x50)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x50 srli s11,s11,0x20 : s11 := (uint64) m ===== *)
      iApply (wp_srli4_s_sconf (mword_of_int (RI + 0x50)) Rs11 Rs11
                (mword_of_int 32 : mword 6) D1 (K - 14)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi50").
      iIntros (CIDb2 Hqb2) "Hcg Hpc".
      set (D2 := <[Regidx Rs11 := regval_into_reg
                    (shift_bits_right (rget D1 Rs11)
                       (subrange_vec_dec (mword_of_int 32 : mword 6)
                          (Z.sub log2_xlen 1) 0))]> D1).
      assert (HD2s11 : D2 !!! Regidx Rs11
                       = (mword_of_int (Z.of_nat mm) : mword 64)).
      { rewrite /D2 upd_eq. rgne. rewrite HD1s11.
        apply rd_zext32. rewrite (rd_nat_u mm ltac:(lia)).
        rewrite Hbsz in Hmmo. lia. }
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x50) : mword 64) 4
                    = mword_of_int (RI + 0x54)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x54 addi a2,s2,88 : a2 := bp->data ===== *)
      assert (HD2s2 : D2 !!! Regidx Rs2 = bnode kkb) by lkp.
      iApply (wp_addi4_s_sconf (mword_of_int (RI + 0x54)) Ra2 Rs2
                (mword_of_int 88 : mword 12) D2 (K - 14)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi54").
      iIntros (CIDb3 Hqb3) "Hcg Hpc".
      set (D3 := <[Regidx Ra2 := regval_into_reg
                    (add_vec (rget D2 Rs2)
                       (sign_extend' 64 (mword_of_int 88 : mword 12)))]> D2).
      assert (HD3a2 : D3 !!! Regidx Ra2 = b_data (bnode kkb)).
      { rewrite /D3 upd_eq. rgne. rewrite HD2s2. apply rd_data_addr. }
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x54) : mword 64) 4
                    = mword_of_int (RI + 0x58)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x58 c.mv a3,s11 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x58)) Ra3 Rs11
                D3 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi58").
      iIntros (CIDb4 Hqb4) "Hcg Hpc".
      set (D4 := <[Regidx Ra3 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget D3 Rs11))]> D3).
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x58) : mword 64) 2
                    = mword_of_int (RI + 0x5a)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x5a c.add a2,a2,a5 : a2 := bp->data + off%BSIZE ===== *)
      iApply (wp_cadd_s_sconf (mword_of_int (RI + 0x5a)) Ra2 Ra5
                D4 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5a").
      iIntros (CIDb5 Hqb5) "Hcg Hpc".
      set (D5 := <[Regidx Ra2 := regval_into_reg
                    (add_vec (rget D4 Ra2) (rget D4 Ra5))]> D4).
      assert (HD5a2 : D5 !!! Regidx Ra2 = pa_add (b_data (bnode kkb)) o).
      { rewrite /D5 upd_eq. rgne; rgne.
        rewrite (_ : D4 !!! Regidx Ra2 = b_data (bnode kkb)); [| lkp].
        rewrite (_ : D4 !!! Regidx Ra5
                     = (mword_of_int (Z.of_nat o) : mword 64)); [| lkp].
        apply rd_pa_add_moi. }
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x5a) : mword 64) 2
                    = mword_of_int (RI + 0x5c)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x5c c.mv a1,s4 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x5c)) Ra1 Rs4
                D5 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5c").
      iIntros (CIDb6 Hqb6) "Hcg Hpc".
      set (D6 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget D5 Rs4))]> D5).
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x5c) : mword 64) 2
                    = mword_of_int (RI + 0x5e)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x5e c.mv a0,s7 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x5e)) Ra0 Rs7
                D6 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e").
      iIntros (CIDb7 Hqb7) "Hcg Hpc".
      set (D7 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget D6 Rs7))]> D6).
      assert (HD7a0 : D7 !!! Regidx Ra0 = usv).
      { rewrite /D7 upd_eq. rgne.
        rewrite (_ : D6 !!! Regidx Rs7 = usv); [| lkp]. apply add_vec_zero_l. }
      assert (HD7a1 : D7 !!! Regidx Ra1
                      = pa_add (m !!! Regidx Ra2 : mword 64) tot).
      { rewrite (_ : D7 !!! Regidx Ra1
                     = add_vec (zero_reg : mword 64) (rget D5 Rs4)); [| lkp].
        rgne. rewrite (_ : D5 !!! Regidx Rs4
                           = pa_add (m !!! Regidx Ra2 : mword 64) tot); [| lkp].
        apply add_vec_zero_l. }
      assert (HD7a2 : D7 !!! Regidx Ra2 = pa_add (b_data (bnode kkb)) o) by lkp.
      assert (HD7a3 : D7 !!! Regidx Ra3
                      = (mword_of_int (Z.of_nat mm) : mword 64)).
      { rewrite (_ : D7 !!! Regidx Ra3
                     = add_vec (zero_reg : mword 64) (rget D3 Rs11)); [| lkp].
        rgne. rewrite (_ : D3 !!! Regidx Rs11
                           = (mword_of_int (Z.of_nat mm) : mword 64)); [| lkp].
        apply add_vec_zero_l. }
      assert (HD7sp : rd_sp m D7) by (rewrite /rd_sp; lkp).
      assert (HD7s1 : D7 !!! Regidx Rs1
                      = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
      assert (HD7s2 : D7 !!! Regidx Rs2 = bnode kkb) by lkp.
      assert (HD7s3 : D7 !!! Regidx Rs3
                      = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp.
      assert (HD7s4 : D7 !!! Regidx Rs4
                      = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
      assert (HD7s5 : D7 !!! Regidx Rs5
                      = (mword_of_int (Z.of_nat nc) : mword 64)) by lkp.
      assert (HD7s6 : D7 !!! Regidx Rs6 = ip) by lkp.
      assert (HD7s7 : D7 !!! Regidx Rs7 = usv) by lkp.
      assert (HD7s8 : D7 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
      assert (HD7s9 : D7 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
      assert (HD7s10 : D7 !!! Regidx Rs10
                       = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
      assert (HD7s11 : D7 !!! Regidx Rs11
                       = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x5e) : mword 64) 2
                    = mword_of_int (RI + 0x60)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ---- the SOURCE window inside the checked-out buffer ---- *)
      iDestruct (rd_buf_win_acc (bnode kkb) (blkmap_get bm fbn)
                   (mword_of_int 0 : mword 32) (data fbn) o mm Hmmo
                   with "Hbuf") as "(%Hlenb & Hwin & Hwinback)".
      (* ---- and the destination window, on the kernel arm ---- *)
      iAssert ((if user
                then proc_priv_core (proc_addr j) pidv (upd_upt V PI)
                else [∗ list] jj ∈ seq 0 mm,
                       pa_add (pa_add (m !!! Regidx Ra2 : mword 64) tot) jj
                         ↦ₘ[ktb] rd_delivered data dst_olds off tot (tot + jj)%nat)
               ∗ (if user then True
                  else p_pid (proc_addr j) ↦₄{dq} pidv
                       ∗ ([∗ list] jj ∈ seq 0 tot,
                            pa_add (m !!! Regidx Ra2 : mword 64) jj
                              ↦ₘ[ktb] rd_delivered data dst_olds off tot jj)
                       ∗ ([∗ list] jj ∈ seq 0 (n - tot - mm),
                            pa_add (pa_add (pa_add (m !!! Regidx Ra2 : mword 64) tot)
                                      mm) jj
                              ↦ₘ[ktb] rd_delivered data dst_olds off tot
                                   (tot + (mm + jj))%nat)))%I
        with "[Hdst]" as "[Hdstw Hdstrest]".
      { rewrite /rd_dst. destruct user.
        - iSplitL "Hdst"; [iExact "Hdst" | done].
        - iDestruct "Hdst" as "[Hdst Hppid]".
          iDestruct (rd_split3 (KTR := ktb) (m !!! Regidx Ra2 : mword 64)
                       tot mm (n - tot - mm)%nat n
                       (fun i => rd_delivered data dst_olds off tot i)
                       ltac:(lia) with "Hdst") as "(Hp & Hq & Hr)".
          iSplitL "Hq"; [iExact "Hq"|]. iSplitL "Hppid"; [iExact "Hppid"|].
          iSplitL "Hp"; [iExact "Hp"|]. iExact "Hr". }
      (* ===== +0x60 jal ra,either_copyout ===== *)
      iApply (wp_jal_s_sconf (mword_of_int (RI + 0x60)) Rra
                (mword_of_int 2092096 : mword 21) D7 (K - 14)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi60").
      iIntros (CIDb8 Hqb8) "Hcg Hpc".
      set (D8 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (RI + 0x60) : mword 64) 4)]> D7).
      assert (Htgtec : add_vec (mword_of_int (RI + 0x60) : mword 64)
                         (sign_extend' 64 (mword_of_int 2092096 : mword 21))
                       = mword_of_int KernelSyms.either_copyout) by pcw.
      iEval (rewrite Htgtec) in "Hpc".
      assert (HD8ra : D8 !!! Regidx Rra
                      = add_vec_int (mword_of_int (RI + 0x60) : mword 64) 4)
        by (rewrite /D8; apply upd_eq).
      assert (HD8a0 : D8 !!! Regidx Ra0 = usv) by lkp.
      assert (HD8a1 : D8 !!! Regidx Ra1
                      = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
      assert (HD8a2 : D8 !!! Regidx Ra2
                      = pa_add (b_data (bnode kkb)) o) by lkp.
      assert (HD8a3 : D8 !!! Regidx Ra3
                      = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
      iDestruct (cpu_own_transport CIDa14 CIDb8 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iEval (rewrite -HD8a2) in "Hwin".
      iEval (rewrite -HD8a1) in "Hdstw".
      iApply (EC.wp_either_copyout_sconf ktb KT0 γa γf D8 (K - 14)%nat 0%nat eb
                (proc_addr j) pidv (upd_upt V PI) user mm
                (fun i => (data fbn) !!! (o + i)%nat)
                (fun jj => rd_delivered data dst_olds off tot (tot + jj)%nat) b lks
                ltac:(lia)
                ltac:(rewrite HD8a0; exact Husv) HD8a3
                ltac:(destruct user;
                      [change (2 ^ 64)%Z with 18446744073709551616%Z
                      |change (2 ^ 31)%Z with 2147483648%Z];
                      rewrite Hbsz in Hmmo; lia)
                ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)
                with "Hcg Hcnt Htext Hpc Hkenv Hwin Hdstw").
      all: try lkbelow.
      iIntros (CIDb9 Hqb9 mE) "%HcsE Hcg Hcnt Hpc Hwin Hpost".
      assert (Hpc64 : ret_pc (D8 !!! Regidx Rra : mword 64)
                      = mword_of_int (RI + 0x64)) by (rewrite HD8ra; pcw).
      iEval (rewrite Hpc64) in "Hpc".
      iEval (rewrite /either_copyout_post HD8a1) in "Hpost".
      iEval (rewrite HD8a2) in "Hwin".
      (* ---- the two arms of the post, in one shape ---- *)
      iAssert (∃ P2 : uptd,
                 ⌜uptd_ext (pv_upt V) P2⌝ ∗
                 ⌜(mE !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64)
                  \/ ((mE !!! Regidx Ra0 : mword 64)
                        = (mword_of_int (-1) : mword 64) /\ user = true)⌝ ∗
                 rd_dst (ktb := ktb) γf j pidv dq user (upd_upt V P2)
                        (m !!! Regidx Ra2 : mword 64) n
                        (rd_delivered data dst_olds off (tot + mm)%nat))%I
        with "[Hpost Hdstrest]" as "Hnorm".
      { rewrite /rd_dst. destruct user.
        - iDestruct "Hpost" as "(%Hr & Hpp)".
          iDestruct "Hpp" as (P2) "[%Hx Hpriv]".
          iExists P2.
          iSplitR; [iPureIntro; exact (uptd_ext_trans _ _ _ HextI Hx)|].
          iSplitR; [iPureIntro; destruct Hr as [Hr|Hr];
                    [left; exact Hr | right; split; [exact Hr | reflexivity]]|].
          iExact "Hpriv".
        - iDestruct "Hpost" as "(%Hr & Hmid)".
          iDestruct "Hdstrest" as "(Hppid & Hp & Hq)".
          iExists PI.
          iSplitR; [iPureIntro; exact HextI|].
          iSplitR; [iPureIntro; left; exact Hr|].
          iSplitR "Hppid"; [| iExact "Hppid"].
          iApply (rd_join3 (KTR := ktb) (m !!! Regidx Ra2 : mword 64)
                    tot mm (n - tot - mm)%nat n
                    (fun i => rd_delivered data dst_olds off (tot + mm)%nat i)
                    ltac:(lia) with "[Hp] [Hmid] [Hq]").
          + iApply (big_sepL_mono with "Hp"). intros i jj Hjs.
            apply lookup_seq in Hjs as [-> Hlt]. rewrite Nat.add_0_l.
            rewrite (rd_deliver_lo data dst_olds off tot mm i ltac:(lia)).
            reflexivity.
          + iApply (big_sepL_mono with "Hmid"). intros i jj Hjs.
            apply lookup_seq in Hjs as [-> Hlt]. rewrite Nat.add_0_l.
            rewrite (rd_deliver_mid data dst_olds off tot mm fbn o i
                       ltac:(lia) ltac:(lia) ltac:(lia)).
            reflexivity.
          + iApply (big_sepL_mono with "Hq"). intros i jj Hjs.
            apply lookup_seq in Hjs as [-> Hlt]. rewrite Nat.add_0_l.
            rewrite (rd_deliver_hi data dst_olds off tot mm
                       (tot + (mm + i))%nat ltac:(lia)).
            reflexivity. }
      iDestruct "Hnorm" as (P2) "(%Hext2 & %HrE & Hdst2)".
      (* the buffer goes back UNCHANGED: readi never modified it *)
      iDestruct ("Hwinback" with "Hwin") as "Hbuf".
      iDestruct ("Hheldback" $! (data fbn) with "Hbuf") as "Hheld".
      pose proof HcsE as HcsEc.
      assert (HEsp : rd_sp m mE).
      { rewrite /rd_sp
          (callee_saved_lookup HcsEc csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HD7sp. }
      assert (HEs1 : mE !!! Regidx Rs1
                     = (mword_of_int (Z.of_nat (off + tot)) : mword 64))
        by (rewrite (callee_saved_lookup HcsEc Rs1 ltac:(vm_compute; reflexivity));
            exact HD7s1).
      assert (HEs2 : mE !!! Regidx Rs2 = bnode kkb)
        by (rewrite (callee_saved_lookup HcsEc Rs2 ltac:(vm_compute; reflexivity));
            exact HD7s2).
      assert (HEs3 : mE !!! Regidx Rs3
                     = (mword_of_int (Z.of_nat tot) : mword 64))
        by (rewrite (callee_saved_lookup HcsEc Rs3 ltac:(vm_compute; reflexivity));
            exact HD7s3).
      assert (HEs4 : mE !!! Regidx Rs4
                     = pa_add (m !!! Regidx Ra2 : mword 64) tot)
        by (rewrite (callee_saved_lookup HcsEc Rs4 ltac:(vm_compute; reflexivity));
            exact HD7s4).
      assert (HEs5 : mE !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64))
        by (rewrite (callee_saved_lookup HcsEc Rs5 ltac:(vm_compute; reflexivity));
            exact HD7s5).
      assert (HEs6 : mE !!! Regidx Rs6 = ip)
        by (rewrite (callee_saved_lookup HcsEc Rs6 ltac:(vm_compute; reflexivity));
            exact HD7s6).
      assert (HEs7 : mE !!! Regidx Rs7 = usv)
        by (rewrite (callee_saved_lookup HcsEc Rs7 ltac:(vm_compute; reflexivity));
            exact HD7s7).
      assert (HEs8 : mE !!! Regidx Rs8 = (mword_of_int (-1) : mword 64))
        by (rewrite (callee_saved_lookup HcsEc Rs8 ltac:(vm_compute; reflexivity));
            exact HD7s8).
      assert (HEs9 : mE !!! Regidx Rs9 = (mword_of_int 1024 : mword 64))
        by (rewrite (callee_saved_lookup HcsEc Rs9 ltac:(vm_compute; reflexivity));
            exact HD7s9).
      assert (HEs10 : mE !!! Regidx Rs10
                      = (mword_of_int (Z.of_nat mm) : mword 64))
        by (rewrite (callee_saved_lookup HcsEc Rs10 ltac:(vm_compute; reflexivity));
            exact HD7s10).
      assert (HEs11 : mE !!! Regidx Rs11
                      = (mword_of_int (Z.of_nat mm) : mword 64))
        by (rewrite (callee_saved_lookup HcsEc Rs11 ltac:(vm_compute; reflexivity));
            exact HD7s11).
      assert (HKbl : (K_brelse <= K - 14)%nat) by (lia).
      destruct HrE as [Hr0 | Hrm1].
      - (* ============ THE COPY SUCCEEDED ============ *)
        iPoseProof (rdi_068 with "Htext") as "Hi68".
        iPoseProof (rdi_06a with "Htext") as "Hi6a".
        iPoseProof (rdi_06e with "Htext") as "Hi6e".
        iPoseProof (rdi_072 with "Htext") as "Hi72".
        iPoseProof (rdi_076 with "Htext") as "Hi76".
        iPoseProof (rdi_078 with "Htext") as "Hi78".
        iApply (wp_beq_fall_s_sconf (mword_of_int (RI + 0x64))
                  (mword_of_int 70 : mword 13) Rs8 Ra0 mE (K - 14)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite Hr0 HEs8; vm_compute; reflexivity)
                  with "Hcg Hpc Hi64").
        iIntros (CIDc1 Hqc1) "Hcg Hpc".
        assert (Hpp : add_vec_int (mword_of_int (RI + 0x64) : mword 64) 4
                      = mword_of_int (RI + 0x68)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x68 c.mv a0,s2 ===== *)
        iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x68)) Ra0 Rs2
                  mE (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi68").
        iIntros (CIDc2 Hqc2) "Hcg Hpc".
        set (F1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget mE Rs2))]> mE).
        assert (HF1a0 : F1 !!! Regidx Ra0 = bnode kkb).
        { rewrite /F1 upd_eq. rgne. rewrite HEs2. apply add_vec_zero_l. }
        assert (Hpp : add_vec_int (mword_of_int (RI + 0x68) : mword 64) 2
                      = mword_of_int (RI + 0x6a)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x6a jal ra,brelse ===== *)
        iApply (wp_jal_s_sconf (mword_of_int (RI + 0x6a)) Rra
                  (mword_of_int 2094636 : mword 21) F1 (K - 14)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi6a").
        iIntros (CIDc3 Hqc3) "Hcg Hpc".
        set (F2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (RI + 0x6a) : mword 64) 4)]> F1).
        assert (Htgtbl : add_vec (mword_of_int (RI + 0x6a) : mword 64)
                           (sign_extend' 64 (mword_of_int 2094636 : mword 21))
                         = mword_of_int KernelSyms.brelse) by pcw.
        iEval (rewrite Htgtbl) in "Hpc".
        assert (HF2ra : F2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (RI + 0x6a) : mword 64) 4)
          by (rewrite /F2; apply upd_eq).
        assert (HF2a0 : F2 !!! Regidx Ra0 = bnode kkb) by lkp.
        iDestruct (cpu_own_transport CIDb9 CIDc3 0 eb (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (rd_dst_pid γf j pidv dq user (upd_upt V P2)
                     (m !!! Regidx Ra2 : mword 64) n
                     (rd_delivered data dst_olds off (tot + mm)%nat)
                     with "Hdst2") as "[Hppid Hdstback]".
        iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kkb
                  pidv dev (blkmap_get bm fbn) (rd_q user dq) F2 (K - 14)%nat eb
                  (proc_addr j) (data fbn) bsdB dB b lks
                  HKbl Hkklt HF2a0 Hbelow
                  with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hheld").
        all: try lkbelow.
        iIntros (CIDc7 Hqc7 mR) "%HcsR Hcg Hcnt Hpc Hppid Hsl".
        iDestruct ("Hdstback" with "Hppid") as "Hdst2".
        assert (Hpc6e : ret_pc (F2 !!! Regidx Rra : mword 64)
                        = mword_of_int (RI + 0x6e)) by (rewrite HF2ra; pcw).
        iEval (rewrite Hpc6e) in "Hpc".
        iEval (rewrite Hubno) in "Hfsb1".
        iDestruct ("Hblback" $! (data fbn) with "Hfsb1 Htok1") as "Hblocks".
        iDestruct (rd_blocks_restore γfs bm data fbn with "Hblocks") as "Hblocks".
        pose proof HcsR as HcsRc.
        assert (HRsp : rd_sp m mR).
        { rewrite /rd_sp
            (callee_saved_lookup HcsRc csp_rs1 ltac:(vm_compute; reflexivity)).
          assert (HF2sp : rd_sp m F2) by (rewrite /rd_sp; lkp). exact HF2sp. }
        assert (HRs1 : mR !!! Regidx Rs1
                       = (mword_of_int (Z.of_nat (off + tot)) : mword 64)).
        { rewrite (callee_saved_lookup HcsRc Rs1 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs1
                       = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
          exact HH. }
        assert (HRs3 : mR !!! Regidx Rs3
                       = (mword_of_int (Z.of_nat tot) : mword 64)).
        { rewrite (callee_saved_lookup HcsRc Rs3 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs3
                       = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp.
          exact HH. }
        assert (HRs4 : mR !!! Regidx Rs4
                       = pa_add (m !!! Regidx Ra2 : mword 64) tot).
        { rewrite (callee_saved_lookup HcsRc Rs4 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs4
                       = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
          exact HH. }
        assert (HRs5 : mR !!! Regidx Rs5
                       = (mword_of_int (Z.of_nat nc) : mword 64)).
        { rewrite (callee_saved_lookup HcsRc Rs5 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs5
                       = (mword_of_int (Z.of_nat nc) : mword 64)) by lkp.
          exact HH. }
        assert (HRs6 : mR !!! Regidx Rs6 = ip).
        { rewrite (callee_saved_lookup HcsRc Rs6 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs6 = ip) by lkp. exact HH. }
        assert (HRs7 : mR !!! Regidx Rs7 = usv).
        { rewrite (callee_saved_lookup HcsRc Rs7 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs7 = usv) by lkp. exact HH. }
        assert (HRs8 : mR !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)).
        { rewrite (callee_saved_lookup HcsRc Rs8 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs8
                       = (mword_of_int (-1) : mword 64)) by lkp. exact HH. }
        assert (HRs9 : mR !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)).
        { rewrite (callee_saved_lookup HcsRc Rs9 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs9
                       = (mword_of_int 1024 : mword 64)) by lkp. exact HH. }
        assert (HRs10 : mR !!! Regidx Rs10
                        = (mword_of_int (Z.of_nat mm) : mword 64)).
        { rewrite (callee_saved_lookup HcsRc Rs10 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs10
                       = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
          exact HH. }
        assert (HRs11 : mR !!! Regidx Rs11
                        = (mword_of_int (Z.of_nat mm) : mword 64)).
        { rewrite (callee_saved_lookup HcsRc Rs11 ltac:(vm_compute; reflexivity)).
          assert (HH : F2 !!! Regidx Rs11
                       = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
          exact HH. }
        (* ===== +0x6e addw s3,s10,s3 : tot += m ===== *)
        iApply (wp_addw4_s_sconf (mword_of_int (RI + 0x6e)) Rs3 Rs10 Rs3
                  mR (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6e").
        iIntros (CIDc8 Hqc8) "Hcg Hpc".
        set (G1 := <[Regidx Rs3 := regval_into_reg
                      (sign_extend' 64
                        (add_vec (subrange_vec_dec (rget mR Rs10) 31 0 : mword 32)
                                 (subrange_vec_dec (rget mR Rs3) 31 0 : mword 32)))]> mR).
        assert (HG1s3 : G1 !!! Regidx Rs3
                        = (mword_of_int (Z.of_nat (tot + mm)) : mword 64)).
        { rewrite /G1 upd_eq. rgne; rgne. rewrite HRs10 HRs3.
          rewrite (rd_addw (Z.of_nat mm) (Z.of_nat tot)
                     ltac:(lia) ltac:(lia) ltac:(lia)).
          assert (Hz : (Z.of_nat mm + Z.of_nat tot)%Z = Z.of_nat (tot + mm)) by lia.
          rewrite Hz. reflexivity. }
        assert (Hpp : add_vec_int (mword_of_int (RI + 0x6e) : mword 64) 4
                      = mword_of_int (RI + 0x72)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x72 addw s1,s10,s1 : off += m ===== *)
        assert (HG1s10 : G1 !!! Regidx Rs10
                         = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
        assert (HG1s1 : G1 !!! Regidx Rs1
                        = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
        iApply (wp_addw4_s_sconf (mword_of_int (RI + 0x72)) Rs1 Rs10 Rs1
                  G1 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi72").
        iIntros (CIDc9 Hqc9) "Hcg Hpc".
        set (G2 := <[Regidx Rs1 := regval_into_reg
                      (sign_extend' 64
                        (add_vec (subrange_vec_dec (rget G1 Rs10) 31 0 : mword 32)
                                 (subrange_vec_dec (rget G1 Rs1) 31 0 : mword 32)))]> G1).
        assert (HG2s1 : G2 !!! Regidx Rs1
                        = (mword_of_int (Z.of_nat (off + (tot + mm))) : mword 64)).
        { rewrite /G2 upd_eq. rgne; rgne. rewrite HG1s10 HG1s1.
          rewrite (rd_addw (Z.of_nat mm) (Z.of_nat (off + tot))
                     ltac:(lia) ltac:(lia) ltac:(lia)).
          assert (Hz : (Z.of_nat mm + Z.of_nat (off + tot))%Z
                       = Z.of_nat (off + (tot + mm))) by lia.
          rewrite Hz. reflexivity. }
        assert (Hpp : add_vec_int (mword_of_int (RI + 0x72) : mword 64) 4
                      = mword_of_int (RI + 0x76)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x76 c.add s4,s4,s11 : dst += m ===== *)
        assert (HG2s4 : G2 !!! Regidx Rs4
                        = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
        assert (HG2s11 : G2 !!! Regidx Rs11
                         = (mword_of_int (Z.of_nat mm) : mword 64)) by lkp.
        iApply (wp_cadd_s_sconf (mword_of_int (RI + 0x76)) Rs4 Rs11
                  G2 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi76").
        iIntros (CIDc10 Hqc10) "Hcg Hpc".
        set (G3 := <[Regidx Rs4 := regval_into_reg
                      (add_vec (rget G2 Rs4) (rget G2 Rs11))]> G2).
        assert (HG3s4 : G3 !!! Regidx Rs4
                        = pa_add (m !!! Regidx Ra2 : mword 64) (tot + mm)).
        { rewrite /G3 upd_eq. rgne; rgne. rewrite HG2s4 HG2s11. apply rd_pa_step. }
        assert (HG3s3 : G3 !!! Regidx Rs3
                        = (mword_of_int (Z.of_nat (tot + mm)) : mword 64)) by lkp.
        assert (HG3s1 : G3 !!! Regidx Rs1
                        = (mword_of_int (Z.of_nat (off + (tot + mm))) : mword 64))
          by lkp.
        assert (HG3s5 : G3 !!! Regidx Rs5
                        = (mword_of_int (Z.of_nat nc) : mword 64)) by lkp.
        assert (HG3s6 : G3 !!! Regidx Rs6 = ip) by lkp.
        assert (HG3s7 : G3 !!! Regidx Rs7 = usv) by lkp.
        assert (HG3s8 : G3 !!! Regidx Rs8
                        = (mword_of_int (-1) : mword 64)) by lkp.
        assert (HG3s9 : G3 !!! Regidx Rs9
                        = (mword_of_int 1024 : mword 64)) by lkp.
        assert (HG3sp : rd_sp m G3) by (rewrite /rd_sp; lkp).
        assert (Hpp : add_vec_int (mword_of_int (RI + 0x76) : mword 64) 2
                      = mword_of_int (RI + 0x78)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0x78 bgeu s3,s5 : is the read finished? ===== *)
        destruct (Nat.leb_spec nc (tot + mm)) as [Hfin | Hmore].
        + (* ---------- finished: leave the loop at +0xbe ---------- *)
          assert (Htotmm : (tot + mm)%nat = nc) by lia.
          iApply (wp_bgeu_taken_s_sconf (mword_of_int (RI + 0x78))
                    (mword_of_int 70 : mword 13) Rs5 Rs3 G3 (K - 14)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HG3s3 HG3s5;
                          rewrite (bc_ge_moi (tot + mm) nc ltac:(lia) ltac:(lia));
                          apply Nat.leb_le; lia)
                    ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi78").
          iApply bi.later_intro. iIntros (CIDc11 Hqc11) "Hcg Hpc".
          assert (Htgtbe : add_vec (mword_of_int (RI + 0x78) : mword 64)
                    (sign_extend' 64 (mword_of_int 70 : mword 13))
                  = mword_of_int (RI + 0xbe)) by pcw.
          iEval (rewrite Htgtbe) in "Hpc".
          iPoseProof (rdi_0be with "Htext") as "Hjbe".
          iPoseProof (rdi_0c0 with "Htext") as "Hjc0".
          iPoseProof (rdi_0c2 with "Htext") as "Hjc2".
          iPoseProof (rdi_0c4 with "Htext") as "Hjc4".
          iPoseProof (rdi_0c6 with "Htext") as "Hjc6".
          iPoseProof (rdi_0c8 with "Htext") as "Hjc8".
          iDestruct (cpu_own_transport CIDc7 CIDc11 0 eb (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          (* Hextc/Hextm were last transported to CIDa14 (before the
             either_copyout crossing); neither either_copyout nor brelse
             thread the complement, so it is stranded there -- span the
             WIDE hop straight to CIDc11, skipping both callees. *)
          iDestruct (trap_csrs_ext_transport CIDa14 CIDc11 eb (proc_addr j)
                       ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CIDa14 CIDc11 eb (proc_addr j)
                       ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
          iApply (rd_exit (CID0 := CIDc11)  γfs bn γf dev ip bm data dn
                    user off n (tot + mm)%nat dst_olds V P2
                    (mword_of_int (Z.of_nat (tot + mm)) : mword 64)
                    pidv dq dqd j
                    (RI + 0xbe) (RI + 0xc0) (RI + 0xc2) (RI + 0xc4) (RI + 0xc6)
                    (RI + 0xc8)
                    (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")))
                    m G3 K eb b lks
                    HK HG3sp HG3s3 Hext2 ltac:(lia) ltac:(right; split; [reflexivity | lia])
                    ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw)
                    ltac:(pcw) ltac:(vm_compute; reflexivity)
                    with "Hcg Hcnt Hextc Hextm Htext Hpc Hjbe Hjc0 Hjc2 Hjc4 Hjc6 Hjc8
                          Hframe Hidev Hmeta Hmap Hblocks
                          Hdst2 Hsl [Hcont]").
          iApply (wp_next_shift (b := true) (CIDa := CIDa14) (CIDb := CIDc11)
                    ltac:(wp_next_chain) with "Hcont").
        + (* ---------- another block: back to the head at +0x7c ------- *)
          iApply (wp_bgeu_fall_s_sconf (mword_of_int (RI + 0x78))
                    (mword_of_int 70 : mword 13) Rs5 Rs3 G3 (K - 14)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HG3s3 HG3s5;
                          rewrite (bc_ge_moi (tot + mm) nc ltac:(lia) ltac:(lia));
                          apply Nat.leb_gt; lia)
                    with "Hcg Hpc Hi78").
          iIntros (CIDc11 Hqc11) "Hcg Hpc".
          assert (Hpp : add_vec_int (mword_of_int (RI + 0x78) : mword 64) 4
                        = mword_of_int (RI + 0x7c)) by pcw.
          iEval (rewrite Hpp) in "Hpc". clear Hpp.
          (* the iteration filled its block to the boundary, so the fuel
             decreases by exactly one ([rd_blocks_step]) *)
          assert (Hboundary : mm = (BSIZE - o)%nat) by (rewrite Hmmd; lia).
          assert (Hstep : (rd_blocks (off + (tot + mm)) (nc - (tot + mm)) + 1
                           <= rd_blocks (off + tot) (nc - tot))%nat).
          { assert (Ho' : ((off + tot) `mod` BSIZE)%nat = o)
              by (rewrite Hoe; reflexivity).
            pose proof (rd_blocks_step (off + tot) (nc - tot)%nat
                          ltac:(rewrite Ho'; lia)) as Hs.
            rewrite Ho' in Hs.
            replace (off + tot + (BSIZE - o))%nat with (off + (tot + mm))%nat in Hs
              by lia.
            replace (nc - tot - (BSIZE - o))%nat with (nc - (tot + mm))%nat in Hs
              by lia.
            exact Hs. }
          iDestruct (cpu_own_transport CIDc7 CIDc11 0 eb (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          (* same wide hop as the exit arm above: Hextc/Hextm last moved to
             CIDa14, and neither either_copyout nor brelse thread them. *)
          iDestruct (trap_csrs_ext_transport CIDa14 CIDc11 eb (proc_addr j)
                       ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
          iDestruct (cpu_claim_ext_transport CIDa14 CIDc11 eb (proc_addr j)
                       ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
          iDestruct (wp_next_shift (b := true) (CIDa := CIDa14) (CIDb := CIDc11)
                       ltac:(wp_next_chain) with "Hcont") as "Hcont".
          iApply (IH CIDc11 (tot + mm)%nat P2 G3
                    ltac:(lia) Hext2 ltac:(lia)
                    HG3sp HG3s6 HG3s7 HG3s4 HG3s1 HG3s5 HG3s3 HG3s9 HG3s8
                    with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hkenv Hprocs
                          Hdevi Hdgeom Hdlock Hframe Hidev
                          Hmeta Hmap Hblocks Hdst2 Hsl Hcont").
      - (* ====== THE COPY OUT FAULTED -- only reachable on the USER arm,
             where either_copyout may answer -1.  readi releases a buffer
             it never modified, so there is nothing to log and nothing to
             re-index: [bio_locked] is the one bread produced. ====== *)
        destruct Hrm1 as [Hrm1 Huser].
        iPoseProof (rdi_0aa with "Htext") as "Hiaa".
        iPoseProof (rdi_0ac with "Htext") as "Hiac".
        iPoseProof (rdi_0b0 with "Htext") as "Hib0".
        iApply (wp_beq_taken_s_sconf (mword_of_int (RI + 0x64))
                  (mword_of_int 70 : mword 13) Rs8 Ra0 mE (K - 14)%nat b
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite Hrm1 HEs8; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi64").
        iApply bi.later_intro. iIntros (CIDd1 Hqd1) "Hcg Hpc".
        assert (Htgtaa : add_vec (mword_of_int (RI + 0x64) : mword 64)
                  (sign_extend' 64 (mword_of_int 70 : mword 13))
                = mword_of_int (RI + 0xaa)) by pcw.
        iEval (rewrite Htgtaa) in "Hpc".
        (* ===== +0xaa c.mv a0,s2 ===== *)
        iApply (wp_cmv_s_sconf (mword_of_int (RI + 0xaa)) Ra0 Rs2
                  mE (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiaa").
        iIntros (CIDd2 Hqd2) "Hcg Hpc".
        set (J1 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget mE Rs2))]> mE).
        assert (HJ1a0 : J1 !!! Regidx Ra0 = bnode kkb).
        { rewrite /J1 upd_eq. rgne. rewrite HEs2. apply add_vec_zero_l. }
        assert (Hpp : add_vec_int (mword_of_int (RI + 0xaa) : mword 64) 2
                      = mword_of_int (RI + 0xac)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0xac jal ra,brelse ===== *)
        iApply (wp_jal_s_sconf (mword_of_int (RI + 0xac)) Rra
                  (mword_of_int 2094570 : mword 21) J1 (K - 14)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hiac").
        iIntros (CIDd3 Hqd3) "Hcg Hpc".
        set (J2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (RI + 0xac) : mword 64) 4)]> J1).
        assert (Htgtbl : add_vec (mword_of_int (RI + 0xac) : mword 64)
                           (sign_extend' 64 (mword_of_int 2094570 : mword 21))
                         = mword_of_int KernelSyms.brelse) by pcw.
        iEval (rewrite Htgtbl) in "Hpc".
        assert (HJ2ra : J2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (RI + 0xac) : mword 64) 4)
          by (rewrite /J2; apply upd_eq).
        assert (HJ2a0 : J2 !!! Regidx Ra0 = bnode kkb) by lkp.
        iDestruct (cpu_own_transport CIDb9 CIDd3 0 eb (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (rd_dst_pid γf j pidv dq user (upd_upt V P2)
                     (m !!! Regidx Ra2 : mword 64) n
                     (rd_delivered data dst_olds off (tot + mm)%nat)
                     with "Hdst2") as "[Hppid Hdstback]".
        iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kkb
                  pidv dev (blkmap_get bm fbn) (rd_q user dq) J2 (K - 14)%nat eb
                  (proc_addr j) (data fbn) bsdB dB b lks
                  HKbl Hkklt HJ2a0 Hbelow
                  with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hheld").
        all: try lkbelow.
        iIntros (CIDd7 Hqd7 mR) "%HcsR Hcg Hcnt Hpc Hppid Hsl".
        iDestruct ("Hdstback" with "Hppid") as "Hdst2".
        assert (Hpcb0 : ret_pc (J2 !!! Regidx Rra : mword 64)
                        = mword_of_int (RI + 0xb0)) by (rewrite HJ2ra; pcw).
        iEval (rewrite Hpcb0) in "Hpc".
        iEval (rewrite Hubno) in "Hfsb1".
        iDestruct ("Hblback" $! (data fbn) with "Hfsb1 Htok1") as "Hblocks".
        iDestruct (rd_blocks_restore γfs bm data fbn with "Hblocks") as "Hblocks".
        pose proof HcsR as HcsRc.
        assert (HRsp : rd_sp m mR).
        { rewrite /rd_sp
            (callee_saved_lookup HcsRc csp_rs1 ltac:(vm_compute; reflexivity)).
          assert (HH : rd_sp m J2) by (rewrite /rd_sp; lkp). exact HH. }
        (* ===== +0xb0 c.li s3,-1 : tot := -1 ===== *)
        iApply (wp_cli_s_sconf (mword_of_int (RI + 0xb0)) Rs3
                  (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                  mR (K - 14)%nat b ltac:(nz) ltac:(rdok) rd_li_m1
                  with "Hcg Hpc Hib0").
        iIntros (CIDd8 Hqd8) "Hcg Hpc".
        set (J3 := <[Regidx Rs3 := regval_into_reg
                      (mword_of_int (-1) : mword 64)]> mR).
        assert (HJ3s3 : J3 !!! Regidx Rs3 = (mword_of_int (-1) : mword 64))
          by (rewrite /J3; apply upd_eq).
        assert (HJ3sp : rd_sp m J3)
          by (rewrite /rd_sp /J3 upd_ne; [exact HRsp | nz]).
        assert (Hpp : add_vec_int (mword_of_int (RI + 0xb0) : mword 64) 2
                      = mword_of_int (RI + 0xb2)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* the destination claim reverts to [tot]: on this arm [user] is
           [true], so both readings are the same [proc_priv]. *)
        iAssert (rd_dst (ktb := ktb) γf j pidv dq user (upd_upt V P2)
                        (m !!! Regidx Ra2 : mword 64) n
                        (rd_delivered data dst_olds off tot))%I
          with "[Hdst2]" as "Hdst3".
        { rewrite /rd_dst. destruct user; [iExact "Hdst2" | discriminate Huser]. }
        iPoseProof (rdi_0b2 with "Htext") as "Hjb2".
        iPoseProof (rdi_0b4 with "Htext") as "Hjb4".
        iPoseProof (rdi_0b6 with "Htext") as "Hjb6".
        iPoseProof (rdi_0b8 with "Htext") as "Hjb8".
        iPoseProof (rdi_0ba with "Htext") as "Hjba".
        iPoseProof (rdi_0bc with "Htext") as "Hjbc".
        iDestruct (cpu_own_transport CIDd7 CIDd8 0 eb (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        (* wide hop, as in the other exit arm: Hextc/Hextm last moved to
           CIDa14, and neither either_copyout nor brelse thread them. *)
        iDestruct (trap_csrs_ext_transport CIDa14 CIDd8 eb (proc_addr j)
                     ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDa14 CIDd8 eb (proc_addr j)
                     ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
        iApply (rd_exit (CID0 := CIDd8)  γfs bn γf dev ip bm data dn
                  user off n tot dst_olds V P2 (mword_of_int (-1) : mword 64)
                  pidv dq dqd j
                  (RI + 0xb2) (RI + 0xb4) (RI + 0xb6) (RI + 0xb8) (RI + 0xba)
                  (RI + 0xbc)
                  (sign_extend' 21 (concat_vec (mword_of_int 14 : mword 11) ('b"0")))
                  m J3 K eb b lks
                  HK HJ3sp HJ3s3 Hext2 ltac:(lia)
                  ltac:(left; split; [reflexivity | exact Huser])
                  ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw) ltac:(pcw)
                  ltac:(pcw) ltac:(vm_compute; reflexivity)
                  with "Hcg Hcnt Hextc Hextm Htext Hpc Hjb2 Hjb4 Hjb6 Hjb8 Hjba Hjbc
                        Hframe Hidev Hmeta Hmap Hblocks
                        Hdst3 Hsl [Hcont]").
        iApply (wp_next_shift (b := true) (CIDa := CIDa14) (CIDb := CIDd8)
                  ltac:(wp_next_chain) with "Hcont"). }
    (* ===== +0xa2 bgeu a3,a4 : m = min(nc - tot, BSIZE - off%BSIZE) ===== *)
    assert (HE5a5 : E5 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat o) : mword 64)) by lkp.
    assert (HE5s2 : E5 !!! Regidx Rs2 = bnode kkb) by lkp.
    assert (HE5a3 : E5 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat (nc - tot)) : mword 64)) by lkp.
    assert (HE5a4 : E5 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat (BSIZE - o)) : mword 64)) by lkp.
    assert (HE5sp : rd_sp m E5) by (rewrite /rd_sp; lkp).
    assert (HE5s1 : E5 !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
    assert (HE5s3 : E5 !!! Regidx Rs3
                    = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp.
    assert (HE5s4 : E5 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
    assert (HE5s5 : E5 !!! Regidx Rs5
                    = (mword_of_int (Z.of_nat nc) : mword 64)) by lkp.
    assert (HE5s6 : E5 !!! Regidx Rs6 = ip) by lkp.
    assert (HE5s7 : E5 !!! Regidx Rs7 = usv) by lkp.
    assert (HE5s8 : E5 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
    assert (HE5s9 : E5 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
    destruct (Nat.leb_spec (BSIZE - o) (nc - tot)) as [Hfill | Hlast].
    - (* the chunk fills the block to the boundary: s10 already holds it *)
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (RI + 0xa2))
                (mword_of_int 8106 : mword 13) Ra4 Ra3 E5 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HE5a3 HE5a4;
                      rewrite (bc_ge_moi (nc - tot) (BSIZE - o) ltac:(lia) ltac:(lia));
                      apply Nat.leb_le; lia)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia2").
      iApply bi.later_intro. iIntros (CIDa15 Hqa15) "Hcg Hpc".
      assert (Htgt4c : add_vec (mword_of_int (RI + 0xa2) : mword 64)
                (sign_extend' 64 (mword_of_int 8106 : mword 13))
              = mword_of_int (RI + 0x4c)) by pcw.
      iEval (rewrite Htgt4c) in "Hpc".
      iApply ("BODY" $! CIDa15 E5 (BSIZE - o)%nat with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc");
        [ wp_next_chain | lia | exact HE5sp | exact HE5s10 | exact HE5a5
        | exact HE5s2 | exact HE5s4 | exact HE5s7 | exact HE5s6 | exact HE5s1
        | exact HE5s5 | exact HE5s3 | exact HE5s9 | exact HE5s8 ].
    - (* the last chunk: s10 := a3 = nc - tot *)
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (RI + 0xa2))
                (mword_of_int 8106 : mword 13) Ra4 Ra3 E5 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HE5a3 HE5a4;
                      rewrite (bc_ge_moi (nc - tot) (BSIZE - o) ltac:(lia) ltac:(lia));
                      apply Nat.leb_gt; lia)
                with "Hcg Hpc Hia2").
      iIntros (CIDa15 Hqa15) "Hcg Hpc".
      assert (Hpp : add_vec_int (mword_of_int (RI + 0xa2) : mword 64) 4
                    = mword_of_int (RI + 0xa6)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xa6 c.mv s10,a3 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (RI + 0xa6)) Rs10 Ra3
                E5 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia6").
      iIntros (CIDa16 Hqa16) "Hcg Hpc".
      set (E6 := <[Regidx Rs10 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget E5 Ra3))]> E5).
      assert (HE6s10 : E6 !!! Regidx Rs10
                       = (mword_of_int (Z.of_nat (nc - tot)) : mword 64)).
      { rewrite /E6 upd_eq. rgne. rewrite HE5a3. apply add_vec_zero_l. }
      assert (Hpp : add_vec_int (mword_of_int (RI + 0xa6) : mword 64) 2
                    = mword_of_int (RI + 0xa8)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xa8 c.j +0x4c ===== *)
      iApply (wp_cj_s_sconf (mword_of_int (RI + 0xa8))
                (sign_extend' 21 (concat_vec (mword_of_int 2002 : mword 11) ('b"0")))
                E6 (K - 14)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hia8").
      iIntros (CIDa17 Hqa17). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgt4c : add_vec (mword_of_int (RI + 0xa8) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2002 : mword 11) ('b"0"))))
              = mword_of_int (RI + 0x4c)) by pcw.
      iEval (rewrite Htgt4c) in "Hpc".
      assert (HE6a5 : E6 !!! Regidx Ra5
                      = (mword_of_int (Z.of_nat o) : mword 64)) by lkp.
      assert (HE6s2 : E6 !!! Regidx Rs2 = bnode kkb) by lkp.
      assert (HE6sp : rd_sp m E6) by (rewrite /rd_sp; lkp).
      assert (HE6s1 : E6 !!! Regidx Rs1
                      = (mword_of_int (Z.of_nat (off + tot)) : mword 64)) by lkp.
      assert (HE6s3 : E6 !!! Regidx Rs3
                      = (mword_of_int (Z.of_nat tot) : mword 64)) by lkp.
      assert (HE6s4 : E6 !!! Regidx Rs4
                      = pa_add (m !!! Regidx Ra2 : mword 64) tot) by lkp.
      assert (HE6s5 : E6 !!! Regidx Rs5
                      = (mword_of_int (Z.of_nat nc) : mword 64)) by lkp.
      assert (HE6s6 : E6 !!! Regidx Rs6 = ip) by lkp.
      assert (HE6s7 : E6 !!! Regidx Rs7 = usv) by lkp.
      assert (HE6s8 : E6 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
      assert (HE6s9 : E6 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
      iApply ("BODY" $! CIDa17 E6 (nc - tot)%nat with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc");
        [ wp_next_chain | lia | exact HE6sp | exact HE6s10 | exact HE6a5
        | exact HE6s2 | exact HE6s4 | exact HE6s7 | exact HE6s6 | exact HE6s1
        | exact HE6s5 | exact HE6s3 | exact HE6s9 | exact HE6s8 ].
  Qed.

End ReadiLoop.

(* ===================================================================== *)
(*  +0x00 .. +0x4a : the prologue, the PRE-FRAME exit, the dead overflow  *)
(*  test, the clamp and the n = 0 arm.                                    *)
(* ===================================================================== *)
Section ReadiMain.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the CALLER's buffer tier -- see this function's spec for why it is not
     [KT1].  A KtierLe HYPOTHESIS in the section beats [ktier_le_refl] at
     instance search, so every OTHER leaf in this file has to name its own
     datum tier out loud (the blanket [(ktd := KT1)] below). *)
  Context {ktb : ktier}.
  Context `{!KtierLe ktb KT1}.
  Local Ltac reg_neq := vm_compute; discriminate.
  Local Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | rgne
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  (* RULE ONE (claude-notes/optimization.md): the +0x34-onwards tail both
     clamp arms of [wp_readi_sconf] hand off to, named so the walk's
     proofmode steps stop re-embedding ~20 lines of ∀/wands per step.
     The ∀ binders stay visible at the [iAssert] below; only what they
     quantify over is folded here. *)
  Definition rd_readtail_body
      (j : nat) (b : bool) (K : nat) (m : regfile) (ip : mword 64)
      (dn : dinode) (off n szn : nat) (CIDs5 : CpuId)
      (CIDt : CpuId) (Mt : regfile) (nc : nat) : iProp Σ :=
    (⌜b = false \/ proc_addr j = zero_reg -> (CIDt : CPU) = (CIDs5 : CPU)⌝ -∗
     ⌜nc = rd_clamp (di_size dn) off n⌝ -∗
     ⌜(nc <= n)%nat⌝ -∗
     ⌜(off + nc <= szn)%nat⌝ -∗
     ⌜rd_sp m Mt⌝ -∗
     ⌜Mt !!! Regidx Rs5 = (mword_of_int (Z.of_nat nc) : mword 64)⌝ -∗
     ⌜Mt !!! Regidx Rs6 = ip⌝ -∗
     ⌜Mt !!! Regidx Rs7 = (m !!! Regidx Ra1 : mword 64)⌝ -∗
     ⌜Mt !!! Regidx Rs4 = pa_add (m !!! Regidx Ra2 : mword 64) 0%nat⌝ -∗
     ⌜Mt !!! Regidx Rs1 = (mword_of_int (Z.of_nat (off + 0)) : mword 64)⌝ -∗
     ⌜Mt !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)⌝ -∗
     ⌜Mt !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64)⌝ -∗
     ⌜Mt !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64)⌝ -∗
     ⌜Mt !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64)⌝ -∗
     ⌜Mt !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64)⌝ -∗
     sie_cap_gpr KT1 Mt (K - 14)%nat b (proc_addr j) -∗
     pc_is (mword_of_int (RI + 0x34) : mword 64) -∗
     WP (Loop : expr riscv_lang))%I.

  Lemma wp_readi_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (γa : gname) (γf : gname)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode)
      (user : bool) (off n : nat) (dst_olds : nat -> bv 8)
      (V : pprivate)
      (pidv : mword 32) (dq dqd : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_readi_sconf_body ktb γs j γl γu γd γk pd pav pu bn γfs γa γf
                          cov logstart dev ip bm data dn
                          user off n dst_olds V pidv dq dqd m K eb b lks.
  Proof.
    cbv beta delta [wp_readi_sconf_body].
    intros pcE pj dst ret_tgt HK Hgeom Hwf Hcov Hszmax Hoff32 Hsumg Hj Hgl
           Ha0 Ha1 Ha3 Ha4 Hbelow.
    pose proof HK as HK'. 
    change (2 ^ 32)%Z with 4294967296%Z in Hoff32.
    assert (Hgeom0 : log_geom_ok cov logstart) by exact Hgeom.
    assert (HmbZ : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    remember (Z.to_nat (bv_unsigned (di_size dn))) as szn eqn:Hszne.
    assert (Hszz : Z.of_nat szn = bv_unsigned (di_size dn))
      by (rewrite Hszne; apply rd_size_nat).
    rewrite -Hszz in Hcov. rewrite -Hszz in Hszmax.
    rewrite HmbZ in Hszmax.
    assert (Hsznmax : (szn <= MAXFILE * BSIZE)%nat)
      by (rewrite rd_maxfile_val rd_bsize_val; lia).
    assert (Hsznlt : (Z.of_nat szn < 2147483648)%Z) by lia.
    assert (Hszlt : bv_unsigned (di_size dn) < 2147483648)
      by (rewrite -Hszz; exact Hsznlt).
    assert (Hszu : bv_unsigned (mword_of_int (Z.of_nat szn) : mword 64)
                   = Z.of_nat szn) by (apply rd_nat_u; lia).
    assert (Hoffu : bv_unsigned (mword_of_int (Z.of_nat off) : mword 64)
                    = Z.of_nat off) by (apply rd_nat_u; lia).
    (* THE TWO ABI WORDS.  [off] and [n] are full 32-bit uints, so a3, a4 and
       the [addw]'s sum are sign-extended and worth [w32_uarg] as unsigned
       64-bit words -- above every file size exactly when they are negative.
       THE JOINT PREMISE IS USED HERE, at the sum: it is what makes the
       [c.addw]'s result DENOTE [off + n] rather than its wrap.  See
       W32Arith.v. *)
    assert (Ha3u : bv_unsigned
                     (sign_extend' 64 (mword_of_int (Z.of_nat off) : mword 32)
                      : mword 64) = w32_uarg (Z.of_nat off))
      by (apply w32_arg_unsigned; lia).
    (* [Hsumu], the same reading of the [addw]'s result, is NOT available
       here: its bound is guarded by the size test and so is derived in the
       fall-through arm below, where the guard has been discharged.  Only
       a3 is read before the test. *)
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hkenv Hidev
              Hmeta Hmap Hblocks Hdst #Hprocs #Hdevi #Hdgeom #Hdlock Hsl Hcont".
    iAssert (rd_cont (ktb := ktb) (CID0 := CID) γfs bn γf dev ip bm data dn user off n
               dst_olds V pidv dq dqd j m K eb b lks)%I with "[Hcont]" as "Hcont";
      [rewrite /rd_cont /rd_dst; iExact "Hcont"|].
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Heb2b. cbn in Heb2b.
    iPoseProof (rdi_000 with "Htext") as "Hi00".
    iPoseProof (rdi_002 with "Htext") as "Hi02".
    iPoseProof (rdi_006 with "Htext") as "Hi06".
    iPoseProof (rdi_008 with "Htext") as "Hi08".
    iPoseProof (rdi_00a with "Htext") as "Hi0a".
    iPoseProof (rdi_00c with "Htext") as "Hi0c".
    iPoseProof (rdi_00e with "Htext") as "Hi0e".
    iPoseProof (rdi_010 with "Htext") as "Hi10".
    iPoseProof (rdi_012 with "Htext") as "Hi12".
    iPoseProof (rdi_014 with "Htext") as "Hi14".
    iPoseProof (rdi_016 with "Htext") as "Hi16".
    iPoseProof (rdi_018 with "Htext") as "Hi18".
    iPoseProof (rdi_01a with "Htext") as "Hi1a".
    iPoseProof (rdi_01c with "Htext") as "Hi1c".
    iPoseProof (rdi_01e with "Htext") as "Hi1e".
    iPoseProof (rdi_020 with "Htext") as "Hi20".
    iPoseProof (rdi_022 with "Htext") as "Hi22".
    iPoseProof (rdi_024 with "Htext") as "Hi24".
    iPoseProof (rdi_026 with "Htext") as "Hi26".
    iPoseProof (rdi_02a with "Htext") as "Hi2a".
    iPoseProof (rdi_02c with "Htext") as "Hi2c".
    iPoseProof (rdi_030 with "Htext") as "Hi30".
    iPoseProof (rdi_034 with "Htext") as "Hi34".
    iPoseProof (rdi_038 with "Htext") as "Hi38".
    iPoseProof (rdi_03a with "Htext") as "Hi3a".
    iPoseProof (rdi_03c with "Htext") as "Hi3c".
    iPoseProof (rdi_03e with "Htext") as "Hi3e".
    iPoseProof (rdi_040 with "Htext") as "Hi40".
    iPoseProof (rdi_042 with "Htext") as "Hi42".
    iPoseProof (rdi_044 with "Htext") as "Hi44".
    iPoseProof (rdi_048 with "Htext") as "Hi48".
    iPoseProof (rdi_04a with "Htext") as "Hi4a".
    iPoseProof (rdi_0ca with "Htext") as "Hica".
    iPoseProof (rdi_0cc with "Htext") as "Hicc".
    iPoseProof (rdi_0ee with "Htext") as "Hiee".
    iPoseProof (rdi_0f0 with "Htext") as "Hif0".
    rewrite /inode_meta.
    iDestruct "Hmeta" as "(Hmt & Hmj & Hmn & Hml & Hmz)".
    (* ===== +0x00 c.lw a5,76(a0) : a5 := ip->size ===== *)
    assert (Hszadr : add_vec (rget m Ra0)
                       (sign_extend' 64 (mword_of_int 76 : mword 12))
                     = i_size ip) by (rgne; rewrite Ha0; reflexivity).
    iEval (rewrite -Hszadr) in "Hmz".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) pcE Ra5 Ra0 (mword_of_int 76 : mword 12)
              m K (di_size dn : mword 32) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi00 Hmz").
    iIntros (CIDp0 Hqp0) "Hcg Hpc Hmz".
    iEval (rewrite Hszadr) in "Hmz".
    set (Q0 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (di_size dn : mword 32))]> m).
    assert (HQ0a5 : Q0 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat szn) : mword 64)).
    { rewrite /Q0 upd_eq. rewrite (rd_sext32_moi (di_size dn) Hszlt).
      rewrite -Hszz. reflexivity. }
    assert (HQ0a3 : Q0 !!! Regidx Ra3
                    = sign_extend' 64 (mword_of_int (Z.of_nat off) : mword 32))
      by lkp.
    assert (Hpp : add_vec_int pcE 2 = mword_of_int (RI + 0x2))
      by (rewrite /pcE; pcw).
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x02 bltu a5,a3 : off > ip->size ? ===== *)
    destruct (Nat.ltb_spec szn off) as [Hsml | Hbig].
    { (* ---- THE PRE-FRAME EXIT: li a0,0; ret, with no frame at all ---- *)
      assert (Hclamp0 : rd_clamp (di_size dn) off n = 0%nat).
      { rewrite /rd_clamp -Hszne. case_decide as Hd; [lia | exfalso; lia]. }
      (* the size compare is 64-bit unsigned and a3 may be a sign-extended
         NEGATIVE off; either way an [off] past the end is above the size as
         an unsigned word ([w32_uarg_gt]) *)
      iApply (wp_bltu_taken_s_sconf (mword_of_int (RI + 0x2))
                (mword_of_int 236 : mword 13) Ra3 Ra5 Q0 K b ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HQ0a5 HQ0a3;
                      rewrite (rd_ltu_read _ _ _ _ Hszu Ha3u);
                      apply Z.ltb_lt; apply w32_uarg_gt; lia)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi02").
      iApply bi.later_intro. iIntros (CIDx1 Hqx1) "Hcg Hpc".
      assert (Htgt : add_vec (mword_of_int (RI + 0x2) : mword 64)
                (sign_extend' 64 (mword_of_int 236 : mword 13))
              = mword_of_int (RI + 0xee)) by pcw.
      iEval (rewrite Htgt) in "Hpc".
      (* ===== +0xee c.li a0,0 ===== *)
      iApply (wp_cli_s_sconf (mword_of_int (RI + 0xee)) Ra0
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                Q0 K b ltac:(nz) ltac:(rdok) rd_li_0 with "Hcg Hpc Hiee").
      iIntros (CIDx2 Hqx2) "Hcg Hpc".
      set (X1 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int 0 : mword 64)]> Q0).
      assert (HX1a0 : X1 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
        by (rewrite /X1; apply upd_eq).
      assert (Hpp : add_vec_int (mword_of_int (RI + 0xee) : mword 64) 2
                    = mword_of_int (RI + 0xf0)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xf0 c.ret ===== *)
      assert (HX1ra : X1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)) by lkp.
      iApply (wp_cret_s_sconf (mword_of_int (RI + 0xf0)) Rra X1 K b ltac:(nz)
                with "Hcg Hpc Hif0").
      iIntros (CIDx3 Hqx3) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (X1 !!! Regidx Rra : mword 64)
                      = ret_pc (m !!! Regidx Rra : mword 64))
        by (rewrite HX1ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iAssert (inode_meta ip dn) with "[Hmt Hmj Hmn Hml Hmz]" as "Hmeta".
      { rewrite /inode_meta.
        iSplitL "Hmt"; [iExact "Hmt"|]. iSplitL "Hmj"; [iExact "Hmj"|].
        iSplitL "Hmn"; [iExact "Hmn"|]. iSplitL "Hml"; [iExact "Hml"|].
        iExact "Hmz". }
      iAssert (rd_dst (ktb := ktb) γf j pidv dq user (upd_upt V (pv_upt V))
                      (m !!! Regidx Ra2 : mword 64) n
                      (rd_delivered data dst_olds off 0%nat))%I
        with "[Hdst]" as "Hdst".
      { rewrite /rd_dst. destruct user.
        - rewrite rd_upd_upt_id. iExact "Hdst".
        - iDestruct "Hdst" as "[Hdst Hppid]".
          iSplitR "Hppid"; [| iExact "Hppid"].
          iApply (big_sepL_mono with "Hdst"). intros i jj Hj2.
          apply lookup_seq in Hj2 as [-> Hlt]. rewrite Nat.add_0_l.
          rewrite (rd_deliver_0 data dst_olds off i). reflexivity. }
      iDestruct (cpu_own_transport CID CIDx3 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID CIDx3 eb (proc_addr j)
                   ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CIDx3 eb (proc_addr j)
                   ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
      rewrite /rd_cont.
      iSpecialize ("Hcont" $! CIDx3 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! X1 0%nat (pv_upt V)
                with "[%] [%] [%] [%] Hcg Hcnt Hextc Hextm Hpc Hidev Hmeta Hmap Hblocks Hdst Hsl").
      { unfold callee_saved. split_and!; lkp. }
      { apply uptd_ext_refl. }
      { lia. }
      { right. split; [exact HX1a0 | rewrite Hclamp0; reflexivity]. }
    }
    (* ---- THE SIZE TEST HAS BOUNDED off.  [off <= size < 2^31], so a3's
       sign extension is the identity and from here on a3 is the plain
       literal every step below already expected.  [n] is NOT bounded --
       it stays a full 32-bit uint, in a4 and in s5, until the clamp. ---- *)
    (* ...and it is what DISCHARGES THE GUARD on the joint premise.  The
       [c.addw a4,a3] at +0x022 is behind this test, so the sum only has to
       be non-wrapping here -- which is the whole reason the premise is
       guarded rather than asked outright.  See SpecReadi.v's header. *)
    assert (Hsum : (Z.of_nat off + Z.of_nat n < 4294967296)%Z).
    { change 4294967296%Z with (2 ^ 32)%Z.
      apply Hsumg. rewrite -Hszz. lia. }
    assert (Hsumu : bv_unsigned
                      (sign_extend' 64
                         (mword_of_int (Z.of_nat (off + n)) : mword 32)
                       : mword 64) = w32_uarg (Z.of_nat (off + n)))
      by (apply w32_arg_unsigned; lia).
    assert (Hofflt : (Z.of_nat off < 2147483648)%Z) by lia.
    assert (Ha3lit : (sign_extend' 64 (mword_of_int (Z.of_nat off) : mword 32)
                      : mword 64) = mword_of_int (Z.of_nat off))
      by (apply rd_sext32; lia).
    rewrite Ha3lit in Ha3. rewrite Ha3lit in HQ0a3.
    (* ---- everything past this point holds the destination at [tot = 0]
       and the descriptor at [pv_upt V] ---- *)
    assert (HVid : upd_upt V (pv_upt V) = V) by apply rd_upd_upt_id.
    iAssert (rd_dst (ktb := ktb) γf j pidv dq user (upd_upt V (pv_upt V))
                    (m !!! Regidx Ra2 : mword 64) n
                    (rd_delivered data dst_olds off 0%nat))%I
      with "[Hdst]" as "Hdst".
    { rewrite /rd_dst. destruct user.
      - rewrite HVid. iExact "Hdst".
      - iDestruct "Hdst" as "[Hdst Hppid]".
        iSplitR "Hppid"; [| iExact "Hppid"].
        iApply (big_sepL_mono with "Hdst"). intros i jj Hj2.
        apply lookup_seq in Hj2 as [-> Hlt]. rewrite Nat.add_0_l.
        rewrite (rd_deliver_0 data dst_olds off i). reflexivity. }
    iAssert (inode_meta ip dn) with "[Hmt Hmj Hmn Hml Hmz]" as "Hmeta".
    { rewrite /inode_meta.
      iSplitL "Hmt"; [iExact "Hmt"|]. iSplitL "Hmj"; [iExact "Hmj"|].
      iSplitL "Hmn"; [iExact "Hmn"|]. iSplitL "Hml"; [iExact "Hml"|].
      iExact "Hmz". }
    iApply (wp_bltu_fall_s_sconf (mword_of_int (RI + 0x2))
              (mword_of_int 236 : mword 13) Ra3 Ra5 Q0 K b ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HQ0a5 HQ0a3;
                    rewrite (rd_ltu_read _ _ _ _ Hszu Hoffu);
                    apply Z.ltb_ge; lia)
              with "Hcg Hpc Hi02").
    iIntros (CIDp1 Hqp1) "Hcg Hpc".
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x2) : mword 64) 4
                  = mword_of_int (RI + 0x6)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x06 c.addi16sp sp,-112 : the 14-slot frame ===== *)
    assert (HQ0sp : Q0 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by lkp.
    assert (Hpush : add_vec (Q0 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6)))
                    = pa_stk (Q0 !!! Regidx csp_rs1 : mword 64) 14).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (RI + 0x6))
              (mword_of_int 57 : mword 6) Q0 K 14 b ltac:(lia) Hpush
              with "Hcg Hpc Hi06").
    iIntros (CIDp2 Hqp2) "Hcg Hstk Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (Q0 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))))]> Q0).
    assert (HR1sp : rd_sp m R1).
    { rewrite /rd_sp /R1 upd_eq HQ0sp. reflexivity. }
    iEval (rewrite HQ0sp) in "Hstk".
    iEval (rewrite (stack_own_slots (KTR := KT1))) in "Hstk".
    iEval (cbn [seq]) in "Hstk".
    iDestruct "Hstk" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                          & HfA & HfB & HfC & HfD & HfE & _)".
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x6) : mword 64) 2
                  = mword_of_int (RI + 0x8)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x08 sd ra,104(sp) ===== *)
    iDestruct "Hf1" as (w1) "Hf1".
    assert (Hc1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x08)) (mword_of_int 13 : mword 6) Rra
              R1 (K - 14)%nat w1 b with "Hcg Hpc Hi08 Hf1").
    iIntros (CIDs1 Hqs1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    assert (Hw1 : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64)) by lkp.
    first [ iEval (rewrite Hw1) in "Hf1" | iEval (rgne; rewrite Hw1) in "Hf1" ].
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x08) : mword 64) 2
                  = mword_of_int (RI + 0x0a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x0a sd s0,96(sp) ===== *)
    iDestruct "Hf2" as (w2) "Hf2".
    assert (Hc2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x0a)) (mword_of_int 12 : mword 6) Rs0
              R1 (K - 14)%nat w2 b with "Hcg Hpc Hi0a Hf2").
    iIntros (CIDs2 Hqs2) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    assert (Hw2 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64)) by lkp.
    first [ iEval (rewrite Hw2) in "Hf2" | iEval (rgne; rewrite Hw2) in "Hf2" ].
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x0a) : mword 64) 2
                  = mword_of_int (RI + 0x0c)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x0c sd s1,88(sp) ===== *)
    iDestruct "Hf3" as (w3) "Hf3".
    assert (Hc3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc3) in "Hf3".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x0c)) (mword_of_int 11 : mword 6) Rs1
              R1 (K - 14)%nat w3 b with "Hcg Hpc Hi0c Hf3").
    iIntros (CIDs3 Hqs3) "Hcg Hpc Hf3".
    iEval (rewrite Hc3) in "Hf3".
    assert (Hw3 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)) by lkp.
    first [ iEval (rewrite Hw3) in "Hf3" | iEval (rgne; rewrite Hw3) in "Hf3" ].
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x0c) : mword 64) 2
                  = mword_of_int (RI + 0x0e)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x0e sd s4,64(sp) ===== *)
    iDestruct "Hf6" as (w6) "Hf6".
    assert (Hc6 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc6) in "Hf6".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x0e)) (mword_of_int 8 : mword 6) Rs4
              R1 (K - 14)%nat w6 b with "Hcg Hpc Hi0e Hf6").
    iIntros (CIDs6 Hqs6) "Hcg Hpc Hf6".
    iEval (rewrite Hc6) in "Hf6".
    assert (Hw6 : (R1 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64)) by lkp.
    first [ iEval (rewrite Hw6) in "Hf6" | iEval (rgne; rewrite Hw6) in "Hf6" ].
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x0e) : mword 64) 2
                  = mword_of_int (RI + 0x10)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x10 sd s5,56(sp) ===== *)
    iDestruct "Hf7" as (w7) "Hf7".
    assert (Hc7 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc7) in "Hf7".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x10)) (mword_of_int 7 : mword 6) Rs5
              R1 (K - 14)%nat w7 b with "Hcg Hpc Hi10 Hf7").
    iIntros (CIDs7 Hqs7) "Hcg Hpc Hf7".
    iEval (rewrite Hc7) in "Hf7".
    assert (Hw7 : (R1 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64)) by lkp.
    first [ iEval (rewrite Hw7) in "Hf7" | iEval (rgne; rewrite Hw7) in "Hf7" ].
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x10) : mword 64) 2
                  = mword_of_int (RI + 0x12)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x12 sd s6,48(sp) ===== *)
    iDestruct "Hf8" as (w8) "Hf8".
    assert (Hc8 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc8) in "Hf8".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x12)) (mword_of_int 6 : mword 6) Rs6
              R1 (K - 14)%nat w8 b with "Hcg Hpc Hi12 Hf8").
    iIntros (CIDs8 Hqs8) "Hcg Hpc Hf8".
    iEval (rewrite Hc8) in "Hf8".
    assert (Hw8 : (R1 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64)) by lkp.
    first [ iEval (rewrite Hw8) in "Hf8" | iEval (rgne; rewrite Hw8) in "Hf8" ].
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x12) : mword 64) 2
                  = mword_of_int (RI + 0x14)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x14 sd s7,40(sp) ===== *)
    iDestruct "Hf9" as (w9) "Hf9".
    assert (Hc9 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc9) in "Hf9".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x14)) (mword_of_int 5 : mword 6) Rs7
              R1 (K - 14)%nat w9 b with "Hcg Hpc Hi14 Hf9").
    iIntros (CIDs9 Hqs9) "Hcg Hpc Hf9".
    iEval (rewrite Hc9) in "Hf9".
    assert (Hw9 : (R1 !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64)) by lkp.
    first [ iEval (rewrite Hw9) in "Hf9" | iEval (rgne; rewrite Hw9) in "Hf9" ].
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x14) : mword 64) 2
                  = mword_of_int (RI + 0x16)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x16 addi s0,sp,112 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (RI + 0x16))
              (Cregidx (mword_of_int 0)) (mword_of_int 28 : mword 8) Rs0
              R1 (K - 14)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rdok) with "Hcg Hpc Hi16").
    iIntros (CIDp3 Hqp3) "Hcg Hpc".
    set (S1 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 28 : mword 8))))]> R1).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x16) : mword 64) 2
                  = mword_of_int (RI + 0x18)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x18 c.mv s6,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x18)) Rs6 Ra0
              S1 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18").
    iIntros (CIDp4 Hqp4) "Hcg Hpc".
    set (S2 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S1 Ra0))]> S1).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x18) : mword 64) 2
                  = mword_of_int (RI + 0x1a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x1a c.mv s7,a1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x1a)) Rs7 Ra1
              S2 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
    iIntros (CIDp5 Hqp5) "Hcg Hpc".
    set (S3 := <[Regidx Rs7 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S2 Ra1))]> S2).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x1a) : mword 64) 2
                  = mword_of_int (RI + 0x1c)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x1c c.mv s4,a2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x1c)) Rs4 Ra2
              S3 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1c").
    iIntros (CIDp6 Hqp6) "Hcg Hpc".
    set (S4 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S3 Ra2))]> S3).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x1c) : mword 64) 2
                  = mword_of_int (RI + 0x1e)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x1e c.mv s1,a3 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x1e)) Rs1 Ra3
              S4 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1e").
    iIntros (CIDp7 Hqp7) "Hcg Hpc".
    set (S5 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S4 Ra3))]> S4).
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x1e) : mword 64) 2
                  = mword_of_int (RI + 0x20)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x20 c.mv s5,a4 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (RI + 0x20)) Rs5 Ra4
              S5 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi20").
    iIntros (CIDp8 Hqp8) "Hcg Hpc".
    set (S6 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget S5 Ra4))]> S5).
    assert (HS6sp : rd_sp m S6) by (rewrite /rd_sp; lkp).
    assert (HS6a3 : S6 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat off) : mword 64)) by lkp.
    assert (HS6a4 : S6 !!! Regidx Ra4
                    = sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))
      by lkp.
    assert (HS6a5 : S6 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat szn) : mword 64)) by lkp.
    assert (HS6s6 : S6 !!! Regidx Rs6 = ip).
    { rewrite (_ : S6 !!! Regidx Rs6
                   = add_vec (zero_reg : mword 64) (rget S1 Ra0)); [| lkp].
      rgne. rewrite (_ : S1 !!! Regidx Ra0 = ip); [| lkp]. apply add_vec_zero_l. }
    assert (HS6s7 : S6 !!! Regidx Rs7 = (m !!! Regidx Ra1 : mword 64)).
    { rewrite (_ : S6 !!! Regidx Rs7
                   = add_vec (zero_reg : mword 64) (rget S2 Ra1)); [| lkp].
      rgne. rewrite (_ : S2 !!! Regidx Ra1 = (m !!! Regidx Ra1 : mword 64)); [| lkp].
      apply add_vec_zero_l. }
    assert (HS6s4 : S6 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) 0%nat).
    { rewrite (_ : S6 !!! Regidx Rs4
                   = add_vec (zero_reg : mword 64) (rget S3 Ra2)); [| lkp].
      rgne. rewrite (_ : S3 !!! Regidx Ra2 = (m !!! Regidx Ra2 : mword 64)); [| lkp].
      rewrite add_vec_zero_l. rewrite -(rd_pa_add_moi _ 0%nat).
      change (Z.of_nat 0%nat) with 0%Z. symmetry. apply kv_addv_zero. }
    assert (HS6s1 : S6 !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat (off + 0)) : mword 64)).
    { rewrite (_ : S6 !!! Regidx Rs1
                   = add_vec (zero_reg : mword 64) (rget S4 Ra3)); [| lkp].
      rgne. rewrite (_ : S4 !!! Regidx Ra3
                         = (mword_of_int (Z.of_nat off) : mword 64)); [| lkp].
      rewrite add_vec_zero_l. rewrite Nat.add_0_r. reflexivity. }
    assert (HS6s5 : S6 !!! Regidx Rs5
                    = sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32)).
    { rewrite /S6 upd_eq. rgne.
      rewrite (_ : S5 !!! Regidx Ra4
                   = (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32)
                      : mword 64)); [| lkp].
      apply add_vec_zero_l. }
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x20) : mword 64) 2
                  = mword_of_int (RI + 0x22)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x22 c.addw a4,a3 : a4 := n + off.  THE JOINT PREMISE is
       what makes this non-wrapping; see SpecReadi.v. ===== *)
    iEval (rewrite rd_creg_a3 rd_creg_a4) in "Hi22".
    iApply (wp_addw_s_sconf (mword_of_int (RI + 0x22)) Ra4 Ra3
              S6 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iIntros (CIDp9 Hqp9) "Hcg Hpc".
    set (T1 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64
                    (add_vec (subrange_vec_dec (rget S6 Ra4) 31 0 : mword 32)
                             (subrange_vec_dec (rget S6 Ra3) 31 0 : mword 32)))]> S6).
    (* the [addw] truncates both operands, so the sign extension is invisible
       to it and the sum comes back in the same ABI form -- [w32_addw_arg],
       which needs no premise at all: both sides wrap mod 2^32 *)
    assert (HT1a4 : T1 !!! Regidx Ra4
                    = sign_extend' 64
                        (mword_of_int (Z.of_nat (off + n)) : mword 32)).
    { rewrite /T1 upd_eq. rgne; rgne. rewrite HS6a4 HS6a3.
      rewrite (w32_addw_arg (Z.of_nat n) (Z.of_nat off)).
      assert (Hz : (Z.of_nat n + Z.of_nat off)%Z = Z.of_nat (off + n)) by lia.
      rewrite Hz. reflexivity. }
    assert (HT1a3 : T1 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat off) : mword 64)) by lkp.
    assert (HT1a5 : T1 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat szn) : mword 64)) by lkp.
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x22) : mword 64) 2
                  = mword_of_int (RI + 0x24)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x24 c.li a0,0 (the value the overflow exit would return) ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (RI + 0x24)) Ra0
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              T1 (K - 14)%nat b ltac:(nz) ltac:(rdok) rd_li_0 with "Hcg Hpc Hi24").
    iIntros (CIDp10 Hqp10) "Hcg Hpc".
    set (T2 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> T1).
    assert (HT2a4 : T2 !!! Regidx Ra4
                    = sign_extend' 64
                        (mword_of_int (Z.of_nat (off + n)) : mword 32)) by lkp.
    assert (HT2a3 : T2 !!! Regidx Ra3
                    = (mword_of_int (Z.of_nat off) : mword 64)) by lkp.
    assert (HT2a5 : T2 !!! Regidx Ra5
                    = (mword_of_int (Z.of_nat szn) : mword 64)) by lkp.
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x24) : mword 64) 2
                  = mword_of_int (RI + 0x26)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0x26 bltu a4,a3 : xv6's overflow test -- DEAD by the joint
       premise (off + n cannot have wrapped, so the sum's word is at least
       off's, sign-extended or not: [w32_uarg_lb]) ===== *)
    iApply (wp_bltu_fall_s_sconf (mword_of_int (RI + 0x26))
              (mword_of_int 182 : mword 13) Ra3 Ra4 T2 (K - 14)%nat b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HT2a4 HT2a3;
                    rewrite (rd_ltu_read _ _ _ _ Hsumu Hoffu);
                    apply Z.ltb_ge;
                    pose proof (w32_uarg_lb (Z.of_nat (off + n))); lia)
              with "Hcg Hpc Hi26").
    iIntros (CIDp11 Hqp11) "Hcg Hpc".
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x26) : mword 64) 4
                  = mword_of_int (RI + 0x2a)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HT2sp : rd_sp m T2) by (rewrite /rd_sp; lkp).
    (* ===== +0x2a sd s3,72(sp) ===== *)
    iDestruct "Hf5" as (w5) "Hf5".
    assert (Hc5 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hc5) in "Hf5".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x2a)) (mword_of_int 9 : mword 6) Rs3
              T2 (K - 14)%nat w5 b with "Hcg Hpc Hi2a Hf5").
    iIntros (CIDs5 Hqs5) "Hcg Hpc Hf5".
    iEval (rewrite Hc5) in "Hf5".
    assert (Hw5 : (T2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)) by lkp.
    first [ iEval (rewrite Hw5) in "Hf5" | iEval (rgne; rewrite Hw5) in "Hf5" ].
    assert (Hpp : add_vec_int (mword_of_int (RI + 0x2a) : mword 64) 2
                  = mword_of_int (RI + 0x2c)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    iAssert (rd_fr8 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
      as "Hframe".
    { rewrite /rd_fr8.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
      iSplitL "Hf9"; [iExact "Hf9"|]. iSplitL "HfA"; [iExact "HfA"|].
      iSplitL "HfB"; [iExact "HfB"|]. iSplitL "HfC"; [iExact "HfC"|].
      iSplitL "HfD"; [iExact "HfD"|]. iExact "HfE". }
    assert (HT2s5 : T2 !!! Regidx Rs5
                    = sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32)).
    { rewrite (_ : T2 !!! Regidx Rs5 = (S6 !!! Regidx Rs5 : mword 64));
        [exact HS6s5 | lkp]. }
    assert (HT2s6 : T2 !!! Regidx Rs6 = ip).
    { rewrite (_ : T2 !!! Regidx Rs6 = (S6 !!! Regidx Rs6 : mword 64));
        [exact HS6s6 | lkp]. }
    assert (HT2s7 : T2 !!! Regidx Rs7 = (m !!! Regidx Ra1 : mword 64)).
    { rewrite (_ : T2 !!! Regidx Rs7 = (S6 !!! Regidx Rs7 : mword 64));
        [exact HS6s7 | lkp]. }
    assert (HT2s4 : T2 !!! Regidx Rs4
                    = pa_add (m !!! Regidx Ra2 : mword 64) 0%nat).
    { rewrite (_ : T2 !!! Regidx Rs4 = (S6 !!! Regidx Rs4 : mword 64));
        [exact HS6s4 | lkp]. }
    assert (HT2s1 : T2 !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat (off + 0)) : mword 64)).
    { rewrite (_ : T2 !!! Regidx Rs1 = (S6 !!! Regidx Rs1 : mword 64));
        [exact HS6s1 | lkp]. }
    (* ================================================================ *)
    (*  +0x34 ONWARDS, entered from BOTH arms of the clamp.  Only the    *)
    (*  register file and the clamped count travel.                      *)
    (* ================================================================ *)
    iAssert (∀ (CIDt : CpuId) (Mt : regfile) (nc : nat),
        rd_readtail_body j b K m ip dn off n szn CIDs5 CIDt Mt nc)%I
      with "[Hcnt Hextc Hextm Hcont Hframe Hidev Hmeta Hmap Hblocks
             Hdst Hsl]" as "TAIL".
    { iIntros (CIDt Mt nc) "%Hanch %Hncdef %Hncn %Hoffnc %Htsp %Hts5 %Hts6 %Hts7
                            %Hts4 %Hts1 %Hts2 %Hts8 %Hts9 %Hts10 %Hts11 Hcg Hpc".
      destruct (Nat.eqb_spec nc 0) as [Hn0 | Hnne].
      { (* ---------- nc = 0: nothing to read ---------- *)
        (* NOT [subst nc] -- [Hncdef] would win and replace [nc] by
           [rd_clamp …] rather than by 0. *)
        rewrite Hn0 in Hts5 Hncdef.
        iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (RI + 0x34))
                  (mword_of_int 150 : mword 13) Rs5 Mt (K - 14)%nat b ltac:(nz)
                  ltac:(rgne; rewrite Hts5;
                        rewrite (bc_eqz_moi 0%nat ltac:(lia)); reflexivity)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi34").
        iApply bi.later_intro. iIntros (CIDz1 Hqz1) "Hcg Hpc".
        assert (Htgtca : add_vec (mword_of_int (RI + 0x34) : mword 64)
                  (sign_extend' 64 (mword_of_int 150 : mword 13))
                = mword_of_int (RI + 0xca)) by pcw.
        iEval (rewrite Htgtca) in "Hpc".
        (* ===== +0xca c.mv s3,s5 : tot := nc = 0 ===== *)
        iApply (wp_cmv_s_sconf (mword_of_int (RI + 0xca)) Rs3 Rs5
                  Mt (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hica").
        iIntros (CIDz2 Hqz2) "Hcg Hpc".
        set (Z1 := <[Regidx Rs3 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (rget Mt Rs5))]> Mt).
        assert (HZ1s3 : Z1 !!! Regidx Rs3
                        = (mword_of_int (Z.of_nat 0%nat) : mword 64)).
        { rewrite /Z1 upd_eq. rgne. rewrite Hts5. apply add_vec_zero_l. }
        assert (HZ1sp : rd_sp m Z1)
          by (rewrite /rd_sp /Z1 upd_ne; [exact Htsp | nz]).
        assert (HZ1s2 : Z1 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
          by (rewrite /Z1 upd_ne; [exact Hts2 | nz]).
        assert (HZ1s8 : Z1 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
          by (rewrite /Z1 upd_ne; [exact Hts8 | nz]).
        assert (HZ1s9 : Z1 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
          by (rewrite /Z1 upd_ne; [exact Hts9 | nz]).
        assert (HZ1s10 : Z1 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
          by (rewrite /Z1 upd_ne; [exact Hts10 | nz]).
        assert (HZ1s11 : Z1 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
          by (rewrite /Z1 upd_ne; [exact Hts11 | nz]).
        assert (Hpp : add_vec_int (mword_of_int (RI + 0xca) : mword 64) 2
                      = mword_of_int (RI + 0xcc)) by pcw.
        iEval (rewrite Hpp) in "Hpc". clear Hpp.
        (* ===== +0xcc c.j +0xd8 ===== *)
        iApply (wp_cj_s_sconf (mword_of_int (RI + 0xcc))
                  (sign_extend' 21 (concat_vec (mword_of_int 6 : mword 11) ('b"0")))
                  Z1 (K - 14)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hicc").
        iIntros (CIDz3 Hqz3). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Htgtd8 : add_vec (mword_of_int (RI + 0xcc) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 6 : mword 11) ('b"0"))))
                = mword_of_int (RI + 0xd8)) by pcw.
        iEval (rewrite Htgtd8) in "Hpc".
        iDestruct (cpu_own_transport CID CIDz3 0 eb (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CID CIDz3 eb (proc_addr j)
                     ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CID CIDz3 eb (proc_addr j)
                     ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
        iApply (rd_join (CID0 := CIDz3)  γfs bn γf dev ip bm data dn
                  user off n 0%nat dst_olds V (pv_upt V)
                  (mword_of_int (Z.of_nat 0%nat) : mword 64)
                  pidv dq dqd j m Z1 K eb b lks
                  HK HZ1sp HZ1s3 HZ1s2 HZ1s8 HZ1s9 HZ1s10 HZ1s11
                  ltac:(apply uptd_ext_refl) ltac:(lia)
                  ltac:(right; split; [reflexivity | exact Hncdef])
                  with "Hcg Hcnt Hextc Hextm Htext Hpc Hframe Hidev
                        Hmeta Hmap Hblocks Hdst Hsl [Hcont]").
        iApply (wp_next_shift (b := true) (CIDa := CID) (CIDb := CIDz3) ltac:(wp_next_chain)
                  with "Hcont"). }
      (* ---------- nc <> 0: save the other five and enter the loop ------- *)
      iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (RI + 0x34))
                (mword_of_int 150 : mword 13) Rs5 Mt (K - 14)%nat b ltac:(nz)
                ltac:(rgne; rewrite Hts5; rewrite (bc_eqz_moi nc ltac:(lia));
                      apply Nat.eqb_neq; exact Hnne)
                with "Hcg Hpc Hi34").
      iIntros (CIDp13 Hqp13) "Hcg Hpc".
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x34) : mword 64) 4
                    = mword_of_int (RI + 0x38)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      rewrite /rd_fr8.
      iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                              & HfA & HfB & HfC & HfD & HfE)".
      (* ===== +0x38 sd s2,80(sp) ===== *)
      iDestruct "Hf4" as (v4) "Hf4".
      assert (Hd4 : add_vec (Mt !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
      { rewrite Htsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try pcw. }
      iEval (rewrite -Hd4) in "Hf4".
      iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x38)) (mword_of_int 10 : mword 6) Rs2
                Mt (K - 14)%nat v4 b with "Hcg Hpc Hi38 Hf4").
      iIntros (CIDu1 Hqu1) "Hcg Hpc Hf4".
      iEval (rewrite Hd4) in "Hf4".
      first [ iEval (rewrite Hts2) in "Hf4" | iEval (rgne; rewrite Hts2) in "Hf4" ].
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x38) : mword 64) 2
                    = mword_of_int (RI + 0x3a)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x3a sd s8,32(sp) ===== *)
      iDestruct "HfA" as (v10) "HfA".
      assert (Hd10 : add_vec (Mt !!! Regidx csp_rs1 : mword 64)
                       (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                     = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
      { rewrite Htsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try pcw. }
      iEval (rewrite -Hd10) in "HfA".
      iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x3a)) (mword_of_int 4 : mword 6) Rs8
                Mt (K - 14)%nat v10 b with "Hcg Hpc Hi3a HfA").
      iIntros (CIDu2 Hqu2) "Hcg Hpc HfA".
      iEval (rewrite Hd10) in "HfA".
      first [ iEval (rewrite Hts8) in "HfA" | iEval (rgne; rewrite Hts8) in "HfA" ].
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x3a) : mword 64) 2
                    = mword_of_int (RI + 0x3c)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x3c sd s9,24(sp) ===== *)
      iDestruct "HfB" as (v11) "HfB".
      assert (Hd11 : add_vec (Mt !!! Regidx csp_rs1 : mword 64)
                       (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                     = pa_stk (m !!! Regidx csp_rs1 : mword 64) 11).
      { rewrite Htsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try pcw. }
      iEval (rewrite -Hd11) in "HfB".
      iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x3c)) (mword_of_int 3 : mword 6) Rs9
                Mt (K - 14)%nat v11 b with "Hcg Hpc Hi3c HfB").
      iIntros (CIDu3 Hqu3) "Hcg Hpc HfB".
      iEval (rewrite Hd11) in "HfB".
      first [ iEval (rewrite Hts9) in "HfB" | iEval (rgne; rewrite Hts9) in "HfB" ].
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x3c) : mword 64) 2
                    = mword_of_int (RI + 0x3e)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x3e sd s10,16(sp) ===== *)
      iDestruct "HfC" as (v12) "HfC".
      assert (Hd12 : add_vec (Mt !!! Regidx csp_rs1 : mword 64)
                       (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                     = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12).
      { rewrite Htsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try pcw. }
      iEval (rewrite -Hd12) in "HfC".
      iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x3e)) (mword_of_int 2 : mword 6) Rs10
                Mt (K - 14)%nat v12 b with "Hcg Hpc Hi3e HfC").
      iIntros (CIDu4 Hqu4) "Hcg Hpc HfC".
      iEval (rewrite Hd12) in "HfC".
      first [ iEval (rewrite Hts10) in "HfC" | iEval (rgne; rewrite Hts10) in "HfC" ].
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x3e) : mword 64) 2
                    = mword_of_int (RI + 0x40)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x40 sd s11,8(sp) ===== *)
      iDestruct "HfD" as (v13) "HfD".
      assert (Hd13 : add_vec (Mt !!! Regidx csp_rs1 : mword 64)
                       (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                     = pa_stk (m !!! Regidx csp_rs1 : mword 64) 13).
      { rewrite Htsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try pcw. }
      iEval (rewrite -Hd13) in "HfD".
      iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (RI + 0x40)) (mword_of_int 1 : mword 6) Rs11
                Mt (K - 14)%nat v13 b with "Hcg Hpc Hi40 HfD").
      iIntros (CIDu5 Hqu5) "Hcg Hpc HfD".
      iEval (rewrite Hd13) in "HfD".
      first [ iEval (rewrite Hts11) in "HfD" | iEval (rgne; rewrite Hts11) in "HfD" ].
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x40) : mword 64) 2
                    = mword_of_int (RI + 0x42)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x42 c.li s3,0 ===== *)
      iApply (wp_cli_s_sconf (mword_of_int (RI + 0x42)) Rs3
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                Mt (K - 14)%nat b ltac:(nz) ltac:(rdok) rd_li_0 with "Hcg Hpc Hi42").
      iIntros (CIDu6 Hqu6) "Hcg Hpc".
      set (U1 := <[Regidx Rs3 := regval_into_reg (mword_of_int 0 : mword 64)]> Mt).
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x42) : mword 64) 2
                    = mword_of_int (RI + 0x44)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x44 li s9,1024 ===== *)
      iApply (wp_li4_s_sconf (mword_of_int (RI + 0x44)) Rs9
                (mword_of_int 1024 : mword 12) (mword_of_int 1024 : mword 64)
                U1 (K - 14)%nat b ltac:(nz) ltac:(rdok) rd_li_1024
                with "Hcg Hpc Hi44").
      iIntros (CIDu7 Hqu7) "Hcg Hpc".
      set (U2 := <[Regidx Rs9 := regval_into_reg (mword_of_int 1024 : mword 64)]> U1).
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x44) : mword 64) 4
                    = mword_of_int (RI + 0x48)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x48 c.li s8,-1 ===== *)
      iApply (wp_cli_s_sconf (mword_of_int (RI + 0x48)) Rs8
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                U2 (K - 14)%nat b ltac:(nz) ltac:(rdok) rd_li_m1 with "Hcg Hpc Hi48").
      iIntros (CIDu8 Hqu8) "Hcg Hpc".
      set (U3 := <[Regidx Rs8 := regval_into_reg (mword_of_int (-1) : mword 64)]> U2).
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x48) : mword 64) 2
                    = mword_of_int (RI + 0x4a)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x4a c.j +0x7c : into the loop head ===== *)
      iApply (wp_cj_s_sconf (mword_of_int (RI + 0x4a))
                (sign_extend' 21 (concat_vec (mword_of_int 25 : mword 11) ('b"0")))
                U3 (K - 14)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi4a").
      iIntros (CIDu9 Hqu9). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgt7c : add_vec (mword_of_int (RI + 0x4a) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 25 : mword 11) ('b"0"))))
              = mword_of_int (RI + 0x7c)) by pcw.
      iEval (rewrite Htgt7c) in "Hpc".
      iAssert (rd_fr13 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
        as "Hframe".
      { rewrite /rd_fr13.
        iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
        iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
        iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
        iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
        iSplitL "Hf9"; [iExact "Hf9"|]. iSplitL "HfA"; [iExact "HfA"|].
        iSplitL "HfB"; [iExact "HfB"|]. iSplitL "HfC"; [iExact "HfC"|].
        iSplitL "HfD"; [iExact "HfD"|]. iExact "HfE". }
      assert (HU3sp : rd_sp m U3) by (rewrite /rd_sp; lkp).
      assert (HU3s6 : U3 !!! Regidx Rs6 = ip) by lkp.
      assert (HU3s7 : U3 !!! Regidx Rs7 = (m !!! Regidx Ra1 : mword 64)) by lkp.
      assert (HU3s4 : U3 !!! Regidx Rs4
                      = pa_add (m !!! Regidx Ra2 : mword 64) 0%nat).
      { rewrite (_ : U3 !!! Regidx Rs4 = (Mt !!! Regidx Rs4 : mword 64));
          [exact Hts4 | lkp]. }
      assert (HU3s1 : U3 !!! Regidx Rs1
                      = (mword_of_int (Z.of_nat (off + 0)) : mword 64)).
      { rewrite (_ : U3 !!! Regidx Rs1 = (Mt !!! Regidx Rs1 : mword 64));
          [exact Hts1 | lkp]. }
      assert (HU3s5 : U3 !!! Regidx Rs5
                      = (mword_of_int (Z.of_nat nc) : mword 64)).
      { rewrite (_ : U3 !!! Regidx Rs5 = (Mt !!! Regidx Rs5 : mword 64));
          [exact Hts5 | lkp]. }
      assert (HU3s3 : U3 !!! Regidx Rs3
                      = (mword_of_int (Z.of_nat 0%nat) : mword 64)) by lkp.
      assert (HU3s9 : U3 !!! Regidx Rs9 = (mword_of_int 1024 : mword 64)) by lkp.
      assert (HU3s8 : U3 !!! Regidx Rs8 = (mword_of_int (-1) : mword 64)) by lkp.
      iDestruct (cpu_own_transport CID CIDu9 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID CIDu9 eb (proc_addr j)
                   ltac:(rewrite Heb2b; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CIDu9 eb (proc_addr j)
                   ltac:(rewrite Heb2b; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CIDu9) ltac:(wp_next_chain)
                   with "Hcont") as "Hcont".
      iApply (rd_loop (CID0 := CIDu9)  γs j γl γu γd γk pd pav pu γfs bn γf γa
                cov logstart dev ip bm data dn user off n nc szn dst_olds V
                (m !!! Regidx Ra1 : mword 64) pidv dq dqd m K eb b lks
                HK Hgeom0 Hwf Hcov Hsznmax
                ltac:(change (2 ^ 32)%Z with 4294967296%Z; exact Hsum)
                Hncn Hoffnc Hncdef Ha1 Hj Hgl Hbelow
                (rd_blocks off nc) 0%nat (pv_upt V) U3
                ltac:(lia) ltac:(apply uptd_ext_refl)
                ltac:(replace (off + 0)%nat with off by lia;
                      replace (nc - 0)%nat with nc by lia; lia)
                HU3sp HU3s6 HU3s7 HU3s4 HU3s1 HU3s5 HU3s3 HU3s9 HU3s8
                with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hkenv Hprocs
                      Hdevi Hdgeom Hdlock Hframe Hidev
                      Hmeta Hmap Hblocks Hdst Hsl Hcont"). }
    (* ===== +0x2c bgeu a5,a4 : does the read fit inside the file? ===== *)
    destruct (Nat.leb_spec (off + n) szn) as [Hge | Hlt].
    - (* ---------- it does: no clamp, nc = n ---------- *)
      assert (Hclampn : rd_clamp (di_size dn) off n = n).
      { rewrite /rd_clamp -Hszne. case_decide as Hd; [exfalso; lia | reflexivity]. }
      (* the count survives unclamped, so it is at most the size and s5's
         ABI word is the literal the tail counts in *)
      assert (HT2s5' : T2 !!! Regidx Rs5
                       = (mword_of_int (Z.of_nat n) : mword 64))
        by (rewrite HT2s5; apply rd_sext32; lia).
      (* the sum is at most the size, hence below 2^31, hence not
         sign-extended: [w32_uarg_le] *)
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (RI + 0x2c))
                (mword_of_int 8 : mword 13) Ra4 Ra5 T2 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HT2a5 HT2a4; apply bc_geu;
                      rewrite Hszu Hsumu; apply w32_uarg_le; lia)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi2c").
      iApply bi.later_intro. iIntros (CIDv1 Hqv1) "Hcg Hpc".
      assert (Htgt34 : add_vec (mword_of_int (RI + 0x2c) : mword 64)
                (sign_extend' 64 (mword_of_int 8 : mword 13))
              = mword_of_int (RI + 0x34)) by pcw.
      iEval (rewrite Htgt34) in "Hpc".
      iApply ("TAIL" $! CIDv1 T2 n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc");
        [ wp_next_chain | symmetry; exact Hclampn | lia | lia | exact HT2sp
        | exact HT2s5' | exact HT2s6 | exact HT2s7 | exact HT2s4 | exact HT2s1
        | lkp | lkp | lkp | lkp | lkp ].
    - (* ---------- it does not: n := ip->size - off ---------- *)
      assert (Hclamps : rd_clamp (di_size dn) off n = (szn - off)%nat).
      { rewrite /rd_clamp -Hszne. case_decide as Hd; [reflexivity | exfalso; lia]. }
      (* the sum is past the end of the file, and a sum past 2^31 is past it
         as an unsigned word too: [w32_uarg_gt] *)
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (RI + 0x2c))
                (mword_of_int 8 : mword 13) Ra4 Ra5 T2 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HT2a5 HT2a4; apply bc_ltu;
                      rewrite Hszu Hsumu; apply w32_uarg_gt; lia)
                with "Hcg Hpc Hi2c").
      iIntros (CIDv1 Hqv1) "Hcg Hpc".
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x2c) : mword 64) 4
                    = mword_of_int (RI + 0x30)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0x30 subw s5,a5,a3 : n := ip->size - off ===== *)
      iApply (wp_subw_s_sconf (mword_of_int (RI + 0x30)) Rs5 Ra5 Ra3
                T2 (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi30").
      iIntros (CIDv2 Hqv2) "Hcg Hpc".
      set (U0 := <[Regidx Rs5 := regval_into_reg
                    (sign_extend' 64
                      (sub_vec (subrange_vec_dec (rget T2 Ra5) 31 0 : mword 32)
                               (subrange_vec_dec (rget T2 Ra3) 31 0 : mword 32)))]> T2).
      assert (HU0s5 : U0 !!! Regidx Rs5
                      = (mword_of_int (Z.of_nat (szn - off)) : mword 64)).
      { rewrite /U0 upd_eq. rgne; rgne. rewrite HT2a5 HT2a3.
        rewrite (rd_subw (Z.of_nat szn) (Z.of_nat off)
                   ltac:(lia) ltac:(lia) ltac:(lia)).
        rewrite Nat2Z.inj_sub; [reflexivity | lia]. }
      assert (HU0sp : rd_sp m U0)
        by (rewrite /rd_sp /U0 upd_ne; [exact HT2sp | nz]).
      assert (HU0s6 : U0 !!! Regidx Rs6 = ip)
        by (rewrite /U0 upd_ne; [exact HT2s6 | nz]).
      assert (HU0s7 : U0 !!! Regidx Rs7 = (m !!! Regidx Ra1 : mword 64))
        by (rewrite /U0 upd_ne; [exact HT2s7 | nz]).
      assert (HU0s4 : U0 !!! Regidx Rs4
                      = pa_add (m !!! Regidx Ra2 : mword 64) 0%nat)
        by (rewrite /U0 upd_ne; [exact HT2s4 | nz]).
      assert (HU0s1 : U0 !!! Regidx Rs1
                      = (mword_of_int (Z.of_nat (off + 0)) : mword 64))
        by (rewrite /U0 upd_ne; [exact HT2s1 | nz]).
      assert (Hpp : add_vec_int (mword_of_int (RI + 0x30) : mword 64) 4
                    = mword_of_int (RI + 0x34)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      iApply ("TAIL" $! CIDv2 U0 (szn - off)%nat with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hpc");
        [ wp_next_chain | symmetry; exact Hclamps | lia | lia | exact HU0sp
        | exact HU0s5 | exact HU0s6 | exact HU0s7 | exact HU0s4 | exact HU0s1
        | lkp | lkp | lkp | lkp | lkp ].
  Qed.

End ReadiMain.

End ReadiProof.
