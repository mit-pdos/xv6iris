(* ProofWritei.v -- writei over the SIE-agnostic sconf world.

     int writei(struct inode *ip, int user_src, uint64 src, uint off, uint n)
     {
       uint tot, m;  struct buf *bp;
       if(off > ip->size || off + n < off)  return -1;
       if(off + n > MAXFILE*BSIZE)          return -1;
       for(tot = 0; tot < n; tot += m, off += m, src += m){
         uint addr = bmap(ip, off/BSIZE);
         if(addr == 0) break;
         bp = bread(ip->dev, addr);
         m = min(n - tot, BSIZE - off%BSIZE);
         if(either_copyin(bp->data + (off % BSIZE), user_src, src, m) == -1) {
           log_write(bp);  brelse(bp);  break; }
         log_write(bp);  brelse(bp);
       }
       if(off > ip->size) ip->size = off;
       iupdate(ip);
       return tot;
     }

   THE SHAPE OF THE PROOF.  Five lemmas, entered strictly right to left in
   the file and left to right at run time:

     [wi_ret]   +0xdc .. +0xec   pop the seven unconditionally-saved
                                 registers, ret, discharge the contract.
                                 BOTH the -1 arm (which reaches it through
                                 +0x102) and the normal arm end here.
     [wi_join]  +0xd2 .. +0xda   iupdate, a0 := tot, restore s3.  THREE
                                 paths join here.
     [wi_size]  +0xbc .. +0xd0   the size test, the store, and the five
                                 conditional restores (+0xc8 / +0xf2).
     [wi_loop]  +0x82 .. +0xb8   the loop HEAD, and the BODY at +0x4c that
                                 precedes it in address order.  Fuel
                                 induction on the bytes left to copy.  The
                                 partial-copy break path at +0xb0 now calls
                                 log_write BEFORE brelse (see the source
                                 above), so this lemma -- which is not yet
                                 written -- owes that call site a second
                                 application of log_write's spec.
     [wp_writei_sconf]           +0x00 .. +0x4a, the two -1 exits, the
                                 n = 0 arm at +0xee.

   EVERY CALLEE-SAVED REGISTER IS SAVED, so there is no register-threading
   invariant at all: [callee_saved m mf] falls out of the thirteen restores
   plus the [addi sp,sp,112].  What replaces it is the FRAME, in three
   strengths -- [wi_fr7] (the seven unconditional slots pinned, the other
   seven anonymous), [wi_fr8] (s3's slot pinned too, after +0x032) and
   [wi_fr13] (all thirteen, inside the loop).  bmap's s4 lesson applies
   verbatim: every restore precedes the join at +0xcc, so the three paths
   reach it with s1/s3/s8..s11 at their entry values -- the n = 0 arm
   because it never wrote them, the other two because they restored them.

   THE PRE-FRAME EXIT at +0x000..+0x002 is the one genuinely new shape in
   the layer: it tests [off > ip->size] and leaves through a bare
   [li a0,-1; ret] at +0xfe BEFORE the prologue has run, so it holds no
   frame at all and [callee_saved] is established from the two
   caller-saved writes (a5 and a0) alone.

   THE COUPLING THAT MAKES THE LOOP WORK is [wi_held_content]: the block's
   own [fsblock] half, borrowed out of [inode_blocks] with
   [inode_blocks_acc], against the bio handle's machinery half pins the
   buffer's bytes to [data_c fbn].  The copy then splices [m] bytes into
   that list ([wi_splice]) and log_write re-indexes the payload at the
   result, which is exactly one step of the postcondition's range clause
   ([wi_file_byte_splice]). *)
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
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import WpLock.
Require Import SleepLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfVc.
Require Import WpSconfSrliw.
Require Import WpSmodeIntr.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FileInv ProcInv.
Require Import CodeWritei.
Require Import SpecPanic.
Require Import SpecBmap SpecBread SpecBrelse SpecLogWrite SpecEitherCopyin
        SpecIupdate.
Require Import ProofWriteiParts.
Require Import SpecWritei.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  !!! THIS PROOF IS INCOMPLETE, AND THE REASON IS A REAL DEFECT IN THE  *)
(*  !!! CODE, NOT A GAP IN THE PROOF.  The module is therefore NOT sealed *)
(*  !!! against [WRITEI] and there is no LinkWritei.v.                     *)
(*                                                                        *)
(*  THE BLOCKER: the [either_copyin == -1] break at +0x064 -> +0x0b0 does *)
(*                                                                        *)
(*      brelse(bp);  break;                                               *)
(*                                                                        *)
(*  WITHOUT calling log_write first.  By then either_copyin may already   *)
(*  have copied a PREFIX of the user bytes into bp->data (copyin walks    *)
(*  the source page by page and returns -1 on the first page it cannot    *)
(*  reach, having memmove'd every earlier one), so the buffer's bytes are *)
(*  no longer the block's logical content.                                *)
(*                                                                        *)
(*  [SpecBrelse] takes [bio_locked bn V k pidv dev bno bs bsd d], which   *)
(*  is [bio_held ... bs bs bsd d] -- the traveling bytes MUST equal the   *)
(*  payload's logical content, and that is the park swap's whole          *)
(*  obligation.  Re-indexing the payload is [FsBlocks.fsblock_update],    *)
(*  which needs [ghost_map_auth (fs_L γ)] -- the log lock's authority,    *)
(*  reachable only through log_write, which this path does not call.      *)
(*  So the arm cannot be discharged, and it is not dead: on the USER arm  *)
(*  [either_copyin_post] gives [r = 0 \/ r = -1] with the destination     *)
(*  bytes existential on both outcomes.                                   *)
(*                                                                        *)
(*  It is not a modelling artefact either.  A buffer released with        *)
(*  unlogged modifications stays in the bcache holding bytes that were    *)
(*  never committed: a later readi of that block returns them, and a      *)
(*  crash discards them.  That is exactly the inconsistency the bio       *)
(*  layer's [bio_locked] obligation exists to exclude.                    *)
(*                                                                        *)
(*  WHAT IS PROVED BELOW is the whole of writei from +0x0b6 on -- the     *)
(*  size test, the five conditional restores, iupdate, and the return --  *)
(*  i.e. everything the loop's exits feed.  See the report for the        *)
(*  remaining design (the fuel induction, the budget arithmetic and the   *)
(*  per-iteration resource flow are all worked out; only this one arm is  *)
(*  unobtainable).                                                        *)
(* ===================================================================== *)
Module WriteiProof (BM : BMAP) (BR : BREAD) (BL : BRELSE) (LW : LOG_WRITE)
                   (EC : EITHER_COPYIN) (IU : IUPDATE).

Notation WI := KernelSyms.writei.

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
Local Ltac widx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  Vocabulary: the frame in three strengths, and the continuation.       *)
(* ===================================================================== *)
Section WriteiDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* writei's 112-byte frame.  Slot k sits at [sp0 - 8k], i.e. at
     [sp_new + (112 - 8k)]:
       1 ra@104   2 s0@96   3 s1@88   4 s2@80   5 s3@72   6 s4@64
       7 s5@56    8 s6@48   9 s7@40  10 s8@32  11 s9@24  12 s10@16
      13 s11@8   14 (offset 0, never written)                          *)

  (* the SEVEN unconditional saves (+0x008..+0x014), which is all the join
     at +0xd6 may assume: the other seven slots are written only on the
     paths that got that far. *)
  Definition wi_fr7 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ v) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ v) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈ (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈ (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈ (m !!! Regidx Rs7 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈ v))%I.

  (* ...plus s3's slot, pinned from +0x032 to the [c.ldsp s3] at +0xd4 *)
  Definition wi_fr8 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ v) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈ (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈ (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈ (m !!! Regidx Rs7 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈ v))%I.

  (* ...and all thirteen, which is what the loop holds (+0x038..+0x040) *)
  Definition wi_fr13 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈ (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈ (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈ (m !!! Regidx Rs7 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈ (m !!! Regidx Rs8 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 11 ↦₈ (m !!! Regidx Rs9 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 12 ↦₈ (m !!! Regidx Rs10 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 13 ↦₈ (m !!! Regidx Rs11 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 14 ↦₈ v))%I.

  Lemma wi_fr7_of8 (m : regfile) : wi_fr8 m -∗ wi_fr7 m.
  Proof.
    rewrite /wi_fr8 /wi_fr7.
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HA & HB & HC & HD & HE)".
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExists _; iExact "H5"|].
    iSplitL "H6"; [iExact "H6"|]. iSplitL "H7"; [iExact "H7"|].
    iSplitL "H8"; [iExact "H8"|]. iSplitL "H9"; [iExact "H9"|].
    iSplitL "HA"; [iExact "HA"|]. iSplitL "HB"; [iExact "HB"|].
    iSplitL "HC"; [iExact "HC"|]. iSplitL "HD"; [iExact "HD"|]. iExact "HE".
  Qed.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition wi_cont `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γfs : fs_names) (bn : bio_names) (γ : log_names) (γf : gname)
      (cov : gset Z) (logstart inodestart : Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn : dinode) (ds : list dinode)
      (user : bool) (off n : nat) (src_bytes : nat -> bv 8)
      (V : pprivate) (ncount : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (tot : nat) (bm' : blkmap) (data' : nat -> list (bv 8))
        (dn' : dinode) (ds' : list dinode) (n' : nat)
        (wrote : nat -> bv 8) (P' : uptd),
        ⌜callee_saved m mf⌝ -∗
        ⌜blkmap_wf cov logstart bm'⌝ -∗
        ⌜blk_holes_zero bm' data'⌝ -∗
        ⌜diblk_wf ds'⌝ -∗
        ⌜di_addrs dn' = bm_cells bm'⌝ -∗
        ⌜bv_unsigned (di_size dn') < 2 ^ 31⌝ -∗
        ⌜forall k : nat,
           file_byte data' k
           = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
             then wrote (k - off)%nat
             else file_byte data k⌝ -∗
        ⌜user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i⌝ -∗
        ⌜(mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)
          /\ (bv_unsigned (di_size dn) < Z.of_nat off
              \/ (MAXFILE * BSIZE < off + n)%nat)
          /\ tot = 0%nat /\ bm' = bm /\ data' = data /\ dn' = dn /\ ds' = ds
          /\ n' = ncount)
         \/ (mf !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)
             /\ (tot <= n)%nat
             /\ dn' = wi_dinode dn bm' off tot
             /\ ds' = <[islot inum := dn']> ds)⌝ -∗
        ⌜((ncount - wi_cost off n)%nat <= n')%nat /\ (n' <= ncount)%nat⌝ -∗
        ⌜uptd_ext (pv_upt V) P'⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        own_ctx (p_context (proc_addr j)) -∗
        park_hlf j true -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        i_dev ip ↦₄{dqd} dev -∗
        i_inum ip ↦₄{dqn} inum -∗
        inode_meta ip dn' -∗
        inode_map γfs ip bm' -∗
        inode_blocks γfs bm' data' -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds') -∗
        (if user
         then proc_priv γf (proc_addr j) pidv (upd_upt V P')
         else [∗ list] i ∈ seq 0 n,
                pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ (src_bytes i)) -∗
        bslots bn 3 -∗
        log_op γ n' -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I.

End WriteiDefs.

(* the sp relation: inside the frame sp is 112 below its entry value *)
Definition wi_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 57 : mword 6))).

(* ===================================================================== *)
(*  +0xd6 .. +0xe6 : THE RETURN.                                          *)
(* ===================================================================== *)
Section WriteiRet.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Local Lemma wi_ret `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γfs : fs_names) (bn : bio_names) (γ : log_names) (γf : gname)
      (cov : gset Z) (logstart inodestart : Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm bm' : blkmap) (data data' : nat -> list (bv 8))
      (dn dn' : dinode) (ds ds' : list dinode)
      (user : bool) (off n tot : nat) (src_bytes wrote : nat -> bv 8)
      (V : pprivate) (P' : uptd) (ncount n' : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac) (j : nat)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_writei <= K)%nat ->
    wi_sp m M ->
    (* the six registers this block does NOT restore are already back *)
    M !!! Regidx Rs1  = (m !!! Regidx Rs1  : mword 64) ->
    M !!! Regidx Rs3  = (m !!! Regidx Rs3  : mword 64) ->
    M !!! Regidx Rs8  = (m !!! Regidx Rs8  : mword 64) ->
    M !!! Regidx Rs9  = (m !!! Regidx Rs9  : mword 64) ->
    M !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64) ->
    M !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64) ->
    (* ...and the answer is in a0 *)
    blkmap_wf cov logstart bm' ->
    blk_holes_zero bm' data' ->
    diblk_wf ds' ->
    di_addrs dn' = bm_cells bm' ->
    bv_unsigned (di_size dn') < 2 ^ 31 ->
    (forall k : nat,
       file_byte data' k
       = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
         then wrote (k - off)%nat else file_byte data k) ->
    (user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i) ->
    ((M !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)
      /\ (bv_unsigned (di_size dn) < Z.of_nat off
          \/ (MAXFILE * BSIZE < off + n)%nat)
      /\ tot = 0%nat /\ bm' = bm /\ data' = data /\ dn' = dn /\ ds' = ds
      /\ n' = ncount)
     \/ (M !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)
         /\ (tot <= n)%nat
         /\ dn' = wi_dinode dn bm' off tot
         /\ ds' = <[islot inum := dn']> ds)) ->
    ((ncount - wi_cost off n)%nat <= n')%nat -> (n' <= ncount)%nat ->
    uptd_ext (pv_upt V) P' ->
    sie_cap_gpr M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (WI + 0xdc) : mword 64) -∗
    wi_fr7 m -∗
    own_ctx (p_context (proc_addr j)) -∗
    park_hlf j true -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn' -∗
    inode_map γfs ip bm' -∗
    inode_blocks γfs bm' data' -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds') -∗
    (if user
     then proc_priv γf (proc_addr j) pidv (upd_upt V P')
     else [∗ list] i ∈ seq 0 n,
            pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ (src_bytes i)) -∗
    bslots bn 3 -∗
    log_op γ n' -∗
    wi_cont (CID0 := CID0) Φ γfs bn γ γf cov logstart inodestart dev ip inum
            bm data dn ds user off n src_bytes V ncount pidv dq dqd dqn dqs j
            m K C b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hsp Hs1 Hs3 Hs8 Hs9 Hs10 Hs11
           Hwf' Hhz' Hdswf' Hadr' Hsz' Hrange Hker Harm Hlo Hhi Hext.
    pose proof HK as HK'. unfold K_writei in HK'.
    iIntros "Hcg Hcnt #Htext Hpc Hframe Hoctx Hpark Hppid Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hfsb Hsrc Hsl Hop Hcont".
    iPoseProof (wri_dc with "Htext") as "Hidc".
    iPoseProof (wri_de with "Htext") as "Hide".
    iPoseProof (wri_e0 with "Htext") as "Hie0".
    iPoseProof (wri_e2 with "Htext") as "Hie2".
    iPoseProof (wri_e4 with "Htext") as "Hie4".
    iPoseProof (wri_e6 with "Htext") as "Hie6".
    iPoseProof (wri_e8 with "Htext") as "Hie8".
    iPoseProof (wri_ea with "Htext") as "Hiea".
    iPoseProof (wri_ec with "Htext") as "Hiec".
    rewrite /wi_fr7.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    (* the seven loaded slots, at the addresses the [c.ldsp]s form *)
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
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
    (* ===== +0xd6 c.ldsp ra,104(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xdc)) (mword_of_int 13 : mword 6) Rra
              M (K - 14)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hidc [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1sp : wi_sp m P1)
      by (rewrite /wi_sp /P1 upd_ne; [exact Hsp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xdc) : mword 64) 2
                  = mword_of_int (WI + 0xde)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xd8 c.ldsp s0,96(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xde)) (mword_of_int 12 : mword 6) Rs0
              P1 (K - 14)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hide [Hf2]").
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : wi_sp m P2)
      by (rewrite /wi_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xde) : mword 64) 2
                  = mword_of_int (WI + 0xe0)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xda c.ldsp s2,80(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xe0)) (mword_of_int 10 : mword 6) Rs2
              P2 (K - 14)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie0 [Hf4]").
    { iEval (rewrite HP2sp -Hsp Hc4). iExact "Hf4". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf4".
    iEval (rewrite HP2sp -Hsp Hc4) in "Hf4".
    set (P3 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P2).
    assert (HP3sp : wi_sp m P3)
      by (rewrite /wi_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe0) : mword 64) 2
                  = mword_of_int (WI + 0xe2)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xdc c.ldsp s4,64(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xe2)) (mword_of_int 8 : mword 6) Rs4
              P3 (K - 14)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie2 [Hf6]").
    { iEval (rewrite HP3sp -Hsp Hc6). iExact "Hf6". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf6".
    iEval (rewrite HP3sp -Hsp Hc6) in "Hf6".
    set (P4 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P3).
    assert (HP4sp : wi_sp m P4)
      by (rewrite /wi_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe2) : mword 64) 2
                  = mword_of_int (WI + 0xe4)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xde c.ldsp s5,56(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xe4)) (mword_of_int 7 : mword 6) Rs5
              P4 (K - 14)%nat (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie4 [Hf7]").
    { iEval (rewrite HP4sp -Hsp Hc7). iExact "Hf7". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf7".
    iEval (rewrite HP4sp -Hsp Hc7) in "Hf7".
    set (P5 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P4).
    assert (HP5sp : wi_sp m P5)
      by (rewrite /wi_sp /P5 upd_ne; [exact HP4sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe4) : mword 64) 2
                  = mword_of_int (WI + 0xe6)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe0 c.ldsp s6,48(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xe6)) (mword_of_int 6 : mword 6) Rs6
              P5 (K - 14)%nat (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie6 [Hf8]").
    { iEval (rewrite HP5sp -Hsp Hc8). iExact "Hf8". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf8".
    iEval (rewrite HP5sp -Hsp Hc8) in "Hf8".
    set (P6 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P5).
    assert (HP6sp : wi_sp m P6)
      by (rewrite /wi_sp /P6 upd_ne; [exact HP5sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe6) : mword 64) 2
                  = mword_of_int (WI + 0xe8)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe2 c.ldsp s7,40(sp) ===== *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xe8)) (mword_of_int 5 : mword 6) Rs7
              P6 (K - 14)%nat (m !!! Regidx Rs7 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hie8 [Hf9]").
    { iEval (rewrite HP6sp -Hsp Hc9). iExact "Hf9". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf9".
    iEval (rewrite HP6sp -Hsp Hc9) in "Hf9".
    set (P7 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> P6).
    assert (HP7sp : wi_sp m P7)
      by (rewrite /wi_sp /P7 upd_ne; [exact HP6sp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xe8) : mword 64) 2
                  = mword_of_int (WI + 0xea)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe4 c.addi16sp sp,112 : pop ===== *)
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
    iAssert (stack_own (m !!! Regidx csp_rs1 : mword 64) 14)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]" as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1"|].
      iSplitL "Hf2"; [iExists _; iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|].
      iSplitL "Hf4"; [iExists _; iExact "Hf4"|].
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
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (WI + 0xea))
              (mword_of_int 7 : mword 6) P7 (K - 14)%nat 14 b Hpop
              with "Hcg Hpc Hiea Hstk").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (P8 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P7 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 7 : mword 6))))]> P7).
    assert (Hnk : ((K - 14) + 14)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xea) : mword 64) 2
                  = mword_of_int (WI + 0xec)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xe6 c.ret ===== *)
    assert (HP8ra : P8 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
      rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
      rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (WI + 0xec)) Rra P8 K b ltac:(nz)
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
    assert (Cs2 : P8 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
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
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs4 -> c <> Rs5 ->
              c <> Rs6 -> c <> Rs7 -> c <> Rra ->
              P8 !!! Regidx c = (M !!! Regidx c : mword 64)).
    { intros c N2 N8 N18 N20 N21 N22 N23 N1.
      rewrite /P8 upd_ne; [| congruence]. rewrite /P7 upd_ne; [| congruence].
      rewrite /P6 upd_ne; [| congruence]. rewrite /P5 upd_ne; [| congruence].
      rewrite /P4 upd_ne; [| congruence]. rewrite /P3 upd_ne; [| congruence].
      rewrite /P2 upd_ne; [| congruence]. rewrite /P1 upd_ne; [| congruence].
      reflexivity. }
    assert (Cs1 : P8 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (Cother Rs1); [exact Hs1 | nz | nz | nz | nz | nz | nz | nz | nz]. }
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
    iDestruct (cpu_own_transport CID0 CID9 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /wi_cont.
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P8 tot bm' data' dn' ds' n' wrote P'
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hpc
                    Hoctx Hpark Hppid Hidev Hinum Hmeta Hmap Hblocks Hsb Hfsb
                    Hsrc Hsl Hop").
    { unfold callee_saved. split_and!; assumption. }
    { exact Hwf'. }
    { exact Hhz'. }
    { exact Hdswf'. }
    { exact Hadr'. }
    { exact Hsz'. }
    { exact Hrange. }
    { exact Hker. }
    { rewrite Ca0. exact Harm. }
    { split; assumption. }
    { exact Hext. }
  Qed.

End WriteiRet.

(* ===================================================================== *)
(*  +0xcc .. +0xd4 : iupdate, a0 := tot, restore s3.  THREE PATHS JOIN.   *)
(* ===================================================================== *)
Section WriteiJoin.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Local Lemma wi_join `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (bn : bio_names) (γ : log_names) (γf : gname)
      (cov : gset Z) (logstart inodestart : Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm bm' : blkmap) (data data' : nat -> list (bv 8))
      (dn dn' : dinode) (ds : list dinode)
      (user : bool) (off n tot : nat) (src_bytes wrote : nat -> bv 8)
      (V : pprivate) (P' : uptd) (ncount u : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_writei <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    diblk_wf ds ->
    di_addrs dn' = bm_cells bm' ->
    blkmap_wf cov logstart bm' ->
    blk_holes_zero bm' data' ->
    bv_unsigned (di_size dn') < 2 ^ 31 ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    wi_sp m M ->
    M !!! Regidx Rs5 = ip ->
    M !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64) ->
    M !!! Regidx Rs1  = (m !!! Regidx Rs1  : mword 64) ->
    M !!! Regidx Rs8  = (m !!! Regidx Rs8  : mword 64) ->
    M !!! Regidx Rs9  = (m !!! Regidx Rs9  : mword 64) ->
    M !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64) ->
    M !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64) ->
    (forall k : nat,
       file_byte data' k
       = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
         then wrote (k - off)%nat else file_byte data k) ->
    (user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i) ->
    (tot <= n)%nat ->
    dn' = wi_dinode dn bm' off tot ->
    ((ncount - wi_cost off n)%nat <= u)%nat -> (u <= ncount)%nat ->
    uptd_ext (pv_upt V) P' ->
    sie_cap_gpr M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (WI + 0xd2) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv Φ γs -∗
    scheds_inv Φ γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wi_fr8 m -∗
    own_ctx (p_context (proc_addr j)) -∗
    park_hlf j true -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn' -∗
    inode_map γfs ip bm' -∗
    inode_blocks γfs bm' data' -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds) -∗
    (if user
     then proc_priv γf (proc_addr j) pidv (upd_upt V P')
     else [∗ list] i ∈ seq 0 n,
            pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ (src_bytes i)) -∗
    bslots bn 3 -∗
    log_op γ (S u) -∗
    wi_cont (CID0 := CID0) Φ γfs bn γ γf cov logstart inodestart dev ip inum
            bm data dn ds user off n src_bytes V ncount pidv dq dqd dqn dqs j
            m K C b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hgeom Hist Hicov Hilog Hdswf Hadr Hwf' Hhz' Hsz'
           Hj Hgl Hsp Hs5 Hs3 Hs1 Hs8 Hs9 Hs10 Hs11 Hrange Hker Htotn Hdneq
           Hlo Hhi Hext.
    pose proof HK as HK'. unfold K_writei in HK'.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs #Hscheds
              #Hdevi #Hdgeom #Hdlock Hframe Hoctx Hpark Hppid Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hfsb Hsrc Hsl Hop Hcont".
    iPoseProof (wri_d2 with "Htext") as "Hid2".
    iPoseProof (wri_d4 with "Htext") as "Hid4".
    iPoseProof (wri_d8 with "Htext") as "Hid8".
    iPoseProof (wri_da with "Htext") as "Hida".
    (* ===== +0xcc c.mv a0,s5 ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (WI + 0xd2)) Ra0 Rs5
              M (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hid2").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs5))]> M).
    assert (HT0a0 : T0 !!! Regidx Ra0 = ip).
    { rewrite /T0 upd_eq. rgne. rewrite Hs5. apply add_vec_zero_l. }
    assert (HT0sp : wi_sp m T0) by (rewrite /wi_sp /T0 upd_ne; [exact Hsp | nz]).
    assert (HT0s3 : T0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs3 | nz]).
    assert (HT0s1 : T0 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs1 | nz]).
    assert (HT0s8 : T0 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs8 | nz]).
    assert (HT0s9 : T0 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs9 | nz]).
    assert (HT0s10 : T0 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs10 | nz]).
    assert (HT0s11 : T0 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T0 upd_ne; [exact Hs11 | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xd2) : mword 64) 2
                  = mword_of_int (WI + 0xd4)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xce jal ra,iupdate ===== *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (WI + 0xd4)) Rra
              (mword_of_int 2095604 : mword 21) T0 (K - 14)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hid4").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (T1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (WI + 0xd4) : mword 64) 4)]> T0).
    assert (Htgt : add_vec (mword_of_int (WI + 0xd4) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095604 : mword 21))
                   = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Htgt) in "Hpc".
    assert (HT1a0 : T1 !!! Regidx Ra0 = ip)
      by (rewrite /T1 upd_ne; [exact HT0a0 | nz]).
    assert (HT1sp : wi_sp m T1) by (rewrite /wi_sp /T1 upd_ne; [exact HT0sp | nz]).
    assert (HT1ra : T1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (WI + 0xd4) : mword 64) 4)
      by (rewrite /T1; apply upd_eq).
    assert (HT1s3 : T1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s3 | nz]).
    assert (HT1s1 : T1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s1 | nz]).
    assert (HT1s8 : T1 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s8 | nz]).
    assert (HT1s9 : T1 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s9 | nz]).
    assert (HT1s10 : T1 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s10 | nz]).
    assert (HT1s11 : T1 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T1 upd_ne; [exact HT0s11 | nz]).
    iDestruct (cpu_own_transport CID0 CID2 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CID2) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKiu : (K_iupdate <= K - 14)%nat) by (unfold K_iupdate; lia).
    assert (Hdirlen : length (bm_dir bm') = NDIRECT)
      by exact (blkmap_wf_dir_len cov logstart bm' Hwf').
    iDestruct (wi_slots_split bn 2 1 with "Hsl") as "[Hsl2 Hsl1]".
    iApply (IU.wp_iupdate_sconf Φ γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart inodestart dev ip inum dn' bm' ds u
              pidv dq dqd dqn dqs T1 (K - 14)%nat true C b
              HKiu Hgeom Hist Hicov Hilog Hdswf Hadr Hdirlen Hj Hgl HT1a0 eq_refl
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hidev Hinum Hmeta Hmap
                    Hsb Hfsb Hppid Hprocs Hscheds Hoctx Hpark Hdevi Hdgeom
                    Hdlock Hsl2 Hop").
    iIntros (CID3 Hq3 mI) "%Hcs1 Hcg Hcnt Hpc Hoctx Hpark Hppid Hidev Hinum
                           Hmeta Hmap Hsb Hfsb Hsl2 Hop".
    assert (Hpcd8 : ret_pc (T1 !!! Regidx Rra : mword 64)
                    = mword_of_int (WI + 0xd8)) by (rewrite HT1ra; pcw).
    iEval (rewrite Hpcd8) in "Hpc".
    iDestruct (wi_slots_join bn 2 1 with "Hsl2 Hsl1") as "Hsl".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmIsp : wi_sp m mI).
    { rewrite /wi_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT1sp. }
    assert (HmIs3 : mI !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HT1s3).
    assert (HmIs1 : mI !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HT1s1).
    assert (HmIs8 : mI !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs8 ltac:(vm_compute; reflexivity));
          exact HT1s8).
    assert (HmIs9 : mI !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs9 ltac:(vm_compute; reflexivity));
          exact HT1s9).
    assert (HmIs10 : mI !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs10 ltac:(vm_compute; reflexivity));
          exact HT1s10).
    assert (HmIs11 : mI !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs11 ltac:(vm_compute; reflexivity));
          exact HT1s11).
    (* ===== +0xd2 c.mv a0,s3 : the return value ===== *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (WI + 0xd8)) Ra0 Rs3
              mI (K - 14)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hid8").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (T2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mI Rs3))]> mI).
    assert (HT2a0 : T2 !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64)).
    { rewrite /T2 upd_eq. rgne. rewrite HmIs3. apply add_vec_zero_l. }
    assert (HT2sp : wi_sp m T2) by (rewrite /wi_sp /T2 upd_ne; [exact HmIsp | nz]).
    assert (HT2s1 : T2 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs1 | nz]).
    assert (HT2s8 : T2 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs8 | nz]).
    assert (HT2s9 : T2 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs9 | nz]).
    assert (HT2s10 : T2 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs10 | nz]).
    assert (HT2s11 : T2 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T2 upd_ne; [exact HmIs11 | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xd8) : mword 64) 2
                  = mword_of_int (WI + 0xda)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== +0xd4 c.ldsp s3,72(sp) ===== *)
    rewrite /wi_fr8.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    assert (Hc5 : add_vec (T2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xda)) (mword_of_int 9 : mword 6) Rs3
              T2 (K - 14)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hida [Hf5]").
    { iEval (rewrite Hc5). iExact "Hf5". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf5".
    iEval (rewrite Hc5) in "Hf5".
    set (T3 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> T2).
    assert (HT3sp : wi_sp m T3) by (rewrite /wi_sp /T3 upd_ne; [exact HT2sp | nz]).
    assert (HT3s3 : T3 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /T3; apply upd_eq).
    assert (HT3a0 : T3 !!! Regidx Ra0 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2a0 | nz]).
    assert (HT3s1 : T3 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s1 | nz]).
    assert (HT3s8 : T3 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s8 | nz]).
    assert (HT3s9 : T3 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s9 | nz]).
    assert (HT3s10 : T3 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s10 | nz]).
    assert (HT3s11 : T3 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2s11 | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xda) : mword 64) 2
                  = mword_of_int (WI + 0xdc)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* ===== into the return block ===== *)
    iAssert (wi_fr7 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
      as "Hframe".
    { rewrite /wi_fr7.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExists _; iExact "Hf5"|].
      iSplitL "Hf6"; [iExact "Hf6"|]. iSplitL "Hf7"; [iExact "Hf7"|].
      iSplitL "Hf8"; [iExact "Hf8"|]. iSplitL "Hf9"; [iExact "Hf9"|].
      iSplitL "HfA"; [iExact "HfA"|]. iSplitL "HfB"; [iExact "HfB"|].
      iSplitL "HfC"; [iExact "HfC"|]. iSplitL "HfD"; [iExact "HfD"|].
      iExact "HfE". }
    iDestruct (cpu_own_transport CID3 CID5 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    assert (Hdwf' : dinode_wf dn').
    { rewrite /dinode_wf Hadr /bm_cells length_app Hdirlen /=.
      unfold NDIRECT. lia. }
    iApply (wi_ret (CID0 := CID5) Φ γfs bn γ γf cov logstart inodestart dev ip inum
              bm bm' data data' dn dn' ds (<[islot inum := dn']> ds)
              user off n tot src_bytes wrote V P' ncount u
              pidv dq dqd dqn dqs j m T3 K C b
              HK HT3sp HT3s1 HT3s3 HT3s8 HT3s9 HT3s10 HT3s11
              Hwf' Hhz' (diblk_wf_insert ds (islot inum) dn' Hdswf Hdwf')
              Hadr Hsz' Hrange Hker
              ltac:(right; split_and!;
                    [exact HT3a0 | exact Htotn | exact Hdneq | reflexivity])
              Hlo Hhi Hext
              with "Hcg Hcnt Htext Hpc Hframe Hoctx Hpark Hppid Hidev Hinum
                    Hmeta Hmap Hblocks Hsb Hfsb Hsrc Hsl Hop [Hcont]").
    iApply (wp_next_shift (CIDa := CID2) (CIDb := CID5) ltac:(wp_next_chain)
              with "Hcont").
  Qed.

End WriteiJoin.

(* ===================================================================== *)
(*  +0xb6 .. +0xcc : the size test, the store, the five restores.         *)
(*  Both arms restore s1/s8..s11 and reach the join at +0xcc, which is    *)
(*  bmap's s4 lesson at five registers instead of one.                    *)
(* ===================================================================== *)
Section WriteiSize.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Local Lemma wi_size `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γfs : fs_names) (bn : bio_names) (γ : log_names) (γf : gname)
      (cov : gset Z) (logstart inodestart : Z) (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (bm bm' : blkmap) (data data' : nat -> list (bv 8))
      (dn : dinode) (ds : list dinode)
      (user : bool) (off n tot : nat) (src_bytes wrote : nat -> bv 8)
      (V : pprivate) (P' : uptd) (ncount u : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_writei <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    diblk_wf ds ->
    blkmap_wf cov logstart bm' ->
    blk_holes_zero bm' data' ->
    bv_unsigned (di_size dn) < 2 ^ 31 ->
    Z.of_nat (off + tot) < 2 ^ 31 ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    wi_sp m M ->
    M !!! Regidx Rs5 = ip ->
    M !!! Regidx Rs2 = (mword_of_int (Z.of_nat (off + tot)) : mword 64) ->
    M !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64) ->
    (forall k : nat,
       file_byte data' k
       = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
         then wrote (k - off)%nat else file_byte data k) ->
    (user = false -> forall i : nat, (i < tot)%nat -> wrote i = src_bytes i) ->
    (tot <= n)%nat ->
    ((ncount - wi_cost off n)%nat <= u)%nat -> (u <= ncount)%nat ->
    uptd_ext (pv_upt V) P' ->
    sie_cap_gpr M (K - 14)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (WI + 0xbc) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv Φ γs -∗
    scheds_inv Φ γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wi_fr13 m -∗
    own_ctx (p_context (proc_addr j)) -∗
    park_hlf j true -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn -∗
    inode_map γfs ip bm' -∗
    inode_blocks γfs bm' data' -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds) -∗
    (if user
     then proc_priv γf (proc_addr j) pidv (upd_upt V P')
     else [∗ list] i ∈ seq 0 n,
            pa_add (m !!! Regidx Ra2 : mword 64) i ↦ₘ (src_bytes i)) -∗
    bslots bn 3 -∗
    log_op γ (S u) -∗
    wi_cont (CID0 := CID0) Φ γfs bn γ γf cov logstart inodestart dev ip inum
            bm data dn ds user off n src_bytes V ncount pidv dq dqd dqn dqs j
            m K C b -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hgeom Hist Hicov Hilog Hdswf Hwf' Hhz' Hszlt Hofflt
           Hj Hgl Hsp Hs5 Hs2 Hs3 Hrange Hker Htotn Hlo Hhi Hext.
    pose proof HK as HK'. unfold K_writei in HK'.
    change (2 ^ 31)%Z with 2147483648%Z in Hszlt, Hofflt.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs #Hscheds
              #Hdevi #Hdgeom #Hdlock Hframe Hoctx Hpark Hppid Hidev Hinum
              Hmeta Hmap Hblocks Hsb Hfsb Hsrc Hsl Hop Hcont".
    iPoseProof (wri_bc with "Htext") as "Hibc".
    iPoseProof (wri_c0 with "Htext") as "Hic0".
    iPoseProof (wri_c4 with "Htext") as "Hic4".
    iPoseProof (wri_c8 with "Htext") as "Hic8".
    iPoseProof (wri_ca with "Htext") as "Hica".
    iPoseProof (wri_cc with "Htext") as "Hicc".
    iPoseProof (wri_ce with "Htext") as "Hice".
    iPoseProof (wri_d0 with "Htext") as "Hid0".
    iPoseProof (wri_f2 with "Htext") as "Hif2".
    iPoseProof (wri_f4 with "Htext") as "Hif4".
    iPoseProof (wri_f6 with "Htext") as "Hif6".
    iPoseProof (wri_f8 with "Htext") as "Hif8".
    iPoseProof (wri_fa with "Htext") as "Hifa".
    iPoseProof (wri_fc with "Htext") as "Hifc".
    rewrite /wi_fr13.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9
                            & HfA & HfB & HfC & HfD & HfE)".
    rewrite /inode_meta.
    iDestruct "Hmeta" as "(Hmt & Hmj & Hmn & Hml & Hmz)".
    (* ===== +0xb6 lw a5,76(s5) : a5 := ip->size ===== *)
    assert (Hszadr : add_vec (rget M Rs5) (sign_extend' 64 (mword_of_int 76 : mword 12))
                     = i_size ip).
    { rgne. rewrite Hs5. reflexivity. }
    iEval (rewrite -Hszadr) in "Hmz".
    iApply (wp_lw_s_sconf Φ (mword_of_int (WI + 0xbc)) Ra5 Rs5
              (mword_of_int 76 : mword 12) M (K - 14)%nat (di_size dn : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hibc Hmz").
    iIntros (CIDz1 Hqz1) "Hcg Hpc Hmz".
    iEval (rewrite Hszadr) in "Hmz".
    set (M0 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_size dn : mword 32))]> M).
    assert (HM0a5 : M0 !!! Regidx Ra5 = (sign_extend' 64 (di_size dn : mword 32) : mword 64))
      by (rewrite /M0; apply upd_eq).
    assert (HM0s5 : M0 !!! Regidx Rs5 = ip)
      by (rewrite /M0 upd_ne; [exact Hs5 | nz]).
    assert (HM0s2 : M0 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (off + tot)) : mword 64))
      by (rewrite /M0 upd_ne; [exact Hs2 | nz]).
    assert (HM0s3 : M0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /M0 upd_ne; [exact Hs3 | nz]).
    assert (HM0sp : wi_sp m M0) by (rewrite /wi_sp /M0 upd_ne; [exact Hsp | nz]).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xbc) : mword 64) 4
                  = mword_of_int (WI + 0xc0)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    (* the two unsigned readings the [bgeu] compares *)
    assert (Hszu : bv_unsigned (sign_extend' 64 (di_size dn : mword 32) : mword 64)
                   = bv_unsigned (di_size dn))
      by (apply wi_sext32_unsigned; exact Hszlt).
    assert (Hoffu : bv_unsigned (mword_of_int (Z.of_nat (off + tot)) : mword 64)
                    = Z.of_nat (off + tot)).
    { apply moi64_small. split; [apply Nat2Z.is_nonneg |].
      change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
    (* ===== +0xba bgeu a5,s2 : is the file already this long? ===== *)
    destruct (Z_le_gt_dec (Z.of_nat (off + tot)) (bv_unsigned (di_size dn)))
      as [Hge | Hlt].
    - (* ---------- IT IS: skip the store, restore, jump to +0xcc -------- *)
      assert (Hdsz : di_size (wi_dinode dn bm' off tot) = di_size dn).
      { rewrite /wi_dinode. cbn [di_size].
        case_decide as Hd; [| reflexivity].
        exfalso. exact (Z.lt_irrefl _ (Z.le_lt_trans _ _ _ Hge Hd)). }
      iApply (wp_bgeu_taken_s_sconf Φ (mword_of_int (WI + 0xc0))
                (mword_of_int 50 : mword 13) Rs2 Ra5 M0 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM0a5 HM0s2; apply bc_geu;
                      rewrite Hszu Hoffu; exact Hge)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hic0").
      iNext. iIntros (CIDz2 Hqz2) "Hcg Hpc".
      assert (Htgtf2 : add_vec (mword_of_int (WI + 0xc0) : mword 64)
                         (sign_extend' 64 (mword_of_int 50 : mword 13))
                       = mword_of_int (WI + 0xf2)) by pcw.
      iEval (rewrite Htgtf2) in "Hpc".
      set (QB0 := M0).
      assert (HQB0sp : wi_sp m QB0) by exact HM0sp.
      assert (HQB0s5 : QB0 !!! Regidx Rs5 = ip) by exact HM0s5.
      assert (HQB0s3 : QB0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
        by exact HM0s3.
    assert (HcQB1 : add_vec (QB0 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HQB0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xf2)) (mword_of_int 11 : mword 6) Rs1
              QB0 (K - 14)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif2 [Hf3]").
    { iEval (rewrite HcQB1). iExact "Hf3". }
    iIntros (CIDQB1 HqQB1) "Hcg Hpc Hf3".
    iEval (rewrite HcQB1) in "Hf3".
    set (QB1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> QB0).
    assert (HQB1sp : wi_sp m QB1) by (rewrite /wi_sp /QB1 upd_ne; [exact HQB0sp | nz]).
    assert (HQB1s5 : QB1 !!! Regidx Rs5 = ip)
      by (rewrite /QB1 upd_ne; [exact HQB0s5 | nz]).
    assert (HQB1s3 : QB1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB1 upd_ne; [exact HQB0s3 | nz]).
    assert (HQB1Rs1 : QB1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB1; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xf2) : mword 64) 2
                  = mword_of_int (WI + 0xf4)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQB2 : add_vec (QB1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite HQB1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xf4)) (mword_of_int 4 : mword 6) Rs8
              QB1 (K - 14)%nat (m !!! Regidx Rs8 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif4 [HfA]").
    { iEval (rewrite HcQB2). iExact "HfA". }
    iIntros (CIDQB2 HqQB2) "Hcg Hpc HfA".
    iEval (rewrite HcQB2) in "HfA".
    set (QB2 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> QB1).
    assert (HQB2sp : wi_sp m QB2) by (rewrite /wi_sp /QB2 upd_ne; [exact HQB1sp | nz]).
    assert (HQB2s5 : QB2 !!! Regidx Rs5 = ip)
      by (rewrite /QB2 upd_ne; [exact HQB1s5 | nz]).
    assert (HQB2s3 : QB2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB2 upd_ne; [exact HQB1s3 | nz]).
    assert (HQB2Rs1 : QB2 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB2 upd_ne; [exact HQB1Rs1 | nz]).
    assert (HQB2Rs8 : QB2 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QB2; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xf4) : mword 64) 2
                  = mword_of_int (WI + 0xf6)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQB3 : add_vec (QB2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 11).
    { rewrite HQB2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xf6)) (mword_of_int 3 : mword 6) Rs9
              QB2 (K - 14)%nat (m !!! Regidx Rs9 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif6 [HfB]").
    { iEval (rewrite HcQB3). iExact "HfB". }
    iIntros (CIDQB3 HqQB3) "Hcg Hpc HfB".
    iEval (rewrite HcQB3) in "HfB".
    set (QB3 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9 : mword 64)]> QB2).
    assert (HQB3sp : wi_sp m QB3) by (rewrite /wi_sp /QB3 upd_ne; [exact HQB2sp | nz]).
    assert (HQB3s5 : QB3 !!! Regidx Rs5 = ip)
      by (rewrite /QB3 upd_ne; [exact HQB2s5 | nz]).
    assert (HQB3s3 : QB3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB3 upd_ne; [exact HQB2s3 | nz]).
    assert (HQB3Rs1 : QB3 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB3 upd_ne; [exact HQB2Rs1 | nz]).
    assert (HQB3Rs8 : QB3 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QB3 upd_ne; [exact HQB2Rs8 | nz]).
    assert (HQB3Rs9 : QB3 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QB3; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xf6) : mword 64) 2
                  = mword_of_int (WI + 0xf8)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQB4 : add_vec (QB3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12).
    { rewrite HQB3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xf8)) (mword_of_int 2 : mword 6) Rs10
              QB3 (K - 14)%nat (m !!! Regidx Rs10 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hif8 [HfC]").
    { iEval (rewrite HcQB4). iExact "HfC". }
    iIntros (CIDQB4 HqQB4) "Hcg Hpc HfC".
    iEval (rewrite HcQB4) in "HfC".
    set (QB4 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10 : mword 64)]> QB3).
    assert (HQB4sp : wi_sp m QB4) by (rewrite /wi_sp /QB4 upd_ne; [exact HQB3sp | nz]).
    assert (HQB4s5 : QB4 !!! Regidx Rs5 = ip)
      by (rewrite /QB4 upd_ne; [exact HQB3s5 | nz]).
    assert (HQB4s3 : QB4 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB4 upd_ne; [exact HQB3s3 | nz]).
    assert (HQB4Rs1 : QB4 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB4 upd_ne; [exact HQB3Rs1 | nz]).
    assert (HQB4Rs8 : QB4 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QB4 upd_ne; [exact HQB3Rs8 | nz]).
    assert (HQB4Rs9 : QB4 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QB4 upd_ne; [exact HQB3Rs9 | nz]).
    assert (HQB4Rs10 : QB4 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /QB4; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xf8) : mword 64) 2
                  = mword_of_int (WI + 0xfa)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQB5 : add_vec (QB4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 13).
    { rewrite HQB4sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xfa)) (mword_of_int 1 : mword 6) Rs11
              QB4 (K - 14)%nat (m !!! Regidx Rs11 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hifa [HfD]").
    { iEval (rewrite HcQB5). iExact "HfD". }
    iIntros (CIDQB5 HqQB5) "Hcg Hpc HfD".
    iEval (rewrite HcQB5) in "HfD".
    set (QB5 := <[Regidx Rs11 := regval_into_reg (m !!! Regidx Rs11 : mword 64)]> QB4).
    assert (HQB5sp : wi_sp m QB5) by (rewrite /wi_sp /QB5 upd_ne; [exact HQB4sp | nz]).
    assert (HQB5s5 : QB5 !!! Regidx Rs5 = ip)
      by (rewrite /QB5 upd_ne; [exact HQB4s5 | nz]).
    assert (HQB5s3 : QB5 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4s3 | nz]).
    assert (HQB5Rs1 : QB5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4Rs1 | nz]).
    assert (HQB5Rs8 : QB5 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4Rs8 | nz]).
    assert (HQB5Rs9 : QB5 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4Rs9 | nz]).
    assert (HQB5Rs10 : QB5 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /QB5 upd_ne; [exact HQB4Rs10 | nz]).
    assert (HQB5Rs11 : QB5 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /QB5; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xfa) : mword 64) 2
                  = mword_of_int (WI + 0xfc)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xf6 c.j +0xcc ===== *)
      iApply (wp_cj_s_sconf Φ (mword_of_int (WI + 0xfc))
                (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")))
                QB5 (K - 14)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hifc").
      iIntros (CIDz3 Hqz3). iNext. iIntros "Hcg Hpc".
      assert (Htgtd2 : add_vec (mword_of_int (WI + 0xfc) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2027 : mword 11) ('b"0"))))
              = mword_of_int (WI + 0xd2)) by pcw.
      iEval (rewrite Htgtd2) in "Hpc".
      iAssert (inode_meta ip (wi_dinode dn bm' off tot))
        with "[Hmt Hmj Hmn Hml Hmz]" as "Hmeta".
      { rewrite /inode_meta /wi_dinode.
        cbn [di_type di_major di_minor di_nlink di_size].
        rewrite -/(di_size (wi_dinode dn bm' off tot)).
        iSplitL "Hmt"; [iExact "Hmt"|]. iSplitL "Hmj"; [iExact "Hmj"|].
        iSplitL "Hmn"; [iExact "Hmn"|]. iSplitL "Hml"; [iExact "Hml"|].
        rewrite Hdsz. iExact "Hmz". }
      iAssert (wi_fr8 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
        as "Hframe".
      { rewrite /wi_fr8.
        iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
        iSplitL "Hf3"; [iExists _; iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
        iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
        iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
        iSplitL "Hf9"; [iExact "Hf9"|].
        iSplitL "HfA"; [iExists _; iExact "HfA"|].
        iSplitL "HfB"; [iExists _; iExact "HfB"|].
        iSplitL "HfC"; [iExists _; iExact "HfC"|].
        iSplitL "HfD"; [iExists _; iExact "HfD"|]. iExact "HfE". }
      iDestruct (cpu_own_transport CID0 CIDz3 0 true (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (wi_join (CID0 := CIDz3) Φ γs j γl γu γd γk pd pav pu γfs bn γ γf
                cov logstart inodestart dev ip inum bm bm' data data' dn
                (wi_dinode dn bm' off tot) ds user off n tot src_bytes wrote
                V P' ncount u pidv dq dqd dqn dqs m QB5 K C b
                HK Hgeom Hist Hicov Hilog Hdswf eq_refl Hwf' Hhz'
                ltac:(rewrite Hdsz; change (2 ^ 31)%Z with 2147483648%Z; exact Hszlt)
                Hj Hgl HQB5sp HQB5s5 HQB5s3
                HQB5Rs1 HQB5Rs8 HQB5Rs9 HQB5Rs10 HQB5Rs11
                Hrange Hker Htotn eq_refl Hlo Hhi Hext
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hscheds Hdevi
                      Hdgeom Hdlock Hframe Hoctx Hpark Hppid Hidev Hinum Hmeta
                      Hmap Hblocks Hsb Hfsb Hsrc Hsl Hop [Hcont]").
      iApply (wp_next_shift (CIDa := CID0) (CIDb := CIDz3) ltac:(wp_next_chain)
                with "Hcont").
    - (* ---------- IT IS NOT: store the new size, restore, fall through -- *)
      assert (Hltz : bv_unsigned (di_size dn) < Z.of_nat (off + tot)) by lia.
      assert (Hdsz : di_size (wi_dinode dn bm' off tot)
                     = (mword_of_int (Z.of_nat (off + tot)) : mword 32)).
      { rewrite /wi_dinode. cbn [di_size].
        case_decide as Hd; [reflexivity | exfalso; exact (Hd Hltz)]. }
      iApply (wp_bgeu_fall_s_sconf Φ (mword_of_int (WI + 0xc0))
                (mword_of_int 50 : mword 13) Rs2 Ra5 M0 (K - 14)%nat b
                ltac:(nz) ltac:(nz)
                ltac:(rgne; rgne; rewrite HM0a5 HM0s2; apply bc_ltu;
                      rewrite Hszu Hoffu; exact Hltz)
                with "Hcg Hpc Hic0").
      iIntros (CIDz2 Hqz2) "Hcg Hpc".
      assert (Hpp : add_vec_int (mword_of_int (WI + 0xc0) : mword 64) 4
                    = mword_of_int (WI + 0xc4)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      (* ===== +0xbe sw s2,76(s5) : ip->size := off ===== *)
      assert (Hszadr0 : add_vec (rget M0 Rs5) (sign_extend' 64 (mword_of_int 76 : mword 12))
                        = i_size ip).
      { rgne. rewrite HM0s5. reflexivity. }
      iEval (rewrite -Hszadr0) in "Hmz".
      iApply (wp_sw_s_sconf Φ (mword_of_int (WI + 0xc4)) Rs2 Rs5
                (mword_of_int 76 : mword 12) M0 (K - 14)%nat (di_size dn : mword 32) b
                with "Hcg Hpc Hic4 Hmz").
      iIntros (CIDz3 Hqz3) "Hcg Hpc Hmz".
      iEval (rewrite Hszadr0) in "Hmz".
      assert (Hstv : trunc32 (rget M0 Rs2) = (mword_of_int (Z.of_nat (off + tot)) : mword 32)).
      { rgne. rewrite HM0s2. apply trunc32_mword_of_int. }
      iEval (rewrite Hstv) in "Hmz".
      assert (Hpp : add_vec_int (mword_of_int (WI + 0xc4) : mword 64) 4
                    = mword_of_int (WI + 0xc8)) by pcw.
      iEval (rewrite Hpp) in "Hpc". clear Hpp.
      set (QA0 := M0).
      assert (HQA0sp : wi_sp m QA0) by exact HM0sp.
      assert (HQA0s5 : QA0 !!! Regidx Rs5 = ip) by exact HM0s5.
      assert (HQA0s3 : QA0 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
        by exact HM0s3.
    assert (HcQA1 : add_vec (QA0 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HQA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xc8)) (mword_of_int 11 : mword 6) Rs1
              QA0 (K - 14)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hic8 [Hf3]").
    { iEval (rewrite HcQA1). iExact "Hf3". }
    iIntros (CIDQA1 HqQA1) "Hcg Hpc Hf3".
    iEval (rewrite HcQA1) in "Hf3".
    set (QA1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> QA0).
    assert (HQA1sp : wi_sp m QA1) by (rewrite /wi_sp /QA1 upd_ne; [exact HQA0sp | nz]).
    assert (HQA1s5 : QA1 !!! Regidx Rs5 = ip)
      by (rewrite /QA1 upd_ne; [exact HQA0s5 | nz]).
    assert (HQA1s3 : QA1 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA1 upd_ne; [exact HQA0s3 | nz]).
    assert (HQA1Rs1 : QA1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA1; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xc8) : mword 64) 2
                  = mword_of_int (WI + 0xca)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQA2 : add_vec (QA1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite HQA1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xca)) (mword_of_int 4 : mword 6) Rs8
              QA1 (K - 14)%nat (m !!! Regidx Rs8 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hica [HfA]").
    { iEval (rewrite HcQA2). iExact "HfA". }
    iIntros (CIDQA2 HqQA2) "Hcg Hpc HfA".
    iEval (rewrite HcQA2) in "HfA".
    set (QA2 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> QA1).
    assert (HQA2sp : wi_sp m QA2) by (rewrite /wi_sp /QA2 upd_ne; [exact HQA1sp | nz]).
    assert (HQA2s5 : QA2 !!! Regidx Rs5 = ip)
      by (rewrite /QA2 upd_ne; [exact HQA1s5 | nz]).
    assert (HQA2s3 : QA2 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA2 upd_ne; [exact HQA1s3 | nz]).
    assert (HQA2Rs1 : QA2 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA2 upd_ne; [exact HQA1Rs1 | nz]).
    assert (HQA2Rs8 : QA2 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QA2; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xca) : mword 64) 2
                  = mword_of_int (WI + 0xcc)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQA3 : add_vec (QA2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 11).
    { rewrite HQA2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xcc)) (mword_of_int 3 : mword 6) Rs9
              QA2 (K - 14)%nat (m !!! Regidx Rs9 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hicc [HfB]").
    { iEval (rewrite HcQA3). iExact "HfB". }
    iIntros (CIDQA3 HqQA3) "Hcg Hpc HfB".
    iEval (rewrite HcQA3) in "HfB".
    set (QA3 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9 : mword 64)]> QA2).
    assert (HQA3sp : wi_sp m QA3) by (rewrite /wi_sp /QA3 upd_ne; [exact HQA2sp | nz]).
    assert (HQA3s5 : QA3 !!! Regidx Rs5 = ip)
      by (rewrite /QA3 upd_ne; [exact HQA2s5 | nz]).
    assert (HQA3s3 : QA3 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA3 upd_ne; [exact HQA2s3 | nz]).
    assert (HQA3Rs1 : QA3 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA3 upd_ne; [exact HQA2Rs1 | nz]).
    assert (HQA3Rs8 : QA3 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QA3 upd_ne; [exact HQA2Rs8 | nz]).
    assert (HQA3Rs9 : QA3 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QA3; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xcc) : mword 64) 2
                  = mword_of_int (WI + 0xce)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQA4 : add_vec (QA3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 12).
    { rewrite HQA3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xce)) (mword_of_int 2 : mword 6) Rs10
              QA3 (K - 14)%nat (m !!! Regidx Rs10 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hice [HfC]").
    { iEval (rewrite HcQA4). iExact "HfC". }
    iIntros (CIDQA4 HqQA4) "Hcg Hpc HfC".
    iEval (rewrite HcQA4) in "HfC".
    set (QA4 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10 : mword 64)]> QA3).
    assert (HQA4sp : wi_sp m QA4) by (rewrite /wi_sp /QA4 upd_ne; [exact HQA3sp | nz]).
    assert (HQA4s5 : QA4 !!! Regidx Rs5 = ip)
      by (rewrite /QA4 upd_ne; [exact HQA3s5 | nz]).
    assert (HQA4s3 : QA4 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA4 upd_ne; [exact HQA3s3 | nz]).
    assert (HQA4Rs1 : QA4 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA4 upd_ne; [exact HQA3Rs1 | nz]).
    assert (HQA4Rs8 : QA4 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QA4 upd_ne; [exact HQA3Rs8 | nz]).
    assert (HQA4Rs9 : QA4 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QA4 upd_ne; [exact HQA3Rs9 | nz]).
    assert (HQA4Rs10 : QA4 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /QA4; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xce) : mword 64) 2
                  = mword_of_int (WI + 0xd0)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
    assert (HcQA5 : add_vec (QA4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 13).
    { rewrite HQA4sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (WI + 0xd0)) (mword_of_int 1 : mword 6) Rs11
              QA4 (K - 14)%nat (m !!! Regidx Rs11 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hid0 [HfD]").
    { iEval (rewrite HcQA5). iExact "HfD". }
    iIntros (CIDQA5 HqQA5) "Hcg Hpc HfD".
    iEval (rewrite HcQA5) in "HfD".
    set (QA5 := <[Regidx Rs11 := regval_into_reg (m !!! Regidx Rs11 : mword 64)]> QA4).
    assert (HQA5sp : wi_sp m QA5) by (rewrite /wi_sp /QA5 upd_ne; [exact HQA4sp | nz]).
    assert (HQA5s5 : QA5 !!! Regidx Rs5 = ip)
      by (rewrite /QA5 upd_ne; [exact HQA4s5 | nz]).
    assert (HQA5s3 : QA5 !!! Regidx Rs3 = (mword_of_int (Z.of_nat tot) : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4s3 | nz]).
    assert (HQA5Rs1 : QA5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4Rs1 | nz]).
    assert (HQA5Rs8 : QA5 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4Rs8 | nz]).
    assert (HQA5Rs9 : QA5 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4Rs9 | nz]).
    assert (HQA5Rs10 : QA5 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64))
      by (rewrite /QA5 upd_ne; [exact HQA4Rs10 | nz]).
    assert (HQA5Rs11 : QA5 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64))
      by (rewrite /QA5; apply upd_eq).
    assert (Hpp : add_vec_int (mword_of_int (WI + 0xd0) : mword 64) 2
                  = mword_of_int (WI + 0xd2)) by pcw.
    iEval (rewrite Hpp) in "Hpc". clear Hpp.
      iAssert (inode_meta ip (wi_dinode dn bm' off tot))
        with "[Hmt Hmj Hmn Hml Hmz]" as "Hmeta".
      { rewrite /inode_meta /wi_dinode.
        cbn [di_type di_major di_minor di_nlink di_size].
        rewrite -/(di_size (wi_dinode dn bm' off tot)).
        iSplitL "Hmt"; [iExact "Hmt"|]. iSplitL "Hmj"; [iExact "Hmj"|].
        iSplitL "Hmn"; [iExact "Hmn"|]. iSplitL "Hml"; [iExact "Hml"|].
        rewrite Hdsz. iExact "Hmz". }
      iAssert (wi_fr8 m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 HfA HfB HfC HfD HfE]"
        as "Hframe".
      { rewrite /wi_fr8.
        iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
        iSplitL "Hf3"; [iExists _; iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
        iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
        iSplitL "Hf7"; [iExact "Hf7"|]. iSplitL "Hf8"; [iExact "Hf8"|].
        iSplitL "Hf9"; [iExact "Hf9"|].
        iSplitL "HfA"; [iExists _; iExact "HfA"|].
        iSplitL "HfB"; [iExists _; iExact "HfB"|].
        iSplitL "HfC"; [iExists _; iExact "HfC"|].
        iSplitL "HfD"; [iExists _; iExact "HfD"|]. iExact "HfE". }
      iDestruct (cpu_own_transport CID0 CIDQA5 0 true (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      assert (Hszn : bv_unsigned (di_size (wi_dinode dn bm' off tot)) < 2147483648).
      { rewrite Hdsz. rewrite moi32_small; [lia |].
        change (2 ^ 32)%Z with 4294967296%Z. lia. }
      iApply (wi_join (CID0 := CIDQA5) Φ γs j γl γu γd γk pd pav pu γfs bn γ γf
                cov logstart inodestart dev ip inum bm bm' data data' dn
                (wi_dinode dn bm' off tot) ds user off n tot src_bytes wrote
                V P' ncount u pidv dq dqd dqn dqs m QA5 K C b
                HK Hgeom Hist Hicov Hilog Hdswf eq_refl Hwf' Hhz'
                ltac:(change (2 ^ 31)%Z with 2147483648%Z; exact Hszn)
                Hj Hgl HQA5sp HQA5s5 HQA5s3
                HQA5Rs1 HQA5Rs8 HQA5Rs9 HQA5Rs10 HQA5Rs11
                Hrange Hker Htotn eq_refl Hlo Hhi Hext
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hscheds Hdevi
                      Hdgeom Hdlock Hframe Hoctx Hpark Hppid Hidev Hinum Hmeta
                      Hmap Hblocks Hsb Hfsb Hsrc Hsl Hop [Hcont]").
      iApply (wp_next_shift (CIDa := CID0) (CIDb := CIDQA5) ltac:(wp_next_chain)
                with "Hcont").
  Qed.

End WriteiSize.

End WriteiProof.
