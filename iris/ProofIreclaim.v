(* ProofIreclaim.v -- ireclaim over the SIE-agnostic sconf world.

     void ireclaim(int dev) {
       int inum;  struct buf *bp;  struct dinode *dip;  struct inode *ip;
       for(inum = 1; inum < sb.ninodes; inum++){
         bp = bread(dev, IBLOCK(inum, sb));
         dip = (struct dinode * )bp->data + inum % IPB;
         if(dip->type != 0 && dip->nlink == 0){
           printf("ireclaim: orphaned inode %d\n", inum);
           ip = iget(dev, inum);
           brelse(bp);
           begin_op();  ilock(ip);  iunlock(ip);  iput(ip);  end_op();
         } else
           brelse(bp);
       }
     }

   THE SHAPE OF THE PROOF.  Six blocks, entered right to left, plus one
   induction on the fuel [Z.to_nat (ninodes - inum)]:

     [irc_epilogue]  +0xb2 .. +0xc4  pop ra/s0/s1..s6, pop the frame, ret,
                                     and discharge the contract.  ONE live
                                     exit: the [c.jr ra] at +0xc6 is DEAD
                                     ([1 < ninodes] refutes the [bgeu a5,a4]
                                     at +0x0a, which would reach it with the
                                     frame NEVER pushed).
     [irc_step]      +0x6e .. +0x7a  inum++, reload sb.ninodes, the [bgeu]
                                     that either leaves or re-enters the
                                     body.  BOTH paths through the body
                                     arrive here -- the orphan block falls
                                     into it, the plain arm jumps to it from
                                     +0xb0.
     [irc_orphan]    +0x38 .. +0x6c  printk("%d") / iget / brelse /
                                     begin_op / ilock / iunlock / iput /
                                     end_op, then FALL into +0x6e.  The
                                     [beq s3,zero] at +0x50 is DEAD, refuted
                                     by iget's POSTCONDITION
                                     ([IcacheRef.ientry_ne_zero]) and by no
                                     premise of this contract.
     [irc_scan]      +0x7c .. +0xb0  THE LOOP BODY, by induction on the fuel:
                                     bread, the slot arithmetic, [lh a4,0] and
                                     [lh a5,6], and the two [c.beqz]s.
     [wp_ireclaim_sconf] +0x00 .. +0x36, whose [c.j +70] enters the loop
                                     IN THE MIDDLE (past the step block).

   THE LOOP IS ENTERED IN THE MIDDLE, and that is the one structural thing
   ialloc's scan does not have: the prologue jumps straight to the BODY at
   +0x7c, while every later turn arrives there from the STEP at +0x7a.  The
   induction is therefore stated at the body ([irc_loop] below), and the
   step block takes that wand as a HYPOTHESIS rather than being part of it --
   which is also what lets the orphan block, which falls into the step,
   re-enter the loop without being inside the induction.

   NO [log_op] CROSSES THE CONTRACT'S BOUNDARY.  begin_op at +0x54 mints
   [log_op γ MAXOPBLOCKS] and end_op at +0x6a retires it, both inside the
   loop body; [iput_units = 3 <= MAXOPBLOCKS = 10] is a closed numeric fact.
   The reference iget pays out is carved ([IcacheRef.inode_ref_shed]) for
   ilock, gathered back after iunlock, and spent by iput -- also entirely
   inside.  The only things that flow are the bitmap (iput frees blocks) and
   the three buffer slots (returned).

   THE ENTRY SLEEPLOCK IS PROJECTED, NOT SUPPLIED.  The scan cannot name the
   slot iget picks, so the contract takes [IcacheBoot.ic_sleeplocks] and the
   orphan block projects the one the run picks with
   [IcacheBoot.ic_sleeplocks_acc]; the escrow family is projected the same
   way ([irc_esc_acc] below, ProofDirlink's [dl_esc_acc] restated).       *)
From Stdlib Require Import Eqdep_dec ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list list_numbers functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers dfrac.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs WpSmodeIntr.
Require Import WpSmodeHalf.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import ByteBuf.
Require Import PrintintArith.
Require Import PrintkFmt.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import DinodeSlot.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IgetLic.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IcacheBoot.
Require Import CodeIreclaim.
Require Import SpecPrintk.
Require Import SpecBread SpecBrelse SpecIget.
Require Import SpecBeginOp SpecEndOp.
Require Import SpecIlock SpecIunlock SpecIput.
Require Import SpecIreclaim.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  THE FORMATTED MESSAGE.  [auipc s6,0x4 / addi s6,s6,50] at +0x2e/+0x32 *)
(*  off [ireclaim = 0x80003408] resolves to 0x80007488, and -- unlike     *)
(*  balloc's and ialloc's -- this string CARRIES A CONVERSION, so its     *)
(*  [pk_kinds] is [[PkNum]] and printk is called with one vararg          *)
(*  ([a1 = s3 = inum] at +0x38).                                          *)
(* ===================================================================== *)
Definition irc_msg : string :=
  ("ireclaim: orphaned inode %d" ++ String (Ascii.ascii_of_nat 10) EmptyString)%string.
Definition irc_msg_addr : Z := 0x80007488.

Lemma irc_msg_bytes : forall j b, cstring_bytes irc_msg !! j = Some b ->
  KernelData.kernel_data !! (irc_msg_addr + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 29 (destruct j as [|j];
         [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
  vm_compute in Hj; discriminate.
Qed.

Lemma irc_msg_fmt : pk_kinds irc_msg = [PkNum] /\ nonul irc_msg = true /\
                    (Z.of_nat (String.length irc_msg) < 2147483645)%Z.
Proof.
  split_and!; [vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity].
Qed.

(* ===================================================================== *)
(*  MODULE                                                                *)
(* ===================================================================== *)
Module IreclaimProof (BR : BREAD) (BL : BRELSE) (IG : IGET)
                     (BO : BEGIN_OP) (IL : ILOCK) (IU : IUNLOCK)
                     (IP : IPUT) (EO : END_OP) : IRECLAIM.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.
Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac ircidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* the two register-threading invariants.  [irc_thr8] excludes s1..s6, which
   are live across the whole body; [irc_sp] is the pushed frame's sp. *)
Definition irc_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))).

Definition irc_thr8 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
    c <> Rs4 -> c <> Rs5 -> c <> Rs6 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

(* ===================================================================== *)
(*  Vocabulary: the frame, the continuation, the loop wand.               *)
(* ===================================================================== *)
Section IreclaimDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  (* ireclaim's 64-byte frame: ra@56 s0@48 s1@40 s2@32 s3@24 s4@16 s5@8 s6@0 *)
  Definition irc_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈[KT1] (m !!! Regidx Rs6 : mword 64))%I.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md).  [used] here is the contract's
     ORIGINAL set: the loop threads [⌜usedn ⊆ used⌝] beside the resource
     rather than re-indexing this wand, which would need a monotonicity
     step under [wp_next]. *)
  Definition irc_cont `{GEN : GenId} `{CID0 : CpuId}
      (γfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart inodestart ninodes size : Z)
      (used : gset Z)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac) (j : nat)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) : iProp Σ :=
    (* the LITERAL [true], matching the contract's crossing: this function
       can sleep, so its continuation is about an arbitrary hart. *)
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) b lks -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        bslots bn 3 -∗
        iref_slot -∗
        ⌜used' ⊆ used⌝ -∗
        bitmap_res γfs bmapstart cov logstart size used' -∗
        ireg_boot -∗
        WP (Loop : expr riscv_lang))%I.

  (* ONE TURN OF THE LOOP, AT ITS BODY (+0x7c).  This is the wand the
     induction produces and the step block consumes; it is a plain ∀ (its
     own hart [CIDn] is bound inside), so it can be handed to a block lemma
     without a [wp_next_shift]. *)
  Definition irc_loop `{GEN : GenId}
      (γfs : fs_names) (bn : bio_names)
      (cov : gset Z) (logstart bmapstart inodestart ninodes size : Z)
      (used : gset Z) (dev : mword 32)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac) (j : nat)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) (fuel : nat) : iProp Σ :=
    (∀ (Mn : regfile) (inumn : mword 32) (usedn : gset Z) (CIDn : CpuId),
       ⌜(Z.to_nat (ninodes - bv_unsigned inumn) <= fuel)%nat⌝ -∗
       ⌜0 < bv_unsigned inumn < ninodes⌝ -∗
       ⌜usedn ⊆ used⌝ -∗
       ⌜irc_sp m Mn⌝ -∗
       ⌜irc_thr8 m Mn⌝ -∗
       ⌜Mn !!! Regidx Rs1 = (sign_extend' 64 inumn : mword 64)⌝ -∗
       ⌜Mn !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64)⌝ -∗
       ⌜Mn !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64)⌝ -∗
       ⌜Mn !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64)⌝ -∗
       sie_cap_gpr KT1 Mn (K - 8)%nat b (proc_addr j) -∗
       cpu_own 0 true (proc_addr j) b lks -∗
       pc_is (mword_of_int (KernelSyms.ireclaim + 0x7c) : mword 64) -∗
       irc_frame m -∗
       p_pid (proc_addr j) ↦₄{dq} pidv -∗
       sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       bslots bn 3 -∗
       iref_slot -∗
       bitmap_res γfs bmapstart cov logstart size usedn -∗
       ireg_boot -∗
       irc_cont (CID0 := CIDn) γfs bn cov logstart bmapstart inodestart ninodes
                size used pidv dq dqb dqs dqn j m K b lks -∗
       WP (Loop : expr riscv_lang))%I.

  (* the escrow family's projection -- ProofDirlink's [dl_esc_acc] restated,
     because a Proof file may not require another Proof file *)
  Lemma irc_esc_acc (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn γfs γi cov logstart -∗ ic_escrow cn γfs γi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

End IreclaimDefs.

(* ===================================================================== *)
(*  +0xb2 .. +0xc4 : THE ONLY EXIT.  restore all eight, pop, return.      *)
(* ===================================================================== *)
Section IreclaimEpilogue.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma irc_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart inodestart ninodes size : Z)
      (used used' : gset Z)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac)
      (m M : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ireclaim <= K)%nat ->
    used' ⊆ used ->
    irc_sp m M ->
    irc_thr8 m M ->
    sie_cap_gpr KT1 M (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.ireclaim + 0xb2) : mword 64) -∗
    irc_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 3 -∗
    iref_slot -∗
    bitmap_res γfs bmapstart cov logstart size used' -∗
    ireg_boot -∗
    irc_cont (CID0 := CID0) γfs bn cov logstart bmapstart inodestart ninodes size
             used pidv dq dqb dqs dqn j m K b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsub Hsp Hthr.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt #Htext Hpc Hframe Hppid Hsbn Hsbi Hsbb Hsl Hiref Hbm Hboot Hcont".
    iPoseProof (irci_b2 with "Htext") as "Hib2".
    iPoseProof (irci_b4 with "Htext") as "Hib4".
    iPoseProof (irci_b6 with "Htext") as "Hib6".
    iPoseProof (irci_b8 with "Htext") as "Hib8".
    iPoseProof (irci_ba with "Htext") as "Hiba".
    iPoseProof (irci_bc with "Htext") as "Hibc".
    iPoseProof (irci_be with "Htext") as "Hibe".
    iPoseProof (irci_c0 with "Htext") as "Hic0".
    iPoseProof (irci_c2 with "Htext") as "Hic2".
    iPoseProof (irci_c4 with "Htext") as "Hic4".
    rewrite /irc_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8)".
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc5 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc7 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc8 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite Hsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* ===== +0xb2 c.ldsp ra,56(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xb2))
              (mword_of_int 7 : mword 6) Rra
              M (K - 8)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib2 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1sp : irc_sp m P1)
      by (rewrite /irc_sp /P1 upd_ne; [exact Hsp | nz]).
    assert (HP1thr : irc_thr8 m P1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hppb4 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xb2) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xb4)) by pcw.
    iEval (rewrite Hppb4) in "Hpc".
    (* ===== +0xb4 c.ldsp s0,48(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xb4))
              (mword_of_int 6 : mword 6) Rs0
              P1 (K - 8)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib4 [Hf2]").
    { iEval (rewrite HP1sp -Hsp Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -Hsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : irc_sp m P2)
      by (rewrite /irc_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : irc_thr8 m P2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P2 upd_ne; [| regne].
      exact (HP1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hppb6 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xb4) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xb6)) by pcw.
    iEval (rewrite Hppb6) in "Hpc".
    (* ===== +0xb6 c.ldsp s1,40(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xb6))
              (mword_of_int 5 : mword 6) Rs1
              P2 (K - 8)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib6 [Hf3]").
    { iEval (rewrite HP2sp -Hsp Hc3). iExact "Hf3". }
    iIntros (CID3 Hq3) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -Hsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : irc_sp m P3)
      by (rewrite /irc_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : irc_thr8 m P3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P3 upd_ne; [| regne].
      exact (HP2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hppb8 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xb6) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xb8)) by pcw.
    iEval (rewrite Hppb8) in "Hpc".
    (* ===== +0xb8 c.ldsp s2,32(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xb8))
              (mword_of_int 4 : mword 6) Rs2
              P3 (K - 8)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hib8 [Hf4]").
    { iEval (rewrite HP3sp -Hsp Hc4). iExact "Hf4". }
    iIntros (CID4 Hq4) "Hcg Hpc Hf4".
    iEval (rewrite HP3sp -Hsp Hc4) in "Hf4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : irc_sp m P4)
      by (rewrite /irc_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : irc_thr8 m P4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P4 upd_ne; [| regne].
      exact (HP3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    assert (Hppba : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xb8) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xba)) by pcw.
    iEval (rewrite Hppba) in "Hpc".
    (* ===== +0xba c.ldsp s3,24(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xba))
              (mword_of_int 3 : mword 6) Rs3
              P4 (K - 8)%nat (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hiba [Hf5]").
    { iEval (rewrite HP4sp -Hsp Hc5). iExact "Hf5". }
    iIntros (CID5 Hq5) "Hcg Hpc Hf5".
    iEval (rewrite HP4sp -Hsp Hc5) in "Hf5".
    set (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
    assert (HP5sp : irc_sp m P5)
      by (rewrite /irc_sp /P5 upd_ne; [exact HP4sp | nz]).
    assert (HP5thr : irc_thr8 m P5).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P5 upd_ne; [| regne].
      exact (HP4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4ra | nz]).
    assert (Hppbc : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xba) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xbc)) by pcw.
    iEval (rewrite Hppbc) in "Hpc".
    (* ===== +0xbc c.ldsp s4,16(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xbc))
              (mword_of_int 2 : mword 6) Rs4
              P5 (K - 8)%nat (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hibc [Hf6]").
    { iEval (rewrite HP5sp -Hsp Hc6). iExact "Hf6". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf6".
    iEval (rewrite HP5sp -Hsp Hc6) in "Hf6".
    set (P6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P5).
    assert (HP6sp : irc_sp m P6)
      by (rewrite /irc_sp /P6 upd_ne; [exact HP5sp | nz]).
    assert (HP6thr : irc_thr8 m P6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P6 upd_ne; [| regne].
      exact (HP5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HP6ra : P6 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P6 upd_ne; [exact HP5ra | nz]).
    assert (Hppbe : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xbc) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xbe)) by pcw.
    iEval (rewrite Hppbe) in "Hpc".
    (* ===== +0xbe c.ldsp s5,8(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xbe))
              (mword_of_int 1 : mword 6) Rs5
              P6 (K - 8)%nat (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hibe [Hf7]").
    { iEval (rewrite HP6sp -Hsp Hc7). iExact "Hf7". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf7".
    iEval (rewrite HP6sp -Hsp Hc7) in "Hf7".
    set (P7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P6).
    assert (HP7sp : irc_sp m P7)
      by (rewrite /irc_sp /P7 upd_ne; [exact HP6sp | nz]).
    assert (HP7thr : irc_thr8 m P7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P7 upd_ne; [| regne].
      exact (HP6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HP7ra : P7 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P7 upd_ne; [exact HP6ra | nz]).
    assert (Hppc0 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xbe) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xc0)) by pcw.
    iEval (rewrite Hppc0) in "Hpc".
    (* ===== +0xc0 c.ldsp s6,0(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xc0))
              (mword_of_int 0 : mword 6) Rs6
              P7 (K - 8)%nat (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hic0 [Hf8]").
    { iEval (rewrite HP7sp -Hsp Hc8). iExact "Hf8". }
    iIntros (CID8 Hq8) "Hcg Hpc Hf8".
    iEval (rewrite HP7sp -Hsp Hc8) in "Hf8".
    set (P8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P7).
    assert (HP8sp : irc_sp m P8)
      by (rewrite /irc_sp /P8 upd_ne; [exact HP7sp | nz]).
    assert (HP8thr : irc_thr8 m P8).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P8 upd_ne; [| regne].
      exact (HP7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HP8ra : P8 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P8 upd_ne; [exact HP7ra | nz]).
    assert (Hppc2 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xc0) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xc2)) by pcw.
    iEval (rewrite Hppc2) in "Hpc".
    (* ===== +0xc2 c.addi16sp sp,64 : pop ===== *)
    assert (Hwv : add_vec (P8 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP8sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)) : mword 64)
                   = 18446744073709551552) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)) : mword 64)
                    = 64) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551552 + 64)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64) + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0) by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P8 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P8 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HP8sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 8)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1"|].
      iSplitL "Hf2"; [iExists _; iExact "Hf2"|].
      iSplitL "Hf3"; [iExists _; iExact "Hf3"|].
      iSplitL "Hf4"; [iExists _; iExact "Hf4"|].
      iSplitL "Hf5"; [iExists _; iExact "Hf5"|].
      iSplitL "Hf6"; [iExists _; iExact "Hf6"|].
      iSplitL "Hf7"; [iExists _; iExact "Hf7"|].
      iSplitL "Hf8"; [iExists _; iExact "Hf8"|].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xc2))
              (mword_of_int 4 : mword 6) P8 (K - 8)%nat 8 b Hpop
              with "Hcg Hpc Hic2 Hstk").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (P9 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P8 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> P8).
    assert (Hnk : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hppc4 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xc2) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xc4)) by pcw.
    iEval (rewrite Hppc4) in "Hpc".
    (* ===== +0xc4 c.ret ===== *)
    assert (HP9ra : P9 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P9 upd_ne; [exact HP8ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xc4)) Rra P9 K b
              ltac:(nz) with "Hcg Hpc Hic4").
    iIntros (CID10 Hq10) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P9 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP9ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P9 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P9 upd_eq; exact Hwv).
    assert (Cs6 : P9 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_eq. reflexivity. }
    assert (Cs5 : P9 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_eq. reflexivity. }
    assert (Cs4 : P9 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_eq. reflexivity. }
    assert (Cs3 : P9 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_eq. reflexivity. }
    assert (Cs2 : P9 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_eq. reflexivity. }
    assert (Cs1 : P9 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Cs0 : P9 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P9 upd_ne; [| nz]. rewrite /P8 upd_ne; [| nz].
      rewrite /P7 upd_ne; [| nz]. rewrite /P6 upd_ne; [| nz].
      rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Hfin : irc_thr8 m P9).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /P9 upd_ne; [| regne].
      exact (HP8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Cs7 : P9 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; ircidx).
    assert (Cs8 : P9 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; ircidx).
    assert (Cs9 : P9 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; ircidx).
    assert (Cs10 : P9 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; ircidx).
    assert (Cs11 : P9 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; ircidx).
    assert (Hcs : callee_saved m P9)
      by (unfold callee_saved; split_and!; assumption).
   iDestruct (cpu_own_transport CID0 CID10 0 true (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /irc_cont.
    iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P9 used' with "[%] Hcg Hcnt Hpc Hsbn Hsbi Hsbb Hppid
                                       Hsl Hiref [%] Hbm Hboot");
      [exact Hcs | exact Hsub].
  Qed.

End IreclaimEpilogue.

(* ===================================================================== *)
(*  +0x6e .. +0x7a : THE STEP.  inum++, reload sb.ninodes, and the        *)
(*  [bgeu a5,a4] that either leaves the loop or re-enters its body.       *)
(*                                                                        *)
(*  BOTH paths through the body arrive here: the plain arm jumps from     *)
(*  +0xb0, the orphan block FALLS IN from +0x6c.  That is why the loop    *)
(*  wand is a HYPOTHESIS of this lemma rather than this block being part  *)
(*  of the induction -- [irc_orphan] can then re-enter the loop without   *)
(*  itself being inside it.                                               *)
(* ===================================================================== *)
Section IreclaimStep.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma irc_step `{GEN : GenId} `{CID0 : CpuId}
      (j : nat) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart inodestart ninodes size : Z)
      (used usedn : gset Z) (dev : mword 32) (inum : mword 32) (fuel : nat)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac)
      (m Ml : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ireclaim <= K)%nat ->
    ninodes < 2 ^ 31 ->
    usedn ⊆ used ->
    (Z.to_nat (ninodes - bv_unsigned inum) <= S fuel)%nat ->
    0 < bv_unsigned inum < ninodes ->
    irc_sp m Ml ->
    irc_thr8 m Ml ->
    Ml !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64) ->
    Ml !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64) ->
    Ml !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64) ->
    Ml !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64) ->
    sie_cap_gpr KT1 Ml (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.ireclaim + 0x6e) : mword 64) -∗
    irc_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 3 -∗
    iref_slot -∗
    bitmap_res γfs bmapstart cov logstart size usedn -∗
    ireg_boot -∗
    irc_loop γfs bn cov logstart bmapstart inodestart ninodes size used dev
             pidv dq dqb dqs dqn j m K b lks fuel -∗
    irc_cont (CID0 := CID0) γfs bn cov logstart bmapstart inodestart ninodes size
             used pidv dq dqb dqs dqn j m K b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hn31 Hsub Hfuel Hinum Hsp Hthr Hs1 Hs4 Hs5 Hs6.
    pose proof HK as HK'. 
    pose proof (bv_unsigned_in_range _ inum) as [Hinum0 Hinum32].
    assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
      by (vm_compute; reflexivity).
    rewrite Hm32 in Hinum32.
    assert (Hinum31 : bv_unsigned inum < 2147483648)
      by (change (2^31)%Z with 2147483648%Z in Hn31; lia).
    iIntros "Hcg Hcnt #Htext Hpc Hframe Hppid Hsbn Hsbi Hsbb Hsl Hiref Hbm Hboot
              Hloop Hcont".
    iPoseProof (irci_6e with "Htext") as "Hi6e".
    iPoseProof (irci_70 with "Htext") as "Hi70".
    iPoseProof (irci_74 with "Htext") as "Hi74".
    iPoseProof (irci_78 with "Htext") as "Hi78".
    (* the NEXT inum, as the 32-bit word the code carries *)
    set (inum1 := (mword_of_int (bv_unsigned inum + 1) : mword 32)).
    assert (Hinum1u : bv_unsigned inum1 = bv_unsigned inum + 1).
    { rewrite /inum1 moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    assert (Hsext1 : (sign_extend' 64 inum1 : mword 64)
                     = mword_of_int (bv_unsigned inum + 1)).
    { rewrite (ds_sext_small inum1 ltac:(rewrite Hinum1u; lia)) Hinum1u.
      reflexivity. }
    (* ===== +0x6e c.addi s1,1 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x6e)) Rs1
              (mword_of_int 1 : mword 6) Ml (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6e").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (S1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (rget Ml Rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> Ml).
    assert (Hone : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                    : mword 64) = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HS1s1 : S1 !!! Regidx Rs1 = (sign_extend' 64 inum1 : mword 64)).
    { rewrite /S1 upd_eq. rgne.
      rewrite Hs1 Hsext1 (ds_sext_small inum Hinum31) Hone.
      apply bv_eq. rewrite !add_vec64_unsigned !moi64_unsigned.
      rewrite (bvw64_small (bv_unsigned inum)
                 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
      rewrite (bvw64_small 1
                 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
      reflexivity. }
    assert (HS1s4 : S1 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /S1 upd_ne; [exact Hs4 | nz]).
    assert (HS1s5 : S1 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /S1 upd_ne; [exact Hs5 | nz]).
    assert (HS1s6 : S1 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /S1 upd_ne; [exact Hs6 | nz]).
    assert (HS1sp : irc_sp m S1)
      by (rewrite /irc_sp /S1 upd_ne; [exact Hsp | nz]).
    assert (HS1thr : irc_thr8 m S1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /S1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x6e) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x70)) by pcw.
    iEval (rewrite Hpp70) in "Hpc".
    (* ===== +0x70 lw a4,12(s4) : a4 := sb.ninodes ===== *)
    assert (Hsbnadr : add_vec (rget S1 Rs4)
                        (sign_extend' 64 (mword_of_int 12 : mword 12))
                      = sb_ninodes).
    { rgne. rewrite HS1s4. rewrite /sb_ninodes /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hsbnadr) in "Hsbn".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ireclaim + 0x70)) Ra4 Rs4
              (mword_of_int 12 : mword 12) S1 (K - 8)%nat
              (mword_of_int ninodes : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi70 Hsbn").
    iIntros (CID2 Hq2) "Hcg Hpc Hsbn".
    iEval (rewrite Hsbnadr) in "Hsbn".
    set (S2 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (mword_of_int ninodes : mword 32))]> S1).
    assert (HS2a4 : S2 !!! Regidx Ra4 = (mword_of_int ninodes : mword 64)).
    { rewrite /S2 upd_eq. apply sext32_64_small.
      change (2^31)%Z with 2147483648%Z. lia. }
    assert (HS2s1 : S2 !!! Regidx Rs1 = (sign_extend' 64 inum1 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1s1 | nz]).
    assert (HS2s4 : S2 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1s4 | nz]).
    assert (HS2s5 : S2 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1s5 | nz]).
    assert (HS2s6 : S2 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1s6 | nz]).
    assert (HS2sp : irc_sp m S2)
      by (rewrite /irc_sp /S2 upd_ne; [exact HS1sp | nz]).
    assert (HS2thr : irc_thr8 m S2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /S2 upd_ne; [| regne].
      exact (HS1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x70) : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0x74)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    (* ===== +0x74 addiw a5,s1,0 ===== *)
    iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x74)) Ra5 Rs1
              (mword_of_int 0 : mword 12) S2 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (S3 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (rget S2 Rs1)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> S2).
    assert (HS3a5 : S3 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum + 1) : mword 64)).
    { rewrite /S3 upd_eq. rgne. rewrite HS2s1 iu_off0.
      rewrite (iu_sub31_sext inum1). exact Hsext1. }
    assert (HS3a4 : S3 !!! Regidx Ra4 = (mword_of_int ninodes : mword 64))
      by (rewrite /S3 upd_ne; [exact HS2a4 | nz]).
    assert (HS3s1 : S3 !!! Regidx Rs1 = (sign_extend' 64 inum1 : mword 64))
      by (rewrite /S3 upd_ne; [exact HS2s1 | nz]).
    assert (HS3s4 : S3 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /S3 upd_ne; [exact HS2s4 | nz]).
    assert (HS3s5 : S3 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /S3 upd_ne; [exact HS2s5 | nz]).
    assert (HS3s6 : S3 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /S3 upd_ne; [exact HS2s6 | nz]).
    assert (HS3sp : irc_sp m S3)
      by (rewrite /irc_sp /S3 upd_ne; [exact HS2sp | nz]).
    assert (HS3thr : irc_thr8 m S3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /S3 upd_ne; [| regne].
      exact (HS2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0x78 bgeu a5,a4 : is the scan over? ===== *)
    destruct (Z.geb (bv_unsigned inum + 1) ninodes) eqn:Hge.
    - (* ---- OVER: the epilogue at +0xb2 ---- *)
      assert (Hcmp : zopz0zKzJ_u (rget S3 Ra5) (rget S3 Ra4) = true).
      { rgne. rgne. rewrite HS3a5 HS3a4.
        rewrite (ds_bgeu_moi (bv_unsigned inum + 1) ninodes
                   ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)
                   ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)).
        exact Hge. }
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x78))
                (mword_of_int 58 : mword 13) Ra4 Ra5 S3 (K - 8)%nat b
                ltac:(nz) ltac:(nz) Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi78").
      iApply bi.later_intro. iIntros (CID4 Hq4) "Hcg Hpc".
      assert (Hjt : add_vec (mword_of_int (KernelSyms.ireclaim + 0x78) : mword 64)
                      (sign_extend' 64 (mword_of_int 58 : mword 13))
                    = mword_of_int (KernelSyms.ireclaim + 0xb2)) by pcw.
      iEval (rewrite Hjt) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID4 0 true (proc_addr j) b 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (irc_epilogue (CID0 := CID4) j bn γfs cov logstart bmapstart
                inodestart ninodes size used usedn pidv dq dqb dqs dqn
                m S3 K b lks HK Hsub HS3sp HS3thr
                with "Hcg Hcnt Htext Hpc Hframe Hppid Hsbn Hsbi Hsbb Hsl
                      Hiref Hbm Hboot [Hcont]").
      { iApply (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID4)
                  ltac:(wp_next_chain) with "Hcont"). }
    - (* ---- ANOTHER TURN: back to the body at +0x7c ---- *)
      assert (Hcmp : zopz0zKzJ_u (rget S3 Ra5) (rget S3 Ra4) = false).
      { rgne. rgne. rewrite HS3a5 HS3a4.
        rewrite (ds_bgeu_moi (bv_unsigned inum + 1) ninodes
                   ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)
                   ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)).
        exact Hge. }
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x78))
                (mword_of_int 58 : mword 13) Ra4 Ra5 S3 (K - 8)%nat b
                ltac:(nz) ltac:(nz) Hcmp with "Hcg Hpc Hi78").
      iIntros (CID4 Hq4) "Hcg Hpc".
      assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x78) : mword 64) 4
                      = mword_of_int (KernelSyms.ireclaim + 0x7c)) by pcw.
      iEval (rewrite Hpp7c) in "Hpc".
      assert (Hltn : bv_unsigned inum + 1 < ninodes).
      { destruct (Z.lt_ge_cases (bv_unsigned inum + 1) ninodes) as [Hok|Hc];
          [exact Hok |].
        exfalso. rewrite <- Z.geb_le in Hc. rewrite Hc in Hge. discriminate. }
      iDestruct (cpu_own_transport CID0 CID4 0 true (proc_addr j) b 
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      rewrite /irc_loop.
      iApply ("Hloop" $! S3 inum1 usedn CID4
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hpc Hframe
                      Hppid Hsbn Hsbi Hsbb Hsl Hiref Hbm Hboot [Hcont]").
      { rewrite Hinum1u. lia. }
      { rewrite Hinum1u. lia. }
      { exact Hsub. }
      { exact HS3sp. }
      { exact HS3thr. }
      { exact HS3s1. }
      { exact HS3s4. }
      { exact HS3s5. }
      { exact HS3s6. }
      { iApply (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID4)
                  ltac:(wp_next_chain) with "Hcont"). }
  Qed.

End IreclaimStep.

(* ===================================================================== *)
(*  +0x38 .. +0x6c : THE ORPHAN.  printk("%d") / iget / brelse /          *)
(*  begin_op / ilock / iunlock / iput / end_op, then FALL into the step.  *)
(*                                                                        *)
(*  THE BUFFER IS HELD ACROSS iget (+0x44) and only given back by the     *)
(*  brelse at +0x4c -- which is still BEFORE begin_op at +0x54, so the    *)
(*  three slot units never have to stretch to four.                       *)
(*                                                                        *)
(*  THE [beq s3,zero] AT +0x50 IS DEAD, and what refutes it is iget's     *)
(*  POSTCONDITION ([a0 = ientry k] with [k < NINODE], hence               *)
(*  [IcacheRef.ientry_ne_zero]) -- no premise of this contract says       *)
(*  anything about it.                                                    *)
(* ===================================================================== *)
Section IreclaimOrphan.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma irc_orphan `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname) (γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart ninodes size : Z)
      (nib : nat) (used usedn : gset Z)
      (dev inum bno : mword 32) (kk : nat)
      (bs bsd0 : list (bv 8)) (ds : list dinode) (d0 : bool) (fuel : nat)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac)
      (m Ml : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ireclaim <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    ireg_blocks_ok inodestart nib cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    cov_below cov size ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (Z.to_nat (ninodes - bv_unsigned inum) <= S fuel)%nat ->
    0 < bv_unsigned inum < ninodes ->
    usedn ⊆ used ->
    (kk < NBUF)%nat ->
    (* ---- LICENCE (e)'s PREMISES (increment C'-lite, fs-fragments.md §7.1).
       This lemma runs from +0x38, i.e. AFTER the scan has bread the inode
       block and decoded it, and it holds the handle until the brelse at
       +0x4c -- which is two instructions PAST the iget at +0x44.  So what
       the caller already knows about those bytes is exactly what founds the
       iget's licence, at the cost of four pure premises here and four
       [exact]s at the one call site. ---- *)
    bs = diblk_bytes ds ->
    diblk_wf ds ->
    bv_unsigned (di_type (ds !!! DinodeEnc.islot inum)) <> 0 ->
    uint bno = IBLOCK inum inodestart ->
    irc_sp m Ml ->
    irc_thr8 m Ml ->
    Ml !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64) ->
    Ml !!! Regidx Rs2 = bnode kk ->
    Ml !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64) ->
    Ml !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64) ->
    Ml !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64) ->
    Ml !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64) ->
    (* irc_orphan's cone: printk ("pr", 14), iget/iput ("itable", 2),
       begin_op/end_op ("log", 3), ilock ("bcache", 4), iunlock
       ("sleep lock", 6) -- "itable" is the lowest. *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 Ml (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) b lks -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.ireclaim + 0x38) : mword 64) -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    ireg_inv γi γfs inodestart nib -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    ic_sleeplocks cn -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    irc_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 2 -∗
    iref_slot -∗
    bitmap_res γfs bmapstart cov logstart size usedn -∗
    ireg_boot -∗
    bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bno bs bsd0 d0 -∗
    irc_loop γfs bn cov logstart bmapstart inodestart ninodes size used dev
             pidv dq dqb dqs dqn j m K b lks fuel -∗
    irc_cont (CID0 := CID0) γfs bn cov logstart bmapstart inodestart ninodes size
             used pidv dq dqb dqs dqn j m K b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hst Hblk Hsize Hbm0 Hbmcov Hbmlog Hcovb Hnnib Hn31 Hpk
           Hj Hgl Hfuel Hinum Hsub Hkk Hbseq Hdswf Htnz Hbnoeq
           Hsp Hthr Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hbelow.
    pose proof HK as HK'. 
    pose proof irc_msg_fmt as (Hkmsg & Hnmsg & Hlmsg).
    assert (Hnibin : bv_unsigned inum < 16 * Z.of_nat nib) by lia.
    destruct (Hblk inum Hnibin) as [Hibcov Hiblog].
    iIntros "Hcg Hcnt #Htext #Hkdata Hpc #Hpenv #Hbio #Hlctx
              #Hseam #Hgen #Hireg #Hitb2 #Hitbl #Hesc #Hslks #Hprocs
              #Hdevi #Hdgeom #Hdlock Hframe Hppid Hsbn Hsbi Hsbb Hsl Hiref
              Hbm Hboot Hlk Hloop Hcont".
    iPoseProof (printk_env_panic with "Hpenv") as "#Hpanenv".
    iPoseProof (kernel_data_string irc_msg_addr irc_msg
                  (mword_of_int irc_msg_addr) eq_refl
                  ltac:(unfold text_end, irc_msg_addr; lia) irc_msg_bytes
                  with "Hkdata") as "#Hstr".
    iPoseProof (irci_38 with "Htext") as "Hi38".
    iPoseProof (irci_3a with "Htext") as "Hi3a".
    iPoseProof (irci_3c with "Htext") as "Hi3c".
    iPoseProof (irci_40 with "Htext") as "Hi40".
    iPoseProof (irci_42 with "Htext") as "Hi42".
    iPoseProof (irci_44 with "Htext") as "Hi44".
    iPoseProof (irci_48 with "Htext") as "Hi48".
    iPoseProof (irci_4a with "Htext") as "Hi4a".
    iPoseProof (irci_4c with "Htext") as "Hi4c".
    iPoseProof (irci_50 with "Htext") as "Hi50".
    iPoseProof (irci_54 with "Htext") as "Hi54".
    iPoseProof (irci_58 with "Htext") as "Hi58".
    iPoseProof (irci_5a with "Htext") as "Hi5a".
    iPoseProof (irci_5e with "Htext") as "Hi5e".
    iPoseProof (irci_60 with "Htext") as "Hi60".
    iPoseProof (irci_64 with "Htext") as "Hi64".
    iPoseProof (irci_66 with "Htext") as "Hi66".
    iPoseProof (irci_6a with "Htext") as "Hi6a".
    (* ===== +0x38 c.mv a1,s3 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x38)) Ra1 Rs3
              Ml (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi38").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (O1 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget Ml Rs3))]> Ml).
    assert (HO1s1 : O1 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O1 upd_ne; [exact Hs1 | nz]).
    assert (HO1s2 : O1 !!! Regidx Rs2 = bnode kk)
      by (rewrite /O1 upd_ne; [exact Hs2 | nz]).
    assert (HO1s3 : O1 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O1 upd_ne; [exact Hs3 | nz]).
    assert (HO1s4 : O1 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O1 upd_ne; [exact Hs4 | nz]).
    assert (HO1s5 : O1 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O1 upd_ne; [exact Hs5 | nz]).
    assert (HO1s6 : O1 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O1 upd_ne; [exact Hs6 | nz]).
    assert (HO1sp : irc_sp m O1)
      by (rewrite /irc_sp /O1 upd_ne; [exact Hsp | nz]).
    assert (HO1thr : irc_thr8 m O1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x38) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== +0x3a c.mv a0,s6 : a0 := the format string ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x3a)) Ra0 Rs6
              O1 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3a").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (O2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget O1 Rs6))]> O1).
    assert (HO2a0 : O2 !!! Regidx Ra0 = (mword_of_int irc_msg_addr : mword 64)).
    { rewrite /O2 upd_eq. rgne. rewrite HO1s6. apply add_vec_zero_l. }
    assert (HO2s1 : O2 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O2 upd_ne; [exact HO1s1 | nz]).
    assert (HO2s2 : O2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /O2 upd_ne; [exact HO1s2 | nz]).
    assert (HO2s3 : O2 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O2 upd_ne; [exact HO1s3 | nz]).
    assert (HO2s4 : O2 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O2 upd_ne; [exact HO1s4 | nz]).
    assert (HO2s5 : O2 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O2 upd_ne; [exact HO1s5 | nz]).
    assert (HO2s6 : O2 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O2 upd_ne; [exact HO1s6 | nz]).
    assert (HO2sp : irc_sp m O2)
      by (rewrite /irc_sp /O2 upd_ne; [exact HO1sp | nz]).
    assert (HO2thr : irc_thr8 m O2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O2 upd_ne; [| regne].
      exact (HO1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c jal ra,printk ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x3c)) Rra
              (mword_of_int 2084956 : mword 21) O2 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3c").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (O3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x3c) : mword 64) 4)]> O2).
    assert (Htgtpk : add_vec (mword_of_int (KernelSyms.ireclaim + 0x3c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084956 : mword 21))
                     = mword_of_int KernelSyms.printk) by pcw.
    iEval (rewrite Htgtpk) in "Hpc".
    assert (HO3a0 : O3 !!! Regidx Ra0 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O3 upd_ne; [exact HO2a0 | nz]).
    assert (HO3ra : O3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x3c) : mword 64) 4)
      by (rewrite /O3; apply upd_eq).
    assert (HO3s1 : O3 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O3 upd_ne; [exact HO2s1 | nz]).
    assert (HO3s2 : O3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /O3 upd_ne; [exact HO2s2 | nz]).
    assert (HO3s3 : O3 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O3 upd_ne; [exact HO2s3 | nz]).
    assert (HO3s4 : O3 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O3 upd_ne; [exact HO2s4 | nz]).
    assert (HO3s5 : O3 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O3 upd_ne; [exact HO2s5 | nz]).
    assert (HO3s6 : O3 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O3 upd_ne; [exact HO2s6 | nz]).
    assert (HO3sp : irc_sp m O3)
      by (rewrite /irc_sp /O3 upd_ne; [exact HO2sp | nz]).
    assert (HO3thr : irc_thr8 m O3).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O3 upd_ne; [| regne].
      exact (HO2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID0 CID3 0 true (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID3) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* the panic tail runs at depth 0, so the held set is forced empty and
       printk's order premise ("pr", 14) needs no hypothesis here. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iApply (Hpk CID3 O3 (K - 8)%nat true (proc_addr j)
              DfracDiscarded irc_msg [PkANum] b _
              ltac:(lia) Hlmsg Hnmsg ltac:(rewrite Hkmsg; reflexivity)
              ltac:(cbn [length]; lia)
              with "Hcg Htext Hkdata Hpc Hcnt Hpenv [] []").
    all: try lkbelow.
    { rewrite HO3a0. iExact "Hstr". }
    { simpl. iSplit; done. }
    iIntros (CID4 Hq4 mP) "Hcg Hpc %Hcsp Hcnt _ _".
    destruct Hcsp as (Hcspk & Hrapk).
    assert (Hpc40 : ret_pc (O3 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0x40))
      by (rewrite HO3ra; pcw).
    iEval (rewrite Hpc40) in "Hpc".
    pose proof Hcspk as Hcspk_cs.
    assert (HmPs1 : mP !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcspk_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HO3s1).
    assert (HmPs2 : mP !!! Regidx Rs2 = bnode kk)
      by (rewrite (callee_saved_lookup Hcspk_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HO3s2).
    assert (HmPs3 : mP !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcspk_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HO3s3).
    assert (HmPs4 : mP !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcspk_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HO3s4).
    assert (HmPs5 : mP !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcspk_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HO3s5).
    assert (HmPs6 : mP !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcspk_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HO3s6).
    assert (HmPsp : irc_sp m mP).
    { rewrite /irc_sp
        (callee_saved_lookup Hcspk_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HO3sp. }
    assert (HmPthr : irc_thr8 m mP).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcspk_cs c Hcs).
      exact (HO3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0x40 c.mv a1,s3 : a1 := inum ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x40)) Ra1 Rs3
              mP (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi40").
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (O4 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mP Rs3))]> mP).
    assert (HO4a1 : O4 !!! Regidx Ra1 = (sign_extend' 64 inum : mword 64)).
    { rewrite /O4 upd_eq. rgne. rewrite HmPs3. apply add_vec_zero_l. }
    assert (HO4s1 : O4 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O4 upd_ne; [exact HmPs1 | nz]).
    assert (HO4s2 : O4 !!! Regidx Rs2 = bnode kk)
      by (rewrite /O4 upd_ne; [exact HmPs2 | nz]).
    assert (HO4s3 : O4 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O4 upd_ne; [exact HmPs3 | nz]).
    assert (HO4s4 : O4 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O4 upd_ne; [exact HmPs4 | nz]).
    assert (HO4s5 : O4 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O4 upd_ne; [exact HmPs5 | nz]).
    assert (HO4s6 : O4 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O4 upd_ne; [exact HmPs6 | nz]).
    assert (HO4sp : irc_sp m O4)
      by (rewrite /irc_sp /O4 upd_ne; [exact HmPsp | nz]).
    assert (HO4thr : irc_thr8 m O4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O4 upd_ne; [| regne].
      exact (HmPthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x42)) by pcw.
    iEval (rewrite Hpp42) in "Hpc".
    (* ===== +0x42 c.mv a0,s5 : a0 := dev ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x42)) Ra0 Rs5
              O4 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi42").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (O5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget O4 Rs5))]> O4).
    assert (HO5a0 : O5 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /O5 upd_eq. rgne. rewrite HO4s5. apply add_vec_zero_l. }
    assert (HO5a1 : O5 !!! Regidx Ra1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O5 upd_ne; [exact HO4a1 | nz]).
    assert (HO5s1 : O5 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O5 upd_ne; [exact HO4s1 | nz]).
    assert (HO5s2 : O5 !!! Regidx Rs2 = bnode kk)
      by (rewrite /O5 upd_ne; [exact HO4s2 | nz]).
    assert (HO5s4 : O5 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O5 upd_ne; [exact HO4s4 | nz]).
    assert (HO5s5 : O5 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O5 upd_ne; [exact HO4s5 | nz]).
    assert (HO5s6 : O5 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O5 upd_ne; [exact HO4s6 | nz]).
    assert (HO5sp : irc_sp m O5)
      by (rewrite /irc_sp /O5 upd_ne; [exact HO4sp | nz]).
    assert (HO5thr : irc_thr8 m O5).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O5 upd_ne; [| regne].
      exact (HO4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x42) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x44)) by pcw.
    iEval (rewrite Hpp44) in "Hpc".
    (* ===== +0x44 jal ra,iget -- THE BUFFER IS STILL HELD ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x44)) Rra
              (mword_of_int 2095530 : mword 21) O5 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi44").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (O6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x44) : mword 64) 4)]> O5).
    assert (Htgtig : add_vec (mword_of_int (KernelSyms.ireclaim + 0x44) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095530 : mword 21))
                     = mword_of_int KernelSyms.iget) by pcw.
    iEval (rewrite Htgtig) in "Hpc".
    assert (HO6a0 : O6 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O6 upd_ne; [exact HO5a0 | nz]).
    assert (HO6a1 : O6 !!! Regidx Ra1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O6 upd_ne; [exact HO5a1 | nz]).
    assert (HO6ra : O6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x44) : mword 64) 4)
      by (rewrite /O6; apply upd_eq).
    assert (HO6s1 : O6 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O6 upd_ne; [exact HO5s1 | nz]).
    assert (HO6s2 : O6 !!! Regidx Rs2 = bnode kk)
      by (rewrite /O6 upd_ne; [exact HO5s2 | nz]).
    assert (HO6s4 : O6 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O6 upd_ne; [exact HO5s4 | nz]).
    assert (HO6s5 : O6 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O6 upd_ne; [exact HO5s5 | nz]).
    assert (HO6s6 : O6 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O6 upd_ne; [exact HO5s6 | nz]).
    assert (HO6sp : irc_sp m O6)
      by (rewrite /irc_sp /O6 upd_ne; [exact HO5sp | nz]).
    assert (HO6thr : irc_thr8 m O6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O6 upd_ne; [| regne].
      exact (HO5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID4 CID7 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID3) (CIDb := CID7) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* ================================================================== *)
    (*  THE LICENCE (increment C'-lite, fs-fragments.md §7.1), licence (e)  *)
    (* ================================================================== *)
    (*  ireclaim's iget is at +0x44 and its brelse is at +0x4c, so THE
        BUFFER IS STILL IN HAND: [DinodeSlot.ds_held_L] takes the block's
        client half out of the handle and hands back a wand to return it.
        That half, at bytes which decode to a record with a nonzero type,
        IS licence (e) -- and it is STRONGER than §20.4's [bio_locked]
        sketch: the [fs_L] element sits at half-plus-half, so while this
        walk holds one half no [ireg_write_au] / [ireg_claim_au] /
        [ireg_free_au] at ANY inum of this block can fire (§7.1.3, §16.2's
        serialiser as a resource fact rather than a paragraph).

        BOOT-ONLY: sheltered by the pre-userspace one-shot [ireg_boot]
        (plank 3, iget-licence follow-on; see fs-fragments.md §7.1.7).  The
        record ireclaim igets here is CLAIM-SHAPED -- type nonzero, nlink
        zero -- and §7.1.7's finding is that the licence alone does not
        exclude that; what excludes it is that ireclaim is reachable only
        from fsinit, i.e. before [kexec("/init")] and before any second
        process exists.  That is a boot-order fact, [ireg_boot] is the
        shelter's DESIGNATED CARRIER for it, and the model does not state
        it here. *)
    iEval (rewrite /bio_locked) in "Hlk".
    iDestruct (ds_held_L with "Hlk") as "[HpL Hlkback]".
    (* ...AND THE BOOT SHELTER RIDES WITH IT (iclaim-ledger.md §2.6, landed
       in [IgetLic]'s [BufL] arm).  Licence (e) is now BOOT-GATED: the
       presenter lends [ireg_boot] alongside the block half, which is what
       makes (e) unpresentable after the seal fires and therefore refutable
       at an in-transition box.  This walk is the ONE site in the tree that
       presents (e) and it is a boot-thread proof, so the token is simply
       [Hboot], threaded here and taken straight back below -- BORROWED,
       exactly like the block half beside it. *)
    iAssert (iname γi γfs inum (BufL (uint bno) ds)) with "[HpL Hboot]" as "Hlic".
    { rewrite /iname /fsblock -Hbseq. iFrame "HpL Hboot". iPureIntro.
      split; [exact Hdswf | exact Htnz]. }
    iApply (IG.wp_iget_sconf gtl cn γfs γi cov logstart nib dev inum
              (BufL (uint bno) ds)
              O6 0%nat true (proc_addr j) (K - 8)%nat b lks
              ltac:(lia) ltac:(cbn [Z.of_nat]; lia) Hnibin
              HO6a0 HO6a1
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hkdata Hpc Hitb2 Hitbl Hesc Hpanenv Hiref Hlic").
    all: try lkbelow.
    iIntros (CID8 Hq8 mI kslot q) "Hcg Hcnt Hpc %Higfacts Href Hlic".
    (* ...and the half goes straight back into the handle, unspent.  The
       unfolding is done IN the hypothesis: [fs_L]'s ghost_map notation is
       not in scope in this file, and writing the target proposition out
       would import it for one line. *)
    iEval (rewrite /iname /fsblock -Hbseq) in "Hlic".
    iDestruct "Hlic" as "(HpL & _ & _ & Hboot)".
    iDestruct ("Hlkback" with "HpL") as "Hlk".
    iAssert (bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bno bs bsd0 d0)
      with "[Hlk]" as "Hlk"; [rewrite /bio_locked; iExact "Hlk" |].
    destruct Higfacts as (Hcsig & Hkslot & HmIa0).
    assert (Hpc48 : ret_pc (O6 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0x48))
      by (rewrite HO6ra; pcw).
    iEval (rewrite Hpc48) in "Hpc".
    pose proof Hcsig as Hcsig_cs.
    assert (HmIs1 : mI !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsig_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HO6s1).
    assert (HmIs2 : mI !!! Regidx Rs2 = bnode kk)
      by (rewrite (callee_saved_lookup Hcsig_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HO6s2).
    assert (HmIs4 : mI !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcsig_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HO6s4).
    assert (HmIs5 : mI !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsig_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HO6s5).
    assert (HmIs6 : mI !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcsig_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HO6s6).
    assert (HmIsp : irc_sp m mI).
    { rewrite /irc_sp
        (callee_saved_lookup Hcsig_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HO6sp. }
    assert (HmIthr : irc_thr8 m mI).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsig_cs c Hcs).
      exact (HO6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* the two singletons the run's slot needs, projected out of the families *)
    iDestruct (irc_esc_acc cn γfs γi cov logstart kslot Hkslot with "Hesc")
      as "#Hescrow".
    iDestruct (ic_sleeplocks_acc cn kslot Hkslot with "Hslks")
      as (gil gisl) "#Hslk".
    (* ===== +0x48 c.mv s3,a0 : s3 := ip (the register is REUSED) ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x48)) Rs3 Ra0
              mI (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi48").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (O7 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mI Ra0))]> mI).
    assert (HO7s3 : O7 !!! Regidx Rs3 = ientry kslot).
    { rewrite /O7 upd_eq. rgne. rewrite HmIa0. apply add_vec_zero_l. }
    assert (HO7s1 : O7 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O7 upd_ne; [exact HmIs1 | nz]).
    assert (HO7s2 : O7 !!! Regidx Rs2 = bnode kk)
      by (rewrite /O7 upd_ne; [exact HmIs2 | nz]).
    assert (HO7s4 : O7 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O7 upd_ne; [exact HmIs4 | nz]).
    assert (HO7s5 : O7 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O7 upd_ne; [exact HmIs5 | nz]).
    assert (HO7s6 : O7 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O7 upd_ne; [exact HmIs6 | nz]).
    assert (HO7sp : irc_sp m O7)
      by (rewrite /irc_sp /O7 upd_ne; [exact HmIsp | nz]).
    assert (HO7thr : irc_thr8 m O7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O7 upd_ne; [| regne].
      exact (HmIthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x48) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x4a)) by pcw.
    iEval (rewrite Hpp4a) in "Hpc".
    (* ===== +0x4a c.mv a0,s2 : a0 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x4a)) Ra0 Rs2
              O7 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4a").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (O8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget O7 Rs2))]> O7).
    assert (HO8a0 : O8 !!! Regidx Ra0 = bnode kk).
    { rewrite /O8 upd_eq. rgne. rewrite HO7s2. apply add_vec_zero_l. }
    assert (HO8s1 : O8 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O8 upd_ne; [exact HO7s1 | nz]).
    assert (HO8s3 : O8 !!! Regidx Rs3 = ientry kslot)
      by (rewrite /O8 upd_ne; [exact HO7s3 | nz]).
    assert (HO8s4 : O8 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O8 upd_ne; [exact HO7s4 | nz]).
    assert (HO8s5 : O8 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O8 upd_ne; [exact HO7s5 | nz]).
    assert (HO8s6 : O8 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O8 upd_ne; [exact HO7s6 | nz]).
    assert (HO8sp : irc_sp m O8)
      by (rewrite /irc_sp /O8 upd_ne; [exact HO7sp | nz]).
    assert (HO8thr : irc_thr8 m O8).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O8 upd_ne; [| regne].
      exact (HO7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x4a) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x4c)) by pcw.
    iEval (rewrite Hpp4c) in "Hpc".
    (* ===== +0x4c jal ra,brelse : the buffer goes back at last ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x4c)) Rra
              (mword_of_int 2095024 : mword 21) O8 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4c").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (O9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x4c) : mword 64) 4)]> O8).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.ireclaim + 0x4c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095024 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HO9a0 : O9 !!! Regidx Ra0 = bnode kk)
      by (rewrite /O9 upd_ne; [exact HO8a0 | nz]).
    assert (HO9ra : O9 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x4c) : mword 64) 4)
      by (rewrite /O9; apply upd_eq).
    assert (HO9s1 : O9 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /O9 upd_ne; [exact HO8s1 | nz]).
    assert (HO9s3 : O9 !!! Regidx Rs3 = ientry kslot)
      by (rewrite /O9 upd_ne; [exact HO8s3 | nz]).
    assert (HO9s4 : O9 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /O9 upd_ne; [exact HO8s4 | nz]).
    assert (HO9s5 : O9 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /O9 upd_ne; [exact HO8s5 | nz]).
    assert (HO9s6 : O9 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /O9 upd_ne; [exact HO8s6 | nz]).
    assert (HO9sp : irc_sp m O9)
      by (rewrite /irc_sp /O9 upd_ne; [exact HO8sp | nz]).
    assert (HO9thr : irc_thr8 m O9).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /O9 upd_ne; [| regne].
      exact (HO8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID8 CID11 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID7) (CIDb := CID11) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev bno dq O9 (K - 8)%nat true (proc_addr j)
              bs bsd0 d0 b lks ltac:(lia) Hkk HO9a0
              (* brelse's bound is "bcache"(4); irc_orphan's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID12 Hq12 mR) "%Hcsr Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpc50 : ret_pc (O9 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0x50))
      by (rewrite HO9ra; pcw).
    iEval (rewrite Hpc50) in "Hpc".
    iDestruct (iu_slots_join bn 2 1 with "Hsl Hsl1") as "Hsl".
    pose proof Hcsr as Hcsr_cs.
    assert (HmRs1 : mR !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HO9s1).
    assert (HmRs3 : mR !!! Regidx Rs3 = ientry kslot)
      by (rewrite (callee_saved_lookup Hcsr_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HO9s3).
    assert (HmRs4 : mR !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HO9s4).
    assert (HmRs5 : mR !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HO9s5).
    assert (HmRs6 : mR !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HO9s6).
    assert (HmRsp : irc_sp m mR).
    { rewrite /irc_sp
        (callee_saved_lookup Hcsr_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HO9sp. }
    assert (HmRthr : irc_thr8 m mR).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsr_cs c Hcs).
      exact (HO9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0x50 beq s3,zero : THE DEAD ARM.  [ientry kslot] is never
       null, and that is iget's POSTCONDITION and not a premise here. ===== *)
    assert (Hnn : eq_vec (rget mR Rs3) (zero_reg : mword 64) = false).
    { rgne. rewrite HmRs3. apply eq_vec_false_iff.
      apply (ientry_ne_zero kslot ltac:(unfold NINODE in *; lia)). }
    iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x50))
              (mword_of_int 30 : mword 13) Rs3 mR (K - 8)%nat b
              ltac:(nz) Hnn with "Hcg Hpc Hi50").
    iIntros (CID13 Hq13) "Hcg Hpc".
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x50) : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0x54)) by pcw.
    iEval (rewrite Hpp54) in "Hpc".
    (* ===== +0x54 jal ra,begin_op ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x54)) Rra
              (mword_of_int 1954 : mword 21) mR (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi54").
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (OA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x54) : mword 64) 4)]> mR).
    assert (Htgtbo : add_vec (mword_of_int (KernelSyms.ireclaim + 0x54) : mword 64)
                       (sign_extend' 64 (mword_of_int 1954 : mword 21))
                     = mword_of_int KernelSyms.begin_op) by pcw.
    iEval (rewrite Htgtbo) in "Hpc".
    assert (HOAra : OA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x54) : mword 64) 4)
      by (rewrite /OA; apply upd_eq).
    assert (HOAs1 : OA !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /OA upd_ne; [exact HmRs1 | nz]).
    assert (HOAs3 : OA !!! Regidx Rs3 = ientry kslot)
      by (rewrite /OA upd_ne; [exact HmRs3 | nz]).
    assert (HOAs4 : OA !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /OA upd_ne; [exact HmRs4 | nz]).
    assert (HOAs5 : OA !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /OA upd_ne; [exact HmRs5 | nz]).
    assert (HOAs6 : OA !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /OA upd_ne; [exact HmRs6 | nz]).
    assert (HOAsp : irc_sp m OA)
      by (rewrite /irc_sp /OA upd_ne; [exact HmRsp | nz]).
    assert (HOAthr : irc_thr8 m OA).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /OA upd_ne; [| regne].
      exact (HmRthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID12 CID14 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID11) (CIDb := CID14) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (BO.wp_begin_op_sconf γs j γl bn γ γfs cov logstart dev pidv dq
              OA (K - 8)%nat true b lks
              ltac:(lia) Hj Hgl
              (* begin_op's bound is "log"(3); irc_orphan's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt [] [] Htext Hpc Hlctx Hppid Hprocs").
    all: try lkbelow.
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CID15 Hq15 mB) "%Hcsbo Hcg Hcnt _ _ Hpc Hppid Hop".
    assert (Hpc58 : ret_pc (OA !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0x58))
      by (rewrite HOAra; pcw).
    iEval (rewrite Hpc58) in "Hpc".
    pose proof Hcsbo as Hcsbo_cs.
    assert (HmBs1 : mB !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsbo_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HOAs1).
    assert (HmBs3 : mB !!! Regidx Rs3 = ientry kslot)
      by (rewrite (callee_saved_lookup Hcsbo_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HOAs3).
    assert (HmBs4 : mB !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcsbo_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HOAs4).
    assert (HmBs5 : mB !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsbo_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HOAs5).
    assert (HmBs6 : mB !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcsbo_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HOAs6).
    assert (HmBsp : irc_sp m mB).
    { rewrite /irc_sp
        (callee_saved_lookup Hcsbo_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HOAsp. }
    assert (HmBthr : irc_thr8 m mB).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsbo_cs c Hcs).
      exact (HOAthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* THE REFERENCE IS CARVED: ilock takes a SHARE, not a reference. *)
    iEval (rewrite inode_ref_shed) in "Href".
    iDestruct "Href" as "[Hkeep Hshr]".
    (* ===== +0x58 c.mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x58)) Ra0 Rs3
              mB (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi58").
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (OB := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Rs3))]> mB).
    assert (HOBa0 : OB !!! Regidx Ra0 = ientry kslot).
    { rewrite /OB upd_eq. rgne. rewrite HmBs3. apply add_vec_zero_l. }
    assert (HOBs1 : OB !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /OB upd_ne; [exact HmBs1 | nz]).
    assert (HOBs3 : OB !!! Regidx Rs3 = ientry kslot)
      by (rewrite /OB upd_ne; [exact HmBs3 | nz]).
    assert (HOBs4 : OB !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /OB upd_ne; [exact HmBs4 | nz]).
    assert (HOBs5 : OB !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /OB upd_ne; [exact HmBs5 | nz]).
    assert (HOBs6 : OB !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /OB upd_ne; [exact HmBs6 | nz]).
    assert (HOBsp : irc_sp m OB)
      by (rewrite /irc_sp /OB upd_ne; [exact HmBsp | nz]).
    assert (HOBthr : irc_thr8 m OB).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /OB upd_ne; [| regne].
      exact (HmBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x5a)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* ===== +0x5a jal ra,ilock ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x5a)) Rra
              (mword_of_int 2096434 : mword 21) OB (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5a").
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (OC := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x5a) : mword 64) 4)]> OB).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.ireclaim + 0x5a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096434 : mword 21))
                     = mword_of_int KernelSyms.ilock) by pcw.
    iEval (rewrite Htgtil) in "Hpc".
    assert (HOCa0 : OC !!! Regidx Ra0 = ientry kslot)
      by (rewrite /OC upd_ne; [exact HOBa0 | nz]).
    assert (HOCra : OC !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x5a) : mword 64) 4)
      by (rewrite /OC; apply upd_eq).
    assert (HOCs1 : OC !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /OC upd_ne; [exact HOBs1 | nz]).
    assert (HOCs3 : OC !!! Regidx Rs3 = ientry kslot)
      by (rewrite /OC upd_ne; [exact HOBs3 | nz]).
    assert (HOCs4 : OC !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /OC upd_ne; [exact HOBs4 | nz]).
    assert (HOCs5 : OC !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /OC upd_ne; [exact HOBs5 | nz]).
    assert (HOCs6 : OC !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /OC upd_ne; [exact HOBs6 | nz]).
    assert (HOCsp : irc_sp m OC)
      by (rewrite /irc_sp /OC upd_ne; [exact HOBsp | nz]).
    assert (HOCthr : irc_thr8 m OC).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /OC upd_ne; [| regne].
      exact (HOBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID15 CID17 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID14) (CIDb := CID17) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iDestruct (iu_slots_split bn 2 1 with "Hsl") as "[Hsl Hsl1]".
    (* SpecIlock v4 names the share's GENERATION (design 17.3 (A)) *)
    iEval (rewrite inode_shr_gen_intro) in "Hshr".
    iDestruct "Hshr" as (gsh) "Hshr".
    iApply (IL.wp_ilock_sconf γs j γl γu γd γk pd pav pu bn γfs γi cn gil gisl
              cov logstart inodestart nib kslot (q/2)%Qp gsh dev inum
              pidv dq dqs OC (K - 8)%nat true b lks
              ltac:(lia) Hkslot Hgeom Hst Hibcov Hnibin Hj Hgl
              HOCa0
              (* ilock's bound is "bcache"(4); irc_orphan's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt [] [] Htext Hkdata Hpc Hpanenv Hbio Hitbl Hescrow Hireg Hslk
                    Hshr Hsbi Hppid Hprocs Hdevi Hdgeom Hdlock Hsl1").
    all: try lkbelow.
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CID18 Hq18 mL dnl bml fl_)
      "%Hcsil Hcg Hcnt _ _ Hpc Hppid Hsbi Hsl1 Hslkd Hslpid Hdep Hidev Hiinum
       Hvalid Hloaded #Hshot %Hfr_".
    assert (Hpc5e : ret_pc (OC !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0x5e))
      by (rewrite HOCra; pcw).
    iEval (rewrite Hpc5e) in "Hpc".
    iDestruct (iu_slots_join bn 2 1 with "Hsl Hsl1") as "Hsl".
    pose proof Hcsil as Hcsil_cs.
    assert (HmLs1 : mL !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsil_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HOCs1).
    assert (HmLs3 : mL !!! Regidx Rs3 = ientry kslot)
      by (rewrite (callee_saved_lookup Hcsil_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HOCs3).
    assert (HmLs4 : mL !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcsil_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HOCs4).
    assert (HmLs5 : mL !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsil_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HOCs5).
    assert (HmLs6 : mL !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcsil_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HOCs6).
    assert (HmLsp : irc_sp m mL).
    { rewrite /irc_sp
        (callee_saved_lookup Hcsil_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HOCsp. }
    assert (HmLthr : irc_thr8 m mL).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsil_cs c Hcs).
      exact (HOCthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0x5e c.mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x5e)) Ra0 Rs3
              mL (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (OD := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mL Rs3))]> mL).
    assert (HODa0 : OD !!! Regidx Ra0 = ientry kslot).
    { rewrite /OD upd_eq. rgne. rewrite HmLs3. apply add_vec_zero_l. }
    assert (HODs1 : OD !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /OD upd_ne; [exact HmLs1 | nz]).
    assert (HODs3 : OD !!! Regidx Rs3 = ientry kslot)
      by (rewrite /OD upd_ne; [exact HmLs3 | nz]).
    assert (HODs4 : OD !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /OD upd_ne; [exact HmLs4 | nz]).
    assert (HODs5 : OD !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /OD upd_ne; [exact HmLs5 | nz]).
    assert (HODs6 : OD !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /OD upd_ne; [exact HmLs6 | nz]).
    assert (HODsp : irc_sp m OD)
      by (rewrite /irc_sp /OD upd_ne; [exact HmLsp | nz]).
    assert (HODthr : irc_thr8 m OD).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /OD upd_ne; [| regne].
      exact (HmLthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x5e) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x60)) by pcw.
    iEval (rewrite Hpp60) in "Hpc".
    (* ===== +0x60 jal ra,iunlock ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x60)) Rra
              (mword_of_int 2096602 : mword 21) OD (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi60").
    iIntros (CID20 Hq20) "Hcg Hpc".
    set (OE := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x60) : mword 64) 4)]> OD).
    assert (Htgtiu : add_vec (mword_of_int (KernelSyms.ireclaim + 0x60) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096602 : mword 21))
                     = mword_of_int KernelSyms.iunlock) by pcw.
    iEval (rewrite Htgtiu) in "Hpc".
    assert (HOEa0 : OE !!! Regidx Ra0 = ientry kslot)
      by (rewrite /OE upd_ne; [exact HODa0 | nz]).
    assert (HOEra : OE !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x60) : mword 64) 4)
      by (rewrite /OE; apply upd_eq).
    assert (HOEs1 : OE !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /OE upd_ne; [exact HODs1 | nz]).
    assert (HOEs3 : OE !!! Regidx Rs3 = ientry kslot)
      by (rewrite /OE upd_ne; [exact HODs3 | nz]).
    assert (HOEs4 : OE !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /OE upd_ne; [exact HODs4 | nz]).
    assert (HOEs5 : OE !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /OE upd_ne; [exact HODs5 | nz]).
    assert (HOEs6 : OE !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /OE upd_ne; [exact HODs6 | nz]).
    assert (HOEsp : irc_sp m OE)
      by (rewrite /irc_sp /OE upd_ne; [exact HODsp | nz]).
    assert (HOEthr : irc_thr8 m OE).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /OE upd_ne; [| regne].
      exact (HODthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID18 CID20 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID17) (CIDb := CID20) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (IU.wp_iunlock_sconf γs γfs γi cn gil gisl cov logstart kslot
              (q/2)%Qp gsh dev inum dnl bml pidv dq OE (K - 8)%nat true
              (proc_addr j) b lks
              ltac:(lia) Hkslot HOEa0
              (* iunlock's bound is "sleep lock"(6); irc_orphan's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hitbl Hescrow Hslk Hslkd Hslpid
                    Hppid Hprocs Hdep Hidev Hiinum Hvalid Hloaded Hshot").
    all: try lkbelow.
    iIntros (CID21 Hq21 mU) "%Hcsiu Hcg Hcnt Hpc Hppid Hshr".
    iDestruct (inode_shr_gen_forget with "Hshr") as "Hshr".
    assert (Hpc64 : ret_pc (OE !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0x64))
      by (rewrite HOEra; pcw).
    iEval (rewrite Hpc64) in "Hpc".
    (* THE GATHER: the share comes back at the fraction it left at *)
    iDestruct (inode_ref_gather kslot (q/2)%Qp (q/2)%Qp dev inum
                 with "Hkeep Hshr") as "Href".
    iEval (rewrite Qp.div_2) in "Href".
    pose proof Hcsiu as Hcsiu_cs.
    assert (HmUs1 : mU !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsiu_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HOEs1).
    assert (HmUs3 : mU !!! Regidx Rs3 = ientry kslot)
      by (rewrite (callee_saved_lookup Hcsiu_cs Rs3 ltac:(vm_compute; reflexivity));
          exact HOEs3).
    assert (HmUs4 : mU !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcsiu_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HOEs4).
    assert (HmUs5 : mU !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsiu_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HOEs5).
    assert (HmUs6 : mU !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcsiu_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HOEs6).
    assert (HmUsp : irc_sp m mU).
    { rewrite /irc_sp
        (callee_saved_lookup Hcsiu_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HOEsp. }
    assert (HmUthr : irc_thr8 m mU).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsiu_cs c Hcs).
      exact (HOEthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0x64 c.mv a0,s3 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x64)) Ra0 Rs3
              mU (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi64").
    iIntros (CID22 Hq22) "Hcg Hpc".
    set (OF := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mU Rs3))]> mU).
    assert (HOFa0 : OF !!! Regidx Ra0 = ientry kslot).
    { rewrite /OF upd_eq. rgne. rewrite HmUs3. apply add_vec_zero_l. }
    assert (HOFs1 : OF !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /OF upd_ne; [exact HmUs1 | nz]).
    assert (HOFs4 : OF !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /OF upd_ne; [exact HmUs4 | nz]).
    assert (HOFs5 : OF !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /OF upd_ne; [exact HmUs5 | nz]).
    assert (HOFs6 : OF !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /OF upd_ne; [exact HmUs6 | nz]).
    assert (HOFsp : irc_sp m OF)
      by (rewrite /irc_sp /OF upd_ne; [exact HmUsp | nz]).
    assert (HOFthr : irc_thr8 m OF).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /OF upd_ne; [| regne].
      exact (HmUthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x64) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x66)) by pcw.
    iEval (rewrite Hpp66) in "Hpc".
    (* ===== +0x66 jal ra,iput : nlink = 0, so this truncates and frees ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x66)) Rra
              (mword_of_int 2096808 : mword 21) OF (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi66").
    iIntros (CID23 Hq23) "Hcg Hpc".
    set (OG := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x66) : mword 64) 4)]> OF).
    assert (Htgtip : add_vec (mword_of_int (KernelSyms.ireclaim + 0x66) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096808 : mword 21))
                     = mword_of_int KernelSyms.iput) by pcw.
    iEval (rewrite Htgtip) in "Hpc".
    assert (HOGa0 : OG !!! Regidx Ra0 = ientry kslot)
      by (rewrite /OG upd_ne; [exact HOFa0 | nz]).
    assert (HOGra : OG !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x66) : mword 64) 4)
      by (rewrite /OG; apply upd_eq).
    assert (HOGs1 : OG !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /OG upd_ne; [exact HOFs1 | nz]).
    assert (HOGs4 : OG !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /OG upd_ne; [exact HOFs4 | nz]).
    assert (HOGs5 : OG !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /OG upd_ne; [exact HOFs5 | nz]).
    assert (HOGs6 : OG !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /OG upd_ne; [exact HOFs6 | nz]).
    assert (HOGsp : irc_sp m OG)
      by (rewrite /irc_sp /OG upd_ne; [exact HOFsp | nz]).
    assert (HOGthr : irc_thr8 m OG).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /OG upd_ne; [| regne].
      exact (HOFthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID21 CID23 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID20) (CIDb := CID23) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (IP.wp_iput_sconf γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl
              gil gisl cov logstart bmapstart inodestart nib size dev usedn
              kslot q inum MAXOPBLOCKS pidv dq dqb dqs OG (K - 8)%nat true b lks
              ltac:(lia) Hkslot Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hst Hibcov Hiblog Hnibin Hcovb
              ltac:(unfold iput_units, MAXOPBLOCKS; lia) Hj Hgl HOGa0
              Hbelow
              with "Hcg Hcnt [] [] Htext Hkdata Hpc Hpanenv Hbio Hlctx Hitb2 Hitbl Hescrow
                    Hireg Hslk Href Hsbb Hsbi Hbm Hppid Hprocs Hdevi Hdgeom
                    Hdlock Hsl Hop").
    all: try lkbelow.
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CID24 Hq24 mQ n' usedp) "%Hcsip Hcg Hcnt _ _ Hpc Hppid Hsbb Hsbi
                                      %Hsubp Hbm Hsl %Hn' Hop Hiref".
    assert (Hpc6a : ret_pc (OG !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0x6a))
      by (rewrite HOGra; pcw).
    iEval (rewrite Hpc6a) in "Hpc".
    pose proof Hcsip as Hcsip_cs.
    assert (HmQs1 : mQ !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsip_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HOGs1).
    assert (HmQs4 : mQ !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcsip_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HOGs4).
    assert (HmQs5 : mQ !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsip_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HOGs5).
    assert (HmQs6 : mQ !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcsip_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HOGs6).
    assert (HmQsp : irc_sp m mQ).
    { rewrite /irc_sp
        (callee_saved_lookup Hcsip_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HOGsp. }
    assert (HmQthr : irc_thr8 m mQ).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsip_cs c Hcs).
      exact (HOGthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0x6a jal ra,end_op : the reservation is retired ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x6a)) Rra
              (mword_of_int 2072 : mword 21) mQ (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6a").
    iIntros (CID25 Hq25) "Hcg Hpc".
    set (OH := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x6a) : mword 64) 4)]> mQ).
    assert (Htgteo : add_vec (mword_of_int (KernelSyms.ireclaim + 0x6a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2072 : mword 21))
                     = mword_of_int KernelSyms.end_op) by pcw.
    iEval (rewrite Htgteo) in "Hpc".
    assert (HOHra : OH !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x6a) : mword 64) 4)
      by (rewrite /OH; apply upd_eq).
    assert (HOHs1 : OH !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /OH upd_ne; [exact HmQs1 | nz]).
    assert (HOHs4 : OH !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /OH upd_ne; [exact HmQs4 | nz]).
    assert (HOHs5 : OH !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /OH upd_ne; [exact HmQs5 | nz]).
    assert (HOHs6 : OH !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /OH upd_ne; [exact HmQs6 | nz]).
    assert (HOHsp : irc_sp m OH)
      by (rewrite /irc_sp /OH upd_ne; [exact HmQsp | nz]).
    assert (HOHthr : irc_thr8 m OH).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /OH upd_ne; [| regne].
      exact (HmQthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID24 CID25 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID23) (CIDb := CID25) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (EO.wp_end_op_sconf γs j γl γu γd γk pd pav pu bn γ γfs cov logstart
              dev n' pidv dq OH (K - 8)%nat true b lks
              ltac:(lia) Hgeom Hj Hgl
              (* end_op's bound is "log"(3); irc_orphan's own is
                 "itable"(2), and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt [] [] Htext Hkdata Hpc Hpanenv Hbio Hlctx Hseam Hgen Hppid
                    Hprocs Hdevi Hdgeom Hdlock Hop").
    all: try lkbelow.
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CID26 Hq26 mE) "%Hcseo Hcg Hcnt _ _ Hpc Hppid".
    assert (Hpc6e : ret_pc (OH !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0x6e))
      by (rewrite HOHra; pcw).
    iEval (rewrite Hpc6e) in "Hpc".
    pose proof Hcseo as Hcseo_cs.
    assert (HmEs1 : mE !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcseo_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HOHs1).
    assert (HmEs4 : mE !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcseo_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HOHs4).
    assert (HmEs5 : mE !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcseo_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HOHs5).
    assert (HmEs6 : mE !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcseo_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HOHs6).
    assert (HmEsp : irc_sp m mE).
    { rewrite /irc_sp
        (callee_saved_lookup Hcseo_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HOHsp. }
    assert (HmEthr : irc_thr8 m mE).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcseo_cs c Hcs).
      exact (HOHthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== FALL into the step at +0x6e ===== *)
    iApply (irc_step (CID0 := CID26) j bn γfs cov logstart bmapstart inodestart
              ninodes size used usedp dev inum fuel pidv dq dqb dqs dqn
              m mE K b lks HK Hn31
              ltac:(transitivity usedn; [exact Hsubp | exact Hsub])
              Hfuel Hinum HmEsp HmEthr
              HmEs1 HmEs4 HmEs5 HmEs6
              with "Hcg Hcnt Htext Hpc Hframe Hppid Hsbn Hsbi Hsbb Hsl Hiref
                    Hbm Hboot [Hloop] [Hcont]").
    { iExact "Hloop". }
    { iApply (wp_next_shift (b := true) (CIDa := CID25) (CIDb := CID26)
                ltac:(wp_next_chain) with "Hcont"). }
  Qed.

End IreclaimOrphan.

(* ===================================================================== *)
(*  +0xaa .. +0xb0 : THE PLAIN ARM.  brelse and jump to the step.         *)
(*  Factored out because the body reaches it from BOTH of its tests -- a  *)
(*  zero type at +0xa2 and a nonzero nlink at +0xa8.                      *)
(* ===================================================================== *)
Section IreclaimRelease.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma irc_release `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat)
      (γd : disk_names)
      (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart inodestart ninodes size : Z)
      (used usedn : gset Z)
      (dev inum bno : mword 32) (kk : nat)
      (bs bsd0 : list (bv 8)) (d0 : bool) (fuel : nat)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac)
      (m Ml : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ireclaim <= K)%nat ->
    ninodes < 2 ^ 31 ->
    (Z.to_nat (ninodes - bv_unsigned inum) <= S fuel)%nat ->
    0 < bv_unsigned inum < ninodes ->
    usedn ⊆ used ->
    (kk < NBUF)%nat ->
    irc_sp m Ml ->
    irc_thr8 m Ml ->
    Ml !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64) ->
    Ml !!! Regidx Rs2 = bnode kk ->
    Ml !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64) ->
    Ml !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64) ->
    Ml !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64) ->
    (* irc_release's only lock-touching callee is brelse, at "bcache" (4). *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 Ml (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.ireclaim + 0xaa) : mword 64) -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    procs_inv γs -∗
    irc_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 2 -∗
    iref_slot -∗
    bitmap_res γfs bmapstart cov logstart size usedn -∗
    ireg_boot -∗
    bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bno bs bsd0 d0 -∗
    irc_loop γfs bn cov logstart bmapstart inodestart ninodes size used dev
             pidv dq dqb dqs dqn j m K b lks fuel -∗
    irc_cont (CID0 := CID0) γfs bn cov logstart bmapstart inodestart ninodes size
             used pidv dq dqb dqs dqn j m K b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hn31 Hfuel Hinum Hsub Hkk Hsp Hthr Hs1 Hs2 Hs4 Hs5 Hs6 Hbelow.
    pose proof HK as HK'. 
    iIntros "Hcg Hcnt #Htext Hpc #Hbio #Hprocs Hframe Hppid Hsbn Hsbi
              Hsbb Hsl Hiref Hbm Hboot Hlk Hloop Hcont".
    iPoseProof (irci_aa with "Htext") as "Hiaa".
    iPoseProof (irci_ac with "Htext") as "Hiac".
    iPoseProof (irci_b0 with "Htext") as "Hib0".
    (* ===== +0xaa c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xaa)) Ra0 Rs2
              Ml (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiaa").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (V1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget Ml Rs2))]> Ml).
    assert (HV1a0 : V1 !!! Regidx Ra0 = bnode kk).
    { rewrite /V1 upd_eq. rgne. rewrite Hs2. apply add_vec_zero_l. }
    assert (HV1s1 : V1 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /V1 upd_ne; [exact Hs1 | nz]).
    assert (HV1s4 : V1 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /V1 upd_ne; [exact Hs4 | nz]).
    assert (HV1s5 : V1 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /V1 upd_ne; [exact Hs5 | nz]).
    assert (HV1s6 : V1 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /V1 upd_ne; [exact Hs6 | nz]).
    assert (HV1sp : irc_sp m V1)
      by (rewrite /irc_sp /V1 upd_ne; [exact Hsp | nz]).
    assert (HV1thr : irc_thr8 m V1).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /V1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hppac : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xaa) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xac)) by pcw.
    iEval (rewrite Hppac) in "Hpc".
    (* ===== +0xac jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xac)) Rra
              (mword_of_int 2094928 : mword 21) V1 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hiac").
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (V2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xac) : mword 64) 4)]> V1).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.ireclaim + 0xac) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094928 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HV2a0 : V2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /V2 upd_ne; [exact HV1a0 | nz]).
    assert (HV2ra : V2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xac) : mword 64) 4)
      by (rewrite /V2; apply upd_eq).
    assert (HV2s1 : V2 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite /V2 upd_ne; [exact HV1s1 | nz]).
    assert (HV2s4 : V2 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /V2 upd_ne; [exact HV1s4 | nz]).
    assert (HV2s5 : V2 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /V2 upd_ne; [exact HV1s5 | nz]).
    assert (HV2s6 : V2 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite /V2 upd_ne; [exact HV1s6 | nz]).
    assert (HV2sp : irc_sp m V2)
      by (rewrite /irc_sp /V2 upd_ne; [exact HV1sp | nz]).
    assert (HV2thr : irc_thr8 m V2).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /V2 upd_ne; [| regne].
      exact (HV1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    iDestruct (cpu_own_transport CID0 CID2 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID2) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev bno dq V2 (K - 8)%nat true (proc_addr j)
              bs bsd0 d0 b lks ltac:(lia) Hkk HV2a0
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID3 Hq3 mR) "%Hcsr Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hppb0 : ret_pc (V2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.ireclaim + 0xb0))
      by (rewrite HV2ra; pcw).
    iEval (rewrite Hppb0) in "Hpc".
    iDestruct (iu_slots_join bn 2 1 with "Hsl Hsl1") as "Hsl".
    pose proof Hcsr as Hcsr_cs.
    assert (HmRs1 : mR !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HV2s1).
    assert (HmRs4 : mR !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs4 ltac:(vm_compute; reflexivity));
          exact HV2s4).
    assert (HmRs5 : mR !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs5 ltac:(vm_compute; reflexivity));
          exact HV2s5).
    assert (HmRs6 : mR !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
      by (rewrite (callee_saved_lookup Hcsr_cs Rs6 ltac:(vm_compute; reflexivity));
          exact HV2s6).
    assert (HmRsp : irc_sp m mR).
    { rewrite /irc_sp
        (callee_saved_lookup Hcsr_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HV2sp. }
    assert (HmRthr : irc_thr8 m mR).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite (callee_saved_lookup Hcsr_cs c Hcs).
      exact (HV2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    (* ===== +0xb0 c.j -66 : back to the step at +0x6e ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xb0))
              (sign_extend' 21 (concat_vec (mword_of_int 2015 : mword 11) ('b"0")))
              mR (K - 8)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hib0").
    iIntros (CID4 Hq4). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjt : add_vec (mword_of_int (KernelSyms.ireclaim + 0xb0) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 2015 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.ireclaim + 0x6e)) by pcw.
    iEval (rewrite Hjt) in "Hpc".
    iDestruct (cpu_own_transport CID3 CID4 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (irc_step (CID0 := CID4) j bn γfs cov logstart bmapstart inodestart
              ninodes size used usedn dev inum fuel pidv dq dqb dqs dqn
              m mR K b lks HK Hn31 Hsub Hfuel Hinum HmRsp HmRthr
              HmRs1 HmRs4 HmRs5 HmRs6
              with "Hcg Hcnt Htext Hpc Hframe Hppid Hsbn Hsbi Hsbb Hsl Hiref
                    Hbm Hboot [Hloop] [Hcont]").
    { iExact "Hloop". }
    { iApply (wp_next_shift (b := true) (CIDa := CID2) (CIDb := CID4)
                ltac:(wp_next_chain) with "Hcont"). }
  Qed.

End IreclaimRelease.

(* ===================================================================== *)
(*  +0x7c .. +0xb0 : THE LOOP BODY, by induction on the fuel.             *)
(*                                                                        *)
(*  [irc_loop] is HART-CLOSED (its own [CIDn] is bound inside it), so the *)
(*  induction needs no [wp_next] wrapper and the re-entry needs no chain  *)
(*  back to the scan's entry hart: every re-entry hands the turn's        *)
(*  resources over at the hart they were produced at.                     *)
(* ===================================================================== *)
Section IreclaimScan.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Local Lemma irc_scan `{GEN : GenId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname) (γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart ninodes size : Z)
      (nib : nat) (used : gset Z) (dev : mword 32)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) :
    (K_ireclaim <= K)%nat ->
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    ireg_blocks_ok inodestart nib cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    cov_below cov size ->
    1 < ninodes ->
    ninodes <= 16 * Z.of_nat nib ->
    ninodes < 2 ^ 31 ->
    printk_gen_contract (kt := KT1) γpr γu γd ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (* irc_scan reaches irc_step (no lock), irc_orphan ("itable", 2) and
       irc_release ("bcache", 4) every turn; "itable" is the lowest. *)
    locks_below lks "log" ->
    kernel_text -∗ kernel_data -∗
    printk_env γpr γu γd -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    ireg_inv γi γfs inodestart nib -∗
    is_itable2 gtl cn γfs γi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn γfs γi cov logstart -∗
    ic_sleeplocks cn -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    ∀ fuel : nat,
      irc_loop γfs bn cov logstart bmapstart inodestart ninodes size used dev
               pidv dq dqb dqs dqn j m K b lks fuel.
  Proof.
    intros HK Hgeom Hst Hblk Hsize Hbm0 Hbmcov Hbmlog Hcovb Hn1 Hnnib Hn31
           Hpk Hj Hgl Hbelow.
    pose proof HK as HK'. 
    pose proof Hgeom as [Hcovok Hlogsub].
    iIntros "#Htext #Hkdata #Hpenv #Hbio #Hlctx #Hseam #Hgen #Hireg
              #Hitb2 #Hitbl #Hesc #Hslks #Hprocs #Hdevi #Hdgeom #Hdlock".
    iPoseProof (printk_env_panic with "Hpenv") as "#Hpanenv".
    iIntros (fuel).
    iInduction fuel as [|fuel] "IH".
    - (* ---- FUEL 0: unreachable, [inum < ninodes] leaves at least one turn ---- *)
      rewrite /irc_loop.
      iIntros (Ml inum usedn CIDn) "%Hfuel %Hinum %Hsub %Hsp %Hthr %Hs1 %Hs4
                                    %Hs5 %Hs6".
      iIntros "Hcg Hcnt Hpc Hframe Hppid Hsbn Hsbi Hsbb Hsl Hiref Hbm Hboot Hcont".
      exfalso. lia.
    - (* ---- FUEL S: one turn of the loop ---- *)
      rewrite /irc_loop.
      iIntros (Ml inum usedn CIDn) "%Hfuel %Hinum %Hsub %Hsp %Hthr %Hs1 %Hs4
                                    %Hs5 %Hs6".
      iIntros "Hcg Hcnt Hpc Hframe Hppid Hsbn Hsbi Hsbb Hsl Hiref Hbm Hboot Hcont".
      pose proof (bv_unsigned_in_range _ inum) as [Hinum0 Hinum32].
      assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
        by (vm_compute; reflexivity).
      rewrite Hm32 in Hinum32.
      assert (Hinum31 : bv_unsigned inum < 2147483648)
        by (change (2^31)%Z with 2147483648%Z in Hn31; lia).
      assert (Hnib : bv_unsigned inum < 16 * Z.of_nat nib) by lia.
      destruct (Hblk inum Hnib) as [Hcov Hlog].
      destruct (Hcovok _ Hcov) as [Hibpos Hiblt].
      assert (Hib : 0 <= IBLOCK inum inodestart < 2147483648)
        by (change (2 ^ 31)%Z with 2147483648%Z in Hiblt; lia).
      set (bno := (mword_of_int (IBLOCK inum inodestart) : mword 32)).
      assert (Hbno : uint bno = IBLOCK inum inodestart).
      { rewrite /bno bb_uint32 moi32_unsigned. apply bvw32_small.
        change (2^32)%Z with 4294967296%Z. lia. }
      assert (Hbnolt : (uint bno < 2147483648)%Z) by (rewrite Hbno; lia).
      assert (Hbnocov : uint bno ∈ bv_cov (fs_view γfs γd dev cov))
        by (rewrite Hbno; exact Hcov).
      assert (Hslotz : Z.of_nat (DinodeEnc.islot inum) = bv_unsigned inum `mod` 16).
      { rewrite /DinodeEnc.islot Z2Nat.id; [reflexivity |].
        pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [Hz _].
        exact Hz. }
      pose proof (DinodeEnc.islot_lt inum) as Hslotlt.
      iPoseProof (irci_7c with "Htext") as "Hi7c".
      iPoseProof (irci_80 with "Htext") as "Hi80".
      iPoseProof (irci_84 with "Htext") as "Hi84".
      iPoseProof (irci_88 with "Htext") as "Hi88".
      iPoseProof (irci_8a with "Htext") as "Hi8a".
      iPoseProof (irci_8c with "Htext") as "Hi8c".
      iPoseProof (irci_90 with "Htext") as "Hi90".
      iPoseProof (irci_92 with "Htext") as "Hi92".
      iPoseProof (irci_96 with "Htext") as "Hi96".
      iPoseProof (irci_9a with "Htext") as "Hi9a".
      iPoseProof (irci_9c with "Htext") as "Hi9c".
      iPoseProof (irci_9e with "Htext") as "Hi9e".
      iPoseProof (irci_a2 with "Htext") as "Hia2".
      iPoseProof (irci_a4 with "Htext") as "Hia4".
      iPoseProof (irci_a8 with "Htext") as "Hia8".
      (* ===== +0x7c addiw s3,s1,0 : s3 := inum, sign-extended ===== *)
      iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x7c)) Rs3 Rs1
                (mword_of_int 0 : mword 12) Ml (K - 8)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7c").
      iIntros (CID1 Hq1) "Hcg Hpc".
      set (W1 := <[Regidx Rs3 := regval_into_reg
                    (sign_extend' 64
                       (subrange_vec_dec
                          (add_vec (rget Ml Rs1)
                             (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> Ml).
      assert (HW1s3 : W1 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64)).
      { rewrite /W1 upd_eq. rgne. rewrite Hs1 iu_off0.
        rewrite (iu_sub31_sext inum). reflexivity. }
      assert (HW1s1 : W1 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W1 upd_ne; [exact Hs1 | nz]).
      assert (HW1s4 : W1 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W1 upd_ne; [exact Hs4 | nz]).
      assert (HW1s5 : W1 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W1 upd_ne; [exact Hs5 | nz]).
      assert (HW1s6 : W1 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W1 upd_ne; [exact Hs6 | nz]).
      assert (HW1sp : irc_sp m W1)
        by (rewrite /irc_sp /W1 upd_ne; [exact Hsp | nz]).
      assert (HW1thr : irc_thr8 m W1).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W1 upd_ne; [| regne].
        exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x7c) : mword 64) 4
                      = mword_of_int (KernelSyms.ireclaim + 0x80)) by pcw.
      iEval (rewrite Hpp80) in "Hpc".
      (* ===== +0x80 srli a1,s1,0x4 : a1 := inum / IPB ===== *)
      iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x80)) Ra1 Rs1
                (mword_of_int 4 : mword 6) W1 (K - 8)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi80").
      iIntros (CID2 Hq2) "Hcg Hpc".
      set (W2 := <[Regidx Ra1 := regval_into_reg
                    (shift_bits_right (rget W1 Rs1)
                       (subrange_vec_dec (mword_of_int 4 : mword 6)
                          (Z.sub log2_xlen 1) 0))]> W1).
      assert (HW2a1 : W2 !!! Regidx Ra1
                      = (mword_of_int (bv_unsigned inum / 16) : mword 64)).
      { rewrite /W2 upd_eq. rgne. rewrite HW1s1. apply ds_srli4. exact Hinum31. }
      assert (HW2s1 : W2 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W2 upd_ne; [exact HW1s1 | nz]).
      assert (HW2s3 : W2 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W2 upd_ne; [exact HW1s3 | nz]).
      assert (HW2s4 : W2 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W2 upd_ne; [exact HW1s4 | nz]).
      assert (HW2s5 : W2 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W2 upd_ne; [exact HW1s5 | nz]).
      assert (HW2s6 : W2 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W2 upd_ne; [exact HW1s6 | nz]).
      assert (HW2sp : irc_sp m W2)
        by (rewrite /irc_sp /W2 upd_ne; [exact HW1sp | nz]).
      assert (HW2thr : irc_thr8 m W2).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W2 upd_ne; [| regne].
        exact (HW1thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x80) : mword 64) 4
                      = mword_of_int (KernelSyms.ireclaim + 0x84)) by pcw.
      iEval (rewrite Hpp84) in "Hpc".
      (* ===== +0x84 lw a5,24(s4) : a5 := sb.inodestart ===== *)
      assert (Hsbiadr : add_vec (rget W2 Rs4)
                          (sign_extend' 64 (mword_of_int 24 : mword 12))
                        = sb_inodestart).
      { rgne. rewrite HW2s4. rewrite /sb_inodestart /pa_add /add_vec_int. pcw. }
      iEval (rewrite -Hsbiadr) in "Hsbi".
      iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ireclaim + 0x84)) Ra5 Rs4
                (mword_of_int 24 : mword 12) W2 (K - 8)%nat
                (mword_of_int inodestart : mword 32) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi84 Hsbi").
      iIntros (CID3 Hq3) "Hcg Hpc Hsbi".
      iEval (rewrite Hsbiadr) in "Hsbi".
      set (W3 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (mword_of_int inodestart : mword 32))]> W2).
      assert (HW3a5 : W3 !!! Regidx Ra5
                      = (sign_extend' 64 (mword_of_int inodestart : mword 32) : mword 64))
        by (rewrite /W3; apply upd_eq).
      assert (HW3a1 : W3 !!! Regidx Ra1
                      = (mword_of_int (bv_unsigned inum / 16) : mword 64))
        by (rewrite /W3 upd_ne; [exact HW2a1 | nz]).
      assert (HW3s1 : W3 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W3 upd_ne; [exact HW2s1 | nz]).
      assert (HW3s3 : W3 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W3 upd_ne; [exact HW2s3 | nz]).
      assert (HW3s4 : W3 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W3 upd_ne; [exact HW2s4 | nz]).
      assert (HW3s5 : W3 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W3 upd_ne; [exact HW2s5 | nz]).
      assert (HW3s6 : W3 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W3 upd_ne; [exact HW2s6 | nz]).
      assert (HW3sp : irc_sp m W3)
        by (rewrite /irc_sp /W3 upd_ne; [exact HW2sp | nz]).
      assert (HW3thr : irc_thr8 m W3).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W3 upd_ne; [| regne].
        exact (HW2thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp88 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x84) : mword 64) 4
                      = mword_of_int (KernelSyms.ireclaim + 0x88)) by pcw.
      iEval (rewrite Hpp88) in "Hpc".
      (* ===== +0x88 c.addw a1,a5 : a1 := IBLOCK(inum, sb) ===== *)
      iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x88)) Ra1 Ra5
                W3 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi88").
      iIntros (CID4 Hq4) "Hcg Hpc".
      set (W4 := <[Regidx Ra1 := regval_into_reg
                    (sign_extend' 64
                       (add_vec (subrange_vec_dec (rget W3 Ra1) 31 0 : mword 32)
                                (subrange_vec_dec (rget W3 Ra5) 31 0 : mword 32)))]> W3).
      assert (HW4a1 : W4 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64)).
      { rewrite /W4 upd_eq. rgne. rgne. rewrite HW3a1 HW3a5.
        rewrite /bno. rewrite ds_add_vec32_comm.
        apply (iu_addw_ibl inum inodestart Hst Hib). }
      assert (HW4s1 : W4 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W4 upd_ne; [exact HW3s1 | nz]).
      assert (HW4s3 : W4 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W4 upd_ne; [exact HW3s3 | nz]).
      assert (HW4s4 : W4 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W4 upd_ne; [exact HW3s4 | nz]).
      assert (HW4s5 : W4 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W4 upd_ne; [exact HW3s5 | nz]).
      assert (HW4s6 : W4 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W4 upd_ne; [exact HW3s6 | nz]).
      assert (HW4sp : irc_sp m W4)
        by (rewrite /irc_sp /W4 upd_ne; [exact HW3sp | nz]).
      assert (HW4thr : irc_thr8 m W4).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W4 upd_ne; [| regne].
        exact (HW3thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp8a : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x88) : mword 64) 2
                      = mword_of_int (KernelSyms.ireclaim + 0x8a)) by pcw.
      iEval (rewrite Hpp8a) in "Hpc".
      (* ===== +0x8a c.mv a0,s5 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x8a)) Ra0 Rs5
                W4 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a").
      iIntros (CID5 Hq5) "Hcg Hpc".
      set (W5 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget W4 Rs5))]> W4).
      assert (HW5a0 : W5 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
      { rewrite /W5 upd_eq. rgne. rewrite HW4s5. apply add_vec_zero_l. }
      assert (HW5a1 : W5 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
        by (rewrite /W5 upd_ne; [exact HW4a1 | nz]).
      assert (HW5s1 : W5 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W5 upd_ne; [exact HW4s1 | nz]).
      assert (HW5s3 : W5 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W5 upd_ne; [exact HW4s3 | nz]).
      assert (HW5s4 : W5 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W5 upd_ne; [exact HW4s4 | nz]).
      assert (HW5s5 : W5 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W5 upd_ne; [exact HW4s5 | nz]).
      assert (HW5s6 : W5 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W5 upd_ne; [exact HW4s6 | nz]).
      assert (HW5sp : irc_sp m W5)
        by (rewrite /irc_sp /W5 upd_ne; [exact HW4sp | nz]).
      assert (HW5thr : irc_thr8 m W5).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W5 upd_ne; [| regne].
        exact (HW4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x8a) : mword 64) 2
                      = mword_of_int (KernelSyms.ireclaim + 0x8c)) by pcw.
      iEval (rewrite Hpp8c) in "Hpc".
      (* ===== +0x8c jal ra,bread ===== *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x8c)) Rra
                (mword_of_int 2094696 : mword 21) W5 (K - 8)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi8c").
      iIntros (CID6 Hq6) "Hcg Hpc".
      set (W6 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x8c) : mword 64) 4)]> W5).
      assert (Htgtbr : add_vec (mword_of_int (KernelSyms.ireclaim + 0x8c) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094696 : mword 21))
                       = mword_of_int KernelSyms.bread) by pcw.
      iEval (rewrite Htgtbr) in "Hpc".
      assert (HW6a0 : W6 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W6 upd_ne; [exact HW5a0 | nz]).
      assert (HW6a1 : W6 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
        by (rewrite /W6 upd_ne; [exact HW5a1 | nz]).
      assert (HW6ra : W6 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x8c) : mword 64) 4)
        by (rewrite /W6; apply upd_eq).
      assert (HW6s1 : W6 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W6 upd_ne; [exact HW5s1 | nz]).
      assert (HW6s3 : W6 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W6 upd_ne; [exact HW5s3 | nz]).
      assert (HW6s4 : W6 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W6 upd_ne; [exact HW5s4 | nz]).
      assert (HW6s5 : W6 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W6 upd_ne; [exact HW5s5 | nz]).
      assert (HW6s6 : W6 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W6 upd_ne; [exact HW5s6 | nz]).
      assert (HW6sp : irc_sp m W6)
        by (rewrite /irc_sp /W6 upd_ne; [exact HW5sp | nz]).
      assert (HW6thr : irc_thr8 m W6).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W6 upd_ne; [| regne].
        exact (HW5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      iDestruct (cpu_own_transport CIDn CID6 0 true (proc_addr j) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (wp_next_shift (b := true) (CIDa := CIDn) (CIDb := CID6) ltac:(wp_next_chain)
                   with "Hcont") as "Hcont".
      iDestruct (iu_slots_split bn 2 1 with "Hsl") as "[Hsl Hsl1]".
      iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
                (fs_view γfs γd dev cov) pidv dev bno dq
                W6 (K - 8)%nat true b lks
                ltac:(lia) Hbnolt eq_refl Hbnocov eq_refl Hj Hgl
                HW6a0 HW6a1
                (* bread's bound is "bcache"(4); irc_scan's own is
                   "itable"(2), and [locks_below_mono] weakens it. *)
                ltac:(lkbelow)
                with "Hcg Hcnt [] [] Htext Hkdata Hpc Hpanenv Hbio Hppid Hprocs
                      Hdevi Hdgeom Hdlock Hsl1").
      all: try lkbelow.
      { rewrite /trap_csrs_ext. done. }
      { rewrite /cpu_claim_ext. done. }
      iIntros (CID7 Hq7 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt _ _ Hpc Hppid Hheld".
      destruct Hfacts as [Hcsb HmBa0].
      assert (Hpc90 : ret_pc (W6 !!! Regidx Rra : mword 64)
                      = mword_of_int (KernelSyms.ireclaim + 0x90))
        by (rewrite HW6ra; pcw).
      iEval (rewrite Hpc90) in "Hpc".
      pose proof Hcsb as Hcsb_cs.
      assert (HmBs1 : mB !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs1 ltac:(vm_compute; reflexivity));
            exact HW6s1).
      assert (HmBs3 : mB !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs3 ltac:(vm_compute; reflexivity));
            exact HW6s3).
      assert (HmBs4 : mB !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs4 ltac:(vm_compute; reflexivity));
            exact HW6s4).
      assert (HmBs5 : mB !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs5 ltac:(vm_compute; reflexivity));
            exact HW6s5).
      assert (HmBs6 : mB !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite (callee_saved_lookup Hcsb_cs Rs6 ltac:(vm_compute; reflexivity));
            exact HW6s6).
      assert (HmBsp : irc_sp m mB).
      { rewrite /irc_sp
          (callee_saved_lookup Hcsb_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HW6sp. }
      assert (HmBthr : irc_thr8 m mB).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite (callee_saved_lookup Hcsb_cs c Hcs).
        exact (HW6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      (* THE DECODE: the bytes bread returned ARE sixteen dinodes. *)
      iEval (rewrite /bio_locked) in "Hheld".
      iDestruct (iu_held_k with "Hheld") as %Hkk.
      iDestruct (ds_held_L with "Hheld") as "[HpL Hheldback0]".
      iApply fupd_wp.
      iEval (rewrite Hbno (ireg_bi_iblock inum inodestart)) in "HpL".
      iMod (ireg_read_blk ⊤ γi γfs inodestart nib (ireg_bi inum) bs0
              ltac:(solve_ndisj) (ireg_bi_lt inum nib Hnib)
              with "Hireg HpL") as "(%Hex & HpL)".
      iModIntro.
      iEval (rewrite -(ireg_bi_iblock inum inodestart) -Hbno) in "HpL".
      iDestruct ("Hheldback0" with "HpL") as "Hheld".
      destruct Hex as (ds & Hdswf & Hbs0).
      subst bs0.
      assert (Hslotal : dislot_align
                (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)).
      { rewrite /dislot_align.
        assert (E0 : (64 * DinodeEnc.islot inum)%nat
                     = (64 * DinodeEnc.islot inum + 0)%nat) by lia.
        split_and!.
        - rewrite E0. apply iu_align; [exact Hkk | exact Hslotlt | lia
                                      | left; reflexivity | reflexivity].
        - rewrite pa_add_add. apply iu_align;
            [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
        - rewrite pa_add_add. apply iu_align;
            [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
        - rewrite pa_add_add. apply iu_align;
            [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
        - rewrite pa_add_add. apply iu_align;
            [exact Hkk | exact Hslotlt | lia | right; reflexivity | reflexivity]. }
      (* ===== +0x90 c.mv s2,a0 : s2 := bp ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x90)) Rs2 Ra0
                mB (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi90").
      iIntros (CID8 Hq8) "Hcg Hpc".
      set (W7 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
      assert (HW7s2 : W7 !!! Regidx Rs2 = bnode kk).
      { rewrite /W7 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
      assert (HW7a0 : W7 !!! Regidx Ra0 = bnode kk)
        by (rewrite /W7 upd_ne; [exact HmBa0 | nz]).
      assert (HW7s1 : W7 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W7 upd_ne; [exact HmBs1 | nz]).
      assert (HW7s3 : W7 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W7 upd_ne; [exact HmBs3 | nz]).
      assert (HW7s4 : W7 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W7 upd_ne; [exact HmBs4 | nz]).
      assert (HW7s5 : W7 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W7 upd_ne; [exact HmBs5 | nz]).
      assert (HW7s6 : W7 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W7 upd_ne; [exact HmBs6 | nz]).
      assert (HW7sp : irc_sp m W7)
        by (rewrite /irc_sp /W7 upd_ne; [exact HmBsp | nz]).
      assert (HW7thr : irc_thr8 m W7).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W7 upd_ne; [| regne].
        exact (HmBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp92 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x90) : mword 64) 2
                      = mword_of_int (KernelSyms.ireclaim + 0x92)) by pcw.
      iEval (rewrite Hpp92) in "Hpc".
      (* ===== +0x92 addi a5,a0,88 : a5 := bp->data ===== *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x92)) Ra5 Ra0
                (mword_of_int 88 : mword 12) W7 (K - 8)%nat b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi92").
      iIntros (CID9 Hq9) "Hcg Hpc".
      set (W8 := <[Regidx Ra5 := regval_into_reg
                    (add_vec (rget W7 Ra0)
                       (sign_extend' 64 (mword_of_int 88 : mword 12)))]> W7).
      assert (HW8a5 : W8 !!! Regidx Ra5 = b_data (bpa kk)).
      { rewrite /W8 upd_eq. rgne. rewrite HW7a0. apply iu_data_addr. }
      assert (HW8s2 : W8 !!! Regidx Rs2 = bnode kk)
        by (rewrite /W8 upd_ne; [exact HW7s2 | nz]).
      assert (HW8s1 : W8 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W8 upd_ne; [exact HW7s1 | nz]).
      assert (HW8s3 : W8 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W8 upd_ne; [exact HW7s3 | nz]).
      assert (HW8s4 : W8 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W8 upd_ne; [exact HW7s4 | nz]).
      assert (HW8s5 : W8 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W8 upd_ne; [exact HW7s5 | nz]).
      assert (HW8s6 : W8 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W8 upd_ne; [exact HW7s6 | nz]).
      assert (HW8sp : irc_sp m W8)
        by (rewrite /irc_sp /W8 upd_ne; [exact HW7sp | nz]).
      assert (HW8thr : irc_thr8 m W8).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W8 upd_ne; [| regne].
        exact (HW7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp96 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x92) : mword 64) 4
                      = mword_of_int (KernelSyms.ireclaim + 0x96)) by pcw.
      iEval (rewrite Hpp96) in "Hpc".
      (* ===== +0x96 andi a4,s3,15 : a4 := inum % IPB ===== *)
      iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x96)) Ra4 Rs3
                (mword_of_int 15 : mword 12)
                (mword_of_int (Z.of_nat (DinodeEnc.islot inum)) : mword 64)
                W8 (K - 8)%nat b ltac:(nz) ltac:(rdok)
                ltac:(rgne; rewrite HW8s3 ds_andi15 iu_sext_mod16 Hslotz; reflexivity)
                with "Hcg Hpc Hi96").
      iIntros (CID10 Hq10) "Hcg Hpc".
      set (W9 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int (Z.of_nat (DinodeEnc.islot inum)) : mword 64)]> W8).
      assert (HW9a4 : W9 !!! Regidx Ra4
                      = (mword_of_int (Z.of_nat (DinodeEnc.islot inum)) : mword 64))
        by (rewrite /W9; apply upd_eq).
      assert (HW9a5 : W9 !!! Regidx Ra5 = b_data (bpa kk))
        by (rewrite /W9 upd_ne; [exact HW8a5 | nz]).
      assert (HW9s2 : W9 !!! Regidx Rs2 = bnode kk)
        by (rewrite /W9 upd_ne; [exact HW8s2 | nz]).
      assert (HW9s1 : W9 !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W9 upd_ne; [exact HW8s1 | nz]).
      assert (HW9s3 : W9 !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /W9 upd_ne; [exact HW8s3 | nz]).
      assert (HW9s4 : W9 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /W9 upd_ne; [exact HW8s4 | nz]).
      assert (HW9s5 : W9 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /W9 upd_ne; [exact HW8s5 | nz]).
      assert (HW9s6 : W9 !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /W9 upd_ne; [exact HW8s6 | nz]).
      assert (HW9sp : irc_sp m W9)
        by (rewrite /irc_sp /W9 upd_ne; [exact HW8sp | nz]).
      assert (HW9thr : irc_thr8 m W9).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /W9 upd_ne; [| regne].
        exact (HW8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp9a : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x96) : mword 64) 4
                      = mword_of_int (KernelSyms.ireclaim + 0x9a)) by pcw.
      iEval (rewrite Hpp9a) in "Hpc".
      (* ===== +0x9a c.slli a4,0x6 ===== *)
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x9a)) (Regidx Ra4) Ra4
                (mword_of_int 6 : mword 6) W9 (K - 8)%nat b
                ltac:(reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9a").
      iIntros (CID11 Hq11) "Hcg Hpc".
      set (WA := <[Regidx Ra4 := regval_into_reg
                    (shift_bits_left (rget W9 Ra4)
                       (subrange_vec_dec (mword_of_int 6 : mword 6)
                          (Z.sub log2_xlen 1) 0))]> W9).
      assert (HWAa4 : WA !!! Regidx Ra4
                      = (mword_of_int (64 * Z.of_nat (DinodeEnc.islot inum)) : mword 64)).
      { rewrite /WA upd_eq. rgne. rewrite HW9a4. apply iu_slli6; lia. }
      assert (HWAa5 : WA !!! Regidx Ra5 = b_data (bpa kk))
        by (rewrite /WA upd_ne; [exact HW9a5 | nz]).
      assert (HWAs2 : WA !!! Regidx Rs2 = bnode kk)
        by (rewrite /WA upd_ne; [exact HW9s2 | nz]).
      assert (HWAs1 : WA !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /WA upd_ne; [exact HW9s1 | nz]).
      assert (HWAs3 : WA !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /WA upd_ne; [exact HW9s3 | nz]).
      assert (HWAs4 : WA !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /WA upd_ne; [exact HW9s4 | nz]).
      assert (HWAs5 : WA !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /WA upd_ne; [exact HW9s5 | nz]).
      assert (HWAs6 : WA !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /WA upd_ne; [exact HW9s6 | nz]).
      assert (HWAsp : irc_sp m WA)
        by (rewrite /irc_sp /WA upd_ne; [exact HW9sp | nz]).
      assert (HWAthr : irc_thr8 m WA).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /WA upd_ne; [| regne].
        exact (HW9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x9a) : mword 64) 2
                      = mword_of_int (KernelSyms.ireclaim + 0x9c)) by pcw.
      iEval (rewrite Hpp9c) in "Hpc".
      (* ===== +0x9c c.add a5,a5,a4 : a5 := dip ===== *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x9c)) Ra5 Ra4
                WA (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9c").
      iIntros (CID12 Hq12) "Hcg Hpc".
      set (WB := <[Regidx Ra5 := regval_into_reg
                    (add_vec (rget WA Ra5) (rget WA Ra4))]> WA).
      assert (HWBa5 : WB !!! Regidx Ra5
                      = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat).
      { rewrite /WB upd_eq. rgne. rgne. rewrite HWAa5 HWAa4. apply iu_slot_addr. }
      assert (HWBs2 : WB !!! Regidx Rs2 = bnode kk)
        by (rewrite /WB upd_ne; [exact HWAs2 | nz]).
      assert (HWBs1 : WB !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /WB upd_ne; [exact HWAs1 | nz]).
      assert (HWBs3 : WB !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /WB upd_ne; [exact HWAs3 | nz]).
      assert (HWBs4 : WB !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /WB upd_ne; [exact HWAs4 | nz]).
      assert (HWBs5 : WB !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /WB upd_ne; [exact HWAs5 | nz]).
      assert (HWBs6 : WB !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /WB upd_ne; [exact HWAs6 | nz]).
      assert (HWBsp : irc_sp m WB)
        by (rewrite /irc_sp /WB upd_ne; [exact HWAsp | nz]).
      assert (HWBthr : irc_thr8 m WB).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /WB upd_ne; [| regne].
        exact (HWAthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hpp9e : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x9c) : mword 64) 2
                      = mword_of_int (KernelSyms.ireclaim + 0x9e)) by pcw.
      iEval (rewrite Hpp9e) in "Hpc".
      (* ===== the slot, borrowed for the two [lh]s ===== *)
      iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
      iDestruct (iu_buf_bytes (bpa kk) bno (mword_of_int 0 : mword 32) ds Hdswf
                   with "Hbuf") as "[Hbb Hbbback]".
      iDestruct (diblk_slot_acc (b_data (bpa kk)) ds (DinodeEnc.islot inum)
                   Hdswf Hslotlt Hslotal with "Hbb") as "[Hdis Hdisback]".
      rewrite /dislot.
      iDestruct "Hdis" as "(Hd0 & Hd2 & Hd4 & Hd6 & Hd8 & Hda)".
      assert (Hins : <[DinodeEnc.islot inum := ds !!! DinodeEnc.islot inum]> ds = ds).
      { apply list_insert_id. apply list_lookup_lookup_total_lt.
        destruct Hdswf as [Hlen _]. rewrite Hlen. exact Hslotlt. }
      (* ===== +0x9e lh a4,0(a5) : a4 := dip->type ===== *)
      assert (Hlh0 : add_vec (rget WB Ra5)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat).
      { rgne. rewrite HWBa5. apply iu_off0. }
      iEval (rewrite -Hlh0) in "Hd0".
      iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ireclaim + 0x9e)) Ra4 Ra5
                (mword_of_int 0 : mword 12) WB (K - 8)%nat
                (di_type (ds !!! DinodeEnc.islot inum) : mword 16) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9e Hd0").
      iIntros (CID13 Hq13) "Hcg Hpc Hd0".
      iEval (rewrite Hlh0) in "Hd0".
      set (WC := <[Regidx Ra4 := regval_into_reg
                    (sign_extend' 64
                       (di_type (ds !!! DinodeEnc.islot inum) : mword 16))]> WB).
      assert (HWCa4 : WC !!! Regidx Ra4
                      = (sign_extend' 64
                           (di_type (ds !!! DinodeEnc.islot inum) : mword 16)
                         : mword 64))
        by (rewrite /WC; apply upd_eq).
      assert (HWCa5 : WC !!! Regidx Ra5
                      = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)
        by (rewrite /WC upd_ne; [exact HWBa5 | nz]).
      assert (HWCs2 : WC !!! Regidx Rs2 = bnode kk)
        by (rewrite /WC upd_ne; [exact HWBs2 | nz]).
      assert (HWCs1 : WC !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
        by (rewrite /WC upd_ne; [exact HWBs1 | nz]).
      assert (HWCs3 : WC !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
        by (rewrite /WC upd_ne; [exact HWBs3 | nz]).
      assert (HWCs4 : WC !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
        by (rewrite /WC upd_ne; [exact HWBs4 | nz]).
      assert (HWCs5 : WC !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
        by (rewrite /WC upd_ne; [exact HWBs5 | nz]).
      assert (HWCs6 : WC !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
        by (rewrite /WC upd_ne; [exact HWBs6 | nz]).
      assert (HWCsp : irc_sp m WC)
        by (rewrite /irc_sp /WC upd_ne; [exact HWBsp | nz]).
      assert (HWCthr : irc_thr8 m WC).
      { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
        rewrite /WC upd_ne; [| regne].
        exact (HWBthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
      assert (Hppa2 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x9e) : mword 64) 4
                      = mword_of_int (KernelSyms.ireclaim + 0xa2)) by pcw.
      iEval (rewrite Hppa2) in "Hpc".
      (* ===== +0xa2 c.beqz a4,+8 : a free slot? ===== *)
      destruct (decide (bv_unsigned (di_type (ds !!! DinodeEnc.islot inum)) = 0))
        as [Ht0|Ht0].
      + (* ---- TYPE 0: nothing to reclaim, straight to the brelse ---- *)
        assert (Hcmp : eq_vec (rget WC Ra4) (zero_reg : mword 64) = true).
        { rgne. rewrite HWCa4. apply ds_type_zero. exact Ht0. }
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xa2))
                  (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                  WC (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia2").
        iApply bi.later_intro. iIntros (CID14 Hq14) "Hcg Hpc".
        assert (Hjt : add_vec (mword_of_int (KernelSyms.ireclaim + 0xa2) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 4 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.ireclaim + 0xaa)) by pcw.
        iEval (rewrite Hjt) in "Hpc".
        (* the slot goes back UNCHANGED and the handle is whole again *)
        iAssert (dislot (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)
                   (ds !!! DinodeEnc.islot inum))
          with "[Hd0 Hd2 Hd4 Hd6 Hd8 Hda]" as "Hdis".
        { rewrite /dislot. iFrame "Hd0 Hd2 Hd4 Hd6 Hd8 Hda". }
        iDestruct ("Hdisback" $! (ds !!! DinodeEnc.islot inum) with "[%] Hdis")
          as "Hbb".
        { exact (ireg_blk_slot ds (DinodeEnc.islot inum) Hdswf Hslotlt). }
        iEval (rewrite Hins) in "Hbb".
        iDestruct ("Hbbback" $! ds with "[%] Hbb") as "Hbuf"; [exact Hdswf |].
        iDestruct ("Hheldback" $! (diblk_bytes ds) with "Hbuf") as "Hheld".
        iAssert (bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bno
                   (diblk_bytes ds) bsd0 d0) with "[Hheld]" as "Hlk";
          [rewrite /bio_locked; iExact "Hheld" |].
        iDestruct (cpu_own_transport CID7 CID14 0 true (proc_addr j) b
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (irc_release (CID0 := CID14) γs j γd bn γfs cov logstart bmapstart
                  inodestart ninodes size used usedn dev inum bno kk
                  (diblk_bytes ds) bsd0 d0 fuel pidv dq dqb dqs dqn
                  m WC K b lks HK Hn31 Hfuel Hinum Hsub Hkk HWCsp HWCthr
                  HWCs1 HWCs2 HWCs4 HWCs5 HWCs6
                  (* irc_release's bound is "bcache"(4); irc_scan's own is
                     "itable"(2), and [locks_below_mono] weakens it. *)
                  ltac:(lkbelow)
                  with "Hcg Hcnt Htext Hpc Hbio Hprocs Hframe Hppid
                        Hsbn Hsbi Hsbb Hsl Hiref Hbm Hboot Hlk [] [Hcont]").
        { iApply "IH". }
        { iApply (wp_next_shift (b := true) (CIDa := CID6) (CIDb := CID14)
                    ltac:(wp_next_chain) with "Hcont"). }
      + (* ---- TYPE nonzero: read the link count ---- *)
        assert (Hcmp : eq_vec (rget WC Ra4) (zero_reg : mword 64) = false).
        { rgne. rewrite HWCa4. apply ds_type_nonzero. exact Ht0. }
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xa2))
                  (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                  WC (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                  with "Hcg Hpc Hia2").
        iIntros (CID14 Hq14) "Hcg Hpc".
        assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xa2) : mword 64) 2
                        = mword_of_int (KernelSyms.ireclaim + 0xa4)) by pcw.
        iEval (rewrite Hppa4) in "Hpc".
        (* ===== +0xa4 lh a5,6(a5) : a5 := dip->nlink ===== *)
        assert (Hlh6 : add_vec (rget WC Ra5)
                         (sign_extend' 64 (mword_of_int 6 : mword 12))
                       = pa_add (pa_add (b_data (bpa kk))
                                   (64 * DinodeEnc.islot inum)%nat) 6).
        { rgne. rewrite HWCa5. apply iu_disp; [lia | lia | reflexivity]. }
        iEval (rewrite -Hlh6) in "Hd6".
        iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ireclaim + 0xa4)) Ra5 Ra5
                  (mword_of_int 6 : mword 12) WC (K - 8)%nat
                  (di_nlink (ds !!! DinodeEnc.islot inum) : mword 16) b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia4 Hd6").
        iIntros (CID15 Hq15) "Hcg Hpc Hd6".
        iEval (rewrite Hlh6) in "Hd6".
        set (WD := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64
                         (di_nlink (ds !!! DinodeEnc.islot inum) : mword 16))]> WC).
        assert (HWDa5 : WD !!! Regidx Ra5
                        = (sign_extend' 64
                             (di_nlink (ds !!! DinodeEnc.islot inum) : mword 16)
                           : mword 64))
          by (rewrite /WD; apply upd_eq).
        assert (HWDs2 : WD !!! Regidx Rs2 = bnode kk)
          by (rewrite /WD upd_ne; [exact HWCs2 | nz]).
        assert (HWDs1 : WD !!! Regidx Rs1 = (sign_extend' 64 inum : mword 64))
          by (rewrite /WD upd_ne; [exact HWCs1 | nz]).
        assert (HWDs3 : WD !!! Regidx Rs3 = (sign_extend' 64 inum : mword 64))
          by (rewrite /WD upd_ne; [exact HWCs3 | nz]).
        assert (HWDs4 : WD !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
          by (rewrite /WD upd_ne; [exact HWCs4 | nz]).
        assert (HWDs5 : WD !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
          by (rewrite /WD upd_ne; [exact HWCs5 | nz]).
        assert (HWDs6 : WD !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64))
          by (rewrite /WD upd_ne; [exact HWCs6 | nz]).
        assert (HWDsp : irc_sp m WD)
          by (rewrite /irc_sp /WD upd_ne; [exact HWCsp | nz]).
        assert (HWDthr : irc_thr8 m WD).
        { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
          rewrite /WD upd_ne; [| regne].
          exact (HWCthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
        (* the slot goes back UNCHANGED and the handle is whole again *)
        iAssert (dislot (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat)
                   (ds !!! DinodeEnc.islot inum))
          with "[Hd0 Hd2 Hd4 Hd6 Hd8 Hda]" as "Hdis".
        { rewrite /dislot. iFrame "Hd0 Hd2 Hd4 Hd6 Hd8 Hda". }
        iDestruct ("Hdisback" $! (ds !!! DinodeEnc.islot inum) with "[%] Hdis")
          as "Hbb".
        { exact (ireg_blk_slot ds (DinodeEnc.islot inum) Hdswf Hslotlt). }
        iEval (rewrite Hins) in "Hbb".
        iDestruct ("Hbbback" $! ds with "[%] Hbb") as "Hbuf"; [exact Hdswf |].
        iDestruct ("Hheldback" $! (diblk_bytes ds) with "Hbuf") as "Hheld".
        iAssert (bio_locked bn (fs_view γfs γd dev cov) kk pidv dev bno
                   (diblk_bytes ds) bsd0 d0) with "[Hheld]" as "Hlk";
          [rewrite /bio_locked; iExact "Hheld" |].
        (* ===== +0xa8 c.beqz a5,-112 : an ORPHAN? ===== *)
        destruct (decide (bv_unsigned (di_nlink (ds !!! DinodeEnc.islot inum)) = 0))
          as [Hl0|Hl0].
        * (* ---- ORPHANED: the six-call block at +0x38 ---- *)
          assert (Hcmp2 : eq_vec (rget WD Ra5) (zero_reg : mword 64) = true).
          { rgne. rewrite HWDa5. apply ds_type_zero. exact Hl0. }
          iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xa8))
                    (mword_of_int 200 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    WD (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp2
                    ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia8").
          iApply bi.later_intro. iIntros (CID16 Hq16) "Hcg Hpc".
          assert (Hjt : add_vec (mword_of_int (KernelSyms.ireclaim + 0xa8) : mword 64)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 200 : mword 8) ('b"0"))))
                        = mword_of_int (KernelSyms.ireclaim + 0x38)) by pcw.
          iEval (rewrite Hjt) in "Hpc".
          iDestruct (cpu_own_transport CID7 CID16 0 true (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (irc_orphan (CID0 := CID16) γs j γl γu γd γk pd pav pu bn γ γfs
                    γi cn gtl γpr cov logstart bmapstart inodestart ninodes size
                    nib used usedn dev inum bno kk (diblk_bytes ds) bsd0 ds d0
                    fuel
                    pidv dq dqb dqs dqn m WD K b lks
                    HK Hgeom Hst Hblk Hsize Hbm0 Hbmcov Hbmlog Hcovb Hnnib Hn31
                    Hpk Hj Hgl Hfuel Hinum Hsub Hkk
                    (* LICENCE (e)'s four premises (§7.1): the block this
                       walk bread, decoded, with the claim-shaped record the
                       [c.beqz] at +0xa2 has just refuted a zero type for. *)
                    eq_refl Hdswf Ht0 Hbno HWDsp HWDthr
                    HWDs1 HWDs2 HWDs3 HWDs4 HWDs5 HWDs6
                    Hbelow
                    with "Hcg Hcnt Htext Hkdata Hpc Hpenv Hbio Hlctx
                          Hseam Hgen Hireg Hitb2 Hitbl Hesc Hslks Hprocs Hdevi
                          Hdgeom Hdlock Hframe Hppid Hsbn Hsbi Hsbb Hsl Hiref
                          Hbm Hboot Hlk [] [Hcont]").
          { iApply "IH". }
          { iApply (wp_next_shift (b := true) (CIDa := CID6) (CIDb := CID16)
                      ltac:(wp_next_chain) with "Hcont"). }
        * (* ---- LINKED: nothing to do, the brelse ---- *)
          assert (Hcmp2 : eq_vec (rget WD Ra5) (zero_reg : mword 64) = false).
          { rgne. rewrite HWDa5. apply ds_type_nonzero. exact Hl0. }
          iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xa8))
                    (mword_of_int 200 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                    WD (K - 8)%nat b ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp2
                    with "Hcg Hpc Hia8").
          iIntros (CID16 Hq16) "Hcg Hpc".
          assert (Hppaa : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xa8) : mword 64) 2
                          = mword_of_int (KernelSyms.ireclaim + 0xaa)) by pcw.
          iEval (rewrite Hppaa) in "Hpc".
          iDestruct (cpu_own_transport CID7 CID16 0 true (proc_addr j) b
                       ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (irc_release (CID0 := CID16) γs j γd bn γfs cov logstart bmapstart
                    inodestart ninodes size used usedn dev inum bno kk
                    (diblk_bytes ds) bsd0 d0 fuel pidv dq dqb dqs dqn
                    m WD K b lks HK Hn31 Hfuel Hinum Hsub Hkk HWDsp HWDthr
                    HWDs1 HWDs2 HWDs4 HWDs5 HWDs6
                    (* irc_release's bound is "bcache"(4); irc_scan's own is
                       "itable"(2), and [locks_below_mono] weakens it. *)
                    ltac:(lkbelow)
                    with "Hcg Hcnt Htext Hpc Hbio Hprocs Hframe Hppid
                          Hsbn Hsbi Hsbb Hsl Hiref Hbm Hboot Hlk [] [Hcont]").
          { iApply "IH". }
          { iApply (wp_next_shift (b := true) (CIDa := CID6) (CIDb := CID16)
                      ltac:(wp_next_chain) with "Hcont"). }
  Qed.

End IreclaimScan.

(* ===================================================================== *)
(*  +0x00 .. +0x36 : THE PROLOGUE, and the contract.                      *)
(*                                                                        *)
(*  The [bgeu a5,a4] at +0x0a is the DEAD arm: it would return through the *)
(*  SECOND [c.jr ra] at +0xc6 with the frame never pushed, and [1 <        *)
(*  ninodes] refutes it -- ialloc's +0x12 arm at a different offset.       *)
(*  The [c.j +70] at +0x36 then enters the loop AT ITS BODY (+0x7c),       *)
(*  skipping the step block, which is why [irc_scan] is stated there.      *)
(* ===================================================================== *)
Section IreclaimMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Lemma wp_ireclaim_sconf `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (ninodes : Z) (nib : nat) (size : Z)
      (used : gset Z)
      (dev : mword 32)
      (pidv : mword 32) (dq dqb dqs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
      wp_ireclaim_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                             cov logstart bmapstart inodestart ninodes nib size
                             used dev pidv dq dqb dqs dqn m K eb b lks.
  Proof.
    cbv beta delta [wp_ireclaim_sconf_body].
    intros pcE pj ret_tgt HK Hgeom Hst Hblk Hsize Hbm0 Hbmcov Hbmlog Hcovb
           Hn1 Hnnib Hn31 Hpk Hj Hgl Ha0 Heb Hbelow.
    subst eb.
    pose proof HK as HK'. 
    assert (Hnsext : (sign_extend' 64 (mword_of_int ninodes : mword 32) : mword 64)
                     = mword_of_int ninodes)
      by (apply sext32_64_small; change (2^31)%Z with 2147483648%Z; lia).
    assert (Hone32 : (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)
                     = mword_of_int 1) by pcw.
    (* THE +0x0a REFUTATION, as a pure fact, before a single instruction *)
    assert (Hgene : zopz0zKzJ_u (mword_of_int 1 : mword 64)
                      (mword_of_int ninodes : mword 64) = false).
    { rewrite (ds_bgeu_moi 1 ninodes
                 ltac:(lia)
                 ltac:(change (2^31)%Z with 2147483648%Z in Hn31; lia)).
      apply not_true_is_false. intro Hc. apply Z.geb_le in Hc. lia. }
    iIntros "Hcg Hcnt #Htext Hpc #Hkdata #Hpenv #Hbio #Hlctx
              #Hseam #Hgen Hsbn Hsbi Hsbb #Hireg Hboot #Hitb2 #Hitbl #Hesc #Hslks
              Hbm Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hsl Hiref Hcont".
    iAssert (irc_cont (CID0 := CID) γfs bn cov logstart bmapstart inodestart
               ninodes size used pidv dq dqb dqs dqn j m K b lks)%I
      with "[Hcont]" as "Hcont"; [rewrite /irc_cont; iExact "Hcont" |].
    iPoseProof (irci_00 with "Htext") as "Hi00".
    iPoseProof (irci_04 with "Htext") as "Hi04".
    iPoseProof (irci_08 with "Htext") as "Hi08".
    iPoseProof (irci_0a with "Htext") as "Hi0a".
    iPoseProof (irci_0e with "Htext") as "Hi0e".
    iPoseProof (irci_10 with "Htext") as "Hi10".
    iPoseProof (irci_12 with "Htext") as "Hi12".
    iPoseProof (irci_14 with "Htext") as "Hi14".
    iPoseProof (irci_16 with "Htext") as "Hi16".
    iPoseProof (irci_18 with "Htext") as "Hi18".
    iPoseProof (irci_1a with "Htext") as "Hi1a".
    iPoseProof (irci_1c with "Htext") as "Hi1c".
    iPoseProof (irci_1e with "Htext") as "Hi1e".
    iPoseProof (irci_20 with "Htext") as "Hi20".
    iPoseProof (irci_22 with "Htext") as "Hi22".
    iPoseProof (irci_24 with "Htext") as "Hi24".
    iPoseProof (irci_26 with "Htext") as "Hi26".
    iPoseProof (irci_2a with "Htext") as "Hi2a".
    iPoseProof (irci_2e with "Htext") as "Hi2e".
    iPoseProof (irci_32 with "Htext") as "Hi32".
    iPoseProof (irci_36 with "Htext") as "Hi36".
    (* ===== +0x00 auipc a4,0x1d ===== *)
    iApply (wp_auipc_s_sconf pcE Ra4
              (mword_of_int 29 : mword 20) m K b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (R1 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (pcE : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> m).
    assert (HR1a4 : R1 !!! Regidx Ra4
                    = add_vec (mword_of_int KernelSyms.ireclaim : mword 64)
                        (auipc_off (mword_of_int 29 : mword 20)))
      by (rewrite /R1; apply upd_eq).
    assert (Hpp04 : add_vec_int (pcE : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0x4)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 lw a4,1192(a4) : a4 := sb.ninodes ===== *)
    assert (Hnadr : add_vec (rget R1 Ra4)
                      (sign_extend' 64 (mword_of_int 1138 : mword 12))
                    = sb_ninodes).
    { rgne. rewrite HR1a4. rewrite /sb_ninodes /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hnadr) in "Hsbn".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.ireclaim + 0x4)) Ra4 Ra4
              (mword_of_int 1138 : mword 12) R1 K
              (mword_of_int ninodes : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi04 Hsbn").
    iIntros (CID2 Hq2) "Hcg Hpc Hsbn".
    iEval (rewrite Hnadr) in "Hsbn".
    set (R2 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (mword_of_int ninodes : mword 32))]> R1).
    assert (HR2a4 : R2 !!! Regidx Ra4 = (mword_of_int ninodes : mword 64))
      by (rewrite /R2 upd_eq; exact Hnsext).
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x4) : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0x8)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x8)) Ra5
              (mword_of_int 1 : mword 6)
              (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)
              R2 K b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi08").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (R3 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)]> R2).
    assert (HR3a5 : R3 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R3; apply upd_eq).
    assert (HR3a4 : R3 !!! Regidx Ra4 = (mword_of_int ninodes : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a4 | nz]).
    assert (HR3a0 : R3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [exact Ha0 | nz]. }
    assert (HR3sp0 : (R3 !!! Regidx csp_rs1 : mword 64)
                     = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR3ra : (R3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR3s0 : (R3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR3s1 : (R3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR3s2 : (R3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR3s3 : (R3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR3s4 : (R3 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR3s5 : (R3 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (HR3s6 : (R3 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64)).
    { rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [reflexivity | nz]. }
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x8) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0xa)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* ===== +0x0a bgeu a5,a4 : THE DEAD ARM ===== *)
    iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xa))
              (mword_of_int 188 : mword 13) Ra4 Ra5 R3 K b
              ltac:(nz) ltac:(nz)
              ltac:(rgne; rgne; rewrite HR3a5 HR3a4 Hone32; exact Hgene)
              with "Hcg Hpc Hi0a").
    iIntros (CID4 Hq4) "Hcg Hpc".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xa) : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0xe)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e c.addi16sp sp,-64 : the 8-slot frame ===== *)
    assert (Hpushm : add_vec (m !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                     = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (KernelSyms.ireclaim + 0xe))
              (mword_of_int 60 : mword 6) R3 K 8 b
              ltac:(lia) ltac:(rewrite HR3sp0; exact Hpushm)
              with "Hcg Hpc Hi0e").
    iIntros (CID5 Hq5) "Hcg Hframe Hpc".
    set (R4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (R3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> R3).
    assert (HR4sp : irc_sp m R4)
      by (rewrite /irc_sp /R4 upd_eq HR3sp0; reflexivity).
    assert (HR4thr : irc_thr8 m R4).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R4 upd_ne; [| regne]. rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (HR4a0 : R4 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4a5 : R4 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3a5 | nz]).
    assert (HR4ra : (R4 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3ra | nz]).
    assert (HR4s0 : (R4 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s0 | nz]).
    assert (HR4s1 : (R4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s1 | nz]).
    assert (HR4s2 : (R4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s2 | nz]).
    assert (HR4s3 : (R4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s3 | nz]).
    assert (HR4s4 : (R4 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s4 | nz]).
    assert (HR4s5 : (R4 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s5 | nz]).
    assert (HR4s6 : (R4 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s6 | nz]).
    iEval (rewrite HR3sp0) in "Hframe".
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & _)".
    iDestruct "T1" as (v1) "Hf1".   iDestruct "T2" as (v2) "Hf2".
    iDestruct "T3" as (v3) "Hf3".   iDestruct "T4" as (v4) "Hf4".
    iDestruct "T5" as (v5) "Hf5".   iDestruct "T6" as (v6) "Hf6".
    iDestruct "T7" as (v7) "Hf7".   iDestruct "T8" as (v8) "Hf8".
    assert (Hb1 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR4sp Hpushm. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR4sp Hpushm. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR4sp Hpushm. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb4 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HR4sp Hpushm. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb5 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HR4sp Hpushm. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb6 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HR4sp Hpushm. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb7 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite HR4sp Hpushm. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb8 : add_vec (R4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite HR4sp Hpushm. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1".   iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3".   iEval (rewrite -Hb4) in "Hf4".
    iEval (rewrite -Hb5) in "Hf5".   iEval (rewrite -Hb6) in "Hf6".
    iEval (rewrite -Hb7) in "Hf7".   iEval (rewrite -Hb8) in "Hf8".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0xe) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 .. +0x1e : the eight saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x10))
              (mword_of_int 7 : mword 6) Rra
              R4 (K - 8)%nat v1 b with "Hcg Hpc Hi10 Hf1").
    iIntros (CID6 Hq6) "Hcg Hpc Hf1".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x12))
              (mword_of_int 6 : mword 6) Rs0
              R4 (K - 8)%nat v2 b with "Hcg Hpc Hi12 Hf2").
    iIntros (CID7 Hq7) "Hcg Hpc Hf2".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x12) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x14))
              (mword_of_int 5 : mword 6) Rs1
              R4 (K - 8)%nat v3 b with "Hcg Hpc Hi14 Hf3").
    iIntros (CID8 Hq8) "Hcg Hpc Hf3".
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x16))
              (mword_of_int 4 : mword 6) Rs2
              R4 (K - 8)%nat v4 b with "Hcg Hpc Hi16 Hf4").
    iIntros (CID9 Hq9) "Hcg Hpc Hf4".
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x16) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x18))
              (mword_of_int 3 : mword 6) Rs3
              R4 (K - 8)%nat v5 b with "Hcg Hpc Hi18 Hf5").
    iIntros (CID10 Hq10) "Hcg Hpc Hf5".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x18) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x1a))
              (mword_of_int 2 : mword 6) Rs4
              R4 (K - 8)%nat v6 b with "Hcg Hpc Hi1a Hf6").
    iIntros (CID11 Hq11) "Hcg Hpc Hf6".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x1c))
              (mword_of_int 1 : mword 6) Rs5
              R4 (K - 8)%nat v7 b with "Hcg Hpc Hi1c Hf7").
    iIntros (CID12 Hq12) "Hcg Hpc Hf7".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x1e)) by pcw.
    iEval (rewrite Hpp1e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x1e))
              (mword_of_int 0 : mword 6) Rs6
              R4 (K - 8)%nat v8 b with "Hcg Hpc Hi1e Hf8").
    iIntros (CID13 Hq13) "Hcg Hpc Hf8".
    iEval (rewrite Hb1; rgne; rewrite HR4ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR4s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR4s1) in "Hf3".
    iEval (rewrite Hb4; rgne; rewrite HR4s2) in "Hf4".
    iEval (rewrite Hb5; rgne; rewrite HR4s3) in "Hf5".
    iEval (rewrite Hb6; rgne; rewrite HR4s4) in "Hf6".
    iEval (rewrite Hb7; rgne; rewrite HR4s5) in "Hf7".
    iEval (rewrite Hb8; rgne; rewrite HR4s6) in "Hf8".
    iAssert (irc_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8]" as "Hframe".
    { rewrite /irc_frame.
      iSplitL "Hf1"; [iExact "Hf1"|]. iSplitL "Hf2"; [iExact "Hf2"|].
      iSplitL "Hf3"; [iExact "Hf3"|]. iSplitL "Hf4"; [iExact "Hf4"|].
      iSplitL "Hf5"; [iExact "Hf5"|]. iSplitL "Hf6"; [iExact "Hf6"|].
      iSplitL "Hf7"; [iExact "Hf7"|]. iExact "Hf8". }
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    (* ===== +0x20 c.addi4spn s0,sp,64 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x20))
              (Cregidx (mword_of_int 0))
              (mword_of_int 16 : mword 8) Rs0 R4 (K - 8)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi20").
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (R5 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R4).
    assert (HR5sp : irc_sp m R5)
      by (rewrite /irc_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5thr : irc_thr8 m R5).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R5 upd_ne; [| regne].
      exact (HR4thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (HR5a0 : R5 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5a5 : R5 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a5 | nz]).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 c.mv s5,a0 : s5 := dev ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x22)) Rs5 Ra0
              R5 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (R6 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R5 Ra0))]> R5).
    assert (HR6s5 : R6 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R6 upd_eq. rgne. rewrite HR5a0. apply add_vec_zero_l. }
    assert (HR6a5 : R6 !!! Regidx Ra5
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5a5 | nz]).
    assert (HR6sp : irc_sp m R6)
      by (rewrite /irc_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6thr : irc_thr8 m R6).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R6 upd_ne; [| regne].
      exact (HR5thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 c.mv s1,a5 : inum := 1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x24)) Rs1 Ra5
              R6 (K - 8)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi24").
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (R7 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R6 Ra5))]> R6).
    assert (HR7s1 : R7 !!! Regidx Rs1
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)).
    { rewrite /R7 upd_eq. rgne. rewrite HR6a5. apply add_vec_zero_l. }
    assert (HR7s5 : R7 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6s5 | nz]).
    assert (HR7sp : irc_sp m R7)
      by (rewrite /irc_sp /R7 upd_ne; [exact HR6sp | nz]).
    assert (HR7thr : irc_thr8 m R7).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R7 upd_ne; [| regne].
      exact (HR6thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.ireclaim + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 auipc s4,0x1d ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x26)) Rs4
              (mword_of_int 29 : mword 20) R7 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi26").
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (R8 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.ireclaim + 0x26) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> R7).
    assert (HR8s4 : R8 !!! Regidx Rs4
                    = add_vec (mword_of_int (KernelSyms.ireclaim + 0x26) : mword 64)
                        (auipc_off (mword_of_int 29 : mword 20)))
      by (rewrite /R8; apply upd_eq).
    assert (HR8s1 : R8 !!! Regidx Rs1
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R8 upd_ne; [exact HR7s1 | nz]).
    assert (HR8s5 : R8 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R8 upd_ne; [exact HR7s5 | nz]).
    assert (HR8sp : irc_sp m R8)
      by (rewrite /irc_sp /R8 upd_ne; [exact HR7sp | nz]).
    assert (HR8thr : irc_thr8 m R8).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R8 upd_ne; [| regne].
      exact (HR7thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x26) : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a addi s4,s4,1142 : s4 := &sb ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x2a)) Rs4 Rs4
              (mword_of_int 1088 : mword 12) R8 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a").
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (R9 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (rget R8 Rs4)
                     (sign_extend' 64 (mword_of_int 1088 : mword 12)))]> R8).
    assert (HR9s4 : R9 !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64)).
    { rewrite /R9 upd_eq. rgne. rewrite HR8s4. pcw. }
    assert (HR9s1 : R9 !!! Regidx Rs1
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8s1 | nz]).
    assert (HR9s5 : R9 !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8s5 | nz]).
    assert (HR9sp : irc_sp m R9)
      by (rewrite /irc_sp /R9 upd_ne; [exact HR8sp | nz]).
    assert (HR9thr : irc_thr8 m R9).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /R9 upd_ne; [| regne].
      exact (HR8thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x2a) : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    (* ===== +0x2e auipc s6,0x4 ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x2e)) Rs6
              (mword_of_int 4 : mword 20) R9 (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2e").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (RA := <[Regidx Rs6 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.ireclaim + 0x2e) : mword 64)
                     (auipc_off (mword_of_int 4 : mword 20)))]> R9).
    assert (HRAs6 : RA !!! Regidx Rs6
                    = add_vec (mword_of_int (KernelSyms.ireclaim + 0x2e) : mword 64)
                        (auipc_off (mword_of_int 4 : mword 20)))
      by (rewrite /RA; apply upd_eq).
    assert (HRAs4 : RA !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /RA upd_ne; [exact HR9s4 | nz]).
    assert (HRAs1 : RA !!! Regidx Rs1
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /RA upd_ne; [exact HR9s1 | nz]).
    assert (HRAs5 : RA !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /RA upd_ne; [exact HR9s5 | nz]).
    assert (HRAsp : irc_sp m RA)
      by (rewrite /irc_sp /RA upd_ne; [exact HR9sp | nz]).
    assert (HRAthr : irc_thr8 m RA).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /RA upd_ne; [| regne].
      exact (HR9thr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x2e) : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0x32)) by pcw.
    iEval (rewrite Hpp32) in "Hpc".
    (* ===== +0x16 addi s6,s6,22 : s6 := the format string ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x32)) Rs6 Rs6
              (mword_of_int 4080 : mword 12) RA (K - 8)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi32").
    iIntros (CID20 Hq20) "Hcg Hpc".
    set (RB := <[Regidx Rs6 := regval_into_reg
                  (add_vec (rget RA Rs6)
                     (sign_extend' 64 (mword_of_int 4080 : mword 12)))]> RA).
    assert (HRBs6 : RB !!! Regidx Rs6 = (mword_of_int irc_msg_addr : mword 64)).
    { rewrite /RB upd_eq. rgne. rewrite HRAs6. unfold irc_msg_addr. pcw. }
    assert (HRBs4 : RB !!! Regidx Rs4 = (mword_of_int KernelSyms.sb : mword 64))
      by (rewrite /RB upd_ne; [exact HRAs4 | nz]).
    assert (HRBs1 : RB !!! Regidx Rs1
                    = (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64))
      by (rewrite /RB upd_ne; [exact HRAs1 | nz]).
    assert (HRBs5 : RB !!! Regidx Rs5 = (sign_extend' 64 dev : mword 64))
      by (rewrite /RB upd_ne; [exact HRAs5 | nz]).
    assert (HRBsp : irc_sp m RB)
      by (rewrite /irc_sp /RB upd_ne; [exact HRAsp | nz]).
    assert (HRBthr : irc_thr8 m RB).
    { intros c Hcs N2 N8 N9 N18 N19 N20 N21 N22.
      rewrite /RB upd_ne; [| regne].
      exact (HRAthr c Hcs N2 N8 N9 N18 N19 N20 N21 N22). }
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.ireclaim + 0x32) : mword 64) 4
                    = mword_of_int (KernelSyms.ireclaim + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    (* ===== +0x36 c.j +70 : INTO THE MIDDLE OF THE LOOP, at +0x7c ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.ireclaim + 0x36))
              (sign_extend' 21 (concat_vec (mword_of_int 35 : mword 11) ('b"0")))
              RB (K - 8)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi36").
    iIntros (CID21 Hq21). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjt : add_vec (mword_of_int (KernelSyms.ireclaim + 0x36) : mword 64)
                    (sign_extend' 64
                       (sign_extend' 21 (concat_vec (mword_of_int 35 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.ireclaim + 0x7c)) by pcw.
    iEval (rewrite Hjt) in "Hpc".
    iDestruct (cpu_own_transport CID CID21 0 true (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID21) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (Hunit1 : bv_unsigned (mword_of_int 1 : mword 32) = 1).
    { rewrite moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    iPoseProof (irc_scan γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                  cov logstart bmapstart inodestart ninodes size nib used dev
                  pidv dq dqb dqs dqn m K b lks
                  HK Hgeom Hst Hblk Hsize Hbm0 Hbmcov Hbmlog Hcovb Hn1 Hnnib
                  Hn31 Hpk Hj Hgl Hbelow
                  with "Htext Hkdata Hpenv Hbio Hlctx Hseam Hgen Hireg
                        Hitb2 Hitbl Hesc Hslks Hprocs Hdevi Hdgeom Hdlock")
      as "Hscan".
    iSpecialize ("Hscan" $! (Z.to_nat (ninodes - 1))).
    rewrite /irc_loop.
    iApply ("Hscan" $! RB (mword_of_int 1 : mword 32) used CID21
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcnt Hpc Hframe
                    Hppid Hsbn Hsbi Hsbb Hsl Hiref Hbm Hboot Hcont").
    { rewrite Hunit1. lia. }
    { rewrite Hunit1. lia. }
    { reflexivity. }
    { exact HRBsp. }
    { exact HRBthr. }
    { exact HRBs1. }
    { exact HRBs4. }
    { exact HRBs5. }
    { exact HRBs6. }
  Qed.

End IreclaimMain.

End IreclaimProof.
