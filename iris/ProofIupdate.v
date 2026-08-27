(* ProofIupdate.v -- iupdate over the SIE-agnostic sconf world.

     void iupdate(struct inode *ip) {
       struct buf *bp;  struct dinode *dip;
       bp = bread(ip->dev, IBLOCK(ip->inum, sb));
       dip = (struct dinode * )bp->data + ip->inum % IPB;
       dip->type = ip->type;   dip->major = ip->major;
       dip->minor = ip->minor; dip->nlink = ip->nlink;
       dip->size  = ip->size;
       memmove(dip->addrs, ip->addrs, sizeof(ip->addrs));
       log_write(bp);
       brelse(bp);
     }

   COMPLETELY STRAIGHT-LINE: 44 instructions, no branch, no arm, no panic of
   its own.  Two lemmas, entered left to right, cut at the memmove return so
   the file's two Qeds stay small:

     [iu_tail]           +0x66 .. +0x7c   log_write, brelse, pop, ret, and
                                          the contract.
     [wp_iupdate_sconf]  +0x00 .. +0x62   prologue, bread, the five field
                                          stores, the memmove.

   THE COUPLING THAT MAKES IT WORK is [InodeRegion.ireg_read]: the block's
   client half lives in the inode REGION, never in the caller's hands
   (design §11.3/§12), so the sixteen-dinode list [ds] is learned HERE --
   one mask-preserving opening of [ireg_inv] against the machinery half
   riding in the handle's own payload, which pins the buffer's bytes to
   [diblk_bytes ds] for some well-formed [ds].  So the sixteen dinodes the
   pure model names ARE the bytes the stores land in, and [ds] never
   appears in the contract.  From there [diblk_slot_acc] hands out slot
   [inum mod IPB] as six typed pieces
   (four halfword cells, one word cell, a 52-byte window) and takes them
   back at the NEW dinode, which is the entire content of what iupdate does
   to the buffer.

   THE FIVE SCALARS AND THE THIRTEEN ADDRS come from different resources --
   [inode_meta ip dn] and [inode_map fsc_fs ip bm] -- and the contract's
   premise [di_addrs dn = bm_cells bm] is what ties them.  memmove's source
   is those thirteen cells viewed as 52 contiguous bytes
   ([InodeInv.inode_addrs_buf]); its non-overlap with the destination is
   carried by SEPARATION, since the inode and the buffer are separate
   conjuncts. *)
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
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeHalf.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import BioFs.  (* [bio_held_fs_L] *)
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import CodeIupdate.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import SpecBread SpecBrelse SpecLogWrite SpecMemmove.
Require Import DinodeSlot.
Require Import SpecIupdate.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

Module IupdateProof (BR : BREAD) (MM : MEMMOVE) (LW : LOG_WRITE) (BL : BRELSE)
  : IUPDATE.


Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac iuidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  Vocabulary: the frame, the register-threading invariants, the         *)
(*  continuation.                                                         *)
(* ===================================================================== *)
Section IupdateDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, ICFG : icfg, FSC : fscfg}.

  (* iupdate's 32-byte frame: ra@24 s0@16 s1@8 s2@0 *)
  Definition iu_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] (m !!! Regidx Rs2 : mword 64))%I.

  (* WHAT A FLUSH HANDS BACK, AS A PARAMETER (design §20.18, stage C2).
     Every contract below is the SAME 44-instruction walk; what differs is
     which region lemma fills log_write's ghost step and therefore what the
     step pays out.  Four landed contracts take
     [InodeRegion.ireg_out γi inum dn] -- the retagged fragment, or the
     marker at a type-0 flush -- and the fifth takes
     [dinode_at γi inum dn] beside the [FsStateLink.link_tok] the flushed
     [ip->nlink++] buys.  So [Pout] is a parameter
     of the continuation and the ghost step is a PREMISE, rather than the
     walk being cloned once per payout. *)

  (* the ghost step itself, at the sixteen-dinode list the walk learned at
     its own bread: exactly [SpecLogWrite.wp_log_write_au]'s premise, with
     the payout abstracted. *)
  (* RECORD-GRANULAR SINCE durable-disk 2b-inode-1: what the step
     surrenders is the flushed inode's OWN 64-byte run at [64 * islot inum]
     of its block, not the whole block -- literally
     [SpecLogWrite.wp_log_write_au_range_body]'s atomic-update premise at
     [off := 64 * islot inum], [len := 64], [sub_new := dinode_bytes dn].
     [ds] stays the index because the walk has it (it decoded the buffer at
     its own bread) and because [bsl := diblk_bytes ds] is what the log's
     tie compares against. *)
  Definition iu_region_au (γ : log_names) (inodestart : Z)
      (inum : mword 32) (dn : dinode) (ds : list dinode) (e0 : nat)
      (Pout : iProp Σ) : iProp Σ :=
    (|={⊤, ⊤ ∖ ↑iregN}=> ∃ (sub_old : list (bv 8)) (v : nat),
       ⌜length sub_old = 64%nat⌝ ∗
       FsBlocks.byte_range (fs_bytes fsc_fs) (IBLOCK inum inodestart)
         (Z.of_nat (64 * islot inum)) sub_old ∗ log_epoch_lb γ v ∗
       (⌜length (diblk_bytes ds) = BSIZE /\
         length (dinode_bytes dn) = 64%nat /\
         sub_old = take 64%nat
                     (drop (64 * islot inum)%nat (diblk_bytes ds))⌝ -∗
        logged_at γ e0 (IBLOCK inum inodestart) -∗ ⌜(v <= e0)%nat⌝ -∗
        FsBlocks.byte_range (fs_bytes fsc_fs) (IBLOCK inum inodestart)
          (Z.of_nat (64 * islot inum)) (dinode_bytes dn)
        ={⊤ ∖ ↑iregN, ⊤}=∗ Pout))%I.

  (* ...and the form a SEAL supplies, which cannot name [ds]: the list is
     proof-internal (the walk learns it at [InodeRegion.ireg_read], out of
     the region's own coupling), so the premise quantifies over it and takes
     the caller's [dinode_at] on the way in. *)
  Definition iu_region_step (γ : log_names) (γi : gname)
      (inodestart : Z) (inum : mword 32) (dn dn0 : dinode) (e0 : nat)
      (Pout : iProp Σ) : iProp Σ :=
    (∀ (ds : list dinode),
       ⌜diblk_wf ds⌝ -∗ dinode_at γi inum dn0 -∗
       iu_region_au γ inodestart inum dn ds e0 Pout)%I.

  (* the record being flushed is a legal dinode -- one line, needed by both
     builders below and by nothing else *)
  Lemma iu_dinode_wf (dn : dinode) (bm : blkmap) :
    di_addrs dn = bm_cells bm -> length (bm_dir bm) = NDIRECT -> dinode_wf dn.
  Proof.
    intros Hda Hdirlen.
    rewrite /dinode_wf Hda /bm_cells length_app Hdirlen. reflexivity.
  Qed.

  (* THE ORDINARY STEP.  It used to be TWO-ARMED -- a type-0 flush was
     iput's free path, ABSORBING the fragment and paying out the marker --
     and the payout [InodeRegion.ireg_out] is still written that way (§16.4)
     so that no landed caller's continuation moves a character.  But the
     free arm is now DEAD here (iclaim-ledger.md §3.1, RULING A): since
     [EscrowDeposit.ireg_free_deposit_au] retires the freeze in the same step it takes
     an [ifreeze_post] token, which no generic caller of iupdate holds, and
     the only type-0 write left in the reordered kernel goes through the
     off-lock DEPOSIT.  So the contract narrows to [di_type dn <> 0], the
     [case_decide]'s zero arm is refuted by that premise, and what is left
     is the single [ireg_write_au] this step always really was. *)
  Lemma iu_step_out (γ : log_names) (γi : gname)
      (inodestart : Z) (nib : nat)
      (inum : mword 32) (dn dn0 : dinode) (e0 : nat) :
    bv_unsigned inum < 16 * Z.of_nat nib ->
    dinode_wf dn ->
    di_type_stable dn dn0 ->
    di_nlink_stable dn dn0 ->
    bv_unsigned (di_type dn) <> 0 ->
    ireg_inv γi fsc_fs inodestart nib -∗
    iu_region_step γ γi inodestart inum dn dn0 e0 (ireg_out γi inum dn).
  Proof.
    intros Hnib Hdnwf Hstab Hnlk Hnzty.
    iIntros "#Hireg" (ds) "%Hdswf Hdn".
    (* the ordinary flush owes no receipt ([InodeRegion.ireg_ep_mono]
       carries it for free), so its anchor is the unit: one adapter line
       and both region lemmas below are unchanged. *)
    rewrite /iu_region_au. iApply lw_au_rec.
    rewrite /ireg_out. case_decide as Hty.
    - exfalso. exact (Hnzty Hty).
    - iApply (ireg_write_au ⊤ γi fsc_fs inodestart nib inum dn0 dn
                (diblk_bytes ds)
                ltac:(solve_ndisj) Hnib Hdnwf Hty Hstab Hnlk
                with "Hireg Hdn").
  Qed.

  (* THE LINK-MINTING STEP (design §20.6's mkdir/sys_link rows, §20.18's
     C2): the SAME ghost step with [InodeRegion.ireg_write_link] in place of
     [ireg_write_au] -- its fupd is byte-for-byte the ordinary one's -- so
     the difference between the two contracts is this one lemma name and
     the payout it hands back.  The type premise is forced: (L3) makes a
     type-0 record's [nlink] zero, and the increment below makes the
     flushed one's at least one. *)
  Lemma iu_step_link (γ : log_names) (γi : gname)
      (inodestart : Z) (nib : nat)
      (inum : mword 32) (dn dn0 : dinode) (e0 : nat)
      (pin : bool) (oty : option ity) :
    bv_unsigned inum < 16 * Z.of_nat nib ->
    dinode_wf dn ->
    bv_unsigned (di_type dn) <> 0 ->
    di_type_stable dn dn0 ->
    (* THE INCREMENT AT THE MACHINE'S WIDTH, plus the kernel's own guard --
       [InodeRegion.ireg_write_link]'s reshaped premises, relayed verbatim.
       The Z-level equation this used to take is derived inside the region,
       under (L4), because that is the only place it is available at all
       (fs-sysfile.md's twelfth stop). *)
    di_nlink dn = add_vec (di_nlink dn0 : mword 16) (mword_of_int 1) ->
    di_nlink dn0 <> (mword_of_int 32767 : mword 16) ->
    (* ...and the FILL's, relayed the same way ([InodeRegion.ireg_lnk_fill]):
       a caller may CHOOSE the register's value only where it is empty. *)
    (forall v : ity, oty = Some v ->
       ireg_mult dn0 = 0%nat
       /\ ireg_reg_ok (bv_unsigned (di_type dn)) v) ->
    ireg_inv γi fsc_fs inodestart nib -∗
    (* THE FREEZE-PIN PREMISE, RULING A-prime's two-armed form
       (iclaim-ledger.md §3.9), relayed straight to the mover: either the
       raised record is ALREADY named, or the caller presents the inum's
       freeze token.  Borrowed and returned -- it comes back inside the
       anchor below, which is why the anchor grew a third conjunct. *)
    ireg_link_pin pin (bv_unsigned inum) dn0 -∗
    iu_region_step γ γi inodestart inum dn dn0 e0
      (dinode_at γi inum dn ∗
       (∃ v : ity,
          ⌜ireg_reg_ok (bv_unsigned (di_type dn)) v
           /\ (forall w, oty = Some w -> v = w)⌝
          ∗ FsStateLink.link_toks (FsBytesGamma.fs_gamma_L fsc_fs)
              (bv_unsigned inum)
              (FsStateLink.link_reps
                 (ireg_dot_delta (bv_unsigned (di_type dn0))
                    (bv_unsigned (di_nlink dn0))) v)) ∗
       ireg_link_pin pin (bv_unsigned inum) dn0).
  Proof.
    intros Hnib Hdnwf Hnz Hstab Hbump Hgrd Hup.
    iIntros "#Hireg Hpin" (ds) "%Hdswf Hdn".
    (* nlink RISES here, so the receipt is vacuous at the written record
       and the anchor is the unit -- the same one adapter line the ordinary
       step takes. *)
    rewrite /iu_region_au. iApply lw_au_rec.
    iApply (ireg_write_link_reg ⊤ γi fsc_fs inodestart nib inum dn0 dn
              (diblk_bytes ds) pin oty
              ltac:(solve_ndisj) Hnib Hdnwf Hnz Hstab Hbump Hgrd Hup
              with "Hireg Hdn Hpin").
  Qed.

  (* THE UNLINK STEP (design fs-icache.md §20.18, stage C4; fs-log.md
     §G.17).  [InodeRegion.ireg_write_unlink] is the one region writer that
     LOWERS nlink, hence the only one that can park a fresh zero, hence the
     only one that owes [InodeRegion.izrcpt] at the record it writes.  Its
     fupd is already the atomic update's new shape -- it surrenders the
     inum's observation counter [v] with its epoch bound and takes the
     receipt back -- so this step is a pure translation of the two wand
     inputs into that receipt, along one of TWO routes:

     - THE WITNESS ROUTE (the zero case, [ip->nlink = 0]): [logged_at γ e0
       (IBLOCK inum inodestart)] with [⌜v <= e0⌝] IS [izrcpt]'s right
       disjunct, once the two ambient ties identify the region's own log
       and first inode block with the threaded ones.  Nothing else can
       produce it: outside log_write's ghost step the two lower bounds are
       incomparable (§G.14).
     - THE VACUOUS ROUTE ([⌜nlink dn <> 0⌝], the parent-decrement case):
       [izrcpt]'s antecedent is false at the written record, so the receipt
       is free -- and then the anchor is the unit, at the caller's OWN [γ],
       which is why this arm needs neither tie. *)
  Lemma iu_step_unlink (γ : log_names) (γi : gname)
      (inodestart : Z) (nib : nat)
      (inum : mword 32) (dn dn0 : dinode) (e0 : nat)
      (uty : ity) :
    bv_unsigned inum < 16 * Z.of_nat nib ->
    dinode_wf dn ->
    bv_unsigned (di_type dn) <> 0 ->
    di_type_stable dn dn0 ->
    bv_unsigned (di_nlink dn0) = bv_unsigned (di_nlink dn) + 1 ->
    ireg_inv γi fsc_fs inodestart nib -∗
    (* THE COUNTING RA's UNIT, COMING BACK (durable-disk 2b-inode-5): the
       token the directory entry whose removal this decrement pays for
       gave up out of its own [FsStateInode.ent_toks]. *)
    FsStateLink.link_toks (FsBytesGamma.fs_gamma_L fsc_fs) (bv_unsigned inum)
      (FsStateLink.link_reps
         (ireg_dot_delta (bv_unsigned (di_type dn))
            (bv_unsigned (di_nlink dn))) uty) -∗
    (⌜γ = icfg_log⌝ ∗ ⌜inodestart = icfg_ist⌝
     ∨ ⌜bv_unsigned (di_nlink dn) <> 0⌝) -∗
    iu_region_step γ γi inodestart inum dn dn0 e0
      (dinode_at γi inum dn).
  Proof.
    intros Hnib Hdnwf Hnz Hstab Hnl.
    iIntros "#Hireg Htok Hrc" (ds) "%Hdswf Hdn".
    rewrite /iu_region_au.
    iMod (ireg_write_unlink_reg ⊤ γi fsc_fs inodestart nib inum dn0 dn
            (diblk_bytes ds) uty
            ltac:(solve_ndisj) Hnib Hdnwf Hnz Hstab Hnl
            with "Hireg Hdn Htok")
      as (rec_old v) "(%Hlr & Hrun & #Hvlb & Hcl)".
    iEval (rewrite FsBytesGamma.gamma_byte_range) in "Hrun".
    iDestruct "Hrc" as "[[%Hlg %Hist] | %Hnzd]".
    - (* THE WITNESS ROUTE *)
      subst γ inodestart.
      iModIntro. iExists rec_old, v.
      iSplitR; [iPureIntro; exact Hlr |]. iFrame "Hrun Hvlb".
      iIntros "(%Hlbsl & %Hlrec & %Hslice) #Hwit %Hle Hrun".
      iEval (rewrite -FsBytesGamma.gamma_byte_range) in "Hrun".
      iMod ("Hcl" with "[] [] Hrun") as "Hout".
      { iPureIntro. exact Hslice. }
      { rewrite /izrcpt iblk_of_IBLOCK. iIntros (_).
        iRight. iExists e0. iFrame "Hwit". iPureIntro. exact Hle. }
      iModIntro. iExact "Hout".
    - (* THE VACUOUS ROUTE *)
      iMod (log_epoch_lb_0 γ) as "#Hlb0".
      iModIntro. iExists rec_old, 0%nat.
      iSplitR; [iPureIntro; exact Hlr |]. iFrame "Hrun Hlb0".
      iIntros "(%Hlbsl & %Hlrec & %Hslice) _ _ Hrun".
      iEval (rewrite -FsBytesGamma.gamma_byte_range) in "Hrun".
      iMod ("Hcl" with "[] [] Hrun") as "Hout".
      { iPureIntro. exact Hslice. }
      { rewrite /izrcpt. iIntros (H0). exfalso. exact (Hnzd H0). }
      iModIntro. iExact "Hout".
  Qed.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition iu_cont `{GEN : GenId} `{CID0 : CpuId}
      (bn : bio_names) (γ : log_names)
      (inodestart : Z) (ip : mword 64) (inum : mword 32)
      (dn : dinode) (bm : blkmap) (u : nat) (Sbo : gset Z) (v : nat)
      (Pout : iProp Σ)
      (dev : mword 32) (pidv : mword 32) (dq dqd dqn dqs : dfrac) (j : nat)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv_bare (proc_addr j) pidv Vpr -∗
        i_dev ip ↦₄{dqd} dev -∗
        i_inum ip ↦₄{dqn} inum -∗
        inode_meta ip dn -∗
        inode_map fsc_fs ip bm -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        (* the flush's payout, a PARAMETER since §20.18's C2 -- see the
           banner above [iu_region_au] *)
        Pout -∗
        bslots 2 -∗
        (* SET FORM throughout the interior: the OUT set is a parameter, so
           the counted seal instantiates it at the caller's own witness
           unioned with the inode block, and forgets it again on the way
           out.  See SpecIupdate's set-form banner.

           EPOCH-CLOSED ON THE WAY OUT (fs-log.md §G.4).  The credit is an
           ENTRY-side premise: a credit is only sound against the epoch of
           the op presenting it, so the entry goes IN with its birth epoch
           named -- but log_write's own post re-closes the existential
           ([LogInv.log_opSw]), the credit is spent by then, and nothing
           downstream of the flush compares epochs.  So the contract is
           asymmetric on purpose: [log_opSe] in, [log_opS] out. *)
        log_opS γ u Sbo -∗
        (* THE DEPOSIT'S OUT-HALF (fs-log.md §G.17).  iupdate is
           straight-line and always log_writes, so the witness is
           unconditional; [⌜v <= e⌝] was cashed inside [log_write] against
           the [ln_ep] auth, which is the one place in the system that can
           order the caller's anchor against a batch's epoch. *)
        (∃ e : nat, logged_at γ e (IBLOCK inum inodestart) ∗ ⌜(v <= e)%nat⌝) -∗
        WP (Loop : expr riscv_lang))%I.

  
End IupdateDefs.

(* the register-threading invariant: the four registers the frame saves *)
Definition iu_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition iu_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))).

(* ===================================================================== *)
(*  +0x66 .. +0x7c : log_write, brelse, and the epilogue.                 *)
(* ===================================================================== *)
Section IupdateTail.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, ICFG : icfg, FSC : fscfg}.

  Local Lemma iu_tail `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat)
      (γd : disk_names) (bn : bio_names)
      (γ : log_names)
      (cov : gset Z) (logstart : Z) (inodestart : Z)
      (dev : mword 32)
      (ip : mword 64) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (ds : list dinode) (u : nat) (Sb : gset Z) (cru : bool) (e0 v : nat)
      (kk : nat) (bno : mword 32) (bsd : list (bv 8)) (d0 : bool)
      (Pout : iProp Σ)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_iupdate <= K)%nat ->
    iu_sp m M ->
    iu_thr m M ->
    M !!! Regidx Rs2 = bnode kk ->
    (kk < NBUF)%nat ->
    (* the two encoding facts the RECORD-granular [log_write] needs
       (durable-disk 2b-inode-1); both are the walk's own, established at
       its bread and by [iu_dinode_wf]. *)
    diblk_wf ds ->
    dinode_wf dn ->
    uint bno = IBLOCK inum inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    (* iu_tail reaches log_write ("log", 3) and brelse ("bcache", 4); log is
       the lower of the two, so one premise at its rank covers both via
       [locks_below_mono]. *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (K - 4)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    (* THE COMPLEMENT, PURE PASS-THROUGH: log_write and brelse are not in the
       ALREADY-GENERALIZED set, so neither touches it -- it rides untouched
       from here to the final [Hcont] specialization (one wide transport,
       not three narrow ones, per claude-notes/completed/eb-generic-sweep.md). *)
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.iupdate + 0x66) : mword 64) -∗
    bio_ctx bn (fs_view fsc_fs γd dev cov) -∗
    log_ctx γ bn fsc_fs cov logstart dev -∗
    procs_inv γs -∗
    iu_frame m -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    i_dev ip ↦₄{dqd} dev -∗
    i_inum ip ↦₄{dqn} inum -∗
    inode_meta ip dn -∗
    inode_map fsc_fs ip bm -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots 1 -∗
    log_epoch_lb γ v -∗
    (* THE ABSORPTION CREDIT (S5a finding 3, RESOURCE-FORM since fs-log.md
       §G.4): passed straight through to log_write's own [cr], where it is
       honest for exactly this reason.  This lemma no longer BUILDS it --
       the own-set claimants build it at the three derived seals below,
       and a [crz] iput hands in the group witness instead. *)
    log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
    log_opSe γ (S u) Sb e0 -∗
    (* THE REGION'S GHOST STEP, AS A PREMISE (design §20.18, stage C2).
       Which region lemma fires at log_write's ghost step -- the ordinary
       two-arm [ireg_out] one, or [InodeRegion.ireg_write_link]'s mint -- is
       the CALLER's choice, and it is the only difference between the five
       contracts this file seals.  The list [ds] is already fixed here (the
       walk learned it at its own bread), so the premise is the AU itself
       rather than [iu_region_step]'s quantified form. *)
    iu_region_au γ inodestart inum dn ds e0 Pout -∗
    bio_held bn (fs_view fsc_fs γd dev cov) kk pidv dev bno
       (diblk_bytes (<[islot inum := dn]> ds)) (diblk_bytes ds) bsd d0 -∗
    iu_cont (CID0 := CID0) bn γ inodestart ip inum dn bm
            (if cru then S u else u)
            (Sb ∪ {[IBLOCK inum inodestart]}) v Pout
            dev pidv dq dqd dqn dqs j m K eb b lks Vpr -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hthr Hs2 Hkk Hdswf Hdnwf Hbno Hcov Hlog Hbelow.
    pose proof HK as HK'.
    (* iupdate's stores move exactly this inode's 64 bytes of the buffer *)
    assert (Hslot16 : (islot inum < 16)%nat) by exact (islot_lt inum).
    assert (Hsplice : length (diblk_bytes (<[islot inum := dn]> ds)) = BSIZE ->
                      length (diblk_bytes ds) = BSIZE ->
                      length (dinode_bytes dn) = 64%nat /\
                      diblk_bytes (<[islot inum := dn]> ds)
                      = blk_splice (64 * islot inum)%nat (dinode_bytes dn)
                                   (diblk_bytes ds)).
    { intros _ _. split;
        [ exact (dinode_bytes_length dn Hdnwf)
        | exact (diblk_bytes_splice ds (islot inum) dn Hdswf Hdnwf Hslot16) ]. }
    
    iIntros "Hcg Hcnt Htc Hclm #Htext Hpc #Hbio #Hlctx #Hprocs Hframe Hppid Hidev Hinum Hmeta Hmap Hsb Hsl #Hvlb #Hcrd0 Hop Hau Hheld Hcont".
    (* THE eb/b BRIDGE, once per top-level lemma (eb-generic-sweep.md). *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    (* ===== +0x66 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iupdate + 0x66)) Ra0 Rs2
              M (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_66 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs2))]> M).
    assert (HT0a0 : T0 !!! Regidx Ra0 = bnode kk).
    { rewrite /T0 upd_eq. rgne. rewrite Hs2. apply add_vec_zero_l. }
    assert (HT0s2 : T0 !!! Regidx Rs2 = bnode kk)
      by (rewrite /T0 upd_ne; [exact Hs2 | nz]).
    assert (HT0sp : iu_sp m T0)
      by (rewrite /iu_sp /T0 upd_ne; [exact Hsp | nz]).
    assert (HT0thr : iu_thr m T0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18). }
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x66) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x68)) by pcw.
    iEval (rewrite Hpp68) in "Hpc".
    (* ===== +0x68 jal ra,log_write ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iupdate + 0x68)) Rra
              (mword_of_int 3172 : mword 21) T0 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (iui_68 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc".
    set (T1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iupdate + 0x68) : mword 64) 4)]> T0).
    assert (Htgtlw : add_vec (mword_of_int (KernelSyms.iupdate + 0x68) : mword 64)
                       (sign_extend' 64 (mword_of_int 3172 : mword 21))
                     = mword_of_int KernelSyms.log_write) by pcw.
    iEval (rewrite Htgtlw) in "Hpc".
    assert (HT1a0 : T1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /T1 upd_ne; [exact HT0a0 | nz]).
    assert (HT1s2 : T1 !!! Regidx Rs2 = bnode kk)
      by (rewrite /T1 upd_ne; [exact HT0s2 | nz]).
    assert (HT1sp : iu_sp m T1)
      by (rewrite /iu_sp /T1 upd_ne; [exact HT0sp | nz]).
    assert (HT1ra : T1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iupdate + 0x68) : mword 64) 4)
      by (rewrite /T1; apply upd_eq).
    assert (HT1thr : iu_thr m T1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T1 upd_ne; [| regne]. exact (HT0thr c Hcs N2 N8 N9 N18). }
   iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID2) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKlw : (K_log_write <= K - 4)%nat) by (lia).
    (* THE ATOMIC-UPDATE FORM (design §12.2).  The block's half is not in
       our hands and never was: [ireg_write_au] IS the premise, opening the
       region at log_write's own ghost step and paying out the retagged
       fragment.  [cr := false] (this is an ordinary uncredited spend, the
       unit is gone) and [Sb] is the caller's own set, now an explicit
       parameter: iupdate does not care which blocks this op has already
       logged, but its CALLER does, so the set is threaded rather than
       forgotten.  The counted seal below is what forgets it. *)
    iRename "Hop" into "HopS".
    (* THE CREDIT, FORWARDED (fs-log.md §G.4).  log_write's credited arm
       takes a RESOURCE, and so does this contract, so there is nothing to
       build here: the caller's credit is already stated at the block this
       flush writes, only spelled [IBLOCK inum inodestart] where log_write
       spells it [uint bno].  [Hbno] is that one equation. *)
    iAssert (log_credit γ cru Sb e0 (uint bno)) as "#Hcrd";
      [rewrite Hbno; iExact "Hcrd0" |].
    (* THE RECORD-GRANULAR FORM (durable-disk 2b-inode-1): iupdate's stores
       move exactly this inode's 64 bytes of the buffer, so what it hands
       [log_write] is the sub-range form, and the shape obligation is the
       encoding fact [InodeRegion.diblk_bytes_splice]. *)
    iApply (LW.wp_log_write_au_range bn γ fsc_fs γd cov logstart dev kk pidv bno
              (diblk_bytes (<[islot inum := dn]> ds)) (diblk_bytes ds) bsd d0 u
              (64 * islot inum)%nat 64%nat (dinode_bytes dn)
              cru Sb e0 v (⊤ ∖ ↑iregN) Pout
              T1 0%nat eb (proc_addr j) (K - 4)%nat b
              _ HKlw ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia) Hkk HT1a0
              ltac:(rewrite Hbno; exact Hcov)
              ltac:(rewrite Hbno; exact Hlog)
              (* the byte view's mask (durable-disk 1c-flip step 4) *)
              ltac:(apply subseteq_difference_r; [solve_ndisj | apply logN_top])
              (SpecLogWrite.lw_rec_window (islot inum) Hslot16)
              ltac:(lia)
              Hsplice
              Hbelow
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hsl Hvlb Hcrd HopS [Hau] Hheld").
    all: try lkbelow.
    { iEval (rewrite Hbno). iExact "Hau". }
    iIntros (CID3 Hq3 mL) "Hcg Hcnt Hpc %Hcs1 HopS Hdn Hlk Hsl".
    (* log_write returned the set grown by the block it logged, and [Hbno]
       names that block: it is THIS inum's inode block, so the growth the
       public contract promises is exact rather than existential. *)
    iEval (rewrite Hbno) in "HopS".
    (* SpecLogWrite's post now hands back the entry with its birth epoch
       named and the epoch-stamped registry row attached (fs-log.md §G.3);
       iupdate/ialloc do not spend it yet, so it is forgotten right here and
       everything below is unchanged.  G-2 replaces this line. *)
    iDestruct (log_opSwe_opSw with "HopS") as "HopS".
    iDestruct (log_opSw_witness with "HopS") as "[Hop #Hwit]".
    assert (Hpc6c : ret_pc (T1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iupdate + 0x6c)) by (rewrite HT1ra; pcw).
    iEval (rewrite Hpc6c) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmLs2 : mL !!! Regidx Rs2 = bnode kk)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HT1s2).
    assert (HmLsp : iu_sp m mL).
    { rewrite /iu_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT1sp. }
    assert (HmLthr : iu_thr m mL).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HT1thr c Hcs N2 N8 N9 N18). }
    (* ===== +0x6c c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iupdate + 0x6c)) Ra0 Rs2
              mL (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_6c with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (T2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mL Rs2))]> mL).
    assert (HT2a0 : T2 !!! Regidx Ra0 = bnode kk).
    { rewrite /T2 upd_eq. rgne. rewrite HmLs2. apply add_vec_zero_l. }
    assert (HT2sp : iu_sp m T2)
      by (rewrite /iu_sp /T2 upd_ne; [exact HmLsp | nz]).
    assert (HT2thr : iu_thr m T2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T2 upd_ne; [| regne]. exact (HmLthr c Hcs N2 N8 N9 N18). }
    assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x6c) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x6e)) by pcw.
    iEval (rewrite Hpp6e) in "Hpc".
    (* ===== +0x6e jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iupdate + 0x6e)) Rra
              (mword_of_int 2095798 : mword 21) T2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (iui_6e with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (T3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iupdate + 0x6e) : mword 64) 4)]> T2).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.iupdate + 0x6e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095798 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HT3a0 : T3 !!! Regidx Ra0 = bnode kk)
      by (rewrite /T3 upd_ne; [exact HT2a0 | nz]).
    assert (HT3sp : iu_sp m T3)
      by (rewrite /iu_sp /T3 upd_ne; [exact HT2sp | nz]).
    assert (HT3ra : T3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iupdate + 0x6e) : mword 64) 4)
      by (rewrite /T3; apply upd_eq).
    assert (HT3thr : iu_thr m T3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T3 upd_ne; [| regne]. exact (HT2thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID3 CID5 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID2) (CIDb := CID5) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 4)%nat) by (lia).
    iApply (BL.wp_brelse_sconf γs bn (fs_view fsc_fs γd dev cov) kk
              pidv dev bno dq T3 (K - 4)%nat eb (proc_addr j)
              (diblk_bytes (<[islot inum := dn]> ds)) bsd true b
              lks Vpr HKbl Hkk HT3a0
              (* brelse's bound is "bcache"(4); iu_tail's own is "log"(3),
                 and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID6 Hq6 mR) "%Hcs2 Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpc72 : ret_pc (T3 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iupdate + 0x72)) by (rewrite HT3ra; pcw).
    iEval (rewrite Hpc72) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRsp : iu_sp m mR).
    { rewrite /iu_sp
        (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT3sp. }
    assert (HmRthr : iu_thr m mR).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      exact (HT3thr c Hcs N2 N8 N9 N18). }
    iDestruct (iu_slots_join 1 1 with "Hsl Hsl1") as "Hsl".
    (* ===== +0x72 .. +0x78 : the four restores ===== *)
    rewrite /iu_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4)".
    assert (Hc1 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* +0x72 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iupdate + 0x72)) (mword_of_int 3 : mword 6) Rra
              mR (K - 4)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf1]").
    { iApply (iui_72 with "Htext"). }
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mR).
    assert (HP1sp : iu_sp m P1)
      by (rewrite /iu_sp /P1 upd_ne; [exact HmRsp | nz]).
    assert (HP1thr : iu_thr m P1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P1 upd_ne; [| regne]. exact (HmRthr c Hcs N2 N8 N9 N18). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x72) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x74)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    (* +0x74 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iupdate + 0x74)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf2]").
    { iApply (iui_74 with "Htext"). }
    { iEval (rewrite HP1sp -HmRsp Hc2). iExact "Hf2". }
    iIntros (CID8 Hq8) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -HmRsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : iu_sp m P2)
      by (rewrite /iu_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : iu_thr m P2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9 N18). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x74) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x76)) by pcw.
    iEval (rewrite Hpp76) in "Hpc".
    (* +0x76 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iupdate + 0x76)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (iui_76 with "Htext"). }
    { iEval (rewrite HP2sp -HmRsp Hc3). iExact "Hf3". }
    iIntros (CID9 Hq9) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -HmRsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : iu_sp m P3)
      by (rewrite /iu_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : iu_thr m P3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9 N18). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x76) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x78)) by pcw.
    iEval (rewrite Hpp78) in "Hpc".
    (* +0x78 c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iupdate + 0x78)) (mword_of_int 0 : mword 6) Rs2
              P3 (K - 4)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc [] [Hf4]").
    { iApply (iui_78 with "Htext"). }
    { iEval (rewrite HP3sp -HmRsp Hc4). iExact "Hf4". }
    iIntros (CID10 Hq10) "Hcg Hpc Hf4".
    iEval (rewrite HP3sp -HmRsp Hc4) in "Hf4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : iu_sp m P4)
      by (rewrite /iu_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : iu_thr m P4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9 N18). }
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x78) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x7a)) by pcw.
    iEval (rewrite Hpp7a) in "Hpc".
    (* ===== +0x7a c.addi16sp sp,32 : pop ===== *)
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP4sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
                   = 18446744073709551584) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64
                      (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
                    = 32) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551584 + 32)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0)
        by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P4 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP4sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 4)
      with "[Hf1 Hf2 Hf3 Hf4]" as "Hstk".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "Hf4"; [iExists _; iExact "Hf4" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.iupdate + 0x7a))
              (mword_of_int 2 : mword 6) P4 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc [] Hstk").
    { iApply (iui_7a with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (P5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x7a) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x7c)) by pcw.
    iEval (rewrite Hpp7c) in "Hpc".
    (* ===== +0x7c c.ret ===== *)
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.iupdate + 0x7c)) Rra P5 K b ltac:(nz)
              with "Hcg Hpc []").
    { iApply (iui_7c with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P5 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P5 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P5 upd_eq; exact Hwv).
    assert (Cs0 : P5 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Cs2 : P5 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_eq. reflexivity. }
    assert (Hfin : iu_thr m P5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P5 upd_ne; [| regne]. exact (HP4thr c Hcs N2 N8 N9 N18). }
    assert (Cs3 : P5 !!! Regidx (mword_of_int 19 : mword 5)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs4 : P5 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs5 : P5 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs6 : P5 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs7 : P5 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs8 : P5 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs9 : P5 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs10 : P5 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    assert (Cs11 : P5 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; iuidx).
    iDestruct (cpu_own_transport CID6 CID12 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* THE WIDE HOP: neither log_write nor brelse threads the complement, so
       it is still at CID0 (iu_tail's own entry hart) -- span all the way to
       here in one hop, skipping both calls (eb-generic-sweep.md). *)
    iDestruct (trap_csrs_ext_transport CID0 CID12 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID0 CID12 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    rewrite /iu_cont.
    iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P5 with "[%] Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinum
                     Hmeta Hmap Hsb Hdn Hsl Hop Hwit").
    { unfold callee_saved. split_and!; assumption. }
  Qed.

End IupdateTail.

(* ===================================================================== *)
(*  +0x00 .. +0x62 : the prologue, bread, the five field stores and the   *)
(*  memmove.                                                              *)
(* ===================================================================== *)
Section ProofIupdateMain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, ICFG : icfg, FSC : fscfg}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE GENERIC CREDITED CORE: [eb] and its complement [trap_csrs_ext]/
     [cpu_claim_ext] are REAL parameters (eb-generic-sweep.md), and [cru] is
     the absorption credit (fs-sysfile S5a finding 3), threaded straight into
     log_write's own [cr] -- [CreateBudget.iu_spend] is its arithmetic.  The
     seals below: [wp_iupdate_cred] pins [eb := true] with [emp] wands
     (the Module obligation, fs-sysfile S5b); [wp_iupdate_gen] is that at
     [cru := false]; [wp_iupdate_sconf] derives the public eb-generic
     contract threading the real wands through at [cru := false]. *)
  Lemma iu_main_gen
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z) (cru : bool) (e0 v : nat) (Pout : iProp Σ)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : let pcE : mword 64 := mword_of_int KernelSyms.iupdate in
      let pj := proc_addr j in
      let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
      (K_iupdate <= K)%nat ->
      log_geom_ok cov logstart ->
      0 <= inodestart ->
      IBLOCK inum inodestart ∈ cov ->
      ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
      bv_unsigned inum < 16 * Z.of_nat nib ->
      di_addrs dn = bm_cells bm ->
      length (bm_dir bm) = NDIRECT ->
      (j < NPROC)%nat ->
      γs !! j = Some γl ->
      m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
      (* iupdate's cone: bread ("bcache", 4), log_write ("log", 3), brelse
         ("bcache", 4) -- "log" is the lowest, so one premise there covers
         the whole cone via [locks_below_mono]. *)
      locks_below lks "log" ->
      sie_cap_gpr KT1 m K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      kernel_text -∗ kernel_data -∗ pc_is pcE -∗
      panic_env -∗
      bio_ctx bn (fs_view fsc_fs γd dev cov) -∗
      log_ctx γ bn fsc_fs cov logstart dev -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      inode_meta ip dn -∗
      inode_map fsc_fs ip bm -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      ireg_inv γi fsc_fs inodestart nib -∗
      dinode_at γi inum dn0 -∗
      (* THE REGION'S GHOST STEP, AS A PREMISE (design §20.18, stage C2):
         the caller says which region lemma fires and therefore what the
         flush pays out.  It takes the [dinode_at] above back, because the
         walk needs it first for its own [InodeRegion.ireg_read] -- that is
         where the sixteen-dinode list this step is stated over comes from,
         and why the premise quantifies over it. *)
      iu_region_step γ γi inodestart inum dn dn0 e0 Pout -∗
      proc_priv_bare pj pidv Vpr -∗
      procs_inv γs -∗
      dev_inv γu γd -∗
      disk_geom γd pd pav pu -∗
      is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
      bslots 2 -∗
      log_epoch_lb γ v -∗
      log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
      log_opSe γ (S u) Sb e0 -∗
      wp_next true pj (fun (CID : CpuId) =>
      ∀ mf : regfile,
          ⌜callee_saved m mf⌝ -∗
          sie_cap_gpr KT1 mf K b pj -∗
          cpu_own 0 eb pj b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb pj -∗
          pc_is ret_tgt -∗
          proc_priv_bare pj pidv Vpr -∗
          i_dev ip ↦₄{dqd} dev -∗
          i_inum ip ↦₄{dqn} inum -∗
          inode_meta ip dn -∗
          inode_map fsc_fs ip bm -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          Pout -∗
          bslots 2 -∗
          log_opS γ (if cru then S u else u) (Sb ∪ {[IBLOCK inum inodestart]}) -∗
          (∃ e : nat, logged_at γ e (IBLOCK inum inodestart) ∗ ⌜(v <= e)%nat⌝) -∗
          WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros pcE pj ret_tgt HK Hgeom Hst Hcov Hlog Hnib Hda Hdirlen Hj Hgl Ha0 Hbelow.
    pose proof HK as HK'. 
    destruct Hgeom as [Hcovok Hlogsub].
    destruct (Hcovok _ Hcov) as [Hibpos Hiblt].
    assert (Hib : 0 <= IBLOCK inum inodestart < 2147483648)
      by (change (2 ^ 31)%Z with 2147483648%Z in Hiblt; lia).
    (* the block number, as the 32-bit word the ABI passes *)
    set (bno := (mword_of_int (IBLOCK inum inodestart) : mword 32)).
    assert (Hbno : uint bno = IBLOCK inum inodestart).
    { rewrite /bno bb_uint32 moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    assert (Hbnolt : (uint bno < 2147483648)%Z) by (rewrite Hbno; lia).
    assert (Hbnocov : uint bno ∈ bv_cov (fs_view fsc_fs γd dev cov))
      by (rewrite Hbno; exact Hcov).
    (* the slot index *)
    pose proof (bv_unsigned_in_range _ inum) as [Hinum0 Hinum1].
    assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
      by (vm_compute; reflexivity).
    rewrite Hm32 in Hinum1.
    assert (Hslotz : Z.of_nat (islot inum) = bv_unsigned inum `mod` 16).
    { rewrite /islot Z2Nat.id; [reflexivity |].
      pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [Hz _].
      exact Hz. }
    pose proof (islot_lt inum) as Hslotlt.
    assert (Hdnwf : dinode_wf dn).
    { rewrite /dinode_wf Hda /bm_cells length_app Hdirlen. reflexivity. }
    assert (Hcelllen : length (bm_cells bm) = 13%nat)
      by (rewrite /bm_cells length_app Hdirlen; reflexivity).
    iIntros "Hcg Hcnt Htc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx Hidev Hinumc Hmeta Hmap
              Hsb #Hireg Hdn Hstep Hppid #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl #Hvlb #Hcrd0 Hop Hcont".
    (* THE eb/b BRIDGE (claude-notes/completed/eb-generic-sweep.md): derived
       once, used only to guard the [_ext_transport]s below -- [b] is never
       [subst]ed, it is spelled by name in dozens of leaf-instruction calls. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iAssert (iu_cont (CID0 := CID) bn γ inodestart ip inum dn bm
               (if cru then S u else u)
               (Sb ∪ {[IBLOCK inum inodestart]}) v Pout
               dev pidv dq dqd dqn dqs j m K eb b lks Vpr)%I with "[Hcont]" as "Hcont";
      [rewrite /iu_cont; iExact "Hcont" |].
    iDestruct "Hmeta" as "(Hmty & Hmmaj & Hmmin & Hmnl & Hmsz)".
    (* ===== +0x00 c.addi sp,sp,-32 ===== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (iui_00 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HR1sp : iu_sp m R1) by (rewrite /iu_sp /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    iDestruct "S3" as (v3) "Hf3". iDestruct "S4" as (v4) "Hf4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3". iEval (rewrite -Hb4) in "Hf4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.iupdate + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 .. +0x08 : the four saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iupdate + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat v1 b with "Hcg Hpc [] Hf1").
    { iApply (iui_02 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iupdate + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat v2 b with "Hcg Hpc [] Hf2").
    { iApply (iui_04 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iupdate + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat v3 b with "Hcg Hpc [] Hf3").
    { iApply (iui_06 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iupdate + 0x08)) (mword_of_int 0 : mword 6) Rs2
              R1 (K - 4)%nat v4 b with "Hcg Hpc [] Hf4").
    { iApply (iui_08 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc Hf4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* the frame, restated at the entry file *)
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s2 : (R1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hf3".
    iEval (rewrite Hb4; rgne; rewrite HR1s2) in "Hf4".
    iAssert (iu_frame m) with "[Hf1 Hf2 Hf3 Hf4]" as "Hframe".
    { rewrite /iu_frame.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |]. iExact "Hf4". }
    (* ===== +0x0a c.addi4spn s0,sp,32 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.iupdate + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (iui_0a with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (HR2sp : iu_sp m R2)
      by (rewrite /iu_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip)
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Ha0 | nz]).
    assert (HR2thr : iu_thr m R2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.mv s1,a0 : s1 := ip ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iupdate + 0x0c)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_0c with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = ip).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a0. apply add_vec_zero_l. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = ip)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3sp : iu_sp m R3)
      by (rewrite /iu_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : iu_thr m R3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e c.lw a5,4(a0) : a5 := ip->inum ===== *)
    assert (Hinadr : add_vec (rget R3 Ra0) (sign_extend' 64 (mword_of_int 4 : mword 12))
                     = i_inum ip).
    { rgne. rewrite HR3a0. reflexivity. }
    iEval (rewrite -Hinadr) in "Hinumc".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x0e)) Ra5 Ra0
              (mword_of_int 4 : mword 12) R3 (K - 4)%nat inum b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hinumc").
    { iApply (iui_0e with "Htext"). }
    iIntros (CID8 Hq8) "Hcg Hpc Hinumc".
    iEval (rewrite Hinadr) in "Hinumc".
    set (R4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 inum)]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5 = (sign_extend' 64 inum : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a0 : R4 !!! Regidx Ra0 = ip)
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4s1 : R4 !!! Regidx Rs1 = ip)
      by (rewrite /R4 upd_ne; [exact HR3s1 | nz]).
    assert (HR4sp : iu_sp m R4)
      by (rewrite /iu_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : iu_thr m R4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 srliw a5,a5,0x4 : a5 := inum / IPB ===== *)
    iApply (wp_srliw_s_sconf (mword_of_int (KernelSyms.iupdate + 0x10)) Ra5 Ra5
              (mword_of_int 4 : mword 5)
              (mword_of_int (bv_unsigned inum / 16) : mword 64)
              R4 (K - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HR4a5; apply iu_srliw4)
              with "Hcg Hpc []").
    { iApply (iui_10 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (R5 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (bv_unsigned inum / 16) : mword 64)]> R4).
    assert (HR5a5 : R5 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /R5; apply upd_eq).
    assert (HR5a0 : R5 !!! Regidx Ra0 = ip)
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5s1 : R5 !!! Regidx Rs1 = ip)
      by (rewrite /R5 upd_ne; [exact HR4s1 | nz]).
    assert (HR5sp : iu_sp m R5)
      by (rewrite /iu_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5thr : iu_thr m R5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R5 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x10) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 auipc a1,0x1d ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iupdate + 0x14)) Ra1
              (mword_of_int 29 : mword 20) R5 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_14 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (R6 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iupdate + 0x14) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> R5).
    assert (HR6a1 : R6 !!! Regidx Ra1
                    = add_vec (mword_of_int (KernelSyms.iupdate + 0x14) : mword 64)
                        (auipc_off (mword_of_int 29 : mword 20)))
      by (rewrite /R6; apply upd_eq).
    assert (HR6a5 : R6 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5a5 | nz]).
    assert (HR6a0 : R6 !!! Regidx Ra0 = ip)
      by (rewrite /R6 upd_ne; [exact HR5a0 | nz]).
    assert (HR6s1 : R6 !!! Regidx Rs1 = ip)
      by (rewrite /R6 upd_ne; [exact HR5s1 | nz]).
    assert (HR6sp : iu_sp m R6)
      by (rewrite /iu_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6thr : iu_thr m R6).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R6 upd_ne; [| regne]. exact (HR5thr c Hcs N2 N8 N9 N18). }
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x14) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    (* ===== +0x18 lw a1,1850(a1) : a1 := sb.inodestart ===== *)
    assert (Hsbadr : add_vec (rget R6 Ra1)
                       (sign_extend' 64 (mword_of_int 1906 : mword 12))
                     = sb_inodestart).
    { rgne. rewrite HR6a1. rewrite /sb_inodestart /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hsbadr) in "Hsb".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x18)) Ra1 Ra1
              (mword_of_int 1906 : mword 12) R6 (K - 4)%nat
              (mword_of_int inodestart : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hsb").
    { iApply (iui_18 with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc Hsb".
    iEval (rewrite Hsbadr) in "Hsb".
    set (R7 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int inodestart : mword 32))]> R6).
    assert (HR7a1 : R7 !!! Regidx Ra1
                    = (sign_extend' 64 (mword_of_int inodestart : mword 32) : mword 64))
      by (rewrite /R7; apply upd_eq).
    assert (HR7a5 : R7 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6a5 | nz]).
    assert (HR7a0 : R7 !!! Regidx Ra0 = ip)
      by (rewrite /R7 upd_ne; [exact HR6a0 | nz]).
    assert (HR7s1 : R7 !!! Regidx Rs1 = ip)
      by (rewrite /R7 upd_ne; [exact HR6s1 | nz]).
    assert (HR7sp : iu_sp m R7)
      by (rewrite /iu_sp /R7 upd_ne; [exact HR6sp | nz]).
    assert (HR7thr : iu_thr m R7).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R7 upd_ne; [| regne]. exact (HR6thr c Hcs N2 N8 N9 N18). }
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x18) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c c.addw a1,a1,a5 : a1 := IBLOCK(inum, sb) ===== *)
    iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.iupdate + 0x1c)) Ra1 Ra5
              R7 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_1c with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (R8 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64
                     (add_vec (subrange_vec_dec (rget R7 Ra1) 31 0 : mword 32)
                              (subrange_vec_dec (rget R7 Ra5) 31 0 : mword 32)))]> R7).
    assert (HR8a1 : R8 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64)).
    { rewrite /R8 upd_eq. rgne. rgne. rewrite HR7a1 HR7a5.
      rewrite /bno. apply (iu_addw_ibl inum inodestart Hst Hib). }
    assert (HR8a0 : R8 !!! Regidx Ra0 = ip)
      by (rewrite /R8 upd_ne; [exact HR7a0 | nz]).
    assert (HR8s1 : R8 !!! Regidx Rs1 = ip)
      by (rewrite /R8 upd_ne; [exact HR7s1 | nz]).
    assert (HR8sp : iu_sp m R8)
      by (rewrite /iu_sp /R8 upd_ne; [exact HR7sp | nz]).
    assert (HR8thr : iu_thr m R8).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R8 upd_ne; [| regne]. exact (HR7thr c Hcs N2 N8 N9 N18). }
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x1e)) by pcw.
    iEval (rewrite Hpp1e) in "Hpc".
    (* ===== +0x1e c.lw a0,0(a0) : a0 := ip->dev ===== *)
    assert (Hdadr : add_vec (rget R8 Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = i_dev ip).
    { rgne. rewrite HR8a0. reflexivity. }
    iEval (rewrite -Hdadr) in "Hidev".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x1e)) Ra0 Ra0
              (mword_of_int 0 : mword 12) R8 (K - 4)%nat dev b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hidev").
    { iApply (iui_1e with "Htext"). }
    iIntros (CID13 Hq13) "Hcg Hpc Hidev".
    iEval (rewrite Hdadr) in "Hidev".
    set (R9 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> R8).
    assert (HR9a0 : R9 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R9; apply upd_eq).
    assert (HR9a1 : R9 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8a1 | nz]).
    assert (HR9s1 : R9 !!! Regidx Rs1 = ip)
      by (rewrite /R9 upd_ne; [exact HR8s1 | nz]).
    assert (HR9sp : iu_sp m R9)
      by (rewrite /iu_sp /R9 upd_ne; [exact HR8sp | nz]).
    assert (HR9thr : iu_thr m R9).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R9 upd_ne; [| regne]. exact (HR8thr c Hcs N2 N8 N9 N18). }
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x20)) by pcw.
    iEval (rewrite Hpp20) in "Hpc".
    (* ===== +0x20 jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iupdate + 0x20)) Rra
              (mword_of_int 2095612 : mword 21) R9 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (iui_20 with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (RA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iupdate + 0x20) : mword 64) 4)]> R9).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.iupdate + 0x20) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095612 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HRAa0 : RA !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /RA upd_ne; [exact HR9a0 | nz]).
    assert (HRAa1 : RA !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
      by (rewrite /RA upd_ne; [exact HR9a1 | nz]).
    assert (HRAs1 : RA !!! Regidx Rs1 = ip)
      by (rewrite /RA upd_ne; [exact HR9s1 | nz]).
    assert (HRAsp : iu_sp m RA)
      by (rewrite /iu_sp /RA upd_ne; [exact HR9sp | nz]).
    assert (HRAra : RA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iupdate + 0x20) : mword 64) 4)
      by (rewrite /RA; apply upd_eq).
    assert (HRAthr : iu_thr m RA).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /RA upd_ne; [| regne]. exact (HR9thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID CID14 0 eb (proc_addr j) b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID CID14 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID CID14 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID14) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 4)%nat) by (lia).
    iDestruct (iu_slots_split 1 1 with "Hsl") as "[Hsl Hsl1]".
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view fsc_fs γd dev cov) pidv dev bno dq
              RA (K - 4)%nat eb b
              lks Vpr HKbr Hbnolt eq_refl Hbnocov eq_refl Hj Hgl HRAa0 HRAa1
              (* bread's bound is "bcache"(4); iupdate's own is "log"(3),
                 and [locks_below_mono] weakens it. *)
              ltac:(lkbelow)
              with "Hcg Hcnt Htc Hclm Htext Hkd Hpc Hpenv Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hsl1").
    all: try lkbelow.
    iIntros (CID15 Hq15 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Htc Hclm Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc24 : ret_pc (RA !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iupdate + 0x24)) by (rewrite HRAra; pcw).
    iEval (rewrite Hpc24) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs1 : mB !!! Regidx Rs1 = ip)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HRAs1).
    assert (HmBsp : iu_sp m mB).
    { rewrite /iu_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HRAsp. }
    assert (HmBthr : iu_thr m mB).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HRAthr c Hcs N2 N8 N9 N18). }
    (* THE COUPLING: the buffer's bytes ARE the sixteen dinodes.  The
       block's client half lives in the REGION, so this is one
       mask-preserving opening of [ireg_inv] (design §12.2): the machinery
       half riding in the handle's payload pins the region's parked bytes
       to the ones bread returned, and out comes the [ds] that the contract
       no longer takes.  A [={⊤}=∗] cannot be [iMod]-ed straight onto a
       [WP (Loop)] goal -- [iApply fupd_wp] first, the tree's idiom
       (ProofInitlog.v:664). *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (iu_held_k with "Hheld") as %Hkk.
    iDestruct (bio_held_fs_L with "Hheld") as "[HpL Hheldback0]".
    iApply fupd_wp.
    iMod (ireg_read ⊤ γi fsc_fs inodestart nib inum dn0 (uint bno) bs0
            ltac:(solve_ndisj) logN_top Hnib Hbno
            with "Hireg Hdn HpL") as "(%Hex & Hdn & HpL)".
    iModIntro.
    iDestruct ("Hheldback0" with "HpL") as "Hheld".
    destruct Hex as (ds & Hdswf & Hbs0 & _).
    subst bs0.
    iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
    iDestruct (iu_buf_bytes (bpa kk) bno (mword_of_int 0 : mword 32) ds Hdswf
                 with "Hbuf") as "[Hby Hbyback]".
    assert (Hslotal : dislot_align
              (pa_add (b_data (bnode kk)) (64 * islot inum)%nat)).
    { rewrite /dislot_align.
      assert (E0 : (64 * islot inum)%nat = (64 * islot inum + 0)%nat) by lia.
      split_and!.
      - rewrite E0. apply iu_align; [exact Hkk | exact Hslotlt | lia | left; reflexivity
                                   | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | right; reflexivity | reflexivity]. }
    iDestruct (diblk_slot_acc (b_data (bpa kk)) ds (islot inum)
                 Hdswf Hslotlt Hslotal with "Hby") as "[Hslot Hslotback]".
    iDestruct "Hslot" as "(Hd0 & Hd2 & Hd4 & Hd6 & Hd8 & Hda)".
    (* ===== +0x24 c.mv s2,a0 : s2 := bp ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iupdate + 0x24)) Rs2 Ra0
              mB (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_24 with "Htext"). }
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (B0 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HB0s2 : B0 !!! Regidx Rs2 = bnode kk).
    { rewrite /B0 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HB0a0 : B0 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B0 upd_ne; [exact HmBa0 | nz]).
    assert (HB0s1 : B0 !!! Regidx Rs1 = ip)
      by (rewrite /B0 upd_ne; [exact HmBs1 | nz]).
    assert (HB0sp : iu_sp m B0)
      by (rewrite /iu_sp /B0 upd_ne; [exact HmBsp | nz]).
    assert (HB0thr : iu_thr m B0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B0 upd_ne; [| regne]. exact (HmBthr c Hcs N2 N8 N9 N18). }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 addi a5,a0,88 : a5 := bp->data ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iupdate + 0x26)) Ra5 Ra0
              (mword_of_int 88 : mword 12) B0 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_26 with "Htext"). }
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (B1 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget B0 Ra0)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> B0).
    assert (HB1a5 : B1 !!! Regidx Ra5 = b_data (bnode kk)).
    { rewrite /B1 upd_eq. rgne. rewrite HB0a0. apply iu_data_addr. }
    assert (HB1s2 : B1 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HB0s2 | nz]).
    assert (HB1s1 : B1 !!! Regidx Rs1 = ip)
      by (rewrite /B1 upd_ne; [exact HB0s1 | nz]).
    assert (HB1sp : iu_sp m B1)
      by (rewrite /iu_sp /B1 upd_ne; [exact HB0sp | nz]).
    assert (HB1thr : iu_thr m B1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B1 upd_ne; [| regne]. exact (HB0thr c Hcs N2 N8 N9 N18). }
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x26) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a c.lw a4,4(s1) : a4 := ip->inum ===== *)
    assert (Hinadr2 : add_vec (rget B1 Rs1)
                        (sign_extend' 64 (mword_of_int 4 : mword 12)) = i_inum ip).
    { rgne. rewrite HB1s1. reflexivity. }
    iEval (rewrite -Hinadr2) in "Hinumc".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x2a)) Ra4 Rs1
              (mword_of_int 4 : mword 12) B1 (K - 4)%nat inum b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hinumc").
    { iApply (iui_2a with "Htext"). }
    iIntros (CID18 Hq18) "Hcg Hpc Hinumc".
    iEval (rewrite Hinadr2) in "Hinumc".
    set (B2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 inum)]> B1).
    assert (HB2a4 : B2 !!! Regidx Ra4 = (sign_extend' 64 inum : mword 64))
      by (rewrite /B2; apply upd_eq).
    assert (HB2a5 : B2 !!! Regidx Ra5 = b_data (bnode kk))
      by (rewrite /B2 upd_ne; [exact HB1a5 | nz]).
    assert (HB2s2 : B2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B2 upd_ne; [exact HB1s2 | nz]).
    assert (HB2s1 : B2 !!! Regidx Rs1 = ip)
      by (rewrite /B2 upd_ne; [exact HB1s1 | nz]).
    assert (HB2sp : iu_sp m B2)
      by (rewrite /iu_sp /B2 upd_ne; [exact HB1sp | nz]).
    assert (HB2thr : iu_thr m B2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B2 upd_ne; [| regne]. exact (HB1thr c Hcs N2 N8 N9 N18). }
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x2c)) by pcw.
    iEval (rewrite Hpp2c) in "Hpc".
    (* ===== +0x2c c.andi a4,15 : a4 := inum % IPB ===== *)
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.iupdate + 0x2c)) Ra4
              (mword_of_int 15 : mword 6) B2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_2c with "Htext"). }
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (B3 := <[Regidx Ra4 := regval_into_reg
                  (and_vec (rget B2 Ra4)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6))))]> B2).
    assert (HB3a4 : B3 !!! Regidx Ra4
                    = (mword_of_int (Z.of_nat (islot inum)) : mword 64)).
    { rewrite /B3 upd_eq. rgne. rewrite HB2a4 iu_andi15 iu_sext_mod16 Hslotz.
      reflexivity. }
    assert (HB3a5 : B3 !!! Regidx Ra5 = b_data (bnode kk))
      by (rewrite /B3 upd_ne; [exact HB2a5 | nz]).
    assert (HB3s2 : B3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B3 upd_ne; [exact HB2s2 | nz]).
    assert (HB3s1 : B3 !!! Regidx Rs1 = ip)
      by (rewrite /B3 upd_ne; [exact HB2s1 | nz]).
    assert (HB3sp : iu_sp m B3)
      by (rewrite /iu_sp /B3 upd_ne; [exact HB2sp | nz]).
    assert (HB3thr : iu_thr m B3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B3 upd_ne; [| regne]. exact (HB2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x2c) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    (* ===== +0x2e c.slli a4,0x6 : a4 := (inum % IPB) * 64 ===== *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.iupdate + 0x2e)) (Regidx Ra4) Ra4
              (mword_of_int 6 : mword 6) B3 (K - 4)%nat b
              ltac:(reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_2e with "Htext"). }
    iIntros (CID20 Hq20) "Hcg Hpc".
    set (B4 := <[Regidx Ra4 := regval_into_reg
                  (shift_bits_left (rget B3 Ra4)
                     (subrange_vec_dec (mword_of_int 6 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> B3).
    assert (HB4a4 : B4 !!! Regidx Ra4
                    = (mword_of_int (64 * Z.of_nat (islot inum)) : mword 64)).
    { rewrite /B4 upd_eq. rgne. rewrite HB3a4.
      apply iu_slli6; lia. }
    assert (HB4a5 : B4 !!! Regidx Ra5 = b_data (bnode kk))
      by (rewrite /B4 upd_ne; [exact HB3a5 | nz]).
    assert (HB4s2 : B4 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B4 upd_ne; [exact HB3s2 | nz]).
    assert (HB4s1 : B4 !!! Regidx Rs1 = ip)
      by (rewrite /B4 upd_ne; [exact HB3s1 | nz]).
    assert (HB4sp : iu_sp m B4)
      by (rewrite /iu_sp /B4 upd_ne; [exact HB3sp | nz]).
    assert (HB4thr : iu_thr m B4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B4 upd_ne; [| regne]. exact (HB3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x2e) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x30)) by pcw.
    iEval (rewrite Hpp30) in "Hpc".
    (* ===== +0x30 c.add a5,a5,a4 : a5 := dip ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.iupdate + 0x30)) Ra5 Ra4
              B4 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_30 with "Htext"). }
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (B5 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget B4 Ra5) (rget B4 Ra4))]> B4).
    assert (HB5a5 : B5 !!! Regidx Ra5
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat).
    { rewrite /B5 upd_eq. rgne. rgne. rewrite HB4a5 HB4a4. apply iu_slot_addr. }
    assert (HB5s2 : B5 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B5 upd_ne; [exact HB4s2 | nz]).
    assert (HB5s1 : B5 !!! Regidx Rs1 = ip)
      by (rewrite /B5 upd_ne; [exact HB4s1 | nz]).
    assert (HB5sp : iu_sp m B5)
      by (rewrite /iu_sp /B5 upd_ne; [exact HB4sp | nz]).
    assert (HB5thr : iu_thr m B5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B5 upd_ne; [| regne]. exact (HB4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x30) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x32)) by pcw.
    iEval (rewrite Hpp32) in "Hpc".
    (* ================= the five field copies ================= *)
    (* ---- type : lh a4,68(s1) ; sh a4,0(a5) ---- *)
    assert (Htyadr : add_vec (rget B5 Rs1)
                       (sign_extend' 64 (mword_of_int 68 : mword 12)) = i_type ip).
    { rgne. rewrite HB5s1. reflexivity. }
    iEval (rewrite -Htyadr) in "Hmty".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x32)) Ra4 Rs1
              (mword_of_int 68 : mword 12) B5 (K - 4)%nat (di_type dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hmty").
    { iApply (iui_32 with "Htext"). }
    iIntros (CID22 Hq22) "Hcg Hpc Hmty".
    iEval (rewrite Htyadr) in "Hmty".
    set (F0 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (di_type dn : mword 16))]> B5).
    assert (HF0a4 : F0 !!! Regidx Ra4 = (sign_extend' 64 (di_type dn : mword 16) : mword 64))
      by (rewrite /F0; apply upd_eq).
    assert (HF0a5 : F0 !!! Regidx Ra5
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F0 upd_ne; [exact HB5a5 | nz]).
    assert (HF0s2 : F0 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F0 upd_ne; [exact HB5s2 | nz]).
    assert (HF0s1 : F0 !!! Regidx Rs1 = ip)
      by (rewrite /F0 upd_ne; [exact HB5s1 | nz]).
    assert (HF0sp : iu_sp m F0)
      by (rewrite /iu_sp /F0 upd_ne; [exact HB5sp | nz]).
    assert (HF0thr : iu_thr m F0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F0 upd_ne; [| regne]. exact (HB5thr c Hcs N2 N8 N9 N18). }
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x32) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    assert (Hs0adr : add_vec (rget F0 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = pa_add (b_data (bpa kk)) (64 * islot inum)%nat).
    { rgne. rewrite HF0a5. apply iu_off0. }
    iEval (rewrite -Hs0adr) in "Hd0".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x36)) Ra4 Ra5
              (mword_of_int 0 : mword 12) F0 (K - 4)%nat
              (di_type (ds !!! islot inum) : mword 16) b with "Hcg Hpc [] Hd0").
    { iApply (iui_36 with "Htext"). }
    iIntros (CID23 Hq23) "Hcg Hpc Hd0".
    iEval (rewrite Hs0adr; rgne; rewrite HF0a4 trunc16_sext64) in "Hd0".
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x36) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* ---- major : lh a4,70(s1) ; sh a4,2(a5) ---- *)
    assert (Hmjadr : add_vec (rget F0 Rs1)
                       (sign_extend' 64 (mword_of_int 70 : mword 12)) = i_major ip).
    { rgne. rewrite HF0s1. reflexivity. }
    iEval (rewrite -Hmjadr) in "Hmmaj".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x3a)) Ra4 Rs1
              (mword_of_int 70 : mword 12) F0 (K - 4)%nat (di_major dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hmmaj").
    { iApply (iui_3a with "Htext"). }
    iIntros (CID24 Hq24) "Hcg Hpc Hmmaj".
    iEval (rewrite Hmjadr) in "Hmmaj".
    set (F1 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (di_major dn : mword 16))]> F0).
    assert (HF1a4 : F1 !!! Regidx Ra4 = (sign_extend' 64 (di_major dn : mword 16) : mword 64))
      by (rewrite /F1; apply upd_eq).
    assert (HF1a5 : F1 !!! Regidx Ra5
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F1 upd_ne; [exact HF0a5 | nz]).
    assert (HF1s2 : F1 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F1 upd_ne; [exact HF0s2 | nz]).
    assert (HF1s1 : F1 !!! Regidx Rs1 = ip)
      by (rewrite /F1 upd_ne; [exact HF0s1 | nz]).
    assert (HF1sp : iu_sp m F1)
      by (rewrite /iu_sp /F1 upd_ne; [exact HF0sp | nz]).
    assert (HF1thr : iu_thr m F1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F1 upd_ne; [| regne]. exact (HF0thr c Hcs N2 N8 N9 N18). }
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x3a) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x3e)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    assert (Hs2adr : add_vec (rget F1 Ra5) (sign_extend' 64 (mword_of_int 2 : mword 12))
                     = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 2).
    { rgne. rewrite HF1a5. apply (iu_disp _ 2 2%nat); [lia | lia | reflexivity]. }
    iEval (rewrite -Hs2adr) in "Hd2".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x3e)) Ra4 Ra5
              (mword_of_int 2 : mword 12) F1 (K - 4)%nat
              (di_major (ds !!! islot inum) : mword 16) b with "Hcg Hpc [] Hd2").
    { iApply (iui_3e with "Htext"). }
    iIntros (CID25 Hq25) "Hcg Hpc Hd2".
    iEval (rewrite Hs2adr; rgne; rewrite HF1a4 trunc16_sext64) in "Hd2".
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x3e) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x42)) by pcw.
    iEval (rewrite Hpp42) in "Hpc".
    (* ---- minor : lh a4,72(s1) ; sh a4,4(a5) ---- *)
    assert (Hmnadr : add_vec (rget F1 Rs1)
                       (sign_extend' 64 (mword_of_int 72 : mword 12)) = i_minor ip).
    { rgne. rewrite HF1s1. reflexivity. }
    iEval (rewrite -Hmnadr) in "Hmmin".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x42)) Ra4 Rs1
              (mword_of_int 72 : mword 12) F1 (K - 4)%nat (di_minor dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hmmin").
    { iApply (iui_42 with "Htext"). }
    iIntros (CID26 Hq26) "Hcg Hpc Hmmin".
    iEval (rewrite Hmnadr) in "Hmmin".
    set (F2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (di_minor dn : mword 16))]> F1).
    assert (HF2a4 : F2 !!! Regidx Ra4 = (sign_extend' 64 (di_minor dn : mword 16) : mword 64))
      by (rewrite /F2; apply upd_eq).
    assert (HF2a5 : F2 !!! Regidx Ra5
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F2 upd_ne; [exact HF1a5 | nz]).
    assert (HF2s2 : F2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F2 upd_ne; [exact HF1s2 | nz]).
    assert (HF2s1 : F2 !!! Regidx Rs1 = ip)
      by (rewrite /F2 upd_ne; [exact HF1s1 | nz]).
    assert (HF2sp : iu_sp m F2)
      by (rewrite /iu_sp /F2 upd_ne; [exact HF1sp | nz]).
    assert (HF2thr : iu_thr m F2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F2 upd_ne; [| regne]. exact (HF1thr c Hcs N2 N8 N9 N18). }
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x42) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x46)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    assert (Hs4adr : add_vec (rget F2 Ra5) (sign_extend' 64 (mword_of_int 4 : mword 12))
                     = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 4).
    { rgne. rewrite HF2a5. apply (iu_disp _ 4 4%nat); [lia | lia | reflexivity]. }
    iEval (rewrite -Hs4adr) in "Hd4".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x46)) Ra4 Ra5
              (mword_of_int 4 : mword 12) F2 (K - 4)%nat
              (di_minor (ds !!! islot inum) : mword 16) b with "Hcg Hpc [] Hd4").
    { iApply (iui_46 with "Htext"). }
    iIntros (CID27 Hq27) "Hcg Hpc Hd4".
    iEval (rewrite Hs4adr; rgne; rewrite HF2a4 trunc16_sext64) in "Hd4".
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x46) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x4a)) by pcw.
    iEval (rewrite Hpp4a) in "Hpc".
    (* ---- nlink : lh a4,74(s1) ; sh a4,6(a5) ---- *)
    assert (Hnladr : add_vec (rget F2 Rs1)
                       (sign_extend' 64 (mword_of_int 74 : mword 12)) = i_nlink ip).
    { rgne. rewrite HF2s1. reflexivity. }
    iEval (rewrite -Hnladr) in "Hmnl".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x4a)) Ra4 Rs1
              (mword_of_int 74 : mword 12) F2 (K - 4)%nat (di_nlink dn : mword 16) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hmnl").
    { iApply (iui_4a with "Htext"). }
    iIntros (CID28 Hq28) "Hcg Hpc Hmnl".
    iEval (rewrite Hnladr) in "Hmnl".
    set (F3 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (di_nlink dn : mword 16))]> F2).
    assert (HF3a4 : F3 !!! Regidx Ra4 = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
      by (rewrite /F3; apply upd_eq).
    assert (HF3a5 : F3 !!! Regidx Ra5
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F3 upd_ne; [exact HF2a5 | nz]).
    assert (HF3s2 : F3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F3 upd_ne; [exact HF2s2 | nz]).
    assert (HF3s1 : F3 !!! Regidx Rs1 = ip)
      by (rewrite /F3 upd_ne; [exact HF2s1 | nz]).
    assert (HF3sp : iu_sp m F3)
      by (rewrite /iu_sp /F3 upd_ne; [exact HF2sp | nz]).
    assert (HF3thr : iu_thr m F3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F3 upd_ne; [| regne]. exact (HF2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x4a) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x4e)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    assert (Hs6adr : add_vec (rget F3 Ra5) (sign_extend' 64 (mword_of_int 6 : mword 12))
                     = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 6).
    { rgne. rewrite HF3a5. apply (iu_disp _ 6 6%nat); [lia | lia | reflexivity]. }
    iEval (rewrite -Hs6adr) in "Hd6".
    iApply (wp_sh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x4e)) Ra4 Ra5
              (mword_of_int 6 : mword 12) F3 (K - 4)%nat
              (di_nlink (ds !!! islot inum) : mword 16) b with "Hcg Hpc [] Hd6").
    { iApply (iui_4e with "Htext"). }
    iIntros (CID29 Hq29) "Hcg Hpc Hd6".
    iEval (rewrite Hs6adr; rgne; rewrite HF3a4 trunc16_sext64) in "Hd6".
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x4e) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x52)) by pcw.
    iEval (rewrite Hpp52) in "Hpc".
    (* ---- size : c.lw a4,76(s1) ; c.sw a4,8(a5) ---- *)
    assert (Hszadr : add_vec (rget F3 Rs1)
                       (sign_extend' 64 (mword_of_int 76 : mword 12)) = i_size ip).
    { rgne. rewrite HF3s1. reflexivity. }
    iEval (rewrite -Hszadr) in "Hmsz".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.iupdate + 0x52)) Ra4 Rs1
              (mword_of_int 76 : mword 12) F3 (K - 4)%nat (di_size dn : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hmsz").
    { iApply (iui_52 with "Htext"). }
    iIntros (CID30 Hq30) "Hcg Hpc Hmsz".
    iEval (rewrite Hszadr) in "Hmsz".
    set (F4 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (di_size dn : mword 32))]> F3).
    assert (HF4a4 : F4 !!! Regidx Ra4 = (sign_extend' 64 (di_size dn : mword 32) : mword 64))
      by (rewrite /F4; apply upd_eq).
    assert (HF4a5 : F4 !!! Regidx Ra5
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /F4 upd_ne; [exact HF3a5 | nz]).
    assert (HF4s2 : F4 !!! Regidx Rs2 = bnode kk)
      by (rewrite /F4 upd_ne; [exact HF3s2 | nz]).
    assert (HF4s1 : F4 !!! Regidx Rs1 = ip)
      by (rewrite /F4 upd_ne; [exact HF3s1 | nz]).
    assert (HF4sp : iu_sp m F4)
      by (rewrite /iu_sp /F4 upd_ne; [exact HF3sp | nz]).
    assert (HF4thr : iu_thr m F4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /F4 upd_ne; [| regne]. exact (HF3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x52) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x54)) by pcw.
    iEval (rewrite Hpp54) in "Hpc".
    assert (Hs8adr : add_vec (rget F4 Ra5) (sign_extend' 64 (mword_of_int 8 : mword 12))
                     = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 8).
    { rgne. rewrite HF4a5. apply (iu_disp _ 8 8%nat); [lia | lia | reflexivity]. }
    iEval (rewrite -Hs8adr) in "Hd8".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.iupdate + 0x54)) Ra4 Ra5
              (mword_of_int 8 : mword 12) F4 (K - 4)%nat
              (di_size (ds !!! islot inum) : mword 32) b with "Hcg Hpc [] Hd8").
    { iApply (iui_54 with "Htext"). }
    iIntros (CID31 Hq31) "Hcg Hpc Hd8".
    iEval (rewrite Hs8adr; rgne; rewrite HF4a4 trunc32_sext64) in "Hd8".
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x54) : mword 64) 2
                    = mword_of_int (KernelSyms.iupdate + 0x56)) by pcw.
    iEval (rewrite Hpp56) in "Hpc".
    (* ================= memmove(dip->addrs, ip->addrs, 52) ================= *)
    (* ---- +0x56 li a2,52 ---- *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.iupdate + 0x56)) Ra2
              (mword_of_int 52 : mword 12)
              (mword_of_int (Z.of_nat 52%nat) : mword 64) F4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (iui_56 with "Htext"). }
    iIntros (CID32 Hq32) "Hcg Hpc".
    set (G0 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 52%nat) : mword 64)]> F4).
    assert (HG0a2 : G0 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 52%nat) : mword 64))
      by (rewrite /G0; apply upd_eq).
    assert (HG0a5 : G0 !!! Regidx Ra5
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /G0 upd_ne; [exact HF4a5 | nz]).
    assert (HG0s2 : G0 !!! Regidx Rs2 = bnode kk)
      by (rewrite /G0 upd_ne; [exact HF4s2 | nz]).
    assert (HG0s1 : G0 !!! Regidx Rs1 = ip)
      by (rewrite /G0 upd_ne; [exact HF4s1 | nz]).
    assert (HG0sp : iu_sp m G0)
      by (rewrite /iu_sp /G0 upd_ne; [exact HF4sp | nz]).
    assert (HG0thr : iu_thr m G0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G0 upd_ne; [| regne]. exact (HF4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x56) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x5a)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* ---- +0x5a addi a1,s1,80 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iupdate + 0x5a)) Ra1 Rs1
              (mword_of_int 80 : mword 12) G0 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_5a with "Htext"). }
    iIntros (CID33 Hq33) "Hcg Hpc".
    set (G1 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget G0 Rs1)
                     (sign_extend' 64 (mword_of_int 80 : mword 12)))]> G0).
    assert (HG1a1 : G1 !!! Regidx Ra1 = i_addr ip 0).
    { rewrite /G1 upd_eq. rgne. rewrite HG0s1. apply iu_addrs0. }
    assert (HG1a2 : G1 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 52%nat) : mword 64))
      by (rewrite /G1 upd_ne; [exact HG0a2 | nz]).
    assert (HG1a5 : G1 !!! Regidx Ra5
                    = pa_add (b_data (bnode kk)) (64 * islot inum)%nat)
      by (rewrite /G1 upd_ne; [exact HG0a5 | nz]).
    assert (HG1s2 : G1 !!! Regidx Rs2 = bnode kk)
      by (rewrite /G1 upd_ne; [exact HG0s2 | nz]).
    assert (HG1s1 : G1 !!! Regidx Rs1 = ip)
      by (rewrite /G1 upd_ne; [exact HG0s1 | nz]).
    assert (HG1sp : iu_sp m G1)
      by (rewrite /iu_sp /G1 upd_ne; [exact HG0sp | nz]).
    assert (HG1thr : iu_thr m G1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G1 upd_ne; [| regne]. exact (HG0thr c Hcs N2 N8 N9 N18). }
    assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x5a) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x5e)) by pcw.
    iEval (rewrite Hpp5e) in "Hpc".
    (* ---- +0x5e addi a0,a5,12 ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iupdate + 0x5e)) Ra0 Ra5
              (mword_of_int 12 : mword 12) G1 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (iui_5e with "Htext"). }
    iIntros (CID34 Hq34) "Hcg Hpc".
    set (G2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget G1 Ra5)
                     (sign_extend' 64 (mword_of_int 12 : mword 12)))]> G1).
    assert (HG2a0 : G2 !!! Regidx Ra0
                    = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 12).
    { rewrite /G2 upd_eq. rgne. rewrite HG1a5.
      apply (iu_disp _ 12 12%nat); [lia | lia | reflexivity]. }
    assert (HG2a1 : G2 !!! Regidx Ra1 = i_addr ip 0)
      by (rewrite /G2 upd_ne; [exact HG1a1 | nz]).
    assert (HG2a2 : G2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 52%nat) : mword 64))
      by (rewrite /G2 upd_ne; [exact HG1a2 | nz]).
    assert (HG2s2 : G2 !!! Regidx Rs2 = bnode kk)
      by (rewrite /G2 upd_ne; [exact HG1s2 | nz]).
    assert (HG2sp : iu_sp m G2)
      by (rewrite /iu_sp /G2 upd_ne; [exact HG1sp | nz]).
    assert (HG2thr : iu_thr m G2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G2 upd_ne; [| regne]. exact (HG1thr c Hcs N2 N8 N9 N18). }
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.iupdate + 0x5e) : mword 64) 4
                    = mword_of_int (KernelSyms.iupdate + 0x62)) by pcw.
    iEval (rewrite Hpp62) in "Hpc".
    (* ---- +0x62 jal ra,memmove ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iupdate + 0x62)) Rra
              (mword_of_int 2087718 : mword 21) G2 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (iui_62 with "Htext"). }
    iIntros (CID35 Hq35) "Hcg Hpc".
    set (G3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iupdate + 0x62) : mword 64) 4)]> G2).
    assert (Htgtmm : add_vec (mword_of_int (KernelSyms.iupdate + 0x62) : mword 64)
                       (sign_extend' 64 (mword_of_int 2087718 : mword 21))
                     = mword_of_int KernelSyms.memmove) by pcw.
    iEval (rewrite Htgtmm) in "Hpc".
    assert (HG3a0 : G3 !!! Regidx Ra0
                    = pa_add (pa_add (b_data (bpa kk)) (64 * islot inum)%nat) 12)
      by (rewrite /G3 upd_ne; [exact HG2a0 | nz]).
    assert (HG3a1 : G3 !!! Regidx Ra1 = i_addr ip 0)
      by (rewrite /G3 upd_ne; [exact HG2a1 | nz]).
    assert (HG3a2 : G3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 52%nat) : mword 64))
      by (rewrite /G3 upd_ne; [exact HG2a2 | nz]).
    assert (HG3s2 : G3 !!! Regidx Rs2 = bnode kk)
      by (rewrite /G3 upd_ne; [exact HG2s2 | nz]).
    assert (HG3sp : iu_sp m G3)
      by (rewrite /iu_sp /G3 upd_ne; [exact HG2sp | nz]).
    assert (HG3ra : G3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iupdate + 0x62) : mword 64) 4)
      by (rewrite /G3; apply upd_eq).
    assert (HG3thr : iu_thr m G3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G3 upd_ne; [| regne]. exact (HG2thr c Hcs N2 N8 N9 N18). }
    (* the SOURCE: the thirteen addrs cells as 52 contiguous bytes *)
    iDestruct "Hmap" as "[Haddrs Hindres]".
    iDestruct (inode_addrs_buf ip (bm_cells bm) with "Haddrs") as "[Hsrc Hsrcback]".
    iEval (rewrite Hcelllen) in "Hsrc".
    iEval (change (4 * 13)%nat with 52%nat) in "Hsrc".
    assert (Hlen32 : (Z.of_nat 52%nat < 2 ^ 32)%Z) by (vm_compute; reflexivity).
    assert (HKmm : (2 <= K - 4)%nat) by lia.
    iEval (rewrite -HG3a1) in "Hsrc".
    iEval (rewrite /bb_bytes -HG3a0) in "Hda".
    iApply (MM.wp_memmove_sconf KT1 KT0 KT0 G3 (K - 4)%nat 52%nat
              (fun jj => ind_bytes (bm_cells bm) !!! jj)
              (fun jj => ind_bytes (di_addrs (ds !!! islot inum)) !!! jj)
              (DfracOwn 1) b (proc_addr j) HKmm Hlen32 HG3a2
              with "Hcg Htext Hpc Hsrc Hda").
    iIntros (CID36 Hq36 mM) "Hcg Hpc Hsrc Hdst %Hmma0 %Hcsmm".
    assert (Hpc66 : ret_pc (G3 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iupdate + 0x66)) by (rewrite HG3ra; pcw).
    iEval (rewrite Hpc66) in "Hpc".
    iEval (rewrite HG3a1) in "Hsrc".
    iEval (rewrite HG3a0) in "Hdst".
    iEval (change 52%nat with (4 * 13)%nat; rewrite -Hcelllen) in "Hsrc".
    iDestruct ("Hsrcback" with "Hsrc") as "Haddrs".
    iAssert (inode_map fsc_fs ip bm) with "[Haddrs Hindres]" as "Hmap".
    { rewrite /inode_map. iSplitL "Haddrs"; [iExact "Haddrs" | iExact "Hindres"]. }
    (* the destination window is now the NEW dinode's addrs image *)
    iEval (rewrite -Hda) in "Hdst".
    pose proof Hcsmm as Hcsmm_cs.
    assert (HmMs2 : mM !!! Regidx Rs2 = bnode kk)
      by (rewrite (callee_saved_lookup Hcsmm_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HG3s2).
    assert (HmMsp : iu_sp m mM).
    { rewrite /iu_sp
        (callee_saved_lookup Hcsmm_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HG3sp. }
    assert (HmMthr : iu_thr m mM).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcsmm_cs c Hcs).
      exact (HG3thr c Hcs N2 N8 N9 N18). }
    (* ---- rebuild the slot at the NEW dinode, and the buffer with it ---- *)
    iDestruct ("Hslotback" $! dn with "[%] [Hd0 Hd2 Hd4 Hd6 Hd8 Hdst]") as "Hby".
    { exact Hdnwf. }
    { rewrite /dislot.
      iSplitL "Hd0"; [iExact "Hd0" |].
      iSplitL "Hd2"; [iExact "Hd2" |].
      iSplitL "Hd4"; [iExact "Hd4" |].
      iSplitL "Hd6"; [iExact "Hd6" |].
      iSplitL "Hd8"; [iExact "Hd8" |].
      rewrite /bb_bytes Hda. iExact "Hdst". }
    iDestruct ("Hbyback" $! (<[islot inum := dn]> ds) with "[%] Hby") as "Hbuf".
    { exact (diblk_wf_insert ds (islot inum) dn Hdswf Hdnwf). }
    iDestruct ("Hheldback" with "Hbuf") as "Hheld".
    (* ---- into the tail ---- *)
    iDestruct (cpu_own_transport CID15 CID36 0 eb (proc_addr j) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID15 CID36 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID15 CID36 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    (* THE STEP, AT THE LIST THE WALK LEARNED: [ds] is fixed from here on,
       so the caller's quantified premise is instantiated once and the tail
       takes the atomic update itself. *)
    (* THE PAYLOAD'S INDEX FUNCTION, NAMED ONCE (durable-disk 1d').  The
       log's parked payload crosses [log_write]'s atomic update, so the
       contract below is stated over the log's own context; the caller's
       ghost step is quantified over the record list precisely so that
       existential here costs no seal above a line. *)
    (* THE PAYLOAD-STEP PREMISE (durable-disk 3a, ratified (D)): the caller
       is the one that holds the log's context, so it is the one that can
       justify the payload's logged-index move.  It hands it to the region
       step, which cannot build it. *)
    iDestruct ("Hstep" $! ds with "[%] Hdn") as "Hau";
      [exact Hdswf |].
    iApply (iu_tail (CID0 := CID36) γs j γd bn γ cov logstart inodestart
              dev
              ip inum dn bm ds u Sb cru e0 v kk bno bsd0 d0 Pout
              pidv dq dqd dqn dqs m mM K eb b lks
              Vpr HK HmMsp HmMthr HmMs2 Hkk Hdswf Hdnwf Hbno Hcov Hlog Hbelow
              with "Hcg Hcnt Htc Hclm Htext Hpc Hbio Hlctx Hprocs Hframe
                    Hppid Hidev Hinumc [Hmty Hmmaj Hmmin Hmnl Hmsz] Hmap Hsb
                    Hsl Hvlb Hcrd0 Hop Hau Hheld [Hcont]").
    { rewrite /inode_meta.
      iSplitL "Hmty"; [iExact "Hmty" |]. iSplitL "Hmmaj"; [iExact "Hmmaj" |].
      iSplitL "Hmmin"; [iExact "Hmmin" |]. iSplitL "Hmnl"; [iExact "Hmnl" |].
      iExact "Hmsz". }
    { iApply (wp_next_shift (b := true) (CIDa := CID14) (CIDb := CID36) ltac:(wp_next_chain)
                with "Hcont"). }
Qed.

  Lemma wp_iupdate_gen
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_iupdate_gen_body γs j γl γu γd γk pd pav pu bn γ γi
                          cov logstart inodestart nib dev ip inum dn dn0 bm u Sb
                          pidv dq dqd dqn dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_iupdate_gen_body].
    intros pcE pj ret_tgt HK Hgeom Hst Hcov Hlog Hnib Hstab Hnlk Hnzty Hda Hdirlen Hj Hgl Ha0 Hbelow.
    iIntros "Hcg Hcnt Htc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx Hidev Hinumc Hmeta Hmap
              Hsb #Hireg Hdn Hppid #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl Hop Hcont".
    (* the trivial anchor: a lower bound of zero is the unit, so the three
       derived seals cost their callers nothing (fs-log.md §G.17) *)
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    (* THE EPOCH, OPENED AND RE-CLOSED (fs-log.md §G.4, and §G.19's shape
       one tier down).  The core states its credit against a NAMED birth
       epoch; this seal has no credit to make ([cru := false], where the
       resource is [emp]), so the name is opened here, used by
       [log_credit_own], and forgotten again on the way out.  That is what
       keeps this statement -- and ProofWritei / ProofDirlink / ProofIalloc
       under it -- byte-stable. *)
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iPoseProof (log_credit_own γ false Sb e0 (IBLOCK inum inodestart)
                  ltac:(discriminate)) as "#Hcrd".
    (* THE ORDINARY GHOST STEP (§20.18 C2): the two-arm region move this
       contract always made, now supplied to the core rather than wired
       into it. *)
    iPoseProof (iu_step_out γ γi inodestart nib inum dn dn0 e0 Hnib
                  (iu_dinode_wf dn bm Hda Hdirlen) Hstab Hnlk Hnzty
                  with "Hireg") as "Hstep".
    iApply (iu_main_gen γs j γl γu γd γk pd pav pu bn γ γi
              cov logstart inodestart nib dev ip inum dn dn0 bm u Sb false e0 0%nat
              (ireg_out γi inum dn)
              pidv dq dqd dqn dqs m K eb b lks
              Vpr HK Hgeom Hst Hcov Hlog Hnib Hda Hdirlen Hj Hgl Ha0 Hbelow
              with "Hcg Hcnt Htc Hclm Htext Hkd Hpc Hpenv Hbio Hlctx Hidev Hinumc Hmeta Hmap
                    Hsb Hireg Hdn Hstep Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hlb0 Hcrd Hop
                    [Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf) "%Hcs Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap Hsb
                  Hiout Hsl Hop Hwit".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap
                     Hsb Hiout Hsl Hop").
    exact Hcs.
  Qed.

  (* THE CREDITED eb-GENERIC SEAL (fs-sysfile GR-2b): [iu_main_gen] with
     NOTHING pinned -- it IS the generic core, so the seal is the same
     plumbing [wp_iupdate_gen] does with [cru] passed through instead of
     [false].  itrunc's tail flush needs exactly this: the credit, at an
     [eb] its own pass-through contract quantifies over. *)
  Lemma wp_iupdate_credgen
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z) (cru : bool) (e0 v : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_iupdate_credgen_body γs j γl γu γd γk pd pav pu bn γ γi
                              cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru e0 v
                              pidv dq dqd dqn dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_iupdate_credgen_body].
    intros pcE pj ret_tgt HK Hgeom Hst Hcov Hlog Hnib Hstab Hnlk Hnzty Hda Hdirlen Hj Hgl Ha0 Hbelow.
    iIntros "Hcg Hcnt Htc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx Hidev Hinumc Hmeta Hmap
              Hsb #Hireg Hdn Hppid #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl #Hvlb #Hcrd Hop Hcont".
    iPoseProof (iu_step_out γ γi inodestart nib inum dn dn0 e0 Hnib
                  (iu_dinode_wf dn bm Hda Hdirlen) Hstab Hnlk Hnzty
                  with "Hireg") as "Hstep".
    iApply (iu_main_gen γs j γl γu γd γk pd pav pu bn γ γi
              cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru e0 v
              (ireg_out γi inum dn)
              pidv dq dqd dqn dqs m K eb b lks
              Vpr HK Hgeom Hst Hcov Hlog Hnib Hda Hdirlen Hj Hgl Ha0 Hbelow
              with "Hcg Hcnt Htc Hclm Htext Hkd Hpc Hpenv Hbio Hlctx Hidev Hinumc Hmeta Hmap
                    Hsb Hireg Hdn Hstep Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hvlb Hcrd Hop
                    [Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf) "%Hcs Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap Hsb
                  Hiout Hsl Hop Hwit".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap
                     Hsb Hiout Hsl Hop Hwit").
    exact Hcs.
  Qed.

  (* THE CREDITED SEAL (fs-sysfile S5b's Module obligation): [iu_main_gen]
     pinned at [eb := true], where both complements are [emp] by definition
     ([trap_csrs_ext true] / [cpu_claim_ext true]); the callback drops the
     two [emp] wands the generic core hands back. *)
  Lemma wp_iupdate_cred
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z) (cru : bool)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_iupdate_cred_body γs j γl γu γd γk pd pav pu bn γ γi
                           cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru
                           pidv dq dqd dqn dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_iupdate_cred_body].
    intros pcE pj ret_tgt HK Hcru Hgeom Hst Hcov Hlog Hnib Hstab Hnlk Hnzty Hda Hdirlen Hj Hgl Ha0 Heb Hbelow.
    subst eb.
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx Hidev Hinumc Hmeta Hmap
              Hsb #Hireg Hdn Hppid #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl Hop Hcont".
    (* the trivial anchor: a lower bound of zero is the unit, so the three
       derived seals cost their callers nothing (fs-log.md §G.17) *)
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    (* the own-set credit, at the epoch opened here and forgotten again *)
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iPoseProof (log_credit_own γ cru Sb e0 (IBLOCK inum inodestart) Hcru)
      as "#Hcrd".
    iPoseProof (iu_step_out γ γi inodestart nib inum dn dn0 e0 Hnib
                  (iu_dinode_wf dn bm Hda Hdirlen) Hstab Hnlk Hnzty
                  with "Hireg") as "Hstep".
    iApply (iu_main_gen γs j γl γu γd γk pd pav pu bn γ γi
              cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru e0 0%nat
              (ireg_out γi inum dn)
              pidv dq dqd dqn dqs m K true b lks
              Vpr HK Hgeom Hst Hcov Hlog Hnib Hda Hdirlen Hj Hgl Ha0 Hbelow
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlctx Hidev Hinumc Hmeta Hmap
                    Hsb Hireg Hdn Hstep Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hlb0 Hcrd Hop
                    [Hcont]").
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf) "%Hcs Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap Hsb
                  Hiout Hsl Hop Hwit".
    iClear "Htc Hclm".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hpc Hppid Hidev Hinumc Hmeta Hmap
                     Hsb Hiout Hsl Hop").
    exact Hcs.
  Qed.

  (* THE COUNTED SEAL, derived at the [log_op] existential's OWN WITNESS
     (fs-icache.md section 18; ProofBmap's wp_bmap_sconf, same shape).
     [log_op γ u] IS [∃ Sb, log_opS γ u Sb], so the counted form destructs
     it, runs the core at whatever set was hiding there, and forgets the
     grown set again on the way out via [log_opS_op].  Deriving at [Sb := ∅]
     instead would force every counted caller to prove its set empty, which
     is both false and unnecessary. *)
  Lemma wp_iupdate_sconf
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_iupdate_sconf_body γs j γl γu γd γk pd pav pu bn γ γi
                            cov logstart inodestart nib dev ip inum dn dn0 bm u
                            pidv dq dqd dqn dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_iupdate_sconf_body].
    intros pcE pj ret_tgt HK Hgeom Hst Hcov Hlog Hnib Hstab Hnlk Hnzty Hda Hdirlen Hj Hgl Ha0 Hbelow.
    iIntros "Hcg Hcnt Htc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx Hidev Hinumc Hmeta Hmap
              Hsb #Hireg Hdn Hppid #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl Hop Hcont".
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    iDestruct (log_op_openS with "Hop") as (Sb0) "[Hop Htx]".
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iPoseProof (log_credit_own γ false Sb0 e0 (IBLOCK inum inodestart)
                  ltac:(discriminate)) as "#Hcrd".
    iPoseProof (iu_step_out γ γi inodestart nib inum dn dn0 e0 Hnib
                  (iu_dinode_wf dn bm Hda Hdirlen) Hstab Hnlk Hnzty
                  with "Hireg") as "Hstep".
    iApply (iu_main_gen γs j γl γu γd γk pd pav pu bn γ γi
              cov logstart inodestart nib dev ip inum dn dn0 bm u Sb0 false e0 0%nat
              (ireg_out γi inum dn)
              pidv dq dqd dqn dqs m K eb b lks
              Vpr HK Hgeom Hst Hcov Hlog Hnib Hda Hdirlen Hj Hgl Ha0 Hbelow
              with "Hcg Hcnt Htc Hclm Htext Hkd Hpc Hpenv Hbio Hlctx Hidev Hinumc Hmeta Hmap
                    Hsb Hireg Hdn Hstep Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hlb0 Hcrd Hop
                    [Hcont Htx]").
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf) "%Hcs Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap Hsb
                  Hiout Hsl Hop Hwit".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap
                     Hsb Hiout Hsl [Hop Htx]").
    { exact Hcs. }
    { iApply (log_opS_op with "Hop Htx"). }
  Qed.

  (* THE LINK-MINTING SEAL (design fs-icache.md §20.18, stage C2).  The
     credited seal's plumbing with ONE substitution: [iu_step_link] fills
     the region's ghost step instead of [iu_step_out], so the payout is the
     retagged fragment PLUS the link token the flushed [nlink++] pays for.
     Nothing else about the walk changes -- [InodeRegion.ireg_write_link_reg]'s
     fupd is byte-for-byte [ireg_write_au]'s -- which is exactly what the
     [Pout] parameter was introduced to make visible. *)
  Lemma wp_iupdate_link
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z) (cru : bool)
      (pin : bool) (oty : option ity)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_iupdate_link_body γs j γl γu γd γk pd pav pu bn γ γi
                           cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru
                           pin oty pidv dq dqd dqn dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_iupdate_link_body].
    intros pcE pj ret_tgt HK Hcru Hgeom Hst Hcov Hlog Hnib Hstab Hnz
           Hup Hbump Hgrd
           Hda Hdirlen Hj Hgl Ha0 Heb Hbelow.
    subst eb.
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx Hidev Hinumc Hmeta Hmap
              Hsb #Hireg Hdn Hpin Hppid #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl Hop Hcont".
    (* the trivial anchor and the own-set credit, exactly as the credited
       seal builds them *)
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iPoseProof (log_credit_own γ cru Sb e0 (IBLOCK inum inodestart) Hcru)
      as "#Hcrd".
    (* THE ONE SUBSTITUTION *)
    iPoseProof (iu_step_link γ γi inodestart nib inum dn dn0 e0 pin oty Hnib
                  (iu_dinode_wf dn bm Hda Hdirlen) Hnz Hstab Hbump Hgrd
                  Hup
                  with "Hireg Hpin") as "Hstep".
    iApply (iu_main_gen γs j γl γu γd γk pd pav pu bn γ γi
              cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru e0 0%nat
              (dinode_at γi inum dn ∗
               (∃ v : ity,
          ⌜ireg_reg_ok (bv_unsigned (di_type dn)) v
           /\ (forall w, oty = Some w -> v = w)⌝
          ∗ FsStateLink.link_toks (FsBytesGamma.fs_gamma_L fsc_fs)
              (bv_unsigned inum)
              (FsStateLink.link_reps
                 (ireg_dot_delta (bv_unsigned (di_type dn0))
                    (bv_unsigned (di_nlink dn0))) v)) ∗
               ireg_link_pin pin (bv_unsigned inum) dn0)%I
              pidv dq dqd dqn dqs m K true b lks Vpr
              HK Hgeom Hst Hcov Hlog Hnib Hda Hdirlen Hj Hgl Ha0 Hbelow
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlctx Hidev Hinumc Hmeta Hmap
                    Hsb Hireg Hdn Hstep Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hlb0 Hcrd Hop
                    [Hcont]").
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf) "%Hcs Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap Hsb
                  Hiout Hsl Hop Hwit".
    iClear "Htc Hclm".
    (* the payout, taken apart into the contract's two wands *)
    iDestruct "Hiout" as "(Hdnout & Htok & Hpin)".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hpc Hppid Hidev Hinumc Hmeta Hmap
                     Hsb Hdnout Htok Hpin Hsl Hop").
    exact Hcs.
  Qed.

  (* THE LINK-SPENDING SEAL (design fs-icache.md §20.18, stage C4).  The
     link-minting seal's plumbing with ONE substitution again --
     [iu_step_unlink] fills the region's ghost step -- plus the link token
     and the receipt choice threaded into it.  The walk itself is untouched:
     [InodeRegion.ireg_write_unlink_reg]'s fupd is the atomic update's shape,
     and that is the whole of what [SpecLogWrite]'s C4 edit bought. *)
  Lemma wp_iupdate_unlink
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (dev : mword 32)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (u : nat) (Sb : gset Z) (cru : bool)
      (uty : ity)
      (pidv : mword 32) (dq dqd dqn dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_iupdate_unlink_body γs j γl γu γd γk pd pav pu bn γ γi
                             cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru
                             uty pidv dq dqd dqn dqs m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_iupdate_unlink_body].
    intros pcE pj ret_tgt HK Hcru Hgeom Hst Hcov Hlog Hnib Hstab Hnz Hnl
           Hda Hdirlen
           Hj Hgl Ha0 Heb Hbelow.
    subst eb.
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx Hidev Hinumc Hmeta Hmap
              Hsb #Hireg Hdn Htok Hrc Hppid #Hprocs #Hdevi #Hdgeom
              #Hdlock Hsl Hop Hcont".
    (* the trivial DEPOSITOR anchor and the own-set credit, exactly as the
       link-minting seal builds them: this contract's receipt is the
       WRITER's, cashed inside the region's own fupd, so the [v] the walk
       threads is still the unit. *)
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iPoseProof (log_credit_own γ cru Sb e0 (IBLOCK inum inodestart) Hcru)
      as "#Hcrd".
    (* THE ONE SUBSTITUTION *)
    iPoseProof (iu_step_unlink γ γi inodestart nib inum dn dn0 e0 uty Hnib
                  (iu_dinode_wf dn bm Hda Hdirlen) Hnz Hstab Hnl
                  with "Hireg Htok Hrc") as "Hstep".
    iApply (iu_main_gen γs j γl γu γd γk pd pav pu bn γ γi
              cov logstart inodestart nib dev ip inum dn dn0 bm u Sb cru e0 0%nat
              (dinode_at γi inum dn)%I
              pidv dq dqd dqn dqs m K true b lks Vpr
              HK Hgeom Hst Hcov Hlog Hnib Hda Hdirlen Hj Hgl Ha0 Hbelow
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hlctx Hidev Hinumc Hmeta Hmap
                    Hsb Hireg Hdn Hstep Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Hlb0 Hcrd Hop
                    [Hcont]").
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf) "%Hcs Hcg Hcnt Htc Hclm Hpc Hppid Hidev Hinumc Hmeta Hmap Hsb
                  Hiout Hsl Hop Hwit".
    iClear "Htc Hclm".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hpc Hppid Hidev Hinumc Hmeta Hmap
                     Hsb Hiout Hsl Hop").
    exact Hcs.
  Qed.

End ProofIupdateMain.

End IupdateProof.
