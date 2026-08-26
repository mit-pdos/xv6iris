(* ====================================================================== *)
(*  SbPark.v -- WHO OWNS BLOCK 1 (durable-disk lane C-3a)                  *)
(*  (claude-notes/design/durable-fs-plan.md section 4; the gap is listed   *)
(*   as (C) in FsCollect.v's header)                                       *)
(*                                                                        *)
(*  NOBODY DID.  The era hands [fsblock (fs_bytes γfs) 1 bs_sb] to fsinit  *)
(*  ([FsCfgBoot.fs_kit_fsinit_ghost]), fsinit's post returned it and       *)
(*  forkret DROPPED it -- so at a commit no resource said what block 1     *)
(*  holds, and the collection's two superblock clauses ([FsDurSnap.sk_parse] *)
(*  and [sk_meta_used] at [FsImg.SB_BNO]) had no source.  This file is     *)
(*  that source: block 1's byte run, at FULL fraction, parked in an        *)
(*  invariant of its own beside the ONE local fact it can state -- that    *)
(*  its bytes parse to a superblock record.                                *)
(*                                                                        *)
(*  WHY FRACTION 1 AND NOT [DfracDiscarded].  [FsDurSnap.sk_meta_used]     *)
(*  says no inode owns a metadata block, and the collection reads that     *)
(*  off the separating conjunction: a full owner excludes ANY other share  *)
(*  ([FsBlocks.fsblock_ne_full]).  A persistent share does not -- a        *)
(*  read-locked inode holds 3/4 of its blocks and                          *)
(*  [DfracDiscarded ⋅ DfracOwn (3/4)] is perfectly valid -- so a           *)
(*  discarded copy would leave the clause unprovable at exactly the state  *)
(*  the design's quarter-share exists for.                                 *)
(*                                                                        *)
(*  WHY A FILE OF ITS OWN, AND WHY IT SITS BELOW [LogInv].  The handle     *)
(*  has to reach the COMMIT, and [SpecEndOp.wp_end_op] carries no file     *)
(*  system invariant at all: [LogInv.log_ctx] is the only persistent       *)
(*  bundle end_op holds, which is why the plan parks the collection's law  *)
(*  there.  So this predicate is a conjunct of [log_ctx] -- and [LogInv]   *)
(*  deliberately imports no pure well-formedness layer (see its header),   *)
(*  so the one pure reading block 1 needs lives here rather than there.    *)
(*                                                                        *)
(*  WHERE IT IS BORN.  The invariant cannot be allocated in the era fupd   *)
(*  beside [BitmapInv.bitmap_inv] or [InodeRegion.ireg_inv]: fsinit's own  *)
(*  [readsb] needs block 1's run in hand across a bread, so the run is out *)
(*  of every invariant until fsinit is past +0x26, while both of those     *)
(*  invariants exist before fsinit is called.  [initlog] is the first      *)
(*  point at which the run is free AND something end_op will hold is being *)
(*  built, so initlog allocates this invariant and seals it into           *)
(*  [log_ctx] ([ProofInitlog], the single site that builds one).           *)
(* ====================================================================== *)

From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.

Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import BioDefs.     (* [BSIZE] *)
Require Import FsBlocks.    (* [fs_names], [fsblock], [logN] *)
Require Import FsImg.       (* [fs_sb], [fs_parse_sb], [fs_sb_ok], [SB_BNO] *)
Require Export Xv6Cameras.

Local Open Scope Z_scope.

Section SbPark.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* A CHILD OF [FsBlocks.logN], AND THE SIBLING OF THE BYTE VIEW'S OWN
     [fsbN] (durable-disk lane E-blk1; the reasoning is written out at
     [FsBlocks.fsbN]).  Every FS-side byte accessor already carries
     [↑logN ⊆ E], so ONE premise now reaches both the byte view and block
     1's park -- which is what lets [log_write] refute a write at block 1
     inside its own atomic-update window, whose mask is the caller's [Efs]
     and about which its contract says only [↑logN ⊆ Efs].  Siblings and
     not nested: the commit holds the byte view open while the collection
     reads block 1. *)
  Definition sbN : namespace := logN .@ "sb".

  Lemma sbN_sub (E : coPset) : (↑logN : coPset) ⊆ E -> (↑sbN : coPset) ⊆ E.
  Proof.
    intros HE. etrans; [| exact HE]. rewrite /sbN. apply nclose_subseteq.
  Qed.

  (* THE BODY.  The bytes are existential -- nothing outside ever names
     them -- and the record they decode to is a PARAMETER, because that is
     the half a consumer needs: [FsState.sb_owned Γ sb bs] is exactly this
     pair read through [FsBytesGamma.gamma_blk_owned]. *)
  Definition sb_park_body (γfs : fs_names) (sb : fs_sb) : iProp Σ :=
    (∃ bs : list (bv 8),
       ⌜fs_parse_sb (fun _ => bs) = Some sb⌝ ∗
       fsblock (fs_bytes γfs) SB_BNO bs)%I.

  Global Instance sb_park_body_timeless γfs sb :
    Timeless (sb_park_body γfs sb).
  Proof. rewrite /sb_park_body. apply _. Qed.

  Definition sb_park (γfs : fs_names) (sb : fs_sb) : iProp Σ :=
    inv sbN (sb_park_body γfs sb).

  Global Instance sb_park_persistent γfs sb : Persistent (sb_park γfs sb).
  Proof. rewrite /sb_park. apply _. Qed.

  (* ...and the form a bundle with no [fs_sb] parameter can carry.  The
     record is closed over rather than threaded: [log_ctx]'s arity is fixed
     by the ~75 files that name it, and a consumer that needs to identify
     the record with the boot configuration's holds the concrete
     [sb_park] instead (fsinit and initlog both do). *)
  Definition sb_parked (γfs : fs_names) : iProp Σ :=
    (∃ sb : fs_sb, ⌜fs_sb_ok sb⌝ ∗ sb_park γfs sb)%I.

  Global Instance sb_parked_persistent γfs : Persistent (sb_parked γfs).
  Proof. rewrite /sb_parked. apply _. Qed.

  (* ---- birth ------------------------------------------------------- *)

  Lemma sb_park_alloc (E : coPset) (γfs : fs_names) (sb : fs_sb)
      (bs : list (bv 8)) :
    fs_parse_sb (fun _ => bs) = Some sb ->
    fsblock (fs_bytes γfs) SB_BNO bs ={E}=∗ sb_park γfs sb.
  Proof.
    intros Hparse. iIntros "Hb".
    iMod (inv_alloc sbN E (sb_park_body γfs sb) with "[Hb]") as "#Hi".
    { iNext. rewrite /sb_park_body. iExists bs.
      iSplitR; [iPureIntro; exact Hparse |]. iExact "Hb". }
    iModIntro. rewrite /sb_park. iExact "Hi".
  Qed.

  Lemma sb_parked_of_park (γfs : fs_names) (sb : fs_sb) :
    fs_sb_ok sb -> sb_park γfs sb -∗ sb_parked γfs.
  Proof.
    intros Hok. iIntros "#H". rewrite /sb_parked. iExists sb.
    iSplitR; [iPureIntro; exact Hok |]. iExact "H".
  Qed.

  (* ---- the accessor ------------------------------------------------ *)

  (* OPEN, READ, CLOSE.  Every conclusion the collection draws from block 1
     is read off the run while the invariant is open -- the parse is pure
     and the fraction is spent on nothing -- so the closing wand takes the
     very run it handed out.  This is the shape [FsCollect.col_hand]'s
     superblock leg wants; [FsCollectImg] states the same accessor in
     [FsState.sb_owned]'s vocabulary. *)
  Lemma sb_park_acc (E : coPset) (γfs : fs_names) (sb : fs_sb) :
    ↑sbN ⊆ E ->
    sb_park γfs sb ={E, E ∖ ↑sbN}=∗
      ∃ bs : list (bv 8),
        ⌜fs_parse_sb (fun _ => bs) = Some sb⌝ ∗
        fsblock (fs_bytes γfs) SB_BNO bs ∗
        (fsblock (fs_bytes γfs) SB_BNO bs ={E ∖ ↑sbN, E}=∗ True).
  Proof.
    intros HE. iIntros "#Hi".
    iMod (inv_acc E sbN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hbody".
    iDestruct "Hbody" as (bs) "[%Hparse Hb]".
    iModIntro. iExists bs. iSplitR; [iPureIntro; exact Hparse |].
    iFrame "Hb". iIntros "Hb".
    iMod ("Hclose" with "[Hb]") as "_".
    { iNext. rewrite /sb_park_body. iExists bs.
      iSplitR; [iPureIntro; exact Hparse |]. iExact "Hb". }
    by iModIntro.
  Qed.

  (* the byte view's own invariant is at [FsBlocks.fsbN]; block 1's park is
     its SIBLING under [logN], so a consumer may hold both open *)
  Lemma fsbN_sbN_disj : (↑fsbN : coPset) ## ↑sbN.
  Proof. solve_ndisj. Qed.

  (* ---- THE REFUTATION [log_write] READS (durable-disk lane E-blk1) ---- *)

  (* NOBODY CAN OWN A RUN INSIDE BLOCK 1, and that is what makes "the log's
     write set never names block 1" a maintained row of [LogInv.log_state]
     rather than a premise on twenty call sites.  [SpecLogWrite]'s
     byte-range atomic update hands the callee the caller's window at
     FRACTION 1; the park holds the whole block at fraction 1; two full
     owners of one byte are inconsistent.

     Stated at [↑logN ⊆ E] and not at [↑sbN ⊆ E] because that is the mask
     premise [log_write]'s contract already carries -- see [sbN] above.
     [FsCollectImg.log_ctx_sb_not_owned] is the same refutation at a WHOLE
     block, in the abstract byte view's vocabulary. *)
  Lemma sb_parked_bno_ne (E : coPset) (γfs : fs_names) (b : Z) (off : nat)
      (sub : list (bv 8)) :
    (↑logN : coPset) ⊆ E -> (off < BSIZE)%nat -> (0 < length sub)%nat ->
    sb_parked γfs -∗
    byte_range (fs_bytes γfs) b (Z.of_nat off) sub ={E}=∗
      ⌜b <> SB_BNO⌝ ∗ byte_range (fs_bytes γfs) b (Z.of_nat off) sub.
  Proof.
    intros HE Hoff Hpos. iIntros "#Hp Hr".
    rewrite /sb_parked. iDestruct "Hp" as (sb) "[%Hok #Hpark]".
    iMod (sb_park_acc E γfs sb (sbN_sub E HE) with "Hpark")
      as (bs) "(%Hparse & Hb & Hclose)".
    iDestruct (fsblock_byte_range_ne (fs_bytes γfs) SB_BNO b off bs sub
                 Hoff Hpos with "Hb Hr") as %Hne.
    iMod ("Hclose" with "Hb") as "_".
    iModIntro. iSplitR; [iPureIntro; exact (not_eq_sym Hne) |]. iExact "Hr".
  Qed.

End SbPark.

Global Typeclasses Opaque sb_park_body.
