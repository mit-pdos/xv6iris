(* ====================================================================== *)
(*  FsInitPinBoot.v -- THE ERA-0 TRANSPORT: THE BOOT'S OWN MAP IS [era0_D] *)
(*  (fs-syscall-specs lane P's recorded GAP (1), closed)                   *)
(* ====================================================================== *)

(*  WHAT THIS FILE IS.  [FsInitPin.v] proved the two era-0 /init pins as
    facts about a FIXED map -- [era0_D], the literal mkfs image's committed
    home blocks -- quantified over EVERY abstract state [S] with
    [FsDurSnap.snap_ok S era0_D].  What it could not say, and recorded as
    its one gap, is that the map a BOOT actually founds its file system at
    is that map: at [BootShared.boot_shared_alloc]'s altitude the era's
    state [S], its block view [Pb], its superblock and its coverage all
    arrive as ERA-GENERIC PARAMETERS, and nothing in the bundle says which
    era this is.

    THIS FILE SUPPLIES THE MISSING IDENTIFICATION, and nothing else.  It
    adds NO new statement to the boot chain, moves nothing (R10), and is
    required by no file: like [FsInitPin] it is a LEAF, and its import cone
    is [FsInitPin]'s own -- every module named below is one [FsInitPin]
    already requires, so no cone anywhere grows.  (That is also the reason
    it is a SEPARATE file rather than an appendix to [FsInitPin]: nothing
    forced the split by hygiene, so the split is made on ALTITUDE --
    [FsInitPin] is a fact about a gmap and computes the image, this is a
    fact about a BOOT's premises and computes nothing -- and it keeps
    [FsInitPin]'s landed text and its empty [Print Assumptions] untouched.)

    THE ERA-0 PREMISE, in its exact landed spelling.  There is no era
    COUNTER at the boot altitude and there deliberately cannot be one:
    [SystemAdequacy.xv6_boot_era] is applied at every power-on and knows
    only what [FsCrash.P_fs_project] tells it about the disk it is booting
    on.  What distinguishes era 0 is therefore an equation about the DISK,
    and it is the one hypothesis [SystemAdequacy.xv6_power_adequacy_xv6Σ]
    takes:

        Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk

    read at the block view the file system works in, i.e.

        FsCrash.fs_blocks dk = FsImgDisk.fsimg_P

    ([fsimg_P] IS [fs_blocks fsimg_dk] by definition, FsImgDisk.v:75).
    Together with [SystemAdequacy]'s own [fsimg_cov] this pins the two
    parameters the crash predicate fixes for the whole execution.  The
    remaining parameter, the log start, is NOT assumed: it is read off the
    era's own snapshot ([FsDurSnap.sk_sbok] -> [FsImg.sbo_logstart] pins it
    at 2) and off the image's superblock ([FsImgCheck.fsimg_sb_logstart]
    checks the same 2), which is exactly how [xv6_boot_era]'s [Hlseq]
    reconciles them.

    THE TWO ROUTES, and both are here because the boot uses both.
      (A) THE MINT'S BUNDLE, [FsCfgBoot.fs_boot_snap_wf] -- literally the
          premise [BootShared.boot_shared_alloc] takes.  Its conjunct (3)
          is [snap_ok S (fs_restrict Pb (fs_home_set cov (sb_logstart sb)))],
          and section 2 shows THAT MAP IS [era0_D].  The step is conjunct
          (6) -- [Pb] agrees with the raw disk off the header's write set --
          plus the fact that at the image the write set is EMPTY, because
          mkfs leaves a clean log ([FsImgCheck.fsimg_wf_log_clean]).
      (B) THE CRASH PREDICATE'S EPOCH, [FsCrash.fs_recovery] -- the route
          [xv6_boot_era] takes to get the epoch in the first place, where
          [FsCrash.fs_recovery_det] pins the lent epoch's map to the
          projection's.  Section 3 shows that at an era-0 disk that common
          map is [era0_D], by [FsCrash.fs_recovery_clean] at the same clean
          log.  Route (B) is also what makes the CRASH-BEFORE-/init
          corollary free (section 3b).

    WHAT IS NOT CLAIMED.  Nothing here says the disk is still the image at
    any later era -- that is refutable, and durable-disk lane E-himg
    deleted the statement that used to say it.  Every sentence below is
    hedged behind the era-0 disk equation, which is a hypothesis about the
    machine the system is SWITCHED ON with and about nothing else.        *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.

(* [FsInitPin.v]'s import block, VERBATIM and in its order (the ghost
   classes first, so the file-system stack's names win over the block
   layer's twins -- durable-notes.md), with [FsInitPin] itself appended
   after [FsAbs].  Every module here is already on [FsInitPin]'s cone. *)
Require Import Xv6Cameras.
Require Import FsState.
Require Import BioDefs.
Require Import DinodeEnc.
Require Import DirView.
Require Import InodeInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import FsStateEra.
Require Import FsCrash.        (* [fs_recovery], [fs_recovery_det],
                                  [fs_recovery_clean], [hdr_wset],
                                  [fs_blocks]; re-exports [LogDefs]     *)
Require Import FsDurSnap.      (* [snap_ok], [sk_bytes], [sk_sbok],
                                  [fs_snap], [fs_snap_read_ok_keep]     *)
Require Import FsDurSyscall.
Require Import FsCfgBoot.      (* [fs_boot_snap_wf] -- the mint's bundle *)
Require Import FsDurImg.
Require Import SystemAdequacy. (* [fsimg_cov], [fsimg_nib]              *)
Require Import FsImgDisk.      (* [fsimg_P] = [fs_blocks fsimg_dk]      *)
Require Import FsImgCheck.     (* [fsimg_sb], [fsimg_wf_log_clean],
                                  [fsimg_sb_logstart]                   *)
Require Import FsImg.
Require Import FsAbs.          (* LAST (FsAbs's own rule)               *)
Require Import FsInitPin.      (* [era0_D], [INIT_INO], [init_path],
                                  [init_bytes] and the three pins       *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE PINS, AS ONE NAME                                              *)
(*                                                                        *)
(*  [FsInitPin]'s three era-0 conclusions, packaged so that every          *)
(*  transport below states them once.  IT IS A [Prop] ABOUT A VIEW and     *)
(*  nothing else: no ghost, no state, no map -- which is what lets the     *)
(*  resource forms of section 4 hand it out without spending anything.     *)
(* ====================================================================== *)

Definition era0_pins (av : aview) : Prop :=
  (* the PATH pin: "/init" resolves, in the root, to inum 7 *)
  apath_at av FsImg.ROOTINO init_path = Some INIT_INO
  (* the CONTENT pin: inum 7 holds [init_elf]'s bytes, at nlink 1 *)
  /\ av !! INIT_INO = Some (MkAnode (AFile init_bytes) 1%nat)
  (* ...and the WALK, which is exactly the [arun] premise
     [FsAbsPins.apr_walk] takes *)
  /\ arun av FsImg.ROOTINO init_path [FsImg.ROOTINO; INIT_INO].

(* the one composition point with [FsInitPin]: everything below reduces to
   producing this lemma's premise at the boot's own state *)
Lemma era0_pins_of_snap (S : fs_state_rec) :
  snap_ok S era0_D -> era0_pins (abs_view (fss_inodes S)).
Proof.
  intros HS. split; [exact (era0_init_path_pin S HS) |].
  split; [exact (era0_init_content_pin S HS) | exact (era0_init_arun S HS)].
Qed.

(* ====================================================================== *)
(*  2.  ROUTE (A): THE MINT'S OWN BUNDLE                                   *)
(* ====================================================================== *)

(* ---- 2a.  mkfs LEAVES A CLEAN LOG, so the header names no pending home
   block.  This is the whole of what makes the era's block view [Pb] equal
   to the raw disk on the home set: conjunct (6) of [fs_boot_snap_wf] is
   hedged behind [b ∉ hdr_wset], and at era 0 that set is empty. *)
Lemma era0_hdr_wset :
  hdr_wset fsimg_P (FsImg.sb_logstart fsimg_sb) = ∅.
Proof.
  rewrite /hdr_wset (hdr_dec_zero _ fsimg_wf_log_clean).
  cbn [snd]. reflexivity.
Qed.

(* ---- 2b.  THE ERA'S LOG START IS THE IMAGE'S.  Not assumed: the left
   side is read off the boot's own snapshot ([sk_sbok] -> [sbo_logstart],
   which pins it at 2) and the right side is checked at the image's
   superblock ([fsimg_sb_logstart], the same 2).  This is
   [SystemAdequacy.xv6_boot_era]'s [Hlseq], stated where the transport
   needs it. *)
Lemma era0_logstart (dk : Z -> bv 8) (ndisk : nat) (S : fs_state_rec)
    (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (cov : gset Z) :
  fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
  FsImg.sb_logstart sb = FsImg.sb_logstart fsimg_sb.
Proof.
  intros (Hsbeq & _ & Hsnok & _).
  rewrite Hsbeq (FsImg.sbo_logstart _ (sk_sbok (sk_bytes Hsnok))).
  rewrite fsimg_sb_logstart. reflexivity.
Qed.

(* ---- 2c.  THE IDENTIFICATION -- lane P's gap (1), route (A).
   THE MAP THE BOOT MINT FOUNDS THE ERA'S FILE SYSTEM AT *IS* [era0_D]. *)
Theorem era0_boot_map (dk : Z -> bv 8) (ndisk : nat) (S : fs_state_rec)
    (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (cov : gset Z) :
  fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
  (* THE ERA-0 PREMISE: this era's disk is the one mkfs wrote *)
  fs_blocks dk = fsimg_P ->
  cov = fsimg_cov ->
  fs_restrict Pb (fs_home_set cov (FsImg.sb_logstart sb)) = era0_D.
Proof.
  intros Hb Hdk Hcov.
  pose proof (era0_logstart dk ndisk S Pb sb nib cov Hb) as Hls.
  destruct Hb as (_ & _ & _ & _ & _ & Hagr & _).
  subst cov. rewrite Hls in Hagr. rewrite Hdk in Hagr. rewrite Hls.
  (* [fs_restrict_ext] is the congruence: two views that agree ON THE SET
     restrict to the same map.  Agreement is conjunct (6) with its side
     condition discharged by the empty write set. *)
  rewrite /era0_D. apply fs_restrict_ext. intros b Hb.
  apply (Hagr b Hb). rewrite era0_hdr_wset. exact (not_elem_of_empty b).
Qed.

(* ...hence the boot's own state satisfies [FsInitPin]'s premise... *)
Theorem era0_boot_snap_ok (dk : Z -> bv 8) (ndisk : nat) (S : fs_state_rec)
    (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (cov : gset Z) :
  fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
  fs_blocks dk = fsimg_P ->
  cov = fsimg_cov ->
  snap_ok S era0_D.
Proof.
  intros Hb Hdk Hcov.
  pose proof (era0_boot_map dk ndisk S Pb sb nib cov Hb Hdk Hcov) as Hmap.
  destruct Hb as (_ & _ & Hsnok & _). rewrite Hmap in Hsnok. exact Hsnok.
Qed.

(* ...AND THE THREE PINS HOLD OF THE VIEW THE ERA BOOTS WITH.
   [FsCfgSnap.fs_cfg_alloc_snap] founds [γtop] at [fss_inodes S], so
   [abs_view (fss_inodes S)] is the founded [FsAbs.astate]'s view on the
   nose ([FsInitPin]'s §"WHY THE SNAPSHOT STATE IS THE RIGHT PLACE"). *)
Theorem era0_boot_pins (dk : Z -> bv 8) (ndisk : nat) (S : fs_state_rec)
    (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (cov : gset Z) :
  fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
  fs_blocks dk = fsimg_P ->
  cov = fsimg_cov ->
  era0_pins (abs_view (fss_inodes S)).
Proof.
  intros Hb Hdk Hcov.
  exact (era0_pins_of_snap S
           (era0_boot_snap_ok dk ndisk S Pb sb nib cov Hb Hdk Hcov)).
Qed.

(* ====================================================================== *)
(*  3.  ROUTE (B): THE CRASH PREDICATE'S EPOCH                             *)
(*                                                                        *)
(*  [SystemAdequacy.xv6_boot_era] does not start from the bundle: it       *)
(*  starts from [FsCrash.P_fs_lend]'s epoch, whose committed map it pins   *)
(*  to its own projection's with [FsCrash.fs_recovery_det], and only then  *)
(*  builds the bundle.  So the identification is ALSO wanted one rung      *)
(*  earlier, at the recovery relation, where it is cheaper: recovery is a  *)
(*  FUNCTION of the physical disk, and at a clean log that function is the *)
(*  restriction to the home blocks.                                       *)
(* ====================================================================== *)

Theorem era0_recovery_D (D : gmap Z (list (bv 8))) :
  fs_recovery fsimg_P D fsimg_cov (FsImg.sb_logstart fsimg_sb) -> D = era0_D.
Proof.
  exact (proj1 (fs_recovery_clean fsimg_P D fsimg_cov
                  (FsImg.sb_logstart fsimg_sb) fsimg_wf_log_clean)).
Qed.

(* ...and the converse, so [era0_D] is not merely SOME map an era-0 boot
   might recover to: it is the one it does. *)
Lemma era0_recovery (dk : Z -> bv 8) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) era0_D fsimg_cov (FsImg.sb_logstart fsimg_sb).
Proof.
  intros Hdk. rewrite Hdk.
  apply (proj2 (fs_recovery_clean fsimg_P era0_D fsimg_cov
                  (FsImg.sb_logstart fsimg_sb) fsimg_wf_log_clean)).
  reflexivity.
Qed.

(* THE LENT EPOCH'S MAP, at era 0.  This is [xv6_boot_era]'s own two-line
   move -- [fs_recovery_det] on the lend's [D0] and the projection's [D] --
   with the era-0 disk equation added, which is what turns the pinned map
   into a NAMED one. *)
Theorem era0_lend_D (dk : Z -> bv 8) (D0 D : gmap Z (list (bv 8))) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D0 fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  fs_recovery (fs_blocks dk) D  fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  D0 = D /\ D0 = era0_D.
Proof.
  intros Hdk Hrec0 Hrec. split.
  - exact (fs_recovery_det _ _ _ _ _ Hrec0 Hrec).
  - apply era0_recovery_D. rewrite -Hdk. exact Hrec0.
Qed.

(* ...and the pins, off the epoch's own state.  [snap_ok S D] is what
   [FsDurSnap.fs_snap_read_ok_keep] reads off the lent epoch
   NON-DESTRUCTIVELY (BT-3's producer), so this is the form
   [xv6_boot_era]'s [Hsnok] arrives in. *)
Theorem era0_recovery_pins (dk : Z -> bv 8) (D : gmap Z (list (bv 8)))
    (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D ->
  era0_pins (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec HS. apply era0_pins_of_snap.
  assert (HD : D = era0_D).
  { apply era0_recovery_D. rewrite -Hdk. exact Hrec. }
  rewrite -HD. exact HS.
Qed.

(* ---------------------------------------------------------------------- *)
(*  3b.  THE CRASH-BEFORE-/init COROLLARY -- and it costs nothing.         *)
(*                                                                        *)
(*  ERA 0 CRASHES AND RECOVERS BEFORE /init EVER RUNS is not a statement   *)
(*  about an era COUNTER: [fs_recovery] is a function of the PHYSICAL DISK *)
(*  alone, so NOTHING COMMITTED is spelled exactly as THE DISK STILL       *)
(*  CARRIES THE IMAGE'S BYTES -- which is this file's era-0 premise, at    *)
(*  the RE-boot's disk.  [fs_recovery_det] then says the re-founding map   *)
(*  is the SAME map, and the pins are the same pins.                       *)
(*                                                                        *)
(*  WHAT IT DOES NOT DRAG IN: no part of the recovery cone beyond the      *)
(*  relation itself.  The WAL's crash argument, the permits and the        *)
(*  mirror are what PROVE that an uncommitted era leaves the durable       *)
(*  extent alone; this corollary consumes that conclusion as its           *)
(*  hypothesis [Hdk'] and proves what follows from it, which is all lane P *)
(*  asked for.                                                            *)
(* ---------------------------------------------------------------------- *)
Corollary era0_reboot_pins (dk dk' : Z -> bv 8)
    (D D' : gmap Z (list (bv 8))) (S : fs_state_rec) :
  (* era 0's own founding disk and map... *)
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  (* ...the disk the RE-boot finds, nothing having been committed... *)
  fs_blocks dk' = fs_blocks dk ->
  fs_recovery (fs_blocks dk') D' fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  (* ...and the state the re-boot's own epoch stands at *)
  snap_ok S D' ->
  D' = D /\ D' = era0_D /\ era0_pins (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec Hdk' Hrec' HS'.
  rewrite Hdk' in Hrec'.
  destruct (era0_lend_D dk D' D Hdk Hrec' Hrec) as [Heq Hera].
  split; [exact Heq |]. split; [exact Hera |].
  exact (era0_recovery_pins dk D' S Hdk Hrec' HS').
Qed.

(* ====================================================================== *)
(*  4.  THE RESOURCE FORMS                                                 *)
(*                                                                        *)
(*  Lane P's report called the live corollary "one lemma away"; these are  *)
(*  the two lemmas, at the two resources a boot-time consumer can be       *)
(*  holding.  BOTH ARE NON-DESTRUCTIVE: the conclusion is pure, so the     *)
(*  authority (or the snapshot) is handed straight back and nothing is     *)
(*  spent.                                                                *)
(* ====================================================================== *)

(* ---- 4a.  AT THE EPOCH ITSELF, which is what [BootShared]'s caller has
   in hand before the mint runs ([xv6_boot_era] unpacks [P_dur] into
   exactly this).  The premise [dblk_full era0_D] is discharged here, not
   assumed: every block of a whole-disk image is [BSIZE] bytes. *)
Lemma era0_dblk_full : FsDurRead.dblk_full era0_D.
Proof.
  intros b bs Hbs. rewrite /era0_D in Hbs.
  apply fs_restrict_lookup_Some in Hbs as [_ ->].
  exact (fsimg_blocks_full b).
Qed.

Section Era0Epoch.
  (* [FsDurSnap.v]'s own [Section Snap] binder list, verbatim. *)
  Context `{!DiskImg.diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  (* THE PINS OFF THE LENT EPOCH, snapshot handed back.  This is
     [fs_snap_read_ok_keep] -- BT-3's non-destructive producer -- composed
     with section 1, at the era-0 map. *)
  Lemma fs_snap_era0_pins (g gl gt : gname) (S : fs_state_rec) :
    fs_snap (FsDurBytes.snap_gamma g gl gt) g era0_D S -∗
      ⌜era0_pins (abs_view (fss_inodes S))⌝
      ∗ fs_snap (FsDurBytes.snap_gamma g gl gt) g era0_D S.
  Proof.
    iIntros "H".
    iDestruct (fs_snap_read_ok_keep _ _ _ _ _ era0_dblk_full with "H")
      as "[%Hok H]".
    iFrame "H". iPureIntro. exact (era0_pins_of_snap S Hok).
  Qed.
End Era0Epoch.

(* ---- 4b.  AT THE FOUNDED AUTHORITY, which is what a consumer INSIDE the
   era holds ([ProofForkret]'s pinned-kexec gate, per lane P's consumer
   map).  These are [FsInitPin]'s section 6 with its [snap_ok] premise
   replaced by the boot's own bundle, so the consumer owes only the era-0
   disk equation. *)
Section Era0Live.
  (* [FsAbs.v]'s own binder list, verbatim. *)
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  Lemma astate_era0_boot_pins Γ (dk : Z -> bv 8) (ndisk : nat)
      (S : fs_state_rec) (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
      (cov : gset Z) :
    fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
    fs_blocks dk = fsimg_P ->
    cov = fsimg_cov ->
    astate Γ (abs_view (fss_inodes S)) -∗
      astate Γ (abs_view (fss_inodes S))
      ∗ ⌜era0_pins (abs_view (fss_inodes S))⌝.
  Proof.
    intros Hb Hdk Hcov. iIntros "Hst". iFrame "Hst". iPureIntro.
    exact (era0_boot_pins dk ndisk S Pb sb nib cov Hb Hdk Hcov).
  Qed.

  (* ...and the content pin as an AGREEMENT: a client-held share of inum 7
     IS /init's bytes.  [Some_inj], never [injection] -- [FsInitPin]'s §3
     performance rule (the row carries the 35,976-byte literal). *)
  Lemma nview_era0_boot_init Γ (dk : Z -> bv 8) (ndisk : nat)
      (S : fs_state_rec) (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
      (cov : gset Z) (q : Qp) (a : anode) :
    fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
    fs_blocks dk = fsimg_P ->
    cov = fsimg_cov ->
    astate Γ (abs_view (fss_inodes S)) -∗ nview Γ q INIT_INO a -∗
      ⌜a = MkAnode (AFile init_bytes) 1%nat⌝.
  Proof.
    intros Hb Hdk Hcov. iIntros "Hst Hn".
    iApply (nview_era0_init Γ S q a
              (era0_boot_snap_ok dk ndisk S Pb sb nib cov Hb Hdk Hcov)
              with "Hst Hn").
  Qed.
End Era0Live.
