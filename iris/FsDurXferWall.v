(* ====================================================================== *)
(*  FsDurXferWall.v -- WHY THE COMMIT'S SNAPSHOT IS STILL BUILT FROM A     *)
(*  VALUE, AND WHAT WOULD HAVE TO CHANGE FIRST (durable-disk lane H2)      *)
(*                                                                        *)
(*  Lane H built the RESOURCE TRANSPORT ([FsDurXfer.fs_state_xfer]) and    *)
(*  its registry entry points ([FsDurSnap.fs_snap_alloc_xfer],             *)
(*  [P_dur_alloc_xfer]), and lane H2 moved the COMMIT so that the file     *)
(*  system builds its own epoch at its own ghost step and the WAL only     *)
(*  installs it ([LogSnapLaw.snap_law_out], [FsDurSnap.dsnap_step_xfer]).  *)
(*  What lane H2 did NOT do is make that epoch come out of the TRANSPORT   *)
(*  rather than out of [P_dur_alloc], and it did not shrink [snap_ok].     *)
(*  Two facts below are why; both are one-liners, and both are about the   *)
(*  SHAPES, not about any proof.                                          *)
(*                                                                        *)
(*  (1)  THE EXPORTED CLAIM CANNOT BE READ OFF THE SNAPSHOT'S RESOURCES.   *)
(*       [FsDurSnap.fs_snap Gamma g B D S] mentions the committed block    *)
(*       map [D] in EXACTLY ONE PLACE -- the pure conjunct                 *)
(*       [<pure snap_ok S D>].  Everything else (the byte authority at     *)
(*       [B], the abstract map's authority and fragments, [fs_state])      *)
(*       is a function of [S] alone.  So a "reading lemma" that recovers   *)
(*       [snap_ok S D] from the resources would have to hold at EVERY [D], *)
(*       including the empty map -- and [snap_ok S empty] is false         *)
(*       ([sk_sb] wants block [SB_BNO]).  [snap_ok_not_readable] below.    *)
(*                                                                        *)
(*       The root cause is not a missing lemma: [D] is a VALUE the WAL     *)
(*       computes from its own cache map, and relating a value to a        *)
(*       resource is a pure statement by construction.  Making the tie     *)
(*       derivable means giving [P_dur] a resource that PINS [D] -- a      *)
(*       ledger of all of [D]'s bytes -- and the snapshot cannot own that  *)
(*       beside [fs_state Gamma S] at full fraction (they would overlap on *)
(*       every block [S] names, which [phi_excl] refutes).  So [snap_ok]   *)
(*       stays a carried tie, and every clause the theorem exports         *)
(*       ([SystemAdequacy.fs_boot_pure]) has to be MATERIALISED at each    *)
(*       commit -- which is what [FsCollect.col_snap_ok_ex] does.          *)
(*                                                                        *)
(*  (2)  THE COMMIT'S COLLECTION IS NOT A LEGAL TRANSPORT SOURCE.          *)
(*       [FsDurXfer.fs_state_xfer] takes [fs_state Gamma S], whose byte    *)
(*       legs are [DfracOwn 1].  What quiescence yields is                 *)
(*       [FsCollect.col_bundle], whose share is EXISTENTIAL and whose only *)
(*       constraint is "the double is invalid" -- because a READ-LOCKED    *)
(*       inode has handed a quarter to its reader and the escrow keeps     *)
(*       three quarters (plan section 4).  [DfracOwn (3/4)] satisfies that *)
(*       constraint ([dfrac_34_no_pair]) and cannot be promoted to the     *)
(*       full element ([phi_no_promote]): assuming the promotion, split    *)
(*       the full element as 3/4 + 1/4, promote the 3/4 again, and the     *)
(*       two owners at one address are inconsistent.                      *)
(*                                                                        *)
(*       So a future lane that wants the transport at the commit has to    *)
(*       generalise it to a PER-OBJECT SHARE first (the disjointness       *)
(*       survives: [phi_excl] is fraction-aware and any two shares whose   *)
(*       doubles are invalid sum past one -- [FsCollect.dfrac_nvalid_pair] *)
(*       is that arithmetic, already in tree).  Even then it buys nothing  *)
(*       on its own while (1) stands: [fs_snap_alloc_xfer] takes           *)
(*       [snap_ok S D] as a premise BESIDE the instance, so at the commit  *)
(*       the transport is a strictly larger obligation than                *)
(*       [P_dur_alloc].  (1) is the one to fix first.                     *)
(* ====================================================================== *)

From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list sets bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_map.

Require Import BioDefs.
Require Import DiskImg.       (* [diskImgG] -- IMPORTED, not merely required:
                                 a capacity class named through a transitive
                                 Require is inert (durable-notes) *)
Require Import LogDefs.        (* [fs_dbytes] *)
Require Import FsImg.          (* [SB_BNO] *)
Require Import FsStateDefs.    (* [phi_excl], [phi_frac], [dfrac_full_nvalid] *)
Require Import FsState.        (* [fs_state], [top_frag] *)
Require Import FsDurXfer.      (* [snap_gamma] *)
Require Import FsDurSnap.      (* [snap_ok], [fs_snap], [fs_snap_alloc] *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE EMPTY COMMITTED MAP IS NOT A FILE SYSTEM                       *)
(* ====================================================================== *)

Lemma snap_ok_empty_absurd (S : fs_state_rec) : snap_ok S ∅ -> False.
Proof.
  intros H. pose proof (sk_sb (sk_bytes H)) as Hsb.
  rewrite lookup_empty in Hsb. discriminate.
Qed.

Section Wall.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* THE RESOURCE HALF of [FsDurSnap.fs_snap], verbatim minus the pure tie.
     [D] does not occur in it -- that is the whole content of (1). *)
  Definition fs_snap_res Γ (g : gname) (B : gmap Z (bv 8))
      (S : fs_state_rec) : iProp Σ :=
    (ghost_map_auth g 1 B
     ∗ ghost_map_auth (γtop Γ) 1 (fss_inodes S)
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag Γ i n)
     ∗ fs_state Γ S)%I.

  Lemma fs_snap_split Γ g B D S :
    fs_snap Γ g B D S ⊣⊢ fs_snap_res Γ g B S ∗ ⌜snap_ok S D⌝.
  Proof.
    rewrite /fs_snap /fs_snap_res. iSplit.
    - iIntros "(H1 & H2 & H3 & H4 & %Hok)". iFrame. by iPureIntro.
    - iIntros "((H1 & H2 & H3 & H4) & %Hok)". iFrame. by iPureIntro.
  Qed.

  (* ...and the resource half IS inhabited, so the refutation below is not
     vacuous.  A witness at the real mkfs image is
     [FsAdequacyImg.fsimg_snap_ok] (not imported here: this file is a leaf
     and that one's cone is the whole boot chain). *)
  Lemma fs_snap_res_inhabited (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
    snap_ok S D ->
    ⊢ |==> ∃ g gl gt : gname,
        fs_snap_res (snap_gamma g gl gt) g (fs_dbytes D) S.
  Proof.
    intros Hok.
    iMod (fs_snap_alloc S D Hok) as (g gl gt) "(Hba & Hta & Htf & Hst)".
    iModIntro. iExists g, gl, gt. rewrite /fs_snap_res. iFrame.
  Qed.

  (* (1), AS ONE LEMMA.  A reading of the exported tie off the snapshot's
     resources would hold at every [D]; it therefore holds at the empty map,
     which no state fits. *)
  Lemma snap_ok_not_readable Γ (g : gname) (B : gmap Z (bv 8))
      (S : fs_state_rec) :
    (forall D : gmap Z (list (bv 8)), fs_snap_res Γ g B S ⊢ ⌜snap_ok S D⌝) ->
    fs_snap_res Γ g B S ⊢ ⌜False⌝.
  Proof.
    intros Hread. iIntros "H".
    iDestruct (Hread ∅ with "H") as %Hok.
    iPureIntro. exact (snap_ok_empty_absurd S Hok).
  Qed.

  (* ==================================================================== *)
  (*  2.  A THREE-QUARTER RUN IS AN ADMISSIBLE BUNDLE SHARE AND IS NOT     *)
  (*      A FULL ONE                                                       *)
  (* ==================================================================== *)

  (* [FsCollect.col_bundle]'s only constraint on its share *)
  Lemma dfrac_34_no_pair : ~ ✓ (DfracOwn (3/4) ⋅ DfracOwn (3/4)).
  Proof.
    intros Hv. rewrite dfrac_op_own dfrac_valid_own in Hv.
    by compute in Hv.
  Qed.

  (* ...and it cannot become the element [fs_state] wants *)
  Lemma phi_no_promote Γ (Hex : phi_excl Γ) (Hfr : phi_frac Γ)
      (a : Z) (v : bv 8) :
    (fsΦ Γ (DfracOwn (3/4)) a v ⊢ fsΦ Γ (DfracOwn 1) a v) ->
    fsΦ Γ (DfracOwn (3/4)) a v ⊢ ⌜False⌝.
  Proof.
    intros Hpr. iIntros "H".
    iDestruct (Hpr with "H") as "H".
    rewrite -Qp.three_quarter_quarter (Hfr a v (3/4)%Qp (1/4)%Qp).
    iDestruct "H" as "[H1 H2]".
    iDestruct (Hpr with "H1") as "H1".
    iDestruct (Hex a v v (DfracOwn 1) (DfracOwn (1/4)) with "[$H1 $H2]")
      as %Hv.
    iPureIntro. exact (dfrac_full_nvalid (DfracOwn (1/4)) Hv).
  Qed.

End Wall.
