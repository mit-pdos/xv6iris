(* ====================================================================== *)
(*  FsDurXferWall.v -- WHAT A SNAPSHOT'S RESOURCES DO NOT SAY, AND WHY THE *)
(*  COMMIT'S COLLECTION IS STILL NOT A TRANSPORT SOURCE                    *)
(*  (durable-disk lanes H2 / H3)                                          *)
(*                                                                        *)
(*  Lane H built the RESOURCE TRANSPORT ([FsDurXfer.fs_state_xfer]), lane  *)
(*  H2 moved the COMMIT so that the file system builds its own epoch, and  *)
(*  lane H3 gave the epoch an IDENTITY ([FsDurRead.snap_auth]: the byte    *)
(*  authority stands at a map inside [LogDefs.fs_dbytes D]) and turned     *)
(*  every CONTENT clause of [FsDurSnap.snap_ok] into a reading off the     *)
(*  epoch's own resources ([FsDurSnap.fs_snap_read_ok]).  Two facts about  *)
(*  the SHAPES are what is left; both are one-liners.                      *)
(*                                                                        *)
(*  (1)  THE GEOMETRY IS NOT READABLE, AND THAT IS A FACT ABOUT            *)
(*       [ghost_map], NOT A MISSING LEMMA.  An AUTHORITY may hold entries  *)
(*       no fragment names, so the identity -- which says the snapshot's   *)
(*       own bytes are INSIDE [fs_dbytes D] -- bounds nothing about [D]'s  *)
(*       domain.  Grow [D] by one whole block above the state's own        *)
(*       [size]: every resource of the epoch still holds                   *)
(*       ([fs_snap_res_grow], and the identity is monotone because the     *)
(*       flattening is), while [FsDurSnap.ss_dombelow] fails at that block *)
(*       ([snap_shape_grow_absurd]).  [snap_shape_not_readable] is the two *)
(*       together.                                                        *)
(*                                                                        *)
(*       So [FsDurSnap.snap_shape] -- block lengths, the map's range, the  *)
(*       superblock's own geometry, which inums the region names, and the  *)
(*       directory clauses at the region's width -- STAYS a carried pure   *)
(*       conjunct.  Every clause of it is a CONFIGURATION fact both        *)
(*       producers have for free ([FsCollect.col_geom] plus [col_hand]'s   *)
(*       domain and directory rows at a commit; the mkfs geometry at era   *)
(*       0), and none of it is about the file system's contents -- which   *)
(*       is why the expensive half, the byte ties and the used-set         *)
(*       coupling, no longer has to be materialised anywhere.              *)
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
(*       So a lane that wants the transport AT THE COMMIT has to           *)
(*       generalise it to a PER-OBJECT SHARE first (the disjointness       *)
(*       survives: [phi_excl] is fraction-aware and any two shares whose   *)
(*       doubles are invalid sum past one -- [FsCollect.dfrac_nvalid_pair] *)
(*       is that arithmetic, already in tree), and make the collection     *)
(*       ACCESSOR-shaped so the bundles go back to their invariants.  What *)
(*       it then owes [FsDurSnap.P_dur_alloc_xfer] is [snap_shape] and     *)
(*       nothing else, which [FsCollect.col_hand] already carries.         *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
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
Require Import FsDurBytes.     (* [dbytes_ok], [fs_dbytes_insert] *)
Require Import FsStateDefs.    (* [phi_excl], [phi_frac], [dfrac_full_nvalid] *)
Require Import FsState.        (* [fs_state], [top_frag] *)
Require Import FsDurXfer.      (* [snap_gamma] *)
Require Import FsDurRead.      (* [snap_auth] -- the epoch's IDENTITY *)
Require Import FsDurSnap.      (* [snap_ok], [snap_shape], [fs_snap] *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  A BLOCK ABOVE THE STATE'S OWN SIZE IS NOT A FILE-SYSTEM BLOCK      *)
(* ====================================================================== *)

Lemma snap_shape_grow_absurd (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (b : Z) (bs : list (bv 8)) :
  sb_size (fss_sb S) <= b ->
  snap_shape S (<[b := bs]> D) -> False.
Proof.
  intros Hb Hsh.
  assert (Hin : is_Some (<[b := bs]> D !! b))
    by (exists bs; apply lookup_insert).
  pose proof (ss_dombelow Hsh b Hin) as [_ Hlt]. lia.
Qed.

(* ...and the flattening is MONOTONE in the block map, which is the whole
   of (1): the identity is a subset and a subset bounds nothing above. *)
Lemma fs_dbytes_grow (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
  dbytes_ok (<[b := bs]> D) -> D !! b = None ->
  fs_dbytes D ⊆ fs_dbytes (<[b := bs]> D).
Proof.
  intros Hok Hb.
  rewrite (fs_dbytes_insert D b bs Hok Hb).
  apply map_union_subseteq_r.
  exact (fs_dbytes_disj_seq D b bs
           (dbytes_ok_insert D b bs Hb Hok)
           (dbytes_ok_head D b bs Hok) Hb).
Qed.

Section Wall.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* THE RESOURCE HALF of [FsDurSnap.fs_snap], verbatim minus the geometry *)
  Definition fs_snap_res Γ (g : gname) (B : gmap Z (bv 8))
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) : iProp Σ :=
    (snap_auth g B D
     ∗ ghost_map_auth (γtop Γ) 1 (fss_inodes S)
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag Γ i n)
     ∗ fs_state Γ S
     ∗ ∃ kv : ity, own (γlink Γ) (link_tok_elem ROOTINO kv))%I.

  Lemma fs_snap_split Γ g B D S :
    fs_snap Γ g B D S ⊣⊢ fs_snap_res Γ g B D S ∗ ⌜snap_shape S D⌝.
  Proof.
    rewrite /fs_snap /fs_snap_res. iSplit.
    - iIntros "(H1 & H2 & H3 & H4 & H5 & %Hsh)". iFrame. by iPureIntro.
    - iIntros "((H1 & H2 & H3 & H4 & H5) & %Hsh)". iFrame. by iPureIntro.
  Qed.

  (* ...and the resource half IS inhabited at the tied form, so the
     refutation below is not vacuous.  A witness at the real mkfs image is
     [FsAdequacyImg.fsimg_snap_ok] (not imported here: this file is a leaf
     and that one's cone is the whole boot chain). *)
  Lemma fs_snap_res_inhabited (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
    snap_ok S D ->
    ⊢ |==> ∃ g gl gt : gname,
        fs_snap_res (snap_gamma g gl gt) g (fs_dbytes D) D S.
  Proof.
    intros Hok.
    iMod (fs_snap_alloc S D Hok) as (g gl gt) "H".
    iModIntro. iExists g, gl, gt.
    rewrite fs_snap_split. iDestruct "H" as "[$ _]".
  Qed.

  (* THE IDENTITY IS MONOTONE IN [D]: nothing the epoch owns notices a
     block the footprint does not cover. *)
  Lemma fs_snap_res_grow Γ g B (D : gmap Z (list (bv 8)))
      (b : Z) (bs : list (bv 8)) S :
    dbytes_ok (<[b := bs]> D) -> D !! b = None ->
    fs_snap_res Γ g B D S ⊢ fs_snap_res Γ g B (<[b := bs]> D) S.
  Proof.
    intros Hok Hb. rewrite /fs_snap_res /snap_auth.
    iIntros "[Hau Hrest]". iDestruct "Hau" as "[Ha %Hsub]".
    iSplitR "Hrest"; [| iExact "Hrest"].
    iFrame "Ha". iPureIntro.
    exact (transitivity Hsub (fs_dbytes_grow D b bs Hok Hb)).
  Qed.

  (* (1), AS ONE LEMMA.  A reading of the GEOMETRY off the epoch's
     resources would survive growing [D] by a block above the state's own
     size, and no state fits that. *)
  Lemma snap_shape_not_readable Γ (g : gname) (B : gmap Z (bv 8))
      (D : gmap Z (list (bv 8))) (S : fs_state_rec)
      (b : Z) (bs : list (bv 8)) :
    dbytes_ok (<[b := bs]> D) -> D !! b = None ->
    sb_size (fss_sb S) <= b ->
    (forall D' : gmap Z (list (bv 8)),
       fs_snap_res Γ g B D' S ⊢ ⌜snap_shape S D'⌝) ->
    fs_snap_res Γ g B D S ⊢ ⌜False⌝.
  Proof.
    intros Hok Hb Hsz Hread. iIntros "H".
    rewrite (fs_snap_res_grow Γ g B D b bs S Hok Hb).
    iDestruct (Hread (<[b := bs]> D) with "H") as %Hsh.
    iPureIntro. exact (snap_shape_grow_absurd S D b bs Hsz Hsh).
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
