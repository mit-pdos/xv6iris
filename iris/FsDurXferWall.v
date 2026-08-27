(* ====================================================================== *)
(*  FsDurXferWall.v -- WHAT A SNAPSHOT'S RESOURCES DO NOT SAY, AND WHY THE *)
(*  COMMIT'S COLLECTION IS STILL NOT A TRANSPORT SOURCE                    *)
(*  (durable-disk lanes H2 / H3 / H4)                                     *)
(*                                                                        *)
(*  Lane H built the RESOURCE TRANSPORT ([FsDurXfer.fs_state_xfer]), lane  *)
(*  H2 moved the COMMIT so that the file system builds its own epoch, and  *)
(*  lane H3 gave the epoch an IDENTITY ([FsDurRead.snap_auth]: the byte    *)
(*  authority stands at a map inside [LogDefs.fs_dbytes D]) and turned     *)
(*  every CONTENT clause of [FsDurSnap.snap_ok] into a reading off the     *)
(*  epoch's own resources ([FsDurSnap.fs_snap_read_ok]).  Two facts about  *)
(*  the SHAPES are what is left; both are one-liners.                      *)
(*                                                                        *)
(*  (1)  THE GEOMETRY IS NOT READABLE, AND STRENGTHENING THE IDENTITY TO   *)
(*       AN EQUALITY DOES NOT CHANGE THAT (lane H4).  The reason is one    *)
(*       fact about the FLATTENING: [LogDefs.fs_dbytes] is BLIND to a      *)
(*       block whose byte list is empty, so it is not injective, and       *)
(*       "the snapshot's own map IS the flattening of [D]" therefore       *)
(*       determines nothing about [D] at such a block.  Pad [D] with       *)
(*       [b := []]: the flattening is UNCHANGED ([fs_dbytes_pad]), so      *)
(*       every resource of the epoch holds at the padded map AT THE        *)
(*       EQUALITY FORM TOO -- [fs_snap_res_eq_pad] is an [⊣⊢], not the     *)
(*       one-way growth H3 had to use -- while [FsDurSnap.ss_bsz] fails    *)
(*       at [b] ([snap_shape_pad_absurd]).                                *)
(*       [snap_shape_not_readable_eq] is the two together, at the          *)
(*       EQUALITY identity; [snap_shape_not_readable] is H3's, at the      *)
(*       [⊆] one.  Neither is a missing lemma.                            *)
(*                                                                        *)
(*       AND THE EQUALITY IS NOT PROVABLE AT THE COMMIT EITHER, for a      *)
(*       reason that is about xv6 and not about ghost state: nothing in    *)
(*       the design says a block whose bitmap bit is SET belongs to some   *)
(*       inode.  [FsDurSnap.sk_own_used] and [sk_meta_used] are both the   *)
(*       "owned or metadata => used" direction; the converse is stated     *)
(*       nowhere, and it is FALSE of this kernel (a crash between          *)
(*       [balloc]'s bit and the record that names the block leaks it).     *)
(*       [FsState.fs_footprint] owns block 1, the bitmap block, the        *)
(*       region, every node's own blocks and the FREE pool -- a leaked     *)
(*       block is in none of those, and it is a block of [D] all the       *)
(*       same.  So the footprint's flattening is a PROPER subset of        *)
(*       [fs_dbytes D] in general, which is why the identity is stated at  *)
(*       [⊆] and why the transport can only ever produce [⊆].             *)
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
(*  (2)  THE COMMIT'S COLLECTION IS NOT AN [fs_state], AND DOES NOT NEED   *)
(*       TO BE.                                                            *)
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
(*       BOTH FACTS STAND AND NEITHER IS AN OBSTACLE ANY MORE (lane H4).   *)
(*       The commit's source was never going to be an [fs_state]: its      *)
(*       records sit REGION-side at fraction 1 while its data legs are at  *)
(*       each inode's own share.  So the commit hands the mint the RUNS    *)
(*       instead ([FsDurXfer.phi_runs_ex], one share per run,              *)
(*       existentially bound per object), reads their disjointness off     *)
(*       [phi_excl] at MIXED shares ([dfrac_nvalid_pair], which moved to   *)
(*       [FsDurXfer] for exactly this) and their union's place inside the  *)
(*       era's map off [phi_agree], and calls                              *)
(*       [FsDurSnap.P_dur_alloc_mint] -- whose premise is a package of     *)
(*       READINGS and no resource at all, which is why the collection      *)
(*       never had to become ACCESSOR-shaped and [FsCollectAll.pure_keep]  *)
(*       stays.  What is left of (2) is the two shapes below, as facts     *)
(*       about dfracs.                                                     *)
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
Require Import FsDurAlloc.     (* [fs_snap_alloc] -- the value-first entry
                                  the two inhabitedness witnesses use *)

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

(* ...AND THE FLATTENING IS BLIND TO AN EMPTY BLOCK, which is what makes
   the EQUALITY form no stronger than the [⊆] one (durable-disk lane H4).
   [map_seqZ] of the empty list is the empty map, so padding [D] with
   [b := []] leaves [fs_dbytes D] on the nose. *)
Lemma fs_dbytes_pad (D : gmap Z (list (bv 8))) (b : Z) :
  dbytes_ok D -> D !! b = None -> fs_dbytes (<[b := []]> D) = fs_dbytes D.
Proof.
  intros Hok Hb.
  assert (Hok' : dbytes_ok (<[b := []]> D))
    by (apply dbytes_ok_insert_2; [exact Hok | simpl; lia]).
  rewrite (fs_dbytes_insert D b [] Hok' Hb).
  rewrite (_ : (map_seqZ (b * Z.of_nat BSIZE) [] : gmap Z (bv 8)) = ∅);
    [| reflexivity].
  rewrite left_id_L //.
Qed.

(* ...and a padded map is no file system's: pad ABOVE the state's own size
   and the map names a block that is no block of this era
   ([FsDurSnap.ss_dombelow]).  Until lane H5 this went through [ss_bsz] --
   an empty block is not a whole block -- but the block WIDTH is the WAL's
   fact and no longer rides the snapshot at all, so the refutation is now
   [snap_shape_grow_absurd] at the empty run. *)
Lemma snap_shape_pad_absurd (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (b : Z) :
  sb_size (fss_sb S) <= b -> snap_shape S (<[b := []]> D) -> False.
Proof. exact (snap_shape_grow_absurd S D b []). Qed.

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
     [SystemAdequacy.fsimg_snap_ok] (not imported here: this file is a leaf
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

  (* ==================================================================== *)
  (*  1b.  THE EQUALITY IDENTITY DOES NOT HELP (durable-disk lane H4)      *)
  (*                                                                      *)
  (*  [FsDurRead.snap_auth] ties the epoch's map to [D] by [⊆].  Making    *)
  (*  it an EQUALITY is the obvious strengthening, and it buys nothing:    *)
  (*  the flattening is blind to a block whose byte list is empty, so the  *)
  (*  equation determines [D] nowhere.  Both refutations below are at the  *)
  (*  equality form, and the first is an [⊣⊢] -- the padded map is         *)
  (*  INDISTINGUISHABLE, not merely weaker.                               *)
  (* ==================================================================== *)

  Definition snap_auth_eq (g : gname) (B : gmap Z (bv 8))
      (D : gmap Z (list (bv 8))) : iProp Σ :=
    (ghost_map_auth g 1 B ∗ ⌜B = fs_dbytes D⌝)%I.

  Definition fs_snap_res_eq Γ (g : gname) (B : gmap Z (bv 8))
      (D : gmap Z (list (bv 8))) (S : fs_state_rec) : iProp Σ :=
    (snap_auth_eq g B D
     ∗ ghost_map_auth (γtop Γ) 1 (fss_inodes S)
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag Γ i n)
     ∗ fs_state Γ S
     ∗ ∃ kv : ity, own (γlink Γ) (link_tok_elem ROOTINO kv))%I.

  (* ...and it is INHABITED at the tied form, so the refutation below is
     not vacuous: [FsDurSnap.fs_snap_alloc] mints its authority at
     [fs_dbytes D] on the nose, so the equality holds by [reflexivity]. *)
  Lemma fs_snap_res_eq_inhabited (S : fs_state_rec)
      (D : gmap Z (list (bv 8))) :
    snap_ok S D ->
    ⊢ |==> ∃ g gl gt : gname,
        fs_snap_res_eq (snap_gamma g gl gt) g (fs_dbytes D) D S.
  Proof.
    intros Hok.
    iMod (fs_snap_alloc S D Hok) as (g gl gt) "H".
    iModIntro. iExists g, gl, gt.
    rewrite fs_snap_split /fs_snap_res /fs_snap_res_eq /snap_auth_eq
            /snap_auth.
    iDestruct "H" as "[(Hau & H2 & H3 & H4 & H5) _]".
    iDestruct "Hau" as "[Ha _]". iFrame "Ha H2 H3 H4 H5".
    iPureIntro. reflexivity.
  Qed.

  (* THE PAD IS INVISIBLE TO THE EQUALITY. *)
  Lemma fs_snap_res_eq_pad Γ (g : gname) (D : gmap Z (list (bv 8)))
      (b : Z) (S : fs_state_rec) :
    dbytes_ok D -> D !! b = None ->
    fs_snap_res_eq Γ g (fs_dbytes D) D S
    ⊣⊢ fs_snap_res_eq Γ g (fs_dbytes D) (<[b := []]> D) S.
  Proof.
    intros Hok Hb.
    rewrite /fs_snap_res_eq /snap_auth_eq (fs_dbytes_pad D b Hok Hb) //.
  Qed.

  (* (1) AT THE EQUALITY IDENTITY.  A reading of the GEOMETRY off the
     epoch's resources would survive padding [D] with an empty block, and
     no state fits that. *)
  Lemma snap_shape_not_readable_eq Γ (g : gname)
      (D : gmap Z (list (bv 8))) (b : Z) (S : fs_state_rec) :
    dbytes_ok D -> D !! b = None -> sb_size (fss_sb S) <= b ->
    (forall D' : gmap Z (list (bv 8)),
       fs_snap_res_eq Γ g (fs_dbytes D) D' S ⊢ ⌜snap_shape S D'⌝) ->
    fs_snap_res_eq Γ g (fs_dbytes D) D S ⊢ ⌜False⌝.
  Proof.
    intros Hok Hb Hsz Hread. iIntros "H".
    rewrite (fs_snap_res_eq_pad Γ g D b S Hok Hb).
    iDestruct (Hread (<[b := []]> D) with "H") as %Hsh.
    iPureIntro. exact (snap_shape_pad_absurd S D b Hsz Hsh).
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
