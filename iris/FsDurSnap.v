(* FsDurSnap.v -- SNAPSHOT COMMITS: the durable file-system instance is
   ALLOCATED AFRESH at every group commit and never updated.

   Design of record: claude-notes/design/fs-state.md section 4^9 (the
   owner's SNAPSHOT ruling, with its addendum 5 "the transport lemma IS
   the allocator"); worklist item 4 of
   claude-notes/projects/durable-disk.md.

   THE ONE IDEA.  No durable ghost is ever moved.  At a group commit the
   committer ALLOCATES a fresh gname family at the quiescent state's
   values, proves the whole file-system predicate at BIRTH, and DISCARDS
   the previous instance (the logic is affine).  Allocation is
   unconditionally frame-preserving, so every update wall the project met
   -- the auth-in-frame refutation (fs-state.md section 4), the
   completeness demand, the accessor chain's missing intermediate object,
   the deferred ledger's cross-op eviction, the kinds tie's geometry -- is
   vacated by construction: there is nothing to update.

   WHAT THE TRANSPORT TAKES.  Its inputs are a VALUE and PURE FACTS, and
   NOTHING ELSE -- no era resource, no previous instance, no authority
   loan.  That is what makes it callable at the commit (where the era's
   pieces are distributed behind [iregN]/[ftopN]/[bitmapN] and the icache
   escrow, hence unreachable at any mask) and, at stage 4, callable at
   BOOT to clone the durable snapshot onto a fresh era family.

   THE ONE THING THAT MAKES IT WORK: the snapshot's byte points-to is
   PERSISTENT ([a -> v] at [DfracDiscarded]).  A frozen instance may be
   (fs-state.md 4^9 (3)), and it is what lets [fs_state] be BUILT from a
   flat byte map with no whole-state disjointness premise: with [blk_owned]
   persistent, the footprint's pieces are COPIES of the ledger's blocks and
   the [∗] costs nothing.  With an exclusive points-to the same
   construction demands "distinct inodes name distinct blocks", which is
   a cross-inode pure fact -- fs-state.md section 0's forbidden shape, and
   underivable from any per-object accumulation.  The exclusivity the
   durable instance gives up is consumed nowhere: [phi_excl]'s consumers
   ([FsStateBitmap.free_pool_used], hence xv6's "freeing free block"
   panic, and [blk_owned_ne]) are all ERA-side, and a snapshot is never
   written.

   WHAT IS NOT PERSISTENT, and why the snapshot as a whole is not: the
   link family's per-inum [auth nlink] has no core.  Nothing needs to
   borrow a snapshot -- it lives inside [crashN] and its consumers read
   the PURE [snap_ok], which is persistent -- so the bundle stays
   exclusive and the receipts are copies of the pure tie. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import BioDefs.
Require Import DiskImg.       (* [diskImgG] -- the byte map's capacity class;
                                 IMPORTED, since [Import] is not transitive
                                 and a backtick binder for a class that is
                                 not in scope silently invents a VARIABLE
                                 (durable-notes.md, typeclass-sweep trap 1) *)
Require Import BitmapEnc.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeDefs.
Require Import FsImg.
Require Import LogDefs.       (* [fs_dbytes] -- the byte flattening       *)
Require Import Xv6Cameras.
Require Import FsDurBytes.    (* [fs_dbytes_blocks] -- Gamma-generically  *)
(* LAST, so [FsState]'s [fs_view] / [byte_range] / [blk_owned] / [link_auth]
   win over the block layer's twins that arrive transitively through
   [FsDurBytes] -> [RiscvPtsto] (durable-notes.md, "AND WHERE THAT IMPORT
   COLLIDES, PUT IT EARLY"). *)
Require Export FsState.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE TIE                                                      *)
(* ===================================================================== *)

(* inum [z]'s 64 bytes sit at offset [off] of its inode block's byte list.
   Stated as a SPLIT rather than as a [take]/[drop] equation because that
   is the shape [FsStateDefs.byte_range_app] consumes, and because it is
   what a writer's own splice fact ([FsBlocks.blk_splice]) already says. *)
Definition rec_in_blk (bs : list (bv 8)) (off : Z) (dn : dinode) : Prop :=
  exists pre post,
    bs = (pre ++ dinode_bytes dn ++ post)%list /\ Z.of_nat (length pre) = off.

(* THE ACCUMULATED PURE CONTENT: an abstract state [S] and the committed
   block map [D] agree at [S]'s FOOTPRINT.  Every clause names ONE object
   and its own bytes -- there is no clause about two inodes, no domain
   sweep, no disjointness, and no "used set" completeness (fs-state.md
   section 0).  The three that are not per-object are:

   - [sk_dom], the inode map's DOMAIN over the region.  It is
     fs-state.md 4.5 (2)'s per-inum EXISTENCE witness and 3c's third
     [dgeo_ok] equation, and under snapshots it is by construction: the
     value [S] is read off the era's own top-map authority, whose domain
     IS the region's inums.
   - [sk_links], the link family's validity.  It is the tokens-<=-nlink
     law, which fs-state.md section 7 already names as "the one whole-state
     fact in the design"; it is never MAINTAINED here, only carried, and
     the allocator needs it because [own_alloc] needs a valid element.
   - [sk_bsz], "every block of [D] is a whole block", which is the log's
     own row (b) property. *)
Record snap_ok (S : fs_state_rec) (D : gmap Z (list (bv 8))) : Prop :=
  MkSnapOk {
  sk_bsz    : forall b bs, D !! b = Some bs -> length bs = BSIZE;
  (* the superblock block, and the one clause [sb_owned] states *)
  sk_sb     : D !! SB_BNO = Some (fss_sbb S);
  sk_parse  : fs_parse_sb (fun _ => fss_sbb S) = Some (fss_sb S);
  (* the bitmap block IS the encoding of the used set *)
  sk_bmap   : D !! sb_bmapstart (fss_sb S)
              = Some (bm_bytes BSIZE (fss_used S));
  (* every block below the size whose bit reads FREE is a block of [D] *)
  sk_pool   : forall b, 0 <= b < sb_size (fss_sb S) -> b ∉ fss_used S ->
                is_Some (D !! b);
  (* the inodes: range, local clauses, and the three byte ties *)
  sk_inum   : forall i n, fss_inodes S !! i = Some n -> 0 <= i < 2 ^ 32;
  sk_local  : forall i n, fss_inodes S !! i = Some n -> inode_local i n;
  sk_rec    : forall i n, fss_inodes S !! i = Some n ->
                exists bs,
                  D !! (sb_inodestart (fss_sb S) + i `div` 16) = Some bs
                  /\ rec_in_blk bs (64 * (i `mod` 16)) (fn_rec n);
  sk_blk    : forall i n k bs, fss_inodes S !! i = Some n ->
                fn_blk n !! k = Some bs -> D !! fn_naddr n k = Some bs;
  sk_ind    : forall i n, fss_inodes S !! i = Some n -> fn_indb n <> 0 ->
                D !! fn_indb n = Some (ind_bytes (fn_ent n));
  (* the region's inums are all named *)
  sk_dom    : forall i, 0 <= i < sb_ninodes (fss_sb S) ->
                is_Some (fss_inodes S !! i);
  (* the link family's own validity *)
  sk_links  : ✓ link_elem (fss_inodes S);
}.

Global Arguments sk_bsz {_ _} _.
Global Arguments sk_sb {_ _} _.
Global Arguments sk_parse {_ _} _.
Global Arguments sk_bmap {_ _} _.
Global Arguments sk_pool {_ _} _.
Global Arguments sk_inum {_ _} _.
Global Arguments sk_local {_ _} _.
Global Arguments sk_rec {_ _} _.
Global Arguments sk_blk {_ _} _.
Global Arguments sk_ind {_ _} _.
Global Arguments sk_dom {_ _} _.
Global Arguments sk_links {_ _} _.

(* THE PURE READING THE SPIKE USES: the state names every region inum, and
   for the named node the record's bytes are where they are.  Everything a
   consumer of a snapshot learns about one inode goes through this.

   BOTH SIDES ARE NAMED DEFINITIONS and not inline arithmetic, because the
   guarded form below appears inside a [⌜ ⌝], where the ambient scope is
   [type_scope] and [a + b] would parse as [sum] (durable-notes.md, the
   scope-stack trap). *)
Definition snap_inum_ok (S : fs_state_rec) (i : Z) : Prop :=
  0 <= i < sb_ninodes (fss_sb S).

Definition snap_inode_at (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) : Prop :=
  exists n, fss_inodes S !! i = Some n
         /\ inode_local i n
         /\ exists bs, D !! (sb_inodestart (fss_sb S) + i `div` 16) = Some bs
                    /\ rec_in_blk bs (64 * (i `mod` 16)) (fn_rec n).

Lemma snap_ok_inode (S : fs_state_rec) (D : gmap Z (list (bv 8))) (i : Z) :
  snap_ok S D -> snap_inum_ok S i -> snap_inode_at S D i.
Proof.
  intros Hok Hi.
  destruct (sk_dom Hok i Hi) as [n Hn].
  exists n. split; [exact Hn |]. split; [exact (sk_local Hok i n Hn) |].
  exact (sk_rec Hok i n Hn).
Qed.

(* ===================================================================== *)
(*  2.  THE SNAPSHOT'S VIEW RECORD                                        *)
(* ===================================================================== *)

Section Snap.
  (* [diskImgG] is the tree's UNIQUE [ghost_mapG Σ Z (bv 8)]; the snapshot's
     byte map is a FRESH gname at that same class. *)
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.
  Implicit Types D : gmap Z (list (bv 8)).

  Definition snap_gamma (g gl gt : gname) : fs_view_names Σ :=
    MkFsView (fun (a : Z) (v : bv 8) => (a ↪[g]□ v)%I) gl gt.

  Global Instance snap_gamma_gtimeless g gl gt :
    GTimeless (snap_gamma g gl gt).
  Proof. intros a v. rewrite /snap_gamma /=. apply _. Qed.

  Global Instance snap_phi_persistent g gl gt a v :
    Persistent (fsΦ (snap_gamma g gl gt) a v).
  Proof. rewrite /snap_gamma /=. apply _. Qed.

  Global Instance snap_byte_range_persistent g gl gt b off bs :
    Persistent (byte_range (snap_gamma g gl gt) b off bs).
  Proof. rewrite /byte_range. apply _. Qed.

  Global Instance snap_blk_owned_persistent g gl gt b bs :
    Persistent (blk_owned (snap_gamma g gl gt) b bs).
  Proof. rewrite /blk_owned. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE BLOCK LEDGER, and the way into a piece of a block          *)
  (* ------------------------------------------------------------------ *)

  Definition blk_ledger Γ D : iProp Σ :=
    ([∗ map] b ↦ bs ∈ D, blk_owned Γ b bs)%I.

  Global Instance blk_ledger_persistent g gl gt D :
    Persistent (blk_ledger (snap_gamma g gl gt) D).
  Proof. rewrite /blk_ledger. apply _. Qed.

  Lemma blk_ledger_lookup Γ D b bs :
    D !! b = Some bs -> blk_ledger Γ D ⊢ blk_owned Γ b bs.
  Proof. intros Hb. rewrite /blk_ledger (big_sepM_lookup _ _ b bs Hb) //. Qed.

  (* a RECORD out of its block: [byte_range_app] twice, keeping the middle *)
  Lemma blk_owned_rec_in Γ b bs off dn :
    rec_in_blk bs off dn ->
    blk_owned Γ b bs ⊢ byte_range Γ b off (dinode_bytes dn).
  Proof.
    intros (pre & post & -> & Hlen).
    rewrite /blk_owned. iIntros "[_ H]".
    rewrite byte_range_app. iDestruct "H" as "[_ H]".
    rewrite Z.add_0_l Hlen.
    rewrite byte_range_app. iDestruct "H" as "[$ _]".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE INSTANCE, FROM A LEDGER AND THE PURE TIE                    *)
  (*                                                                      *)
  (*  Gamma-GENERIC and SOURCE-AGNOSTIC: nothing here knows which          *)
  (*  points-to [fsΦ Γ] is, nor where the ledger came from.  The [□] on    *)
  (*  the ledger is the whole of what the construction needs of the        *)
  (*  points-to, and it is what replaces the whole-state disjointness a    *)
  (*  linear ledger would demand.                                          *)
  (* ------------------------------------------------------------------ *)

  Lemma fs_state_of_ledger Γ S D :
    snap_ok S D ->
    □ blk_ledger Γ D -∗ fs_links (γlink Γ) (fss_inodes S) -∗ fs_state Γ S.
  Proof.
    intros Hok. iIntros "#Hled Hlinks".
    rewrite /fs_state. iSplitR "Hlinks"; last iSplitL "Hlinks".
    - (* ---- the superblock ---- *)
      rewrite /sb_owned. iSplitL; [| iPureIntro; exact (sk_parse Hok)].
      iApply (blk_ledger_lookup Γ D SB_BNO (fss_sbb S) (sk_sb Hok) with "Hled").
    - (* ---- the inodes ---- *)
      rewrite /fs_inodes /fs_links.
      iApply (big_sepM_impl with "Hlinks").
      iIntros "!#" (i n Hi) "Hown".
      rewrite /inode_owned. iSplitR "Hown".
      + (* the footprint *)
        rewrite /inode_phi. iSplitR "".
        * (* the record *)
          rewrite (rec_owned_sb Γ (fss_sb S) i (fn_rec n) (sk_inum Hok i n Hi)).
          rewrite /rec_owned_at.
          destruct (sk_rec Hok i n Hi) as (bs & Hbs & Hin).
          iApply (blk_owned_rec_in Γ _ bs _ (fn_rec n) Hin).
          iApply (blk_ledger_lookup Γ D _ bs Hbs with "Hled").
        * iSplitL.
          -- (* the data blocks *)
             iApply big_sepM_intro. iIntros "!#" (k bs Hk).
             iApply (blk_ledger_lookup Γ D (fn_naddr n k) bs
                       (sk_blk Hok i n k bs Hi Hk) with "Hled").
          -- (* the indirect block *)
             rewrite /ind_owned.
             destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
             iApply (blk_ledger_lookup Γ D (fn_indb n) (ind_bytes (fn_ent n))
                       (sk_ind Hok i n Hi Hnz) with "Hled").
      + (* the ghosts *)
        rewrite /inode_ghost.
        iDestruct (inode_link_scatter with "Hown") as "[$ $]".
        iPureIntro. exact (sk_local Hok i n Hi).
    - (* ---- the bitmap and the free pool ---- *)
      rewrite /free_bitmap /free_bitmap_at. iSplitL.
      + iApply (blk_ledger_lookup Γ D (sb_bmapstart (fss_sb S))
                  (bm_bytes BSIZE (fss_used S)) (sk_bmap Hok) with "Hled").
      + rewrite /free_pool.
        iApply big_sepL_intro. iIntros "!#" (k b Hb).
        apply lookup_seqZ in Hb as [-> Hb].
        rewrite /pool_elt.
        destruct (bool_decide (0 + Z.of_nat k ∈ fss_used S)) eqn:Hu; [done |].
        apply bool_decide_eq_false in Hu.
        destruct (sk_pool Hok (0 + Z.of_nat k) ltac:(lia) Hu) as [bs Hbs].
        iExists bs.
        iApply (blk_ledger_lookup Γ D _ bs Hbs with "Hled").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  5.  THE ALLOCATOR = THE TRANSPORT (fs-state.md 4^9, addendum 5)     *)
  (*                                                                      *)
  (*  All three gname families in ONE update, returned EXISTENTIALLY:     *)
  (*  [own_alloc] cannot target a name, and the landed allocator family   *)
  (*  ([FsState.fs_boot_alloc_at]) already has this shape.  The byte map   *)
  (*  joins it here.                                                      *)
  (* ------------------------------------------------------------------ *)

  Lemma snap_ledger_of_elems g gl gt D :
    (forall b bs, D !! b = Some bs -> length bs = BSIZE) ->
    ([∗ map] a ↦ v ∈ fs_dbytes D, a ↪[g]□ v)
    ⊢ blk_ledger (snap_gamma g gl gt) D.
  Proof.
    intros Hlen.
    rewrite /blk_ledger -(fs_dbytes_blocks (snap_gamma g gl gt) D Hlen).
    iIntros "H". iExact "H".
  Qed.

  (* the byte map, freshly allocated and immediately frozen *)
  Lemma snap_bytes_alloc (B : gmap Z (bv 8)) :
    ⊢ |==> ∃ g : gname,
        ghost_map_auth g 1 B ∗ ([∗ map] a ↦ v ∈ B, a ↪[g]□ v).
  Proof.
    iMod (ghost_map_alloc_empty (K := Z) (V := bv 8)) as (g) "Ha".
    iMod (ghost_map_insert_persist_big B with "Ha") as "[Ha Hel]";
      [apply map_disjoint_empty_r |].
    rewrite right_id_L. iModIntro. iExists g. iFrame.
  Qed.

  (* THE TRANSPORT.  Inputs: the abstract state VALUE [S] and the pure tie
     to the block map [D].  Output: a fresh family and the whole instance
     at [S], with its own byte authority. *)
  Theorem fs_snap_alloc S D :
    snap_ok S D ->
    ⊢ |==> ∃ g gl gt : gname,
        ghost_map_auth g 1 (fs_dbytes D)
        ∗ ghost_map_auth gt 1 (fss_inodes S)
        ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag (snap_gamma g gl gt) i n)
        ∗ fs_state (snap_gamma g gl gt) S.
  Proof.
    intros Hok.
    iMod (snap_bytes_alloc (fs_dbytes D)) as (g) "[Hba Hbe]".
    iMod (fs_links_alloc (fss_inodes S) (sk_links Hok)) as (gl) "Hlinks".
    iMod (ghost_map_alloc (fss_inodes S)) as (gt) "[Hta Htf]".
    iModIntro. iExists g, gl, gt.
    iDestruct (snap_ledger_of_elems g gl gt D (sk_bsz Hok) with "Hbe")
      as "#Hled".
    iFrame "Hba Hta Htf".
    iApply (fs_state_of_ledger (snap_gamma g gl gt) S D Hok with "Hled").
    iExact "Hlinks".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  6.  THE SNAPSHOT, AND THE EPOCH REGISTRY                            *)
  (* ------------------------------------------------------------------ *)

  (* ONE epoch's durable instance: the byte authority it owns outright, the
     abstract map's authority and every fragment, the nested predicate, and
     the PURE tie to the committed block map.  Nothing outside [crashN]
     ever holds a piece of it. *)
  Definition fs_snap Γ (g : gname) D S : iProp Σ :=
    (ghost_map_auth g 1 (fs_dbytes D)
     ∗ ghost_map_auth (γtop Γ) 1 (fss_inodes S)
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag Γ i n)
     ∗ fs_state Γ S
     ∗ ⌜snap_ok S D⌝)%I.

  Global Instance fs_snap_timeless `{!GTimeless Γ} g D S :
    Timeless (fs_snap Γ g D S).
  Proof. rewrite /fs_snap. apply _. Qed.

  (* THE REGISTRY: the CURRENT snapshot, at the committed block map [D].
     The gname family and the state are existential -- an epoch is named
     only by the map it stands at, which is what makes [P_dur] a function
     of [D] alone and therefore droppable into [FsCrash.P_fs] with no
     arity change. *)
  Definition P_dur D : iProp Σ :=
    (∃ (g gl gt : gname) (S : fs_state_rec),
       fs_snap (snap_gamma g gl gt) g D S)%I.

  Global Instance P_dur_timeless D : Timeless (P_dur D).
  Proof. rewrite /P_dur. apply _. Qed.

  Lemma P_dur_alloc S D : snap_ok S D -> ⊢ |==> P_dur D.
  Proof.
    intros Hok.
    iMod (fs_snap_alloc S D Hok) as (g gl gt) "(Hba & Hta & Htf & Hst)".
    iModIntro. iExists g, gl, gt, S. rewrite /fs_snap. by iFrame.
  Qed.

  (* THE COMMIT'S STEP.  The previous epoch is DISCARDED (affine) and the
     next one allocated; no ghost is updated, so the step needs nothing
     from the old instance and nothing from the era but the value and the
     facts. *)
  Definition dsnap_step D D' : iProp Σ := (P_dur D ==∗ P_dur D')%I.

  Lemma dsnap_step_of S' D D' : snap_ok S' D' -> ⊢ dsnap_step D D'.
  Proof.
    intros Hok. rewrite /dsnap_step. iIntros "_".
    iApply (P_dur_alloc S' D' Hok).
  Qed.

  Lemma dsnap_step_id D : ⊢ dsnap_step D D.
  Proof. rewrite /dsnap_step. iIntros "$". done. Qed.

  Lemma dsnap_step_trans D D' D'' :
    dsnap_step D D' -∗ dsnap_step D' D'' -∗ dsnap_step D D''.
  Proof.
    rewrite /dsnap_step. iIntros "H1 H2 H".
    iMod ("H1" with "H") as "H". iApply ("H2" with "H").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  7.  WHAT A CONSUMER READS OFF THE CURRENT SNAPSHOT                  *)
  (* ------------------------------------------------------------------ *)

  (* the pure tie is persistent, so a receipt is a COPY and no borrowing
     is needed -- which is what makes the non-persistence of the bundle
     itself cost nothing *)
  Lemma P_dur_tie D : P_dur D -∗ ∃ S, ⌜snap_ok S D⌝.
  Proof. iIntros "H". iDestruct "H" as (g gl gt S) "(_&_&_&_&%)". eauto. Qed.

  (* ...and the same with the snapshot HANDED BACK, which is the form an
     invariant's opener needs.  Everything the spike theorem reads off the
     current snapshot goes through this plus the pure [snap_ok_inode]:
     nothing is spent, because the tie is pure. *)
  Lemma P_dur_tie_keep D : P_dur D -∗ ∃ S, ⌜snap_ok S D⌝ ∗ P_dur D.
  Proof.
    iIntros "H". iDestruct "H" as (g gl gt S) "Hs".
    iDestruct "Hs" as "(Hba & Hta & Htf & Hst & %Hok)".
    iExists S. iSplitR; [iPureIntro; exact Hok |].
    iExists g, gl, gt, S. rewrite /fs_snap. by iFrame.
  Qed.

  (* THE SPIKE'S READING: at the current snapshot, every region inum is
     named, its node satisfies the local clauses, and its record's bytes
     are the ones the committed map holds at its slot. *)
  Lemma P_dur_inode D (i : Z) :
    P_dur D -∗
      ∃ S, ⌜snap_ok S D⌝
           ∗ ⌜snap_inum_ok S i -> snap_inode_at S D i⌝
           ∗ P_dur D.
  Proof.
    iIntros "H".
    iDestruct (P_dur_tie_keep with "H") as (S Hok) "HP".
    iExists S. iFrame "HP". iSplitR; [iPureIntro; exact Hok |].
    iPureIntro. intros Hi. exact (snap_ok_inode S D i Hok Hi).
  Qed.

End Snap.
