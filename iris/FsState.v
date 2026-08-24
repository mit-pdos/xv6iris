(* FsState.v -- the file system as ONE nested separation-logic predicate,
   at either view.

   Design of record: claude-notes/design/fs-state.md sections 1, 2 and 4.
   Stage 2a of claude-notes/projects/durable-disk.md.  The pieces:

     FsStateDefs.v    the view record [Γ], [byte_range], [blk_owned]
     FsStateLink.v    the link-counting RA
     FsStateInode.v   [rec_owned], [ind_owned], [inode_owned], [dir_owned]
     FsStateBitmap.v  [free_bitmap]
     FsState.v        [sb_owned], [fs_inodes], [fs_state], [fs_view], the mint

   THE ONE [∗]-ITERATION is [fs_inodes]; there is NO pure clause at this
   level or at [fs_state]'s (fs-state.md section 2, last bullet).  The
   abstraction is a SET of inodes, some of which decode as directories:
   there is no tree, no reachability, no "used set", no completeness clause,
   and nothing anywhere states a fact about more than one inode.

   THE MINT ([fs_state_mint], fs-state.md section 1 "Functoriality") walks
   the durable instance and allocates the logged instance's link ghosts to
   match.  It is a TRANSPORT: [fs_state_split] factors [fs_state] into the
   Φ-only [fs_footprint] and the Φ-free [fs_ghost], the caller supplies the
   footprint at the other Φ, and the mint moves the rest.  The link family's
   VALIDITY -- which is exactly "#tokens ≤ nlink at every inum", the one
   whole-state fact in the design -- is READ OFF the durable instance's own
   [own] by [fs_links_valid]; it is never proved and never maintained. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import BioDefs.
Require Import BitmapEnc.
Require Import DinodeEnc.
Require Import FsImg.
(* [fsTopG] -- an [Xv6G.xv6G] MEMBER since durable-disk 2b-inode-3 (see the
   note at [Xv6Cameras.fsTopG]).  IMPORTED, not exported, and imported
   BEFORE the [FsState*] exports below: [Xv6Cameras] declares names that
   collide with live ones here, and the LAST import wins (durable-notes,
   "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY").  The link family's own
   camera and class live there too, as [fsLinkUR] / [fsLinkG] -- the icache
   ledger already owned the name [linkUR].  Nothing above this file needs the class
   from here -- every one of them binds the bundle instead. *)
Require Import Xv6Cameras.
Require Export FsStateInode.
Require Export FsStateBitmap.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  1.  The abstract state                                             *)
(* ------------------------------------------------------------------ *)

Record fs_state_rec := MkFsS {
  fss_sb     : fs_sb;                 (* the parsed superblock            *)
  fss_sbb    : list (bv 8);           (* block [SB_BNO]'s raw bytes       *)
  fss_inodes : gmap Z fs_node;        (* the inodes, by inum              *)
  fss_used   : gset Z;                (* the bitmap's SET bits (in use)   *)
}.

Section FsState.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.

  (* ---------------------------------------------------------------- *)
  (*  2.  The nested predicates                                        *)
  (* ---------------------------------------------------------------- *)

  (* the superblock block, and the ONE local clause it can state: its bytes
     parse to [sb].  There is no encoder in the tree -- the superblock is
     only ever decoded (FsImg.fs_parse_sb) -- so the tie is stated at the
     parse, and the bytes are part of the abstract state. *)
  Definition sb_owned Γ (sb : fs_sb) (bs : list (bv 8)) : iProp Σ :=
    (blk_owned Γ SB_BNO bs ∗ ⌜fs_parse_sb (fun _ => bs) = Some sb⌝)%I.

  Definition fs_inodes Γ (sb : fs_sb) (I : gmap Z fs_node) : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, inode_owned Γ sb i n)%I.

  Definition fs_state Γ S : iProp Σ :=
    (sb_owned Γ (fss_sb S) (fss_sbb S)
     ∗ fs_inodes Γ (fss_sb S) (fss_inodes S)
     ∗ free_bitmap Γ (fss_sb S) (fss_used S))%I.

  (* fs-state.md section 4.  [γtop] is the abstract map a holder of one
     [inode_owned] carries a fragment of; that fragment is how it updates
     the top at its AU. *)
  Definition fs_view Γ : iProp Σ :=
    (∃ S, ghost_map_auth (γtop Γ) 1 (fss_inodes S) ∗ fs_state Γ S)%I.

  Definition top_frag Γ (i : Z) (n : fs_node) : iProp Σ := i ↪[γtop Γ] n.

  (* ---------------------------------------------------------------- *)
  (*  3.  Timelessness: [fsΦ] timeless => everything timeless          *)
  (* ---------------------------------------------------------------- *)

  Global Instance sb_owned_timeless `{!GTimeless Γ} sb bs :
    Timeless (sb_owned Γ sb bs).
  Proof. rewrite /sb_owned. apply _. Qed.

  Global Instance fs_inodes_timeless `{!GTimeless Γ} sb I :
    Timeless (fs_inodes Γ sb I).
  Proof. rewrite /fs_inodes. apply _. Qed.

  Global Instance fs_state_timeless `{!GTimeless Γ} S :
    Timeless (fs_state Γ S).
  Proof. rewrite /fs_state. apply _. Qed.

  Global Instance fs_view_timeless `{!GTimeless Γ} : Timeless (fs_view Γ).
  Proof. rewrite /fs_view. apply _. Qed.

  Global Instance top_frag_timeless Γ i n : Timeless (top_frag Γ i n).
  Proof. rewrite /top_frag. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (*  4.  THE FOOTPRINT / GHOST FACTORING                              *)
  (*                                                                   *)
  (*  [fs_footprint] is the [∗] of [fsΦ] at exactly the byte addresses  *)
  (*  [S] describes, and mentions NOTHING else of [Γ].  [fs_ghost]      *)
  (*  mentions no [fsΦ] at all.  The mint (section 6) is the composite  *)
  (*  of these two facts.                                              *)
  (* ---------------------------------------------------------------- *)

  Definition fs_footprint Γ S : iProp Σ :=
    (blk_owned Γ SB_BNO (fss_sbb S)
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, inode_phi Γ (fss_sb S) i n)
     ∗ blk_owned Γ (sb_bmapstart (fss_sb S)) (bm_bytes BSIZE (fss_used S))
     ∗ free_pool Γ (sb_size (fss_sb S)) (fss_used S))%I.

  Definition fs_ghost Γ S : iProp Σ :=
    (⌜fs_parse_sb (fun _ => fss_sbb S) = Some (fss_sb S)⌝
     ∗ [∗ map] i ↦ n ∈ fss_inodes S, inode_ghost Γ i n)%I.

  Global Instance fs_footprint_timeless `{!GTimeless Γ} S :
    Timeless (fs_footprint Γ S).
  Proof. rewrite /fs_footprint. apply _. Qed.

  Global Instance fs_ghost_timeless Γ S : Timeless (fs_ghost Γ S).
  Proof. rewrite /fs_ghost. apply _. Qed.

  (* the footprint does not read [γlink] or [γtop] *)
  Lemma fs_footprint_gname Γ g t S :
    fs_footprint Γ S ⊣⊢ fs_footprint (MkFsView (fsΦ Γ) g t) S.
  Proof. done. Qed.

  Lemma fs_state_split Γ S : fs_state Γ S ⊣⊢ fs_footprint Γ S ∗ fs_ghost Γ S.
  Proof.
    rewrite /fs_state /fs_footprint /fs_ghost /sb_owned /fs_inodes
            /free_bitmap /free_bitmap_at /inode_owned.
    rewrite big_sepM_sep.
    iSplit.
    - iIntros "((Hsb & %Hp) & [Hphi Hg] & Hbm & Hpool)". by iFrame.
    - iIntros "((Hsb & Hphi & Hbm & Hpool) & %Hp & Hg)". by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  5.  The link family, gathered                                    *)
  (* ---------------------------------------------------------------- *)

  Definition link_elem (I : gmap Z fs_node) : fsLinkUR :=
    ([^op map] i ↦ n ∈ I, link_elem_node i n).

  Definition fs_links (g : gname) (I : gmap Z fs_node) : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, own g (link_elem_node i n))%I.

  Definition fs_pure S : iProp Σ :=
    (⌜fs_parse_sb (fun _ => fss_sbb S) = Some (fss_sb S)⌝
     ∗ [∗ map] i ↦ n ∈ fss_inodes S, ⌜inode_local i n⌝)%I.

  Global Instance fs_pure_persistent S : Persistent (fs_pure S).
  Proof. rewrite /fs_pure. apply _. Qed.

  Global Instance fs_pure_timeless S : Timeless (fs_pure S).
  Proof. rewrite /fs_pure. apply _. Qed.

  Global Instance fs_links_timeless g I : Timeless (fs_links g I).
  Proof. rewrite /fs_links. apply _. Qed.

  Lemma fs_ghost_split Γ S :
    fs_ghost Γ S ⊣⊢ fs_links (γlink Γ) (fss_inodes S) ∗ fs_pure S.
  Proof.
    rewrite /fs_ghost /fs_pure /fs_links /inode_ghost.
    rewrite (big_sepM_proper
               (fun i n => link_auth Γ i (fn_nlink n) ∗ ent_toks Γ i n
                           ∗ ⌜inode_local i n⌝)%I
               (fun i n => own (γlink Γ) (link_elem_node i n)
                           ∗ ⌜inode_local i n⌝)%I);
      last first.
    { intros i n _. rewrite assoc inode_link_iff //. }
    rewrite big_sepM_sep.
    iSplit.
    - iIntros "(%Hp & Hl & Hc)". by iFrame.
    - iIntros "(Hl & %Hp & Hc)". by iFrame.
  Qed.

  (* THE ONE PLACE the whole-state counting fact is ever produced: it is
     READ OFF the instance's own [own], not proved. *)
  Lemma fs_links_valid g I : fs_links g I -∗ ⌜✓ link_elem I⌝.
  Proof.
    destruct (decide (I = ∅)) as [-> | Hne].
    - iIntros "_". iPureIntro.
      rewrite /link_elem big_opM_empty. apply ucmra_unit_valid.
    - apply map_choose in Hne as (i & n & Hin).
      rewrite /fs_links (big_sepM_delete _ I i n) //.
      iIntros "[Hi Hrest]".
      iDestruct (own_gather_map (A := fsLinkUR) g link_elem_node (delete i I)
                   (link_elem_node i n) with "Hi Hrest") as "H".
      iDestruct (own_valid with "H") as %Hv.
      iPureIntro. rewrite /link_elem (big_opM_delete _ I i n) //.
  Qed.

  Lemma fs_links_alloc (I : gmap Z fs_node) :
    ✓ link_elem I -> ⊢ |==> ∃ g : gname, fs_links g I.
  Proof.
    intros Hv.
    iMod (own_alloc (link_elem I)) as (g) "H"; [done |].
    iExists g. iModIntro.
    rewrite /fs_links /link_elem. by iApply big_opM_own_1.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  5b. THE BOOT ALLOCATION (B3)                                      *)
  (*                                                                    *)
  (*  Stage 4's [fs_state_mint] takes the family's validity OFF the      *)
  (*  durable instance ([fs_links_valid]).  At boot there is no durable  *)
  (*  instance to read it off, so the boot OWES it -- and that debt is   *)
  (*  stated here as a PREMISE, not hidden: [✓ link_elem I] IS the       *)
  (*  tokens-<=-nlink law of the initial map.  It is discharged for free *)
  (*  at a map of entry-less nodes ([link_elem_valid_no_ents] below);    *)
  (*  a map read off the image discharges it from [FsImg.fs_links_wf]    *)
  (*  (W9: every live directory has [nlink = 1] and no incoming ticket)  *)
  (*  and [FsImg.fs_links_eq] (the file-nlink equality).                 *)
  (* ---------------------------------------------------------------- *)

  (* A node with no directory entries carries no tokens, so its whole
     contribution to the family is its own auth. *)
  Lemma link_elem_no_ents (I : gmap Z fs_node) :
    (forall i n, I !! i = Some n -> dir_entries n = ∅) ->
    link_elem I ≡ (fun n => (● (fn_nlink n) : authR natUR)) <$> I.
  Proof.
    induction I as [| i n I Hi IH] using map_ind; intros Hall.
    - rewrite /link_elem big_opM_empty fmap_empty //.
    - assert (Hin : <[i := n]> I !! i = Some n) by (rewrite lookup_insert //).
      assert (Hrest : forall j m, I !! j = Some m -> dir_entries m = ∅).
      { intros j m Hj. apply (Hall j m).
        rewrite lookup_insert_ne; [exact Hj |].
        intros ->. rewrite Hi in Hj. done. }
      rewrite /link_elem big_opM_insert //.
      rewrite {1}/link_elem_node (Hall i n Hin) big_opM_empty right_id.
      rewrite -/(link_elem I) (IH Hrest) fmap_insert.
      rewrite insert_singleton_op; [done |]. rewrite lookup_fmap Hi //.
  Qed.

  Lemma link_elem_valid_no_ents (I : gmap Z fs_node) :
    (forall i n, I !! i = Some n -> dir_entries n = ∅) -> ✓ link_elem I.
  Proof.
    intros Hall. rewrite (link_elem_no_ents I Hall).
    intros j. rewrite lookup_fmap.
    destruct (I !! j) as [n |] eqn:E; [| done].
    rewrite /= Some_valid. by apply auth_auth_valid.
  Qed.

  (* BOTH era ghosts, allocated together from a map of nodes: the top map's
     AUTH plus one fragment per inum, and the link family with every inum's
     auth and every directory entry's token (the [fs_links] bundle, which
     [FsStateInode.inode_link_scatter] opens into
     [link_auth Γ i (fn_nlink n) ∗ ent_toks Γ n] at any [Γ] whose [γlink] is
     [gl]).  This is what [FsBoot.fs_boot_ghosts] runs. *)
  (* THE TWO MAPS ARE INDEPENDENT (durable-disk 2b-inode-3), and the general
     form is the one boot uses.  The TOP map is a plain [ghost_map] and owes
     NO validity at all, so it may be allocated at the IMAGE's nodes; the
     LINK family's [✓ link_elem] is a claim about tokens-<=-nlink over the
     whole family, so while the link step is still ahead it is allocated at
     the zero map, where the obligation is free ([link_elem_valid_no_ents]).
     [fs_boot_alloc] is this at [IL = IT]. *)
  Lemma fs_boot_alloc_at (IL IT : gmap Z fs_node) :
    ✓ link_elem IL ->
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 IT
        ∗ ([∗ map] i ↦ n ∈ IT, i ↪[gt] n)
        ∗ fs_links gl IL.
  Proof.
    intros Hv.
    iMod (fs_links_alloc IL Hv) as (gl) "Hl".
    iMod (ghost_map_alloc IT) as (gt) "[Ha Hf]".
    iModIntro. iExists gl, gt. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  5c. THE REGION'S BOOT SHAPE (durable-disk 2b-inode-4)             *)
  (*                                                                    *)
  (*  The inode REGION parks one [link_auth] per inum at the record's    *)
  (*  own [nlink] -- 2b-inode-1's ruling (i) applied to the ghost that   *)
  (*  mirrors a record FIELD -- because that is where the RA's law is    *)
  (*  READ: [IgetLic]'s licence (a) turns a directory record's token     *)
  (*  into "the target is allocated", and the target's authority has to  *)
  (*  be reachable from a presenter that does not hold the target.       *)
  (*                                                                    *)
  (*  At boot every token is still AT HOME, so the family's validity is  *)
  (*  free ([link_full_elem_valid]) and NO image sweep is spent.  Once   *)
  (*  a directory's tokens ride in its checked-out payload the boot owes *)
  (*  [FsImg]'s W9 + [fs_links_eq] instead; that is the links step.      *)
  (* ---------------------------------------------------------------- *)

  Definition link_full_map (I : gmap Z fs_node) : fsLinkUR :=
    ([^op map] i ↦ n ∈ I, link_full_elem i (fn_nlink n)).

  Definition fs_links_full (g : gname) (I : gmap Z fs_node) : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, own g (link_full_elem i (fn_nlink n)))%I.

  Global Instance fs_links_full_timeless g I : Timeless (fs_links_full g I).
  Proof. rewrite /fs_links_full. apply _. Qed.

  Lemma link_full_map_fmap (I : gmap Z fs_node) :
    link_full_map I
    ≡ (fun n => (● (fn_nlink n) ⋅ ◯ (fn_nlink n) : authR natUR)) <$> I.
  Proof.
    induction I as [| i n I Hi IH] using map_ind.
    - rewrite /link_full_map big_opM_empty fmap_empty //.
    - rewrite /link_full_map big_opM_insert // link_full_elem_singleton.
      rewrite -/(link_full_map I) IH fmap_insert.
      rewrite insert_singleton_op; [done |]. rewrite lookup_fmap Hi //.
  Qed.

  Lemma link_full_map_valid (I : gmap Z fs_node) : ✓ link_full_map I.
  Proof.
    rewrite link_full_map_fmap. intros j. rewrite lookup_fmap.
    destruct (I !! j) as [n |] eqn:E; [| done].
    rewrite /= Some_valid. apply auth_both_valid_discrete.
    split; [apply nat_included; lia | done].
  Qed.

  Lemma fs_links_full_alloc (I : gmap Z fs_node) :
    ⊢ |==> ∃ g : gname, fs_links_full g I.
  Proof.
    iMod (own_alloc (link_full_map I)) as (g) "H";
      [apply link_full_map_valid |].
    iExists g. iModIntro.
    rewrite /fs_links_full /link_full_map. by iApply big_opM_own_1.
  Qed.

  (* ...and the two ghosts allocated together, the region's way: no
     validity premise at all, because nothing is outstanding. *)
  Lemma fs_boot_alloc_full (IL IT : gmap Z fs_node) :
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 IT
        ∗ ([∗ map] i ↦ n ∈ IT, i ↪[gt] n)
        ∗ fs_links_full gl IL.
  Proof.
    iMod (fs_links_full_alloc IL) as (gl) "Hl".
    iMod (ghost_map_alloc IT) as (gt) "[Ha Hf]".
    iModIntro. iExists gl, gt. iFrame.
  Qed.

  Lemma fs_boot_alloc (I : gmap Z fs_node) :
    ✓ link_elem I ->
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 I
        ∗ ([∗ map] i ↦ n ∈ I, i ↪[gt] n)
        ∗ fs_links gl I.
  Proof. exact (fs_boot_alloc_at I I). Qed.

  (* The two directions of the factoring, AS WANDS.  A bare [rewrite] of an
     [⊣⊢] inside the proofmode rewrites the CONTEXT and the CONCLUSION
     together and desyncs them (durable-notes.md), and every consumer of the
     factoring already holds its input as a hypothesis. *)
  Lemma fs_state_to Γ S :
    fs_state Γ S -∗
      fs_footprint Γ S ∗ fs_links (γlink Γ) (fss_inodes S) ∗ fs_pure S.
  Proof.
    rewrite {1}fs_state_split fs_ghost_split. iIntros "($ & $ & $)".
  Qed.

  Lemma fs_state_of Γ S :
    fs_footprint Γ S -∗ fs_links (γlink Γ) (fss_inodes S) -∗ fs_pure S -∗
    fs_state Γ S.
  Proof.
    rewrite fs_state_split fs_ghost_split. iIntros "H1 H2 H3". iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  6.  THE MINT                                                     *)
  (*                                                                   *)
  (*  [ΓL] carries only the target [fsΦ]; its gname fields are not      *)
  (*  read (fs_footprint_gname), and the fresh ones come out of the     *)
  (*  conclusion.                                                      *)
  (* ---------------------------------------------------------------- *)

  Lemma fs_state_mint (ΓD ΓL : fs_view_names Σ) S :
    fs_state ΓD S -∗ fs_footprint ΓL S ==∗
      ∃ gl gt : gname,
        fs_state ΓD S ∗ fs_state (MkFsView (fsΦ ΓL) gl gt) S.
  Proof.
    iIntros "HD Hfp".
    iDestruct (fs_state_to with "HD") as "(HDfp & HDl & #Hpure)".
    iDestruct (fs_links_valid with "HDl") as %Hv.
    iMod (fs_links_alloc (fss_inodes S) Hv) as (gl) "HLl".
    iMod (ghost_map_alloc_empty (K := Z) (V := fs_node)) as (gt) "_".
    iModIntro. iExists gl, gt.
    iSplitL "HDfp HDl".
    { iApply (fs_state_of with "HDfp HDl Hpure"). }
    iApply (fs_state_of (MkFsView (fsΦ ΓL) gl gt) S with "[Hfp] HLl Hpure").
    iExact "Hfp".
  Qed.

  (* the same, delivering the top map too: the era's [fs_view], plus one
     [top_frag] per inode -- which is what a holder of [inode_owned] carries
     (fs-state.md section 4). *)
  Lemma fs_view_mint (ΓD ΓL : fs_view_names Σ) S :
    fs_state ΓD S -∗ fs_footprint ΓL S ==∗
      ∃ gl gt : gname,
        fs_state ΓD S
        ∗ fs_view (MkFsView (fsΦ ΓL) gl gt)
        ∗ ([∗ map] i ↦ n ∈ fss_inodes S,
             top_frag (MkFsView (fsΦ ΓL) gl gt) i n).
  Proof.
    iIntros "HD Hfp".
    iDestruct (fs_state_to with "HD") as "(HDfp & HDl & #Hpure)".
    iDestruct (fs_links_valid with "HDl") as %Hv.
    iMod (fs_links_alloc (fss_inodes S) Hv) as (gl) "HLl".
    iMod (ghost_map_alloc (fss_inodes S)) as (gt) "[Hauth Hfrag]".
    iModIntro. iExists gl, gt.
    iSplitL "HDfp HDl".
    { iApply (fs_state_of with "HDfp HDl Hpure"). }
    iFrame "Hfrag".
    rewrite /fs_view. iExists S. iFrame "Hauth".
    iApply (fs_state_of (MkFsView (fsΦ ΓL) gl gt) S with "[Hfp] HLl Hpure").
    iExact "Hfp".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  7.  Reading one inode out of the state                           *)
  (* ---------------------------------------------------------------- *)

  Lemma fs_inodes_acc Γ sb I i n :
    I !! i = Some n ->
    fs_inodes Γ sb I ⊢
      inode_owned Γ sb i n
      ∗ (∀ n', inode_owned Γ sb i n' -∗ fs_inodes Γ sb (<[i := n']> I)).
  Proof.
    intros Hi. rewrite /fs_inodes.
    iIntros "H".
    iDestruct (big_sepM_insert_acc _ _ i n Hi with "H") as "[$ H]".
    iIntros (n') "Hn". by iApply "H".
  Qed.

  Lemma fs_state_inode_acc Γ S i n :
    fss_inodes S !! i = Some n ->
    fs_state Γ S ⊢
      inode_owned Γ (fss_sb S) i n
      ∗ (∀ n', inode_owned Γ (fss_sb S) i n'
                    -∗ fs_state Γ (MkFsS (fss_sb S) (fss_sbb S)
                                         (<[i := n']> (fss_inodes S))
                                         (fss_used S))).
  Proof.
    intros Hi. rewrite /fs_state.
    iIntros "(Hsb & Hin & Hbm)".
    iDestruct (fs_inodes_acc _ _ _ i n Hi with "Hin") as "[$ Hin]".
    iIntros (n') "Hn". iFrame "Hsb Hbm". by iApply "Hin".
  Qed.

End FsState.

Global Typeclasses Opaque sb_owned fs_inodes fs_state fs_footprint fs_ghost
                         fs_links fs_pure.
