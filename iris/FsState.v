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
From iris.algebra Require Import auth gmap gmultiset numbers.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import BioDefs.
Require Import BitmapEnc.
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

  (* THE FRAGMENT AT A SHARE (durable-fs-plan.md section 3, [ilock]'s read
     arm; durable-disk B''-join).  A read-locking [ilock] hands its holder a
     QUARTER of this element beside the quarter of the byte legs, and the
     escrow's read arm keeps three quarters.  Two things ride on that one
     line: a read-locker cannot RETAG (every mover --
     [InodeRegion.ireg_top_retag] -- needs the whole element), and the arm's
     existentially-bound node is PINNED to the holder's by ghost-map
     agreement, which is what lets [IcacheEscrow.ic_unshed_rd] re-form the
     payload with no per-slot pin ghost at all.

     [top_frag] IS ITS [DfracOwn 1] READING, on the nose ([k ↪[γ] v] IS
     [k ↪[γ]{DfracOwn 1} v]), so no site that spells [top_frag] moves. *)
  Definition top_frag_q Γ (dq : dfrac) (i : Z) (n : fs_node) : iProp Σ :=
    i ↪[γtop Γ]{dq} n.

  Lemma top_frag_1 Γ i n : top_frag Γ i n = top_frag_q Γ (DfracOwn 1) i n.
  Proof. reflexivity. Qed.

  Global Instance top_frag_q_timeless Γ dq i n : Timeless (top_frag_q Γ dq i n).
  Proof. rewrite /top_frag_q. apply _. Qed.

  Lemma top_frag_q_split Γ (q1 q2 : Qp) i n :
    top_frag_q Γ (DfracOwn (q1 + q2)) i n
    ⊣⊢ top_frag_q Γ (DfracOwn q1) i n ∗ top_frag_q Γ (DfracOwn q2) i n.
  Proof.
    rewrite /top_frag_q -ghost_map_elem_fractional //.
  Qed.

  (* THE PIN: two shares of the same inum's fragment name the SAME node. *)
  Lemma top_frag_q_agree Γ dq1 dq2 i n1 n2 :
    top_frag_q Γ dq1 i n1 -∗ top_frag_q Γ dq2 i n2 -∗ ⌜n1 = n2⌝.
  Proof.
    rewrite /top_frag_q. iIntros "H1 H2".
    by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

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

  (* THE REGISTER'S AUTHORITY IS EXISTENTIAL IN THE BUNDLE (a file has many
     namers, so no function of the node alone can name it), so the FAMILY's
     element is indexed by a CHOICE FUNCTION -- one multiset per inum, each
     satisfying that inum's own [fn_par_ok].  Everything downstream reads
     the pair [link_elem_ok] + [✓ link_elem] and nothing else about it; the
     value-first allocator that computes [f] from [I] is [FsCfgBoot]'s and
     is what the resource-transport mint replaces. *)
  Definition link_elem_ok (I : gmap Z fs_node) (f : Z -> gmultiset (option Z))
    : Prop :=
    forall i n, I !! i = Some n -> fn_par_ok n (f i).

  Definition link_elem (I : gmap Z fs_node) (f : Z -> gmultiset (option Z))
    : fsLinkUR :=
    ([^op map] i ↦ n ∈ I, link_elem_node i n (f i)).

  (* ONE inode's whole contribution, under the existential its register
     authority is bound by.  Named, because it is what the commit's
     collection produces one inum at a time. *)
  Definition fs_link_node (g : gname) (i : Z) (n : fs_node) : iProp Σ :=
    (∃ P, ⌜fn_par_ok n P⌝ ∗ own g (link_elem_node i n P))%I.

  Global Instance fs_link_node_timeless g i n : Timeless (fs_link_node g i n).
  Proof. rewrite /fs_link_node. apply _. Qed.

  Definition fs_links (g : gname) (I : gmap Z fs_node) : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, fs_link_node g i n)%I.

  (* [link_elem] only ever reads [f] inside [I]'s domain *)
  Lemma link_elem_ext (I : gmap Z fs_node) (f g : Z -> gmultiset (option Z)) :
    (forall i, is_Some (I !! i) -> f i = g i) ->
    link_elem I f ≡ link_elem I g.
  Proof.
    intros Hfg. rewrite /link_elem. apply big_opM_proper.
    intros i n Hi. rewrite (Hfg i ltac:(by eexists)) //.
  Qed.

  (* A big-op of SINGLETONS AT THEIR OWN KEYS reads pointwise: the one
     induction every "the family is valid" argument in this file needs, and
     the reason none of them has to name an [fmap]. *)
  Lemma big_op_singletons_lookup {A : cmra} (I : gmap Z fs_node)
      (h : Z -> fs_node -> A) (j : Z) :
    (([^op map] i ↦ n ∈ I, ({[ i := h i n ]} : gmap Z A)) !! j)
    ≡ (fun n => h j n) <$> (I !! j).
  Proof.
    revert j. induction I as [| i n I Hi IH] using map_ind; intros j.
    - rewrite big_opM_empty lookup_empty //.
    - assert (Heq : ([^op map] k ↦ m ∈ <[i := n]> I,
                       ({[ k := h k m ]} : gmap Z A))
                    ≡ ({[ i := h i n ]} : gmap Z A)
                      ⋅ ([^op map] k ↦ m ∈ I, ({[ k := h k m ]} : gmap Z A)))
        by (rewrite big_opM_insert //).
      rewrite (Heq j) lookup_op.
      destruct (decide (j = i)) as [-> | Hne].
      + pose proof (IH i) as IHi. rewrite Hi in IHi. simpl in IHi.
        rewrite lookup_singleton lookup_insert IHi right_id //.
      + rewrite lookup_singleton_ne; [| done].
        rewrite lookup_insert_ne; [| done].
        rewrite left_id. exact (IH j).
  Qed.

  Lemma link_elem_empty (f : Z -> gmultiset (option Z)) : link_elem ∅ f = ε.
  Proof. rewrite /link_elem big_opM_empty //. Qed.

  Lemma link_elem_insert (I : gmap Z fs_node) (i : Z) (n : fs_node)
      (f : Z -> gmultiset (option Z)) :
    I !! i = None ->
    link_elem (<[i := n]> I) f ≡ link_elem_node i n (f i) ⋅ link_elem I f.
  Proof. intros Hi. rewrite /link_elem big_opM_insert //. Qed.

  Lemma link_elem_delete (I : gmap Z fs_node) (i : Z) (n : fs_node)
      (f : Z -> gmultiset (option Z)) :
    I !! i = Some n ->
    link_elem I f ≡ link_elem_node i n (f i) ⋅ link_elem (delete i I) f.
  Proof. intros Hi. rewrite /link_elem (big_opM_delete _ I i n) //. Qed.

  Lemma link_elem_ok_ext (I : gmap Z fs_node) (f g : Z -> gmultiset (option Z)) :
    (forall i, is_Some (I !! i) -> f i = g i) ->
    link_elem_ok I f -> link_elem_ok I g.
  Proof.
    intros Hfg Hok i n Hi. rewrite -(Hfg i ltac:(by eexists)). exact (Hok i n Hi).
  Qed.

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
    rewrite /fs_ghost /fs_pure /fs_links /fs_link_node.
    rewrite (big_sepM_proper
               (fun i n => inode_ghost Γ i n)%I
               (fun i n => (∃ P, ⌜fn_par_ok n P⌝
                                 ∗ own (γlink Γ) (link_elem_node i n P))
                           ∗ ⌜inode_local i n⌝)%I);
      last first.
    { intros i n _. rewrite inode_ghost_iff //. }
    rewrite big_sepM_sep.
    iSplit.
    - iIntros "(%Hp & Hl & Hc)". by iFrame.
    - iIntros "(Hl & %Hp & Hc)". by iFrame.
  Qed.

  (* THE ONE PLACE the whole-state counting fact is ever produced: it is
     READ OFF the instance's own [own], not proved.  The choice function
     comes out of the same walk that gathers the [own]s. *)
  (* THE ACCUMULATOR FORM: the empty map contributes the unit, which an
     [emp] cannot produce, so the walk starts from a resource the caller
     already holds -- exactly [own_gather_map]'s shape one level up. *)
  Lemma fs_links_gather g I (x : fsLinkUR) :
    own g x -∗ fs_links g I -∗
    ∃ f, ⌜link_elem_ok I f⌝ ∗ own g (x ⋅ link_elem I f).
  Proof.
    revert x. induction I as [| i n I Hi IH] using map_ind; intros x.
    - iIntros "Hx _". iExists (fun _ => ∅). iSplitR.
      { iPureIntro. intros j m Hj. rewrite lookup_empty in Hj. discriminate. }
      rewrite link_elem_empty right_id. iFrame.
    - rewrite /fs_links /fs_link_node big_sepM_insert //.
      iIntros "Hx [(%P & %Hok & Hi) Hrest]".
      iDestruct (own_op with "[$Hx $Hi]") as "Hxi".
      iDestruct (IH (x ⋅ link_elem_node i n P) with "Hxi Hrest")
        as (f) "[%Hf Hr]".
      set (f' := fun z => if decide (z = i) then P else f z).
      assert (Hext : forall j, is_Some (I !! j) -> f j = f' j).
      { intros j [m Hj]. rewrite /f'. destruct (decide (j = i)) as [-> |];
          [rewrite Hi in Hj; discriminate | done]. }
      assert (Hfi : f' i = P) by (rewrite /f' decide_True //).
      iExists f'. iSplitR.
      { iPureIntro. intros j m Hj.
        destruct (decide (j = i)) as [-> | Hne].
        - rewrite lookup_insert in Hj. injection Hj as <-. rewrite Hfi //.
        - rewrite lookup_insert_ne // in Hj.
          rewrite -(Hext j ltac:(by eexists)). exact (Hf j m Hj). }
      rewrite (link_elem_insert I i n f' Hi) Hfi.
      rewrite -(link_elem_ext I f f' ltac:(intros j Hj; exact (Hext j Hj))).
      rewrite assoc. iFrame.
  Qed.

  Lemma fs_links_valid g I :
    fs_links g I -∗ ⌜∃ f, link_elem_ok I f /\ ✓ link_elem I f⌝.
  Proof.
    destruct (decide (I = ∅)) as [-> | Hne].
    - iIntros "_". iPureIntro. exists (fun _ => ∅). split.
      + intros j m Hj. rewrite lookup_empty in Hj. discriminate.
      + rewrite link_elem_empty. apply ucmra_unit_valid.
    - apply map_choose in Hne as (i & n & Hin).
      rewrite /fs_links /fs_link_node (big_sepM_delete _ I i n) //.
      iIntros "[(%P & %Hok & Hi) Hrest]".
      iDestruct (fs_links_gather g (delete i I) (link_elem_node i n P)
                   with "Hi Hrest") as (f) "[%Hf H]".
      iDestruct (own_valid with "H") as %Hv.
      iPureIntro.
      set (f' := fun z => if decide (z = i) then P else f z).
      assert (Hext : forall j, is_Some (delete i I !! j) -> f j = f' j).
      { intros j [m Hj]. rewrite /f'. destruct (decide (j = i)) as [-> |];
          [rewrite lookup_delete in Hj; discriminate | done]. }
      assert (Hfi : f' i = P) by (rewrite /f' decide_True //).
      exists f'. split.
      + intros j m Hj. destruct (decide (j = i)) as [-> | Hne'].
        * rewrite Hin in Hj. injection Hj as <-. rewrite Hfi //.
        * rewrite -(Hext j ltac:(eexists; rewrite lookup_delete_ne //)).
          apply (Hf j m). rewrite lookup_delete_ne //.
      + rewrite (link_elem_delete I i n f' Hin) Hfi.
        rewrite -(link_elem_ext (delete i I) f f'
                    ltac:(intros j Hj; exact (Hext j Hj))).
        exact Hv.
  Qed.

  (* ...AND THE SAME READING WITH A SPARE FRAGMENT IN HAND (durable-disk
     lane E-clauses).  [FsDurSnap.sk_links] is the family's validity
     SLACKED by one token at the root, and the commit's supplier is the
     inode region's own keep-alive token ([InodeRegion.ireg_keep]) beside
     the collected [fs_links].  Gathering the two into ONE [own] is all it
     takes; the accumulator form of the gather is what makes the empty map
     a non-case. *)
  Lemma fs_links_valid_tok g I i k :
    fs_links g I -∗ own g (link_tok_elem i k) -∗
    ⌜∃ f, link_elem_ok I f /\ ✓ (link_elem I f ⋅ link_tok_elem i k)⌝.
  Proof.
    iIntros "HI Ht".
    iDestruct (fs_links_gather g I (link_tok_elem i k) with "Ht HI")
      as (f) "[%Hf H]".
    iDestruct (own_valid with "H") as %Hv.
    iPureIntro. exists f. split; [exact Hf |]. rewrite comm. exact Hv.
  Qed.

  Lemma fs_links_alloc (I : gmap Z fs_node) (f : Z -> gmultiset (option Z)) :
    link_elem_ok I f -> ✓ link_elem I f ->
    ⊢ |==> ∃ g : gname, fs_links g I.
  Proof.
    intros Hok Hv.
    iMod (own_alloc (link_elem I f)) as (g) "H"; [done |].
    iExists g. iModIntro.
    rewrite /fs_links /fs_link_node /link_elem.
    iDestruct (big_opM_own_1 with "H") as "H".
    iApply (big_sepM_mono with "H"). intros i n Hi; simpl.
    iIntros "H". iExists (f i). iFrame. iPureIntro. exact (Hok i n Hi).
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

  (* A node with no directory entries carries no tokens and no register
     fragments, so its whole contribution to the family is its own two
     authorities. *)
  Lemma link_elem_node_no_ents (i : Z) (n : fs_node)
      (P : gmultiset (option Z)) :
    dir_entries n = ∅ ->
    link_elem_node i n P
    ≡ ({[ i := ((● (fn_nlink n) : authUR natUR), (● P : fsParUR)) ]}
       : fsLinkUR).
  Proof.
    intros He. rewrite /link_elem_node He big_opM_empty right_id
      /link_auth_elem /par_auth_elem singleton_op
      -pair_op right_id left_id //.
  Qed.

  Lemma link_elem_no_ents_lookup (I : gmap Z fs_node)
      (f : Z -> gmultiset (option Z)) (j : Z) :
    (forall i n, I !! i = Some n -> dir_entries n = ∅) ->
    link_elem I f !! j
    ≡ (fun n => ((● (fn_nlink n) : authUR natUR), (● (f j) : fsParUR)))
      <$> (I !! j).
  Proof.
    intros Hall.
    assert (Heq : link_elem I f
                  ≡ ([^op map] i ↦ n ∈ I,
                       ({[ i := ((● (fn_nlink n) : authUR natUR),
                                 (● (f i) : fsParUR)) ]} : fsLinkUR))).
    { rewrite /link_elem. apply big_opM_proper. intros i n Hi.
      exact (link_elem_node_no_ents i n (f i) (Hall i n Hi)). }
    rewrite (Heq j).
    exact (big_op_singletons_lookup I
             (fun i n => ((● (fn_nlink n) : authUR natUR),
                          (● (f i) : fsParUR))) j).
  Qed.

  Lemma link_elem_valid_no_ents (I : gmap Z fs_node) (f : Z -> gmultiset (option Z)) :
    (forall i n, I !! i = Some n -> dir_entries n = ∅) -> ✓ link_elem I f.
  Proof.
    intros Hall j. rewrite (link_elem_no_ents_lookup I f j Hall).
    destruct (I !! j) as [n |] eqn:E; [| done].
    rewrite /= Some_valid. apply pair_valid.
    split; by apply auth_auth_valid.
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
  Lemma fs_boot_alloc_at (IL IT : gmap Z fs_node) (f : Z -> gmultiset (option Z)) :
    link_elem_ok IL f -> ✓ link_elem IL f ->
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 IT
        ∗ ([∗ map] i ↦ n ∈ IT, i ↪[gt] n)
        ∗ fs_links gl IL.
  Proof.
    intros Hok Hv.
    iMod (fs_links_alloc IL f Hok Hv) as (gl) "Hl".
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

  Definition link_full_map (I : gmap Z fs_node) (f : Z -> gmultiset (option Z))
    : fsLinkUR :=
    ([^op map] i ↦ n ∈ I, link_full_elem i (fn_nlink n) (f i)).

  Definition fs_links_full (g : gname) (I : gmap Z fs_node)
      (f : Z -> gmultiset (option Z)) : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, own g (link_full_elem i (fn_nlink n) (f i)))%I.

  Global Instance fs_links_full_timeless g I f :
    Timeless (fs_links_full g I f).
  Proof. rewrite /fs_links_full. apply _. Qed.

  Lemma link_full_map_lookup (I : gmap Z fs_node) (f : Z -> gmultiset (option Z))
      (j : Z) :
    link_full_map I f !! j
    ≡ (fun n => ((● (fn_nlink n) ⋅ ◯ (fn_nlink n) : authUR natUR),
                 (● (f j) ⋅ ◯ (f j) : fsParUR))) <$> (I !! j).
  Proof.
    assert (Heq : link_full_map I f
                  ≡ ([^op map] i ↦ n ∈ I,
                       ({[ i := ((● (fn_nlink n) ⋅ ◯ (fn_nlink n)
                                  : authUR natUR),
                                 (● (f i) ⋅ ◯ (f i) : fsParUR)) ]}
                        : fsLinkUR))).
    { rewrite /link_full_map. apply big_opM_proper. intros i n Hi.
      exact (link_full_elem_singleton i (fn_nlink n) (f i)). }
    rewrite (Heq j).
    exact (big_op_singletons_lookup I
             (fun i n => ((● (fn_nlink n) ⋅ ◯ (fn_nlink n) : authUR natUR),
                          (● (f i) ⋅ ◯ (f i) : fsParUR))) j).
  Qed.

  Lemma link_full_map_valid (I : gmap Z fs_node) (f : Z -> gmultiset (option Z)) :
    ✓ link_full_map I f.
  Proof.
    intros j. rewrite (link_full_map_lookup I f j).
    destruct (I !! j) as [n |] eqn:E; [| done].
    rewrite /= Some_valid. apply pair_valid. split.
    - apply auth_both_valid_discrete. split; [apply nat_included; lia | done].
    - apply auth_both_valid_discrete.
      split; [by apply gmultiset_included | done].
  Qed.

  Lemma fs_links_full_alloc (I : gmap Z fs_node) (f : Z -> gmultiset (option Z)) :
    ⊢ |==> ∃ g : gname, fs_links_full g I f.
  Proof.
    iMod (own_alloc (link_full_map I f)) as (g) "H";
      [apply link_full_map_valid |].
    iExists g. iModIntro.
    rewrite /fs_links_full /link_full_map. by iApply big_opM_own_1.
  Qed.

  (* ...and the two ghosts allocated together, the region's way: no
     validity premise at all, because nothing is outstanding. *)
  Lemma fs_boot_alloc_full (IL IT : gmap Z fs_node) (f : Z -> gmultiset (option Z)) :
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 IT
        ∗ ([∗ map] i ↦ n ∈ IT, i ↪[gt] n)
        ∗ fs_links_full gl IL f.
  Proof.
    iMod (fs_links_full_alloc IL f) as (gl) "Hl".
    iMod (ghost_map_alloc IT) as (gt) "[Ha Hf]".
    iModIntro. iExists gl, gt. iFrame.
  Qed.

  (* THE BOOT MINT'S ALLOCATION, AT THE SLACKED ELEMENT (durable-disk lane
     E-clauses).  [FsDurSnap.sk_links] is [✓ (link_elem I ⋅ link_tok_elem
     ROOTINO 1)], and ONE [own_alloc] at that element yields the whole
     [fs_links] bundle PLUS the spare token the inode region parks as
     [InodeRegion.ireg_keep] -- so the mint never has to split a family it
     has already handed out.  The root inum is a PARAMETER: this file sits
     below [InodeRegion], and [ireg_root] is [FsImg.ROOTINO]. *)
  Lemma fs_boot_alloc_root_slack (I : gmap Z fs_node)
      (f : Z -> gmultiset (option Z)) (r : Z) :
    link_elem_ok I f -> ✓ (link_elem I f ⋅ link_tok_elem r 1%nat) ->
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 I
        ∗ ([∗ map] i ↦ n ∈ I, i ↪[gt] n)
        ∗ fs_links gl I
        ∗ own gl (link_tok_elem r 1%nat).
  Proof.
    intros Hok Hv.
    iMod (own_alloc (link_elem I f ⋅ link_tok_elem r 1%nat)) as (gl) "H";
      [done |].
    iDestruct (own_op with "H") as "[Hl Ht]".
    iMod (ghost_map_alloc I) as (gt) "[Ha Hf]".
    iModIntro. iExists gl, gt. iFrame "Ha Hf Ht".
    rewrite /fs_links /fs_link_node /link_elem.
    iDestruct (big_opM_own_1 with "Hl") as "Hl".
    iApply (big_sepM_mono with "Hl"). intros i n Hi; simpl.
    iIntros "H". iExists (f i). iFrame. iPureIntro. exact (Hok i n Hi).
  Qed.

  (* THE DEGENERATE INSTANCE, and it is what durable-disk 2c's fixed-layer
     plumbing mints: two fresh gnames with an EMPTY top map and an empty
     link family.  It exists because [RiscvPtsto.fs_dur_names] -- the
     bundle [Gamma_D]'s two gnames ride the fixed layer in -- has to be
     produced inside adequacy's own update, and the machine layer must not
     name a file-system camera.  The IMAGE's instance is
     [fs_boot_alloc_at]; this is the same lemma at [I = empty]. *)
  Lemma fs_boot_alloc_empty :
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 (∅ : gmap Z fs_node) ∗ fs_links gl ∅.
  Proof.
    iMod (fs_boot_alloc_at ∅ ∅ (fun _ => ∅)) as (gl gt) "(Ha & _ & Hl)".
    { intros i n Hi. rewrite lookup_empty in Hi. discriminate. }
    { apply link_elem_valid_no_ents.
      intros i n Hi. rewrite lookup_empty in Hi. discriminate. }
    iModIntro. iExists gl, gt. iFrame.
  Qed.

  Lemma fs_boot_alloc (I : gmap Z fs_node) (f : Z -> gmultiset (option Z)) :
    link_elem_ok I f -> ✓ link_elem I f ->
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 I
        ∗ ([∗ map] i ↦ n ∈ I, i ↪[gt] n)
        ∗ fs_links gl I.
  Proof. exact (fs_boot_alloc_at I I f). Qed.

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
    iDestruct (fs_links_valid with "HDl") as %(f & Hok & Hv).
    iMod (fs_links_alloc (fss_inodes S) f Hok Hv) as (gl) "HLl".
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
    iDestruct (fs_links_valid with "HDl") as %(f & Hok & Hv).
    iMod (fs_links_alloc (fss_inodes S) f Hok Hv) as (gl) "HLl".
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
