(* FsState.v -- the file system as ONE nested separation-logic predicate,
   at either view.

   Design of record: claude-notes/design/fs-state.md sections 1, 2 and 4.
   Stage 2a of claude-notes/projects/durable-disk.md.  The pieces:

     FsStateDefs.v    the view record [Γ], [byte_range], [blk_owned]
     FsStateLink.v    the link-counting RA
     FsStateInode.v   [rec_owned], [ind_owned], [inode_owned]
     FsStateBitmap.v  [free_bitmap]
     FsState.v        [sb_owned], [fs_inodes], [fs_state], [fs_footprint]

   THE ONE [∗]-ITERATION is [fs_inodes]; there is NO pure clause at this
   level or at [fs_state]'s (fs-state.md section 2, last bullet).  The
   abstraction is a SET of inodes, some of which decode as directories:
   there is no tree, no reachability, no "used set", no completeness clause,
   and nothing anywhere states a fact about more than one inode.

   [fs_state] TAKES A DFRAC (durable-disk EV-X): every BYTE of the file
   system rides at that share and the ghost column -- the link authority,
   the type register, a directory's entry tokens -- stays WHOLE.  It is
   written at [FsStateDefs.gamma_q Γ dq], the view whose [fsΦ] is pinned at
   [dq], so there is no parallel hierarchy of [_q] definitions and
   [fs_state Γ (DfracOwn 1) S] is the old predicate by [reflexivity]
   ([fs_state_1]).

   THE MINT IS THE TRANSPORT ([FsDurXfer.fs_state_xfer]), which ALLOCATES
   the target's byte map at the flattening of the source's own runs.
   [fs_state_split] factors [fs_state] into the Φ-only [fs_footprint] (at
   the share) and the Φ-free [fs_ghost] (whole), which is what makes that
   possible.  The link family's VALIDITY -- exactly "#tokens ≤ nlink at
   every inum", the one whole-state fact in the design -- is READ OFF the
   source instance's own [own] by [fs_links_valid]; it is never proved and
   never maintained. *)

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
Require Import FsTree.
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

(* ------------------------------------------------------------------ *)
(*  1a.  THE GEOMETRY -- WHAT IT MEANS FOR THE MAP TO BE A REGION      *)
(*       (durable-disk lane H5)                                        *)
(*                                                                     *)
(*  [inode_local] says what ONE inode is; these four say how the inode *)
(*  MAP and the SUPERBLOCK fit together, and they are the last thing a *)
(*  consumer of a file system needs that no per-inode clause gives:    *)
(*                                                                     *)
(*  - [fg_sbok] -- the superblock's own layout ([FsImg.fs_sb_ok]).     *)
(*    [sb_owned]'s parse says the bytes DECODE to [fss_sb]; it does    *)
(*    not say the fields make sense, and nothing about the resources   *)
(*    can (an all-zero block parses).                                  *)
(*  - [fg_reg] / [fg_regdom] -- the named inums are EXACTLY the        *)
(*    region's.  A [ghost_map] authority may hold entries no fragment  *)
(*    names and a [∗] over a map says nothing about which keys are     *)
(*    there, so this is a fact about the map, not about the ghosts.    *)
(*  - [fg_dirloc] -- every directory's entries point INSIDE the        *)
(*    region, its dots are at records 0 and 1, and an orphan holds     *)
(*    only dots.  It is per-inode but needs the region's WIDTH, which  *)
(*    [inode_local i n] (an inum and a node and nothing else) cannot   *)
(*    see; [IcacheEscrow.ipool_alloc] and [ic_loaded] take all three.  *)
(*                                                                     *)
(*  THEY LIVE IN [fs_state] (as its last, pure conjunct) RATHER THAN   *)
(*  ON THE SNAPSHOT, because they are true of a FILE SYSTEM and not of *)
(*  a committed view: stated here they are a READING at BOTH instances *)
(*  ([fs_state_geom]) and the durable snapshot carries nothing about   *)
(*  them.  What the snapshot still has to carry is only what relates   *)
(*  the state to [D] ([FsDurSnap.snap_shape]).                         *)
(* ------------------------------------------------------------------ *)

(* the region's width off [S]'s own superblock: mkfs rounds [ninodes] up to
   a whole inode block, so the region is [ninodes/16 + 1] blocks and the
   inum space is [16 *] that.  It is the width [FsDurSnap.sk_regdom] is
   stated at and the one [sk_dirloc]'s [DirView.dir_ok] is bounded by; at
   the boot configuration it IS [IcacheRef.icfg_nib]
   ([FirstTok.col_geom_of_config]'s own hypothesis). *)
Definition fs_nib (S : fs_state_rec) : nat :=
  Z.to_nat (sb_ninodes (fss_sb S) / 16 + 1).

Record fs_geom (S : fs_state_rec) : Prop := MkFsGeom {
  fg_sbok   : fs_sb_ok (fss_sb S);
  fg_reg    : forall i n, fss_inodes S !! i = Some n ->
                0 <= i /\ i `div` 16 < sb_bmapstart (fss_sb S)
                                       - sb_inodestart (fss_sb S);
  fg_regdom : forall i, 0 <= i < 16 * (sb_ninodes (fss_sb S) / 16 + 1) ->
                is_Some (fss_inodes S !! i);
  fg_dirloc : forall i n, fss_inodes S !! i = Some n ->
                node_dir_local i (fs_nib S) n;
}.

Global Arguments fg_sbok {_} _.
Global Arguments fg_reg {_} _.
Global Arguments fg_regdom {_} _.
Global Arguments fg_dirloc {_} _.

(* THE INUM BOUND, DERIVED.  [fg_reg] puts a named inum's record block
   inside the region and [FsImg.sbo_ushort] caps the region's inum space at
   [2^16], so no named inum can leave a [ushort] -- let alone [2^32].  This
   used to be a clause of its own ([snap_bytes]' [sk_inum]). *)
Lemma fs_geom_inum (S : fs_state_rec) (i : Z) (n : fs_node) :
  fs_geom S -> fss_inodes S !! i = Some n -> 0 <= i < 2 ^ 32.
Proof.
  intros Hg Hi.
  pose proof (fg_reg Hg i n Hi) as [Hi0 Hlt].
  pose proof (fg_sbok Hg) as Hsb.
  pose proof (sbo_bmapstart _ Hsb) as Hbm.
  pose proof (sbo_ushort _ Hsb) as Hus.
  pose proof (sbo_ninodes _ Hsb) as Hni. unfold ROOTINO in Hni.
  assert (Hdiv : 0 <= sb_ninodes (fss_sb S) / 16)
    by (apply Z.div_pos; lia).
  pose proof (Z.div_mod i 16 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as Hmb.
  lia.
Qed.

(* [fg_regdom] read below [ninodes]: mkfs rounds the count up to a whole
   inode block, so the region's inum space contains it. *)
Lemma fs_geom_dom (S : fs_state_rec) (i : Z) :
  fs_geom S -> 0 <= i < sb_ninodes (fss_sb S) -> is_Some (fss_inodes S !! i).
Proof.
  intros Hg Hi. apply (fg_regdom Hg).
  pose proof (Z.div_mod (sb_ninodes (fss_sb S)) 16 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (sb_ninodes (fss_sb S)) 16 ltac:(lia)).
  lia.
Qed.

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

  (* ---------------------------------------------------------------- *)
  (*  2a.  THE PREDICATE TAKES A SHARE (durable-disk EV-X)              *)
  (*                                                                    *)
  (*  [fs_state Γ dq S] is the file system with EVERY BYTE at [dq] and   *)
  (*  the ghost column WHOLE.  It is written at the constant-share view  *)
  (*  [FsStateDefs.gamma_q Γ dq] rather than through a parallel          *)
  (*  hierarchy of [_q] definitions, and that is the whole trick: a      *)
  (*  view's [fsΦ] is what every byte shape below reads, so pinning it   *)
  (*  at [dq] moves the record, the data blocks, the indirect block,     *)
  (*  the superblock block, the bitmap block and the free pool together  *)
  (*  and leaves [γlink] and [γtop] -- hence [FsStateInode.inode_ghost]  *)
  (*  (the link authority, the type register and the entry tokens) --    *)
  (*  LITERALLY UNCHANGED ([gamma_q_inode_ghost] is [reflexivity]).      *)
  (*                                                                    *)
  (*  WHY THE AUTHORITIES DO NOT SPLIT.  [link_auth] is an [auth] whose  *)
  (*  fragments are the entry tokens: half of it is not half a file      *)
  (*  system, it is an unusable element, and the mint allocates the      *)
  (*  family from the SOURCE'S OWN element ([fs_links_valid_tok]) at any *)
  (*  share of the bytes.  Same for the abstract map's fragments, which  *)
  (*  do split ([top_frag_q]) but are not part of [fs_state] at all --   *)
  (*  they ride with the era's escrow arms and with a snapshot's         *)
  (*  [FsDurSnap.fs_snap], never inside the predicate.                   *)
  (*                                                                    *)
  (*  [fs_state Γ (DfracOwn 1) S] IS the old fraction-1 predicate:       *)
  (*  [byte_range] hands [DfracOwn 1] down and the constant view then    *)
  (*  ignores it, so [fs_state_1] below is [reflexivity] and every       *)
  (*  consumer of the old form moved by a SWEEP.                         *)
  (*                                                                    *)
  (*  LAST, so no destructuring pattern above the first three conjuncts  *)
  (*  moves (durable-notes.md, the rule on a new conjunct going into a   *)
  (*  predicate forty proofs destructure: put it LAST).                  *)
  (* ---------------------------------------------------------------- *)

  Definition fs_state Γ (dq : dfrac) S : iProp Σ :=
    (sb_owned (gamma_q Γ dq) (fss_sb S) (fss_sbb S)
     ∗ fs_inodes (gamma_q Γ dq) (fss_sb S) (fss_inodes S)
     ∗ free_bitmap (gamma_q Γ dq) (fss_sb S) (fss_used S)
     ∗ ⌜fs_geom S⌝)%I.

  (* THE ONE-LINE BRIDGE. *)
  Lemma fs_state_1 Γ S :
    fs_state Γ (DfracOwn 1) S
    ⊣⊢ (sb_owned Γ (fss_sb S) (fss_sbb S)
        ∗ fs_inodes Γ (fss_sb S) (fss_inodes S)
        ∗ free_bitmap Γ (fss_sb S) (fss_used S)
        ∗ ⌜fs_geom S⌝).
  Proof. reflexivity. Qed.

  (* ...AND THE OTHER WAY ROUND: the predicate at a share IS the predicate
     at FULL share over the constant-share VIEW, because [gamma_q] is
     idempotent in its second argument ([gamma_q (gamma_q Γ dq) (DfracOwn 1)]
     and [gamma_q Γ dq] are the same term).  That is what lets every
     Gamma-generic lemma about the fraction-1 predicate -- the runs
     correspondence of [FsDurXfer] above all -- be READ at a share with no
     new proof (durable-disk EV-X). *)
  Lemma fs_state_gq Γ dq S :
    fs_state Γ dq S = fs_state (gamma_q Γ dq) (DfracOwn 1) S.
  Proof. reflexivity. Qed.

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

  Global Instance fs_state_timeless `{!GTimeless Γ} dq S :
    Timeless (fs_state Γ dq S).
  Proof. rewrite /fs_state. apply _. Qed.

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

  Definition fs_footprint Γ (dq : dfrac) S : iProp Σ :=
    (blk_owned (gamma_q Γ dq) SB_BNO (fss_sbb S)
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S,
          inode_phi (gamma_q Γ dq) (fss_sb S) i n)
     ∗ blk_owned (gamma_q Γ dq) (sb_bmapstart (fss_sb S))
         (bm_bytes BSIZE (fss_used S))
     ∗ free_pool (gamma_q Γ dq) (sb_size (fss_sb S)) (fss_used S))%I.

  Lemma fs_footprint_1 Γ S :
    fs_footprint Γ (DfracOwn 1) S
    ⊣⊢ (blk_owned Γ SB_BNO (fss_sbb S)
        ∗ ([∗ map] i ↦ n ∈ fss_inodes S, inode_phi Γ (fss_sb S) i n)
        ∗ blk_owned Γ (sb_bmapstart (fss_sb S)) (bm_bytes BSIZE (fss_used S))
        ∗ free_pool Γ (sb_size (fss_sb S)) (fss_used S)).
  Proof. reflexivity. Qed.

  Lemma fs_footprint_gq Γ dq S :
    fs_footprint Γ dq S = fs_footprint (gamma_q Γ dq) (DfracOwn 1) S.
  Proof. reflexivity. Qed.

  Definition fs_ghost Γ S : iProp Σ :=
    (⌜fs_parse_sb (fun _ => fss_sbb S) = Some (fss_sb S)⌝
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, inode_ghost Γ i n)
     ∗ ⌜fs_geom S⌝)%I.

  Global Instance fs_footprint_timeless `{!GTimeless Γ} dq S :
    Timeless (fs_footprint Γ dq S).
  Proof. rewrite /fs_footprint. apply _. Qed.

  Global Instance fs_ghost_timeless Γ S : Timeless (fs_ghost Γ S).
  Proof. rewrite /fs_ghost. apply _. Qed.

  (* the footprint does not read [γlink] or [γtop] *)
  Lemma fs_footprint_gname Γ g t dq S :
    fs_footprint Γ dq S ⊣⊢ fs_footprint (MkFsView (fsΦ Γ) g t) dq S.
  Proof. done. Qed.

  (* SHEDDING A SHARE (durable-disk EV-X).  The commit's collection meets
     the metadata objects and the region's records at fraction 1 and each
     inode's data leg at three quarters, so it sheds the whole ones down to
     the uniform share the transport takes.  It is stated in ONE direction:
     the free pool's element hides its bytes under an existential, so two
     halves of a pool row cannot be rejoined without an agreement law, and
     nothing ever needs to. *)
  Lemma fs_footprint_shed Γ (Hfr : phi_frac Γ) (q1 q2 : Qp) S :
    fs_footprint Γ (DfracOwn (q1 + q2)) S
    ⊢ fs_footprint Γ (DfracOwn q1) S ∗ fs_footprint Γ (DfracOwn q2) S.
  Proof.
    pose proof (gamma_q_shed Γ Hfr q1 q2) as Hs.
    rewrite /fs_footprint. iIntros "(Hsb & Hin & Hbm & Hpool)".
    iDestruct (blk_owned_shed _ _ _ Hs with "Hsb") as "[Hsb1 Hsb2]".
    iDestruct (blk_owned_shed _ _ _ Hs with "Hbm") as "[Hbm1 Hbm2]".
    iDestruct (free_pool_shed _ _ _ Hs with "Hpool") as "[Hp1 Hp2]".
    iAssert ([∗ map] i ↦ n ∈ fss_inodes S,
               inode_phi (gamma_q Γ (DfracOwn q1)) (fss_sb S) i n
               ∗ inode_phi (gamma_q Γ (DfracOwn q2)) (fss_sb S) i n)%I
      with "[Hin]" as "Hin".
    { iApply (big_sepM_impl with "Hin"). iIntros "!>" (i n Hi) "H".
      iApply (inode_phi_shed _ _ _ Hs with "H"). }
    rewrite big_sepM_sep. iDestruct "Hin" as "[Hin1 Hin2]".
    iSplitL "Hsb1 Hin1 Hbm1 Hp1"; iFrame.
  Qed.


  (* [fs_footprint_q] -- EV stage 5's footprint with a share PER INODE,
     existentially bound with only "the double is invalid" on it -- is
     DELETED at EV-X.  [fs_state] takes a dfrac now, so the commit collects
     at ONE uniform share (three quarters: every escrow arm can supply it
     and every fraction-1 owner can shed to it) and what quiescence yields
     is [fs_footprint Γ (DfracOwn (3/4)) S] on the nose
     ([FsCollectAll.col_hand_footprint_acc]).  With it went
     [FsStateInode.inode_phi_q] and [FsDurXfer]'s whole per-run share
     vocabulary ([phi_runs_ex] and friends). *)

  Lemma fs_state_split Γ dq S :
    fs_state Γ dq S ⊣⊢ fs_footprint Γ dq S ∗ fs_ghost Γ S.
  Proof.
    rewrite /fs_state /fs_footprint /fs_ghost /sb_owned /fs_inodes
            /free_bitmap /free_bitmap_at /inode_owned.
    rewrite (big_sepM_proper
               (fun i n => inode_phi (gamma_q Γ dq) (fss_sb S) i n
                           ∗ inode_ghost (gamma_q Γ dq) i n)%I
               (fun i n => inode_phi (gamma_q Γ dq) (fss_sb S) i n
                           ∗ inode_ghost Γ i n)%I);
      last first.
    { intros i n _. rewrite gamma_q_inode_ghost //. }
    rewrite big_sepM_sep.
    iSplit.
    - iIntros "((Hsb & %Hp) & [Hphi Hg] & (Hbm & Hpool) & %Hgeo)". by iFrame.
    - iIntros "((Hsb & Hphi & Hbm & Hpool) & %Hp & Hg & %Hgeo)". by iFrame.
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
  Definition link_choice : Type :=
    Z -> gset fname * (ity * (fname -> ity)).

  Definition lc_D (f : link_choice) (i : Z) : gset fname := (f i).1.
  Definition lc_v (f : link_choice) (i : Z) : ity := (f i).2.1.
  Definition lc_tyf (f : link_choice) (i : Z) : fname -> ity := (f i).2.2.

  Definition link_elem_ok (I : gmap Z fs_node) (f : link_choice) : Prop :=
    forall i n, I !! i = Some n ->
      node_ent_ok i n (lc_D f i) (lc_v f i) (lc_tyf f i).

  Definition link_elem (I : gmap Z fs_node) (f : link_choice) : fsLinkUR :=
    ([^op map] i ↦ n ∈ I, link_elem_node i n (lc_v f i) (lc_tyf f i)).

  (* ONE inode's whole contribution, under the existential its register
     authority is bound by.  Named, because it is what the commit's
     collection produces one inum at a time. *)
  Definition fs_link_node (g : gname) (i : Z) (n : fs_node) : iProp Σ :=
    (∃ D v tyf, ⌜node_ent_ok i n D v tyf⌝
                ∗ own g (link_elem_node i n v tyf))%I.

  Global Instance fs_link_node_timeless g i n : Timeless (fs_link_node g i n).
  Proof. rewrite /fs_link_node. apply _. Qed.

  Definition fs_links (g : gname) (I : gmap Z fs_node) : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, fs_link_node g i n)%I.

  (* [link_elem] only ever reads [f] inside [I]'s domain *)
  Lemma link_elem_ext (I : gmap Z fs_node) (f g : link_choice) :
    (forall i, is_Some (I !! i) -> f i = g i) ->
    link_elem I f ≡ link_elem I g.
  Proof.
    intros Hfg. rewrite /link_elem. apply big_opM_proper.
    intros i n Hi. rewrite /lc_v /lc_tyf (Hfg i ltac:(by eexists)) //.
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

  Lemma link_elem_empty (f : link_choice) : link_elem ∅ f = ε.
  Proof. rewrite /link_elem big_opM_empty //. Qed.

  Lemma link_elem_insert (I : gmap Z fs_node) (i : Z) (n : fs_node)
      (f : link_choice) :
    I !! i = None ->
    link_elem (<[i := n]> I) f ≡ link_elem_node i n (lc_v f i) (lc_tyf f i) ⋅ link_elem I f.
  Proof. intros Hi. rewrite /link_elem big_opM_insert //. Qed.

  Lemma link_elem_delete (I : gmap Z fs_node) (i : Z) (n : fs_node)
      (f : link_choice) :
    I !! i = Some n ->
    link_elem I f ≡ link_elem_node i n (lc_v f i) (lc_tyf f i) ⋅ link_elem (delete i I) f.
  Proof. intros Hi. rewrite /link_elem (big_opM_delete _ I i n) //. Qed.

  Lemma link_elem_ok_ext (I : gmap Z fs_node) (f g : link_choice) :
    (forall i, is_Some (I !! i) -> f i = g i) ->
    link_elem_ok I f -> link_elem_ok I g.
  Proof.
    intros Hfg Hok i n Hi. rewrite /lc_D /lc_v /lc_tyf.
    rewrite -(Hfg i ltac:(by eexists)). exact (Hok i n Hi).
  Qed.

  Definition fs_pure S : iProp Σ :=
    (⌜fs_parse_sb (fun _ => fss_sbb S) = Some (fss_sb S)⌝
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, ⌜inode_local i n⌝)
     ∗ ⌜fs_geom S⌝)%I.

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
               (fun i n => (∃ D v tyf, ⌜node_ent_ok i n D v tyf⌝
                                 ∗ own (γlink Γ) (link_elem_node i n v tyf))
                           ∗ ⌜inode_local i n⌝)%I);
      last first.
    { intros i n _. rewrite inode_ghost_iff //. }
    rewrite big_sepM_sep.
    iSplit.
    - iIntros "(%Hp & (Hl & Hc) & %Hgeo)". by iFrame.
    - iIntros "(Hl & %Hp & Hc & %Hgeo)". by iFrame.
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
    - iIntros "Hx _". iExists (fun _ => (∅, (TFile, fun _ => TFile))). iSplitR.
      { iPureIntro. intros j m Hj. rewrite lookup_empty in Hj. discriminate. }
      rewrite link_elem_empty right_id. iFrame.
    - rewrite /fs_links /fs_link_node big_sepM_insert //.
      iIntros "Hx [(%DD & %vv & %P & %Hok & Hi) Hrest]".
      iDestruct (own_op with "[$Hx $Hi]") as "Hxi".
      iDestruct (IH (x ⋅ link_elem_node i n vv P) with "Hxi Hrest")
        as (f) "[%Hf Hr]".
      set (f' := fun z => if decide (z = i) then (DD, (vv, P)) else f z).
      assert (Hext : forall j, is_Some (I !! j) -> f j = f' j).
      { intros j [m Hj]. rewrite /f'. destruct (decide (j = i)) as [-> |];
          [rewrite Hi in Hj; discriminate | done]. }
      assert (Hfi : f' i = (DD, (vv, P))) by (rewrite /f' decide_True //).
      iExists f'. iSplitR.
      { iPureIntro. intros j m Hj.
        destruct (decide (j = i)) as [-> | Hne].
        - rewrite lookup_insert in Hj. injection Hj as <-.
          rewrite /lc_D /lc_v /lc_tyf Hfi //.
        - rewrite lookup_insert_ne // in Hj.
          rewrite /lc_D /lc_v /lc_tyf -(Hext j ltac:(by eexists)).
          exact (Hf j m Hj). }
      rewrite (link_elem_insert I i n f' Hi) /lc_v /lc_tyf Hfi.
      rewrite -(link_elem_ext I f f' ltac:(intros j Hj; exact (Hext j Hj))).
      rewrite assoc. iFrame.
  Qed.

  Lemma fs_links_valid g I :
    fs_links g I -∗ ⌜∃ f, link_elem_ok I f /\ ✓ link_elem I f⌝.
  Proof.
    destruct (decide (I = ∅)) as [-> | Hne].
    - iIntros "_". iPureIntro. exists (fun _ => (∅, (TFile, fun _ => TFile))). split.
      + intros j m Hj. rewrite lookup_empty in Hj. discriminate.
      + rewrite link_elem_empty. apply ucmra_unit_valid.
    - apply map_choose in Hne as (i & n & Hin).
      rewrite /fs_links /fs_link_node (big_sepM_delete _ I i n) //.
      iIntros "[(%DD & %vv & %P & %Hok & Hi) Hrest]".
      iDestruct (fs_links_gather g (delete i I) (link_elem_node i n vv P)
                   with "Hi Hrest") as (f) "[%Hf H]".
      iDestruct (own_valid with "H") as %Hv.
      iPureIntro.
      set (f' := fun z => if decide (z = i) then (DD, (vv, P)) else f z).
      assert (Hext : forall j, is_Some (delete i I !! j) -> f j = f' j).
      { intros j [m Hj]. rewrite /f'. destruct (decide (j = i)) as [-> |];
          [rewrite lookup_delete in Hj; discriminate | done]. }
      assert (Hfi : f' i = (DD, (vv, P))) by (rewrite /f' decide_True //).
      exists f'. split.
      + intros j m Hj. destruct (decide (j = i)) as [-> | Hne'].
        * rewrite Hin in Hj. injection Hj as <-.
          rewrite /lc_D /lc_v /lc_tyf Hfi //.
        * rewrite /lc_D /lc_v /lc_tyf
            -(Hext j ltac:(eexists; rewrite lookup_delete_ne //)).
          apply (Hf j m). rewrite lookup_delete_ne //.
      + rewrite (link_elem_delete I i n f' Hin) /lc_v /lc_tyf Hfi.
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
  Lemma fs_links_valid_tok g I i (v : ity) :
    fs_links g I -∗ own g (link_tok_elem i v) -∗
    ⌜∃ f, link_elem_ok I f /\ ✓ (link_elem I f ⋅ link_tok_elem i v)⌝.
  Proof.
    iIntros "HI Ht".
    iDestruct (fs_links_gather g I (link_tok_elem i v) with "Ht HI")
      as (f) "[%Hf H]".
    iDestruct (own_valid with "H") as %Hv.
    iPureIntro. exists f. split; [exact Hf |]. rewrite comm. exact Hv.
  Qed.

  Lemma fs_links_alloc (I : gmap Z fs_node) (f : link_choice) :
    link_elem_ok I f -> ✓ link_elem I f ->
    ⊢ |==> ∃ g : gname, fs_links g I.
  Proof.
    intros Hok Hv.
    iMod (own_alloc (link_elem I f)) as (g) "H"; [done |].
    iExists g. iModIntro.
    rewrite /fs_links /fs_link_node /link_elem.
    iDestruct (big_opM_own_1 with "H") as "H".
    iApply (big_sepM_mono with "H"). intros i n Hi; simpl.
    iIntros "H". iExists (lc_D f i), (lc_v f i), (lc_tyf f i). iFrame.
    iPureIntro. exact (Hok i n Hi).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  5b. THE BOOT ALLOCATION (B3)                                      *)
  (*                                                                    *)
  (*  Stage 4's mint took the family's validity OFF the                  *)
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
  Lemma link_elem_node_no_ents (i : Z) (n : fs_node) (v : ity)
      (tyf : fname -> ity) :
    dir_entries n = ∅ ->
    link_elem_node i n v tyf
    ≡ ({[ i := (● (link_reps (fn_mult n) v) : fsLinkElemUR) ]}
       : fsLinkUR).
  Proof.
    intros He. rewrite /link_elem_node He big_opM_empty right_id
      /link_auth_elem //.
  Qed.

  Lemma link_elem_no_ents_lookup (I : gmap Z fs_node)
      (f : link_choice) (j : Z) :
    (forall i n, I !! i = Some n -> dir_entries n = ∅) ->
    link_elem I f !! j
    ≡ (fun n => (● (link_reps (fn_mult n) (lc_v f j)) : fsLinkElemUR))
      <$> (I !! j).
  Proof.
    intros Hall.
    assert (Heq : link_elem I f
                  ≡ ([^op map] i ↦ n ∈ I,
                       ({[ i := (● (link_reps (fn_mult n) (lc_v f i))
                                 : fsLinkElemUR) ]} : fsLinkUR))).
    { rewrite /link_elem. apply big_opM_proper. intros i n Hi.
      exact (link_elem_node_no_ents i n (lc_v f i) (lc_tyf f i)
               (Hall i n Hi)). }
    rewrite (Heq j).
    exact (big_op_singletons_lookup I
             (fun i n => (● (link_reps (fn_mult n) (lc_v f i))
                          : fsLinkElemUR)) j).
  Qed.

  Lemma link_elem_valid_no_ents (I : gmap Z fs_node) (f : link_choice) :
    (forall i n, I !! i = Some n -> dir_entries n = ∅) -> ✓ link_elem I f.
  Proof.
    intros Hall j. rewrite (link_elem_no_ents_lookup I f j Hall).
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
  Lemma fs_boot_alloc_at (IL IT : gmap Z fs_node) (f : link_choice) :
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

  Definition link_full_map (I : gmap Z fs_node) (fv : Z -> ity) : fsLinkUR :=
    ([^op map] i ↦ n ∈ I, link_full_elem i (fn_mult n) (fv i)).

  Definition fs_links_full (g : gname) (I : gmap Z fs_node) (fv : Z -> ity)
    : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, own g (link_full_elem i (fn_mult n) (fv i)))%I.

  Global Instance fs_links_full_timeless g I fv :
    Timeless (fs_links_full g I fv).
  Proof. rewrite /fs_links_full. apply _. Qed.

  Lemma link_full_map_lookup (I : gmap Z fs_node) (fv : Z -> ity) (j : Z) :
    link_full_map I fv !! j
    ≡ (fun n => (● (link_reps (fn_mult n) (fv j))
                 ⋅ ◯ (link_reps (fn_mult n) (fv j)) : fsLinkElemUR))
      <$> (I !! j).
  Proof.
    assert (Heq : link_full_map I fv
                  ≡ ([^op map] i ↦ n ∈ I,
                       ({[ i := (● (link_reps (fn_mult n) (fv i))
                                 ⋅ ◯ (link_reps (fn_mult n) (fv i))
                                 : fsLinkElemUR) ]} : fsLinkUR))).
    { rewrite /link_full_map. apply big_opM_proper. intros i n Hi.
      exact (link_full_elem_singleton i (fn_mult n) (fv i)). }
    rewrite (Heq j).
    exact (big_op_singletons_lookup I
             (fun i n => (● (link_reps (fn_mult n) (fv i))
                          ⋅ ◯ (link_reps (fn_mult n) (fv i))
                          : fsLinkElemUR)) j).
  Qed.

  Lemma link_full_map_valid (I : gmap Z fs_node) (fv : Z -> ity) :
    ✓ link_full_map I fv.
  Proof.
    intros j. rewrite (link_full_map_lookup I fv j).
    destruct (I !! j) as [n |] eqn:E; [| done].
    rewrite /= Some_valid. apply auth_both_valid_discrete.
    split; [by apply gmultiset_included | done].
  Qed.

  Lemma fs_links_full_alloc (I : gmap Z fs_node) (fv : Z -> ity) :
    ⊢ |==> ∃ g : gname, fs_links_full g I fv.
  Proof.
    iMod (own_alloc (link_full_map I fv)) as (g) "H";
      [apply link_full_map_valid |].
    iExists g. iModIntro.
    rewrite /fs_links_full /link_full_map. by iApply big_opM_own_1.
  Qed.

  (* ...and the two ghosts allocated together, the region's way: no
     validity premise at all, because nothing is outstanding. *)
  Lemma fs_boot_alloc_full (IL IT : gmap Z fs_node) (fv : Z -> ity) :
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 IT
        ∗ ([∗ map] i ↦ n ∈ IT, i ↪[gt] n)
        ∗ fs_links_full gl IL fv.
  Proof.
    iMod (fs_links_full_alloc IL fv) as (gl) "Hl".
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
      (f : link_choice) (r : Z) (v : ity) :
    link_elem_ok I f -> ✓ (link_elem I f ⋅ link_tok_elem r v) ->
    ⊢ |==> ∃ gl gt : gname,
        ghost_map_auth gt 1 I
        ∗ ([∗ map] i ↦ n ∈ I, i ↪[gt] n)
        ∗ fs_links gl I
        ∗ own gl (link_tok_elem r v).
  Proof.
    intros Hok Hv.
    iMod (own_alloc (link_elem I f ⋅ link_tok_elem r v)) as (gl) "H";
      [done |].
    iDestruct (own_op with "H") as "[Hl Ht]".
    iMod (ghost_map_alloc I) as (gt) "[Ha Hf]".
    iModIntro. iExists gl, gt. iFrame "Ha Hf Ht".
    rewrite /fs_links /fs_link_node /link_elem.
    iDestruct (big_opM_own_1 with "Hl") as "Hl".
    iApply (big_sepM_mono with "Hl"). intros i n Hi; simpl.
    iIntros "H". iExists (lc_D f i), (lc_v f i), (lc_tyf f i). iFrame.
    iPureIntro. exact (Hok i n Hi).
  Qed.

  Lemma fs_boot_alloc (I : gmap Z fs_node) (f : link_choice) :
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
  Lemma fs_state_to Γ dq S :
    fs_state Γ dq S -∗
      fs_footprint Γ dq S ∗ fs_links (γlink Γ) (fss_inodes S) ∗ fs_pure S.
  Proof.
    rewrite {1}fs_state_split fs_ghost_split. iIntros "($ & $ & $)".
  Qed.

  Lemma fs_state_of Γ dq S :
    fs_footprint Γ dq S -∗ fs_links (γlink Γ) (fss_inodes S) -∗ fs_pure S -∗
    fs_state Γ dq S.
  Proof.
    rewrite fs_state_split fs_ghost_split. iIntros "H1 H2 H3". iFrame.
  Qed.

  (* THE GEOMETRY IS A READING, AT EITHER INSTANCE (durable-disk lane H5).
     Nothing is spent -- the conclusion is pure -- so a snapshot's consumer
     and a commit's collection read it the same way. *)
  Lemma fs_state_geom Γ dq S : fs_state Γ dq S -∗ ⌜fs_geom S⌝.
  Proof. rewrite /fs_state. iIntros "(_ & _ & _ & $)". Qed.

  Lemma fs_pure_geom S : fs_pure S -∗ ⌜fs_geom S⌝.
  Proof. rewrite /fs_pure. iIntros "(_ & _ & $)". Qed.

  (* ---------------------------------------------------------------- *)
  (*  6.  THE MINT IS THE TRANSPORT, AND IT LIVES IN [FsDurXfer]        *)
  (*                                                                    *)
  (*  Stage 4's [fs_state_mint] / [fs_view_mint] -- which took the       *)
  (*  target's footprint AS A PREMISE and only moved the ghost half --   *)
  (*  are RETIRED at EV-X.  They never acquired a caller: the real mint  *)
  (*  ALLOCATES the target's byte map at the flattening of the source's  *)
  (*  own runs ([FsDurXfer.fs_state_xfer]), so nobody ever has a         *)
  (*  footprint at the fresh view to hand in.  [fs_state_to] /           *)
  (*  [fs_state_of] above are the factoring they were built out of and   *)
  (*  the transport uses those directly.                                *)
  (* ---------------------------------------------------------------- *)

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

  (* THE RETAG OWES THE NEW NODE'S DIRECTORY CLAUSES (durable-disk lane
     H5): [fs_geom]'s first three rows are about the superblock and the
     map's DOMAIN, which an [insert] at a key already there does not move,
     but [fg_dirloc] is about the node's CONTENT.  Every mover in the tree
     has it -- it is what [IcacheEscrow]'s deposit arms re-prove -- so the
     wand takes it. *)
  Lemma fs_state_inode_acc Γ dq S i n :
    fss_inodes S !! i = Some n ->
    fs_state Γ dq S ⊢
      inode_owned (gamma_q Γ dq) (fss_sb S) i n
      ∗ (∀ n', ⌜node_dir_local i (fs_nib S) n'⌝ -∗
               inode_owned (gamma_q Γ dq) (fss_sb S) i n'
                    -∗ fs_state Γ dq (MkFsS (fss_sb S) (fss_sbb S)
                                            (<[i := n']> (fss_inodes S))
                                            (fss_used S))).
  Proof.
    intros Hi. rewrite /fs_state.
    iIntros "(Hsb & Hin & Hbm & %Hgeo)".
    iDestruct (fs_inodes_acc _ _ _ i n Hi with "Hin") as "[$ Hin]".
    iIntros (n') "%Hdl Hn". iFrame "Hsb Hbm".
    iSplitL; [by iApply "Hin" |]. iPureIntro.
    destruct Hgeo as [Hsbok Hreg Hdom Hdlo]. split; simpl.
    - exact Hsbok.
    - intros j m Hj. destruct (decide (j = i)) as [-> | Hne].
      + exact (Hreg i n Hi).
      + rewrite lookup_insert_ne // in Hj. exact (Hreg j m Hj).
    - intros j Hj. destruct (Hdom j Hj) as [m Hm].
      destruct (decide (j = i)) as [-> | Hne].
      * exists n'. by rewrite lookup_insert.
      * exists m. by rewrite lookup_insert_ne.
    - intros j m Hj. destruct (decide (j = i)) as [-> | Hne].
      + rewrite lookup_insert in Hj. injection Hj as <-. exact Hdl.
      + rewrite lookup_insert_ne // in Hj. exact (Hdlo j m Hj).
  Qed.

End FsState.

Global Typeclasses Opaque sb_owned fs_inodes fs_state fs_footprint fs_ghost
                         fs_links fs_pure.
