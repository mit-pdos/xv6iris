(* ======================================================================= *)
(*  FsRep.v -- THE FRAGMENT ALGEBRA: the tree layer as a READING over       *)
(*  resources that already exist.                                          *)
(*  design: claude-notes/design/fs-fragments.md §2 (rulings R3, R9)         *)
(* ======================================================================= *)

(*  WHAT IS NEW HERE, AND IT IS ALMOST NOTHING.

    This is F1b.  [FsTree.v] said what a file-system shape IS; this file
    says which RESOURCES exhibit one.  Every clause below is built out of
    something already landed and already correctly homed:

      the NODE   [InodeRegion.dinode_at] (an exclusive [ghost_map Z dinode]
                 element) plus [InodeInv.inode_blocks];
      the EDGES  [DirLinks.dir_links], verbatim -- **there is NO separate
                 edge resource and none may be created** (§2(ii)).  The
                 landed ticket says WHO IS POINTED AT ([dir_link_at]'s
                 payload is [ilink (dir_inum data k)]); the (source, name)
                 half is carried by the BYTES, i.e. by [fnode i (NDir
                 ents)].  Out-edges are owned by the source node, which is
                 exactly the fragment locality this layer wants, already
                 paid for.

    **NO NEW AUTHORITY, NO NEW GHOST NAME, NO NEW INVARIANT** (R3).  Three
    §20.9 death certificates cover every home a whole-tree authority could
    have: §20.9(c) killed a global authority inside [ireg_body] (a mover
    can then read the key only by opening, and nothing lets the CALLER
    supply a fact about it); §20.9(d) killed parking an authority with the
    record; §20.9(e) killed a new gname (it would enter [ireg_inv] AND
    [ipool_shape], i.e. [ic_escrow]'s arity, i.e. every fs contract).  So
    [fs_rep] is a DERIVED PREDICATE over client-held fragments.  If a proof
    on top of this file finds itself wanting an authority, it is wrong:
    stop and re-read §20.9.

    ---- A HARD CONSEQUENCE, AND IT IS A THEOREM NOT A STYLE CHOICE ------

    [fnode i n] requires [dinode_at γi i dn], which lives in
    [IcacheEscrow.ipool_alloc] (behind the itable spinlock) or in
    [ic_loaded] (behind the inode sleeplock).  **A thread can hold [fnode i
    n] only while [i] is locked**, so [fs_rep t] over a whole tree is
    unholdable by any thread, and [fs_rep] can appear only inside
    atomic-update / HOCAP accessors -- never as a client-held whole-tree
    assertion.  That kills FSCQ-style whole-tree pre/posts outright, and it
    is why F2 must be a logically-atomic triple whose linearization point
    is a single [dirlookup] under one lock (R8), not a re-derivation of
    namex's postcondition.

    Second consequence, from §20.9(h)/(i): the edge ticket keeps its grey
    disjunct, so **an edge of [t] may point at a node that is not in [t]**.
    [fs_closed] is false in general and is not defined here.
    FRAGMENTS-WITH-HOLES is the only consistent top-level shape.

    ---- THE HEADLINE: §20.17.4's OWED FACT --------------------------------

    sys_unlink's grey conversion (S7) has to know WHICH [ilink dp] to
    convert, and the only one is inside [ip]'s [dir_links] at [ip]'s
    [".."] record -- but [dir_link_at] is keyed by record INDEX and the
    model has no invariant placing [".."] at index 1
    (fs-icache.md:5270-5280: "§20.6's preservation table quietly assumes it
    and nobody had noticed").  In the tree the fact is free and it is named
    rather than positional: [fnode_dotdot] turns [ents !! ".." = Some dp]
    into the RECORD INDEX dirlookup would stop at, live and naming [dp],
    and a caller that holds [DirLinks.dir_links] can open it at that
    index.  **[fnode_dotdot] is the clearest single place where the tree
    layer pays for itself.**                                              *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map.
Require Import SailStdpp.Values.
Require Import RiscvPtsto.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import DirView.
Require Import InodeRegion.
Require Import FsTree.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.

Section FsRep.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  0.  THE KEY COERCION                                               *)
  (* ------------------------------------------------------------------ *)

  (* [dinode_at] takes a [bv 32] and files it at [bv_unsigned inum] in a
     [ghost_map Z dinode] (InodeRegion.v:560).  The tree is [Z]-keyed -- the
     map underneath is -- so the coercion lands here, and
     [FsTree.fs_inums_ok] is what makes it round-trip. *)
  Definition inum_of (i : Z) : bv 32 := Z_to_bv 32 i.

  Lemma inum_of_unsigned (i : Z) :
    0 <= i < 2 ^ 32 -> bv_unsigned (inum_of i) = i.
  Proof.
    intros H. unfold inum_of. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. exact H.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  1.  THE NODE FRAGMENT                                              *)
  (* ------------------------------------------------------------------ *)

  (* **[bm] IS EXISTENTIAL AND UNCOUPLED, DELIBERATELY.**  The coupling of
     the block map to [di_addrs] is [InodeLock.inode_ok cov logstart dn bm
     data], whose two extra parameters would ride on every [fnode] for a
     fact this layer never reads.  A caller that wants the coupling still
     has it in the escrow payload it carved the [fnode] out of; a caller
     that only wants the SHAPE does not pay for it. *)
  Definition fnode (γi : gname) (γfs : fs_names) (i : Z) (n : fsnode)
    : iProp Σ :=
    (∃ (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)),
       dinode_at γi (inum_of i) dn ∗
       inode_blocks γfs bm data ∗
       ⌜node_rep n dn data⌝)%I.

  Lemma fnode_intro (γi : gname) (γfs : fs_names) (i : Z) (n : fsnode)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    node_rep n dn data ->
    dinode_at γi (inum_of i) dn -∗ inode_blocks γfs bm data -∗
    fnode γi γfs i n.
  Proof.
    intros Hrep. iIntros "Hd Hb". iExists dn, bm, data. iFrame. done.
  Qed.

  (* the canonical introduction: the node need not be guessed, it is read
     off the bytes ([FsTree.node_of]) *)
  Lemma fnode_intro_of (γi : gname) (γfs : fs_names) (i : Z)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) <> 0 ->
    dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))) ->
    dinode_at γi (inum_of i) dn -∗ inode_blocks γfs bm data -∗
    fnode γi γfs i (node_of dn data).
  Proof.
    intros Hnz Hu. iApply fnode_intro. exact (node_rep_of dn data Hnz Hu).
  Qed.

  (* EXCLUSIVE, one line from [dinode_at_excl] (InodeRegion.v:567) -- and
     this is the twice-instantiate audit's answer for [fnode]: two nodes at
     one inum entail [False] because the points-to is exclusive, not
     because anything was assumed. *)
  Lemma fnode_excl (γi : gname) (γfs : fs_names) (i : Z) (n1 n2 : fsnode) :
    fnode γi γfs i n1 -∗ fnode γi γfs i n2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (dn1 bm1 data1) "(Hd1 & _ & _)".
    iDestruct "H2" as (dn2 bm2 data2) "(Hd2 & _ & _)".
    iApply (dinode_at_excl with "Hd1 Hd2").
  Qed.

  (* NO [Timeless] INSTANCE, AND NONE IS OWED.  [inode_blocks]'s own
     instance lives in [IcacheEscrow.v] (:234), ABOVE this file, and
     dragging the escrow in to get it would enlarge the cone for a
     property nothing here needs: R3 forbids the invariant that would be
     the only consumer.  A file above IcacheEscrow that wants a timeless
     [fnode] can declare it there in one line. *)

  (* A NODE IS ALLOCATED.  [FsTree.node_rep_alloc] lifted: whoever holds an
     [fnode] holds a record whose type is nonzero.  This is what a consumer
     that wants allocatedness reads off the tree instead of chasing a
     ledger fragment. *)
  Lemma fnode_alloc (γi : gname) (γfs : fs_names) (i : Z) (n : fsnode) :
    fnode γi γfs i n -∗
      ∃ (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)),
        ⌜node_rep n dn data⌝ ∗ ⌜bv_unsigned (di_type dn) <> 0⌝ ∗
        dinode_at γi (inum_of i) dn ∗ inode_blocks γfs bm data.
  Proof.
    iIntros "H". iDestruct "H" as (dn bm data) "(Hd & Hb & %Hrep)".
    iExists dn, bm, data. iFrame.
    iPureIntro. split; [exact Hrep | exact (node_rep_alloc n dn data Hrep)].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE EDGES -- [dir_links], VERBATIM                             *)
  (* ------------------------------------------------------------------ *)

  (* NOTHING HERE ANY MORE (durable-disk lane G, slice 6f).  The tree layer
     used to restate [DirLinks.dir_links] under the name [fedges], with an
     accessor [fedges_acc] handing out one record's ticket.  Neither had a
     consumer -- [fnode_dotdot] below supplies the index, but no proof in
     the tree ever asked for the ticket -- so both are gone and the one
     place that did need the resource ([FsLookup.wp_dirlookup_tree_body])
     names [dir_links] outright.  The edge map itself belongs to the byte
     layer and dies with the old link ledger (slice 6c). *)

  (* ------------------------------------------------------------------ *)
  (*  3.  READING AN ENTRY OFF A DIRECTORY NODE                          *)
  (* ------------------------------------------------------------------ *)

  (* **THE CONVERSION THE MODEL HAD NO FACT FOR.**  A NAME in [ents] is a
     RECORD INDEX in the bytes -- the one [dirlookup] stops at -- live and
     naming the entry's inum.  [FsTree.node_rep_ent] does the pure half;
     this is the resource-level lift, and it hands the node back whole
     (nothing is consumed: the existentials are re-supplied to
     [fnode_intro]). *)
  Lemma fnode_ent (γi : gname) (γfs : fs_names) (i : Z)
      (ents : gmap fname Z) (s : fname) (z : Z) :
    ents !! s = Some z ->
    fnode γi γfs i (NDir ents) -∗
      ∃ (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) (k : nat),
        ⌜node_rep (NDir ents) dn data⌝ ∗
        ⌜bv_unsigned (di_type dn) = T_DIR_z⌝ ∗
        ⌜dir_first data (dir_nrec (bv_unsigned (di_size dn))) s = Some k⌝ ∗
        ⌜(k < dir_nrec (bv_unsigned (di_size dn)))%nat⌝ ∗
        ⌜dir_live data k⌝ ∗
        ⌜dir_bname data k = s⌝ ∗
        ⌜bv_unsigned (dir_inum data k) = z⌝ ∗
        dinode_at γi (inum_of i) dn ∗ inode_blocks γfs bm data.
  Proof.
    intros Hs. iIntros "H". iDestruct "H" as (dn bm data) "(Hd & Hb & %Hrep)".
    destruct (node_rep_ent ents dn data s z Hrep Hs)
      as (k & Hfirst & Hlive & Hname & Hz).
    iExists dn, bm, data, k. iFrame.
    iPureIntro. split; [exact Hrep |].
    split; [exact (node_rep_dir ents dn data Hrep) |].
    split; [exact Hfirst |].
    split; [exact (dir_first_lt _ _ _ _ Hfirst) |].
    split; [exact Hlive |].
    split; [exact Hname | exact Hz].
  Qed.

  (* ...and back, under the invariant: every live record IS an entry.  The
     pair is what makes "the tree's edges" and "the bytes' records" the
     same thing in both directions, at the record view. *)
  Lemma fnode_rec (γi : gname) (γfs : fs_names) (i : Z)
      (ents : gmap fname Z) (dn : dinode) (data : nat -> list (bv 8))
      (k : nat) :
    node_rep (NDir ents) dn data ->
    (k < dir_nrec (bv_unsigned (di_size dn)))%nat -> dir_live data k ->
    ents !! dir_bname data k = Some (bv_unsigned (dir_inum data k)).
  Proof. intros Hrep Hk Hl. exact (node_rep_ent_of ents dn data k Hrep Hk Hl). Qed.

  (* **THE HEADLINE (R9).**  §20.17.4's owed fact, at the one name it is
     owed for.  This is [fnode_ent] at [s := DOTDOT], stated on its own
     because the fact it delivers -- "[ip]'s parent link is the record at
     index [k], and that record is live and names [dp]" -- is the premise
     S7 could not previously write down at all.  Open [DirLinks.dir_links]
     at [k] and the [ilink dp] to convert is in hand. *)
  Lemma fnode_dotdot (γi : gname) (γfs : fs_names) (ip dp : Z)
      (ents : gmap fname Z) :
    ents !! DOTDOT = Some dp ->
    fnode γi γfs ip (NDir ents) -∗
      ∃ (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) (k : nat),
        ⌜node_rep (NDir ents) dn data⌝ ∗
        ⌜bv_unsigned (di_type dn) = T_DIR_z⌝ ∗
        ⌜dir_first data (dir_nrec (bv_unsigned (di_size dn))) DOTDOT = Some k⌝ ∗
        ⌜(k < dir_nrec (bv_unsigned (di_size dn)))%nat⌝ ∗
        ⌜dir_live data k⌝ ∗
        ⌜dir_bname data k = DOTDOT⌝ ∗
        ⌜bv_unsigned (dir_inum data k) = dp⌝ ∗
        dinode_at γi (inum_of ip) dn ∗ inode_blocks γfs bm data.
  Proof. apply fnode_ent. Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE WHOLE READING, AND THE CSL DIVIDEND                        *)
  (* ------------------------------------------------------------------ *)

  Definition fmap_rep (γi : gname) (γfs : fs_names) (m : gmap Z fsnode)
    : iProp Σ := ([∗ map] i ↦ n ∈ m, fnode γi γfs i n)%I.

  Definition fs_rep (γi : gname) (γfs : fs_names) (t : fstree) : iProp Σ :=
    (fmap_rep γi γfs (fs_nodes t) ∗ ⌜fs_wf t⌝)%I.

  (* **THE FRAME LAW, AND IT IS GENUINELY FREE.**  [big_sepM_union], no
     more: the node store is a [gmap] and [dinode_at] is a [ghost_map]
     element, so disjoint sub-trees separate at no cost.  That is the CSL
     dividend the design promises. *)
  Lemma fmap_rep_union (γi : gname) (γfs : fs_names) (m1 m2 : gmap Z fsnode) :
    m1 ##ₘ m2 ->
    fmap_rep γi γfs (m1 ∪ m2) ⊣⊢ fmap_rep γi γfs m1 ∗ fmap_rep γi γfs m2.
  Proof. intros Hd. rewrite /fmap_rep. by rewrite big_sepM_union. Qed.

  Lemma fmap_rep_empty (γi : gname) (γfs : fs_names) :
    fmap_rep γi γfs ∅ ⊣⊢ emp.
  Proof. rewrite /fmap_rep. by rewrite big_sepM_empty. Qed.

  Lemma fmap_rep_insert (γi : gname) (γfs : fs_names) (m : gmap Z fsnode)
      (i : Z) (n : fsnode) :
    m !! i = None ->
    fmap_rep γi γfs (<[i := n]> m)
    ⊣⊢ fnode γi γfs i n ∗ fmap_rep γi γfs m.
  Proof. intros H. rewrite /fmap_rep. by rewrite big_sepM_insert. Qed.

  Lemma fmap_rep_acc (γi : gname) (γfs : fs_names) (m : gmap Z fsnode)
      (i : Z) (n : fsnode) :
    m !! i = Some n ->
    fmap_rep γi γfs m -∗
      fnode γi γfs i n ∗ (fnode γi γfs i n -∗ fmap_rep γi γfs m).
  Proof.
    intros H. rewrite /fmap_rep. apply bi.entails_wand.
    by apply big_sepM_lookup_acc.
  Qed.

  (* the same at tree altitude: [fs_wf] rides through untouched, because a
     node's CONTENT changing cannot move the key set *)
  Lemma fs_rep_acc (γi : gname) (γfs : fs_names) (t : fstree)
      (i : Z) (n : fsnode) :
    fs_nodes t !! i = Some n ->
    fs_rep γi γfs t -∗
      fnode γi γfs i n ∗ (fnode γi γfs i n -∗ fs_rep γi γfs t).
  Proof.
    intros H. iIntros "[Hm %Hwf]".
    iDestruct (fmap_rep_acc γi γfs (fs_nodes t) i n H with "Hm") as "[$ Hback]".
    iIntros "Hn". iSplitL "Hback Hn"; [| done]. iApply "Hback". iFrame.
  Qed.

  (* two nodes of one tree at one inum are one node -- [fs_rep]'s share of
     the twice-instantiate audit, and the reason [node_rep_inj] is owed *)
  Lemma fs_rep_node_det (γi : gname) (γfs : fs_names) (t : fstree)
      (i : Z) (n1 n2 : fsnode) :
    fs_nodes t !! i = Some n1 -> fs_nodes t !! i = Some n2 -> n1 = n2.
  Proof. intros H1 H2. congruence. Qed.

  (* ------------------------------------------------------------------ *)
  (*  5.  PATH SLICES                                                    *)
  (* ------------------------------------------------------------------ *)

  (* the nodes a walk touches, as a set *)
  Definition path_nodes (t : fstree) (i : Z) (p : list fname) : gset Z :=
    list_to_set (path_chain t i p).

  (* **PATH-POINTS-TO, i.e. F4's closed-fragment special case.**  The walk
     lands on [j], and the caller holds exactly the nodes the walk stepped
     through.  It is a SLICE of [fs_rep], carved by [fmap_rep_split] below,
     which is why it composes with the frame law rather than beside it. *)
  Definition fslice (γi : gname) (γfs : fs_names) (t : fstree)
      (i : Z) (p : list fname) (j : Z) : iProp Σ :=
    (⌜path_at t i p = Some j⌝ ∗
     fmap_rep γi γfs
       (stdpp.base.filter (fun kv : Z * fsnode => kv.1 ∈ path_nodes t i p)
               (fs_nodes t)))%I.

  Lemma fmap_rep_split (γi : gname) (γfs : fs_names) (m : gmap Z fsnode)
      (D : gset Z) :
    fmap_rep γi γfs m
    ⊣⊢ fmap_rep γi γfs (stdpp.base.filter (fun kv : Z * fsnode => kv.1 ∈ D) m)
        ∗ fmap_rep γi γfs (stdpp.base.filter (fun kv : Z * fsnode => kv.1 ∉ D) m).
  Proof.
    rewrite -fmap_rep_union.
    2:{ apply map_disjoint_filter_complement. }
    f_equiv. symmetry. apply map_filter_union_complement.
  Qed.

  Lemma fs_rep_slice (γi : gname) (γfs : fs_names) (t : fstree)
      (i : Z) (p : list fname) (j : Z) :
    path_at t i p = Some j ->
    fs_rep γi γfs t -∗
      fslice γi γfs t i p j ∗ (fslice γi γfs t i p j -∗ fs_rep γi γfs t).
  Proof.
    intros Hp. iIntros "[Hm %Hwf]".
    iDestruct (fmap_rep_split γi γfs (fs_nodes t) (path_nodes t i p) with "Hm")
      as "[Hin Hout]".
    iSplitL "Hin"; [by iFrame |].
    iIntros "[_ Hin]". iSplitL; [| done].
    iApply (fmap_rep_split γi γfs (fs_nodes t) (path_nodes t i p)). iFrame.
  Qed.

  (* the walk's endpoint is one of the slice's nodes -- what makes an
     [fslice] usable at all *)
  Lemma fslice_last (t : fstree) (i : Z) (p : list fname) (j : Z) :
    path_at t i p = Some j -> j ∈ path_nodes t i p.
  Proof.
    intros H. rewrite /path_nodes elem_of_list_to_set.
    exact (path_chain_last t i j p H).
  Qed.

End FsRep.
