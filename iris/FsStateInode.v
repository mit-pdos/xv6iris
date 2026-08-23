(* FsStateInode.v -- one inode, as nested separation-logic predicates.

   Design of record: claude-notes/design/fs-state.md section 2.  Stage 2a of
   claude-notes/projects/durable-disk.md.

   THE INODE NODE.  [fs_node] is the abstract value of one inode:

       n = { rec ; ent ; blk }

   [rec] is the 64-byte on-disk record, [ent] the indirect block's entry
   array, and [blk] maps a SLOT INDEX to that slot's block contents.  [blk]
   ranges over EVERY nonzero [addrs] entry -- direct and, through the owned
   indirect block, indirect -- REGARDLESS of [rec.size].  That is the F3
   ruling, built into the representation: an inode may own blocks beyond its
   size ([itrunc] frees them all; [writei]'s partial-failure commit leaves
   one), and nothing above has to reason about the discrepancy.

   The abstract byte-sequence is a READING, not the ownership:
   [fn_file_bytes n] and [dir_entries n] are functions of [n].  The one local
   clause the reading needs to be total is [inl_covers] (every slot below the
   size is allocated).  Distinctness of an inode's own blocks is the [∗]
   ([FsStateDefs.blk_owned_ne]); no clause states it.

   LOCAL REASONING (fs-state.md section 0).  Every clause of [inode_local]
   mentions ONE inode.  The only clause that mentions an inum at all is the
   "." entry, and it names the inode's OWN inum.  Links to other inodes are
   carried as [link_tok]s, never as an equation. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers.
From iris.base_logic.lib Require Import iprop own.
Require Import BioDefs.
Require Import RiscvModelBytes.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import DirView.
Require Import InodeDefs.
Require Import FsTree.
Require Import FsImg.
Require Export FsStateLink.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  1.  The node, and its readings                                     *)
(* ------------------------------------------------------------------ *)

Record fs_node := MkNode {
  fn_rec : dinode;                    (* the 64-byte on-disk record        *)
  fn_ent : list (bv 32);              (* the indirect block's entry array  *)
  fn_blk : gmap nat (list (bv 8));    (* slot |-> block contents           *)
}.

Global Instance fs_node_inhabited : Inhabited fs_node :=
  populate (MkNode inhabitant [] ∅).

Definition fn_type (n : fs_node) : Z := bv_unsigned (di_type (fn_rec n)).
Definition fn_size (n : fs_node) : Z := bv_unsigned (di_size (fn_rec n)).
Definition fn_nlink (n : fs_node) : nat :=
  Z.to_nat (bv_unsigned (di_nlink (fn_rec n))).

(* the block number of slot [k]: direct out of the record, indirect out of
   the entry array *)
Definition fn_naddr (n : fs_node) (k : nat) : Z :=
  if decide (k < FS_NDIRECT)%nat
  then bv_unsigned (di_addrs (fn_rec n) !!! k)
  else bv_unsigned (fn_ent n !!! (k - FS_NDIRECT)%nat).

(* the indirect block itself; 0 = none *)
Definition fn_indb (n : fs_node) : Z :=
  bv_unsigned (di_addrs (fn_rec n) !!! FS_NDIRECT).

(* the [data] function the tree's readings are stated over.  Slots the node
   does not own read as zeroes -- which is only ever consulted below the
   size, where [inl_covers] says the slot IS owned. *)
Definition fn_data (n : fs_node) : nat -> list (bv 8) :=
  fun k => default (replicate BSIZE (bv_0 8)) (fn_blk n !! k).

Definition fn_nrec (n : fs_node) : nat := dir_nrec (fn_size n).

Definition fn_file_bytes (n : fs_node) : list (bv 8) :=
  file_bytes (fn_data n) (Z.to_nat (fn_size n)).

Definition fn_is_dir (n : fs_node) : bool := bool_decide (fn_type n = T_DIR_z).

Definition dir_entries (n : fs_node) : gmap fname Z :=
  if fn_is_dir n then dir_view (fn_data n) (fn_nrec n) else ∅.

(* an ORPHAN directory is one at [nlink = 0]: its ".." entry is TOKENLESS,
   the parent having taken that token back at the unlink (fs-state.md
   section 2).  This kernel's "grey" record. *)
Definition fn_orphan (n : fs_node) : bool := bool_decide (fn_nlink n = 0%nat).

(* ------------------------------------------------------------------ *)
(*  2.  The local clauses                                              *)
(* ------------------------------------------------------------------ *)

Record inode_local (i : Z) (n : fs_node) : Prop := MkInodeLocal {
  (* representation *)
  inl_rec_wf     : dinode_wf (fn_rec n);
  inl_ent_len    : length (fn_ent n) = FS_NINDIRECT;
  inl_ind_zero   : fn_indb n = 0 -> fn_ent n = replicate FS_NINDIRECT (bv_0 32);
  inl_blk_dom    : forall k, (k < FS_MAXFILE)%nat ->
                     (is_Some (fn_blk n !! k) <-> fn_naddr n k <> 0);
  inl_blk_top    : forall k, (FS_MAXFILE <= k)%nat -> fn_blk n !! k = None;
  inl_blk_len    : forall k bs, fn_blk n !! k = Some bs -> length bs = BSIZE;
  (* the record's own fields *)
  inl_type       : fn_type n = 0 \/ fn_type n = T_DIR_z
                   \/ fn_type n = T_FILE_z \/ fn_type n = T_DEVICE_z;
  inl_size       : 0 <= fn_size n <= Z.of_nat FS_MAXFILE * BSIZE_z;
  inl_covers     : forall k, (k < FS_MAXFILE)%nat ->
                     Z.of_nat k * BSIZE_z < fn_size n -> fn_naddr n k <> 0;
  inl_free       : fn_type n = 0 -> fn_nlink n = 0%nat;
  inl_nlink      : bv_unsigned (di_nlink (fn_rec n)) <= 32767;
  (* directory-local; vacuous for anything else.  [inode_owned] is the one
     iterated predicate, so a directory's clauses live here rather than in a
     sibling of it -- see [dir_owned] below, which is the reading. *)
  inl_dir_size   : fn_is_dir n = true -> (16 | fn_size n);
  inl_dir_uniq   : fn_is_dir n = true -> dir_names_unique (fn_data n) (fn_nrec n);
  inl_dir_dot    : fn_is_dir n = true -> dir_entries n !! DOT = Some i;
  inl_dir_dotdot : fn_is_dir n = true -> is_Some (dir_entries n !! DOTDOT);
}.

Global Arguments inl_rec_wf {_ _} _.
Global Arguments inl_ent_len {_ _} _.
Global Arguments inl_ind_zero {_ _} _.
Global Arguments inl_blk_dom {_ _} _.
Global Arguments inl_blk_top {_ _} _.
Global Arguments inl_blk_len {_ _} _.
Global Arguments inl_type {_ _} _.
Global Arguments inl_size {_ _} _.
Global Arguments inl_covers {_ _} _.
Global Arguments inl_free {_ _} _.
Global Arguments inl_nlink {_ _} _.
Global Arguments inl_dir_size {_ _} _.
Global Arguments inl_dir_uniq {_ _} _.
Global Arguments inl_dir_dot {_ _} _.
Global Arguments inl_dir_dotdot {_ _} _.

(* the reading is total below the size: [inl_covers] plus [inl_blk_dom] *)
Lemma inode_local_data_owned i n k :
  inode_local i n -> (k < FS_MAXFILE)%nat ->
  Z.of_nat k * BSIZE_z < fn_size n ->
  exists bs, fn_blk n !! k = Some bs /\ fn_data n k = bs /\ length bs = BSIZE.
Proof.
  intros Hl Hk Hlt.
  destruct (proj2 (inl_blk_dom Hl k Hk) (inl_covers Hl k Hk Hlt)) as [bs Hbs].
  exists bs. rewrite /fn_data Hbs /=. split; [done | split; [done |]].
  by eapply inl_blk_len.
Qed.

(* the F3 reading, spelled out: a slot the node OWNS need not be below the
   size.  [inl_blk_dom] is an iff with the ADDRESS, never with the size. *)
Lemma inode_local_beyond_size i n k bs :
  inode_local i n -> fn_blk n !! k = Some bs ->
  (k < FS_MAXFILE)%nat /\ fn_naddr n k <> 0 /\ length bs = BSIZE.
Proof.
  intros Hl Hbs.
  assert (Hk : (k < FS_MAXFILE)%nat).
  { destruct (decide (k < FS_MAXFILE)%nat) as [| Hge]; [done |].
    rewrite (inl_blk_top Hl k) // in Hbs. lia. }
  split; [done |]. split; [| by eapply inl_blk_len].
  apply (inl_blk_dom Hl k Hk). by exists bs.
Qed.

(* ------------------------------------------------------------------ *)
(*  3.  The node's byte ownership                                      *)
(* ------------------------------------------------------------------ *)

Section InodeOwned.
  Context `{!fsLinkG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* inum [i]'s 64-byte slot of its inode block *)
  Definition rec_owned Γ (sb : fs_sb) (i : Z) (dn : dinode) : iProp Σ :=
    byte_range Γ (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
                 (Z.of_nat (64 * islot (fs_inum_bv i))) (dinode_bytes dn).

  Definition ind_owned Γ (n : fs_node) : iProp Σ :=
    (if decide (fn_indb n = 0) then emp
     else blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n)))%I.

  (* the Φ-only part of an inode: exactly its footprint *)
  Definition inode_phi Γ (sb : fs_sb) (i : Z) (n : fs_node) : iProp Σ :=
    (rec_owned Γ sb i (fn_rec n)
     ∗ ([∗ map] k ↦ bs ∈ fn_blk n, blk_owned Γ (fn_naddr n k) bs)
     ∗ ind_owned Γ n)%I.

  (* ---------------------------------------------------------------- *)
  (*  4.  The link tokens an inode's directory entries carry           *)
  (* ---------------------------------------------------------------- *)

  (* "." never carries a token (it would count the directory's link to
     itself twice); ".." carries one unless the directory is an orphan. *)
  Definition ent_tokenless (orph : bool) (s : fname) : bool :=
    bool_decide (s = DOT) || (orph && bool_decide (s = DOTDOT)).

  Definition ent_tok Γ (orph : bool) (s : fname) (t : Z) : iProp Σ :=
    (if ent_tokenless orph s then emp else link_tok Γ t)%I.

  Definition ent_toks Γ (n : fs_node) : iProp Σ :=
    ([∗ map] s ↦ t ∈ dir_entries n, ent_tok Γ (fn_orphan n) s t)%I.

  (* the same thing as ONE resource-algebra element -- what the mint
     allocates (fs-state.md section 1, "Functoriality") *)
  Definition ent_elem (orph : bool) (s : fname) (t : Z) : linkUR :=
    if ent_tokenless orph s then ε else link_tok_elem t 1.

  Definition link_elem_node (i : Z) (n : fs_node) : linkUR :=
    link_auth_elem i (fn_nlink n)
    ⋅ ([^op map] s ↦ t ∈ dir_entries n, ent_elem (fn_orphan n) s t).

  (* the Φ-FREE part of an inode: the link ghosts and the local clauses *)
  Definition inode_ghost Γ (i : Z) (n : fs_node) : iProp Σ :=
    (link_auth Γ i (fn_nlink n) ∗ ent_toks Γ n ∗ ⌜inode_local i n⌝)%I.

  Definition inode_owned Γ (sb : fs_sb) (i : Z) (n : fs_node) : iProp Σ :=
    (inode_phi Γ sb i n ∗ inode_ghost Γ i n)%I.

  (* the reading a directory's clients use *)
  Definition dir_owned Γ (sb : fs_sb) (d : Z) (n : fs_node) : iProp Σ :=
    (inode_owned Γ sb d n ∗ ⌜fn_is_dir n = true⌝)%I.

  Lemma inode_owned_split Γ sb i n :
    inode_owned Γ sb i n ⊣⊢ inode_phi Γ sb i n ∗ inode_ghost Γ i n.
  Proof. done. Qed.

  Lemma inode_owned_local Γ sb i n :
    inode_owned Γ sb i n -∗ ⌜inode_local i n⌝.
  Proof. iIntros "[_ (_ & _ & $)]". Qed.

  Lemma dir_owned_of Γ sb d n :
    fn_is_dir n = true -> inode_owned Γ sb d n ⊢ dir_owned Γ sb d n.
  Proof. iIntros (H) "H". by iFrame. Qed.

  (* ---------------------------------------------------------------- *)
  (*  5.  Timelessness                                                 *)
  (* ---------------------------------------------------------------- *)

  Global Instance rec_owned_timeless `{!GTimeless Γ} sb i dn :
    Timeless (rec_owned Γ sb i dn).
  Proof. rewrite /rec_owned. apply _. Qed.

  Global Instance ind_owned_timeless `{!GTimeless Γ} n :
    Timeless (ind_owned Γ n).
  Proof. rewrite /ind_owned. case_decide; apply _. Qed.

  Global Instance inode_phi_timeless `{!GTimeless Γ} sb i n :
    Timeless (inode_phi Γ sb i n).
  Proof. rewrite /inode_phi. apply _. Qed.

  Global Instance ent_tok_timeless Γ orph s t : Timeless (ent_tok Γ orph s t).
  Proof. rewrite /ent_tok. destruct (ent_tokenless orph s); apply _. Qed.

  Global Instance ent_toks_timeless Γ n : Timeless (ent_toks Γ n).
  Proof. rewrite /ent_toks. apply _. Qed.

  Global Instance inode_ghost_timeless Γ i n : Timeless (inode_ghost Γ i n).
  Proof. rewrite /inode_ghost. apply _. Qed.

  Global Instance inode_owned_timeless `{!GTimeless Γ} sb i n :
    Timeless (inode_owned Γ sb i n).
  Proof. rewrite /inode_owned. apply _. Qed.

  Global Instance dir_owned_timeless `{!GTimeless Γ} sb d n :
    Timeless (dir_owned Γ sb d n).
  Proof. rewrite /dir_owned. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (*  6.  Gathering and scattering the link ghosts                     *)
  (*                                                                   *)
  (*  These are the two halves of the mint's transport (FsState.v):     *)
  (*  gathering reads the family's VALIDITY off the durable instance's  *)
  (*  own [own]; scattering hands the freshly allocated one back out.   *)
  (* ---------------------------------------------------------------- *)

  Lemma inode_link_gather Γ i n (x : linkUR) :
    own (γlink Γ) x -∗ link_auth Γ i (fn_nlink n) -∗ ent_toks Γ n -∗
    own (γlink Γ) (x ⋅ link_elem_node i n).
  Proof.
    iIntros "Hx Ha Ht".
    iDestruct (own_op with "[$Hx $Ha]") as "Hxa".
    iDestruct (own_gather_map_opt (γlink Γ)
                 (fun (_ : fname) (t : Z) => link_tok_elem t 1)
                 (fun (s : fname) (_ : Z) => ent_tokenless (fn_orphan n) s)
                 (dir_entries n) (x ⋅ link_auth_elem i (fn_nlink n))
                with "Hxa [Ht]") as "H".
    { iApply (big_sepM_mono with "Ht"). intros s t _; simpl.
      rewrite /ent_tok /link_tok /link_toks. done. }
    rewrite /link_elem_node /ent_elem -assoc //.
  Qed.

  (* the same, with no accumulator: the auth IS the accumulator *)
  Lemma inode_link_pack Γ i n :
    link_auth Γ i (fn_nlink n) -∗ ent_toks Γ n -∗
    own (γlink Γ) (link_elem_node i n).
  Proof.
    iIntros "Ha Ht".
    iDestruct (own_gather_map_opt (γlink Γ)
                 (fun (_ : fname) (t : Z) => link_tok_elem t 1)
                 (fun (s : fname) (_ : Z) => ent_tokenless (fn_orphan n) s)
                 (dir_entries n) (link_auth_elem i (fn_nlink n))
                with "Ha [Ht]") as "H".
    { iApply (big_sepM_mono with "Ht"). intros s t _; simpl.
      rewrite /ent_tok /link_tok /link_toks. done. }
    rewrite /link_elem_node /ent_elem //.
  Qed.

  Lemma inode_link_scatter Γ i n :
    own (γlink Γ) (link_elem_node i n) ⊢
    link_auth Γ i (fn_nlink n) ∗ ent_toks Γ n.
  Proof.
    rewrite /link_elem_node own_op. iIntros "[$ Ht]".
    iDestruct (own_scatter_map_opt (γlink Γ)
                 (fun (_ : fname) (t : Z) => link_tok_elem t 1)
                 (fun (s : fname) (_ : Z) => ent_tokenless (fn_orphan n) s)
                 (dir_entries n) with "[Ht]") as "H".
    { rewrite /ent_elem //. }
    iApply (big_sepM_mono with "H"). intros s t _; simpl.
    rewrite /ent_tok /link_tok /link_toks. done.
  Qed.

  Lemma inode_link_iff Γ i n :
    link_auth Γ i (fn_nlink n) ∗ ent_toks Γ n
    ⊣⊢ own (γlink Γ) (link_elem_node i n).
  Proof.
    iSplit.
    - iIntros "[Ha Ht]". iApply (inode_link_pack with "Ha Ht").
    - iApply inode_link_scatter.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  7.  ENCODE LEMMAS -- what a writer uses at its AU                *)
  (*                                                                   *)
  (*  Every one of them is an ACCESSOR: it hands the writer the byte    *)
  (*  range the log is about to move, and takes it back at the new      *)
  (*  bytes.  None of them updates anything itself -- at an abstract    *)
  (*  [fsΦ] there is no update to make; the log's [byte_range_update]   *)
  (*  is what moves the bytes, and these lemmas are the repackaging     *)
  (*  either side of it.                                               *)
  (* ---------------------------------------------------------------- *)

  Lemma rec_owned_length dn : dinode_wf dn -> length (dinode_bytes dn) = 64%nat.
  Proof. apply dinode_bytes_length. Qed.

  (* (a) the record's bytes move -- iupdate, ialloc, ifree *)
  Lemma rec_owned_acc Γ sb i dn dn' :
    rec_owned Γ sb i dn ⊢
      byte_range Γ (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
                   (Z.of_nat (64 * islot (fs_inum_bv i))) (dinode_bytes dn)
      ∗ (byte_range Γ (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
                      (Z.of_nat (64 * islot (fs_inum_bv i))) (dinode_bytes dn')
         -∗ rec_owned Γ sb i dn').
  Proof. iIntros "H". iFrame "H". by iIntros "H". Qed.

  (* the record write inside a whole inode.  The addresses may move (this is
     also the "attach a freshly allocated direct block" step), as long as no
     slot the node ALREADY owns changes address. *)
  Definition fn_addrs_kept (n n' : fs_node) : Prop :=
    forall k, is_Some (fn_blk n !! k) -> fn_naddr n' k = fn_naddr n k.

  Lemma inode_phi_rec_move Γ sb i n n' :
    fn_blk n' = fn_blk n ->
    fn_ent n' = fn_ent n ->
    fn_indb n' = fn_indb n ->
    fn_addrs_kept n n' ->
    inode_phi Γ sb i n ⊢
      rec_owned Γ sb i (fn_rec n)
      ∗ (rec_owned Γ sb i (fn_rec n') -∗ inode_phi Γ sb i n').
  Proof.
    intros Hblk Hent Hind Hkept.
    iIntros "(Hr & Hb & Hi)". iFrame "Hr". iIntros "Hr".
    rewrite /inode_phi. iFrame "Hr".
    iSplitL "Hb".
    - rewrite Hblk. iApply (big_sepM_mono with "Hb").
      intros k bs Hk; simpl.
      assert (Hs : is_Some (fn_blk n !! k)) by (by exists bs).
      rewrite (Hkept k Hs) //.
    - rewrite /ind_owned Hind Hent //.
  Qed.

  (* (b) one data block's bytes move -- writei, and the readings follow *)
  Definition fn_set_blk (n : fs_node) (k : nat) (bs : list (bv 8)) : fs_node :=
    MkNode (fn_rec n) (fn_ent n) (<[k := bs]> (fn_blk n)).

  Lemma fn_naddr_set_blk n k bs : fn_naddr (fn_set_blk n k bs) = fn_naddr n.
  Proof. done. Qed.
  Lemma fn_indb_set_blk n k bs : fn_indb (fn_set_blk n k bs) = fn_indb n.
  Proof. done. Qed.

  Lemma inode_phi_blk_move Γ sb i n k bs bs' :
    fn_blk n !! k = Some bs ->
    inode_phi Γ sb i n ⊢
      blk_owned Γ (fn_naddr n k) bs
      ∗ (blk_owned Γ (fn_naddr n k) bs'
         -∗ inode_phi Γ sb i (fn_set_blk n k bs')).
  Proof.
    intros Hk. iIntros "(Hr & Hb & Hi)".
    iDestruct (big_sepM_insert_acc _ _ k bs Hk with "Hb") as "[$ Hb]".
    iIntros "Hnew". iDestruct ("Hb" with "Hnew") as "Hb".
    rewrite /inode_phi /fn_set_blk /=. by iFrame.
  Qed.

  (* (c) ATTACH a block the node did not own -- balloc's block arriving at a
     slot whose address the record (or the indirect block) already names.
     Together with (a)/(d) this is bmap's growth step; used alone with the
     size unchanged it is [writei]'s PARTIAL FAILURE, which commits the block
     without committing the size. *)
  Lemma inode_phi_blk_add Γ sb i n k bs :
    fn_blk n !! k = None ->
    inode_phi Γ sb i n ∗ blk_owned Γ (fn_naddr n k) bs
    ⊢ inode_phi Γ sb i (fn_set_blk n k bs).
  Proof.
    intros Hk. iIntros "((Hr & Hb & Hi) & Hnew)".
    rewrite /inode_phi /fn_set_blk /=. iFrame "Hr Hi".
    rewrite big_sepM_insert //. iFrame.
  Qed.

  (* (d) the indirect block's bytes move -- bmap writing one entry *)
  Lemma inode_phi_ind_move Γ sb i n n' :
    fn_rec n' = fn_rec n ->
    fn_blk n' = fn_blk n ->
    fn_addrs_kept n n' ->
    fn_indb n <> 0 ->
    inode_phi Γ sb i n ⊢
      blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n))
      ∗ (blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n')) -∗ inode_phi Γ sb i n').
  Proof.
    intros Hrec Hblk Hkept Hnz.
    iIntros "(Hr & Hb & Hi)".
    rewrite {1}/ind_owned decide_False //.
    iFrame "Hi". iIntros "Hi".
    rewrite /inode_phi /rec_owned Hrec. iFrame "Hr".
    iSplitL "Hb".
    - rewrite Hblk. iApply (big_sepM_mono with "Hb").
      intros k bs Hk; simpl.
      assert (Hs : is_Some (fn_blk n !! k)) by (by exists bs).
      rewrite (Hkept k Hs) //.
    - rewrite /ind_owned /fn_indb Hrec decide_False //.
  Qed.

  (* (e) the indirect block is CREATED -- the record gains addrs[12] and the
     new block arrives *)
  Lemma inode_phi_ind_create Γ sb i n n' :
    fn_blk n' = fn_blk n ->
    fn_addrs_kept n n' ->
    fn_indb n = 0 ->
    fn_indb n' <> 0 ->
    inode_phi Γ sb i n ⊢
      rec_owned Γ sb i (fn_rec n)
      ∗ (rec_owned Γ sb i (fn_rec n')
         -∗ blk_owned Γ (fn_indb n') (ind_bytes (fn_ent n'))
         -∗ inode_phi Γ sb i n').
  Proof.
    intros Hblk Hkept Hz Hnz.
    iIntros "(Hr & Hb & _)". iFrame "Hr". iIntros "Hr Hnew".
    rewrite /inode_phi. iFrame "Hr".
    iSplitL "Hb".
    - rewrite Hblk. iApply (big_sepM_mono with "Hb").
      intros k bs Hk; simpl.
      assert (Hs : is_Some (fn_blk n !! k)) by (by exists bs).
      rewrite (Hkept k Hs) //.
    - rewrite /ind_owned decide_False //.
  Qed.

  (* (f) ITRUNC frees EVERY owned block -- the direct and indirect data
     blocks and the indirect block itself, whether or not they are below the
     size.  What comes back is the truncated record; the blocks go to
     [free_bitmap] (FsStateBitmap.bitmap_free). *)
  Lemma inode_phi_trunc Γ sb i n n' :
    fn_blk n' = ∅ ->
    fn_indb n' = 0 ->
    inode_phi Γ sb i n ⊢
      ([∗ map] k ↦ bs ∈ fn_blk n, blk_owned Γ (fn_naddr n k) bs)
      ∗ ind_owned Γ n
      ∗ rec_owned Γ sb i (fn_rec n)
      ∗ (rec_owned Γ sb i (fn_rec n') -∗ inode_phi Γ sb i n').
  Proof.
    intros Hblk Hind.
    iIntros "(Hr & Hb & Hi)".
    iSplitL "Hb"; [iExact "Hb" |].
    iSplitL "Hi"; [iExact "Hi" |].
    iSplitL "Hr"; [iExact "Hr" |].
    iIntros "Hr".
    rewrite /inode_phi Hblk big_sepM_empty /ind_owned (decide_True _ _ Hind).
    iFrame "Hr". auto.
  Qed.

  (* the indirect block, handed back as an anonymous block when it exists *)
  Lemma ind_owned_block Γ n :
    fn_indb n <> 0 ->
    ind_owned Γ n ⊢ blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n)).
  Proof. intros Hnz. rewrite /ind_owned (decide_False _ _ Hnz) //. Qed.

  Lemma ind_owned_none Γ n : fn_indb n = 0 -> ind_owned Γ n ⊣⊢ emp.
  Proof. intros Hz. rewrite /ind_owned (decide_True _ _ Hz) //. Qed.

  (* ---------------------------------------------------------------- *)
  (*  8.  ENCODE LEMMAS -- the dirent moves, at the token layer         *)
  (*                                                                   *)
  (*  The BYTES of a dirent write move by (b) above; what is left is    *)
  (*  the token that rides with the entry.  Stated at the ENTRY-MAP     *)
  (*  delta so that the pure bridge (section 9) and the resource move   *)
  (*  stay separable.                                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma ent_toks_delete Γ n n' s t :
    fn_orphan n' = fn_orphan n ->
    dir_entries n !! s = Some t ->
    dir_entries n' = delete s (dir_entries n) ->
    ent_toks Γ n -∗ ent_tok Γ (fn_orphan n) s t ∗ ent_toks Γ n'.
  Proof.
    intros Horph Hs Hdel.
    rewrite /ent_toks (big_sepM_delete _ (dir_entries n) s t) //.
    iIntros "[$ H]". rewrite Hdel Horph //.
  Qed.

  Lemma ent_toks_insert Γ n n' s t :
    fn_orphan n' = fn_orphan n ->
    dir_entries n !! s = None ->
    dir_entries n' = <[s := t]> (dir_entries n) ->
    ent_toks Γ n -∗ ent_tok Γ (fn_orphan n) s t -∗ ent_toks Γ n'.
  Proof.
    intros Horph Hs Hins.
    rewrite /ent_toks Hins Horph big_sepM_insert //.
    iIntros "H Ht". iFrame.
  Qed.

  (* the ORPHAN step: the directory's own [nlink] reaches 0, the parent takes
     its ".." token back, and the entry becomes tokenless.  Everything else
     keeps its token, because [ent_tokenless] differs at ".." only. *)
  Lemma dot_ne_dotdot : DOT <> DOTDOT.
  Proof. rewrite /DOT /DOTDOT. intros H. inversion H. Qed.

  Lemma ent_tokenless_orphan_ne orph orph' s :
    s <> DOTDOT -> ent_tokenless orph' s = ent_tokenless orph s.
  Proof.
    intros Hne. rewrite /ent_tokenless (bool_decide_eq_false_2 _ Hne).
    by rewrite !andb_false_r.
  Qed.

  Lemma ent_tokenless_dotdot orph : ent_tokenless orph DOTDOT = orph.
  Proof.
    rewrite /ent_tokenless.
    rewrite (bool_decide_eq_false_2 (DOTDOT = DOT));
      [| intros H; by apply dot_ne_dotdot].
    by rewrite bool_decide_eq_true_2 // andb_true_r orb_false_l.
  Qed.

  Lemma ent_tok_dotdot Γ orph t :
    ent_tok Γ orph DOTDOT t ⊣⊢ (if orph then emp else link_tok Γ t).
  Proof. rewrite /ent_tok ent_tokenless_dotdot //. Qed.

  Lemma ent_toks_orphan Γ n n' t :
    dir_entries n' = dir_entries n ->
    fn_orphan n = false ->
    fn_orphan n' = true ->
    dir_entries n !! DOTDOT = Some t ->
    ent_toks Γ n -∗ link_tok Γ t ∗ ent_toks Γ n'.
  Proof.
    intros Hents Ho Ho' Hdd.
    rewrite /ent_toks Hents Ho Ho'.
    rewrite (big_sepM_delete (fun s t => ent_tok Γ false s t)
               (dir_entries n) DOTDOT t) //.
    rewrite (big_sepM_delete (fun s t => ent_tok Γ true s t)
               (dir_entries n) DOTDOT t) //.
    rewrite !ent_tok_dotdot.
    iIntros "[Hd H]". iFrame "Hd". iSplitR; [done |].
    iApply (big_sepM_mono with "H"). intros s v Hs; simpl.
    rewrite /ent_tok (ent_tokenless_orphan_ne false true s) //.
    intros ->. rewrite lookup_delete in Hs. done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  9.  The readings, after a write                                  *)
  (* ---------------------------------------------------------------- *)

  Lemma fn_data_set_blk n k bs j :
    fn_data (fn_set_blk n k bs) j =
      if decide (j = k) then bs else fn_data n j.
  Proof.
    rewrite /fn_data /fn_set_blk /=.
    destruct (decide (j = k)) as [-> |].
    - by rewrite lookup_insert.
    - by rewrite lookup_insert_ne.
  Qed.

  (* what a [dir_written_at]/[dir_zeroed_at] hypothesis is stated over *)
  Lemma fn_file_byte_set_blk n k bs j :
    file_byte (fn_data (fn_set_blk n k bs)) j =
      if decide ((j `div` BSIZE)%nat = k)
      then bs !!! (j `mod` BSIZE)%nat
      else file_byte (fn_data n) j.
  Proof.
    rewrite /file_byte fn_data_set_blk.
    by destruct (decide ((j `div` BSIZE)%nat = k)).
  Qed.

  Lemma fn_size_set_blk n k bs : fn_size (fn_set_blk n k bs) = fn_size n.
  Proof. done. Qed.
  Lemma fn_is_dir_set_blk n k bs : fn_is_dir (fn_set_blk n k bs) = fn_is_dir n.
  Proof. done. Qed.
  Lemma fn_nlink_set_blk n k bs : fn_nlink (fn_set_blk n k bs) = fn_nlink n.
  Proof. done. Qed.
  Lemma fn_orphan_set_blk n k bs : fn_orphan (fn_set_blk n k bs) = fn_orphan n.
  Proof. done. Qed.

  (* ---------------------------------------------------------------- *)
  (*  10. The DIRENT moves at [dir_owned], and the link reading        *)
  (*                                                                   *)
  (*  Each hands the writer the Φ-part (whose bytes the log moves, by  *)
  (*  [inode_phi_blk_move]) and does the token move beside it.  The    *)
  (*  entry-map delta is a PREMISE: it is a pure fact about ONE        *)
  (*  directory's own bytes, proved by the caller from [FsTree]        *)
  (*  ([dir_entries_zero] below is the removal case, outright).        *)
  (* ---------------------------------------------------------------- *)

  (* the direction safety uses: at [nlink = 0] no entry points here *)
  Lemma inode_link_tok_nz Γ sb i n :
    inode_owned Γ sb i n -∗ link_tok Γ i -∗ ⌜fn_nlink n <> 0%nat⌝.
  Proof.
    iIntros "[_ (Ha & _ & _)] Ht".
    destruct (decide (fn_nlink n = 0%nat)) as [Hz | Hnz]; [| done].
    rewrite Hz. iDestruct (link_auth_zero_no_tok with "Ha Ht") as "[]".
  Qed.

  Lemma dir_owned_unlink Γ sb d n n' s t :
    fn_orphan n' = fn_orphan n ->
    fn_nlink n' = fn_nlink n ->
    dir_entries n !! s = Some t ->
    dir_entries n' = delete s (dir_entries n) ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n
      ∗ ent_tok Γ (fn_orphan n) s t
      ∗ (inode_phi Γ sb d n' -∗ dir_owned Γ sb d n').
  Proof.
    intros Horph Hnl Hs Hdel Hloc Hdir.
    iIntros "[[$ (Ha & Ht & _)] _]".
    iDestruct (ent_toks_delete Γ n n' s t Horph Hs Hdel with "Ht") as "[$ Ht]".
    iIntros "Hphi".
    rewrite /dir_owned /inode_owned /inode_ghost Hnl. by iFrame.
  Qed.

  Lemma dir_owned_link Γ sb d n n' s t :
    fn_orphan n' = fn_orphan n ->
    fn_nlink n' = fn_nlink n ->
    dir_entries n !! s = None ->
    dir_entries n' = <[s := t]> (dir_entries n) ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n
      ∗ (inode_phi Γ sb d n' -∗ ent_tok Γ (fn_orphan n) s t
         -∗ dir_owned Γ sb d n').
  Proof.
    intros Horph Hnl Hs Hins Hloc Hdir.
    iIntros "[[$ (Ha & Ht & _)] _]".
    iIntros "Hphi Htok".
    iDestruct (ent_toks_insert Γ n n' s t Horph Hs Hins with "Ht Htok") as "Ht".
    rewrite /dir_owned /inode_owned /inode_ghost Hnl. by iFrame.
  Qed.

  (* the child's side of "unlink a directory": its [nlink] reaches 0, its
     ".." entry becomes TOKENLESS, and the token it held goes back to the
     parent.  The caller supplies the new [link_auth] because the RA move
     ([link_return] at the parent's own auth) is its to make. *)
  Lemma dir_owned_orphan Γ sb d n n' t :
    dir_entries n' = dir_entries n ->
    fn_orphan n = false -> fn_orphan n' = true ->
    dir_entries n !! DOTDOT = Some t ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n ∗ link_auth Γ d (fn_nlink n) ∗ link_tok Γ t
      ∗ (inode_phi Γ sb d n' -∗ link_auth Γ d (fn_nlink n')
         -∗ dir_owned Γ sb d n').
  Proof.
    intros Hents Ho Ho' Hdd Hloc Hdir.
    iIntros "[[$ (Ha & Ht & _)] _]". iFrame "Ha".
    iDestruct (ent_toks_orphan Γ n n' t Hents Ho Ho' Hdd with "Ht") as "[$ Ht]".
    iIntros "Hphi Ha".
    rewrite /dir_owned /inode_owned /inode_ghost. by iFrame.
  Qed.

End InodeOwned.

(* ------------------------------------------------------------------ *)
(*  11. The PURE bridge from the tree's dirent vocabulary              *)
(*                                                                     *)
(*  [FsTree] states an unlink as [dir_zeroed_at] and proves the view    *)
(*  delta outright; the token move above then applies.  (The mirror     *)
(*  equation for an INSERT is not in the tree -- [FsTree] proves the    *)
(*  uniqueness preservation, [dir_names_unique_write], but no           *)
(*  [dir_view data' nrec' = <[s:=t]> (dir_view data nrec)].  Until it   *)
(*  is, [ent_toks_insert] takes that delta as a hypothesis, which is    *)
(*  the shape a caller has anyway.)                                     *)
(* ------------------------------------------------------------------ *)

Lemma dir_entries_zero (n n' : fs_node) (k0 : nat) :
  fn_is_dir n = true -> fn_is_dir n' = true ->
  fn_size n' = fn_size n ->
  dir_names_unique (fn_data n) (fn_nrec n) ->
  (k0 < fn_nrec n)%nat ->
  dir_live (fn_data n) k0 ->
  dir_zeroed_at (fn_data n) (fn_data n') k0 ->
  dir_entries n' = delete (dir_bname (fn_data n) k0) (dir_entries n).
Proof.
  intros Hd Hd' Hsz Hu Hk Hlive Hz.
  rewrite /dir_entries Hd Hd' /fn_nrec Hsz.
  by apply (dir_view_zero (fn_data n) (fn_data n') (dir_nrec (fn_size n)) k0).
Qed.
