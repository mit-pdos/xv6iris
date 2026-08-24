(* FsDurSnap.v -- SNAPSHOT COMMITS: the durable file-system instance is
   ALLOCATED AFRESH at every group commit and never updated.

   Design of record: claude-notes/design/fs-state.md section 4^9 (the
   owner's SNAPSHOT ruling, with its addendum 5 -- the transport lemma IS
   the allocator); worklist item 4 of
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
Require Import DirView.
Require Import FsTree.
Require Import InodeDefs.
Require Import RiscvModelBytes.  (* [nth_byte] / [bv_eq_of_bytes] *)
Require Import FsImg.
Require Import LogDefs.       (* [fs_dbytes] -- the byte flattening       *)
Require Import Xv6Cameras.
Require Import FsDurBytes.    (* [fs_dbytes_blocks] -- Gamma-generically  *)
(* LAST, so [FsState]'s [fs_view] / [byte_range] / [blk_owned] / [link_auth]
   win over the block layer's twins that arrive transitively through
   [FsDurBytes] -> [RiscvPtsto]; durable-notes.md, AND WHERE THAT IMPORT
   COLLIDES, PUT IT EARLY. *)
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

(* ===================================================================== *)
(*  1a. WHICH BLOCK EACH CLAUSE READS                                     *)
(*                                                                        *)
(*  The two vocabularies the USED-SET COUPLING and the FRAME are stated    *)
(*  in.  Both are per-object readings: [fn_owns] names ONE node's blocks   *)
(*  and [snap_meta] the three roles that are not a node's at all.          *)
(* ===================================================================== *)

(* block [b] is one of node [n]'s OWN blocks: a data block it holds, or its
   indirect block.  These are exactly the blocks [snap_blk] and [snap_ind]
   read at [n]. *)
Definition fn_owns (n : fs_node) (b : Z) : Prop :=
  (exists k, is_Some (fn_blk n !! k) /\ fn_naddr n k = b)
  \/ (fn_indb n <> 0 /\ fn_indb n = b).

(* ...and the blocks the NON-inode clauses read: the superblock's block, the
   bitmap's block, and the inode region's blocks (one per sixteen inums).
   The region arm quantifies over the inums the STATE names rather than over
   the region's geometry, which is the only form derivable from [S] alone. *)
Definition snap_meta (S : fs_state_rec) (b : Z) : Prop :=
  b = SB_BNO
  \/ b = sb_bmapstart (fss_sb S)
  \/ (exists i, is_Some (fss_inodes S !! i)
             /\ b = sb_inodestart (fss_sb S) + i `div` 16).

(* ===================================================================== *)
(*  1a'. THE REPRESENTATION CLAUSES                                       *)
(*                                                                        *)
(*  The half of [inode_local] that says a node IS the reading of its own   *)
(*  bytes: the record is well formed, the entry array has the indirect     *)
(*  block's length (and is zeroes when there is no indirect block), and a  *)
(*  slot is held exactly when its address is nonzero.  Nothing here is a   *)
(*  claim about the file system -- there is no type, no size, no link      *)
(*  count and no directory clause -- which is why all five survive every   *)
(*  window a semantic clause does not: a writer that has just spliced a    *)
(*  record has not made the node stop being that record's reading.         *)
(*                                                                        *)
(*  THEY BELONG ON THE ACCUMULATED SIDE, AND THAT IS NOT A CONVENIENCE.    *)
(*  With them in [snap_bytes], the three byte ties PIN THE NODE            *)
(*  ([snap_bytes_node_inj] in 1f), so a writer can identify the state the  *)
(*  PAYLOAD existentially names with the era state its own resources are   *)
(*  about.  Without them the payload's [S] is underdetermined at exactly   *)
(*  the two fields a writer must re-prove its own clauses at -- [fn_ent]   *)
(*  (whose only pin, [ind_bytes_inj], needs the entry array's LENGTH) and  *)
(*  [fn_blk]'s DOMAIN -- and no era-side fact reaches an existential.      *)
(*  See claude-notes/projects/durable-disk.md item 4b.                     *)
(* ===================================================================== *)
Record inode_repr (n : fs_node) : Prop := MkInodeRepr {
  inr_rec_wf   : dinode_wf (fn_rec n);
  inr_ent_len  : length (fn_ent n) = FS_NINDIRECT;
  inr_ind_zero : fn_indb n = 0 -> fn_ent n = replicate FS_NINDIRECT (bv_0 32);
  inr_blk_dom  : forall k, (k < FS_MAXFILE)%nat ->
                   (is_Some (fn_blk n !! k) <-> fn_naddr n k <> 0);
  inr_blk_top  : forall k, (FS_MAXFILE <= k)%nat -> fn_blk n !! k = None;
}.

Global Arguments inr_rec_wf {_} _.
Global Arguments inr_ent_len {_} _.
Global Arguments inr_ind_zero {_} _.
Global Arguments inr_blk_dom {_} _.
Global Arguments inr_blk_top {_} _.

Lemma inode_repr_of_local (i : Z) (n : fs_node) :
  inode_local i n -> inode_repr n.
Proof.
  intros Hl. split.
  - exact (inl_rec_wf Hl).
  - exact (inl_ent_len Hl).
  - exact (inl_ind_zero Hl).
  - exact (inl_blk_dom Hl).
  - exact (inl_blk_top Hl).
Qed.

(* ===================================================================== *)
(*  1b. THE BYTE HALF: the tie, and the USED-SET COUPLING                 *)
(*                                                                        *)
(*  THE ACCUMULATED PURE CONTENT (fs-state.md 4^9, addendum 7): an         *)
(*  abstract state [S] and the committed block map [D] agree at [S]'s      *)
(*  FOOTPRINT, and the state's own blocks are laid out DISJOINTLY inside   *)
(*  the bitmap's used set.  This half is true EVEN MID-OPERATION, which is *)
(*  why it -- and not [snap_ok] -- is what a batch accumulates per write.  *)
(*                                                                        *)
(*  Every byte clause names ONE object and its own bytes.  Three do not,   *)
(*  and each is named at its definition:                                   *)
(*                                                                        *)
(*  - [snap_dom], the inode map's DOMAIN over the region.  It is           *)
(*    fs-state.md 4.5 (2)'s per-inum EXISTENCE witness and 3c's third      *)
(*    [dgeo_ok] equation, and under snapshots it is by construction: the   *)
(*    value [S] is read off the era's own top-map authority, whose domain  *)
(*    IS the region's inums.                                              *)
(*  - [snap_links], the link family's validity.  It is the tokens-<=-nlink *)
(*    law, which fs-state.md section 7 already names as the one            *)
(*    whole-state fact in the design; it is never MAINTAINED here, only    *)
(*    carried, and the allocator needs it because [own_alloc] needs a      *)
(*    valid element.                                                       *)
(*  - [snap_bsz], "every block of [D] is a whole block", which is the      *)
(*    log's own row (b) property.                                          *)
(*                                                                        *)
(*  THE COUPLING -- [snap_meta_used], [snap_own_used], [snap_disj] -- IS   *)
(*  THE ONE SANCTIONED WHOLE-STATE PURE CLAUSE (fs-state.md 4^9 (7)):      *)
(*  section 0's LETTER is bent here and nowhere else, and its SPIRIT       *)
(*  (local maintenance) holds.  What it BUYS is exactly                    *)
(*  [snap_untouched_of_own] and [snap_untouched_of_free] in 1e below: the  *)
(*  frame's hypothesis quantifies over every inode of [S], and the         *)
(*  coupling turns it into a fact ONE writer holds about ONE object: that  *)
(*  the block is its own node's, or that the block's bit read CLEAR -- the *)
(*  latter straight off the adopting writer's own bitmap atomic update.    *)
(*  No writer ever meets the quantifier.                                   *)
(* ===================================================================== *)
Record snap_bytes (S : fs_state_rec) (D : gmap Z (list (bv 8))) : Prop :=
  MkSnapBytes {
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
  (* the inodes: range, representation, and the three byte ties *)
  sk_inum   : forall i n, fss_inodes S !! i = Some n -> 0 <= i < 2 ^ 32;
  sk_repr   : forall i n, fss_inodes S !! i = Some n -> inode_repr n;
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
  (* ---- THE USED-SET COUPLING ---- *)
  (* the metadata roles are MARKED IN USE, so a block whose bit reads clear
     is none of them *)
  sk_meta_used : forall b, snap_meta S b -> b ∈ fss_used S;
  (* every node's own blocks are marked in use, and none of them is a
     metadata block *)
  sk_own_used  : forall i n b, fss_inodes S !! i = Some n -> fn_owns n b ->
                   b ∈ fss_used S /\ ~ snap_meta S b;
  (* ...and no two nodes share one *)
  sk_disj      : forall i n j m b,
                   fss_inodes S !! i = Some n -> fss_inodes S !! j = Some m ->
                   fn_owns n b -> fn_owns m b -> i = j;
}.

Global Arguments sk_bsz {_ _} _.
Global Arguments sk_sb {_ _} _.
Global Arguments sk_parse {_ _} _.
Global Arguments sk_bmap {_ _} _.
Global Arguments sk_pool {_ _} _.
Global Arguments sk_inum {_ _} _.
Global Arguments sk_repr {_ _} _.
Global Arguments sk_rec {_ _} _.
Global Arguments sk_blk {_ _} _.
Global Arguments sk_ind {_ _} _.
Global Arguments sk_dom {_ _} _.
Global Arguments sk_links {_ _} _.
Global Arguments sk_meta_used {_ _} _.
Global Arguments sk_own_used {_ _} _.
Global Arguments sk_disj {_ _} _.

(* ===================================================================== *)
(*  1c. THE LOCAL HALF, AND THE TIE THE ALLOCATOR TAKES                   *)
(*                                                                        *)
(*  [snap_local] is the per-inode clauses and NOTHING ELSE -- it does not  *)
(*  mention [D] at all, which is why no write can disturb it and why it    *)
(*  does not have to be carried through one.  It is FALSE mid-operation    *)
(*  (create's window between [ip->nlink = 1] and its two [dirlink]s is the *)
(*  worked case), so it is not accumulated per write: each operation       *)
(*  re-establishes it at its own objects as [SpecEndOp]'s pure residue,    *)
(*  and the objects it did not touch ride the frame.  A snapshot is        *)
(*  quiescence-only, so it is demanded exactly where it is true.           *)
(* ===================================================================== *)
Definition snap_local (S : fs_state_rec) : Prop :=
  forall i n, fss_inodes S !! i = Some n -> inode_local i n.

(* THE TIE THE ALLOCATOR TAKES: both halves.  The split above is about what
   a BATCH accumulates; a COMMIT proves this. *)
Definition snap_ok (S : fs_state_rec) (D : gmap Z (list (bv 8))) : Prop :=
  snap_bytes S D /\ snap_local S.

(* the two projections, so that a consumer that wants one clause of the
   byte half names it exactly as it did at the unsplit record *)
Definition sk_bytes {S D} (H : snap_ok S D) : snap_bytes S D := proj1 H.
Definition sk_local {S D} (H : snap_ok S D) : snap_local S := proj2 H.

Lemma snap_ok_intro (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
  snap_bytes S D -> snap_local S -> snap_ok S D.
Proof. intros Hb Hl. exact (conj Hb Hl). Qed.

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
  intros [Hok Hloc] Hi.
  destruct (sk_dom Hok i Hi) as [n Hn].
  exists n. split; [exact Hn |]. split; [exact (Hloc i n Hn) |].
  exact (sk_rec Hok i n Hn).
Qed.

(* ===================================================================== *)
(*  1b. THE ENCODING IS INJECTIVE, AND WHAT THAT BUYS                     *)
(*                                                                        *)
(*  The whole point of the snapshot registry over the flat byte blob is    *)
(*  that the durable side now carries an ABSTRACT STATE, so a client can   *)
(*  learn a fact about an INODE and not merely about a byte.  Turning a    *)
(*  byte fact into a node fact is exactly injectivity of the encoder, and  *)
(*  the tree did not have it.                                             *)
(*                                                                        *)
(*  FOR RELOCATION: [bv16_eq_of_bytes] / [bv32_eq_of_bytes] belong in      *)
(*  [RiscvModelBytes.v] beside [bv_eq_of_bytes]; [word_bytes_inj] /        *)
(*  [ind_bytes_inj] in [BlockWords.v] and [half_bytes_inj] /               *)
(*  [dinode_bytes_inj] in [DinodeEnc.v], each beside its encoder.  They    *)
(*  are here because an additive change to a file that low rebuilds its    *)
(*  whole cone on every iteration -- durable-notes.md, an ADDITIVE change *)
(*  to a shared invariant file belongs in a NEW leaf file.                 *)
(* ===================================================================== *)

Lemma bv16_eq_of_bytes (w w' : bv 16) :
  nth_byte w 0 = nth_byte w' 0 -> nth_byte w 1 = nth_byte w' 1 -> w = w'.
Proof.
  intros H0 H1. apply (bv_eq_of_bytes (n := 2%N)).
  intros j Hj. destruct j as [| [| j]]; [exact H0 | exact H1 |].
  exfalso. rewrite Nat2N.inj_succ Nat2N.inj_succ in Hj. lia.
Qed.

Lemma bv32_eq_of_bytes (w w' : bv 32) :
  nth_byte w 0 = nth_byte w' 0 -> nth_byte w 1 = nth_byte w' 1 ->
  nth_byte w 2 = nth_byte w' 2 -> nth_byte w 3 = nth_byte w' 3 -> w = w'.
Proof.
  intros H0 H1 H2 H3. apply (bv_eq_of_bytes (n := 4%N)).
  intros j Hj. destruct j as [| [| [| [| j]]]];
    [exact H0 | exact H1 | exact H2 | exact H3 |].
  exfalso.
  rewrite Nat2N.inj_succ Nat2N.inj_succ Nat2N.inj_succ Nat2N.inj_succ in Hj.
  lia.
Qed.

(* [injection] on a list of BITVECTORS goes one constructor too far -- it
   decomposes the [BV] record itself and hands back an equation between two
   [bv_unsigned] projections, which the byte lemmas above cannot take.  So
   the elements are read out positionally instead, where [!!!] on a literal
   list is conversion. *)
Lemma half_bytes_inj (w w' : bv 16) : half_bytes w = half_bytes w' -> w = w'.
Proof.
  intros H. apply bv16_eq_of_bytes.
  - change (nth_byte w 0) with (half_bytes w !!! 0%nat).
    change (nth_byte w' 0) with (half_bytes w' !!! 0%nat). by rewrite H.
  - change (nth_byte w 1) with (half_bytes w !!! 1%nat).
    change (nth_byte w' 1) with (half_bytes w' !!! 1%nat). by rewrite H.
Qed.

Lemma word_bytes_inj (w w' : bv 32) : word_bytes w = word_bytes w' -> w = w'.
Proof.
  intros H. apply bv32_eq_of_bytes.
  - change (nth_byte w 0) with (word_bytes w !!! 0%nat).
    change (nth_byte w' 0) with (word_bytes w' !!! 0%nat). by rewrite H.
  - change (nth_byte w 1) with (word_bytes w !!! 1%nat).
    change (nth_byte w' 1) with (word_bytes w' !!! 1%nat). by rewrite H.
  - change (nth_byte w 2) with (word_bytes w !!! 2%nat).
    change (nth_byte w' 2) with (word_bytes w' !!! 2%nat). by rewrite H.
  - change (nth_byte w 3) with (word_bytes w !!! 3%nat).
    change (nth_byte w' 3) with (word_bytes w' !!! 3%nat). by rewrite H.
Qed.

Lemma ind_bytes_inj (e e' : list (bv 32)) :
  length e = length e' -> ind_bytes e = ind_bytes e' -> e = e'.
Proof.
  revert e'. induction e as [| w e IH]; intros [| w' e'] Hlen H;
    [reflexivity | simpl in Hlen; lia | simpl in Hlen; lia |].
  rewrite !ind_bytes_cons in H.
  assert (Hl : length (word_bytes w) = length (word_bytes w'))
    by (rewrite !word_bytes_length //).
  destruct (app_inj_1 _ _ _ _ Hl H) as [Hw He].
  f_equal; [exact (word_bytes_inj w w' Hw) |].
  apply IH; [simpl in Hlen; lia | exact He].
Qed.

(* THE ENCODER IS INJECTIVE ON WELL-FORMED RECORDS.  [dinode_wf] is needed
   for the address array alone: two records whose [di_addrs] have different
   lengths encode to byte lists of different lengths, and the peel below is
   what needs them equal. *)
Lemma dinode_bytes_inj (d d' : dinode) :
  dinode_wf d -> dinode_wf d' -> dinode_bytes d = dinode_bytes d' -> d = d'.
Proof.
  destruct d as [ty ma mi nl sz ad]; destruct d' as [ty' ma' mi' nl' sz' ad'].
  rewrite /dinode_wf /dinode_bytes.
  cbn [di_type di_major di_minor di_nlink di_size di_addrs].
  intros Had Had' H.
  (* the five lengths as NAMED facts: an inline [ltac:] in an argument
     position whose expected type is still an evar is elaborated before the
     conclusion is unified, and the [rewrite] then has nothing to hit
     (durable-notes.md, "Inline [ltac:] in argument position") *)
  assert (Hh : forall a b : bv 16,
                 length (half_bytes a) = length (half_bytes b))
    by (intros a b; rewrite !half_bytes_length //).
  assert (Hw : forall a b : bv 32,
                 length (word_bytes a) = length (word_bytes b))
    by (intros a b; rewrite !word_bytes_length //).
  destruct (app_inj_1 _ _ _ _ (Hh ty ty') H) as [Hty H1].
  destruct (app_inj_1 _ _ _ _ (Hh ma ma') H1) as [Hma H2].
  destruct (app_inj_1 _ _ _ _ (Hh mi mi') H2) as [Hmi H3].
  destruct (app_inj_1 _ _ _ _ (Hh nl nl') H3) as [Hnl H4].
  destruct (app_inj_1 _ _ _ _ (Hw sz sz') H4) as [Hsz Had2].
  f_equal.
  - exact (half_bytes_inj _ _ Hty).
  - exact (half_bytes_inj _ _ Hma).
  - exact (half_bytes_inj _ _ Hmi).
  - exact (half_bytes_inj _ _ Hnl).
  - exact (word_bytes_inj _ _ Hsz).
  - apply ind_bytes_inj; [rewrite Had Had' // | exact Had2].
Qed.

(* ...hence a record IS determined by the bytes of the slot it sits in *)
Lemma rec_in_blk_inj (bs : list (bv 8)) (off : Z) (dn dn' : dinode) :
  dinode_wf dn -> dinode_wf dn' ->
  rec_in_blk bs off dn -> rec_in_blk bs off dn' -> dn = dn'.
Proof.
  intros Hwf Hwf' (pre & post & Hbs & Hlen) (pre' & post' & Hbs' & Hlen').
  assert (Hpre : length pre = length pre') by lia.
  rewrite Hbs in Hbs'.
  destruct (app_inj_1 _ _ _ _ Hpre Hbs') as [_ Hrest].
  assert (Hl : length (dinode_bytes dn) = length (dinode_bytes dn'))
    by (rewrite (dinode_bytes_length dn Hwf) (dinode_bytes_length dn' Hwf') //).
  destruct (app_inj_1 _ _ _ _ Hl Hrest) as [Hd _].
  exact (dinode_bytes_inj dn dn' Hwf Hwf' Hd).
Qed.

(* ===================================================================== *)
(*  1c. WHAT A DURABLE BYTE FACT SAYS ABOUT THE SNAPSHOT'S STATE          *)
(* ===================================================================== *)

(* THE RECORD.  What the committed map holds at inum [i]'s slot IS the
   snapshot node's record -- which is the step from a fact about the
   durable disk's BYTES to a fact about the durable FILE SYSTEM,
   i.e. the whole of what the snapshot registry adds over the flat blob. *)
Lemma snap_ok_rec_of_bytes (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (bs : list (bv 8)) (dn : dinode) :
  snap_ok S D -> snap_inum_ok S i ->
  D !! (sb_inodestart (fss_sb S) + i `div` 16) = Some bs ->
  rec_in_blk bs (64 * (i `mod` 16)) dn -> dinode_wf dn ->
  exists n, fss_inodes S !! i = Some n /\ fn_rec n = dn /\ inode_local i n.
Proof.
  intros Hok Hi Hbs Hin Hwf.
  destruct (snap_ok_inode S D i Hok Hi) as (n & Hn & Hloc & bs' & Hbs' & Hin').
  rewrite Hbs in Hbs'. injection Hbs' as <-.
  exists n. split; [exact Hn |]. split; [| exact Hloc].
  exact (rec_in_blk_inj bs _ (fn_rec n) dn (inl_rec_wf Hloc) Hwf Hin' Hin).
Qed.

(* THE DATA.  A slot below the node's size is a block of [D], at the node's
   own reading -- so every dirent fact about a node's [fn_data] is a fact
   about the committed map's blocks. *)
Lemma snap_ok_data (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (k : nat) :
  snap_ok S D -> fss_inodes S !! i = Some n ->
  (k < FS_MAXFILE)%nat -> Z.of_nat k * BSIZE_z < fn_size n ->
  D !! fn_naddr n k = Some (fn_data n k).
Proof.
  intros [Hok Hloc] Hn Hk Hlt.
  destruct (inode_local_data_owned i n k (Hloc i n Hn) Hk Hlt)
    as (bs & Hbs & Hdat & _).
  rewrite Hdat. exact (sk_blk Hok i n k bs Hn Hbs).
Qed.

(* THE DIRECTORY ENTRY.  A pure reading of [dir_entries], stated here
   because the spike's parent half is its one consumer; FOR RELOCATION it
   belongs in [FsStateInode.v] beside [dir_entries]. *)
Lemma dir_entries_of_first (np : fs_node) (s : fname) (z : Z) (k : nat) :
  fn_is_dir np = true ->
  dir_first (fn_data np) (fn_nrec np) s = Some k ->
  bv_unsigned (dir_inum (fn_data np) k) = z ->
  dir_entries np !! s = Some z.
Proof.
  intros Hdir Hfirst Hinum.
  rewrite /dir_entries Hdir.
  apply dir_view_lookup_Some. exists k. split; [exact Hfirst | exact Hinum].
Qed.

(* ===================================================================== *)
(*  1d. THE TWO SHAPES THE SPIKE THEOREM READS OFF A SNAPSHOT             *)
(*                                                                        *)
(*  Each side is a NAMED [Prop] rather than inline arithmetic, because     *)
(*  both appear inside a [⌜ ⌝] where the ambient scope is [type_scope]     *)
(*  and [a + b] would parse as [sum].                                     *)
(* ===================================================================== *)

(* "the committed map's inode block holds [dn] at inum [i]'s slot" *)
Definition snap_slot_holds (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (dn : dinode) : Prop :=
  exists bs, D !! (sb_inodestart (fss_sb S) + i `div` 16) = Some bs
          /\ rec_in_blk bs (64 * (i `mod` 16)) dn.

(* "the durable file system's inode [i] IS the record [dn]" *)
Definition snap_node_is (S : fs_state_rec) (i : Z) (dn : dinode) : Prop :=
  exists n, fss_inodes S !! i = Some n /\ fn_rec n = dn /\ inode_local i n.

(* "the durable file system's directory [p] maps [s] to [z]" *)
Definition snap_dir_entry (S : fs_state_rec) (p : Z) (s : fname) (z : Z)
    : Prop :=
  exists np, fss_inodes S !! p = Some np /\ fn_is_dir np = true
          /\ dir_entries np !! s = Some z.

Lemma snap_ok_node_of_slot (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (dn : dinode) :
  snap_ok S D -> snap_inum_ok S i -> dinode_wf dn ->
  snap_slot_holds S D i dn -> snap_node_is S i dn.
Proof.
  intros Hok Hi Hwf (bs & Hbs & Hin).
  destruct (snap_ok_rec_of_bytes S D i bs dn Hok Hi Hbs Hin Hwf)
    as (n & Hn & Hrec & Hloc).
  exists n. split_and!; [exact Hn | exact Hrec | exact Hloc].
Qed.

Lemma snap_dir_entry_of_first (S : fs_state_rec) (p : Z) (np : fs_node)
    (s : fname) (z : Z) (k : nat) :
  fss_inodes S !! p = Some np -> fn_is_dir np = true ->
  dir_first (fn_data np) (fn_nrec np) s = Some k ->
  bv_unsigned (dir_inum (fn_data np) k) = z ->
  snap_dir_entry S p s z.
Proof.
  intros Hp Hdir Hfirst Hinum.
  exists np. split_and!;
    [exact Hp | exact Hdir | exact (dir_entries_of_first np s z k Hdir Hfirst Hinum)].
Qed.

(* ===================================================================== *)
(*  1e. THE ONE-BLOCK FRAME, AND THE COUPLING THAT SUPPLIES ITS FACT      *)
(*                                                                        *)
(*  A batch's writes have to carry the tie from the previous commit's      *)
(*  state to the next one's, and the part of that which is FRAME -- the    *)
(*  objects the batch did not touch -- is [snap_bytes_frame].  Its         *)
(*  hypothesis [snap_untouched S b] is honest and is NOT per-object: no    *)
(*  clause of [snap_bytes S] may read block [b], which quantifies over     *)
(*  every inode of [S].                                                    *)
(*                                                                        *)
(*  THAT WAS THE RESIDUAL OBSTACLE OF THE FLIP, and the USED-SET COUPLING  *)
(*  (1b) is what retires it: neither of the two derivations below          *)
(*  quantifies over the state, so NO WRITER EVER MEETS THE QUANTIFIER.     *)
(*                                                                        *)
(*  - [snap_untouched_of_free]: "b's bit reads CLEAR".  A block outside    *)
(*    the used set is no metadata block ([sk_meta_used]) and in no node's  *)
(*    footprint ([sk_own_used]).  This is the ADOPT case, and the fact is  *)
(*    exactly what the adopting writer reads off its OWN bitmap atomic     *)
(*    update -- balloc's scan found the bit zero before it set it.         *)
(*  - [snap_untouched_of_own]: "b is MY node's block".  Then it is no      *)
(*    metadata block ([sk_own_used] again) and no OTHER node's             *)
(*    ([sk_disj]), so every clause but my own frames.  This is what a data *)
(*    or indirect-block writer holds from its own splice fact.             *)
(*                                                                        *)
(*  The second one is stated as the residue [snap_untouched_but], since a  *)
(*  writer at its own block DOES move its own clauses; the composite       *)
(*  "frame everything else and re-prove mine" is the supplier lane's, and  *)
(*  is one [snap_bytes] constructor over these two plus the writer's own   *)
(*  splice fact.                                                           *)
(* ===================================================================== *)

Definition snap_untouched (S : fs_state_rec) (b : Z) : Prop :=
  ~ snap_meta S b
  /\ (forall i n, fss_inodes S !! i = Some n -> ~ fn_owns n b).

(* ...and the same with ONE inode exempted: the shape a writer at its own
   block has, since its own clauses are the ones it re-proves. *)
Definition snap_untouched_but (S : fs_state_rec) (i : Z) (b : Z) : Prop :=
  ~ snap_meta S b
  /\ (forall j m, fss_inodes S !! j = Some m -> j <> i -> ~ fn_owns m b).

(* THE ADOPT CASE, off the writer's own bitmap atomic update. *)
Lemma snap_untouched_of_free (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (b : Z) :
  snap_bytes S D -> b ∉ fss_used S -> snap_untouched S b.
Proof.
  intros Hok Hfree. split.
  - intros Hm. exact (Hfree (sk_meta_used Hok b Hm)).
  - intros i n Hi Hown. exact (Hfree (proj1 (sk_own_used Hok i n b Hi Hown))).
Qed.

(* THE OWN CASE, off the writer's own splice fact. *)
Lemma snap_untouched_of_own (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (b : Z) :
  snap_bytes S D -> fss_inodes S !! i = Some n -> fn_owns n b ->
  snap_untouched_but S i b.
Proof.
  intros Hok Hi Hown. split.
  - exact (proj2 (sk_own_used Hok i n b Hi Hown)).
  - intros j m Hj Hne Hownj. exact (Hne (sk_disj Hok j m i n b Hj Hi Hownj Hown)).
Qed.

(* the [snap_meta] arms, read out one at a time: this is how a caller that
   holds [~ snap_meta S b] discharges the three clause-level disequalities *)
Lemma snap_meta_sb (S : fs_state_rec) (b : Z) :
  ~ snap_meta S b -> b <> SB_BNO.
Proof. intros Hm ->. apply Hm. by left. Qed.

Lemma snap_meta_bmap (S : fs_state_rec) (b : Z) :
  ~ snap_meta S b -> b <> sb_bmapstart (fss_sb S).
Proof. intros Hm ->. apply Hm. right. by left. Qed.

Lemma snap_meta_reg (S : fs_state_rec) (b i : Z) (n : fs_node) :
  ~ snap_meta S b -> fss_inodes S !! i = Some n ->
  b <> sb_inodestart (fss_sb S) + i `div` 16.
Proof.
  intros Hm Hi Heq. apply Hm. right. right. exists i.
  split; [by exists n | exact Heq].
Qed.

(* THE FRAME.  Only the byte half moves -- [snap_local] does not mention
   [D] at all, so a write cannot disturb it, which is the whole point of
   the split. *)
Lemma snap_bytes_frame (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (b : Z) (bs : list (bv 8)) :
  snap_bytes S D -> snap_untouched S b -> length bs = BSIZE ->
  snap_bytes S (<[b := bs]> D).
Proof.
  intros Hok (Hm & Hin) Hlen.
  (* one lookup transport, used at every clause that names a block *)
  assert (Hne : forall c cs, c <> b -> D !! c = Some cs ->
                  <[b := bs]> D !! c = Some cs).
  { intros c cs Hc Hcs. rewrite lookup_insert_ne; [exact Hcs |].
    exact (not_eq_sym Hc). }
  split.
  - intros c cs Hcs.
    destruct (decide (c = b)) as [-> | Hc].
    + rewrite lookup_insert in Hcs. injection Hcs as <-. exact Hlen.
    + rewrite lookup_insert_ne in Hcs; [| exact (not_eq_sym Hc)].
      exact (sk_bsz Hok c cs Hcs).
  - exact (Hne _ _ (not_eq_sym (snap_meta_sb S b Hm)) (sk_sb Hok)).
  - exact (sk_parse Hok).
  - exact (Hne _ _ (not_eq_sym (snap_meta_bmap S b Hm)) (sk_bmap Hok)).
  - intros c Hc Hcu.
    destruct (decide (c = b)) as [-> | Hcb].
    + rewrite lookup_insert. by eexists.
    + destruct (sk_pool Hok c Hc Hcu) as [cs Hcs].
      exists cs. exact (Hne _ _ Hcb Hcs).
  - exact (sk_inum Hok).
  - exact (sk_repr Hok).
  - intros i n Hi.
    destruct (sk_rec Hok i n Hi) as (cs & Hcs & Hrin).
    exists cs. split; [| exact Hrin].
    exact (Hne _ _ (not_eq_sym (snap_meta_reg S b i n Hm Hi)) Hcs).
  - intros i n k cs Hi Hk.
    assert (Hb : fn_naddr n k <> b).
    { intro Heq. apply (Hin i n Hi). left. exists k. split; [by exists cs | exact Heq]. }
    exact (Hne _ _ Hb (sk_blk Hok i n k cs Hi Hk)).
  - intros i n Hi Hnz.
    assert (Hb : fn_indb n <> b).
    { intro Heq. apply (Hin i n Hi). right. split; [exact Hnz | exact Heq]. }
    exact (Hne _ _ Hb (sk_ind Hok i n Hi Hnz)).
  - exact (sk_dom Hok).
  - exact (sk_links Hok).
  - exact (sk_meta_used Hok).
  - exact (sk_own_used Hok).
  - exact (sk_disj Hok).
Qed.

(* ...and the reading at the whole tie, for a consumer that holds both
   halves and wants both back. *)
Lemma snap_ok_frame (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (b : Z) (bs : list (bv 8)) :
  snap_ok S D -> snap_untouched S b -> length bs = BSIZE ->
  snap_ok S (<[b := bs]> D).
Proof.
  intros [Hok Hloc] Hu Hlen.
  exact (conj (snap_bytes_frame S D b bs Hok Hu Hlen) Hloc).
Qed.

(* ===================================================================== *)
(*  1f. THE BYTE HALF PINS THE OBJECTS                                    *)
(*                                                                        *)
(*  A payload accumulated as a PURE fact binds its state EXISTENTIALLY, so *)
(*  a writer that must move it owes a fact about a state it did not        *)
(*  choose -- while every resource it holds is about the ERA's state.      *)
(*  These are the bridge, and they are what makes the accumulation         *)
(*  state-free: at one committed map, any two states the byte half admits  *)
(*  agree on the SUPERBLOCK, on EVERY NODE, and on the BITMAP's bits.  So  *)
(*  a writer reads the payload's state as its own and re-proves its own    *)
(*  clauses from its own splice fact; the objects it did not touch ride    *)
(*  1e's frame.                                                            *)
(*                                                                        *)
(*  The used set is pinned only WITHIN THE BITMAP BLOCK, which is right    *)
(*  and not a weakness: nothing reads a bit above the block               *)
(*  ([BitmapInv.bitmap_ok] and [free_set] both cut at [sb_size]), so two   *)
(*  states differing only up there are indistinguishable to every consumer *)
(*  -- the same argument [FsImg.fs_bmap_set]'s header makes.               *)
(* ===================================================================== *)

Lemma snap_bytes_sb_inj (S S' : fs_state_rec) (D : gmap Z (list (bv 8))) :
  snap_bytes S D -> snap_bytes S' D ->
  fss_sbb S = fss_sbb S' /\ fss_sb S = fss_sb S'.
Proof.
  intros H H'.
  assert (Hb : fss_sbb S = fss_sbb S').
  { pose proof (sk_sb H) as Hs. rewrite (sk_sb H') in Hs.
    by injection Hs as <-. }
  split; [exact Hb |].
  pose proof (sk_parse H) as Hp. rewrite Hb in Hp.
  rewrite (sk_parse H') in Hp. by injection Hp as <-.
Qed.

(* the reading of a node is a function of its record and its entry array,
   so the two field equalities carry every derived address *)
Lemma fn_naddr_of_fields (n n' : fs_node) (k : nat) :
  fn_rec n = fn_rec n' -> fn_ent n = fn_ent n' ->
  fn_naddr n k = fn_naddr n' k.
Proof. intros Hr He. rewrite /fn_naddr Hr He //. Qed.

Lemma fn_indb_of_rec (n n' : fs_node) :
  fn_rec n = fn_rec n' -> fn_indb n = fn_indb n'.
Proof. intros Hr. rewrite /fn_indb Hr //. Qed.

Theorem snap_bytes_node_inj (S S' : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n n' : fs_node) :
  snap_bytes S D -> snap_bytes S' D ->
  fss_inodes S !! i = Some n -> fss_inodes S' !! i = Some n' -> n = n'.
Proof.
  intros H H' Hi Hi'.
  destruct (snap_bytes_sb_inj S S' D H H') as [_ Hsb].
  pose proof (sk_repr H i n Hi) as Hrp.
  pose proof (sk_repr H' i n' Hi') as Hrp'.
  (* ---- the record ---- *)
  assert (Hr : fn_rec n = fn_rec n').
  { destruct (sk_rec H i n Hi) as (bs & Hbs & Hin).
    destruct (sk_rec H' i n' Hi') as (bs' & Hbs' & Hin').
    rewrite -Hsb in Hbs'. rewrite Hbs in Hbs'. injection Hbs' as <-.
    exact (rec_in_blk_inj bs _ (fn_rec n) (fn_rec n')
             (inr_rec_wf Hrp) (inr_rec_wf Hrp') Hin Hin'). }
  pose proof (fn_indb_of_rec n n' Hr) as Hib.
  (* ---- the entry array ---- *)
  assert (He : fn_ent n = fn_ent n').
  { destruct (decide (fn_indb n = 0)) as [Hz | Hnz].
    - rewrite (inr_ind_zero Hrp Hz) (inr_ind_zero Hrp' ltac:(rewrite -Hib; exact Hz)) //.
    - pose proof (sk_ind H i n Hi Hnz) as Hd.
      pose proof (sk_ind H' i n' Hi' ltac:(rewrite -Hib; exact Hnz)) as Hd'.
      rewrite -Hib in Hd'. rewrite Hd in Hd'. injection Hd' as Hib2.
      apply (ind_bytes_inj (fn_ent n) (fn_ent n'));
        [rewrite (inr_ent_len Hrp) (inr_ent_len Hrp') // | exact Hib2]. }
  (* ---- the slot contents ---- *)
  assert (Hbk : fn_blk n = fn_blk n').
  { apply map_eq. intros k.
    destruct (decide (k < FS_MAXFILE)%nat) as [Hk | Hk]; last first.
    { rewrite (inr_blk_top Hrp k ltac:(lia)) (inr_blk_top Hrp' k ltac:(lia)) //. }
    pose proof (fn_naddr_of_fields n n' k Hr He) as Hna.
    destruct (fn_blk n !! k) as [bs|] eqn:Eb;
      destruct (fn_blk n' !! k) as [bs'|] eqn:Eb'.
    - pose proof (sk_blk H i n k bs Hi Eb) as Hd.
      pose proof (sk_blk H' i n' k bs' Hi' Eb') as Hd'.
      rewrite -Hna in Hd'. rewrite Hd in Hd'. by injection Hd' as <-.
    - exfalso.
      assert (Hne : fn_naddr n' k <> 0).
      { rewrite -Hna. apply (proj1 (inr_blk_dom Hrp k Hk)). by exists bs. }
      destruct (proj2 (inr_blk_dom Hrp' k Hk) Hne) as [x Hx]. congruence.
    - exfalso.
      assert (Hne : fn_naddr n k <> 0).
      { rewrite Hna. apply (proj1 (inr_blk_dom Hrp' k Hk)). by exists bs'. }
      destruct (proj2 (inr_blk_dom Hrp k Hk) Hne) as [x Hx]. congruence.
    - reflexivity. }
  destruct n as [r e m]; destruct n' as [r' e' m'].
  cbn in Hr, He, Hbk. by subst.
Qed.

(* ...and the bitmap's bits, inside the block *)
Lemma snap_bytes_used_agree (S S' : fs_state_rec) (D : gmap Z (list (bv 8)))
    (b : Z) :
  snap_bytes S D -> snap_bytes S' D -> 0 <= b < 8 * Z.of_nat BSIZE ->
  (b ∈ fss_used S <-> b ∈ fss_used S').
Proof.
  intros H H' Hb.
  destruct (snap_bytes_sb_inj S S' D H H') as [_ Hsb].
  (* NOT [injection]: both sides are [bm_bytes BSIZE _], a 1024-element
     list, and [injection]'s decomposition normalises it -- the sentence
     does not come back (durable-notes.md, a big-op over a literal-sized
     list is a reduct, not a value).  [inj Some] is unification only. *)
  assert (Hm : bm_bytes BSIZE (fss_used S) = bm_bytes BSIZE (fss_used S')).
  { apply (inj Some). rewrite -(sk_bmap H) -(sk_bmap H') Hsb //. }
  pose proof (fs_bit_bm_bytes BSIZE (fss_used S) b Hb) as E.
  pose proof (fs_bit_bm_bytes BSIZE (fss_used S') b Hb) as E'.
  assert (Heq : bool_decide (b ∈ fss_used S) = bool_decide (b ∈ fss_used S')).
  { rewrite -E -E' Hm //. }
  (* the two [Decision]s are spelled out: [apply bool_decide_eq_true_1] on a
     goal that is not itself a [bool_decide] leaves the instance an evar *)
  split; intros Hin.
  - destruct (decide (b ∈ fss_used S')) as [Hy | Hn]; [exact Hy | exfalso].
    rewrite (@bool_decide_eq_true_2 (b ∈ fss_used S) _ Hin)
            (@bool_decide_eq_false_2 (b ∈ fss_used S') _ Hn) in Heq.
    discriminate.
  - destruct (decide (b ∈ fss_used S)) as [Hy | Hn]; [exact Hy | exfalso].
    rewrite (@bool_decide_eq_false_2 (b ∈ fss_used S) _ Hn)
            (@bool_decide_eq_true_2 (b ∈ fss_used S') _ Hin) in Heq.
    discriminate.
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
    intros [Hok Hloc]. iIntros "#Hled Hlinks".
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
        iPureIntro. exact (Hloc i n Hi).
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
    iMod (fs_links_alloc (fss_inodes S) (sk_links (sk_bytes Hok)))
      as (gl) "Hlinks".
    iMod (ghost_map_alloc (fss_inodes S)) as (gt) "[Hta Htf]".
    iModIntro. iExists g, gl, gt.
    iDestruct (snap_ledger_of_elems g gl gt D (sk_bsz (sk_bytes Hok)) with "Hbe")
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

  (* THE SPIKE'S DURABLE HALF, at the current snapshot: a byte fact about
     the committed map's inode block becomes a fact about the durable FILE
     SYSTEM's inode.  This is what the snapshot registry adds over the flat
     byte blob, and it is the reading [mknod_durable] is stated at. *)
  Lemma P_dur_node_of_slot D (i : Z) (dn : dinode) :
    dinode_wf dn ->
    P_dur D -∗
      ∃ S, ⌜snap_ok S D⌝
           ∗ ⌜snap_inum_ok S i -> snap_slot_holds S D i dn ->
              snap_node_is S i dn⌝
           ∗ P_dur D.
  Proof.
    iIntros (Hwf) "H".
    iDestruct (P_dur_tie_keep with "H") as (S Hok) "HP".
    iExists S. iFrame "HP". iSplitR; [iPureIntro; exact Hok |].
    iPureIntro. intros Hi Hslot.
    exact (snap_ok_node_of_slot S D i dn Hok Hi Hwf Hslot).
  Qed.

End Snap.
