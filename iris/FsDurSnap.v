(* FsDurSnap.v -- SNAPSHOT COMMITS: the durable file-system instance is
   ALLOCATED AFRESH at every group commit and never updated.

   Design of record: claude-notes/design/durable-fs-plan.md sections 2, 4
   and 5; the worklist is claude-notes/projects/durable-disk.md.

   THE ONE IDEA.  No durable ghost is ever moved.  At a group commit the
   committer ALLOCATES a fresh gname family at the quiescent state's
   values, proves the whole file-system predicate at BIRTH, and DISCARDS
   the previous instance (the logic is affine).  Allocation is
   unconditionally frame-preserving, so every update wall the project met
   -- the auth-in-frame refutation, the completeness demand, the accessor
   chain's missing intermediate object, the deferred ledger's cross-op
   eviction, the kinds tie's geometry -- is vacated by construction: there
   is nothing to update.

   WHAT THE TRANSPORT TAKES.  Its inputs are a VALUE and PURE FACTS, and
   NOTHING ELSE -- no era resource, no previous instance, no authority
   loan.  That is what makes it callable at the commit (where the era's
   pieces are distributed behind [iregN]/[ftopN]/[bitmapN] and the icache
   escrow, hence unreachable at any mask) and callable at BOOT to clone
   the current snapshot onto a fresh ERA family (plan section 5).

   THE POINTS-TO IS EXCLUSIVE AND THE LEDGER IS LINEAR.  [snap_gamma]'s
   [fsΦ] is the FULL ghost-map element [a -> v], exactly as the era's
   [FsBytesGamma.fs_gamma_L] is, and [fs_state_of_ledger] SPENDS its
   ledger: it cuts the flat byte map into the pieces [FsState.fs_state]
   asks for and hands each out once.  Two things follow, and both are the
   point of the shape:

   - the [∗] between two inodes of a durable [fs_state] MEANS something.
     Under a persistent points-to that conjunction is vacuous -- two
     inodes naming one block would satisfy it -- and disjointness would
     live only in a pure clause.  Here it is the resources.
   - the core is Γ-GENERIC IN EARNEST.  [fs_gamma_L] is not [□]-able, so
     only a linear core can serve BOTH the commit's allocation and the
     boot mint that re-founds an era from the current snapshot;
     [fs_state_of_ledger_era] is the check that it applies there verbatim.

   WHAT THE CUT SPENDS is disjointness, and every bit of it is a clause of
   [snap_bytes] (section 1b).  The used-set COUPLING
   ([sk_meta_used]/[sk_own_used]/[sk_disj]) separates the metadata roles,
   the nodes' own blocks and the free pool from one another; [sk_slot]
   separates one NODE's own slots from each other (the within-node
   companion of [sk_disj]); [sk_sbok] and [sk_reg] separate the three
   metadata roles -- block 1, the inode region, the bitmap block -- which
   is the superblock's own geometry and nothing more.

   [FsStateDefs.phi_excl] HOLDS AT THE SNAPSHOT ([snap_gamma_excl]), so
   [FsStateBitmap.free_pool_used] -- hence xv6's "freeing free block"
   panic arm -- and [FsStateDefs.blk_owned_ne] read on the durable side
   exactly as they do at the era's view.

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
Require Import RiscvPtsto.    (* [riscvGS] / [diskGhostG] -- IMPORTED, not
                                 merely required: a class reached through a
                                 transitive [Require] parses in a binder and
                                 silently becomes a VARIABLE               *)
Require Import FsBlocks.      (* [fs_names] -- the era's gname bundle       *)
Require Import FsBytesGamma.  (* [fs_gamma_L] -- the ERA's view record, for
                                 the non-vacuity check in section 9        *)
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

(* ...the same footprint INDEXED, so that "no block twice" can be said of
   ONE node.  Slot [k < FS_MAXFILE] is the data block the record's [k]th
   address names; slot [FS_MAXFILE] is the indirect block itself.  This is
   [FsImg.fs_slot] read off a node rather than off a raw record, and
   [fn_slot_inj] is [FsImg.fs_slot_inj]: the image path already takes it
   ([FsImgBridge.img_inode_blocks_res]), because it is what makes an
   inode's slot-keyed [∗] of blocks satisfiable at all. *)
Definition fn_slot (n : fs_node) (k : nat) : Z :=
  if decide (k = FS_MAXFILE) then fn_indb n else fn_naddr n k.

Definition fn_slot_inj (n : fs_node) : Prop :=
  forall k j : nat, (k <= FS_MAXFILE)%nat -> (j <= FS_MAXFILE)%nat ->
    fn_slot n k <> 0 -> fn_slot n k = fn_slot n j -> k = j.

(* the two readings, which is all any consumer wants of it *)
Lemma fn_slot_data (n : fs_node) (k : nat) :
  (k < FS_MAXFILE)%nat -> fn_slot n k = fn_naddr n k.
Proof. intros Hk. rewrite /fn_slot. destruct (decide (k = FS_MAXFILE)); [lia | done]. Qed.

Lemma fn_slot_ind (n : fs_node) : fn_slot n FS_MAXFILE = fn_indb n.
Proof.
  rewrite /fn_slot.
  destruct (decide (FS_MAXFILE = FS_MAXFILE)) as [_ | Hc];
    [reflexivity | exfalso; exact (Hc eq_refl)].
Qed.

Lemma fn_slot_data_ne (n : fs_node) (k j : nat) :
  fn_slot_inj n -> (k < FS_MAXFILE)%nat -> (j < FS_MAXFILE)%nat ->
  fn_naddr n k <> 0 -> k <> j -> fn_naddr n k <> fn_naddr n j.
Proof.
  intros Hinj Hk Hj Hnz Hne Heq. apply Hne.
  apply (Hinj k j ltac:(lia) ltac:(lia)).
  - rewrite (fn_slot_data n k Hk). exact Hnz.
  - rewrite (fn_slot_data n k Hk) (fn_slot_data n j Hj). exact Heq.
Qed.

Lemma fn_slot_ind_ne (n : fs_node) (k : nat) :
  fn_slot_inj n -> (k < FS_MAXFILE)%nat -> fn_indb n <> 0 ->
  fn_naddr n k <> fn_indb n.
Proof.
  intros Hinj Hk Hnz Heq.
  assert (HM : FS_MAXFILE = k).
  { apply (Hinj FS_MAXFILE k ltac:(lia) ltac:(lia)).
    - rewrite fn_slot_ind. exact Hnz.
    - rewrite fn_slot_ind (fn_slot_data n k Hk). exact (eq_sym Heq). }
  lia.
Qed.

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
(*  See claude-notes/design/durable-fs-plan.md section 4a.                 *)
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
(*  THE ACCUMULATED PURE CONTENT (plan section 4a): an abstract state      *)
(*  [S] and the committed block map [D] agree at [S]'s FOOTPRINT, and the  *)
(*  state's own blocks are laid out DISJOINTLY inside the bitmap's used    *)
(*  set.  This half is true EVEN MID-OPERATION, which is why it -- and     *)
(*  not [snap_ok] -- is what a batch accumulates per write.                *)
(*                                                                        *)
(*  Every byte clause names ONE object and its own bytes.  Three do not,   *)
(*  and each is named at its definition:                                   *)
(*                                                                        *)
(*  - [snap_dom], the inode map's DOMAIN over the region.  Under           *)
(*    snapshots it is by construction: the value [S] is read off the       *)
(*    era's own top-map authority, whose domain IS the region's inums.     *)
(*  - [snap_links], the link family's validity.  It is the tokens-<=-nlink *)
(*    law, which fs-state.md section 7 already names as the one            *)
(*    whole-state fact in the design; it is never MAINTAINED here, only    *)
(*    carried, and the allocator needs it because [own_alloc] needs a      *)
(*    valid element.                                                       *)
(*  - [snap_bsz], "every block of [D] is a whole block", which is the      *)
(*    log's own row (b) property.                                          *)
(*                                                                        *)
(*  THE COUPLING -- [snap_meta_used], [snap_own_used], [snap_disj] -- IS   *)
(*  THE ONE SANCTIONED WHOLE-STATE PURE CLAUSE (plan section 4a):          *)
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
  (* THE LINK FAMILY'S OWN VALIDITY, WITH THE ROOT'S KEEP-ALIVE SLACK
     (durable-disk lane E-clauses; plan section 5's third missing clause).
     The plain [✓ link_elem (fss_inodes S)] is the tokens-<=-nlink law of
     the family, which is what [FsState.fs_links_alloc] needs; the SLACK --
     one spare fragment at [ROOTINO] -- is what a BOOT MINT needs on top of
     it, because the era's inode region parks a keep-alive token at the root
     ([InodeRegion.ireg_keep], [ireg_root] being [ROOTINO]) that no
     directory entry accounts for: [FsStateInode.ent_tokenless] exempts a
     SELF record, so the root's [".."] carries none and the image's
     [nlink = 1] at the root would otherwise be unclaimed.  Stated as ONE
     clause rather than two because the plain form is its own left factor
     ([sk_links_plain] below) and the record has exactly two readers.
     [FsState.fs_boot_alloc_root_slack] is the mint's [own_alloc] at it:
     one allocation yields [fs_links] plus the spare token.
     The IMAGE discharges it from [FsImg.fsimg_wf_root_link] through
     [FsDurImg.img_link_valid]; the COMMIT reads it off the region's own
     [ireg_keep] beside the collected [FsState.fs_links]
     ([FsState.fs_links_valid_tok]). *)
  sk_links  : ✓ (link_elem (fss_inodes S) ⋅ link_tok_elem ROOTINO 1%nat);
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
  (* ---- THE THREE ROLES ARE THREE BLOCKS, AND A NODE'S SLOTS ARE ITS
     OWN.  What the coupling above does NOT say, and what a LINEAR ledger
     needs on top of it: the superblock's block, the inode region and the
     bitmap block are pairwise distinct (the superblock's own geometry,
     [FsImg.fs_sb_ok], plus "every named inum sits in the region"), and
     one node never names one block twice.  All three are per-object --
     [sk_sbok] is about the superblock alone, [sk_reg]/[sk_slot] about one
     inum -- and all three are maintained exactly as [sk_disj] is: an
     adopting writer's block read CLEAR while its own blocks are marked in
     use.  [sk_slot] is [FsImg.fs_slot_inj], which the image path already
     takes for the very same reason. *)
  sk_sbok      : fs_sb_ok (fss_sb S);
  sk_reg       : forall i n, fss_inodes S !! i = Some n ->
                   0 <= i /\ i `div` 16 < sb_bmapstart (fss_sb S)
                                          - sb_inodestart (fss_sb S);
  sk_slot      : forall i n, fss_inodes S !! i = Some n -> fn_slot_inj n;
  (* ---- THE REGION'S TAIL INUMS ARE NAMED (durable-disk lane E-boot;
     plan section 5's first missing clause).  [sk_dom] names the inums below
     [ninodes]; a BOOT MINT has to re-found the inode region, whose width is
     [16 * nib] with [nib = ninodes/16 + 1] -- mkfs rounds [ninodes] up to a
     whole block, and [InodeRegion.ireg_recs] is sixteen records per region
     block, so [IcacheBoot.ireg_alloc] / [ipool_alloc] / [ftop_alloc] all run
     over [region_inums nib] and not over [[0, ninodes)].  The width is
     spelled off [S]'s own superblock rather than taken as a parameter,
     because [snap_bytes] is a function of [S] and [D] alone.

     IT IS A DOMAIN ROW AND NOT A CONTENT CLAUSE, so section 0's local rule
     is untouched: it says nothing about any node.  Both producers have it:
     the image's node map IS [region_inums nib]
     ([FsCfgBoot.img_nodes_keys]), and at a commit the collected state is
     the [ftop] map restricted to the region ([FsCollect.col_hand]'s domain
     row, against [col_geom]'s width tie [cg_width]).
     LAST, so no destructuring pattern above moves. *)
  sk_regdom : forall i, 0 <= i < 16 * (sb_ninodes (fss_sb S) / 16 + 1) ->
                is_Some (fss_inodes S !! i);
  (* ---- THE THREE DIRECTORY CLAUSES THE ESCROW PAYLOADS CARRY
     (durable-disk lane E-clauses; plan section 5's mint).
     [FsStateInode.node_dir_local] is [DirView.dir_ok] (every live entry's
     inum is inside the region), [dir_dots_ix] (a live directory's records
     0 and 1 POSITIONALLY are the dots -- which [inl_dir_dot] /
     [inl_dir_dotdot] do NOT say: those are about the name -> inum view)
     and [dir_orphan_clean] (an orphan directory holds only dot records).
     [IcacheEscrow.ipool_alloc] and [ic_loaded] take all three, so a BOOT
     MINT that re-founds the pool from a snapshot needs them; the escrow's
     deposit arms re-prove exactly these at every [iunlock], so the commit
     reads them off the same payloads it reads [inode_local] off
     ([FsCollect.col_side]'s bundle arm).

     IT IS PER-OBJECT, and it is here rather than in [inode_local] because
     [dir_ok] needs the REGION'S WIDTH: [inode_local i n] takes an inum and
     a node and nothing else, while a [snap_bytes] clause may read [S]'s own
     superblock -- which is exactly how [sk_regdom] is stated, and
     [snap_nib] below is that same [ninodes/16 + 1].
     LAST, so no destructuring pattern above moves. *)
  sk_dirloc : forall i n, fss_inodes S !! i = Some n ->
                node_dir_local i (Z.to_nat (sb_ninodes (fss_sb S) / 16 + 1)) n;
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
Global Arguments sk_sbok {_ _} _.
Global Arguments sk_reg {_ _} _.
Global Arguments sk_slot {_ _} _.
Global Arguments sk_regdom {_ _} _.
Global Arguments sk_dirloc {_ _} _.

(* THE REGION'S WIDTH, off [S]'s own superblock: mkfs rounds [ninodes] up to
   a whole inode block, so the region is [ninodes/16 + 1] blocks and the
   inum space is [16 *] that.  It is the width [sk_regdom] is stated at and
   the one [sk_dirloc]'s [DirView.dir_ok] is bounded by; at the boot
   configuration it IS [IcacheRef.icfg_nib]
   ([FirstTok.col_geom_of_image]'s own hypothesis). *)
Definition snap_nib (S : fs_state_rec) : nat :=
  Z.to_nat (sb_ninodes (fss_sb S) / 16 + 1).

(* THE MINT-SIDE READING (durable-disk lane E-clauses).  The three
   [DirView] premises [IcacheEscrow.ipool_alloc] takes, off the snapshot's
   node -- so the boot mint's snapshot route has a twin of
   [FsCfgBoot.ipool_alloc_of_image]'s image route.  [nib] is the caller's
   region width, tied to the state's superblock exactly as
   [FsCollect.col_geom]'s [cg_width] ties it. *)
Lemma snap_node_dir_local (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (nib : nat) :
  snap_bytes S D -> fss_inodes S !! i = Some n ->
  Z.of_nat nib = sb_ninodes (fss_sb S) / 16 + 1 ->
  node_dir_local i nib n.
Proof.
  intros Hb Hi Hw.
  assert (Hnib : nib = snap_nib S).
  { rewrite /snap_nib -Hw Nat2Z.id //. }
  rewrite Hnib. exact (sk_dirloc Hb i n Hi).
Qed.

(* the plain family validity, which is [sk_links]'s own left factor: the
   allocator ([FsState.fs_links_alloc]) takes this, the mint takes the
   slacked form. *)
Definition sk_links_plain {S D} (H : snap_bytes S D)
  : ✓ link_elem (fss_inodes S) := cmra_valid_op_l _ _ (sk_links H).

(* ===================================================================== *)
(*  1b'. THE THREE METADATA ROLES ARE THREE DIFFERENT BLOCKS             *)
(*                                                                       *)
(*  The whole of what [sk_sbok] and [sk_reg] are for.  xv6's superblock   *)
(*  puts block 1 below the log, the log below the inode region and the    *)
(*  bitmap block above it, so the three roles cannot collide -- and the   *)
(*  region's upper end is the bitmap block itself, which is why [sk_reg]  *)
(*  is stated at [bmapstart - inodestart] rather than at [ninodes] (the   *)
(*  region's LAST block is partly unused, and the state may name its      *)
(*  inums; the image instance does).                                     *)
(* ===================================================================== *)

Lemma snap_sb_bmap_ne (S : fs_state_rec) :
  fs_sb_ok (fss_sb S) -> SB_BNO <> sb_bmapstart (fss_sb S).
Proof.
  intros Hok.
  pose proof (sbo_logstart _ Hok). pose proof (sbo_nlog _ Hok).
  pose proof (sbo_inodestart _ Hok). pose proof (sbo_bmapstart _ Hok).
  pose proof (sbo_ninodes _ Hok). unfold ROOTINO in *.
  assert (0 <= sb_ninodes (fss_sb S) `div` 16) by (apply Z.div_pos; lia).
  rewrite /SB_BNO. lia.
Qed.

(* THE THREE CUT CLAUSES ARE INHABITED at the REAL instance, and their
   witness is [FsAdequacyImg.fsimg_snap_ok] -- [snap_ok] at the literal
   mkfs image, unconditionally (plan section 7).  [FsDurImg.img_snap_ok]
   discharges [sk_sbok] off W1, [sk_reg] off "the region is exactly
   [[inodestart, bmapstart)]" and [sk_slot] off W4; the FREE inums, which
   W4 says nothing about, go through the one reading below -- a bare node
   names no block at all, so its footprint is injective for free. *)
Lemma fn_slot_inj_bare (n : fs_node) : fn_bare n -> fn_slot_inj n.
Proof.
  intros Hbare k j Hk Hj Hnz.
  exfalso. apply Hnz. rewrite /fn_slot.
  destruct (decide (k = FS_MAXFILE)) as [-> | Hne];
    [exact (fn_bare_indb n Hbare) |].
  exact (fn_bare_naddr n k Hbare ltac:(lia)).
Qed.

Lemma snap_reg_blk (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) :
  snap_bytes S D -> fss_inodes S !! i = Some n ->
  SB_BNO <> sb_inodestart (fss_sb S) + i `div` 16
  /\ sb_bmapstart (fss_sb S) <> sb_inodestart (fss_sb S) + i `div` 16.
Proof.
  intros Hb Hi.
  pose proof (sk_sbok Hb) as Hsb.
  destruct (sk_reg Hb i n Hi) as [Hi0 Hlt].
  pose proof (sbo_logstart _ Hsb). pose proof (sbo_nlog _ Hsb).
  pose proof (sbo_inodestart _ Hsb).
  assert (0 <= i `div` 16) by (apply Z.div_pos; lia).
  rewrite /SB_BNO. lia.
Qed.

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
  - exact (sk_sbok Hok).
  - exact (sk_reg Hok).
  - exact (sk_slot Hok).
  - exact (sk_regdom Hok).
  - exact (sk_dirloc Hok).
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
(*  2.  THE FOOTPRINT, SLOT BY SLOT                                       *)
(*                                                                        *)
(*  [FsState.fs_state]'s pieces, NAMED by an index, so that a LINEAR      *)
(*  ledger can hand them all out in one step and the resulting big-op can *)
(*  then be regrouped into the predicate's own shape.  Every slot is ONE  *)
(*  run of bytes; a slot that owns nothing -- a node with no indirect     *)
(*  block, a block whose bit reads allocated -- is the EMPTY run, which   *)
(*  keeps the family total and makes its obligations vacuous there.       *)
(* ===================================================================== *)

Inductive fp_slot :=
| FpSb                        (* the superblock's block                   *)
| FpBmap                      (* the bitmap block                         *)
| FpRec (i : Z)               (* inum [i]'s 64-byte record slot           *)
| FpBlk (i : Z) (k : nat)     (* inode [i]'s data block at slot [k]       *)
| FpInd (i : Z)               (* inode [i]'s indirect block               *)
| FpPool (b : Z).             (* block [b], while its bit reads FREE      *)

(* the byte-address map of the run [bs] at offset [off] of block [b]:
   [FsStateDefs.byte_range]'s flat reading, and the unit the cut works in *)
Definition fp_run (b off : Z) (bs : list (bv 8)) : gmap Z (bv 8) :=
  map_seqZ (b * BSIZE_z + off) bs.

Definition fp_blk (S : fs_state_rec) (x : fp_slot) : Z :=
  match x with
  | FpSb => SB_BNO
  | FpBmap => sb_bmapstart (fss_sb S)
  | FpRec i => sb_inodestart (fss_sb S) + i `div` 16
  | FpBlk i k => fn_naddr (fss_inodes S !!! i) k
  | FpInd i => fn_indb (fss_inodes S !!! i)
  | FpPool b => b
  end.

Definition fp_off (x : fp_slot) : Z :=
  match x with FpRec i => 64 * (i `mod` 16) | _ => 0 end.

Definition fp_bs (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (x : fp_slot) : list (bv 8) :=
  match x with
  | FpSb => fss_sbb S
  | FpBmap => bm_bytes BSIZE (fss_used S)
  | FpRec i => dinode_bytes (fn_rec (fss_inodes S !!! i))
  | FpBlk i k => default [] (fn_blk (fss_inodes S !!! i) !! k)
  | FpInd i => if decide (fn_indb (fss_inodes S !!! i) = 0) then []
               else ind_bytes (fn_ent (fss_inodes S !!! i))
  | FpPool b => if decide (b ∈ fss_used S) then [] else default [] (D !! b)
  end.

Definition fp_map (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (x : fp_slot) : gmap Z (bv 8) :=
  fp_run (fp_blk S x) (fp_off x) (fp_bs S D x).

(* the six slots' three components, READ OUT.  Every one of them is a
   [reflexivity] or one [lookup_total_correct]; they exist so that the
   assembly below rewrites a HYPOTHESIS by a named equation rather than by
   an iota step the proofmode cannot see. *)
Lemma fp_sb_blk (S : fs_state_rec) : fp_blk S FpSb = SB_BNO.
Proof. reflexivity. Qed.
Lemma fp_sb_off : fp_off FpSb = 0.
Proof. reflexivity. Qed.
Lemma fp_sb_bs (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
  fp_bs S D FpSb = fss_sbb S.
Proof. reflexivity. Qed.

Lemma fp_bmap_blk (S : fs_state_rec) :
  fp_blk S FpBmap = sb_bmapstart (fss_sb S).
Proof. reflexivity. Qed.
Lemma fp_bmap_off : fp_off FpBmap = 0.
Proof. reflexivity. Qed.
Lemma fp_bmap_bs (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
  fp_bs S D FpBmap = bm_bytes BSIZE (fss_used S).
Proof. reflexivity. Qed.

Lemma fp_rec_blk (S : fs_state_rec) (i : Z) :
  fp_blk S (FpRec i) = sb_inodestart (fss_sb S) + i `div` 16.
Proof. reflexivity. Qed.
Lemma fp_rec_off (i : Z) : fp_off (FpRec i) = 64 * (i `mod` 16).
Proof. reflexivity. Qed.
Lemma fp_rec_bs (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) :
  fss_inodes S !! i = Some n -> fp_bs S D (FpRec i) = dinode_bytes (fn_rec n).
Proof. intros Hi. rewrite /fp_bs (lookup_total_correct _ _ _ Hi) //. Qed.

Lemma fp_dat_blk (S : fs_state_rec) (i : Z) (n : fs_node) (k : nat) :
  fss_inodes S !! i = Some n -> fp_blk S (FpBlk i k) = fn_naddr n k.
Proof. intros Hi. rewrite /fp_blk (lookup_total_correct _ _ _ Hi) //. Qed.
Lemma fp_dat_off (i : Z) (k : nat) : fp_off (FpBlk i k) = 0.
Proof. reflexivity. Qed.
Lemma fp_dat_bs (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (k : nat) (bs : list (bv 8)) :
  fss_inodes S !! i = Some n -> fn_blk n !! k = Some bs ->
  fp_bs S D (FpBlk i k) = bs.
Proof.
  intros Hi Hk. rewrite /fp_bs (lookup_total_correct _ _ _ Hi) Hk //.
Qed.

Lemma fp_indb_blk (S : fs_state_rec) (i : Z) (n : fs_node) :
  fss_inodes S !! i = Some n -> fp_blk S (FpInd i) = fn_indb n.
Proof. intros Hi. rewrite /fp_blk (lookup_total_correct _ _ _ Hi) //. Qed.
Lemma fp_indb_off (i : Z) : fp_off (FpInd i) = 0.
Proof. reflexivity. Qed.
Lemma fp_indb_bs (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) :
  fss_inodes S !! i = Some n -> fn_indb n <> 0 ->
  fp_bs S D (FpInd i) = ind_bytes (fn_ent n).
Proof.
  intros Hi Hnz. rewrite /fp_bs (lookup_total_correct _ _ _ Hi).
  destruct (decide (fn_indb n = 0)); [done | reflexivity].
Qed.

Lemma fp_pool_blk (S : fs_state_rec) (b : Z) : fp_blk S (FpPool b) = b.
Proof. reflexivity. Qed.
Lemma fp_pool_off (b : Z) : fp_off (FpPool b) = 0.
Proof. reflexivity. Qed.
Lemma fp_pool_bs_used (S : fs_state_rec) (D : gmap Z (list (bv 8))) (b : Z) :
  b ∈ fss_used S -> fp_bs S D (FpPool b) = [].
Proof.
  intros Hu. rewrite /fp_bs. destruct (decide (b ∈ fss_used S)); [done | tauto].
Qed.
Lemma fp_pool_bs_free (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (b : Z) (bs : list (bv 8)) :
  b ∉ fss_used S -> D !! b = Some bs -> fp_bs S D (FpPool b) = bs.
Proof.
  intros Hu Hb. rewrite /fp_bs.
  destruct (decide (b ∈ fss_used S)); [tauto | rewrite Hb //].
Qed.

(* the index is in range: the only thing the family's members owe *)
Definition fp_valid (S : fs_state_rec) (x : fp_slot) : Prop :=
  match x with
  | FpSb | FpBmap => True
  | FpRec i | FpInd i => is_Some (fss_inodes S !! i)
  | FpBlk i k => is_Some (fss_inodes S !! i)
                 /\ is_Some (fn_blk (fss_inodes S !!! i) !! k)
  | FpPool b => 0 <= b < sb_size (fss_sb S)
  end.

(* ---- 2a.  THE TWO PURE FACTS ABOUT A RUN, and there are only these --- *)

(* a run that IS a slice of a block of [D] is a sub-map of the flattening,
   and it sits inside its own block *)
Lemma fp_run_of_slice (D : gmap Z (list (bv 8))) (b off : Z)
    (bs pre sub post : list (bv 8)) :
  (forall c cs, D !! c = Some cs -> length cs = BSIZE) ->
  D !! b = Some bs -> bs = (pre ++ sub ++ post)%list ->
  Z.of_nat (length pre) = off ->
  fp_run b off sub ⊆ fs_dbytes D
  /\ 0 <= off /\ off + Z.of_nat (length sub) <= BSIZE_z.
Proof.
  intros Hlen Hb Hbs Hoff.
  assert (Hok : dbytes_ok D) by exact (dbytes_ok_full D Hlen).
  assert (Hbl : length bs = BSIZE) by exact (Hlen b bs Hb).
  rewrite Hbs !length_app in Hbl.
  assert (Hst : Z.of_nat BSIZE = BSIZE_z) by reflexivity.
  split; [| split; [lia |]].
  - apply map_subseteq_spec. intros a v Ha.
    rewrite /fp_run in Ha.
    apply lookup_map_seqZ_Some in Ha as [Hge Ha].
    set (j := Z.to_nat (a - (b * BSIZE_z + off))).
    assert (Hj : Z.of_nat j = a - (b * BSIZE_z + off)) by (rewrite /j; lia).
    assert (Hjs : sub !! j = Some v) by exact Ha.
    assert (Hjl : (j < length sub)%nat) by (apply lookup_lt_Some in Hjs; lia).
    assert (Hbsj : bs !! (length pre + j)%nat = Some v).
    { rewrite Hbs lookup_app_r; [| lia].
      replace (length pre + j - length pre)%nat with j by lia.
      rewrite lookup_app_l; [exact Hjs | lia]. }
    pose proof (fs_dbytes_lookup D b bs (length pre + j)%nat v Hok Hb Hbsj) as Hd.
    replace (b * Z.of_nat BSIZE + Z.of_nat (length pre + j)%nat) with a in Hd;
      [exact Hd |].
    rewrite Nat2Z.inj_add. lia.
  - rewrite -Hoff in Hbl *. lia.
Qed.

Lemma fp_run_of_block (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
  (forall c cs, D !! c = Some cs -> length cs = BSIZE) ->
  D !! b = Some bs ->
  fp_run b 0 bs ⊆ fs_dbytes D /\ 0 <= 0 /\ 0 + Z.of_nat (length bs) <= BSIZE_z.
Proof.
  intros Hlen Hb.
  apply (fp_run_of_slice D b 0 bs [] bs []);
    [exact Hlen | exact Hb | rewrite /= app_nil_r // | reflexivity].
Qed.

(* TWO RUNS ARE DISJOINT when they sit in different blocks, or in the same
   block at offsets that do not overlap.  Everything the cut has to know
   about geometry funnels through this one arithmetic step. *)
Lemma fp_run_disj (b1 off1 : Z) (s1 : list (bv 8)) (b2 off2 : Z)
    (s2 : list (bv 8)) :
  0 <= off1 -> off1 + Z.of_nat (length s1) <= BSIZE_z ->
  0 <= off2 -> off2 + Z.of_nat (length s2) <= BSIZE_z ->
  (b1 <> b2 \/ off1 + Z.of_nat (length s1) <= off2
             \/ off2 + Z.of_nat (length s2) <= off1) ->
  fp_run b1 off1 s1 ##ₘ fp_run b2 off2 s2.
Proof.
  intros H1 H2 H3 H4 Hsep. rewrite /fp_run. apply map_seqZ_disjoint.
  change BSIZE_z with 1024 in *.
  destruct Hsep as [Hne | [Hs | Hs]]; [| lia | lia].
  destruct (Z.lt_trichotomy b1 b2) as [Hlt | [Heq | Hlt]].
  - left. assert (1024 <= (b2 - b1) * 1024) by nia. lia.
  - exfalso. exact (Hne Heq).
  - right; left. assert (1024 <= (b1 - b2) * 1024) by nia. lia.
Qed.

(* ---- 2b.  EVERY SLOT IS A GENUINE SLICE ----------------------------- *)

Lemma fp_ok (S : fs_state_rec) (D : gmap Z (list (bv 8))) (x : fp_slot) :
  snap_bytes S D -> fp_valid S x ->
  fp_map S D x ⊆ fs_dbytes D
  /\ 0 <= fp_off x
  /\ fp_off x + Z.of_nat (length (fp_bs S D x)) <= BSIZE_z.
Proof.
  intros Hb Hv.
  assert (Hlen : forall c cs, D !! c = Some cs -> length cs = BSIZE)
    by exact (sk_bsz Hb).
  (* the empty run is a sub-map of anything and occupies nothing *)
  assert (Hnil : forall c : Z, fp_run c 0 [] ⊆ fs_dbytes D
                   /\ 0 <= 0 /\ 0 + Z.of_nat (length (@nil (bv 8))) <= BSIZE_z).
  { intros c. rewrite /fp_run /=. split; [apply map_empty_subseteq |].
    rewrite /BSIZE_z. lia. }
  destruct x as [| | i | i k | i | b]; rewrite /fp_map /fp_bs /fp_blk /fp_off.
  - exact (fp_run_of_block D SB_BNO (fss_sbb S) Hlen (sk_sb Hb)).
  - exact (fp_run_of_block D _ _ Hlen (sk_bmap Hb)).
  - destruct Hv as [n Hn]. rewrite (lookup_total_correct _ _ _ Hn).
    destruct (sk_rec Hb i n Hn) as (bs & Hbs & pre & post & Hsp & Hoff).
    exact (fp_run_of_slice D _ _ bs pre _ post Hlen Hbs Hsp Hoff).
  - destruct Hv as [[n Hn] Hk]. rewrite (lookup_total_correct _ _ _ Hn) in Hk *.
    destruct Hk as [bs Hbs]. rewrite Hbs /=.
    exact (fp_run_of_block D _ bs Hlen (sk_blk Hb i n k bs Hn Hbs)).
  - destruct Hv as [n Hn]. rewrite (lookup_total_correct _ _ _ Hn).
    destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [exact (Hnil _) |].
    exact (fp_run_of_block D _ _ Hlen (sk_ind Hb i n Hn Hnz)).
  - destruct (decide (b ∈ fss_used S)) as [Hu | Hu]; [exact (Hnil _) |].
    destruct (sk_pool Hb b Hv Hu) as [bs Hbs]. rewrite Hbs /=.
    exact (fp_run_of_block D b bs Hlen Hbs).
Qed.

(* ---- 2c.  ...AND TWO SLOTS ARE DISJOINT ----------------------------- *)

(* the class of a slot: which of the three coupling clauses speaks about
   the block it sits at *)
Definition fp_meta_cls (x : fp_slot) : bool :=
  match x with FpSb | FpBmap | FpRec _ => true | _ => false end.

Lemma fp_meta_of (S : fs_state_rec) (x : fp_slot) :
  fp_valid S x -> fp_meta_cls x = true -> snap_meta S (fp_blk S x).
Proof.
  destruct x as [| | i | i k | i | b]; intros Hv Hc; try discriminate.
  - by left.
  - right. by left.
  - right. right. exists i. split; [exact Hv | reflexivity].
Qed.

Lemma fp_owns_of (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (k : nat) :
  fss_inodes S !! i = Some n -> is_Some (fn_blk n !! k) ->
  fn_owns n (fp_blk S (FpBlk i k)).
Proof.
  intros Hn Hk. rewrite /fp_blk (lookup_total_correct _ _ _ Hn).
  left. exists k. split; [exact Hk | reflexivity].
Qed.

Lemma fp_owns_ind (S : fs_state_rec) (i : Z) (n : fs_node) :
  fss_inodes S !! i = Some n -> fn_indb n <> 0 ->
  fn_owns n (fp_blk S (FpInd i)).
Proof.
  intros Hn Hnz. rewrite /fp_blk (lookup_total_correct _ _ _ Hn).
  right. split; [exact Hnz | reflexivity].
Qed.

(* a slot the node OWNS is below [FS_MAXFILE] and names a nonzero block:
   the two readings of [inode_repr] a within-node comparison needs *)
Lemma fp_slot_range (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) (k : nat) :
  snap_bytes S D -> fss_inodes S !! i = Some n -> is_Some (fn_blk n !! k) ->
  (k < FS_MAXFILE)%nat /\ fn_naddr n k <> 0.
Proof.
  intros Hb Hn Hk.
  pose proof (sk_repr Hb i n Hn) as Hr.
  assert (Hlt : (k < FS_MAXFILE)%nat).
  { destruct (decide (k < FS_MAXFILE)%nat) as [Hy | Hge]; [exact Hy |].
    destruct Hk as [bs Hbs].
    rewrite (inr_blk_top Hr k ltac:(lia)) in Hbs. discriminate. }
  split; [exact Hlt |]. exact (proj1 (inr_blk_dom Hr k Hlt) Hk).
Qed.

(* a slot that is not a metadata role either belongs to a NODE -- and then
   its block is that node's own -- or is a free-pool slot, and then its
   block's bit reads CLEAR.  Those two arms are what the coupling
   separates from each other and from the metadata roles. *)
Lemma fp_node_of (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i : Z) (x : fp_slot) :
  fp_valid S x -> fp_bs S D x <> [] ->
  (exists k, x = FpBlk i k) \/ x = FpInd i ->
  exists n, fss_inodes S !! i = Some n /\ fn_owns n (fp_blk S x).
Proof.
  intros Hv H0 [[k ->] | ->].
  - destruct Hv as [[n Hn] Hk]. rewrite (lookup_total_correct _ _ _ Hn) in Hk.
    exists n. split; [exact Hn | exact (fp_owns_of S D i n k Hn Hk)].
  - destruct Hv as [n Hn].
    rewrite /fp_bs (lookup_total_correct _ _ _ Hn) in H0.
    destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
    exists n. split; [exact Hn | exact (fp_owns_ind S i n Hn Hnz)].
Qed.

Lemma fp_pool_free (S : fs_state_rec) (D : gmap Z (list (bv 8))) (b : Z) :
  fp_bs S D (FpPool b) <> [] -> b ∉ fss_used S.
Proof.
  rewrite /fp_bs. intros H0.
  destruct (decide (b ∈ fss_used S)) as [Hu | Hu]; [done | exact Hu].
Qed.

(* THE BLOCKS OF TWO DIFFERENT SLOTS DIFFER -- except for two records of
   ONE inode block, which differ by their OFFSET.  This is where every
   coupling clause is spent, and it is the whole content of the cut. *)
Lemma fp_sep (S : fs_state_rec) (D : gmap Z (list (bv 8))) (x y : fp_slot) :
  snap_bytes S D -> fp_valid S x -> fp_valid S y -> x <> y ->
  fp_bs S D x <> [] -> fp_bs S D y <> [] ->
  fp_blk S x <> fp_blk S y
  \/ fp_off x + Z.of_nat (length (fp_bs S D x)) <= fp_off y
  \/ fp_off y + Z.of_nat (length (fp_bs S D y)) <= fp_off x.
Proof.
  intros Hb Hx Hy Hne Hx0 Hy0.
  destruct (fp_meta_cls x) eqn:Hcx; destruct (fp_meta_cls y) eqn:Hcy.
  - (* ================ metadata vs metadata ================ *)
    destruct x as [| | i | | |]; try discriminate;
      destruct y as [| | j | | |]; try discriminate.
    + exfalso. exact (Hne eq_refl).
    + left. exact (snap_sb_bmap_ne S (sk_sbok Hb)).
    + left. destruct Hy as [n Hn]. exact (proj1 (snap_reg_blk S D j n Hb Hn)).
    + left. exact (not_eq_sym (snap_sb_bmap_ne S (sk_sbok Hb))).
    + exfalso. exact (Hne eq_refl).
    + left. destruct Hy as [n Hn]. exact (proj2 (snap_reg_blk S D j n Hb Hn)).
    + left. destruct Hx as [n Hn].
      exact (not_eq_sym (proj1 (snap_reg_blk S D i n Hb Hn))).
    + left. destruct Hx as [n Hn].
      exact (not_eq_sym (proj2 (snap_reg_blk S D i n Hb Hn))).
    + (* TWO RECORDS.  A different inode block, or the same block at two
         of its sixteen slots -- and a record is 64 bytes wide. *)
      destruct Hx as [n Hn]. destruct Hy as [m Hm].
      destruct (decide (i `div` 16 = j `div` 16)) as [Hq | Hq]; last first.
      { left. rewrite /fp_blk. intros Heq. apply Hq. lia. }
      assert (Hmod : i `mod` 16 <> j `mod` 16).
      { intros Hm16. apply Hne. f_equal.
        pose proof (Z.div_mod i 16 ltac:(lia)).
        pose proof (Z.div_mod j 16 ltac:(lia)). lia. }
      rewrite /fp_off /fp_bs.
      rewrite (lookup_total_correct _ _ _ Hn) (lookup_total_correct _ _ _ Hm).
      rewrite (dinode_bytes_length _ (inr_rec_wf (sk_repr Hb i n Hn)))
              (dinode_bytes_length _ (inr_rec_wf (sk_repr Hb j m Hm))).
      pose proof (Z.mod_pos_bound i 16 ltac:(lia)).
      pose proof (Z.mod_pos_bound j 16 ltac:(lia)).
      destruct (Z.lt_trichotomy (i `mod` 16) (j `mod` 16)) as [Hlt | [He | Hlt]].
      * right; left. lia.
      * exfalso. exact (Hmod He).
      * right; right. lia.
  - (* ======== a metadata role vs a node's block or the pool ======== *)
    left. intros Heq.
    pose proof (fp_meta_of S x Hx Hcx) as Hmeta. rewrite Heq in Hmeta.
    destruct y as [| | | j ky | j | c]; try discriminate.
    + destruct (fp_node_of S D j _ Hy Hy0 ltac:(left; by eexists))
        as (m & Hm & Hom).
      exact (proj2 (sk_own_used Hb j m _ Hm Hom) Hmeta).
    + destruct (fp_node_of S D j _ Hy Hy0 ltac:(by right)) as (m & Hm & Hom).
      exact (proj2 (sk_own_used Hb j m _ Hm Hom) Hmeta).
    + exact (fp_pool_free S D c Hy0 (sk_meta_used Hb _ Hmeta)).
  - (* ======== the mirror image ======== *)
    left. intros Heq.
    pose proof (fp_meta_of S y Hy Hcy) as Hmeta. rewrite -Heq in Hmeta.
    destruct x as [| | | j kx | j | c]; try discriminate.
    + destruct (fp_node_of S D j _ Hx Hx0 ltac:(left; by eexists))
        as (m & Hm & Hom).
      exact (proj2 (sk_own_used Hb j m _ Hm Hom) Hmeta).
    + destruct (fp_node_of S D j _ Hx Hx0 ltac:(by right)) as (m & Hm & Hom).
      exact (proj2 (sk_own_used Hb j m _ Hm Hom) Hmeta).
    + exact (fp_pool_free S D c Hx0 (sk_meta_used Hb _ Hmeta)).
  - (* ======== two node/pool slots ======== *)
    left. intros Heq.
    (* the free pool never meets a node's block: [sk_own_used] marks the
       one in use and the other's bit reads clear *)
    assert (Hnp : forall i z c, fp_valid S z -> fp_bs S D z <> [] ->
              ((exists k, z = FpBlk i k) \/ z = FpInd i) ->
              fp_blk S z = c -> c ∉ fss_used S -> False).
    { intros i z c Hv H0 Hs Hc Hu.
      destruct (fp_node_of S D i z Hv H0 Hs) as (n & Hn & Ho).
      rewrite Hc in Ho.
      exact (Hu (proj1 (sk_own_used Hb i n c Hn Ho))). }
    destruct x as [| | | ix kx | ix | bx]; try discriminate;
      destruct y as [| | | iy ky | iy | by0]; try discriminate.
    + (* two data slots *)
      destruct (fp_node_of S D ix _ Hx Hx0 ltac:(left; by eexists))
        as (n & Hn & Hon).
      destruct (fp_node_of S D iy _ Hy Hy0 ltac:(left; by eexists))
        as (m & Hm & Hom).
      rewrite Heq in Hon.
      assert (Hij : ix = iy) by exact (sk_disj Hb ix n iy m _ Hn Hm Hon Hom).
      subst iy. assert (Hnm : m = n) by congruence. subst m.
      destruct Hx as [_ Hkx]. destruct Hy as [_ Hky].
      rewrite (lookup_total_correct _ _ _ Hn) in Hkx.
      rewrite (lookup_total_correct _ _ _ Hn) in Hky.
      destruct (fp_slot_range S D ix n kx Hb Hn Hkx) as [Hrx Hnzx].
      destruct (fp_slot_range S D ix n ky Hb Hn Hky) as [Hry _].
      rewrite /fp_blk !(lookup_total_correct _ _ _ Hn) in Heq.
      exact (fn_slot_data_ne n kx ky (sk_slot Hb ix n Hn) Hrx Hry Hnzx
               ltac:(intros ->; exact (Hne eq_refl)) Heq).
    + (* a data slot and an indirect block *)
      destruct (fp_node_of S D ix _ Hx Hx0 ltac:(left; by eexists))
        as (n & Hn & Hon).
      destruct (fp_node_of S D iy _ Hy Hy0 ltac:(by right)) as (m & Hm & Hom).
      rewrite Heq in Hon.
      assert (Hij : ix = iy) by exact (sk_disj Hb ix n iy m _ Hn Hm Hon Hom).
      subst iy. assert (Hnm : m = n) by congruence. subst m.
      destruct Hx as [_ Hkx]. rewrite (lookup_total_correct _ _ _ Hn) in Hkx.
      destruct (fp_slot_range S D ix n kx Hb Hn Hkx) as [Hrx _].
      rewrite /fp_bs (lookup_total_correct _ _ _ Hn) in Hy0.
      destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
      rewrite /fp_blk !(lookup_total_correct _ _ _ Hn) in Heq.
      exact (fn_slot_ind_ne n kx (sk_slot Hb ix n Hn) Hrx Hnz Heq).
    + exact (Hnp ix _ by0 Hx Hx0 ltac:(left; by eexists) Heq
               (fp_pool_free S D by0 Hy0)).
    + (* an indirect block and a data slot *)
      destruct (fp_node_of S D ix _ Hx Hx0 ltac:(by right)) as (n & Hn & Hon).
      destruct (fp_node_of S D iy _ Hy Hy0 ltac:(left; by eexists))
        as (m & Hm & Hom).
      rewrite Heq in Hon.
      assert (Hij : ix = iy) by exact (sk_disj Hb ix n iy m _ Hn Hm Hon Hom).
      subst iy. assert (Hnm : m = n) by congruence. subst m.
      destruct Hy as [_ Hky]. rewrite (lookup_total_correct _ _ _ Hn) in Hky.
      destruct (fp_slot_range S D ix n ky Hb Hn Hky) as [Hry _].
      rewrite /fp_bs (lookup_total_correct _ _ _ Hn) in Hx0.
      destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
      rewrite /fp_blk !(lookup_total_correct _ _ _ Hn) in Heq.
      exact (fn_slot_ind_ne n ky (sk_slot Hb ix n Hn) Hry Hnz (eq_sym Heq)).
    + (* one node's indirect block against itself *)
      destruct (fp_node_of S D ix _ Hx Hx0 ltac:(by right)) as (n & Hn & Hon).
      destruct (fp_node_of S D iy _ Hy Hy0 ltac:(by right)) as (m & Hm & Hom).
      rewrite Heq in Hon.
      assert (Hij : ix = iy) by exact (sk_disj Hb ix n iy m _ Hn Hm Hon Hom).
      subst iy. exact (Hne eq_refl).
    + exact (Hnp ix _ by0 Hx Hx0 ltac:(by right) Heq
               (fp_pool_free S D by0 Hy0)).
    + exact (Hnp iy _ bx Hy Hy0 ltac:(left; by eexists) (eq_sym Heq)
               (fp_pool_free S D bx Hx0)).
    + exact (Hnp iy _ bx Hy Hy0 ltac:(by right) (eq_sym Heq)
               (fp_pool_free S D bx Hx0)).
    + (* two pool slots: their block numbers ARE their indices *)
      rewrite /fp_blk in Heq. subst by0. exact (Hne eq_refl).
Qed.

Lemma fp_disj (S : fs_state_rec) (D : gmap Z (list (bv 8))) (x y : fp_slot) :
  snap_bytes S D -> fp_valid S x -> fp_valid S y -> x <> y ->
  fp_map S D x ##ₘ fp_map S D y.
Proof.
  intros Hb Hx Hy Hne.
  destruct (decide (fp_bs S D x = [])) as [Hx0 | Hx0].
  { rewrite /fp_map /fp_run Hx0 /=. apply map_disjoint_empty_l. }
  destruct (decide (fp_bs S D y = [])) as [Hy0 | Hy0].
  { rewrite /fp_map /fp_run Hy0 /=. apply map_disjoint_empty_r. }
  destruct (fp_ok S D x Hb Hx) as (_ & Hx1 & Hx2).
  destruct (fp_ok S D y Hb Hy) as (_ & Hy1 & Hy2).
  rewrite /fp_map. apply (fp_run_disj _ _ _ _ _ _ Hx1 Hx2 Hy1 Hy2).
  exact (fp_sep S D x y Hb Hx Hy Hne Hx0 Hy0).
Qed.

(* ---- 2d.  THE FAMILY, ENUMERATED ------------------------------------ *)

Definition fp_inums (S : fs_state_rec) : list Z :=
  elements (dom (fss_inodes S)).

Definition fp_recs (S : fs_state_rec) : list fp_slot :=
  FpRec <$> fp_inums S.

Definition fp_blks (S : fs_state_rec) : list fp_slot :=
  fp_inums S
    ≫= (fun i => FpBlk i <$> elements (dom (fn_blk (fss_inodes S !!! i)))).

Definition fp_inds (S : fs_state_rec) : list fp_slot :=
  FpInd <$> fp_inums S.

Definition fp_pools (S : fs_state_rec) : list fp_slot :=
  FpPool <$> seqZ 0 (sb_size (fss_sb S)).

Definition fp_list (S : fs_state_rec) : list fp_slot :=
  FpSb :: FpBmap
       :: (fp_recs S ++ fp_blks S ++ fp_inds S ++ fp_pools S).

Lemma fp_inums_elem (S : fs_state_rec) (i : Z) :
  i ∈ fp_inums S <-> is_Some (fss_inodes S !! i).
Proof. rewrite /fp_inums elem_of_elements elem_of_dom //. Qed.

Lemma fp_recs_elem (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_recs S -> exists i, x = FpRec i /\ is_Some (fss_inodes S !! i).
Proof.
  rewrite /fp_recs. intros (i & -> & Hi)%elem_of_list_fmap.
  exists i. split; [reflexivity | by apply fp_inums_elem].
Qed.

Lemma fp_inds_elem (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_inds S -> exists i, x = FpInd i /\ is_Some (fss_inodes S !! i).
Proof.
  rewrite /fp_inds. intros (i & -> & Hi)%elem_of_list_fmap.
  exists i. split; [reflexivity | by apply fp_inums_elem].
Qed.

Lemma fp_pools_elem (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_pools S -> exists b, x = FpPool b /\ 0 <= b < sb_size (fss_sb S).
Proof.
  rewrite /fp_pools. intros (b & -> & Hb)%elem_of_list_fmap.
  apply elem_of_seqZ in Hb. exists b. split; [reflexivity | lia].
Qed.

Lemma fp_blks_elem (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_blks S ->
  exists i k, x = FpBlk i k /\ is_Some (fss_inodes S !! i)
           /\ is_Some (fn_blk (fss_inodes S !!! i) !! k).
Proof.
  rewrite /fp_blks. intros (i & Hx & Hi)%elem_of_list_bind.
  apply elem_of_list_fmap in Hx as (k & -> & Hk).
  exists i, k. split; [reflexivity |].
  split; [by apply fp_inums_elem |].
  apply elem_of_elements, elem_of_dom in Hk. exact Hk.
Qed.

Lemma fp_list_valid (S : fs_state_rec) (x : fp_slot) :
  x ∈ fp_list S -> fp_valid S x.
Proof.
  rewrite /fp_list. intros Hx0.
  apply elem_of_cons in Hx0 as [-> | Hx0]; [done |].
  apply elem_of_cons in Hx0 as [-> | Hx]; [done |].
  apply elem_of_app in Hx as [Hx | Hx].
  { destruct (fp_recs_elem S x Hx) as (i & -> & Hi). exact Hi. }
  apply elem_of_app in Hx as [Hx | Hx].
  { destruct (fp_blks_elem S x Hx) as (i & k & -> & Hi & Hk). by split. }
  apply elem_of_app in Hx as [Hx | Hx].
  { destruct (fp_inds_elem S x Hx) as (i & -> & Hi). exact Hi. }
  destruct (fp_pools_elem S x Hx) as (b & -> & Hb). exact Hb.
Qed.

(* a fmap by an injective function keeps [NoDup].  Stdlib's own
   [NoDup_fmap_2_strong] leaves the list an EVAR when its [f] is a section
   variable, and the instance search for [elements] then fails on the wrong
   set type; taking [f] explicitly is one induction and no guessing. *)
Lemma NoDup_fmap_inj {A B : Type} (f : A -> B) (l : list A) :
  (forall x y : A, f x = f y -> x = y) -> base.NoDup l -> base.NoDup (f <$> l).
Proof.
  intros Hinj Hnd. induction Hnd as [| x l Hx Hnd IH]; [constructor |].
  rewrite fmap_cons. constructor; [| exact IH].
  intros Hin. apply elem_of_list_fmap in Hin as (y & Hy & Hyl).
  apply Hinj in Hy as ->. exact (Hx Hyl).
Qed.

Lemma fp_list_nodup (S : fs_state_rec) : base.NoDup (fp_list S).
Proof.
  assert (Hins : base.NoDup (fp_inums S)).
  { rewrite /fp_inums. apply (NoDup_elements (dom (fss_inodes S))). }
  assert (HR : base.NoDup (fp_recs S)).
  { rewrite /fp_recs.
    apply (NoDup_fmap_inj FpRec _ ltac:(intros a b H; congruence) Hins). }
  assert (HI : base.NoDup (fp_inds S)).
  { rewrite /fp_inds.
    apply (NoDup_fmap_inj FpInd _ ltac:(intros a b H; congruence) Hins). }
  assert (HP : base.NoDup (fp_pools S)).
  { rewrite /fp_pools.
    apply (NoDup_fmap_inj FpPool _ ltac:(intros a b H; congruence)).
    apply (NoDup_seqZ 0 (sb_size (fss_sb S))). }
  assert (HB : base.NoDup (fp_blks S)).
  { rewrite /fp_blks. apply NoDup_bind.
    - intros i1 i2 y _ _ Hy1 Hy2.
      apply elem_of_list_fmap in Hy1 as (k1 & -> & _).
      apply elem_of_list_fmap in Hy2 as (k2 & Hk & _). congruence.
    - intros i _.
      apply (NoDup_fmap_inj (FpBlk i) _ ltac:(intros a b H; congruence)).
      apply (NoDup_elements (dom (fn_blk (fss_inodes S !!! i)))).
    - exact Hins. }
  rewrite /fp_list. apply NoDup_cons_2.
  { intros Hx0. apply elem_of_cons in Hx0 as [Hx | Hx]; [discriminate |].
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_recs_elem S _ Hx) as (i & Hc & _). discriminate. }
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_blks_elem S _ Hx) as (i & k & Hc & _). discriminate. }
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_inds_elem S _ Hx) as (i & Hc & _). discriminate. }
    destruct (fp_pools_elem S _ Hx) as (b & Hc & _). discriminate. }
  apply NoDup_cons_2.
  { intros Hx.
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_recs_elem S _ Hx) as (i & Hc & _). discriminate. }
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_blks_elem S _ Hx) as (i & k & Hc & _). discriminate. }
    apply elem_of_app in Hx as [Hx | Hx].
    { destruct (fp_inds_elem S _ Hx) as (i & Hc & _). discriminate. }
    destruct (fp_pools_elem S _ Hx) as (b & Hc & _). discriminate. }
  apply NoDup_app. split_and!; [exact HR | |].
  { intros x Hx.
    destruct (fp_recs_elem S x Hx) as (i & -> & _). intros Hy.
    apply elem_of_app in Hy as [Hy | Hy].
    { destruct (fp_blks_elem S _ Hy) as (j & k & Hc & _). discriminate. }
    apply elem_of_app in Hy as [Hy | Hy].
    { destruct (fp_inds_elem S _ Hy) as (j & Hc & _). discriminate. }
    destruct (fp_pools_elem S _ Hy) as (b & Hc & _). discriminate. }
  apply NoDup_app. split_and!; [exact HB | |].
  { intros x Hx.
    destruct (fp_blks_elem S x Hx) as (i & k & -> & _ & _). intros Hy.
    apply elem_of_app in Hy as [Hy | Hy].
    { destruct (fp_inds_elem S _ Hy) as (j & Hc & _). discriminate. }
    destruct (fp_pools_elem S _ Hy) as (b & Hc & _). discriminate. }
  apply NoDup_app. split_and!; [exact HI | | exact HP].
  intros x Hx.
  destruct (fp_inds_elem S x Hx) as (i & -> & _). intros Hy.
  destruct (fp_pools_elem S _ Hy) as (b & Hc & _). discriminate.
Qed.

(* ===================================================================== *)
(*  3.  THE BLOCK LEDGER, AND THE CUT                                     *)
(* ===================================================================== *)

Section Ledger.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.
  Implicit Types D : gmap Z (list (bv 8)).

  Definition blk_ledger Γ D : iProp Σ :=
    ([∗ map] b ↦ bs ∈ D, blk_owned Γ b bs)%I.

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
  (*  3a.  A RUN OF BYTES IS A SUB-MAP OF THE FLATTENING                 *)
  (* ------------------------------------------------------------------ *)

  Lemma byte_range_run Γ b off bs :
    byte_range Γ b off bs
    ⊣⊢ ([∗ map] a ↦ v ∈ fp_run b off bs, fsΦ Γ (DfracOwn 1) a v).
  Proof.
    rewrite /fp_run big_sepM_map_seqZ_gen /byte_range /byte_range_q //.
  Qed.

  Lemma blk_owned_run Γ b bs :
    length bs = BSIZE ->
    blk_owned Γ b bs
    ⊣⊢ ([∗ map] a ↦ v ∈ fp_run b 0 bs, fsΦ Γ (DfracOwn 1) a v).
  Proof.
    intros Hl. rewrite /blk_owned byte_range_run.
    iSplit.
    - iIntros "[_ H]". iExact "H".
    - iIntros "H". iSplitR; [by iPureIntro | iExact "H"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3b.  THE CUT                                                       *)
  (*                                                                      *)
  (*  A family of PAIRWISE DISJOINT sub-maps of the byte map is handed     *)
  (*  out SIMULTANEOUSLY; what the family does not cover is dropped (the   *)
  (*  logic is affine, and a ledger may legitimately carry blocks the      *)
  (*  state does not name).  This is the whole of what the linear          *)
  (*  construction needs of the ledger.                                    *)
  (* ------------------------------------------------------------------ *)

  Lemma ledger_carve {A : Type} (Φ : Z -> bv 8 -> iProp Σ)
      (B : gmap Z (bv 8)) (l : list A) (f : A -> gmap Z (bv 8)) :
    base.NoDup l ->
    (forall x, x ∈ l -> f x ⊆ B) ->
    (forall x y, x ∈ l -> y ∈ l -> x <> y -> f x ##ₘ f y) ->
    ([∗ map] a ↦ v ∈ B, Φ a v)
    ⊢ [∗ list] x ∈ l, ([∗ map] a ↦ v ∈ f x, Φ a v).
  Proof.
    revert B. induction l as [| x l IH]; intros B Hnd Hsub Hdisj.
    { rewrite big_sepL_nil. iIntros "_". done. }
    apply NoDup_cons in Hnd as [Hx Hnd].
    assert (Hfx : f x ⊆ B) by (apply Hsub; apply elem_of_cons; by left).
    assert (HB : B = f x ∪ B ∖ f x)
      by (symmetry; exact (map_difference_union (f x) B Hfx)).
    rewrite {1}HB big_sepM_union;
      [| apply map_disjoint_difference_r; reflexivity].
    rewrite big_sepL_cons. iIntros "[$ Hrest]".
    iApply (IH (B ∖ f x) Hnd with "Hrest").
    - intros y Hy. apply map_subseteq_spec. intros a v Hav.
      apply lookup_difference_Some. split.
      + eapply map_subseteq_spec;
          [apply Hsub; apply elem_of_cons; by right | exact Hav].
      + eapply map_disjoint_Some_l; [| exact Hav].
        apply Hdisj; [apply elem_of_cons; by right | apply elem_of_cons; by left |].
        intros ->. exact (Hx Hy).
    - intros y z Hy Hz Hyz.
      apply Hdisj; [apply elem_of_cons; by right | apply elem_of_cons; by right
                   | exact Hyz].
  Qed.

  (* the family's own instance: the footprint's slots, at the flattening *)
  Lemma blk_ledger_cut Γ S D :
    snap_bytes S D ->
    blk_ledger Γ D
    ⊢ [∗ list] x ∈ fp_list S,
        byte_range Γ (fp_blk S x) (fp_off x) (fp_bs S D x).
  Proof.
    intros Hb.
    rewrite /blk_ledger -(fs_dbytes_blocks Γ D (sk_bsz Hb)).
    rewrite (ledger_carve (fsΦ Γ (DfracOwn 1)) (fs_dbytes D) (fp_list S)
               (fp_map S D)
               (fp_list_nodup S)
               (fun x Hx => proj1 (fp_ok S D x Hb (fp_list_valid S x Hx)))
               (fun x y Hx Hy Hne =>
                  fp_disj S D x y Hb (fp_list_valid S x Hx)
                          (fp_list_valid S y Hy) Hne)).
    apply big_sepL_mono. intros k x _. rewrite /fp_map byte_range_run //.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3c.  REGROUPING: a list over the inums IS a big-op over the map     *)
  (* ------------------------------------------------------------------ *)

  Lemma big_sepL_elements_dom {A : Type} (I : gmap Z A) (Ψ : Z -> iProp Σ) :
    ([∗ list] i ∈ elements (dom I), Ψ i) ⊣⊢ ([∗ map] i ↦ _ ∈ I, Ψ i).
  Proof. rewrite -big_sepS_elements -big_sepM_dom //. Qed.

  Lemma big_sepL_elements_dom_nat {A : Type} (m : gmap nat A) (Ψ : nat -> iProp Σ) :
    ([∗ list] k ∈ elements (dom m), Ψ k) ⊣⊢ ([∗ map] k ↦ _ ∈ m, Ψ k).
  Proof. rewrite -big_sepS_elements -big_sepM_dom //. Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE INSTANCE, FROM A LINEAR LEDGER AND THE PURE TIE             *)
  (*                                                                      *)
  (*  Gamma-GENERIC and SOURCE-AGNOSTIC: nothing here knows which          *)
  (*  points-to [fsΦ Γ] is, nor where the ledger came from -- and the      *)
  (*  ledger is SPENT, so the construction applies at an exclusive         *)
  (*  points-to.  That is what makes it serve both the commit's fresh      *)
  (*  snapshot and the boot mint onto the era's own ghosts                 *)
  (*  ([fs_state_of_ledger_era] is the check).                            *)
  (* ------------------------------------------------------------------ *)

  Lemma fs_state_of_ledger Γ S D :
    snap_ok S D ->
    blk_ledger Γ D -∗ fs_links (γlink Γ) (fss_inodes S) -∗ fs_state Γ S.
  Proof.
    intros [Hok Hloc]. iIntros "Hled Hlinks".
    iDestruct (blk_ledger_cut Γ S D Hok with "Hled") as "H".
    iEval (rewrite /fp_list /fp_recs /fp_blks /fp_inds /fp_pools /fp_inums
                   !big_sepL_cons !big_sepL_app) in "H".
    iDestruct "H" as "(Hsb & Hbm & Hrec & Hdat & Hind & Hpool)".
    (* ---- the three inode-indexed groups, as big-ops over the map ---- *)
    iEval (rewrite big_sepL_fmap big_sepL_elements_dom) in "Hrec".
    iEval (rewrite big_sepL_bind big_sepL_elements_dom) in "Hdat".
    iEval (rewrite big_sepL_fmap big_sepL_elements_dom) in "Hind".
    iEval (rewrite big_sepL_fmap) in "Hpool".
    (* ---- assemble ---- *)
    rewrite /fs_state. iSplitL "Hsb"; last iSplitR "Hbm Hpool".
    - (* the superblock *)
      rewrite /sb_owned. iSplitL; [| iPureIntro; exact (sk_parse Hok)].
      iEval (rewrite fp_sb_blk fp_sb_off (fp_sb_bs S D)) in "Hsb".
      rewrite (blk_owned_run Γ SB_BNO (fss_sbb S)
                 (sk_bsz Hok SB_BNO (fss_sbb S) (sk_sb Hok))).
      rewrite -byte_range_run. iExact "Hsb".
    - (* the inodes *)
      rewrite /fs_inodes /inode_owned /inode_phi /inode_ghost.
      iEval (rewrite /fs_links) in "Hlinks".
      iDestruct (big_sepM_sep_2 with "Hrec Hdat") as "Hp".
      iDestruct (big_sepM_sep_2 with "Hp Hind") as "Hp".
      iDestruct (big_sepM_sep_2 with "Hp Hlinks") as "Hp".
      iApply (big_sepM_impl with "Hp").
      iIntros "!#" (i n Hi) "(((Hr & Hd) & Hb) & Hl)".
      iSplitR "Hl".
      + iSplitL "Hr".
        * (* the record *)
          iEval (rewrite fp_rec_blk fp_rec_off (fp_rec_bs S D i n Hi)) in "Hr".
          rewrite (rec_owned_sb Γ (fss_sb S) i (fn_rec n) (sk_inum Hok i n Hi)).
          rewrite /rec_owned_at. iExact "Hr".
        * iSplitL "Hd".
          -- (* the data blocks *)
             iEval (rewrite (lookup_total_correct _ _ _ Hi)
                            big_sepL_fmap big_sepL_elements_dom_nat) in "Hd".
             iApply (big_sepM_impl with "Hd").
             iIntros "!#" (k bs Hk) "Hc".
             iEval (rewrite (fp_dat_blk S i n k Hi) (fp_dat_off i k)
                            (fp_dat_bs S D i n k bs Hi Hk)) in "Hc".
             rewrite (blk_owned_run Γ (fn_naddr n k) bs
                        (sk_bsz Hok _ bs (sk_blk Hok i n k bs Hi Hk))).
             rewrite -byte_range_run. iExact "Hc".
          -- (* the indirect block *)
             rewrite /ind_owned.
             destruct (decide (fn_indb n = 0)) as [Hz | Hnz]; [done |].
             iEval (rewrite (fp_indb_blk S i n Hi) (fp_indb_off i)
                            (fp_indb_bs S D i n Hi Hnz)) in "Hb".
             rewrite (blk_owned_run Γ (fn_indb n) (ind_bytes (fn_ent n))
                        (sk_bsz Hok _ _ (sk_ind Hok i n Hi Hnz))).
             rewrite -byte_range_run. iExact "Hb".
      + iDestruct (inode_link_scatter with "Hl") as "[$ $]".
        iPureIntro. exact (Hloc i n Hi).
    - (* the bitmap block and the free pool *)
      rewrite /free_bitmap /free_bitmap_at. iSplitL "Hbm".
      + iEval (rewrite fp_bmap_blk fp_bmap_off (fp_bmap_bs S D)) in "Hbm".
        rewrite (blk_owned_run Γ (sb_bmapstart (fss_sb S))
                   (bm_bytes BSIZE (fss_used S))
                   (sk_bsz Hok _ _ (sk_bmap Hok))).
        rewrite -byte_range_run. iExact "Hbm".
      + rewrite /free_pool.
        iApply (big_sepL_mono with "Hpool"). intros k b Hk.
        apply lookup_seqZ in Hk as [-> Hk].
        rewrite /pool_elt.
        destruct (decide (0 + Z.of_nat k ∈ fss_used S)) as [Hu | Hu].
        * rewrite (bool_decide_eq_true_2 _ Hu).
          rewrite (fp_pool_bs_used S D _ Hu) byte_range_nil //.
        * rewrite (bool_decide_eq_false_2 _ Hu).
          destruct (sk_pool Hok (0 + Z.of_nat k) ltac:(lia) Hu) as [bs Hbs].
          rewrite (fp_pool_blk S (0 + Z.of_nat k)) (fp_pool_off (0 + Z.of_nat k)).
          rewrite (fp_pool_bs_free S D _ bs Hu Hbs).
          iIntros "Hc". iExists bs. rewrite /blk_owned.
          iSplitR; [iPureIntro; exact (sk_bsz Hok _ bs Hbs) | iExact "Hc"].
  Qed.

End Ledger.

(* ===================================================================== *)
(*  5.  THE SNAPSHOT'S VIEW RECORD                                        *)
(* ===================================================================== *)

Section Snap.
  (* [diskImgG] is the tree's UNIQUE [ghost_mapG Σ Z (bv 8)]; the snapshot's
     byte map is a FRESH gname at that same class. *)
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.
  Implicit Types D : gmap Z (list (bv 8)).

  (* the FULL element, exactly as the era's [FsBytesGamma.fs_gamma_L] is *)
  Definition snap_gamma (g gl gt : gname) : fs_view_names Σ :=
    MkFsView (fun (dq : dfrac) (a : Z) (v : bv 8) => (a ↪[g]{dq} v)%I) gl gt.

  Global Instance snap_gamma_gtimeless g gl gt :
    GTimeless (snap_gamma g gl gt).
  Proof. intros dq a v. rewrite /snap_gamma /=. apply _. Qed.

  (* two owners of one byte is [False].  [FsStateDefs.phi_excl]'s consumers
     -- [FsStateBitmap.free_pool_used], hence xv6's "freeing free block"
     panic arm, and [FsStateDefs.blk_owned_ne] -- therefore read on the
     durable side exactly as they do at the era's view. *)
  Lemma snap_gamma_excl g gl gt : phi_excl (snap_gamma g gl gt).
  Proof.
    intros a v w dq1 dq2. rewrite /snap_gamma /=.
    iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  6.  THE ALLOCATOR = THE TRANSPORT                                   *)
  (*                                                                      *)
  (*  All three gname families in ONE update, returned EXISTENTIALLY:     *)
  (*  [own_alloc] cannot target a name, and the landed allocator family   *)
  (*  ([FsState.fs_boot_alloc_at]) already has this shape.  The byte map   *)
  (*  joins it here.                                                      *)
  (* ------------------------------------------------------------------ *)

  Lemma snap_ledger_of_elems g gl gt D :
    (forall b bs, D !! b = Some bs -> length bs = BSIZE) ->
    ([∗ map] a ↦ v ∈ fs_dbytes D, a ↪[g] v)
    ⊢ blk_ledger (snap_gamma g gl gt) D.
  Proof.
    intros Hlen.
    rewrite /blk_ledger -(fs_dbytes_blocks (snap_gamma g gl gt) D Hlen).
    iIntros "H". iExact "H".
  Qed.

  (* the byte map, freshly allocated: the elements come out EXCLUSIVE and
     are handed straight to the cut *)
  Lemma snap_bytes_alloc (B : gmap Z (bv 8)) :
    ⊢ |==> ∃ g : gname,
        ghost_map_auth g 1 B ∗ ([∗ map] a ↦ v ∈ B, a ↪[g] v).
  Proof.
    iMod (ghost_map_alloc B) as (g) "[Ha Hel]".
    iModIntro. iExists g. iFrame.
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
    iMod (fs_links_alloc (fss_inodes S) (sk_links_plain (sk_bytes Hok)))
      as (gl) "Hlinks".
    iMod (ghost_map_alloc (fss_inodes S)) as (gt) "[Hta Htf]".
    iModIntro. iExists g, gl, gt.
    iDestruct (snap_ledger_of_elems g gl gt D (sk_bsz (sk_bytes Hok)) with "Hbe")
      as "Hled".
    iFrame "Hba Hta Htf".
    iApply (fs_state_of_ledger (snap_gamma g gl gt) S D Hok with "Hled").
    iExact "Hlinks".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  7.  THE SNAPSHOT, AND THE EPOCH REGISTRY                            *)
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
  (*  8.  WHAT A CONSUMER READS OFF THE CURRENT SNAPSHOT                  *)
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

(* ===================================================================== *)
(*  9.  THE NON-VACUITY CHECK: THE CORE AT THE ERA'S OWN VIEW             *)
(*                                                                        *)
(*  [FsBytesGamma.fs_gamma_L]'s points-to is the FULL element of the       *)
(*  era's logged byte view, and it is not [□]-able.  That the same core    *)
(*  applies there VERBATIM -- same statement, same premise, no extra       *)
(*  hypothesis -- is the whole point of making the ledger linear, and it   *)
(*  is what the boot mint (plan section 5) calls: the era's instance is    *)
(*  minted from the current snapshot's value by this lemma at [Gamma_L].  *)
(*  So the check is stated, not described.                                *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  9a. THE HOME BRIDGE (durable-disk lane E-clauses)                     *)
(*                                                                        *)
(*  WHAT THE BOOT MINT MEETS.  At a clean header recovery is the IDENTITY  *)
(*  on the home blocks ([FsCrash.fs_recovery_clean]), so the committed map *)
(*  the snapshot describes is literally                                    *)
(*  [fs_restrict P (fs_home_set cov logstart)] -- a map whose DOMAIN is    *)
(*  the home set ([LogDefs.fs_restrict_dom]).  The mint's input, on the    *)
(*  other hand, is the boot thread's own per-block ownership: one          *)
(*  [FsBlocks.fsblock] per home block.  Those are the SAME RESOURCE, and   *)
(*  [blk_ledger_of_home] below is the equation -- [blk_ledger] is the      *)
(*  big-op over the map, a set big-op is the big-op over its domain, and   *)
(*  [FsBytesGamma.gamma_blk_owned] is the vocabulary.                      *)
(*                                                                        *)
(*  THE POINT IS THE DOMAIN, and it is what makes the coverage /           *)
(*  log-disjointness pair of [InodeLock.inode_ok] free.  Every block the   *)
(*  snapshot NAMES -- block 1, the bitmap block, an inode region block, a  *)
(*  node's data or indirect block, a free-pool block -- is a block of [D]  *)
(*  by one of [sk_sb]/[sk_bmap]/[sk_rec]/[sk_blk]/[sk_ind]/[sk_pool], and  *)
(*  a block of [fs_restrict P home] is a HOME block                        *)
(*  ([snap_names_home]).  A home block is in [cov] and outside the log     *)
(*  region by [LogDefs.fs_home_set]'s own definition                       *)
(*  ([snap_names_cov]).  So the mint owes NO new clause for either half:   *)
(*  this is pure bookkeeping over [fs_restrict].                           *)
(* ===================================================================== *)

(* every block any clause of [snap_bytes] reads.  [snap_meta] is already
   the three metadata roles; the other two arms are a node's own blocks and
   the free pool. *)
Definition snap_names (S : fs_state_rec) (b : Z) : Prop :=
  snap_meta S b
  \/ (exists i n, fss_inodes S !! i = Some n /\ fn_owns n b)
  \/ (0 <= b < sb_size (fss_sb S) /\ b ∉ fss_used S).

Lemma snap_names_dom (S : fs_state_rec) (D : gmap Z (list (bv 8))) (b : Z) :
  snap_bytes S D -> snap_names S b -> is_Some (D !! b).
Proof.
  intros Hb [Hmeta | [(i & n & Hi & Hown) | [Hrange Hfree]]].
  - destruct Hmeta as [-> | [-> | (i & [n Hi] & ->)]].
    + exists (fss_sbb S). exact (sk_sb Hb).
    + eexists. exact (sk_bmap Hb).
    + destruct (sk_rec Hb i n Hi) as (bs & Hbs & _). by exists bs.
  - destruct Hown as [(k & [bs Hbs] & <-) | [Hnz <-]].
    + exists bs. exact (sk_blk Hb i n k bs Hi Hbs).
    + eexists. exact (sk_ind Hb i n Hi Hnz).
  - exact (sk_pool Hb b Hrange Hfree).
Qed.

(* ...AND AT THE RECOVERED MAP, WHICH IS THE MINT'S: a named block is a
   home block, hence covered and outside the log region. *)
Lemma snap_names_home (S : fs_state_rec) (P : Z -> list (bv 8))
    (home : gset Z) (b : Z) :
  snap_bytes S (fs_restrict P home) -> snap_names S b -> b ∈ home.
Proof.
  intros Hb Hn.
  destruct (snap_names_dom S (fs_restrict P home) b Hb Hn) as [bs Hbs].
  exact (proj1 (proj1 (fs_restrict_lookup_Some P home b bs) Hbs)).
Qed.

Lemma snap_names_cov (S : fs_state_rec) (P : Z -> list (bv 8))
    (cov : gset Z) (logstart b : Z) :
  snap_bytes S (fs_restrict P (fs_home_set cov logstart)) ->
  snap_names S b ->
  b ∈ cov /\ b ∉ log_region_set logstart.
Proof.
  intros Hb Hn.
  pose proof (snap_names_home S P (fs_home_set cov logstart) b Hb Hn) as Hh.
  rewrite /fs_home_set elem_of_difference in Hh. exact Hh.
Qed.

Section LedgerEra.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !fsLinkG Σ, !fsTopG Σ}.

  (* THE LEDGER THE MINT HANDS THE ALLOCATOR CORE, spelled at the home set:
     one [FsBlocks.fsblock] per home block IS [blk_ledger] at the restricted
     map, with no side condition at all (both shapes carry the block's own
     length clause). *)
  Lemma blk_ledger_of_home (γfs : fs_names) (P : Z -> list (bv 8))
      (home : gset Z) :
    ([∗ set] b ∈ home, fsblock (fs_bytes γfs) b (P b))
    ⊣⊢ blk_ledger (fs_gamma_L γfs) (fs_restrict P home).
  Proof.
    rewrite /blk_ledger.
    rewrite (big_sepM_proper (fun b bs => blk_owned (fs_gamma_L γfs) b bs)
               (fun b (_ : list (bv 8)) => fsblock (fs_bytes γfs) b (P b))
               (fs_restrict P home)); last first.
    { intros b bs Hbs.
      destruct (proj1 (fs_restrict_lookup_Some P home b bs) Hbs) as [_ ->].
      exact (gamma_blk_owned γfs b (P b)). }
    rewrite big_sepM_dom fs_restrict_dom //.
  Qed.

  Lemma fs_state_of_ledger_era (γfs : fs_names) S D :
    snap_ok S D ->
    blk_ledger (fs_gamma_L γfs) D
    -∗ fs_links (γlink (fs_gamma_L γfs)) (fss_inodes S)
    -∗ fs_state (fs_gamma_L γfs) S.
  Proof. exact (fs_state_of_ledger (fs_gamma_L γfs) S D). Qed.

  (* ...and the era's view is exclusive too, so nothing about the core is
     specific to a frozen instance *)
  Lemma fs_state_of_ledger_era_excl (γfs : fs_names) :
    phi_excl (fs_gamma_L γfs).
  Proof. exact (fs_gamma_L_excl γfs). Qed.

End LedgerEra.
