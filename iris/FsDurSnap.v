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

   THE POINTS-TO IS EXCLUSIVE.  [snap_gamma]'s [fsΦ] is the FULL ghost-map
   element [a -> v], exactly as the era's [FsBytesGamma.fs_gamma_L] is, and
   that is what makes the [∗] between two inodes of a durable [fs_state]
   MEAN something: under a persistent points-to the conjunction is vacuous
   -- two inodes naming one block would satisfy it -- and disjointness
   would have to live in a pure clause instead.  Here it IS the resources,
   which is why [fs_snap_read_ok] can derive [sk_disj] rather than carry it.

   WHERE THE VALUE-FIRST ALLOCATOR WENT (durable-disk lane H5).  Taking a
   byte MAP and CARVING [FsState.fs_state] out of it by pure disjointness
   clauses is ERA 0'S BUSINESS AND NOBODY ELSE'S -- it is the one producer
   with no source instance to mint from -- so the carve lives in
   [FsDurAlloc.v], above this file, and its single caller is
   [FsDurImg.img_fs_snap_alloc].  What is left here is the REGISTRY: the
   epoch's shape ([fs_snap], [P_dur]), the mint off readings
   ([snap_mint], [fs_snap_alloc_mint], [P_dur_alloc_mint]), the reading
   back out ([fs_snap_read_ok]) and the commit's swap ([dsnap_step_xfer]).

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
Require Import RiscvModelBytes.  (* [nth_byte] / [bv_eq_of_bytes] *)
Require Import FsImg.
Require Import LogDefs.       (* [fs_dbytes] -- the byte flattening       *)
Require Import Xv6Cameras.
Require Import FsDurBytes.    (* [fs_dbytes_blocks] -- Gamma-generically  *)
Require Import FsDurXfer.     (* THE RESOURCE TRANSPORT (lane H): [snap_gamma],
                                 [fs_state_xfer] -- both ends of a transport
                                 are [fs_state]s and nothing is decoded *)
Require Import FsDurRead.     (* THE SNAPSHOT'S BYTE IDENTITY (lane H3):
                                 [snap_auth], and the readings off it --
                                 [snap_blk_read_full], [snap_run_read],
                                 [blk_run_overlap]                        *)
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
(*  (the encoding is injective, section 1b), so a writer can identify it   *)
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
(*  (local maintenance) holds.  NOTHING MAINTAINS IT: at a snapshot it is  *)
(*  READ off the epoch's own [∗] ([fs_snap_read_ok], through               *)
(*  [FsStateDefs.phi_excl]), and the ONE producer that has to supply it    *)
(*  rather than read it is era 0's image carve ([FsDurAlloc]), where it is *)
(*  what a LINEAR byte ledger has to be split by.                          *)
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
     ([FsState.fs_links_valid_tok]).
     THE CHOICE FUNCTION rides in front of it (durable-disk G5): each
     entry's register value is existential in the bundle, so the family's
     element is indexed by one value function per inum, each satisfying that
     inum's own [FsStateInode.node_ent_ok]; the SLACK fragment's value is
     existential for the same reason. *)
  sk_links  : exists f v, link_elem_ok (fss_inodes S) f
                          /\ ✓ (link_elem (fss_inodes S) f
                                ⋅ link_tok_elem ROOTINO v);
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
  (* ---- THE LEDGER'S KEYS ARE REAL BLOCKS (durable-disk lane E-himg).
     Every block [D] names lies below the state's OWN [size].  It is the one
     direction the clauses above do not give: they say which blocks [D] MUST
     hold (the metadata, a node's own, every free block below [size]), and
     this says [D] holds nothing else.

     WHAT IT IS FOR: a BOOT MINT re-founds the era's configuration from the
     snapshot, and [FsReady.fgo_covbelow] -- "every covered block is a real
     file-system block" -- is a fact about the era's [cov] against the era's
     [size].  [cov] is fixed across power cycles and [fss_sb S] is not, so
     nothing outside the snapshot can relate them; with this clause and
     [dom D = fs_home_set cov ls] the relation IS the snapshot's.  Both
     producers have it for free: at the image [D]'s domain is the home set,
     which the image's own [FsBoot.fs_cov_in] and disk-size bound put below
     [size]; at a commit it is [FsCollect.cg_size] verbatim.
     LAST, so no destructuring pattern above moves. *)
  sk_dombelow : forall b, is_Some (D !! b) -> 0 <= b < sb_size (fss_sb S);
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
Global Arguments sk_dombelow {_ _} _.

(* THE REGION'S WIDTH, off [S]'s own superblock: mkfs rounds [ninodes] up to
   a whole inode block, so the region is [ninodes/16 + 1] blocks and the
   inum space is [16 *] that.  It is the width [sk_regdom] is stated at and
   the one [sk_dirloc]'s [DirView.dir_ok] is bounded by; at the boot
   configuration it IS [IcacheRef.icfg_nib]
   ([FirstTok.col_geom_of_config]'s own hypothesis). *)
Definition snap_nib (S : fs_state_rec) : nat := fs_nib S.

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
  { rewrite /snap_nib /fs_nib -Hw Nat2Z.id //. }
  rewrite Hnib. exact (sk_dirloc Hb i n Hi).
Qed.

(* the plain family validity, which is [sk_links]'s own left factor: the
   allocator ([FsState.fs_links_alloc]) takes this, the mint takes the
   slacked form. *)
Lemma sk_links_plain {S D} (H : snap_bytes S D) :
  exists f, link_elem_ok (fss_inodes S) f /\ ✓ link_elem (fss_inodes S) f.
Proof.
  destruct (sk_links H) as (f & v & Hok & Hv). exists f. split; [exact Hok |].
  exact (cmra_valid_op_l _ _ Hv).
Qed.

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
   witness is [SystemAdequacy.fsimg_snap_ok] -- [snap_ok] at the literal
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

(* ===================================================================== *)
(*  1c'. THE GEOMETRY -- THE ONE HALF OF THE TIE NO RESOURCE PINS         *)
(*       (durable-disk lane H3)                                           *)
(*                                                                        *)
(*  Everything else in [snap_ok] is a READING off a snapshot's own         *)
(*  resources ([fs_snap_read_ok]): the byte ties by agreement with the     *)
(*  epoch's authority at the committed view's bytes, the coupling and the  *)
(*  two disjointness clauses off [FsStateDefs.phi_excl], the local clauses *)
(*  off [FsStateInode.inode_owned].  These seven are NOT, and the reason   *)
(*  is one fact about a [ghost_map]: an AUTHORITY may hold entries no      *)
(*  fragment names, so nothing the snapshot owns bounds [D]'s domain or a  *)
(*  block's length, and nothing it owns says which INUMS the state names.  *)
(*  [FsDurXferWall.snap_shape_not_readable] is the refutation at the       *)
(*  tied form.                                                            *)
(*                                                                        *)
(*  ALL SEVEN ARE CONFIGURATION FACTS and both producers have them for     *)
(*  free: at a commit they are [FsCollect.col_geom] plus [col_hand]'s own  *)
(*  domain and directory rows; at the image they are the mkfs geometry.    *)
(*  Not one of them is about the file system's CONTENTS, which is why the  *)
(*  used-set coupling and the byte ties -- the expensive half -- no longer *)
(*  have to be materialised anywhere.                                     *)
(*                                                                        *)
(*  EVERY CLAUSE IS A CLAUSE OF [snap_bytes] VERBATIM, so                  *)
(*  [snap_shape_of_ok] is seven projections and no producer pays anything  *)
(*  new.                                                                  *)
(* ===================================================================== *)
Record snap_shape (S : fs_state_rec) (D : gmap Z (list (bv 8))) : Prop :=
  MkSnapShape {
  ss_dombelow : forall b, is_Some (D !! b) -> 0 <= b < sb_size (fss_sb S);
}.

Global Arguments ss_dombelow {_ _} _.

Lemma snap_shape_of_ok (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
  snap_ok S D -> snap_shape S D.
Proof. intros H. split. exact (sk_dombelow (sk_bytes H)). Qed.

(* ...and its FILE-SYSTEM half, which is [FsState.fs_geom] and lives on the
   instance rather than on the snapshot (durable-disk lane H5): the
   superblock's layout, the region's inum column and domain, and the
   directory clauses at the region's width. *)
Lemma fs_geom_of_ok (S : fs_state_rec) (D : gmap Z (list (bv 8))) :
  snap_ok S D -> fs_geom S.
Proof.
  intros H. pose proof (sk_bytes H) as Hb. split.
  - exact (sk_sbok Hb).
  - exact (sk_reg Hb).
  - exact (sk_regdom Hb).
  - exact (sk_dirloc Hb).
Qed.

(* THE PER-INODE READING, as a record so that no clause of it is spelled
   inside a [⌜ ⌝] (where [a + b] would parse as [sum] -- durable-notes.md,
   the scope-stack trap). *)
Record snap_inode_read (sb : fs_sb) (D : gmap Z (list (bv 8)))
    (i : Z) (n : fs_node) : Prop := MkSnapInodeRead {
  sir_rec  : exists bs, D !! (sb_inodestart sb + i `div` 16) = Some bs
                        /\ rec_in_blk bs (64 * (i `mod` 16)) (fn_rec n);
  sir_blk  : forall k bs, fn_blk n !! k = Some bs ->
               D !! fn_naddr n k = Some bs;
  sir_ind  : fn_indb n <> 0 -> D !! fn_indb n = Some (ind_bytes (fn_ent n));
  sir_slot : fn_slot_inj n;
}.

Global Arguments sir_rec {_ _ _ _} _.
Global Arguments sir_blk {_ _ _ _} _.
Global Arguments sir_ind {_ _ _ _} _.
Global Arguments sir_slot {_ _ _ _} _.

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

  (* [snap_gamma], [snap_gamma_gtimeless] and [snap_gamma_excl] are
     [FsDurXfer]'s: the transport allocates the fresh family, so the family
     record belongs beside it. *)

  (* ------------------------------------------------------------------ *)
  (*  7.  THE SNAPSHOT, AND THE EPOCH REGISTRY                            *)
  (* ------------------------------------------------------------------ *)

  (* ONE epoch's durable instance.  Its IDENTITY is [FsDurRead.snap_auth]:
     the byte authority the epoch owns outright, standing at a map that
     lies INSIDE the committed view's own flattening [LogDefs.fs_dbytes D].
     That is an equation between two VALUES -- the WAL's block map and the
     snapshot's own byte map -- and it is what turns every byte tie of
     [snap_bytes] into a READING ([fs_snap_read_ok]) instead of a carried
     fact.

     THE REST IS THE INSTANCE: the abstract map's authority and every
     fragment, the nested predicate, and the inode region's keep-alive
     fragment at the root.  That fragment is OWNED rather than stated
     because [sk_links]' slack is exactly about it -- no directory entry
     accounts for the root's [nlink = 1] ([FsStateInode.ent_tokenless]
     exempts a SELF record) -- so the family's slacked validity is read off
     the resources ([FsState.fs_links_valid_tok]) like everything else.

     THE ONE PURE CONJUNCT LEFT IS [snap_shape], and section
     1c' says why no resource can pin it.  Nothing outside [crashN] ever
     holds a piece of any of this. *)
  Definition fs_snap Γ (g : gname) (B : gmap Z (bv 8)) D S : iProp Σ :=
    (snap_auth g B D
     ∗ ghost_map_auth (γtop Γ) 1 (fss_inodes S)
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag Γ i n)
     ∗ fs_state Γ S
     ∗ (∃ kv : ity, own (γlink Γ) (link_tok_elem ROOTINO kv))
     ∗ ⌜snap_shape S D⌝)%I.

  Global Instance fs_snap_timeless `{!GTimeless Γ} g B D S :
    Timeless (fs_snap Γ g B D S).
  Proof. rewrite /fs_snap. apply _. Qed.

  (* THE REGISTRY: the CURRENT snapshot, at the committed block map [D].
     The gname family, the byte map and the state are existential -- an
     epoch is named only by the map it stands at, which is what makes
     [P_dur] a function of [D] alone and therefore droppable into
     [FsCrash.P_fs] with no arity change. *)
  Definition P_dur D : iProp Σ :=
    (∃ (g gl gt : gname) (B : gmap Z (bv 8)) (S : fs_state_rec),
       fs_snap (snap_gamma g gl gt) g B D S)%I.

  Global Instance P_dur_timeless D : Timeless (P_dur D).
  Proof. rewrite /P_dur. apply _. Qed.


  (* ================================================================== *)
  (*  6a.  THE MINT'S PREMISE (durable-disk lane H4)                     *)
  (*                                                                    *)
  (*  WHAT A PRODUCER WITH NO SOURCE INSTANCE OWES, and it is NOT        *)
  (*  [snap_ok].  Four of the five rows are read off the producer's own  *)
  (*  resources and nothing accumulates them: the superblock's parse and *)
  (*  every inode's local clauses come off the collected payloads, the   *)
  (*  link family's slacked validity off [FsState.fs_links_valid_tok],   *)
  (*  and the RUNS row -- the shape of the byte legs, their pairwise     *)
  (*  DISJOINTNESS and the fact that their union sits inside the         *)
  (*  committed view's own flattening -- off                             *)
  (*  [FsDurXfer.phi_runs_ex_disj] / [phi_runs_ex_in], which are         *)
  (*  [FsStateDefs.phi_excl] and one [ghost_map_lookup] and nothing      *)
  (*  else.  The fifth is the GEOMETRY, which no resource pins           *)
  (*  ([FsDurXferWall], sections 1 and 1b).                              *)
  (*                                                                    *)
  (*  WHAT IS NOT HERE is the whole expensive half of [snap_bytes]: no   *)
  (*  byte tie, no used-set coupling, no [sk_disj], no cut clause.  The  *)
  (*  disjointness a linear ledger had to be CARVED by is now the shape  *)
  (*  of a [∗], read where the [∗] is.                                   *)
  (* ================================================================== *)
  Record snap_mint (S : fs_state_rec) (D : gmap Z (list (bv 8))) : Prop :=
    MkSnapMint {
    sm_shape : snap_shape S D;
    sm_geom  : fs_geom S;
    sm_local : snap_local S;
    sm_parse : fs_parse_sb (fun _ => fss_sbb S) = Some (fss_sb S);
    sm_links : exists (f : link_choice) (v : ity),
                 link_elem_ok (fss_inodes S) f
                 /\ ✓ (link_elem (fss_inodes S) f ⋅ link_tok_elem ROOTINO v);
    sm_runs  : exists PM : gmap Z (list (bv 8)),
                 xf_shape S PM /\ xr_disj (xr_fs S PM)
                 /\ xr_union (xr_fs S PM) ⊆ fs_dbytes D;
  }.

  Global Arguments sm_shape {_ _} _.
  Global Arguments sm_geom {_ _} _.
  Global Arguments sm_local {_ _} _.
  Global Arguments sm_parse {_ _} _.
  Global Arguments sm_links {_ _} _.
  Global Arguments sm_runs {_ _} _.

  Theorem fs_snap_alloc_mint S D :
    snap_mint S D ->
    ⊢ |==> ∃ (g gl gt : gname) (B : gmap Z (bv 8)),
        fs_snap (snap_gamma g gl gt) g B D S.
  Proof.
    intros Hm.
    destruct (sm_links Hm) as (f & v & Hfok & Hfv).
    destruct (sm_runs Hm) as (PM & Hshape & Hdisj & Hin).
    iMod (fs_state_mint_runs S PM f v Hshape Hdisj (sm_parse Hm) (sm_local Hm)
            (sm_geom Hm) Hfok Hfv) as (g gl gt) "(Hba & Hta & Htf & HS & Ht)".
    iModIntro. iExists g, gl, gt, (xr_union (xr_fs S PM)).
    rewrite /fs_snap /snap_auth.
    iFrame "Hba". iSplitR; [by iPureIntro |].
    iFrame "Hta Htf HS".
    iSplitL "Ht"; [by iExists v |].
    iPureIntro. exact (sm_shape Hm).
  Qed.

  Lemma P_dur_alloc_mint S D : snap_mint S D -> ⊢ |==> P_dur D.
  Proof.
    intros Hm.
    iMod (fs_snap_alloc_mint S D Hm) as (g gl gt B) "Hsnap".
    iModIntro. iExists g, gl, gt, B, S. iExact "Hsnap".
  Qed.

  (* ================================================================== *)
  (*  7b.  THE READING (durable-disk lane H3)                            *)
  (*                                                                    *)
  (*  [snap_ok S D] OFF THE SNAPSHOT'S OWN RESOURCES.  Nothing is        *)
  (*  consumed -- every conclusion below is PURE, which is what lets the *)
  (*  proofmode hand the resources back -- and nothing is supplied but   *)
  (*  the geometry.  The COMMIT does not go through this reading at all: *)
  (*  it mints its epoch off [snap_mint] (section 6a), where the very     *)
  (*  same split into "resources" and "geometry" appears at the ERA's     *)
  (*  view -- which is why the commit pays nothing new for it.            *)
  (* ================================================================== *)

  (* ---- the block legs of one inode ---- *)

  Lemma snap_read_blks (g gl gt : gname) B D (n : fs_node) :
    dblk_full D ->
    snap_auth g B D -∗
    ([∗ map] k ↦ bs ∈ fn_blk n,
       blk_owned (snap_gamma g gl gt) (fn_naddr n k) bs) -∗
    ⌜forall k bs, fn_blk n !! k = Some bs -> D !! fn_naddr n k = Some bs⌝.
  Proof.
    intros Hf. iIntros "Hau Hdat".
    rewrite bi.pure_forall. iIntros (k).
    rewrite bi.pure_forall. iIntros (bs).
    rewrite bi.pure_impl. iIntros (Hk).
    iDestruct (big_sepM_lookup _ _ k bs Hk with "Hdat") as "Hb".
    iApply (snap_blk_read_full g gl gt B D (fn_naddr n k) bs Hf with "Hau Hb").
  Qed.

  Lemma snap_read_ind (g gl gt : gname) B D (n : fs_node) :
    dblk_full D ->
    snap_auth g B D -∗ ind_owned (snap_gamma g gl gt) n -∗
    ⌜fn_indb n <> 0 -> D !! fn_indb n = Some (ind_bytes (fn_ent n))⌝.
  Proof.
    intros Hf. iIntros "Hau Hind".
    rewrite bi.pure_impl. iIntros (Hnz).
    rewrite /ind_owned (decide_False _ _ Hnz).
    iApply (snap_blk_read_full g gl gt B D (fn_indb n)
              (ind_bytes (fn_ent n)) Hf with "Hau Hind").
  Qed.

  Lemma snap_read_pool (g gl gt : gname) B D (nb : Z) (u : gset Z) :
    dblk_full D ->
    snap_auth g B D -∗ free_pool (snap_gamma g gl gt) nb u -∗
    ⌜forall b, 0 <= b < nb -> b ∉ u -> is_Some (D !! b)⌝.
  Proof.
    intros Hf. iIntros "Hau Hpool".
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hb).
    rewrite bi.pure_impl. iIntros (Hnu).
    assert (Hb' : Z.of_nat (Z.to_nat b) = b) by lia.
    rewrite (free_pool_split (snap_gamma g gl gt) nb u (Z.to_nat b)); [| lia].
    rewrite Hb' {1}/pool_elt (bool_decide_eq_false_2 _ Hnu).
    iDestruct "Hpool" as "[Helt _]". iDestruct "Helt" as (bsx) "Helt".
    rewrite blk_owned_1.
    iApply (snap_blk_dom g gl gt B D (DfracOwn 1) b bsx Hf with "Hau Helt").
  Qed.

  (* ---- ONE inode's own slots are distinct: exclusivity, not a clause -- *)

  Lemma inode_dat_owns Γ (n : fs_node) (b : Z) :
    fn_owns n b -> inode_dat Γ n ⊢ ∃ bs, blk_owned Γ b bs.
  Proof.
    intros Hon. rewrite /inode_dat. iIntros "[Hd Hi]".
    destruct Hon as [(k & [bs Hk] & <-) | [Hnz <-]].
    - iDestruct (big_sepM_lookup _ _ k bs Hk with "Hd") as "Hb".
      by iExists bs.
    - rewrite /ind_owned (decide_False _ _ Hnz).
      by iExists (ind_bytes (fn_ent n)).
  Qed.

  Lemma inode_phi_owns Γ (sb : fs_sb) (i : Z) (n : fs_node) (b : Z) :
    fn_owns n b -> inode_phi Γ sb i n ⊢ ∃ bs, blk_owned Γ b bs.
  Proof.
    intros Hon. rewrite inode_phi_dat. iIntros "[_ Hd]".
    iApply (inode_dat_owns Γ n b Hon with "Hd").
  Qed.

  Lemma inode_dat_slot_inj Γ (Hex : phi_excl Γ) (i : Z) (n : fs_node) :
    inode_local i n -> inode_dat Γ n -∗ ⌜fn_slot_inj n⌝.
  Proof.
    intros Hloc. iIntros "Hd".
    rewrite bi.pure_forall. iIntros (k).
    rewrite bi.pure_forall. iIntros (j).
    rewrite bi.pure_impl. iIntros (Hk).
    rewrite bi.pure_impl. iIntros (Hj).
    rewrite bi.pure_impl. iIntros (Hnz).
    rewrite bi.pure_impl. iIntros (Heq).
    destruct (decide (k = j)) as [-> | Hne]; [by iPureIntro |].
    iExFalso.
    assert (Hnzj : fn_slot n j <> 0) by (rewrite -Heq; exact Hnz).
    rewrite /inode_dat. iDestruct "Hd" as "[Hdat Hind]".
    destruct (decide (k = FS_MAXFILE)) as [HkM | HkM];
      destruct (decide (j = FS_MAXFILE)) as [HjM | HjM].
    - exfalso. apply Hne. rewrite HkM HjM //.
    - (* k is the indirect block, j a data block *)
      rewrite HkM fn_slot_ind in Hnz.
      rewrite (fn_slot_data n j ltac:(lia)) in Hnzj.
      rewrite HkM fn_slot_ind (fn_slot_data n j ltac:(lia)) in Heq.
      destruct (proj2 (inl_blk_dom Hloc j ltac:(lia)) Hnzj) as [bsj Hbj].
      iDestruct (big_sepM_lookup _ _ j bsj Hbj with "Hdat") as "Hbj".
      rewrite /ind_owned (decide_False _ _ Hnz).
      iEval (rewrite Heq) in "Hind".
      iApply (blk_owned_excl Γ Hex (fn_naddr n j)
                (ind_bytes (fn_ent n)) bsj with "Hind Hbj").
    - (* k a data block, j the indirect block *)
      rewrite (fn_slot_data n k ltac:(lia)) in Hnz.
      rewrite HjM fn_slot_ind in Hnzj.
      rewrite (fn_slot_data n k ltac:(lia)) HjM fn_slot_ind in Heq.
      destruct (proj2 (inl_blk_dom Hloc k ltac:(lia)) Hnz) as [bsk Hbk].
      iDestruct (big_sepM_lookup _ _ k bsk Hbk with "Hdat") as "Hbk".
      rewrite /ind_owned (decide_False _ _ Hnzj).
      iEval (rewrite Heq) in "Hbk".
      iApply (blk_owned_excl Γ Hex (fn_indb n) bsk
                (ind_bytes (fn_ent n)) with "Hbk Hind").
    - (* two data blocks *)
      rewrite (fn_slot_data n k ltac:(lia)) in Hnz.
      rewrite (fn_slot_data n j ltac:(lia)) in Hnzj.
      rewrite (fn_slot_data n k ltac:(lia))
              (fn_slot_data n j ltac:(lia)) in Heq.
      destruct (proj2 (inl_blk_dom Hloc k ltac:(lia)) Hnz) as [bsk Hbk].
      destruct (proj2 (inl_blk_dom Hloc j ltac:(lia)) Hnzj) as [bsj Hbj].
      assert (Hbj' : delete k (fn_blk n) !! j = Some bsj)
        by (rewrite lookup_delete_ne; [exact Hbj | exact Hne]).
      rewrite (big_sepM_delete _ (fn_blk n) k bsk Hbk).
      iDestruct "Hdat" as "[Hbk Hrest]".
      iDestruct (big_sepM_lookup _ _ j bsj Hbj' with "Hrest") as "Hbj".
      iEval (rewrite Heq) in "Hbk".
      iApply (blk_owned_excl Γ Hex (fn_naddr n j) bsk bsj with "Hbk Hbj").
  Qed.

  (* ---- the whole per-inode reading ---- *)

  Lemma snap_read_inode (g gl gt : gname) B D (sb : fs_sb)
      (i : Z) (n : fs_node) :
    dblk_full D -> 0 <= i < 2 ^ 32 -> inode_local i n ->
    snap_auth g B D -∗
    inode_phi (snap_gamma g gl gt) sb i n -∗
    ⌜snap_inode_read sb D i n⌝.
  Proof.
    intros Hf Hi Hloc. iIntros "Hau Hphi".
    rewrite inode_phi_dat. iDestruct "Hphi" as "[Hrec Hdat]".
    iDestruct (inode_dat_slot_inj (snap_gamma g gl gt)
                 (snap_gamma_excl g gl gt) i n Hloc with "Hdat") as %Hslot.
    rewrite /inode_dat. iDestruct "Hdat" as "[Hd Hi]".
    iDestruct (snap_read_blks g gl gt B D n Hf with "Hau Hd") as %Hblk.
    iDestruct (snap_read_ind g gl gt B D n Hf with "Hau Hi") as %Hind.
    rewrite (rec_owned_sb (snap_gamma g gl gt) sb i (fn_rec n) Hi)
            /rec_owned_at.
    pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1].
    assert (Hlen64 : length (dinode_bytes (fn_rec n)) = 64%nat)
      by exact (dinode_bytes_length (fn_rec n) (inl_rec_wf Hloc)).
    iDestruct (snap_run_read_full g gl gt B D
                 (sb_inodestart sb + i `div` 16) (64 * (i `mod` 16))
                 (dinode_bytes (fn_rec n)) Hf ltac:(lia)
                 ltac:(rewrite Hlen64; unfold BSZ; lia)
                 ltac:(rewrite Hlen64; lia) with "Hau Hrec")
      as %(cs & Hb & Hlencs & pre & post & Heq & Hpre).
    iPureIntro. split.
    - exists cs. split; [exact Hb |]. rewrite /rec_in_blk.
      exists pre, post. split; [exact Heq | exact Hpre].
    - exact Hblk.
    - exact Hind.
    - exact Hslot.
  Qed.

  Lemma snap_read_inodes (g gl gt : gname) B D (sb : fs_sb)
      (I : gmap Z fs_node) :
    dblk_full D ->
    (forall i n, I !! i = Some n -> 0 <= i < 2 ^ 32) ->
    (forall i n, I !! i = Some n -> inode_local i n) ->
    snap_auth g B D -∗
    ([∗ map] i ↦ n ∈ I, inode_phi (snap_gamma g gl gt) sb i n) -∗
    ⌜forall i n, I !! i = Some n -> snap_inode_read sb D i n⌝.
  Proof.
    intros Hf Hrng Hloc. iIntros "Hau Hin".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_impl. iIntros (Hi).
    iDestruct (big_sepM_lookup _ _ i n Hi with "Hin") as "Hphi".
    iApply (snap_read_inode g gl gt B D sb i n Hf (Hrng i n Hi) (Hloc i n Hi)
              with "Hau Hphi").
  Qed.

  (* ---- the used-set coupling: three refutations off the [∗] ---- *)

  Lemma fs_inodes_phi_disj Γ (Hex : phi_excl Γ) (sb : fs_sb)
      (I : gmap Z fs_node) :
    ([∗ map] i ↦ n ∈ I, inode_phi Γ sb i n) -∗
    ⌜forall i n j m b, I !! i = Some n -> I !! j = Some m ->
       fn_owns n b -> fn_owns m b -> i = j⌝.
  Proof.
    iIntros "Hin".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_forall. iIntros (j).
    rewrite bi.pure_forall. iIntros (m).
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hi).
    rewrite bi.pure_impl. iIntros (Hj).
    rewrite bi.pure_impl. iIntros (Hon).
    rewrite bi.pure_impl. iIntros (Hom).
    destruct (decide (i = j)) as [-> | Hne]; [by iPureIntro |].
    iExFalso.
    assert (Hj' : delete i I !! j = Some m)
      by (rewrite lookup_delete_ne; [exact Hj | exact Hne]).
    rewrite (big_sepM_delete _ I i n Hi).
    iDestruct "Hin" as "[Hi Hrest]".
    iDestruct (big_sepM_lookup _ _ j m Hj' with "Hrest") as "Hj".
    iDestruct (inode_phi_owns Γ sb i n b Hon with "Hi") as (bs1) "H1".
    iDestruct (inode_phi_owns Γ sb j m b Hom with "Hj") as (bs2) "H2".
    iApply (blk_owned_excl Γ Hex b bs1 bs2 with "H1 H2").
  Qed.

  Lemma fs_inodes_phi_used Γ (Hex : phi_excl Γ) (sb : fs_sb)
      (I : gmap Z fs_node) (nb : Z) (u : gset Z) :
    free_pool Γ nb u -∗
    ([∗ map] i ↦ n ∈ I, inode_phi Γ sb i n) -∗
    ⌜forall i n b, I !! i = Some n -> fn_owns n b -> 0 <= b < nb -> b ∈ u⌝.
  Proof.
    iIntros "Hpool Hin".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hi).
    rewrite bi.pure_impl. iIntros (Hon).
    rewrite bi.pure_impl. iIntros (Hb).
    iDestruct (big_sepM_lookup _ _ i n Hi with "Hin") as "Hphi".
    iDestruct (inode_phi_owns Γ sb i n b Hon with "Hphi") as (bs) "Hblk".
    iApply (free_pool_used Γ Hex nb u b bs Hb with "Hpool Hblk").
  Qed.

  (* ONE inum's record run and ONE inum's own block, out of the same [∗].
     They are different conjuncts even at the SAME inum, which is the case
     that makes this a lemma rather than two [big_sepM_lookup]s. *)
  Lemma inodes_owns_and_rec Γ (sb : fs_sb) (I : gmap Z fs_node)
      (i z : Z) (n m : fs_node) (b : Z) :
    I !! i = Some n -> I !! z = Some m -> fn_owns n b ->
    ([∗ map] j ↦ x ∈ I, inode_phi Γ sb j x) ⊢
      (∃ bs, blk_owned Γ b bs) ∗ rec_owned Γ sb z (fn_rec m).
  Proof.
    intros Hi Hz Hon.
    destruct (decide (z = i)) as [Hzi | Hne].
    - subst z. rewrite Hi in Hz. injection Hz as Hnm. subst m.
      rewrite (big_sepM_lookup _ _ i n Hi) inode_phi_dat.
      iIntros "[Hrec Hdat]". iSplitR "Hrec"; [| iExact "Hrec"].
      iApply (inode_dat_owns Γ n b Hon with "Hdat").
    - assert (Hiz : i <> z) by congruence.
      assert (Hz' : delete i I !! z = Some m)
        by (rewrite lookup_delete_ne; [exact Hz | exact Hiz]).
      rewrite (big_sepM_delete _ I i n Hi).
      rewrite (big_sepM_lookup _ _ z m Hz').
      rewrite (inode_phi_owns Γ sb i n b Hon) inode_phi_dat.
      iIntros "[Hb [Hrec _]]". iFrame "Hb Hrec".
  Qed.

  Lemma fs_owns_not_meta Γ (Hex : phi_excl Γ) (S : fs_state_rec) :
    (forall j m, fss_inodes S !! j = Some m -> 0 <= j < 2 ^ 32) ->
    (forall j m, fss_inodes S !! j = Some m -> inode_local j m) ->
    blk_owned Γ SB_BNO (fss_sbb S) -∗
    blk_owned Γ (sb_bmapstart (fss_sb S)) (bm_bytes BSIZE (fss_used S)) -∗
    ([∗ map] j ↦ m ∈ fss_inodes S, inode_phi Γ (fss_sb S) j m) -∗
    ⌜forall i n b, fss_inodes S !! i = Some n -> fn_owns n b ->
       ~ snap_meta S b⌝.
  Proof.
    intros Hrng Hloc. iIntros "Hsbb Hbmb Hin".
    rewrite bi.pure_forall. iIntros (i).
    rewrite bi.pure_forall. iIntros (n).
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hi).
    rewrite bi.pure_impl. iIntros (Hon).
    rewrite bi.pure_impl. iIntros (Hmeta).
    destruct Hmeta as [-> | [-> | (z & [m Hz] & ->)]].
    - iDestruct (big_sepM_lookup _ _ i n Hi with "Hin") as "Hphi".
      iDestruct (inode_phi_owns Γ (fss_sb S) i n SB_BNO Hon with "Hphi")
        as (bs) "Hblk".
      iApply (blk_owned_excl Γ Hex SB_BNO (fss_sbb S) bs with "Hsbb Hblk").
    - iDestruct (big_sepM_lookup _ _ i n Hi with "Hin") as "Hphi".
      iDestruct (inode_phi_owns Γ (fss_sb S) i n
                   (sb_bmapstart (fss_sb S)) Hon with "Hphi") as (bs) "Hblk".
      iApply (blk_owned_excl Γ Hex (sb_bmapstart (fss_sb S))
                (bm_bytes BSIZE (fss_used S)) bs with "Hbmb Hblk").
    - rewrite (inodes_owns_and_rec Γ (fss_sb S) (fss_inodes S) i z n m
                 _ Hi Hz Hon).
      iDestruct "Hin" as "[Hblk Hrec]".
      iDestruct "Hblk" as (bs) "Hblk".
      rewrite (rec_owned_sb Γ (fss_sb S) z (fn_rec m) (Hrng z m Hz))
              /rec_owned_at.
      pose proof (Z.mod_pos_bound z 16 ltac:(lia)) as [Hm0 Hm1].
      assert (Hlen64 : length (dinode_bytes (fn_rec m)) = 64%nat)
        by exact (dinode_bytes_length (fn_rec m) (inl_rec_wf (Hloc z m Hz))).
      rewrite blk_owned_1 byte_range_1.
      iApply (blk_run_overlap Γ Hex (DfracOwn 1) (DfracOwn 1)
                (sb_inodestart (fss_sb S) + z `div` 16) (64 * (z `mod` 16))
                (dinode_bytes (fn_rec m)) bs (dfrac_full_nvalid _)
                ltac:(lia) ltac:(rewrite Hlen64; unfold BSIZE_z; lia)
                ltac:(rewrite Hlen64; lia) with "Hblk Hrec").
  Qed.

  Lemma fs_meta_used Γ (Hex : phi_excl Γ) (S : fs_state_rec) :
    (forall j m, fss_inodes S !! j = Some m -> 0 <= j < 2 ^ 32) ->
    (forall j m, fss_inodes S !! j = Some m -> inode_local j m) ->
    blk_owned Γ SB_BNO (fss_sbb S) -∗
    blk_owned Γ (sb_bmapstart (fss_sb S)) (bm_bytes BSIZE (fss_used S)) -∗
    ([∗ map] j ↦ m ∈ fss_inodes S, inode_phi Γ (fss_sb S) j m) -∗
    free_pool Γ (sb_size (fss_sb S)) (fss_used S) -∗
    ⌜forall b, snap_meta S b -> 0 <= b < sb_size (fss_sb S) ->
       b ∈ fss_used S⌝.
  Proof.
    intros Hrng Hloc. iIntros "Hsbb Hbmb Hin Hpool".
    rewrite bi.pure_forall. iIntros (b).
    rewrite bi.pure_impl. iIntros (Hmeta).
    rewrite bi.pure_impl. iIntros (Hb).
    destruct Hmeta as [-> | [-> | (z & [m Hz] & ->)]].
    - iApply (free_pool_used Γ Hex (sb_size (fss_sb S)) (fss_used S)
                SB_BNO (fss_sbb S) Hb with "Hpool Hsbb").
    - iApply (free_pool_used Γ Hex (sb_size (fss_sb S)) (fss_used S)
                (sb_bmapstart (fss_sb S)) (bm_bytes BSIZE (fss_used S)) Hb
                with "Hpool Hbmb").
    - iDestruct (big_sepM_lookup _ _ z m Hz with "Hin") as "Hphi".
      rewrite inode_phi_dat. iDestruct "Hphi" as "[Hrec _]".
      rewrite (rec_owned_sb Γ (fss_sb S) z (fn_rec m) (Hrng z m Hz))
              /rec_owned_at.
      pose proof (Z.mod_pos_bound z 16 ltac:(lia)) as [Hm0 Hm1].
      assert (Hlen64 : length (dinode_bytes (fn_rec m)) = 64%nat)
        by exact (dinode_bytes_length (fn_rec m) (inl_rec_wf (Hloc z m Hz))).
      iApply (free_pool_used_run Γ Hex (sb_size (fss_sb S)) (fss_used S)
                (sb_inodestart (fss_sb S) + z `div` 16) (64 * (z `mod` 16))
                (dinode_bytes (fn_rec m)) Hb ltac:(lia)
                ltac:(rewrite Hlen64; unfold BSIZE_z; lia)
                ltac:(rewrite Hlen64; lia) with "Hpool Hrec").
  Qed.

  (* ---- THE READING ---- *)

  (* THE BLOCK WIDTH IS THE WAL'S FACT, NOT THE SNAPSHOT'S (durable-disk
     lane H5): "every block of [D] is a whole block" says nothing about any
     inode, any block role or any bitmap bit, and both readers have it off
     the committed view's own construction ([FsCrash.fs_recovery_dblk_full]
     at the crash predicate, the cache map's length row at a commit).  So it
     is a PREMISE here rather than a carried conjunct. *)
  Theorem fs_snap_read_ok (g gl gt : gname) B D S :
    dblk_full D ->
    fs_snap (snap_gamma g gl gt) g B D S -∗ ⌜snap_ok S D⌝.
  Proof.
    (* [snap_auth] is itself a pair, so the epoch's identity comes off as
       ONE hypothesis (a [&]-pattern would descend into it) *)
    intros Hf. iIntros "[Hau Hrest]".
    iDestruct "Hrest" as "(_ & _ & HS & Hkeep & %Hsh)".
    iEval (rewrite fs_state_split fs_ghost_split) in "HS".
    iDestruct "HS" as "(Hfp & Hlk & #Hp)".
    rewrite /fs_pure. iDestruct "Hp" as "(%Hparse & #Hlocs & %Hgeo)".
    pose proof (fun i n Hi => fs_geom_inum S i n Hgeo Hi) as Hrng.
    iAssert (⌜forall i n, fss_inodes S !! i = Some n -> inode_local i n⌝)%I
      with "[]" as %Hloc.
    { rewrite bi.pure_forall. iIntros (i).
      rewrite bi.pure_forall. iIntros (n).
      rewrite bi.pure_impl. iIntros (Hi).
      iDestruct (big_sepM_lookup _ _ i n Hi with "Hlocs") as %Hx.
      by iPureIntro. }
    rewrite /fs_footprint. iDestruct "Hfp" as "(Hsbb & Hin & Hbmb & Hpool)".
    (* ---- the byte ties, by agreement with the epoch's own authority ---- *)
    iDestruct (snap_blk_read_full g gl gt B D SB_BNO (fss_sbb S) Hf
                 with "Hau Hsbb") as %Hsbv.
    iDestruct (snap_blk_read_full g gl gt B D (sb_bmapstart (fss_sb S))
                 (bm_bytes BSIZE (fss_used S)) Hf with "Hau Hbmb") as %Hbmv.
    iDestruct (snap_read_inodes g gl gt B D (fss_sb S) (fss_inodes S)
                 Hf Hrng Hloc with "Hau Hin") as %Hnodes.
    iDestruct (snap_read_pool g gl gt B D (sb_size (fss_sb S)) (fss_used S)
                 Hf with "Hau Hpool") as %Hpoolv.
    (* ---- the used-set coupling, off the [∗] ---- *)
    iDestruct (fs_inodes_phi_disj (snap_gamma g gl gt)
                 (snap_gamma_excl g gl gt) (fss_sb S) (fss_inodes S)
                 with "Hin") as %Hdisj.
    iDestruct (fs_inodes_phi_used (snap_gamma g gl gt)
                 (snap_gamma_excl g gl gt) (fss_sb S) (fss_inodes S)
                 (sb_size (fss_sb S)) (fss_used S) with "Hpool Hin") as %Hused.
    iDestruct (fs_owns_not_meta (snap_gamma g gl gt)
                 (snap_gamma_excl g gl gt) S Hrng Hloc
                 with "Hsbb Hbmb Hin") as %Hnotmeta.
    iDestruct (fs_meta_used (snap_gamma g gl gt) (snap_gamma_excl g gl gt)
                 S Hrng Hloc with "Hsbb Hbmb Hin Hpool") as %Hmetau.
    (* ---- the link family's validity, slacked at the root ---- *)
    iDestruct "Hkeep" as (kv) "Hkeep".
    iDestruct (fs_links_valid_tok with "Hlk Hkeep") as %Hlinks.
    iPureIntro. apply snap_ok_intro; [| exact Hloc].
    split.
    - exact Hf.
    - exact Hsbv.
    - exact Hparse.
    - exact Hbmv.
    - exact Hpoolv.
    - exact Hrng.
    - intros i n Hi. exact (inode_repr_of_local i n (Hloc i n Hi)).
    - intros i n Hi. exact (sir_rec (Hnodes i n Hi)).
    - intros i n k bs Hi Hk. exact (sir_blk (Hnodes i n Hi) k bs Hk).
    - intros i n Hi Hnz. exact (sir_ind (Hnodes i n Hi) Hnz).
    - intros i Hi. exact (fs_geom_dom S i Hgeo Hi).
    - destruct Hlinks as (f & Hfok & Hfv). exists f, kv. split; assumption.
    - intros b Hb. apply (Hmetau b Hb).
      destruct Hb as [-> | [-> | (z & [m Hz] & ->)]].
      + apply (ss_dombelow Hsh). exists (fss_sbb S). exact Hsbv.
      + apply (ss_dombelow Hsh).
        exists (bm_bytes BSIZE (fss_used S)). exact Hbmv.
      + apply (ss_dombelow Hsh).
        destruct (sir_rec (Hnodes z m Hz)) as (cs & Hcs & _).
        exists cs. exact Hcs.
    - intros i n b Hi Hon.
      assert (Hin : is_Some (D !! b)).
      { destruct Hon as [(k & [bs Hk] & <-) | [Hnz <-]].
        - exists bs. exact (sir_blk (Hnodes i n Hi) k bs Hk).
        - exists (ind_bytes (fn_ent n)). exact (sir_ind (Hnodes i n Hi) Hnz). }
      split.
      + exact (Hused i n b Hi Hon (ss_dombelow Hsh b Hin)).
      + exact (Hnotmeta i n b Hi Hon).
    - exact Hdisj.
    - exact (fg_sbok Hgeo).
    - exact (fg_reg Hgeo).
    - intros i n Hi. exact (sir_slot (Hnodes i n Hi)).
    - exact (fg_regdom Hgeo).
    - exact (fg_dirloc Hgeo).
    - exact (ss_dombelow Hsh).
  Qed.

  (* ...and the same with the snapshot HANDED BACK, which is the form an
     invariant's opener needs.  Nothing is spent: the conclusion is pure. *)
  Lemma fs_snap_read_ok_keep (g gl gt : gname) B D S :
    dblk_full D ->
    fs_snap (snap_gamma g gl gt) g B D S -∗
    ⌜snap_ok S D⌝ ∗ fs_snap (snap_gamma g gl gt) g B D S.
  Proof.
    intros Hf. iIntros "H".
    iDestruct (fs_snap_read_ok _ _ _ _ _ _ Hf with "H") as %Hok.
    iSplitR; [by iPureIntro | iExact "H"].
  Qed.

  (* THE COMMIT'S STEP.  The previous epoch is DISCARDED (affine) and the
     next one allocated; no ghost is updated, so the step needs nothing
     from the old instance and nothing from the era but the value and the
     facts. *)
  Definition dsnap_step D D' : iProp Σ := (P_dur D ==∗ P_dur D')%I.

  (* THE STEP TAKES THE NEXT EPOCH ITSELF (durable-disk lane H2).  Its
     predecessor [dsnap_step_of] took the VALUE and the pure tie and built
     the epoch inside the WAL's permit -- the value-first entry, wrong at
     the commit for the reason plan section 4 gives -- and is DELETED: the
     file system now builds its own epoch at its own ghost step, where its
     invariants are open ([FsCollectAll.fs_snap_law_build]), and the WAL
     only swaps the registry over.  The old epoch is DISCARDED (affine);
     nothing is read out of it, which is why the step needs no premise
     about [D] at all. *)
  Lemma dsnap_step_xfer D D' : P_dur D' -∗ dsnap_step D D'.
  Proof. rewrite /dsnap_step. iIntros "H _". by iModIntro. Qed.

  (* ------------------------------------------------------------------ *)
  (*  8.  WHAT A CONSUMER READS OFF THE CURRENT SNAPSHOT                  *)
  (* ------------------------------------------------------------------ *)

  (* THE TIE IS A READING (durable-disk lane H3): the epoch's own resources
     say it, so the receipt costs nothing and nothing is spent -- the
     conclusion is pure and the snapshot stays whole. *)
  Lemma P_dur_tie D : dblk_full D -> P_dur D -∗ ∃ S, ⌜snap_ok S D⌝.
  Proof.
    intros Hf. iIntros "H". iDestruct "H" as (g gl gt B S) "Hs".
    iDestruct (fs_snap_read_ok _ _ _ _ _ _ Hf with "Hs") as %Hok. eauto.
  Qed.

  (* ...and the same with the snapshot HANDED BACK, which is the form an
     invariant's opener needs.  Everything the spike theorem reads off the
     current snapshot goes through this plus the pure [snap_ok_inode]. *)
  Lemma P_dur_tie_keep D :
    dblk_full D -> P_dur D -∗ ∃ S, ⌜snap_ok S D⌝ ∗ P_dur D.
  Proof.
    intros Hf. iIntros "H". iDestruct "H" as (g gl gt B S) "Hs".
    iDestruct (fs_snap_read_ok _ _ _ _ _ _ Hf with "Hs") as %Hok.
    iExists S. iSplitR; [iPureIntro; exact Hok |].
    iExists g, gl, gt, B, S. iExact "Hs".
  Qed.

  (* THE SPIKE'S READING: at the current snapshot, every region inum is
     named, its node satisfies the local clauses, and its record's bytes
     are the ones the committed map holds at its slot. *)
  Lemma P_dur_inode D (i : Z) :
    dblk_full D ->
    P_dur D -∗
      ∃ S, ⌜snap_ok S D⌝
           ∗ ⌜snap_inum_ok S i -> snap_inode_at S D i⌝
           ∗ P_dur D.
  Proof.
    intros Hf. iIntros "H".
    iDestruct (P_dur_tie_keep D Hf with "H") as (S Hok) "HP".
    iExists S. iFrame "HP". iSplitR; [iPureIntro; exact Hok |].
    iPureIntro. intros Hi. exact (snap_ok_inode S D i Hok Hi).
  Qed.

  (* THE SPIKE'S DURABLE HALF, at the current snapshot: a byte fact about
     the committed map's inode block becomes a fact about the durable FILE
     SYSTEM's inode.  This is what the snapshot registry adds over the flat
     byte blob, and it is the reading [mknod_durable] is stated at. *)
  Lemma P_dur_node_of_slot D (i : Z) (dn : dinode) :
    dblk_full D -> dinode_wf dn ->
    P_dur D -∗
      ∃ S, ⌜snap_ok S D⌝
           ∗ ⌜snap_inum_ok S i -> snap_slot_holds S D i dn ->
              snap_node_is S i dn⌝
           ∗ P_dur D.
  Proof.
    iIntros (Hf Hwf) "H".
    iDestruct (P_dur_tie_keep D Hf with "H") as (S Hok) "HP".
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
(*  [FsDurAlloc.blk_ledger_of_home] is the equation -- [blk_ledger] is the *)
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

(* ===================================================================== *)
(*  9a'. THE COVERAGE READING (durable-disk lane E-himg)                  *)
(*                                                                        *)
(*  What a BOOT MINT needs and [snap_names_cov] above does not give: not   *)
(*  "the blocks the snapshot names are covered" but the CONVERSE sweep --  *)
(*  every block of the metadata window is one the snapshot names, so it    *)
(*  is covered.  That is [FsCfgSnap.fs_cfg_alloc_snap]'s coverage corner   *)
(*  [1 <= b < fs_data_start -> b ∈ cov], and it is the fact that used to   *)
(*  arrive as a conjunct of the era-wide image hypothesis.                 *)
(*                                                                        *)
(*  THE WINDOW SPLITS FOUR WAYS, and each piece is one clause: block 1 is  *)
(*  [sk_sb]; the log region is not [D]'s at all and is covered by the      *)
(*  caller's own [log_region_set ⊆ cov] (a fact about the FIXED [cov] and  *)
(*  a [logstart] that [sk_sbok] pins at 2, so it does not move across a    *)
(*  power cycle); an inode-region block is inum [16 j]'s record block by   *)
(*  [sk_regdom] + [sk_rec]; and the bitmap block is [sk_bmap].  The DATA   *)
(*  region needs no reading -- the mint spends only the free pool there,   *)
(*  and [sk_pool] already puts every free block in [D].                    *)
(* ===================================================================== *)

(* the log region is the [LOGBLOCKS + 1] blocks from [ls] up, spelled as a
   membership rather than as [log_region_bound]'s converse.  [FsCrash]'s
   [log_slot_in_region] is the same fact one block at a time, and it lives
   in a file this one is BELOW. *)
(* ...and its converse, [FsImgBridge.log_region_bound] verbatim.  That file
   sits above this one ([LogInv] is on its cone), so the six lines are here
   rather than imported. *)
Lemma log_region_range (ls b : Z) :
  b ∈ log_region_set ls -> ls <= b <= ls + Z.of_nat LOGBLOCKS.
Proof.
  rewrite /log_region_set elem_of_union. intros [Hs | Hh].
  - rewrite elem_of_list_to_set elem_of_list_fmap in Hs.
    destruct Hs as (i & -> & Hi). apply elem_of_seq in Hi.
    rewrite /log_slot_bno. lia.
  - apply elem_of_singleton in Hh. rewrite /log_hdr_bno in Hh. lia.
Qed.

Lemma log_region_between (ls b : Z) :
  ls <= b <= ls + Z.of_nat LOGBLOCKS -> b ∈ log_region_set ls.
Proof.
  intros [Hlo Hhi]. rewrite /log_region_set elem_of_union.
  destruct (decide (b = ls)) as [-> | Hne].
  - right. apply elem_of_singleton. reflexivity.
  - left. rewrite elem_of_list_to_set elem_of_list_fmap.
    exists (Z.to_nat (b - ls - 1)). split.
    + rewrite /log_slot_bno. lia.
    + apply elem_of_seq. lia.
Qed.

Lemma snap_window_dom (S : fs_state_rec) (D : gmap Z (list (bv 8))) (b : Z) :
  snap_bytes S D ->
  1 <= b < fs_data_start (fss_sb S) ->
  is_Some (D !! b) \/ b ∈ log_region_set (sb_logstart (fss_sb S)).
Proof.
  intros Hb Hran.
  pose proof (sk_sbok Hb) as Hsb.
  pose proof (sbo_logstart _ Hsb) as Hls.
  pose proof (sbo_nlog _ Hsb) as Hnl.
  pose proof (sbo_inodestart _ Hsb) as Hist.
  pose proof (sbo_bmapstart _ Hsb) as Hbms.
  pose proof (sbo_ninodes _ Hsb) as Hni. unfold ROOTINO in Hni.
  assert (Hdiv : 0 <= sb_ninodes (fss_sb S) / 16) by (apply Z.div_pos; lia).
  assert (Hds : fs_data_start (fss_sb S) = sb_bmapstart (fss_sb S) + 1)
    by reflexivity.
  destruct (decide (b = 1)) as [-> | Hne1].
  - left. exists (fss_sbb S). exact (sk_sb Hb).
  - destruct (decide (b < sb_inodestart (fss_sb S))) as [Hlog | Hge].
    + right. apply log_region_between. unfold LOGBLOCKS. lia.
    + destruct (decide (b = sb_bmapstart (fss_sb S))) as [-> | Hnbm].
      * left. eexists. exact (sk_bmap Hb).
      * (* an inode-region block: inum [16 * (b - inodestart)] names it *)
        left.
        assert (Hj : 0 <= (b - sb_inodestart (fss_sb S))
                     < sb_ninodes (fss_sb S) / 16 + 1) by lia.
        destruct (sk_regdom Hb (16 * (b - sb_inodestart (fss_sb S)))
                    ltac:(lia)) as [n Hn].
        destruct (sk_rec Hb _ n Hn) as (bs & Hbs & _).
        exists bs.
        rewrite (Z.mul_comm 16 (b - sb_inodestart (fss_sb S))) in Hbs.
        rewrite (Z.div_mul (b - sb_inodestart (fss_sb S)) 16 ltac:(lia))
          in Hbs.
        replace (sb_inodestart (fss_sb S) + (b - sb_inodestart (fss_sb S)))
          with b in Hbs by lia.
        exact Hbs.
Qed.

(* ...AT THE MINT'S MAP: the corner, with the log region's own coverage
   supplied by the caller. *)
Lemma snap_cov_window (S : fs_state_rec) (P : Z -> list (bv 8))
    (cov : gset Z) (b : Z) :
  snap_bytes S (fs_restrict P (fs_home_set cov (sb_logstart (fss_sb S)))) ->
  log_region_set (sb_logstart (fss_sb S)) ⊆ cov ->
  1 <= b < fs_data_start (fss_sb S) -> b ∈ cov.
Proof.
  intros Hb Hlog Hran.
  destruct (snap_window_dom S _ b Hb Hran) as [[bs Hbs] | Hin].
  - apply fs_restrict_lookup_Some in Hbs as [Hh _].
    rewrite /fs_home_set elem_of_difference in Hh. exact (proj1 Hh).
  - exact (Hlog b Hin).
Qed.

(* ...AND THE OTHER DIRECTION, which is [FsReady.fgo_covbelow]: every
   covered block is a real file-system block of THIS era.  A home block is
   one of [D]'s keys ([sk_dombelow]); a log block sits below the inode
   region, hence below [size].  This is the only place the fixed [cov] and
   the era's own superblock are related, and it is why [sk_dombelow]
   exists. *)
Lemma snap_cov_below (S : fs_state_rec) (P : Z -> list (bv 8))
    (cov : gset Z) (b : Z) :
  snap_bytes S (fs_restrict P (fs_home_set cov (sb_logstart (fss_sb S)))) ->
  b ∈ cov -> 0 <= b < sb_size (fss_sb S).
Proof.
  intros Hb Hcov.
  pose proof (sk_sbok Hb) as Hsb.
  pose proof (sbo_logstart _ Hsb) as Hls.
  pose proof (sbo_nlog _ Hsb) as Hnl.
  pose proof (sbo_inodestart _ Hsb) as Hist.
  pose proof (sbo_bmapstart _ Hsb) as Hbms.
  pose proof (sbo_size _ Hsb) as Hsz.
  pose proof (sbo_ninodes _ Hsb) as Hni. unfold ROOTINO in Hni.
  pose proof (sbo_nblocks _ Hsb) as Hnb.
  assert (Hdiv : 0 <= sb_ninodes (fss_sb S) / 16) by (apply Z.div_pos; lia).
  assert (Hds : fs_data_start (fss_sb S) = sb_bmapstart (fss_sb S) + 1)
    by reflexivity.
  destruct (decide (b ∈ log_region_set (sb_logstart (fss_sb S))))
    as [Hin | Hout].
  - pose proof (log_region_range (sb_logstart (fss_sb S)) b Hin).
    unfold LOGBLOCKS in *. lia.
  - assert (Hh : b ∈ fs_home_set cov (sb_logstart (fss_sb S)))
      by (rewrite /fs_home_set elem_of_difference; split; assumption).
    apply (sk_dombelow Hb b).
    exists (P b). apply fs_restrict_lookup_Some. split; [exact Hh | reflexivity].
Qed.
