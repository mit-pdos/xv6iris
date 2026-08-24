(* ====================================================================== *)
(*  FsImgCheck.v -- THE SANITY CHECK, DISK SIDE: the fs.img mkfs built IS   *)
(*  a well-formed file system, and the four verified user programs it holds *)
(*  ARE the tracked ELF raws, byte for byte.                               *)
(* ====================================================================== *)

(*  WHAT THIS FILE IS.

    [ElfKernel.v] and [ElfUser.v] check that each generated dump IS its
    binary, read through the general ELF semantics of [ElfFile.v].  This
    is the same move one layer out: [FsImgDisk.fsimg_dk] is the literal
    2,048,000-byte image mkfs wrote (kernel-rocq/FsImgRaw.v), and the
    theorems below read it through the general file-system semantics of
    [FsImg.v] -- the superblock parses, [fsimg_wf] holds, and

        /echo /init /sh /sync  resolve, in the ROOT DIRECTORY, to inodes
        4 7 13 22, whose CONTENT BYTES are literally [ElfUser.echo_elf],
        [init_elf], [sh_elf], [sync_elf].

    THE CHAIN THAT CLOSES HERE.  [ElfUser.v] proves things about four
    [pstring] blobs: they are well-formed ELF64s, their file-backed images
    are the tracked [<P>Instrs]/[<P>Data] maps, their entries and segment
    geometry are the dumps' constants.  Until now nothing said those blobs
    had anything to do with the machine the proofs run: they were the
    contents of [user/_<p>] on the build host.  The four [fsimg_<p>_at]
    equalities are the missing link -- the bytes exec() will read out of
    the FILE SYSTEM are those blobs -- so every [ElfUser] theorem now
    speaks about the files IN the file system of the disk
    [SystemAdequacy.xv6_fs_adequacy_xv6Σ] powers on with.  The four
    [fsimg_<p>_ok] corollaries below bundle exactly that and cost no new
    computation: they CITE [ElfUser]'s own theorems.

    THE LEAF RULE, as in [ElfKernel.v] / [ElfUser.v]: the image-check
    leaves may import each other (this one imports [FsImgDisk] and
    [ElfUser]), but NO PROOF FILE IMPORTS ANY OF THEM.  [SystemAdequacy.v]
    imports [FsImgDisk] and NOT this file, which is the whole reason the
    machine-facing half was split out: the ~1 MB of file-content
    [vm_compute] below stays off the system theorem's cone.

    HOW THE HEAVY SENTENCES ARE KEPT FINITE (design/elf.md's rules, and
    FsImg.v's header §"EXECUTABILITY IS A DESIGN CONSTRAINT"):

      - a file's bytes are NEVER read by computing [node_at] directly.
        [FsTree.file_bytes] is quadratic in the file size and rebuilds the
        block once per byte, so at 58 kB that computation does not
        terminate usefully.  [FsImg.node_at_file] is rewritten with FIRST
        (its [fs_blocks_full] premise is [fsimg_blocks_full] below, one
        line off [FsCrash.fs_blocks_length]), which turns it into one pass
        over the file's blocks;

      - a path is NEVER walked through [tree_of_disk] as a whole -- that
        would force every file's contents.  [FsImg.path_at_disk_dir] takes
        a one-step walk down to a single [DirView.dir_first] scan of the
        root directory, which is the [O(nrec)] scan [dirlookup] itself
        performs;

      - [fsimg_wf_ok] reads the superblock, the log header, the inode
        blocks, the bitmap, the root directory and the indirect blocks --
        tens of kB.  It does not force a single file's contents, and a
        conjunct that needed to would be a design error.

    If a [vm_compute] here ever fails, DO NOT weaken the statement.  A
    disagreement between the image and the raws is precisely the event
    this file exists to catch: find the disagreeing byte and fix the
    dumper (or mkfs).                                                      *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list.
From stdpp.bitvector Require Import definitions.
Require Import SailStdpp.Values.   (* [mword_of_int]: [FsTree.DOT]'s spelling *)
From xv6iris Require Import
  FsImgDisk FsImg LogDefs FsCrash
  DinodeEnc DirentEnc DirView FsTree
  ElfFile ElfUser.
From User Require Import
  SyncInstrs SyncData EchoInstrs EchoData
  ShInstrs   ShData   InitInstrs InitData.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  THE REDUCTION IS PAID ONCE, AT [Qed] -- NOT TWICE                      *)
(* ====================================================================== *)

(*  [vm_compute. reflexivity.] REDUCES THE GOAL TWICE: once in the tactic
    engine, and again in the KERNEL, which re-checks the [vm_cast] the
    tactic left in the proof term.  On this file's sentences that is the
    whole cost -- [fsimg_wf_ok] measured 65.9 s of tactic and 62.6 s of
    [Qed] for the same reduction, and the four [<p>_bytes_bool] sweeps
    pay the same way (claude-notes/optimization.md, "[Qed] re-checks and
    therefore DOUBLES every [vm_compute]").

    [vm_eq] builds that cast DIRECTLY -- [vm_cast_no_check (eq_refl rhs)]
    typechecks nothing at tactic time and hands the kernel the one
    reduction it was always going to do.  Same proof term, same VM, half
    the wall clock.

    IT MUST BE THE **RIGHT** SIDE.  [eq_refl rhs] casts [rhs = rhs] to
    [lhs = rhs], so the kernel reduces the heavy side ONCE; the mirror
    spelling [eq_refl lhs] casts [lhs = lhs] and the VM evaluates that
    heavy side TWICE -- measured WORSE than the [vm_compute. reflexivity.]
    it replaces (ElfKernel 54.0 s baseline, 28.7 s right-side, 78.3 s
    left-side).  The two spellings read identically; only the measurement
    tells them apart.

    WHAT IT COSTS, and the reason to reach for it only on the heavy
    sentences: a disagreement now surfaces at [Qed] as the kernel's
    conversion failure, without the goal in view.  When that happens put
    [vm_compute. reflexivity.] back on that ONE lemma to see the
    disagreeing byte -- and then fix the dumper or mkfs, never the
    statement (this file's header). *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ====================================================================== *)
(*  1.  THE SUPERBLOCK                                                     *)
(* ====================================================================== *)

(* mkfs's eight numbers.  Data region starts at [bmapstart + 1 = 47], and
   [47 + 1953 = 2000 = size]; the inode table is [ninodes/16 = 13] blocks
   at [logstart + nlog = 33]; a single bitmap block covers 8192 blocks,
   comfortably above [size].  [fsimg_wf_ok] below is what CHECKS those
   equations rather than restating them. *)
Definition fsimg_sb : fs_sb :=
  MkFsSb 0x10203040 2000 1953 200 31 2 33 46.

Lemma fsimg_parse_sb : fs_parse_sb fsimg_P = Some fsimg_sb.
Proof. vm_eq. Qed.

(* THE TIE TO [FsImgDisk]: the [2] that file's [fsimg_log_clean] and
   [fsimg_D0] are stated at is the IMAGE'S OWN [logstart], not a guess. *)
Lemma fsimg_sb_logstart : sb_logstart fsimg_sb = 2.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(*  2.  THE IMAGE IS WELL FORMED                                           *)
(* ====================================================================== *)

(* W1-W8 of [FsImg.fsimg_wf]: superblock arithmetic, clean log, every live
   inode's record, no block claimed twice, the bitmap agreeing with the
   used set, every directory's records, the root, and every directory's two
   dot records AT INDEX 0 AND 1 (W8 -- what [DirView.dir_dots_ix] demands
   and what W6/W7's [dir_first] readings cannot pin; measured cost of the
   added sweep, [Qed]'s re-check included, ~+20 s of this file's ~210 s). *)
Lemma fsimg_wf_ok : fsimg_wf fsimg_P fsimg_sb = true.
Proof. vm_eq. Qed.

(* THE HEADLINE READING of the above: the tree this image denotes has a
   root directory whose [".."] is itself. *)
Lemma fsimg_root_dir : fs_root_dir (tree_of_disk fsimg_P fsimg_sb).
Proof. exact (fsimg_wf_tree_root fsimg_P fsimg_sb fsimg_wf_ok). Qed.

(* Every block of a whole-disk image is [BSIZE] bytes -- [node_at_file]'s
   premise, and one of the two places this file touches [FsCrash]. *)
Lemma fsimg_blocks_full : fs_blocks_full fsimg_P.
Proof. intros b. apply fs_blocks_length. Qed.

(* THE W2 BRIDGE, AND THE CONSISTENCY CHECK BETWEEN THE TWO IMAGE FILES.
   [FsImg.fs_log_clean] is [LogDefs.hdr_n] at [LogDefs.log_hdr_bno] with
   both unfolded (FsImg.v §7 says so, because [LogDefs.v] is iris-heavy and
   that file must not be), so W2 of [fsimg_wf_ok] IS the fact
   [FsImgDisk.fsimg_log_clean] proves on its own -- and this lemma is what
   says the two do not drift.  [sb_logstart fsimg_sb] is the [2] the
   superblock itself carries, so the [2] the adequacy corollary pins
   [logstart] to is checked here rather than assumed there.  No computation:
   the unfolding is definitional, and the statement is CONVERTIBLE to
   [FsImgDisk.fsimg_log_clean]'s -- which is the point: the adequacy cone's
   four-byte check and this file's W2 sweep are the same fact. *)
Lemma fsimg_wf_log_clean :
  hdr_n (fsimg_P (log_hdr_bno (sb_logstart fsimg_sb))) = 0.
Proof.
  unfold hdr_n, log_hdr_bno.
  exact (fsimg_wf_log fsimg_P fsimg_sb fsimg_wf_ok).
Qed.

(* ====================================================================== *)
(*  2b.  WHAT THE BOOT-TIME STOCKING OF THE INODE POOL READS OFF THE IMAGE *)
(* ====================================================================== *)

(*  [IcacheBoot.ipool_alloc]'s ALLOCATED arm owes, per live inum, the pure
    bundle [inode_ok] / [dir_ok] / [dir_dots_ix] / [dir_orphan_clean] /
    [dir_uniq], and its FREE arm owes a type-0 record for every other inum
    of the region.  Everything below is what the image side of that owes,
    and the RULE HERE IS COST: each fact is ONE sweep with a lookup spec
    lemma in [FsImg.v], never a per-inum [vm_compute] (208 standalone
    decodes measured ~2 s each -- a no-go shape).  Anything W1-W8 already
    carries is CITED off [fsimg_wf_ok] and costs nothing at all.           *)

(* ---- W8, cited: the dot records ARE at index 0 and 1 ----------------- *)

(* [DirView.dir_dots_ix] for every directory in the image.  NO new
   computation: W8 of [fsimg_wf_ok] is the sweep. *)
Lemma fsimg_dots (i : Z) :
  0 <= i < sb_ninodes fsimg_sb ->
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb i)) = T_DIR_z ->
  dir_dots_ix i (fs_dinode fsimg_P fsimg_sb i)
    (fs_data_of fsimg_P (fs_dinode fsimg_P fsimg_sb i)).
Proof. exact (fsimg_wf_dots fsimg_P fsimg_sb i fsimg_wf_ok). Qed.

(* the root's own, which is the one [userinit]'s [namei("/")] parks *)
Lemma fsimg_root_dots :
  dir_dots_ix ROOTINO (fs_dinode fsimg_P fsimg_sb ROOTINO)
    (fs_data_of fsimg_P (fs_dinode fsimg_P fsimg_sb ROOTINO)).
Proof.
  apply fsimg_dots; [cbv [fsimg_sb ROOTINO sb_ninodes]; lia |].
  (* W7's own type projection -- [fsimg_root_type] below is the same fact,
     but this one is a citation and costs nothing *)
  exact (fs_root_wf_type fsimg_P fsimg_sb
           (fsimg_wf_root fsimg_P fsimg_sb fsimg_wf_ok)).
Qed.

(* ---- W9, cited: the LINK LEDGER's per-inum ticket counts ------------- *)

(*  [IcacheBoot.ireg_alloc]'s stage-B ledger premise stands at [W z =
    FsImg.fs_link_count P sb z] -- the number of ticket-bearing records of
    the image that name [z] -- and the region invariant then owes (L1)
    ([InodeRegion.ireg_link_ok]), [ireg_dir_wl0] and the strict root clause
    [ireg_root_ok] at that value.  All three are W9 of [fsimg_wf_ok], so NO
    new computation lands here; W9's own sweep is what added ~+20 s to this
    file's [vm_compute]. *)

(* (L1): no inum has more tickets than links *)
Lemma fsimg_link_le (z : Z) :
  Z.of_nat (fs_link_count fsimg_P fsimg_sb z)
    <= bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb z)).
Proof. exact (fsimg_wf_link_le fsimg_P fsimg_sb z fsimg_wf_ok). Qed.

(* [ireg_dir_wl0]: a DIRECTORY's plain column is empty -- the root's ["."]
   and [".."] are both SELF records and bear no ticket *)
Lemma fsimg_link_dir (z : Z) :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) = T_DIR_z ->
  fs_link_count fsimg_P fsimg_sb z = 0%nat.
Proof. exact (fsimg_wf_link_dir fsimg_P fsimg_sb z fsimg_wf_ok). Qed.

(* [DirLinks.dir_links_of_plain]'s [DirView.dlc_bound] premise and its ROOT
   EXCLUSION: every live image directory has exactly one link and IS the
   root (mkfs lays down one directory) *)
Lemma fsimg_dir_nlink (z : Z) :
  0 <= z < sb_ninodes fsimg_sb ->
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) = T_DIR_z ->
  bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb z)) = 1.
Proof. exact (fsimg_wf_dir_nlink fsimg_P fsimg_sb z fsimg_wf_ok). Qed.

Lemma fsimg_dir_root (z : Z) :
  0 <= z < sb_ninodes fsimg_sb ->
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) = T_DIR_z ->
  z = ROOTINO.
Proof. exact (fsimg_wf_dir_root fsimg_P fsimg_sb z fsimg_wf_ok). Qed.

(* ...and [ireg_root_ok]'s strict clause at the root, where the two meet *)
Lemma fsimg_root_link :
  fs_link_count fsimg_P fsimg_sb ROOTINO = 0%nat
  /\ bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb ROOTINO)) = 1.
Proof. exact (fsimg_wf_root_link fsimg_P fsimg_sb fsimg_wf_ok). Qed.

(* ---- the durable predicate's sharpening: file nlink EQUALS its count -- *)

(*  [FsImg.fs_links_eq] is stage F1's addition: the durable committed-view
    invariant ([FsWf.fs_durable_wf_body]) states link EQUALITIES, while W9
    keeps only [count <= nlink] for a file -- so the image discharge
    ([FsWfImg.fsimg_durable_wf]) takes this sweep as its one new literal
    fact.  One more W9-shaped pass: the ticket supply is rebuilt once and
    each inum pays one [fs_tick_count].  Measured cost is recorded in the
    worklist (same ballpark as W9's own ~20 s including [Qed]).           *)
Lemma fsimg_links_eq : fs_links_eq fsimg_P fsimg_sb = true.
Proof. vm_eq. Qed.

(* ---- CONJUNCT (15): NO LIVE NON-DOT ROOT RECORD NAMES THE ROOT ------- *)

(*  The one place the image's ticket discipline and the link RA's token
    discipline disagree: [FsImg.fs_rec_ticket] exempts a record naming its
    OWN home under ANY name, [FsStateInode.ent_tokenless] only ["."] and an
    orphaned-or-self [".."].  A root record called "foo" pointing at the
    root would owe a token and pay no ticket, and W1-W9 do not rule it out
    -- so [FsDurImg.img_link_valid] (hence [FsState.fs_boot_alloc_at]'s
    [✓ link_elem] premise) takes this sweep.  ONE [O(nrec)] pass over the
    root's 64 records, the same records W6/W8 already read; it is the only
    sweep in this file that touches exactly one directory. *)
Lemma fsimg_root_no_self : fs_root_no_self fsimg_P fsimg_sb = true.
Proof. vm_eq. Qed.

(* ---- W4 reindexed, cited: no inode names one block twice ------------- *)

(* [InodeInv.blkmap_wf]'s injectivity clause at every live inum, out of
   W4's [NoDup (fs_used_blocks ...)].  NO new computation -- and in
   particular NOT the per-index re-decode of the indirect block, which was
   measured at 636 s. *)
Lemma fsimg_slot_inj (i : Z) :
  0 <= i < sb_ninodes fsimg_sb ->
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb i)) <> 0 ->
  fs_slot_inj fsimg_P (fs_dinode fsimg_P fsimg_sb i).
Proof. exact (fsimg_wf_slot_inj fsimg_P fsimg_sb i fsimg_wf_ok). Qed.

(* ---- the region tail: [16 * nib] records, [ninodes] sweeps ----------- *)

(* [ninodes = 200] but the region is [16 * 13 = 208] records wide, so eight
   records are inside the icache's inode region and outside every W sweep.
   They are all free, and the pool's FREE arm needs to say so. *)
Lemma fsimg_region_free : fs_region_free fsimg_P fsimg_sb 13 = true.
Proof. vm_eq. Qed.

Lemma fsimg_region_tail_free (z : Z) :
  200 <= z < 208 -> bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) = 0.
Proof.
  intros Hz.
  apply (fs_region_free_spec fsimg_P fsimg_sb 13 z fsimg_region_free);
    [lia | cbv [fsimg_sb sb_ninodes]; lia | lia].
Qed.

(* ---- the region's LINK counts: [ireg_alloc]'s stage-A premises -------- *)

(* L3 and L4 ([IcacheBoot.image_free_nlink] / [image_nlink_short]) are the
   two claims no W conjunct carries -- W3 skips a type-0 record entirely,
   so the free records' [nlink]s are unswept, and nothing bounds [nlink]
   above.  Region-wide, for the reason [FsImg.fs_region_nlink]'s header
   gives: the tail's L3 cannot be recovered from [fs_region_free] (that
   would be circular) and L4 is about arbitrary bytes.  Same thirteen
   inode blocks as [fsimg_region_free]; measured together below. *)
Lemma fsimg_region_nlink : fs_region_nlink fsimg_P fsimg_sb 13 = true.
Proof. vm_eq. Qed.

(* ---- CONJUNCT (14): EVERY FREE RECORD IS BARE ------------------------ *)

(*  [FsState.fs_inodes] iterates [FsStateInode.inode_owned] over the WHOLE
    inode map and that carries [inode_local], whose [inl_size]/[inl_covers]
    would be FALSE of a garbage type-0 record: W3 skips such a record
    entirely and [fs_region_nlink] speaks only of [nlink].
    [FsImg.fs_region_bare] is the sweep ([FsDurImg]'s header (2)); with L3
    beside it, [FsDurImg.img_node_bare] gives [FsStateInode.fn_bare] and
    hence [inode_local] at every free inum of the region.  Same thirteen
    inode blocks as the two sweeps above, and it forces no file contents. *)
Lemma fsimg_region_bare : fs_region_bare fsimg_P fsimg_sb 13 = true.
Proof. vm_eq. Qed.

(* THE ONE REGION-WIDE HYPOTHESIS [FsCfgBoot.fs_cfg_alloc] takes beside
   [fsimg_wf_ok]: the tail's type plus L3/L4 over the whole region. *)
Lemma fsimg_region_wf : fs_region_wf fsimg_P fsimg_sb 13 = true.
Proof.
  unfold fs_region_wf.
  rewrite fsimg_region_free, fsimg_region_nlink. reflexivity.
Qed.

Lemma fsimg_free_nlink (z : Z) :
  0 <= z < 208 ->
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) = 0 ->
  bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb z)) = 0.
Proof.
  intros Hz.
  apply (fs_region_nlink_free fsimg_P fsimg_sb 13 z fsimg_region_nlink). lia.
Qed.

Lemma fsimg_nlink_short (z : Z) :
  0 <= z < 208 ->
  bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb z)) <= 32767.
Proof.
  intros Hz.
  apply (fs_region_nlink_short fsimg_P fsimg_sb 13 z fsimg_region_nlink). lia.
Qed.

(* ---- WHICH inums are live, as ONE set ------------------------------- *)

(* [FsImg.fs_live_set] is the [A] of the stocking split [R = A ⊎ (R ∖ A)].
   Twenty-two allocated records, [1 .. 22]; inum 0 and everything from 23
   up is free.  ONE sweep of the thirteen inode blocks. *)
Lemma fsimg_live_set :
  fs_live_set fsimg_P fsimg_sb = list_to_set (Z.of_nat <$> seq 1 22).
Proof. vm_eq. Qed.

(* ...and the membership law the split actually uses, off the computed set
   and [FsImg.fs_live_set_elem_of]: the live inums are exactly [1 .. 22],
   and they are exactly the records with a nonzero type. *)
Lemma fsimg_live_set_elem (z : Z) :
  z ∈ fs_live_set fsimg_P fsimg_sb <-> 1 <= z <= 22.
Proof.
  rewrite fsimg_live_set, elem_of_list_to_set, elem_of_list_fmap.
  split.
  - intros (k & -> & Hk). apply elem_of_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z).
    split; [rewrite Z2Nat.id by lia; reflexivity |].
    apply elem_of_seq. lia.
Qed.

Lemma fsimg_live_iff (z : Z) :
  1 <= z <= 22
  <-> 0 <= z < sb_ninodes fsimg_sb
      /\ bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb z)) <> 0.
Proof.
  rewrite <- fsimg_live_set_elem. apply fs_live_set_elem_of.
Qed.

(* ====================================================================== *)
(*  3.  PATHS OUT OF THE ROOT                                              *)
(* ====================================================================== *)

(* A directory-entry name is a [FsTree.fname = list (bv 8)]; the bytes are
   spelled the way [FsTree.DOT] spells its own. *)
Definition fsimg_byte (z : Z) : bv 8 := (mword_of_int z : mword 8).

Definition fname_echo : fname :=
  [fsimg_byte 0x65; fsimg_byte 0x63; fsimg_byte 0x68; fsimg_byte 0x6f].
Definition fname_init : fname :=
  [fsimg_byte 0x69; fsimg_byte 0x6e; fsimg_byte 0x69; fsimg_byte 0x74].
Definition fname_sh : fname :=
  [fsimg_byte 0x73; fsimg_byte 0x68].
Definition fname_sync : fname :=
  [fsimg_byte 0x73; fsimg_byte 0x79; fsimg_byte 0x6e; fsimg_byte 0x63].

Definition fsimg_root_data : nat -> list (bv 8) :=
  fs_file_data fsimg_P fsimg_sb ROOTINO.

Definition fsimg_root_nrec : nat :=
  dir_nrec (bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb ROOTINO))).

Lemma fsimg_root_type :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb ROOTINO)) = T_DIR_z.
Proof. vm_eq. Qed.

(* **THE FORM TO COMPUTE WITH.**  [FsImg.path_at_disk_dir]: one step out of
   the root is ONE [dir_first] scan of the root's 64 records -- no tree, no
   [dir_view] (which is [O(nrec^2)]), and above all no file contents. *)
Lemma fsimg_path_root (f : fname) :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [f]
  = (fun k => bv_unsigned (dir_inum fsimg_root_data k))
      <$> dir_first fsimg_root_data fsimg_root_nrec f.
Proof.
  apply (path_at_disk_dir fsimg_P fsimg_sb ROOTINO f).
  - cbv [fsimg_sb ROOTINO sb_ninodes]. lia.
  - exact fsimg_root_type.
Qed.

Lemma fsimg_echo_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_echo] = Some 4.
Proof. rewrite fsimg_path_root. vm_eq. Qed.

Lemma fsimg_init_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_init] = Some 7.
Proof. rewrite fsimg_path_root. vm_eq. Qed.

Lemma fsimg_sh_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_sh] = Some 13.
Proof. rewrite fsimg_path_root. vm_eq. Qed.

Lemma fsimg_sync_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_sync] = Some 22.
Proof. rewrite fsimg_path_root. vm_eq. Qed.

(* ====================================================================== *)
(*  4.  THE FILES' BYTES                                                   *)
(* ====================================================================== *)

(* [FsImg.node_at_file]'s right-hand side, named: the first
   [ceil(size/BSIZE)] blocks of the file concatenated, cut to [size].  ONE
   pass over the blocks -- see this file's header for why computing
   [node_at] without rewriting first is not slow but non-terminating. *)
Definition fsimg_file_bytes (i : Z) : list (bv 8) :=
  take (Z.to_nat (bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb i))))
       (fs_take_blocks (fs_file_data fsimg_P fsimg_sb i) 0
          (fs_nblocks (bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb i))))).

Lemma fsimg_node_file (i : Z) :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb i)) = T_FILE_z ->
  node_at fsimg_P fsimg_sb i = Some (NFile (fsimg_file_bytes i)).
Proof.
  intros Hty. unfold fsimg_file_bytes.
  apply (node_at_file fsimg_P fsimg_sb i fsimg_blocks_full);
    rewrite Hty; cbv [T_FILE_z T_DIR_z]; lia.
Qed.

(* ---- echo, inum 4, 35592 bytes --------------------------------------- *)

Lemma fsimg_echo_type :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb 4)) = T_FILE_z.
Proof. vm_eq. Qed.

(* [bool_decide] on a [list (bv 8)] equality, exactly as [ElfUser.v] states
   its image equalities: the decision procedure computes, so the proof term
   stays [eq_refl] and no 35592-element list enters it.  Resolution of the
   [Decision] instance goes by the TYPE, so [Typeclasses Opaque echo_elf]
   is never forced. *)
Lemma fsimg_echo_bytes_bool :
  bool_decide (fsimg_file_bytes 4 = ElfUser.echo_elf) = true.
Proof. vm_eq. Qed.

Lemma fsimg_echo_at :
  node_at fsimg_P fsimg_sb 4 = Some (NFile ElfUser.echo_elf).
Proof.
  pose proof fsimg_echo_bytes_bool as H. apply bool_decide_eq_true_1 in H.
  rewrite (fsimg_node_file 4 fsimg_echo_type), H. reflexivity.
Qed.

(* ---- init, inum 7, 35976 bytes --------------------------------------- *)

Lemma fsimg_init_type :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb 7)) = T_FILE_z.
Proof. vm_eq. Qed.

Lemma fsimg_init_bytes_bool :
  bool_decide (fsimg_file_bytes 7 = ElfUser.init_elf) = true.
Proof. vm_eq. Qed.

Lemma fsimg_init_at :
  node_at fsimg_P fsimg_sb 7 = Some (NFile ElfUser.init_elf).
Proof.
  pose proof fsimg_init_bytes_bool as H. apply bool_decide_eq_true_1 in H.
  rewrite (fsimg_node_file 7 fsimg_init_type), H. reflexivity.
Qed.

(* ---- sh, inum 13, 58312 bytes ---------------------------------------- *)

Lemma fsimg_sh_type :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb 13)) = T_FILE_z.
Proof. vm_eq. Qed.

(* The biggest of the four: 57 content blocks, so 45 of them are reached
   through the indirect block ([FsImg.fs_ind_ents] decodes it ONCE for the
   whole walk -- it is [let]-bound outside [fs_data_of]'s lambda, which is
   what keeps this a 2 s sentence rather than a 256-fold rescan). *)
Lemma fsimg_sh_bytes_bool :
  bool_decide (fsimg_file_bytes 13 = ElfUser.sh_elf) = true.
Proof. vm_eq. Qed.

Lemma fsimg_sh_at :
  node_at fsimg_P fsimg_sb 13 = Some (NFile ElfUser.sh_elf).
Proof.
  pose proof fsimg_sh_bytes_bool as H. apply bool_decide_eq_true_1 in H.
  rewrite (fsimg_node_file 13 fsimg_sh_type), H. reflexivity.
Qed.

(* ---- sync, inum 22, 34944 bytes -------------------------------------- *)

Lemma fsimg_sync_type :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb 22)) = T_FILE_z.
Proof. vm_eq. Qed.

Lemma fsimg_sync_bytes_bool :
  bool_decide (fsimg_file_bytes 22 = ElfUser.sync_elf) = true.
Proof. vm_eq. Qed.

Lemma fsimg_sync_at :
  node_at fsimg_P fsimg_sb 22 = Some (NFile ElfUser.sync_elf).
Proof.
  pose proof fsimg_sync_bytes_bool as H. apply bool_decide_eq_true_1 in H.
  rewrite (fsimg_node_file 22 fsimg_sync_type), H. reflexivity.
Qed.

(* ====================================================================== *)
(*  5.  THE HEADLINES: ONE PER VERIFIED PROGRAM                            *)
(* ====================================================================== *)

(* Each of these bundles the whole chain for one program: the NAME resolves
   in the root directory to an inum, that inum's node is a FILE whose bytes
   are the tracked raw, and -- by CITATION of [ElfUser], with no new
   computation at all -- that raw is a well-formed ELF64 whose file-backed
   image is the dump's own byte maps.  This is the sentence "the program
   the proofs reason about is the program on the disk". *)

Theorem fsimg_echo_ok :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_echo] = Some 4
  /\ node_at fsimg_P fsimg_sb 4 = Some (NFile ElfUser.echo_elf)
  /\ elf_wf ElfUser.echo_elf = true
  /\ elf_file_image ElfUser.echo_elf
     = EchoInstrs.echo_bytes ∪ EchoData.echo_data.
Proof.
  split; [exact fsimg_echo_path |].
  split; [exact fsimg_echo_at |].
  split; [exact ElfUser.echo_elf_wf | exact ElfUser.echo_elf_file_image].
Qed.

Theorem fsimg_init_ok :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_init] = Some 7
  /\ node_at fsimg_P fsimg_sb 7 = Some (NFile ElfUser.init_elf)
  /\ elf_wf ElfUser.init_elf = true
  /\ elf_file_image ElfUser.init_elf
     = InitInstrs.init_bytes ∪ InitData.init_data.
Proof.
  split; [exact fsimg_init_path |].
  split; [exact fsimg_init_at |].
  split; [exact ElfUser.init_elf_wf | exact ElfUser.init_elf_file_image].
Qed.

Theorem fsimg_sh_ok :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_sh] = Some 13
  /\ node_at fsimg_P fsimg_sb 13 = Some (NFile ElfUser.sh_elf)
  /\ elf_wf ElfUser.sh_elf = true
  /\ elf_file_image ElfUser.sh_elf = ShInstrs.sh_bytes ∪ ShData.sh_data.
Proof.
  split; [exact fsimg_sh_path |].
  split; [exact fsimg_sh_at |].
  split; [exact ElfUser.sh_elf_wf | exact ElfUser.sh_elf_file_image].
Qed.

Theorem fsimg_sync_ok :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_sync] = Some 22
  /\ node_at fsimg_P fsimg_sb 22 = Some (NFile ElfUser.sync_elf)
  /\ elf_wf ElfUser.sync_elf = true
  /\ elf_file_image ElfUser.sync_elf
     = SyncInstrs.sync_bytes ∪ SyncData.sync_data.
Proof.
  split; [exact fsimg_sync_path |].
  split; [exact fsimg_sync_at |].
  split; [exact ElfUser.sync_elf_wf | exact ElfUser.sync_elf_file_image].
Qed.
