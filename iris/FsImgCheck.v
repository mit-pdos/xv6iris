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
Proof. vm_compute. reflexivity. Qed.

(* THE TIE TO [FsImgDisk]: the [2] that file's [fsimg_log_clean] and
   [fsimg_D0] are stated at is the IMAGE'S OWN [logstart], not a guess. *)
Lemma fsimg_sb_logstart : sb_logstart fsimg_sb = 2.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(*  2.  THE IMAGE IS WELL FORMED                                           *)
(* ====================================================================== *)

(* W1-W7 of [FsImg.fsimg_wf]: superblock arithmetic, clean log, every live
   inode's record, no block claimed twice, the bitmap agreeing with the
   used set, every directory's records, and the root. *)
Lemma fsimg_wf_ok : fsimg_wf fsimg_P fsimg_sb = true.
Proof. vm_compute. reflexivity. Qed.

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
Proof. vm_compute. reflexivity. Qed.

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
Proof. rewrite fsimg_path_root. vm_compute. reflexivity. Qed.

Lemma fsimg_init_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_init] = Some 7.
Proof. rewrite fsimg_path_root. vm_compute. reflexivity. Qed.

Lemma fsimg_sh_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_sh] = Some 13.
Proof. rewrite fsimg_path_root. vm_compute. reflexivity. Qed.

Lemma fsimg_sync_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_sync] = Some 22.
Proof. rewrite fsimg_path_root. vm_compute. reflexivity. Qed.

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
Proof. vm_compute. reflexivity. Qed.

(* [bool_decide] on a [list (bv 8)] equality, exactly as [ElfUser.v] states
   its image equalities: the decision procedure computes, so the proof term
   stays [eq_refl] and no 35592-element list enters it.  Resolution of the
   [Decision] instance goes by the TYPE, so [Typeclasses Opaque echo_elf]
   is never forced. *)
Lemma fsimg_echo_bytes_bool :
  bool_decide (fsimg_file_bytes 4 = ElfUser.echo_elf) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fsimg_echo_at :
  node_at fsimg_P fsimg_sb 4 = Some (NFile ElfUser.echo_elf).
Proof.
  pose proof fsimg_echo_bytes_bool as H. apply bool_decide_eq_true_1 in H.
  rewrite (fsimg_node_file 4 fsimg_echo_type), H. reflexivity.
Qed.

(* ---- init, inum 7, 35976 bytes --------------------------------------- *)

Lemma fsimg_init_type :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb 7)) = T_FILE_z.
Proof. vm_compute. reflexivity. Qed.

Lemma fsimg_init_bytes_bool :
  bool_decide (fsimg_file_bytes 7 = ElfUser.init_elf) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fsimg_init_at :
  node_at fsimg_P fsimg_sb 7 = Some (NFile ElfUser.init_elf).
Proof.
  pose proof fsimg_init_bytes_bool as H. apply bool_decide_eq_true_1 in H.
  rewrite (fsimg_node_file 7 fsimg_init_type), H. reflexivity.
Qed.

(* ---- sh, inum 13, 58312 bytes ---------------------------------------- *)

Lemma fsimg_sh_type :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb 13)) = T_FILE_z.
Proof. vm_compute. reflexivity. Qed.

(* The biggest of the four: 57 content blocks, so 45 of them are reached
   through the indirect block ([FsImg.fs_ind_ents] decodes it ONCE for the
   whole walk -- it is [let]-bound outside [fs_data_of]'s lambda, which is
   what keeps this a 2 s sentence rather than a 256-fold rescan). *)
Lemma fsimg_sh_bytes_bool :
  bool_decide (fsimg_file_bytes 13 = ElfUser.sh_elf) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fsimg_sh_at :
  node_at fsimg_P fsimg_sb 13 = Some (NFile ElfUser.sh_elf).
Proof.
  pose proof fsimg_sh_bytes_bool as H. apply bool_decide_eq_true_1 in H.
  rewrite (fsimg_node_file 13 fsimg_sh_type), H. reflexivity.
Qed.

(* ---- sync, inum 22, 34944 bytes -------------------------------------- *)

Lemma fsimg_sync_type :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb 22)) = T_FILE_z.
Proof. vm_compute. reflexivity. Qed.

Lemma fsimg_sync_bytes_bool :
  bool_decide (fsimg_file_bytes 22 = ElfUser.sync_elf) = true.
Proof. vm_compute. reflexivity. Qed.

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
