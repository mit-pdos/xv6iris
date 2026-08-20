(* ====================================================================== *)
(*  FsImgDisk.v -- THE MACHINE-FACING HALF OF THE mkfs IMAGE: the initial   *)
(*  disk as a byte function, its block view, and the ONE fact the system    *)
(*  theorem consumes -- that this image recovers, with no log to replay,    *)
(*  to itself.                                                             *)
(* ====================================================================== *)

(*  WHY THIS FILE IS SEPARATE FROM [FsImgCheck.v].

    [SystemAdequacy.v] is deliberately slim -- 3.6 s, on the strictly
    serial build tail (see [SystemAssumptions.v]'s header for what a
    careless addition there costs everybody).  Its FS corollary now names
    the LITERAL mkfs image rather than an abstract disk, and that needs
    exactly five definitions and one lemma: the byte function, its block
    view, the clean-log fact, the durable state and [fs_recovery] at it.
    They are here, and nothing else is, so the import cone
    [SystemAdequacy.v] gains is [PStringBytes] + the generated
    [Kernel.FsImgRaw] and NOTHING MORE.

    Everything that says what the image MEANS -- the superblock parse,
    [fsimg_wf], the per-program [node_at] / [path_at] theorems, and the
    bridge to [ElfUser]'s four verified binaries -- lives in
    [FsImgCheck.v], which imports this file.  That is where the ~1 MB of
    file-content [vm_compute] happens, and it is off the adequacy cone
    entirely.

    THE LEAF RULE (identical to [ElfKernel.v] / [ElfUser.v] / [FsImgCheck.v]):
    the image-check leaves may import each other, and [SystemAdequacy.v]
    imports THIS one because the system theorem is about this very disk.
    No PROOF file imports any of them.

    If a [vm_compute] here ever fails, DO NOT weaken the statement: a
    mismatch between the dump and the image mkfs built is precisely the
    event these files exist to catch.  Find the disagreeing byte and fix
    the dumper.                                                            *)

From Stdlib Require Import ZArith List.
From Stdlib.Strings Require Import PString.
From stdpp Require Import gmap.
From stdpp.bitvector Require Import definitions.
From xv6iris Require Import PStringBytes LogDefs FsCrash.
From Kernel Require Import FsImgRaw.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(*  1.  THE INITIAL DISK                                                    *)
(* ---------------------------------------------------------------------- *)

(* [VirtioModel]'s disk is a TOTAL byte function [Z -> bv 8] (FsCrash.v
   §1a says why it is total rather than a finite map), so the 2,048,000
   bytes mkfs wrote are read out of the generated hex string and every
   address outside them reads as zero.  That zero padding is not a
   modelling convenience: [XV6_DISK_BYTES] is larger than the image, and a
   real virtio disk hands back zeroes past the end of the file backing it.

   The zero byte is spelled [Z_to_bv 8 0], which is [ElfFile.elf_zero_byte]'s
   own spelling -- but written out rather than imported, because pulling
   [ElfFile] into this file would put the whole ELF semantics on
   [SystemAdequacy.v]'s cone for one constant.

   [Typeclasses Opaque] for the reason every big generated constant in the
   tree carries it: instance resolution must never unfold this into a
   2 MB computation. *)
Definition fsimg_dk : Z -> bv 8 :=
  fun a => if (0 <=? a) && (a <? FsImgRaw.fsimg_size)
           then pstring_hex_byte FsImgRaw.fsimg_hex a
           else Z_to_bv 8 0.
Global Typeclasses Opaque fsimg_dk.

(* THE BLOCK VIEW, which is where the file system's own vocabulary starts
   ([FsCrash.fs_blocks]).  Every theorem in [FsImgCheck.v] is stated over
   this, and [FsImg.v]'s abstract [P : Z -> list (bv 8)] is exactly its
   type -- so the check file instantiates with zero glue. *)
Definition fsimg_P : Z -> list (bv 8) := fs_blocks fsimg_dk.

(* ---------------------------------------------------------------------- *)
(*  2.  THE LOG IS CLEAN                                                    *)
(* ---------------------------------------------------------------------- *)

(* mkfs writes a zero log header, and [logstart] is the image's own 2 (the
   superblock says so; [FsImgCheck.fsimg_parse_sb] is what checks that,
   and this file does not need it -- 2 is a literal here exactly as it is
   in the image).

   This is the ONE compute on the adequacy cone, and it reads four bytes.  *)
Lemma fsimg_log_clean : hdr_n (fsimg_P 2) = 0.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(*  3.  THE DURABLE STATE, AND RECOVERY AT IT                               *)
(* ---------------------------------------------------------------------- *)

(* What a reboot finds: the home blocks of the image itself, over whatever
   block range the client covers.  [cov] stays a PARAMETER -- the FS's
   coverage set is the client's choice and nothing about the image
   constrains it. *)
Definition fsimg_D0 (cov : gset Z) : gmap Z (list (bv 8)) :=
  fs_restrict fsimg_P (fs_home_set cov 2).

(* **THE FACT THE SYSTEM THEOREM CONSUMES.**  [FsCrash.fs_recovery_clean]
   says that at [hdr_n = 0] recovery IS [fs_restrict] of the home set, so
   this is that lemma at [fsimg_log_clean] -- no computation beyond the
   four header bytes above.  [log_hdr_bno 2] is [2] by [LogDefs]'
   definition, which is why [fsimg_log_clean] is stated at [2] directly. *)
Lemma fsimg_recovery (cov : gset Z) :
  fs_recovery fsimg_P (fsimg_D0 cov) cov 2.
Proof.
  assert (Hn : hdr_n (fsimg_P (log_hdr_bno 2)) = 0) by exact fsimg_log_clean.
  apply (proj2 (fs_recovery_clean fsimg_P (fsimg_D0 cov) cov 2 Hn)).
  reflexivity.
Qed.
