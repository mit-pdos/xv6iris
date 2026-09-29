(* ====================================================================== *)
(* FsBootParams.v -- THE DISK PARAMETERS A BOOT IS TAKEN AT.               *)
(*                                                                        *)
(* The pure vocabulary the system theorem's statement is parameterised by:  *)
(* the boot mint's range, the pure projection of the crash predicate, and   *)
(* the literal mkfs image's coverage set and inode-region size.            *)
(*                                                                        *)
(* IT IS HERE AND NOT IN [SystemAdequacy.v] BECAUSE OF ALTITUDE.  Every    *)
(* one of these is a [Definition] over [FsCrash] / [FsDurSnap] vocabulary   *)
(* -- no Iris judgment, no ghost state, no adequacy -- and the file-system  *)
(* pin files and the durable syscall layer need them to STATE their own     *)
(* lemmas.  Parked in the system theorem's file they put the whole adequacy *)
(* cone (the [xv6_power_adequacy_gen] tower) in front of every such file;   *)
(* see claude-notes/design/code-organization.md -- a lemma belongs at the   *)
(* altitude of what it says.                                               *)
(*                                                                        *)
(* Nothing here mentions the image's BYTES.  The two facts that do --      *)
(* [SystemAdequacy.fsimg_image_wf] and [SystemAdequacy.fsimg_snap_ok] --    *)
(* are [FsImgCheck] citations and stay with the theorem that discharges     *)
(* the image hypothesis, so requiring this file costs no [FsImgCheck].     *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
                            (* the ssreflect [rewrite /x] the moved proof of
                               [fsimg_cov_elem_of] is written in.  IMPORT,
                               never Export: an Export propagates the [by]
                               notation into far-off files                 *)
Require Import FsState.     (* [fs_state_rec]                             *)
Require Import FsDurSnap.   (* [snap_ok] -- the durable snapshot           *)
Require Import FsCrash.     (* [fs_extent], [fs_recovery], [fs_blocks],
                               [hdr_wf]                                    *)

Local Open Scope Z_scope.

(* THE BOOT MINT's RANGE: the whole xv6 file system image, FSSIZE = 2000
   blocks of BSIZE = 1024 bytes (kernel/param.h, kernel/fs.h, mkfs/mkfs.c).
   Every boot is handed exclusive byte fragments of the era's disk image over
   [[0, XV6_DISK_BYTES)] ([RiscvAdequacy.power_boot_res]); the FS layer's
   block views are carved out of them (claude-notes/design/fs-log.md).  The
   base layer takes this as a PARAMETER -- no FS constant appears below this
   file. *)
Definition XV6_DISK_BYTES : nat := (2000 * 1024)%nat.

(* THE PURE PROJECTION OF THE CRASH PREDICATE: what [FsCrash.P_fs_named]
   says about the PHYSICAL disk it is stated over -- the durable extent's
   geometry, the map the machine would recover to, that map's log header,
   and that the recovered view IS a file system.

   IT IS WHAT EVERY BOOT AFTER THE FIRST KNOWS ABOUT ITS DISK, and there is
   nothing else: it is EXTRACTED from the crash predicate by
   [FsCrash.P_fs_project], which [RiscvAdequacy.riscv_power_adequacy] runs
   against its own [state_interp] at each PowerOn.  An assumed "the disk is
   still mkfs's image at every era" is refutable -- nothing proves that
   xv6's own writes leave the disk mkfs-shaped -- and there is none: the
   image hypothesis below is one equation about the INITIAL machine. *)
Definition fs_boot_pure (cov : gset Z) (ls : Z) (dk : Z -> bv 8) : Prop :=
  fs_extent cov ls XV6_DISK_BYTES /\
  exists D : gmap Z (list (bv 8)),
    fs_recovery (fs_blocks dk) D cov ls /\
    hdr_wf (fs_blocks dk) cov ls /\
    (* ...AND THE COMMITTED VIEW IS A FILE SYSTEM (lane CE).  This is the
       durability claim: the map the machine would recover to right now is
       the encoding of an abstract file-system state -- every inode's record
       parses and is locally well formed, no two inodes share a block, and
       the bitmap's bits are the used set ([FsDurSnap.snap_ok]).  It comes
       off [FsCrash.P_fs]'s durable snapshot, which the commit re-establishes
       at every group commit and nothing else ever moves. *)
    exists S : fs_state_rec, snap_ok S D.

(* ---------------------------------------------------------------------- *)
(* THE IMAGE'S COVERAGE SET (ruling R4).                                  *)
(*                                                                        *)
(* [cov] is the set of block numbers the proof maintains logical content    *)
(* for -- the domain of [FsBoot.fs_C0], and exactly the set               *)
(* [bread] accepts.  The generic theorems keep it a PARAMETER, because      *)
(* nothing about the image constrains it and the conclusion never mentions  *)
(* it; here it is instantiated at the image's own range.  Block 0 is        *)
(* excluded (binit leaves all thirty buffers claiming blockno 0), and the   *)
(* top is the superblock's [size = 2000].                                  *)
(*                                                                        *)
(* Stocking the inode pool is what forces the choice: every block a live    *)
(* image inode names has to be in [cov], on top of the log region, the      *)
(* inode blocks and the bitmap block.  At [cov = ∅] the statement said      *)
(* nothing about a file system at all.                                      *)
(* ---------------------------------------------------------------------- *)
Definition fsimg_cov : gset Z := list_to_set (Z.of_nat <$> seq 1 1999).

Lemma fsimg_cov_elem_of (b : Z) : b ∈ fsimg_cov <-> 1 <= b < 2000.
Proof.
  rewrite /fsimg_cov elem_of_list_to_set list_elem_of_fmap. split.
  - intros (k & -> & Hk). apply elem_of_seq in Hk. lia.
  - intros Hb. exists (Z.to_nat b).
    split; [lia | apply elem_of_seq; lia].
Qed.

(* the image's inode-region size, in blocks: [ninodes/16 + 1 = 200/16 + 1],
   which is [bmapstart - inodestart = 46 - 33].  [FsImgCheck]'s own sweeps
   ([fsimg_region_wf], [fsimg_region_free]) are stated at this 13. *)
Definition fsimg_nib : nat := 13%nat.
