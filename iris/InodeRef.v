(* InodeRef.v -- THE INODE-REFERENCE VOCABULARY, AT THE PROCESS/FILE LAYER.

   A COMPATIBILITY SHIM, and deliberately a thin one.  The predicate this
   file was created to hold -- "this pointer names a live itable entry and
   this is one of its references" -- already exists, one layer down, as
   [IcacheRef.inode_held]: the fs-icache line split the entry geometry, the
   Arc-style count algebra and the address-keyed reference out of
   [IcacheInv.v] into [IcacheRef.v] precisely so that [FileInv.v] and
   [ProcInv.v] could name a reference without importing the filesystem
   invariant cone (the log, the disk, the inode region).  So there is
   nothing left for this file to define.

   WHAT IT STILL DOES is keep the NAME reachable: about twenty files below
   the file table import [InodeRef] to get the reference vocabulary and the
   iref-slot supply in scope at once.  Re-exporting the two real modules is
   the whole content.

   THE AUTHORITY'S GNAME IS CANONICAL, and it lives in [IcacheRef.icfg]
   ([icfg_iref]) rather than in a class of its own: there is exactly one
   inode cache per system, so threading its gname would put a filesystem
   ghost name on [ProcInv.proc_priv] and hence on the thirty-odd spec files
   that mention it.  [icfg] is a superclass of [FileInv.fileG] for the same
   reason -- an FD_INODE file's payload IS an inode reference -- so a file
   that needs both takes [fileG] alone and must NOT bind [icacheG]/[icfg]
   beside it (two instance paths print identically and do not unify;
   durable-notes' typeclass-sweep pitfall). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Export IrefSlots.
Require Export IcacheRef.
Local Open Scope Z_scope.

(* [ientry k] is a kernel address, so it is never null.  Stated here under
   the name the process layer used before the split; [IcacheRef] proves it
   from [ientry_unsigned], together with injectivity, the scan step and the
   sentinel. *)
Lemma ientry_nonzero (k : nat) :
  (k <= NINODE)%nat -> ientry k <> (zero_reg : mword 64).
Proof. apply ientry_ne_zero. Qed.
