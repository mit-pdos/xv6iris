(* ====================================================================== *)
(* FsWf.v -- [dv_of_D]: the junk-tolerant total view of a finite block map. *)
(*                                                                          *)
(* WHY ONE DEFINITION IS ALL THAT IS LEFT.  This file carried               *)
(* [fs_durable_wf] / [fs_durable_wf_view] -- a whole-state PURE             *)
(* well-formedness predicate over the durable committed view -- together    *)
(* with its agreement/extensionality suite, and the [FsEff*]/[FsOp*] files  *)
(* proved that each of xv6's FS transactions preserves it.  Ruling 3        *)
(* (claude-notes/design/fs-state.md §6) states no whole-state pure          *)
(* predicate at all: the durable side is a SEPARATION-LOGIC conjunct of     *)
(* [FsCrash.P_fs], the snapshot [FsDurSnap.P_dur].  Nothing in the crash or *)
(* log layer had read the pure predicate since durable-disk 1d, so the      *)
(* predicate, its suite and the 17 preservation files over it are deleted.  *)
(*                                                                          *)
(* [dv_of_D] survives because it is not about well-formedness: it is the    *)
(* totalisation every [FsImg] decoder wants, read by [FsCollect],           *)
(* [FsCollectAll], [FsCrash], [LogSnapLaw] and [ProofEndOp].                *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
(* The seven imports below are no longer used by this file's own code; they
   are kept because downstream files reach these modules THROUGH this one --
   e.g. [FsCrash] writes qualified [FsImg.*] names without requiring [FsImg]
   itself.  Dropping them is a separate change that has to add the direct
   requires there first; the nightly dead-import sweep will not do it, since
   its per-file --verify cannot see a transitive-load break. *)
Require Import BioDefs.
Require Import DirentEnc.
Require Import DinodeEnc.
Require Import InodeDefs.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  THE VIEW OF A FINITE BLOCK MAP                                         *)
(* ====================================================================== *)

(* The committed view is a [gmap]; every [FsImg] decoder wants a total
   [Z -> list (bv 8)] and is junk-tolerant, so a missing block reads as
   [[]] (the superblock parse then fails on its length guard, every
   [fs_le_at] reads zeros, and no decoder gets stuck). *)
Definition dv_of_D (D : gmap Z (list (bv 8))) : Z -> list (bv 8) :=
  fun b => default [] (D !! b).

