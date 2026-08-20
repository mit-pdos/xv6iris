(* BioDefs.v -- the names, ghost functors, slot fragments, and client view
   shared at the boundary of the bio ownership layer.

   This is deliberately separate from [BioInv]: the log layer constructs a
   view and owns the pool of available bio reference slots, so it should not
   serialize behind the buffer cache's escrow, lock resource, and
   initialization proofs.  [BioInv] re-exports this file to preserve the
   existing API. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac numbers.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Values.
Require Import DiskPtsto.
Require Import Riscv.rv64d_types.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Local Open Scope Z_scope.

(* xv6's file-system block size.  Keep this at the bottom of the dependency
   graph: both the bio client view and pure inode byte indexing need it. *)
Definition BSIZE : nat := 1024%nat.
Definition BSLOTS : nat := 1024%nat.

Record bio_names := MkBioNames {
  bn_lk   : gname;                (* the "bcache" spinlock               *)
  bn_auth : gname;                (* ● (gmap nat (frac * positive))      *)
  bn_slot : gname;                (* the bslot supply                    *)
  bn_slk  : nat -> gname * gname; (* buffer k's sleeplock (γl, γsl)      *)
  bn_own  : nat -> gname;         (* buffer k's checkout token           *)
  bn_mid  : nat -> gname;         (* buffer k's recycle token            *)
}.

Section BioSlots.
  Context `{!bioG Σ}.

  Definition bslots (bn : bio_names) (n : nat) : iProp Σ :=
    own (bn_slot bn) (◯ n).
End BioSlots.

(* THE CLIENT VIEW the whole bio layer is parametric over: the disk ghost the
   covered blocks' [disk_block] fragments live at, the ONE covered device,
   the covered block-number range, and the two opaque content payloads.
   The log layer instantiates the payloads with its logged-view ghost halves;
   bio itself never opens them.  [bv_cov] must not contain 0 (binit leaves
   every buffer's blockno cell at 0) -- [BioInv.bio_init] takes that premise. *)
Record bio_view (Σ : gFunctors) := MkBioView {
  bv_gd    : disk_names;
  bv_dev   : SailStdpp.Values.mword 32;
  bv_cov   : gset Z;
  bv_clean : Z -> list (bv 8) -> iProp Σ;
  bv_dirty : Z -> list (bv 8) -> iProp Σ;
  (* The payloads ride an escrow opened inside atomic updates, so no step is
     available to absorb a later. *)
  bv_clean_tl : forall b bs, Timeless (bv_clean b bs);
  bv_dirty_tl : forall b bs, Timeless (bv_dirty b bs);
}.
Arguments bv_gd {Σ} _.
Arguments bv_dev {Σ} _.
Arguments bv_cov {Σ} _.
Arguments bv_clean {Σ} _.
Arguments bv_dirty {Σ} _.
Arguments bv_clean_tl {Σ} _ _ _.
Arguments bv_dirty_tl {Σ} _ _ _.
Arguments MkBioView {Σ} _ _ _ _ _ _ _.

Global Instance bio_view_clean_timeless {Σ} (V : bio_view Σ) b bs :
  Timeless (bv_clean V b bs) := bv_clean_tl V b bs.
Global Instance bio_view_dirty_timeless {Σ} (V : bio_view Σ) b bs :
  Timeless (bv_dirty V b bs) := bv_dirty_tl V b bs.
