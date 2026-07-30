(* BufOwn.v -- [struct buf]'s field geometry and [buf_own], the caller-side
   buffer bundle virtio_disk_rw consumes.  A common home (used by both the
   disk driver's spec and the bio.c layer) so that neither imports the
   other's whole-function interface.

   struct buf (buf.h; offsets from the disassembly):
     valid@0  disk@4  dev@8  blockno@12  lock@16 (48B sleeplock)
     refcnt@64  prev@72  next@80  data@88 (BSIZE = 1024 bytes)

   [buf_own] deliberately covers ONLY what the rw operation touches:
     - b->blockno, at fraction 1/2 and read-only.  The other half of the
       cell (and of b->dev) lives in the bcache lock's resource forever:
       bget's scan reads every buffer's dev/blockno under bcache.lock alone,
       including buffers currently checked out to a sleeplock holder that is
       inside virtio_disk_rw -- so no caller can ever own the full cell.
     - b->disk, full: the driver hands it to the device protocol (1 while
       the request is in flight) and pins it back to 0 on return.
     - b->data, full, byte-granular, exactly BSIZE bytes.

   The remaining fields are owned elsewhere (BcacheInv.v): valid and the
   other half of dev/blockno by the per-buffer escrow / the bcache lock
   resource, refcnt/prev/next by the bcache lock resource, the sleeplock by
   its own is_sleeplock.  See claude-notes/projects/bio.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.

Local Open Scope Z_scope.

(* struct buf fields.  [b] is the buffer's base address. *)
Definition b_valid   (b : Arch.pa) : Arch.pa := b.
Definition b_disk    (b : Arch.pa) : Arch.pa := pa_add b 4.
Definition b_dev     (b : Arch.pa) : Arch.pa := pa_add b 8.
Definition b_blockno (b : Arch.pa) : Arch.pa := pa_add b 12.
Definition b_data    (b : Arch.pa) : Arch.pa := pa_add b 88.

(* the caller's buffer: the fields rw touches, byte-granular data *)
(* NOTE: like DiskInv.v (which re-exports this file), deliberately NO
   [Require SailStdpp.Base/Values] -- they leak typeclass instances that
   change what a [gmap Arch.pa _] binder elaborates to downstream.  [mword]
   is referenced qualified instead (durable-notes). *)
Definition buf_own `{!riscvGS Σ} (b : Arch.pa)
    (bno : SailStdpp.Values.mword 32)
    (dsk : SailStdpp.Values.mword 32) (bs : list (bv 8)) : iProp Σ :=
  (b_blockno b ↦₄{DfracOwn (1/2)} bno ∗
   b_disk b ↦₄ dsk ∗
   ⌜length bs = 1024%nat⌝ ∗
   ([∗ list] j ↦ byte ∈ bs, pa_add (b_data b) j ↦ₘ byte))%I.
