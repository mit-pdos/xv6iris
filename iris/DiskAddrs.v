(* ====================================================================== *)
(* DiskAddrs.v -- the addresses of [struct disk]'s fields.                 *)
(*                                                                         *)
(* These were in DiskInv.v, which is above VirtioProto.v.  The per-        *)
(* descriptor RECEIPT (tools/vtest/README.md finding 5) lives inside the   *)
(* device invariant and has to name [disk.info[i].b], so the offsets moved *)
(* below it.  DiskInv.v re-exports this file, so nothing downstream        *)
(* changed its spelling.                                                   *)
(*                                                                         *)
(* Offsets are into the C layout of [struct disk] (kernel/virtio_disk.c):  *)
(*                                                                         *)
(*     +0    desc            +32   used_idx                                *)
(*     +8    avail           +40   info[NUM]  (16 bytes each: b, status)   *)
(*     +16   used            +168  ops[NUM]                                *)
(*     +24   free[NUM]       +296  vdisk_lock                              *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require SailStdpp.Values.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import KernelSyms.

Local Open Scope Z_scope.

Definition disk_base : Arch.pa :=
  SailStdpp.Values.mword_of_int (len := 64) KernelSyms.disk.

Definition d_desc_ptr  : Arch.pa := pa_add disk_base 0.
Definition d_avail_ptr : Arch.pa := pa_add disk_base 8.
Definition d_used_ptr  : Arch.pa := pa_add disk_base 16.
Definition d_free_cell (i : nat) : Arch.pa := pa_add disk_base (24 + i).
Definition d_used_idx  : Arch.pa := pa_add disk_base 32.
Definition d_info_b      (i : nat) : Arch.pa := pa_add disk_base (40 + 16 * i).
Definition d_info_status (i : nat) : Arch.pa := pa_add disk_base (48 + 16 * i).
Definition d_ops       (i : nat) : Arch.pa := pa_add disk_base (168 + 16 * i).
Definition d_lock : Arch.pa := pa_add disk_base 296.

(* descriptor-table entry i on the desc page *)
Definition d_desc (pd : Arch.pa) (i : nat) : Arch.pa := pa_add pd (16 * i).

(* avail-ring entry j (j < 8) on the avail page *)
Definition d_ring (pav : Arch.pa) (j : nat) : Arch.pa := pa_add pav (4 + 2 * j).
