(* SpecVirtioDiskIntr.v -- the public interface of virtio_disk_intr, stated
   independently of its proof.

   The completion interrupt handler: under the vdisk_lock it acknowledges
   the device's interrupt line, then walks the used ring from the driver's
   used_idx up to the device's, and for each completed position RECLAIMS
   the request's bytes from the DMA lease (VirtioProto.virtio_proto_reclaim_acc),
   parks the payoff in [disk_res] for the sleeping publisher, clears
   b->disk and wakes the sleeper.

   The "virtio_disk_intr status" panic is REFUTED: a completed slot's
   status byte is pinned at 0 by the protocol (the device model only
   completes the two recognised request types, and xv6 publishes no other).

   The spec is caller-agnostic about which requests complete: its
   postcondition just returns the fabric; the per-request payoff reaches
   the right process through [disk_res].  It is stated at an arbitrary
   noff level so the (unproven) devintr/kerneltrap path can call it. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* intr's own frame is 32 bytes (4 slots); its deepest callee is wakeup (18) *)
Definition K_virtio_disk_intr : nat := 22%nat.

Definition wp_virtio_disk_intr_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !diskGhostG Σ, !uartGhostG Σ}
    `{GEN : GenId} `{CID : CpuId}
     (γs : list gname)
    (γu : uart_names) (γd : disk_names) (γk : gname)
    (pd pav pu : mword 64)
    (m : regfile) (K lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (b : bool) (lks : gset nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.virtio_disk_intr in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_virtio_disk_intr <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  length γs = NPROC ->
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (* acquire's order premise: every lock this hart already holds ranks below
     "virtio_disk"'s -- virtio_disk_intr acquires and releases [disk.vdisk_lock]
     once, so this contract is BALANCED and [lks] is unchanged end to end. *)
  locks_below lks (lock_rank "virtio_disk") ->
  sie_cap_gpr m K b pme -∗
  cpu_own lvl eb pme C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗ procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap mf))⌝ -∗
      sie_cap_gpr mf K b pme -∗
      cpu_own lvl eb pme C b lks -∗
      kernel_text -∗ pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type VIRTIODISKINTR.
  Parameter wp_virtio_disk_intr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !diskGhostG Σ, !uartGhostG Σ}
      `{GEN : GenId} `{CID : CpuId}
       (γs : list gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (m : regfile) (K lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (b : bool) (lks : gset nat),
      wp_virtio_disk_intr_sconf_body γs γu γd γk pd pav pu m K lvl eb pme C b lks.
End VIRTIODISKINTR.
