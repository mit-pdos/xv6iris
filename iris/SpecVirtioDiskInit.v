(* SpecVirtioDiskInit.v -- the public interface of VirtioDiskInit, stated
   independently of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

   [virtio_disk_init] (kernel/virtio_disk.c) brings the virtio-mmio block
   device up.  Like [uartinit] it runs during boot, BEFORE [dev_inv] is
   allocated, so it owns the raw [virtio_frag] half directly rather than
   borrowing it from the invariant -- and it must, because it RESETS the device
   (STATUS <- 0), which no invariant could tolerate.

   What it does, in order:
     initlock(&disk.vdisk_lock, "virtio_disk")
     read + check MAGIC / VERSION / DEVICE_ID / VENDOR_ID
     STATUS <- 0                        (reset)
     STATUS <- ACKNOWLEDGE, then | DRIVER
     read DEVICE_FEATURES, mask, write DRIVER_FEATURES
     STATUS <- | FEATURES_OK, re-read STATUS and check the bit stuck
     QUEUE_SEL <- 0; check QUEUE_READY is clear; check QUEUE_NUM_MAX >= NUM
     kalloc() x3 for the descriptor table, available ring and used ring,
       memset each to zero
     QUEUE_NUM <- 8; the three ring addresses as low/high halves
     QUEUE_READY <- 1; disk.free[0..7] <- 1; STATUS <- | DRIVER_OK

   EVERY panic path is refuted rather than assumed, so this spec needs no
   [panic_wp]:
     - the four identification reads are constants of the model
       ([virtio_ident_reads], [virtio_queue_num_max_read]);
     - FEATURES_OK sticks because the write took ([virtio_status_readback]);
     - QUEUE_READY reads clear because the reset cleared it
       ([virtio_reset_not_ready]);
     - QUEUE_NUM_MAX = 8, so neither the "no queue 0" nor the "max queue too
       short" test fires;
     - kalloc cannot return null, because the caller supplies three pages.

   The postcondition is deliberately NOT the device's DMA lease.  It hands back
   the raw [virtio_frag] at a live configuration plus the three ZEROED queue
   pages, and building [virtio_lease] out of those (which needs the VA-to-PA
   identity bridge) is the caller's step -- see
   claude-notes/projects/virtio-disk.md. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import WpLock.
Require Import KallocInv.
Require Import ProcGeom CpuOwn.
Require Import KvmSpec.
Require Import VirtioModel.
Require Import IntrDefs.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation VIRTIO_DISK_INIT := KernelSyms.virtio_disk_init.

(* the [struct disk] fields this function touches (kernel/virtio_disk.c):
     +0x000 desc      the descriptor table page
     +0x008 avail     the available ring page
     +0x010 used      the used ring page
     +0x018 free[8]   one byte per descriptor, all set to 1 here
     +0x128 vdisk_lock *)
Definition disk_base : mword 64 := mword_of_int KernelSyms.disk.
Definition disk_desc : mword 64 := disk_base.
Definition disk_avail : mword 64 :=
  add_vec disk_base (sign_extend' 64 (mword_of_int 8 : mword 12)).
Definition disk_used : mword 64 :=
  add_vec disk_base (sign_extend' 64 (mword_of_int 16 : mword 12)).
Definition disk_free : mword 64 :=
  add_vec disk_base (sign_extend' 64 (mword_of_int 24 : mword 12)).
Definition disk_lock : mword 64 :=
  add_vec disk_base (sign_extend' 64 (mword_of_int 0x128 : mword 12)).

(* [virtio_disk_init]'s own frame is 32 bytes (4 slots) and its deepest callee
   is [kalloc], which needs 14 -- stated as a CONSTANT, per the spec-design
   rule that a stack bound is never coupled to the arguments. *)
Definition K_virtio_disk_init : nat := 18%nat.

Definition wp_virtio_disk_init_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ γa : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
    (eb : bool) (pp : mword 64) (C : iProp Σ) (on : option nat)
    (v0 : virtio_state) (vlock : bv 32) (vname vcpu : bv 64)
    (pd0 pav0 pu0 : mword 64) (free0 : nat -> bv 8) :=
  let pcE : mword 64 := mword_of_int KernelSyms.virtio_disk_init in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let c_name := lock_name_field disk_lock in
  let c_cpu := add_vec disk_lock (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
  (K_virtio_disk_init <= K)%nat ->
  (* three pages must be allocatable; this is the ONLY hypothesis any of the
     six panic paths needs *)
  (exists nb, on = Some nb /\ (3 <= nb)%nat) ->
  (* the kvm/kalloc convention: tp holds this hart's id, so kalloc's
     push_off/pop_off address this cpu's cells *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  sie_cap_gpr γ m K -∗
  cpu_own γ 0%nat eb pp C -∗
  (* [kernel_data] supplies the "virtio_disk" string literal the auipc/addi
     pair points at -- the name handed to initlock. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  kalloc_env γa on (m !!! Regidx (mword_of_int 4 : mword 5)) -∗
  (* the RAW device half: no [dev_inv], because this function resets the
     device and programs its queue.  Nothing is assumed about [v0]. *)
  virtio_frag v0 -∗
  disk_lock ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  disk_desc ↦₈ pd0 -∗
  disk_avail ↦₈ pav0 -∗
  disk_used ↦₈ pu0 -∗
  ([∗ list] j ∈ seq 0 8, (pa_add disk_free j) ↦ₘ free0 j) -∗
  ( ∀ (mr : regfile) (pd pav pu : mword 64),
    sie_cap_gpr γ mr K -∗
    cpu_own γ 0%nat eb pp C -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    ⌜ page_valid pd ⌝ -∗ ⌜ page_valid pav ⌝ -∗ ⌜ page_valid pu ⌝ -∗
    kalloc_env γa (avail_sub on 3) (m !!! Regidx (mword_of_int 4 : mword 5)) -∗
    (* The device is LIVE, its queue is the three pages just allocated, and
       nothing has been published: seen = used_idx = 0 and the interrupt line
       is low.  The disk image is untouched. *)
    virtio_frag (VirtioState (virtio_init_cfg pd pav pu)
                             zero32 zero16 zero16 (v_disk v0)) -∗
    (* the three queue pages, zeroed.  The two bytes of the available ring's
       index field being zero is what lets the caller pin [ai = 0] when it
       builds the DMA lease. *)
    ([∗ list] j ∈ seq 0 4096, (pa_add pd j) ↦ₘ byte_zero) -∗
    ([∗ list] j ∈ seq 0 4096, (pa_add pav j) ↦ₘ byte_zero) -∗
    ([∗ list] j ∈ seq 0 4096, (pa_add pu j) ↦ₘ byte_zero) -∗
    disk_desc ↦₈ pd -∗
    disk_avail ↦₈ pav -∗
    disk_used ↦₈ pu -∗
    ([∗ list] j ∈ seq 0 8, (pa_add disk_free j) ↦ₘ (Z_to_bv 8 1)) -∗
    disk_lock ↦₄ (mword_of_int 0 : mword 32) -∗
    (* the name field is written once and then DISCARDED: what comes back is
       the persistent [lock_name], ready to be sealed into [is_lock]. *)
    lock_name disk_lock "virtio_disk"%string -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type VIRTIODISKINIT.
  Parameter wp_virtio_disk_init_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ γa : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (eb : bool) (pp : mword 64) (C : iProp Σ) (on : option nat)
      (v0 : virtio_state) (vlock : bv 32) (vname vcpu : bv 64)
      (pd0 pav0 pu0 : mword 64) (free0 : nat -> bv 8),
      wp_virtio_disk_init_sconf_body γ γa Φ m K eb pp C on v0 vlock vname vcpu
                                     pd0 pav0 pu0 free0.
End VIRTIODISKINIT.
