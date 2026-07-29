(* SpecVirtioDiskInit.v -- the public interface of VirtioDiskInit, stated
   independently of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

   [virtio_disk_init] (kernel/virtio_disk.c) brings the virtio-mmio block
   device up.

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

   STATED OVER THE TIME-0 DEVICE INVARIANT (2026-07-29).  This contract used to
   own the raw [virtio_frag] half, on the premise that device init runs before
   the device invariant exists.  That premise is false: the disk thread must
   REFUTE [DevStepDiskWild] at every step, and only [virtio_proto] can do that,
   so [virtio_frag] can never sit raw in a CPU's precondition while the system
   runs.  So the contract takes [WpUart.disk_inv] and borrows the fragment
   around each MMIO access.  Two things make that work:

     - THE CONFIG TRACKER.  [virtio_proto]'s not-live arm holds HALF of the
       config cell at [v_cfg v] (VirtioProto.v); the caller holds the other
       half, [disk_cfg_is γv (DfracOwn (1/2)) c0], and hence knows
       deterministically which configuration the function has programmed so far
       even though the state itself lives under an invariant.  The device never
       writes [v_cfg] ([virtio_req_step_cfg]), so the pair is stable across
       device steps.  [⌜virtio_live c0 = false⌝] is what says the invariant is
       in its not-live arm at entry -- which the reset (STATUS <- 0) would
       re-establish anyway, but which the FIRST reads need before the reset.

     - THE LIVE FLIP.  [virtio_live] needs QUEUE_READY and DRIVER_OK, so the
       arm flips at the LAST MMIO write of the function (STATUS |= DRIVER_OK).
       That write is therefore where the DMA lease is paid in -- inside this
       function, not at the caller as before ([VirtioProto.virtio_proto_intro]
       is the transition) -- and the retired config halves are consumed by the
       freeze that mints the persistent [disk_cfg].

   THE POSTCONDITION consequently no longer hands back a device fragment.  What
   it hands back instead is what a driver needs and can only get here: the
   publisher token [disk_pub γv 0] -- which is ALSO the witness that the queue
   is live, since [virtio_proto]'s not-live arm holds the [dn_np] ghost_var at
   the FULL fraction and every [virtio_proto_*_acc] refutes that arm from the
   caller's half -- and the frozen [disk_cfg γv (virtio_init_cfg pd pav pu)]
   that [DiskInv.disk_geom] is built from.

   Two page conjuncts shrank, because the lease is paid from them: the used
   page goes to the device whole, and so do the two bytes of the available
   ring's index field.  What comes back of the available page is [seq 4 4092],
   i.e. from the ring entries on -- the two flags bytes below the index are
   forfeited too rather than handed back in two pieces, since no consumer has
   ever wanted them.  The descriptor page comes back whole (it is driver-owned
   throughout: it becomes [DiskInv.free_slot_res]).
   See claude-notes/projects/virtio-disk.md.

   THE PROOF IS TEMPORARILY ASSUMED (an [Axiom] in LinkVirtioDiskInit.v): the
   raw-frag proof (ProofVirtioDiskInit.v, deleted here, recoverable from git
   history) is being re-worked over the invariant-opening ACCESSOR-form virtio
   MMIO leaves, and the lease payment at the final STATUS write is new work.
   See claude-notes/projects/main-boot.md, G1. *)
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
Require Import DiskPtsto.
Require Import VirtioProto.
Require Import WpUart.
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

(* THE POSTCONDITION, as one named predicate rather than a twenty-wand chain
   spelled inline at the end of the body.  This is a performance-critical
   abstraction, not tidiness: the whole-function proof carries the continuation
   as a spatial hypothesis across all ~140 instruction steps, and every
   proofmode operation that splits or frames the context re-traverses its type
   -- which, written out, is twenty wands over three [seq 0 4096] big-ops.
   Sealed here it is one constant application, and the proof unfolds it exactly
   once, at the return.  Measured on the first thirty instructions: 24 s with
   the chain inline against 11.5 s with the continuation out of the way.
   [Typeclasses Opaque] (never [Opaque]) so instance search never walks in
   while [rewrite /vdi_post] at the return still does. *)
Definition vdi_post
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γ : gname) (γv : disk_names) (γa : gname) (Φ : mval -> iProp Σ)
    (m : regfile) (K : nat)
    (eb : bool) (pp : mword 64) (C : iProp Σ) (on : option nat)
    (ret_tgt c_cpu : mword 64) : iProp Σ :=
  ( ∀ (mr : regfile) (pd pav pu : mword 64),
    sie_cap_gpr γ mr K -∗
    cpu_own γ 0%nat eb pp C -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    ⌜ page_valid pd ⌝ -∗ ⌜ page_valid pav ⌝ -∗ ⌜ page_valid pu ⌝ -∗
    kalloc_env γa (avail_sub on 3) (m !!! Regidx (mword_of_int 4 : mword 5)) -∗
    (* The device is LIVE and its queue is the three pages just allocated: the
       DMA lease has been paid into [disk_inv]'s [virtio_proto] at the final
       STATUS write, and what comes out is the publisher token at 0 -- nothing
       has been published, and holding it is ALSO the proof that the protocol
       is in its live arm (the not-live arm owns the [dn_np] ghost_var whole) --
       together with the frozen configuration [DiskInv.disk_geom] is built on. *)
    disk_pub γv 0%nat -∗
    disk_cfg γv (virtio_init_cfg pd pav pu) -∗
    (* the queue pages, zeroed, minus what went to the device: the used page
       whole, and the available page's flags+index words (the lease pins the
       index at 0, which is what makes the published count start at 0).  What
       comes back of the available page is the ring entries on. *)
    ([∗ list] j ∈ seq 0 4096, (pa_add pd j) ↦ₘ byte_zero) -∗
    ([∗ list] j ∈ seq 4 4092, (pa_add pav j) ↦ₘ byte_zero) -∗
    disk_desc ↦₈ pd -∗
    disk_avail ↦₈ pav -∗
    disk_used ↦₈ pu -∗
    ([∗ list] j ∈ seq 0 8, (pa_add disk_free j) ↦ₘ (Z_to_bv 8 1)) -∗
    disk_lock ↦₄ (mword_of_int 0 : mword 32) -∗
    (* the name field is written once and then DISCARDED: what comes back is
       the persistent [lock_name], ready to be sealed into [is_lock]. *)
    lock_name disk_lock "virtio_disk"%string -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }})%I.
Global Typeclasses Opaque vdi_post.

Definition wp_virtio_disk_init_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γ : gname) (γv : disk_names) (γa : gname) (Φ : mval -> iProp Σ)
    (m : regfile) (K : nat)
    (eb : bool) (pp : mword 64) (C : iProp Σ) (on : option nat)
    (c0 : virtio_cfg) (vlock : bv 32) (vname vcpu : bv 64)
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
  (* the protocol is in its not-live arm at entry -- which is what the
     caller's config half [c0] identifies with the invariant's *)
  virtio_live c0 = false ->
  sie_cap_gpr γ m K -∗
  cpu_own γ 0%nat eb pp C -∗
  (* [kernel_data] supplies the "virtio_disk" string literal the auipc/addi
     pair points at -- the name handed to initlock. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  kalloc_env γa on (m !!! Regidx (mword_of_int 4 : mword 5)) -∗
  (* the disk fabric, borrowed from the invariant around each MMIO access,
     plus the caller's half of the config tracker: the pair is what keeps the
     configuration this function programs deterministic while the state lives
     under [disk_inv]. *)
  disk_inv γv -∗
  disk_cfg_is γv (DfracOwn (1/2)) c0 -∗
  disk_lock ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  disk_desc ↦₈ pd0 -∗
  disk_avail ↦₈ pav0 -∗
  disk_used ↦₈ pu0 -∗
  ([∗ list] j ∈ seq 0 8, (pa_add disk_free j) ↦ₘ free0 j) -∗
  vdi_post γ γv γa Φ m K eb pp C on ret_tgt c_cpu -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type VIRTIODISKINIT.
  Parameter wp_virtio_disk_init_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !diskGhostG Σ}
      `{CID : CpuId}
      (γ : gname) (γv : disk_names) (γa : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat)
      (eb : bool) (pp : mword 64) (C : iProp Σ) (on : option nat)
      (c0 : virtio_cfg) (vlock : bv 32) (vname vcpu : bv 64)
      (pd0 pav0 pu0 : mword 64) (free0 : nat -> bv 8),
      wp_virtio_disk_init_sconf_body γ γv γa Φ m K eb pp C on c0 vlock vname vcpu
                                     pd0 pav0 pu0 free0.
End VIRTIODISKINIT.
