(* SpecBwrite.v -- the public interface of bwrite, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void bwrite(struct buf *b) {
       if (!holdingsleep(&b->lock)) panic("bwrite");
       virtio_disk_rw(b, 1);
     }

   The write-through: the caller's locked buffer goes to the disk, so the
   [disk_block] exchange is rw's WRITE case verbatim -- old disk bytes in,
   the buffer's bytes out -- and the buffer handle comes back untouched.
   The panic arm is dead: [bio_locked] carries the sleeplock token and the
   holder-carried pid cell, and the caller's own pid cell agrees, so
   holdingsleep returns 1 (SpecHoldingsleep.v's holder variant).

   Because the body calls virtio_disk_rw, this spec threads rw's whole
   resource list (SpecVirtioDiskRw.v): the running-process identity and
   sleep plumbing, the disk fabric, and the vdisk lock. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock SleepLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BufOwn BcacheInv BioInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* bwrite's own frame is 32 bytes (4 slots); its deepest callee is
   virtio_disk_rw (34). *)
Definition K_bwrite : nat := 38%nat.

Definition wp_bwrite_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}
    `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names) (k : nat)
    (pidv dev bno : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (bs bs_disk : list (bv 8)) :=
  let pcE : mword 64 := mword_of_int KernelSyms.bwrite in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_bwrite <= K)%nat ->
  (* rw's honest arithmetic premise: sector = blockno * 2 in 32 bits *)
  (uint bno < 2147483648)%Z ->
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 is the buffer *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  (* PARKING PREMISE (hart-generic scheduler protocol): the saved base enable
     is [true].  Everything below sleeps, and a parking thread must hand the
     trap CSRs across the crossing -- at level 0 with an enabled base the
     pushing acquire produces exactly that set.  See SpecSched.v. *)
  eb = true ->
  sie_cap_gpr γ m K -∗
  (* enters at noff 0 (rw's acquire raises it to what sleep demands) *)
  cpu_own γ 0 eb pj C -∗
  trap_csrs_pay 0 eb -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn -∗
  (* the caller's own pid cell, agreeing with the handle's (holdingsleep) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle rw's sleeps thread through *)
  procs_inv Φ γs -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* the locked buffer and the disk block it names *)
  bio_locked bn k pidv dev bno bs -∗
  disk_block γd (uint bno) bs_disk -∗
  ( ∀ (h : CPU) (g : gname) (mf : regfile),
      ⌜callee_saved_notp m mf⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 4 : mword 5) = cid_word_of h⌝ -∗
      sie_cap_gpr (CID := h) g mf K -∗
      cpu_own (CID := h) g 0 eb pj C -∗
      trap_csrs_pay (CID := h) 0 eb -∗
      pc_is (CID := h) ret_tgt -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc_at Φ γs h g (a_cpu_ctx (cid_word_of h)) pj -∗
      p_pid pj ↦₄{dq} pidv -∗
      bio_locked bn k pidv dev bno bs -∗
      (* the write-through: the disk now holds the buffer's bytes *)
      disk_block γd (uint bno) bs -∗
      WP (LoopE h : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type BWRITE.
  Parameter wp_bwrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}
      `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (k : nat)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (bs bs_disk : list (bv 8)),
      wp_bwrite_sconf_body γ Φ γs j γl γu γd γk pd pav pu bn k
                           pidv dev bno dq m K eb C bs bs_disk.
End BWRITE.
