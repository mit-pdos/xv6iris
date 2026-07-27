(* SpecSleep.v -- the public interface of Sleep, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   sleep(chan, lk) parks the current process on [chan]: entered holding the
   caller's CONDITION LOCK lk (an arbitrary spinlock γk/Rk, so noff = 1 and
   intr_count 1), it takes p->lock, releases lk (noff 1→2→1 -- p->lock is
   the interlock that closes the missed-wakeup race), records chan, moves
   the state to SLEEPING, and parks through sched().  When some scheduler
   dispatches the process again (after a wakeup made it RUNNABLE), sleep
   clears chan, releases p->lock, REACQUIRES lk, and returns.

   The postcondition is the precondition shape back -- lk held again with
   its resource Rk, the running-thread bundle (cur_proc, ▷ sched_vc, own
   context cells) refreshed, noff back at 1 -- plus full callee_saved.
   Nothing in the spec promises the wakeup HAPPENS (liveness); it promises
   what holds when sleep returns. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SwtchCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation SL := KernelSyms.sleep.

Definition wp_sleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)
    (γk : gname) (lka : mword 64) (sk : string) (Rk : iProp Σ)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sleep in
  let pj := proc_addr j in
  (* a0 = the channel, a1 = the caller's condition lock *)
  let chan : mword 64 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let lk0 : mword 64 := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (22 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ 1 eb pj C -∗
  (* sleep is NOT push/pop-order-balanced: it pops p->lock to level 0
     BEFORE re-acquiring the condition lock, so at eb = true the interior
     pop deposits the trap CSRs into the re-enabled arm and the
     re-acquire extracts them back -- the pay must ride the spec. *)
  trap_csrs_pay 0 eb -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γ Φ γs -∗
  (* the caller's condition lock, HELD (acquired on this cpu) *)
  is_lock γk lka sk Rk -∗
  locked γk cpu_id -∗
  Rk -∗
  (* the running-thread bundle *)
  panic_wp -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
  ( ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr γ mf av -∗
      cpu_own γ 1 eb pj C -∗
      trap_csrs_pay 0 eb -∗
      pc_is ret_tgt -∗
      (* lk reacquired, with its resource *)
      locked γk cpu_id -∗
      Rk -∗
      (* the running-thread bundle, refreshed *)
      own_ctx (p_context pj) -∗
      ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SLEEP.
  Parameter wp_sleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γk : gname) (lka : mword 64) (sk : string) (Rk : iProp Σ)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ),
      wp_sleep_sconf_body γ Φ γs j γl γk lka sk Rk m av eb C.
End SLEEP.
