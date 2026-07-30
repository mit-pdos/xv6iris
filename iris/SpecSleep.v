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
   its resource Rk, the running-thread bundle (▷ sched_vc, own context
   cells) refreshed, noff back at 1.  Nothing in the spec promises the
   wakeup HAPPENS (liveness); it promises what holds when sleep returns.

   IT DOES NOT RETURN ON THE HART IT PARKED FROM (SpecSched.v): proc
   contexts are migratable, so the continuation is quantified over the
   DISPATCHING hart [h] and its per-hart SIE ghost [g], every resource comes
   back at [(h, g)], the register fact weakens to [callee_saved_notp m mf]
   plus [mf !!! x4 = cid_word_of h] (CalleeSaved.v), and the conclusion is
   hart [h]'s own [WP (LoopE h)].  Consequences for the interface:
     - the cpu context slot [C] stays ONE hart-independent proposition: it is
       carried out of the entry bundle and back into the exit bundle
       unchanged.  A hart-INDEXED slot could not work -- nothing in the
       crossing turns [C cpu_id] into [C h], and a [C] admitting such a
       bridge is exactly a hart-independent one;
     - the lock tokens come back as [locked γk h] -- the re-acquire runs on
       hart [h];
     - [panic_wp_any] replaces [panic_wp]: the re-acquire's holding-panic arm
       has to be discharged at the RESUMING hart;
     - [eb = true] is now a premise.  At level 0 with an enabled base the
       trap CSRs sit in the SIE arm and the pushing acquire hands them out,
       so the parking thread genuinely holds the set the chain payload
       demands.  [trap_csrs_pay 0 eb] therefore still rides both sides --
       sleep's interior pop reaches level 0 -- but is now [trap_csrs]. *)
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
  eb = true ->
  (22 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ 1 eb pj C -∗
  (* sleep is NOT push/pop-order-balanced: it pops p->lock to level 0
     BEFORE re-acquiring the condition lock, so at eb = true the interior
     pop deposits the trap CSRs into the re-enabled arm and the
     re-acquire extracts them back -- the pay must ride the spec. *)
  trap_csrs_pay 0 eb -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv Φ γs -∗
  (* the caller's condition lock, HELD (acquired on this cpu) *)
  is_lock γk lka sk Rk -∗
  locked γk cpu_id -∗
  Rk -∗
  (* the running-thread bundle *)
  panic_wp_any -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
  ( ∀ (h : CPU) (g : gname) (mf : regfile),
      ⌜callee_saved_notp m mf⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 4 : mword 5) = cid_word_of h⌝ -∗
      sie_cap_gpr (CID := h) g mf av -∗
      cpu_own (CID := h) g 1 eb pj C -∗
      trap_csrs_pay (CID := h) 0 eb -∗
      pc_is (CID := h) ret_tgt -∗
      (* lk reacquired ON HART [h], with its resource *)
      locked γk h -∗
      Rk -∗
      (* the running-thread bundle, refreshed *)
      own_ctx (p_context pj) -∗
      ▷ sched_vc_at Φ γs h g (a_cpu_ctx (cid_word_of h)) pj -∗
      WP (LoopE h : expr riscv_lang) {{ Φ }}) -∗
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

(* ===================================================================== *)
(*  The [lock_openable]-generic form.                                     *)
(* ===================================================================== *)
(* The body above takes the condition lock as a STATIC [is_lock]; but a
   kalloc'd object's lock (a pipe's) is cancellable, and the licence to
   touch it is a credential [Tk] -- exactly the generalization acquire and
   release already have (ACQUIRE_GEN / RELEASE_GEN).  sleep touches lk
   three ways, so the caller owes three refutations of the dead state
   [Dk]: the interior release presents the [locked]/[locked_pre] tokens it
   is already holding, and the re-acquire presents [Tk], which sleep then
   hands back.

   The sleeper's own [Tk] rides its frame through sched(), which is what
   makes sleeping on a reclaimable object sound: as long as any process
   sleeps inside pipewrite/piperead it still holds its end reference, so
   the object cannot die under it.

   [wp_sleep_sconf_body] is the [Tk := emp], [Dk := False] instance
   (via WpLock.is_lock_openable); ProofSleep.SleepOfGen restates it. *)
Definition wp_sleep_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)
    (γk : gname) (lka : mword 64) (Rk Tk Dk : iProp Σ)
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
  eb = true ->
  (22 <= av)%nat ->
  (* the three refutations of the dead state.  The two token refutations are
     needed at EVERY hart: the interior release runs on the parking hart, the
     re-acquire on the dispatching one. *)
  (⊢ Tk -∗ Dk -∗ False) ->
  (forall i : CPU, ⊢ locked γk i -∗ Dk -∗ False) ->
  (forall i : CPU, ⊢ locked_pre γk i -∗ Dk -∗ False) ->
  sie_cap_gpr γ m av -∗
  cpu_own γ 1 eb pj C -∗
  (* same pay note as [wp_sleep_sconf_body]: the interior pop reaches 0 *)
  trap_csrs_pay 0 eb -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv Φ γs -∗
  (* the caller's condition lock, HELD, with the credential *)
  lock_openable γk lka Rk Dk -∗
  Tk -∗
  locked γk cpu_id -∗
  Rk -∗
  (* the running-thread bundle *)
  panic_wp_any -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
  ( ∀ (h : CPU) (g : gname) (mf : regfile),
      ⌜callee_saved_notp m mf⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 4 : mword 5) = cid_word_of h⌝ -∗
      sie_cap_gpr (CID := h) g mf av -∗
      cpu_own (CID := h) g 1 eb pj C -∗
      trap_csrs_pay (CID := h) 0 eb -∗
      pc_is (CID := h) ret_tgt -∗
      (* lk reacquired ON HART [h], with its resource and the credential *)
      Tk -∗
      locked γk h -∗
      Rk -∗
      (* the running-thread bundle, refreshed *)
      own_ctx (p_context pj) -∗
      ▷ sched_vc_at Φ γs h g (a_cpu_ctx (cid_word_of h)) pj -∗
      WP (LoopE h : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SLEEP_GEN.
  Parameter wp_sleep_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γk : gname) (lka : mword 64) (Rk Tk Dk : iProp Σ)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ),
      wp_sleep_gen_sconf_body γ Φ γs j γl γk lka Rk Tk Dk m av eb C.
End SLEEP_GEN.
