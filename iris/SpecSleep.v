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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpMycpu.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import SchedCtx.
Require Import SpecSched.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation SL := KernelSyms.sleep.

Definition wp_sleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)
    (γk : gname) (lka : mword 64) (sk : string) (Rk : iProp Σ)
    (m : regfile) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sleep in
  let pj := proc_addr j in
  (* a0 = the channel, a1 = the caller's condition lock *)
  let chan : mword 64 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let lk0 : mword 64 := m !!! Regidx (mword_of_int 11 : mword 5) in
  let a_cpu_k := add_vec lk0 (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (22 <= av)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m av -∗
  intr_count γ root_ppn 1 -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γ root_ppn Φ γs -∗
  (* the caller's condition lock, HELD (acquired on this cpu) *)
  is_lock γk lka sk Rk -∗
  locked γk -∗
  Rk -∗
  a_cpu_k ↦₈ mycpu_ret cid_word -∗
  (* the running-thread bundle *)
  cur_proc pj -∗
  a_cpu_noff cid_word ↦₄ (mword_of_int 1 : mword 32) -∗
  (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
  p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ root_ppn Φ γs (a_cpu_ctx cid_word) -∗
  ( ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mf av -∗
      intr_count γ root_ppn 1 -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      (* lk reacquired, with its resource *)
      locked γk -∗
      Rk -∗
      a_cpu_k ↦₈ mycpu_ret cid_word -∗
      (* the running-thread bundle, refreshed *)
      cur_proc pj -∗
      a_cpu_noff cid_word ↦₄ (mword_of_int 1 : mword 32) -∗
      (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
      p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc γ root_ppn Φ γs (a_cpu_ctx cid_word) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SLEEP.
  Parameter wp_sleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γk : gname) (lka : mword 64) (sk : string) (Rk : iProp Σ)
      (m : regfile) (av : nat),
      wp_sleep_sconf_body γ root_ppn Φ γs j γl γk lka sk Rk m av.
End SLEEP.
