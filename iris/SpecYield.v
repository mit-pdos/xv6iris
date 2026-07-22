(* SpecYield.v -- the public interface of Yield, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   yield() gives up the CPU: from a normally-running kernel thread (no locks
   held, noff = 0, this CPU's current process is proc j, the scheduler
   parked under ▷), it acquires p->lock, marks the process RUNNABLE, parks
   through sched(), and -- once some scheduler dispatches the process again
   -- releases the lock and returns.  The postcondition is the precondition
   shape back (fresh scheduler context, lock free again, noff back to 0),
   plus full callee_saved: a timer-interrupt path can call yield repeatedly. *)
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
Require Import KptTree.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import SpecSched.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation YD := KernelSyms.yield.

Definition wp_yield_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.yield in
  let pj := proc_addr j in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (20 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  intr_count γ 0 -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γ Φ γs -∗
  cur_proc pj -∗
  a_cpu_noff cid_word ↦₄ (mword_of_int 0 : mword 32) -∗
  (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
  p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) -∗
  ( ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr γ mf av -∗
      intr_count γ 0 -∗
      pc_is ret_tgt -∗
      cur_proc pj -∗
      a_cpu_noff cid_word ↦₄ (mword_of_int 0 : mword 32) -∗
      (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
      p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type YIELD.
  Parameter wp_yield_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat),
      wp_yield_sconf_body γ Φ γs j γl m av.
End YIELD.
