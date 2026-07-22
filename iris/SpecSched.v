(* SpecSched.v -- the public interface of Sched, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   sched() parks the current process: entered holding EXACTLY p->lock
   (noff == 1, interrupts off), with the process's state already moved to a
   parked state (yield sets RUNNABLE, sleep sets SLEEPING -- [needs_ctx st]).
   It swtches into this CPU's scheduler context, handing over the held lock,
   the state/chan cells, and the per-CPU cells (the p_sched chain payload,
   SchedCtx.v).  When sched RETURNS, some scheduler has dispatched this
   process again: same j, state now RUNNING, lock held again, cur_proc back
   at proc j, a FRESH parked-scheduler context under ▷, and tp = cid_word
   re-established (which is what makes the full callee_saved -- including
   x4 -- true in the postcondition). *)
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
Require Import SwtchCtx.
Require Import SchedCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation SD := KernelSyms.sched.

(* 14-slot context-field ownership, contents existential: what a RUNNING
   party holds of its own context field between switches (the resume wand
   hands it back; the next park saves into it).
   TEMPORARY HOME: belongs in SwtchCtx.v; move at the next SwtchCtx touch. *)
Definition own_ctx `{!riscvGS Σ} (pa : mword 64) : iProp Σ :=
  (∃ vs : list (mword 64), ⌜length vs = 14%nat⌝ ∗ ctx_cells pa vs)%I.

Definition wp_sched_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64)
    (m : regfile) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sched in
  let pj := proc_addr j in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  needs_ctx st = true ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (16 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  intr_count γ 1 -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γ Φ γs -∗
  proc_held j γl st ch -∗
  cpu_cells j -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) -∗
  ( ∀ (mf : regfile) (ch' : mword 64),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr γ mf av -∗
      intr_count γ 1 -∗
      pc_is ret_tgt -∗
      proc_held j γl RUNNING ch' -∗
      cpu_cells j -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SCHED.
  Parameter wp_sched_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64)
      (m : regfile) (av : nat),
      wp_sched_sconf_body γ Φ γs j γl st ch m av.
End SCHED.
