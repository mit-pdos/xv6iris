(* SpecReparent.v -- the public interface of reparent (the whole function),
   stated independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be checked
   in parallel.

     // Pass p's abandoned children to init.
     // Caller must hold wait_lock.
     void reparent(struct proc *p) {
       struct proc *pp;
       for (pp = proc; pp < &proc[NPROC]; pp++)
         if (pp->parent == p) { pp->parent = initproc; wakeup(initproc); }
     }

   WHAT THE CONTRACT SAYS, AND WHY IT IS SHAPED THIS WAY.

   * THE PARENT TABLE COMES IN AS CELLS, NOT AS A LOCK.  "Caller must hold
     wait_lock" is exactly the statement that reparent is handed
     [WaitInv.parents_own] -- the CONTENTS-OUT form -- rather than an [is_lock]
     it would have to acquire.  reparent takes no lock and its [cpu_own] level
     is therefore unchanged end to end; the caller's obligation to be holding
     wait_lock lives one altitude up, with kexit.

   * THE EFFECT IS THE PURE MAP [rp_map p ip].  Every cell equal to the
     argument becomes [initproc]; everything else is untouched.  That is the
     whole postcondition, and it is exact -- no existential over the resulting
     table.

   * [initproc] IS READ AT AN ARBITRARY FRACTION and handed straight back.
     This is the weakest premise that works, and the fraction is load-bearing
     rather than cosmetic: the [ld a0,0(s4)] sits INSIDE the loop and runs once
     per reparented child, so a contract that did not pin the global's value
     across the whole scan could not say that all the children got the SAME new
     parent.  Owning any fraction rules out a concurrent writer and pins it.

   * NOTHING IS SAID ABOUT wakeup's EFFECT, because wakeup has none that is
     visible: [SchedCtx.proc_pub] quantifies the state a SLEEPING->RUNNABLE
     move changes, so wakeup's own postcondition is empty and reparent inherits
     that silence.  [procs_inv] is persistent, so passing it costs nothing.

   * [b]-GENERIC, hence a [wp_next]: reparent CALLS wakeup, which may take a
     trap and resume the thread on a different hart.  A caller that holds
     wait_lock instantiates at [b = false] and the binder collapses. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile.
Require Import RiscvExtras.
Require Import FdSlots.
Require Import ProcGeom.
Require Import WaitInv.
Require Import InstrBytes KernelText.
Require Import LockRank.
Require Import CalleeSaved.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import SchedCtx.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

(* six frame slots of reparent's own, plus wakeup's 18. *)
Notation K_reparent := (24%nat) (only parsing).
Definition wp_reparent_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
     (m : regfile) (γs : list gname) (pme ip : mword 64)
    (ps : list (mword 64)) (dqi : dfrac) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.reparent in
  let pv : mword 64 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let rettgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_reparent <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  length γs = NPROC ->
  (* wakeup's myproc/acquire push_off keeps the transient noff increment in range *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (* WAKEUP'S ORDER PREMISE, INHERITED.  reparent acquires nothing itself, but
     it calls wakeup() once per reparented child and wakeup acquires each
     pp->lock, so the bound is exactly [SpecWakeup]'s and reparent is a pure
     conduit for it.  Satisfiable at reparent's only call site: kexit enters
     holding wait_lock (rank 10) and "proc" is rank 11, so the caller's set is
     [{["wait_lock"]}] and 10 < 11.  reparent is BALANCED -- it takes
     no lock of its own and wakeup's own contract is balanced -- so [lks] is
     unchanged end to end and this premise is not re-established anywhere. *)
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m K b pme -∗
  cpu_own lvl eb pme b lks -∗
  kernel_text -∗ pc_is pcE -∗
 procs_inv γs -∗
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
  parents_own ps -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ Mf : regfile,
      ⌜ callee_saved m Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sie_cap_gpr KT1 Mf K b pme -∗
      cpu_own lvl eb pme b lks -∗
      kernel_text -∗ pc_is rettgt -∗
      (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
      parents_own (rp_map pv ip ps) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type REPARENT.
  Parameter wp_reparent_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
       (m : regfile) (γs : list gname) (pme ip : mword 64)
      (ps : list (mword 64)) (dqi : dfrac) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string),
      wp_reparent_sconf_body m γs pme ip ps dqi lvl K eb b lks.
End REPARENT.
