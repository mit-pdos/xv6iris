(* ProtoSchedsInv.v -- the WORKED COMMENTARY on the parked-scheduler
   invariant, now that the mechanism it prototyped has LANDED in
   [SchedCtx.v].  See claude-notes/projects/explicit-cpuid.md, section
   "THE ANSWER, PROTOTYPED".

   Five proofs (sleep / yield / bread / bwrite / acquiresleep) were blocked
   because they carried [sched_vc] -- hart h's parked scheduler context,
   which owns fourteen EXCLUSIVE words of hart h's struct cpu -- across
   interrupts-enabled instructions, where [wp_next] hands back an
   unconstrained hart.  It was the ONLY stranded resource.

   THE HYPOTHESIS THIS FILE VALIDATED: the difficulty came entirely from the
   record being THREAD-OWNED, so a migration had to carry it.  Making it
   GLOBAL instead -- a [scheds_inv] sibling to [procs_inv], holding per hart
   either "this hart's scheduler is running" or "it is parked with record R"
   -- makes it hart-free from the thread's point of view, which is exactly
   the property that crosses for free.  A thread that wants to swtch opens
   the invariant at whatever hart it is NOW on and takes out THAT hart's
   record.

   THE DEFINITIONS NOW LIVE IN THEIR REAL HOMES, and this file only points
   at them, so that it cannot rot the way [ProtoCpuid.v] did:
     - [ProcGeom.cpu_proc_half] / [park_own] / [park_hlf] / [park_full] /
       [park_at] -- the shared half of [cpus[h].proc] and the per-PROC park
       receipt.  The receipt's ghost name is CANONICAL
       ([RiscvPtsto.park_name]), the same device [sie_name] uses and for the
       same reason: it is named inside [proc_lock_res], hence inside
       [procs_inv], so a [γk] parameter would have to be threaded through
       every file that mentions [procs_inv].
     - [SchedCtx.sched_slot] / [scheds_inv] and the six moves
       [scheds_take] / [scheds_put] / [scheds_dispatch] / [scheds_reclaim] /
       [scheds_idle] / [scheds_alloc], plus the two witnesses
       [cpu_own_full_is_vacuous] (why halving [IntrDefs.cpu_cells]' proc
       field is MANDATORY rather than cosmetic) and [scheds_put_take] (the
       round trip, hence the non-vacuity of both directions).

   IT IS IN _CoqProject ON PURPOSE.  ProtoCpuid.v, this refactor's other
   prototype, was left out and duly rotted: by the time anyone read the
   design notes that pointed at it, it no longer typechecked against the
   interface it documented.  A prototype that is not built is not
   documentation. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list finite bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom.
Require Import FdSlots.
Require Import SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import RegFile InstrBytes.
Require Import CalleeSaved KernelText.
Require Import SpecPanic.
Require Import Riscv.riscv_extras.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* THE PAYOFF: what a parking contract's body becomes.                     *)
(*                                                                        *)
(* Diff against the pre-mechanism [SpecYield.wp_yield_sconf_body]:         *)
(*   -  ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj      (premise)   DELETED   *)
(*   -  ▷ sched_vc Φ γs (a_cpu_ctx cid_word) pj      (post)      DELETED   *)
(*   +  scheds_inv Φ γs                               persistent, hart-free *)
(*   +  park_hlf j true                               hart-free token       *)
(* The two additions are exactly as transportable as [procs_inv] and       *)
(* [p_pid] already are, so [wp_next]'s ∀CID lambda carries them for free.  *)
(* ====================================================================== *)
Section Payoff.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition wp_yield_sconf_body'
      (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
    let pcE : mword 64 := mword_of_int KernelSyms.yield in
    let pj := proc_addr j in
    let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    eb = true ->
    (20 <= av)%nat ->
    sie_cap_gpr m av b pj -∗
    cpu_own 0 eb pj C b -∗
    kernel_text -∗ pc_is pcE -∗
    procs_inv Φ γs -∗
    scheds_inv Φ γs -∗                          (* NEW: persistent, hart-free *)
    panic_wp_any -∗
    park_hlf j true -∗                          (* NEW: hart-free receipt *)
    wp_next b pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf av b pj -∗
        cpu_own 0 eb pj C b -∗
        pc_is ret_tgt -∗
        park_hlf j true -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
End Payoff.
