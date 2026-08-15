(* HartMDispatch.v -- the SPAN twin of [dispatchInterrupt_none_from_regs]:
   during M-mode kernel execution (misa.S set, mstatus.MIE clear), every
   interfered span chain through the interrupt dispatch factors through its
   [None] continuation.

   This is segment 2's first sub-characterization (worklist 0b): the
   dispatch reads mideleg / mip / sig_meip / sig_seip / mie -- all
   unownable, all ∀-peeled here ONCE, so no caller ever sees them.  The
   exec-side anchor is [InstrBytes.dispatchInterrupt_none_from_regs] built
   on [exec_getPendingSet_machine_none] (RiscvTryStep/ExecCommon); this
   lemma replays that argument on span chains with the peel kit. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep HartLift
        HartRegNode HartSpan HartSpanChar.
Local Open Scope Z_scope.

Lemma mdispatch_span_char (D Drw : gset register)
    (misa0 mstatus0 : SailStdpp.Values.mword 64)
    (K : option (InterruptType * Privilege)%type -> M unit)
    (rs rs0 : regstate) (l : M unit * regstate) :
  (misa : register) ∈ D ->
  (mstatus : register) ∈ D ->
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  eq_vec (_get_Mstatus_MIE mstatus0) (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  register_lookup misa rs = misa0 ->
  register_lookup mstatus rs = mstatus0 ->
  reg_agree_on D rs0 rs ->
  hspan D Drw (Interface.iMon_bind (dispatchInterrupt Machine) K, rs0) l ->
  hspan_stops Drw l.1 = true ->
  exists rs1, reg_agree_on D rs1 rs /\ hspan D Drw (K None, rs1) l.
Proof.
  (* TODO(agent): the peel chain through [dispatchInterrupt Machine]'s
     nodes.  The read order (machine-traced): misa, mideleg, mip, sig_meip,
     misa, sig_seip, mie, mie, mstatus -- misa/mstatus reads are D-pinned
     (peel with [hspani_read_D_inv] + the premise rewrites), the other five
     are ∀-peeled ([hspani_read_any_inv]; their binders die when the
     MIE=0 rewrite collapses the enable computation).  Use the seg1
     incantation (HartMCycle.mseg1_read3_at_local's comment) for spine
     reduction between peels, and the exec proof
     ([exec_getPendingSet_machine_none], [exec_currentlyEnabled_S]) as the
     map of the branch structure -- the same bit-rewrites that closed the
     exec proof close the span branches.  Finish: the landing chain from
     the [K None] node is the ∃-witness (the chain remainder), with the
     accumulated agreement. *)
Admitted.
