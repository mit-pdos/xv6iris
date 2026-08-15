(* HartMPmp.v -- the SPAN twin of [exec_pmpCheck_machine_unlocked_ifetch4]:
   with every PMP entry unlocked and pmpcfg pinned, every interfered span
   chain through a 4-byte instruction-fetch PMP check at a 4-aligned
   address factors through its allow ([None]) continuation.

   Segment 2's second sub-characterization (worklist 0b): the check reads
   pmpcfg (D-pinned, twice per entry) and pmpaddr (unownable, once per
   entry, ∀-peeled; TOR comparisons on those values are decided per case
   and every case allows at Machine-unlocked, so the binders die).  The
   exec-side anchor and the map of the per-entry induction is
   [RiscvTryStep.exec_pmpCheck_machine_unlocked] and its ifetch4
   corollary (RiscvFetchExec.v). *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec
        HartLift HartRegNode HartSpan HartSpanChar.
Local Open Scope Z_scope.

Lemma mpmp_span_char_ifetch4 (D Drw : gset register)
    (pcfg : type_of_register pmpcfg_n)
    (addr : SailStdpp.Values.mword 64)
    (K : option ExceptionType -> M unit)
    (rs rs0 : regstate) (l : M unit * regstate) :
  (pmpcfg_n : register) ∈ D ->
  (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  register_lookup pmpcfg_n rs = pcfg ->
  reg_agree_on D rs0 rs ->
  hspan D Drw
    (Interface.iMon_bind
       (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) Machine) K, rs0) l ->
  hspan_stops Drw l.1 = true ->
  exists rs1, reg_agree_on D rs1 rs /\ hspan D Drw (K None, rs1) l.
Proof.
  (* TODO(agent): mirror [exec_pmpCheck_machine_unlocked]'s induction on
     span chains: the loop over the 64 entries is a concrete monad spine;
     per entry, peel the two pmpcfg reads (D-pinned; per-entry facts from
     the unlocked premise via [vec_access_dec]) and the pmpaddr read
     (∀-peel), case the entry's address-match outcome (every case allows at
     Machine with the entry unlocked -- the same case analysis the exec
     proof's per-entry lemma performs), and continue.  Factor the per-entry
     step as a local lemma and induct, exactly as the exec proof does --
     do NOT unroll 64 entries by hand.  The alignment premise enters where
     the exec corollary used it (the one-grain fit).  Spine reduction: the
     seg1 incantation (whitelisted cbn + rewrite !hregread_resume_red +
     fact rewrites); vm only on closed never-consumed facts. *)
Admitted.
