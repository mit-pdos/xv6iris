(* HartMFetch.v -- SEGMENT 2 of the M-mode cycle: from the post-chop monad
   [mseg2_start] to the instruction-fetch MemRead, assembled from the two
   sub-characterizations (HartMDispatch, HartMPmp) and the peel kit.

   THE LEAF-ATTACHMENT CONCLUSION (worklist 0d, the resolution): the
   landing is pinned to an UNEVALUATED WALKER APPLICATION,
       l.1 = (hrun_any_f 200 (register_set pmpcfg_n pmpcfg_boot rs)
                mseg2_start).2
   -- the unfootprinted walk at the caller's own pin file [rs], with ONE
   register forced concrete: pmpcfg is replaced by the all-OFF boot table,
   because at a merely-unlocked symbolic [pcfg] the walk's per-entry
   branches are stuck terms (the CHAIN's landing is still characterized at
   the caller's real pcfg -- the equality holds because the post-fetch
   continuation retains nothing the PMP loop read, which is exactly what
   the equality's proof verifies).  A leaf's functional cursors then start
   at [hread_resume w <that application>]: parametric in [pc] (and the
   other pins) through [rs], spelled, F8-safe, and reducible by the
   incantation + the same premise rewrites. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec
        HartLift HartRegNode HartSpan HartSpanChar HartMCycle
        HartMDispatch HartMPmp.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the unfootprinted functional walker (the collector's stepper, promoted;  *)
(* HartPilot carries a probe-local copy -- consolidation there is owed)     *)
(* ---------------------------------------------------------------------- *)

Definition hsil_node_f (rs : regstate) (m : M unit)
    : option (regstate * M unit) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (regstate * M unit) with
       | Interface.RegRead r _ => fun k => Some (rs, k (register_lookup r rs))
       | Interface.RegWrite r _ v => fun k => Some (register_set r v rs, k tt)
       | Interface.InstrAnnounce _   => fun k => Some (rs, k tt)
       | Interface.BranchAnnounce _ _=> fun k => Some (rs, k tt)
       | Interface.Barrier _         => fun k => Some (rs, k tt)
       | Interface.CacheOp _         => fun k => Some (rs, k tt)
       | Interface.TlbOp _           => fun k => Some (rs, k tt)
       | Interface.TakeException _   => fun k => Some (rs, k tt)
       | Interface.ReturnException _ => fun k => Some (rs, k tt)
       | Interface.TranslationStart _=> fun k => Some (rs, k tt)
       | Interface.TranslationEnd _  => fun k => Some (rs, k tt)
       | Interface.CycleCount        => fun k => Some (rs, k tt)
       | Interface.Message _         => fun k => Some (rs, k tt)
       | Interface.GetCycleCount     => fun k => Some (rs, k 0%Z)
       | _ => fun _ => None
       end) k
  end.

Fixpoint hrun_any_f (n : nat) (rs : regstate) (m : M unit)
    : regstate * M unit :=
  match n with
  | 0%nat => (rs, m)
  | S n' => match hsil_node_f rs m with
            | Some (rs', m') => hrun_any_f n' rs' m'
            | None => (rs, m)
            end
  end.

(* ---------------------------------------------------------------------- *)
(* the fetch request, as the model builds it (adjust the BODY if the       *)
(* model spells a field differently -- the pilot's concrete request is     *)
(* the reference)                                                          *)
(* ---------------------------------------------------------------------- *)
Definition mfetch_req (pc : SailStdpp.Values.mword 64)
    : Interface.ReadReq.t 4 :=
  {| Interface.ReadReq.pa := pc;
     Interface.ReadReq.access_kind :=
       SailStdpp.ConcurrencyInterfaceTypes.AK_explicit
         {| SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety
              := SailStdpp.ConcurrencyInterfaceTypes.AV_plain;
            SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_strength
              := SailStdpp.ConcurrencyInterfaceTypes.AS_normal |};
     Interface.ReadReq.va := None;
     Interface.ReadReq.translation := tt;
     Interface.ReadReq.tag := false |}.

(* ---------------------------------------------------------------------- *)
(* the segment characterization                                            *)
(* ---------------------------------------------------------------------- *)
Lemma mfetch_char (D Drw : gset register) (rs rs0 : regstate)
    (l : M unit * regstate)
    (pc misa0 mstatus0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region) :
  (hart_state : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (misa : register) ∈ D ->
  (mstatus : register) ∈ D ->
  (pma_regions : register) ∈ D ->
  (pmpcfg_n : register) ∈ D ->
  (htif_tohost_base : register) ∈ D ->
  (R_bitvector_64 PC : register) ∈ D ->
  eq_vec (_get_Misa_S misa0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  eq_vec (_get_Mstatus_MIE mstatus0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  eq_vec (_get_Mstatus_MPRV mstatus0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  register_lookup hart_state rs = HART_ACTIVE tt ->
  register_lookup cur_privilege rs = Machine ->
  register_lookup misa rs = misa0 ->
  register_lookup mstatus rs = mstatus0 ->
  register_lookup pma_regions rs = pmar0 ->
  register_lookup pmpcfg_n rs = pcfg ->
  register_lookup htif_tohost_base rs = None ->
  register_lookup (R_bitvector_64 PC) rs = pc ->
  (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  is_aligned_paddr (Physaddr pc) 4 = true ->
  pma_allows_ram pmar0 ->
  addr_is_ram pc ->
  reg_agree_on D rs0 rs ->
  hspan D Drw (mseg2_start, rs0) l ->
  hspan_stops Drw l.1 = true ->
  l.1 = (hrun_any_f 200 (register_set pmpcfg_n pmpcfg_boot rs)
           mseg2_start).2
  /\ hread_req_at 4 l.1 = Some (mfetch_req pc)
  /\ reg_agree_on D l.2 rs.
Proof.
  (* TODO(agent): the assembly.  Chain side: peel hart_state (D-pinned;
     the HART_ACTIVE match reduces), reduce to the dispatch bind seam and
     apply [mdispatch_span_char] (its premises are this lemma's, its
     agreement from the composed peels); continue from [K None]: peel the
     PC reads (D-pinned to [pc]), resolve the alignment branch with the
     vaddr premise, the effective-privilege reads (mstatus/cur_privilege
     pins + the MPRV bit fact), the pma_regions read (D-pinned) and the
     PURE pma check by destructing [pma_allows_ram] at the fetch address
     (the ∃-region equation rewrites the stuck [matching_pma_region]
     scrutinee; [pma_class_access] for the RAM class at a 4-byte fetch
     should follow from [addr_is_ram pc] + alignment -- check
     RiscvFetchExec's definitions and adjust the PREMISE SPELLING of the
     last two hypotheses if the class-access shape differs, reporting it);
     then the pmp bind seam and [mpmp_span_char_ifetch4]; from its
     [K None]: the htif read (D-pinned to None; the tohost branch
     reduces), landing on the MemRead.  [hspan_stop_refl] ends the chain.
     Walk side (conclusion 1): reduce
     [(hrun_any_f 200 (register_set pmpcfg_n pmpcfg_boot rs) mseg2_start)]
     with the same incantation: reads answer [register_lookup r (register_set
     pmpcfg_n pmpcfg_boot rs)] -- rewrite each through
     [irrelevant_register_set] (r ≠ pmpcfg_n) to the premise pins, and the
     pmp entries at [register_lookup pmpcfg_n (…) = pmpcfg_boot]
     ([register_lookup_set]) reduce CONCRETELY (all OFF -- every entry's
     match is NoMatch by computation, [pmpcfg_boot_entry] in RiscvLang
     helps).  The two reduced landings must be the SAME term; conclude by
     reflexivity.  Then conclusion 2 computes on it and conclusion 3 is
     the composed agreement.
     Budget checkpoint: if the walk-side reduction exceeds ~60 s of tactic
     time, STOP and report rather than grinding. *)
Admitted.
