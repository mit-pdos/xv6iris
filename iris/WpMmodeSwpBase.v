(* WpMmodeSwpBase.v -- the [swp] counterpart of WpMmodeLeafBase.

   WpMmodeLeafBase holds the pure [exec (execute i) s = Some (RETIRE_SUCCESS,
   s')] catalogue the whole-instruction stack used.  Under per-node stepping a
   leaf discharges [swp (execute i) Phi] instead, and this file holds those
   twins.  It needs a [Sigma], which is why it is not simply appended to
   WpMmodeLeafBase (that file is entirely pure). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartSpan
        HartRegNode RegFile WpGpr.
Require Import ColdBoot.
Local Open Scope Z_scope.

(* collapse the closed [Z.eqb] tests of the model's rX/wX cascades *)
Local Ltac zt :=
  repeat match goal with
  | |- context [ if ?b then _ else _ ] =>
      assert_fails (is_var b);
      let x := eval vm_compute in b in
      lazymatch x with true => change b with true
                     | false => change b with false end
  end.

(* ====================================================================== *)
(* THE M-MODE WRAPPER'S FOOTPRINT.                                         *)
(*                                                                        *)
(* [mm_Drw] is SEVEN cells, not thirty-eight: the GPRs are not here (see   *)
(* the header -- they ride in the caller's [R] and are reached by          *)
(* [swp_rX_bits]/[swp_wX_bits]), and neither is the clock CONFIG, because  *)
(* [HartMCycle.tick_clock_hvalE] ∀-peels every read the tick makes and     *)
(* needs only the three clock CELLS owned.                                 *)
(*                                                                        *)
(* [mm_Dro] is what the wrapper, the fetch and the dispatch actually pin.  *)
(* EIGHT of the twelve are persistent: six are [hw_config]'s frozen cells,  *)
(* and mcountinhibit / minstretcfg are frozen too but arrive from           *)
(* [MinstretInv.minstret_res] -- they are read only by                      *)
(* [should_inc_minstret], so they live with the rest of the minstret facts  *)
(* rather than in the shared config bundle.  The four fractional ones are   *)
(* the genuinely M-mode-specific config, which is what lets [mmode_config]  *)
(* keep its [split]/[combine] (47 sites depend on it) -- the EXCLUSIVE      *)
(* cells go in [pc_is] instead.                                            *)
(* ====================================================================== *)

Definition mm_Drw : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register);
     (R_bitvector_64 minstret : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

Definition mm_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register);
     (hart_state : register); (pmpcfg_n : register);
     (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register);
     (misa : register); (mseccfg : register); (pma_regions : register);
     (htif_tohost_base : register); (elp : register);
     (senvcfg : register) ]}.

Lemma mm_disj : mm_Drw ## mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.

(* the wrapper's own memberships, precomputed (set_solver in an empty
   context is 7 ms; inside a leaf proof with towers in scope it is not) *)
Lemma mm_w_PC : (R_bitvector_64 PC : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_nPC : (R_bitvector_64 nextPC : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_ms : (R_bitvector_64 minstret : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_mi : (R_bool minstret_increment : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_cy : (R_bitvector_64 mcycle : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_ti : (R_bitvector_64 mtime : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.
Lemma mm_w_ip : (R_bitvector_64 mip : register) ∈ mm_Drw.
Proof. rewrite /mm_Drw. set_solver. Qed.

Lemma mm_in_PC : (R_bitvector_64 PC : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_nPC : (R_bitvector_64 nextPC : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_ms : (R_bitvector_64 minstret : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_mi : (R_bool minstret_increment : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_priv : (cur_privilege : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_mst : (mstatus : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_hart : (hart_state : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_pcfg : (pmpcfg_n : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_mc : (R_bitvector_32 mcountinhibit : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_micfg : (R_bitvector_64 minstretcfg : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_misa : (misa : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_sec : (mseccfg : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_pma : (pma_regions : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_htif : (htif_tohost_base : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.
Lemma mm_in_elp : (elp : register) ∈ mm_Drw ∪ mm_Dro.
Proof. rewrite /mm_Drw /mm_Dro. set_solver. Qed.

(* ====================================================================== *)
(* THE ANCHOR TOWER.  A register file is a total function, so a rule that   *)
(* wants to name one has to build it; every cell outside [mm_Drw ∪ mm_Dro]  *)
(* is irrelevant (no frame mentions it), so the base is the cold file and   *)
(* only the footprint's nineteen cells are set.  Three of them are PINNED   *)
(* rather than parameters: this is the M-mode wrapper, so cur_privilege is  *)
(* Machine, hart_state is ACTIVE, and htif_tohost_base is None.            *)
(* ====================================================================== *)

Require Import RiscvFetchExec WpMmodeLeafBase HartMFrame InstrBytes WpInstr KptPt.

Section swpbase.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* THE WHOLE RTYPE BINOP FAMILY, in one lemma.                          *)
  (*                                                                      *)
  (* The model's [execute_RTYPE] is the same three nodes for every [rop] --  *)
  (* read rs1, read rs2, write rd -- and differs only in which function     *)
  (* combines the operands.  Taking that reduction as a HYPOTHESIS (each     *)
  (* instance discharges it by [eq_refl]) makes the ten ops ten one-line     *)
  (* corollaries instead of ten proofs.  Mirrors the exec-side split         *)
  (* [exec_execute_RTYPE_OR] / [_AND] / ... but without repeating the peel.  *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_execute_RTYPE_bin (rs2 rs1 rd : SailStdpp.Values.mword 5)
      (m : regfile) (op : rop)
      (f : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 ->
           SailStdpp.Values.mword 64) :
    execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) op
    = Defs.bind
        (Defs.bind (rX_bits (Regidx rs1))
           (fun a => Defs.bind (rX_bits (Regidx rs2))
                       (fun b => returnM (f a b))))
        (fun v => Defs.bind0 (wX_bits (Regidx rd) v)
                    (returnM RETIRE_SUCCESS)) ->
    uint rd <> 0 ->
    gen_cert -∗ gpr_file m -∗
    swp (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) op)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
         gpr_file (<[Regidx rd :=
            regval_into_reg (f (m !!! Regidx rs1) (m !!! Regidx rs2))]> m)).
  Proof.
    intros Hred Hrd. iIntros "#Hcert Hf". rewrite Hred.
    iApply (swp_bind_use _ _
              (fun v => ⌜v = f (m !!! Regidx rs1) (m !!! Regidx rs2)⌝ ∗
                        gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[Hf] [-]").
      { iApply (swp_rX_file rs1 m with "Hcert Hf"). }
      iIntros (v1) "[-> Hf]".
      iApply (swp_bind_use (rX_bits (Regidx rs2)) _ _ _ with "[Hf] [-]").
      { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
      iIntros (v2) "[-> Hf]".
      iApply swp_ret. by iFrame. }
    iIntros (v) "[-> Hf]".
    iApply (swp_bind0_use _ _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m _ Hrd with "Hcert Hf"). }
    iIntros (u) "Hf".
    iApply swp_ret. by iFrame.
  Qed.

  (* the three ops the M-mode RTYPE leaves actually name *)
  Definition swp_execute_RTYPE_OR (rs2 rs1 rd : SailStdpp.Values.mword 5)
      (m : regfile) := swp_execute_RTYPE_bin rs2 rs1 rd m OR or_vec eq_refl.
  Definition swp_execute_RTYPE_AND (rs2 rs1 rd : SailStdpp.Values.mword 5)
      (m : regfile) := swp_execute_RTYPE_bin rs2 rs1 rd m AND and_vec eq_refl.
  Definition swp_execute_RTYPE_ADD (rs2 rs1 rd : SailStdpp.Values.mword 5)
      (m : regfile) := swp_execute_RTYPE_bin rs2 rs1 rd m ADD add_vec eq_refl.

End swpbase.
