From Stdlib Require Import Eqdep_dec ZArith Lia FunctionalExtensionality.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr.
Local Open Scope Z_scope.

(* [exec_if_false_g] (from WpEntry) drives the [write_CSR] CSR-dispatch walks
   below at the goal head — see its comment / the README "Build-perf note". *)

(* ====================================================================== *)
(* csrw csr,rs1 (= csrrw x0,csr,rs1): csr := legalize_csr(cur,rs1); no GPR.*)
(* Reusable framework (doCSR write path) + pure-legalize CSRs as templates.*)
(* ====================================================================== *)

(* wX to x0 (zreg) is a no-op. *)
Lemma exec_wX_bits_zreg (v : mword 64) s :
  exec (wX_bits zreg v) s = Some (tt, s).
Proof.
  unfold zreg.
  rewrite (exec_wX_bits_gpr (zero_extend' 5 ('b"00")) v s).
  replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* The doCSR write path, parameterised by the per-CSR write_CSR result. *)
Lemma exec_doCSR_csrw (csr : mword 12) (v : mword 64) (s s' : mstate) (cfinal : mword 64) :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr Machine CSRWrite) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Machine CSRWrite = true ->
  eq_vec csr (Ox"344") = false ->
  eq_vec csr (Ox"144") = false ->
  exec (write_CSR csr v) s = Some (Ok cfinal, s') ->
  exec (csr_id_write_callback csr cfinal) s' = Some (tt, s') ->
  exec (doCSR csr v zreg CSRRW CSRWrite) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hpriv Hchk Hext H344 H144 Hwr Hcb.
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hext. cbn match.
  replace (if generic_neq CSRWrite CSRWrite then read_CSR csr else returnM (zeros' 64))
    with (returnM (zeros' 64) : M (mword 64)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (zeros' 64) s)).
  rewrite H344 H144. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (zeros' 64) s)).
  replace (generic_eq CSRWrite CSRRead) with false by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ Hwr). cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_zreg (zeros' 64) s')).
  rewrite (exec_bind0_Some _ _ _ _ _ Hcb).
  apply exec_returnM.
Qed.

(* execute_CSRReg for csrw (rd=x0=zreg, op=CSRRW): reads rs1 (generic), then doCSR write. *)
Lemma exec_execute_csrw_gpr (csr : mword 12) (rs1 : mword 5) (s s' : mstate) (cfinal : mword 64) :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr Machine CSRWrite) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Machine CSRWrite = true ->
  eq_vec csr (Ox"344") = false ->
  eq_vec csr (Ox"144") = false ->
  exec (write_CSR csr (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))) s
    = Some (Ok cfinal, s') ->
  exec (csr_id_write_callback csr cfinal) s' = Some (tt, s') ->
  exec (execute_CSRReg csr (Regidx rs1) zreg CSRRW) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hrs1 Hpriv Hchk Hext H344 H144 Hwr Hcb.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRW (generic_eq zreg zreg) (generic_eq (Regidx rs1) zreg))
    with CSRWrite by (replace (generic_eq zreg zreg) with true by reflexivity; reflexivity).
  assert (Hrv : exec (rX_bits (Regidx rs1)) s
                = Some (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs), s)).
  { rewrite (exec_rX_bits_gpr rs1 s).
    replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
    reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ Hrv).
  apply (exec_doCSR_csrw csr _ s s' cfinal); assumption.
Qed.

Definition csr_mcounteren : mword 12 := mword_of_int 0x306.

Lemma exec_write_CSR_mcounteren (v : mword 64) s :
  exec (write_CSR csr_mcounteren v) s
    = Some (Ok (zero_extend' 64 (legalize_mcounteren (register_lookup mcounteren s.(sregs)) v)),
            set_reg s mcounteren (legalize_mcounteren (register_lookup mcounteren s.(sregs)) v)).
Proof.
  unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  (* reached the 0x306 clause *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mcounteren _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_mcounteren (d : mword 64) s :
  exec (csr_id_write_callback csr_mcounteren d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_mcounteren d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_mcounteren (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr_mcounteren Machine CSRWrite) s = Some (CSR_Check_OK tt, s) ->
  exec (execute_CSRReg csr_mcounteren (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mcounteren
              (legalize_mcounteren (register_lookup mcounteren s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv Hchk.
  apply (exec_execute_csrw_gpr csr_mcounteren rs1 s _
           (zero_extend' 64 (legalize_mcounteren (register_lookup mcounteren s.(sregs))
              (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  - exact Hrs1.
  - exact Hpriv.
  - exact Hchk.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_mcounteren.
  - apply exec_csr_id_write_callback_mcounteren.
Qed.

(* ---- check_CSR reduction for Machine+CSRWrite (engine for the hypothesis) ---- *)
Lemma exec_check_CSR_csrw (csr : mword 12) s :
  exec (check_CSR_priv csr Machine) s = Some (true, s) ->
  check_CSR_access csr CSRWrite = true ->
  exec (is_CSR_accessible csr Machine CSRWrite) s = Some (true, s) ->
  exec (stateen_allows_CSR_access csr Machine CSRWrite) s = Some (true, s) ->
  exec (check_CSR csr Machine CSRWrite) s = Some (true, s).
Proof.
  intros Hpriv Hca Hacc Hst. unfold check_CSR.
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hpriv). cbn match.
  assert (HB : exec (returnM (check_CSR_access csr CSRWrite) : M bool) s = Some (true, s))
    by (rewrite exec_returnm; rewrite Hca; reflexivity).
  rewrite (exec_and_boolM_Some _ _ _ _ _ HB). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hacc). cbn match.
  exact Hst.
Qed.

Lemma exec_check_CSR_result_csrw (csr : mword 12) s :
  exec (check_CSR csr Machine CSRWrite) s = Some (true, s) ->
  exec (check_CSR_result csr Machine CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro Hcc. unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ Hcc). cbn match. apply exec_returnm.
Qed.

(* pure-CSR (is_CSR_accessible = returnM true): mstatus 0x300, mepc 0x341 *)
Lemma exec_check_CSR_result_csrw_pure (csr : mword 12) s :
  exec (check_CSR_priv csr Machine) s = Some (true, s) ->
  check_CSR_access csr CSRWrite = true ->
  exec (is_CSR_accessible csr Machine CSRWrite) s = Some (true, s) ->
  exec (stateen_allows_CSR_access csr Machine CSRWrite) s = Some (true, s) ->
  exec (check_CSR_result csr Machine CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intros. apply exec_check_CSR_result_csrw. apply exec_check_CSR_csrw; assumption.
Qed.

(* Ext_S-gated CSRs: medeleg 0x302, mideleg 0x303, sie 0x104, satp 0x180 *)
Lemma exec_check_CSR_result_csrw_S (csr : mword 12) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_priv csr Machine) s = Some (true, s) ->
  check_CSR_access csr CSRWrite = true ->
  is_CSR_accessible csr Machine CSRWrite = currentlyEnabled Ext_S ->
  exec (stateen_allows_CSR_access csr Machine CSRWrite) s = Some (true, s) ->
  exec (check_CSR_result csr Machine CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intros HS Hpriv Hca Hacceq Hst.
  apply exec_check_CSR_result_csrw. apply exec_check_CSR_csrw; try assumption.
  rewrite Hacceq. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
Qed.

(* ---- Ext_U gated CSRs: menvcfg 0x30a, mcounteren 0x306 ---- *)
Lemma exec_hartSupports_U s : exec (hartSupports Ext_U) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_U) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_U s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_U) s = Some (true, s).
Proof.
  intro HU. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_U) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_U s)). cbn match.
  match goal with |- context[Defs.and_boolM ?l _] =>
    assert (Hu : exec l s = Some (true, s)) by
      (rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s));
       rewrite (exec_returnM _ s); rewrite HU; reflexivity);
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hu)
  end. cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_check_CSR_result_csrw_U (csr : mword 12) s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_priv csr Machine) s = Some (true, s) ->
  check_CSR_access csr CSRWrite = true ->
  is_CSR_accessible csr Machine CSRWrite = currentlyEnabled Ext_U ->
  exec (stateen_allows_CSR_access csr Machine CSRWrite) s = Some (true, s) ->
  exec (check_CSR_result csr Machine CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intros HU Hpriv Hca Hacceq Hst.
  apply exec_check_CSR_result_csrw. apply exec_check_CSR_csrw; try assumption.
  rewrite Hacceq. apply (exec_currentlyEnabled_U s HU).
Qed.

(* ---- medeleg 0x302 (Ext_S, pure legalize) end-to-end execute ---- *)
Definition csr_medeleg : mword 12 := mword_of_int 0x302.

Lemma exec_write_CSR_medeleg (v : mword 64) s :
  exec (write_CSR csr_medeleg v) s
    = Some (Ok (legalize_medeleg (register_lookup medeleg s.(sregs)) v),
            set_reg s medeleg (legalize_medeleg (register_lookup medeleg s.(sregs)) v)).
Proof.
  unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg medeleg s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg medeleg _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg medeleg _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_medeleg (d : mword 64) s :
  exec (csr_id_write_callback csr_medeleg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_medeleg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_medeleg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_medeleg (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s medeleg
              (legalize_medeleg (register_lookup medeleg s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS.
  apply (exec_execute_csrw_gpr csr_medeleg rs1 s _
           (legalize_medeleg (register_lookup medeleg s.(sregs))
              (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_S csr_medeleg s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_medeleg.
  - apply exec_csr_id_write_callback_medeleg.
Qed.

(* discharge mcounteren's check_CSR via Ext_U for a fully-closed execute *)
Lemma exec_execute_csrw_mcounteren_full (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mcounteren (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mcounteren
              (legalize_mcounteren (register_lookup mcounteren s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HU. apply exec_execute_csrw_mcounteren; try assumption.
  apply (exec_check_CSR_result_csrw_U csr_mcounteren s HU);
    [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity ].
Qed.

(* ---- forward_exec for csrw medeleg (exec riscv_step, generic rs1) ---- *)
Section ForwardCsrwMedeleg.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW), s0).

  Definition sAcw : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pccw : mstate := set_reg sAcw nextPC (add_vec_int pc 4).
  Definition sXcw : mstate :=
    set_reg s_pccw medeleg
      (legalize_medeleg (register_lookup medeleg s_pccw.(sregs))
         (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pccw.(sregs))).
  Definition sTcw : mstate := set_reg sXcw PC (register_lookup nextPC sXcw.(sregs)).
  Definition sFcw : mstate :=
    if b then set_reg sTcw minstret (add_vec_int (register_lookup minstret sTcw.(sregs)) 1)
         else sTcw.

  Lemma forward_exec_csrw_medeleg :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFcw).
  Proof using All.
    intros Lpc Lpriv Lhs LmIE Lelp LS.
    assert (LpcA : register_lookup PC sAcw.(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege sAcw.(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state sAcw.(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAcw.(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAcw.(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp sAcw.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAcw = Some (None, sAcw)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAcw _ (exec_currentlyEnabled_S sAcw) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAcw = Some (F_Base w, sAcw)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAcw = Some (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW), sAcw))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege s_pccw.(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (LSC : eq_vec (_get_Misa_S (register_lookup misa s_pccw.(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LS. }
    assert (HexecC : exec (execute (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW))) s_pccw
              = Some (RETIRE_SUCCESS, sXcw)).
    { change (execute (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_medeleg (Regidx rs1) zreg CSRRW).
      unfold sXcw. exact (exec_execute_csrw_medeleg rs1 s_pccw Hrs1 LprivC LSC). }
    assert (Hha : exec (run_hart_active 0) sAcw
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw)).
    { exact (exec_hart_active_progress sAcw sAcw sXcw sAcw w
               (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s sXcw w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwMedeleg.

(* ---- clean-form post-state for csrw medeleg (for the Iris WP layer) ---- *)
Lemma medeleg_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup medeleg s.(sregs) = v ->
  register_lookup medeleg (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.
Ltac reg_ne_c := solve [ vm_compute; reflexivity
                       | (unfold gpr_of_Z; repeat case_match; reflexivity) ].
Lemma gpr_s_pccw (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (v : mword 64) :
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = v ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|reg_ne_c]). exact H.
Qed.

Ltac tmiw := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Section CleanCsrwMedeleg.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         medeleg
         (legalize_medeleg (register_lookup medeleg (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw : mstate :=
    if b then set_reg base_upd_cw minstret (add_vec_int mst0 1) else base_upd_cw.
  Lemma sFcw_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw s pc b rs1 = sFccw.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw s pc b rs1 = base_upd_cw).
    { unfold sTcw. rewrite Enpc. unfold sXcw, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw, s_pccw, sAcw. reflexivity. }
    unfold sFcw, sFccw. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwMedeleg.

Section WpCsrwMedeleg.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_medeleg_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 medeleg0 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ medeleg ↦ᵣ medeleg0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        medeleg ↦ᵣ legalize_medeleg medeleg0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmde Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmde")   as %Lmde.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmdv : register_lookup medeleg (s_pccw s pc b1).(sregs) = medeleg0)
      by (apply medeleg_s_pccw; exact Lmde).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_medeleg s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ medeleg _
            (legalize_medeleg (register_lookup medeleg (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmde") as "[Hreg Hmde]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmdv Hrsv) in "Hmde".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw, base_upd_cw. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmde Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmde Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwMedeleg.

(* Demonstration: ONE engine serves many CSRs/source regs. *)
Definition wp_csrw_medeleg_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_medeleg_gpr pc w (mword_of_int 5).

(* ====================================================================== *)
(* mcounteren (0x306, Ext_U, legalize_mcounteren) — full forward + wp.      *)
(* Reuses the CSR-agnostic sAcw/s_pccw/gpr_s_pccw from the medeleg block.   *)
(* ====================================================================== *)
Definition sXcw_mc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) mcounteren
    (legalize_mcounteren (register_lookup mcounteren (s_pccw s pc b).(sregs))
       (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_mc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_mc s pc b rs1) PC (register_lookup nextPC (sXcw_mc s pc b rs1).(sregs)).
Definition sFcw_mc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_mc s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_mc s pc b rs1).(sregs)) 1)
       else sTcw_mc s pc b rs1.

Lemma mcounteren_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 32) :
  register_lookup mcounteren s.(sregs) = v ->
  register_lookup mcounteren (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwMcounteren.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_mcounteren :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFcw_mc s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp LU.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (LUC : eq_vec (_get_Misa_U (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LU. }
    assert (HexecC : exec (execute (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_mc s pc b rs1)).
    { change (execute (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mcounteren (Regidx rs1) zreg CSRRW).
      unfold sXcw_mc. exact (exec_execute_csrw_mcounteren_full rs1 (s_pccw s pc b) Hrs1 LprivC LUC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_mc s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_mc s pc b rs1) (sAcw s b) w
               (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_mc s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_mc, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_mc, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwMcounteren.

Section CleanCsrwMcounteren.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_mc : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         mcounteren
         (legalize_mcounteren (register_lookup mcounteren (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_mc : mstate :=
    if b then set_reg base_upd_cw_mc minstret (add_vec_int mst0 1) else base_upd_cw_mc.
  Lemma sFcw_mc_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_mc s pc b rs1 = sFccw_mc.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_mc s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_mc; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_mc s pc b rs1 = base_upd_cw_mc).
    { unfold sTcw_mc. rewrite Enpc. unfold sXcw_mc, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_mc, s_pccw, sAcw. reflexivity. }
    unfold sFcw_mc, sFccw_mc. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_mc.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_mc, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwMcounteren.

Section WpCsrwMcounteren.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_mcounteren_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mdv0 : mword 64) (mcounteren0 : mword 32)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ mcounteren ↦ᵣ mcounteren0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        mcounteren ↦ᵣ legalize_mcounteren mcounteren0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS HU Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmc")    as %Lmcen.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmcv : register_lookup mcounteren (s_pccw s pc b1).(sregs) = mcounteren0)
      by (apply mcounteren_s_pccw; exact Lmcen).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_mc s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_mc_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_mcounteren s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HU. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mcounteren _
            (legalize_mcounteren (register_lookup mcounteren (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmc") as "[Hreg Hmc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmcv Hrsv) in "Hmc".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_mc, base_upd_cw_mc. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwMcounteren.

Definition wp_csrw_mcounteren_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_mcounteren_gpr pc w (mword_of_int 5).

(* ====================================================================== *)
(* mepc (0x341, _pure check, set_xepc → update_vec_dec v 0 := 'b0).         *)
(* ====================================================================== *)
Definition csr_mepc : mword 12 := mword_of_int 0x341.
Definition mepc_val (v : mword 64) : mword 64 := update_vec_dec v 0 ('b"0").

Lemma exec_legalize_xepc (v : mword 64) s :
  exec (legalize_xepc v) s = Some (mepc_val v, s).
Proof.
  unfold legalize_xepc, mepc_val.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zca s)).
  apply exec_returnM.
Qed.

Lemma exec_write_CSR_mepc (v : mword 64) s :
  exec (write_CSR csr_mepc v) s = Some (Ok (mepc_val v), set_reg s mepc (mepc_val v)).
Proof.
  unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  assert (Hsx : exec (set_xepc Machine v) s = Some (mepc_val v, set_reg s mepc (mepc_val v))).
  { unfold set_xepc.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_xepc v s)). cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mepc (mepc_val v) s)).
    apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hsx).
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_mepc (d : mword 64) s :
  exec (csr_id_write_callback csr_mepc d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_mepc d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_mepc (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_mepc (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mepc (mepc_val (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv.
  apply (exec_execute_csrw_gpr csr_mepc rs1 s _
           (mepc_val (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_mepc s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_mepc.
  - apply exec_csr_id_write_callback_mepc.
Qed.

Definition sXcw_me (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) mepc
    (mepc_val (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_me (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_me s pc b rs1) PC (register_lookup nextPC (sXcw_me s pc b rs1).(sregs)).
Definition sFcw_me (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_me s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_me s pc b rs1).(sregs)) 1)
       else sTcw_me s pc b rs1.

Lemma mepc_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup mepc s.(sregs) = v ->
  register_lookup mepc (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwMepc.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_mepc :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFcw_me s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (HexecC : exec (execute (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_me s pc b rs1)).
    { change (execute (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mepc (Regidx rs1) zreg CSRRW).
      unfold sXcw_me. exact (exec_execute_csrw_mepc rs1 (s_pccw s pc b) Hrs1 LprivC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_me s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_me s pc b rs1) (sAcw s b) w
               (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_me s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_me, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_me, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwMepc.

Section CleanCsrwMepc.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_me : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         mepc
         (mepc_val (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_me : mstate :=
    if b then set_reg base_upd_cw_me minstret (add_vec_int mst0 1) else base_upd_cw_me.
  Lemma sFcw_me_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_me s pc b rs1 = sFccw_me.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_me s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_me; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_me s pc b rs1 = base_upd_cw_me).
    { unfold sTcw_me. rewrite Enpc. unfold sXcw_me, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_me, s_pccw, sAcw. reflexivity. }
    unfold sFcw_me, sFccw_me. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_me.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_me, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwMepc.

Section WpCsrwMepc.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_mepc_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 mepc0 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ mepc ↦ᵣ mepc0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        mepc ↦ᵣ mepc_val vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmepc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmepc")  as %Lmepc.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmev : register_lookup mepc (s_pccw s pc b1).(sregs) = mepc0)
      by (apply mepc_s_pccw; exact Lmepc).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_me s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_me_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_mepc s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mepc _
            (mepc_val (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmepc") as "[Hreg Hmepc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrsv) in "Hmepc".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_me, base_upd_cw_me. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmepc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmepc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwMepc.

Definition wp_csrw_mepc_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_mepc_gpr pc w (mword_of_int 5).

(* ===== mscratch (0x340): pure direct write, _pure check ===== *)
Definition csr_mscratch : mword 12 := mword_of_int 0x340.
Lemma exec_write_CSR_mscratch (v : mword 64) s :
  exec (write_CSR csr_mscratch v) s = Some (Ok v, set_reg s mscratch v).
Proof. unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mscratch v s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mscratch (set_reg s mscratch v))).
  rewrite register_lookup_set. apply exec_returnM. Qed.
Lemma exec_csr_id_write_callback_mscratch (d : mword 64) s :
  exec (csr_id_write_callback csr_mscratch d) s = Some (tt, s).
Proof. assert (H : csr_id_write_callback csr_mscratch d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM. Qed.
Lemma exec_execute_csrw_mscratch (rs1 : mword 5) s :
  uint rs1 <> 0 -> register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_mscratch (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS, set_reg s mscratch (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
Proof. intros Hrs1 Hpriv.
  apply (exec_execute_csrw_gpr csr_mscratch rs1 s _ (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
  - exact Hrs1. - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_mscratch s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity. - vm_compute; reflexivity. - vm_compute; reflexivity.
  - apply exec_write_CSR_mscratch. - apply exec_csr_id_write_callback_mscratch. Qed.

Definition sXcw_msc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) mscratch
    ((register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_msc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_msc s pc b rs1) PC (register_lookup nextPC (sXcw_msc s pc b rs1).(sregs)).
Definition sFcw_msc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_msc s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_msc s pc b rs1).(sregs)) 1)
       else sTcw_msc s pc b rs1.

Lemma mscratch_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup mscratch s.(sregs) = v ->
  register_lookup mscratch (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwMscratch.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_mscratch :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFcw_msc s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (HexecC : exec (execute (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_msc s pc b rs1)).
    { change (execute (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mscratch (Regidx rs1) zreg CSRRW).
      unfold sXcw_msc. exact (exec_execute_csrw_mscratch rs1 (s_pccw s pc b) Hrs1 LprivC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_msc s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_msc s pc b rs1) (sAcw s b) w
               (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_msc s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_msc, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_msc, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwMscratch.

Section CleanCsrwMscratch.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_msc : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         mscratch
         ((register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_msc : mstate :=
    if b then set_reg base_upd_cw_msc minstret (add_vec_int mst0 1) else base_upd_cw_msc.
  Lemma sFcw_msc_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_msc s pc b rs1 = sFccw_msc.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_msc s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_msc; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_msc s pc b rs1 = base_upd_cw_msc).
    { unfold sTcw_msc. rewrite Enpc. unfold sXcw_msc, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_msc, s_pccw, sAcw. reflexivity. }
    unfold sFcw_msc, sFccw_msc. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_msc.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_msc, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwMscratch.

Section WpCsrwMscratch.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_mscratch_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 mscr0 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ mscratch ↦ᵣ mscr0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        mscratch ↦ᵣ vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmscratch Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmscratch")  as %Lmscratch.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmev : register_lookup mscratch (s_pccw s pc b1).(sregs) = mscr0)
      by (apply mscratch_s_pccw; exact Lmscratch).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_msc s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_msc_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_mscratch s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mscratch _
            ((register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmscratch") as "[Hreg Hmscratch]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrsv) in "Hmscratch".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_msc, base_upd_cw_msc. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmscratch Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmscratch Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwMscratch.

Definition wp_csrw_mscratch_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_mscratch_gpr pc w (mword_of_int 5).

(* ===================================================================== *)
(* MONADIC-LEGALIZE REDUCTION LAYER.  Each legalize_* chains             *)
(* currentlyEnabled/hartSupports calls; reduce them to closed bools via  *)
(* the Acc-recursion recipe, keeping the legalized value SYMBOLIC.       *)
(* First target: mideleg (0x303, _S) — shortest legalize (Sscofpmf+S^3). *)
(* ===================================================================== *)

Lemma exec_hartSupports_Sscofpmf s : exec (hartSupports Ext_Sscofpmf) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sscofpmf) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zihpm s : exec (hartSupports Ext_Zihpm) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zihpm) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

(* currentlyEnabled Sscofpmf = hartSupports Sscofpmf && (hartSupports Zihpm && cE Zicsr) = true *)
Lemma exec_currentlyEnabled_Sscofpmf s :
  exec (currentlyEnabled Ext_Sscofpmf) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sscofpmf) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sscofpmf s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zihpm ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zihpm s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  apply exec_hartSupports_Zicsr.
Qed.

(* The SYMBOLIC legalized mideleg value (S-mode enabled, Sscofpmf enabled). *)
Definition mideleg_legalized (o v : mword 64) : mword 64 :=
  let v := Mk_Minterrupts v in
  _update_Minterrupts_SSI
    (_update_Minterrupts_STI
       (_update_Minterrupts_SEI
          (_update_Minterrupts_MSI
             (_update_Minterrupts_MTI
                (_update_Minterrupts_MEI
                   (_update_Minterrupts_LCOFI o (_get_Minterrupts_LCOFI v)) ('b"0")) ('b"0")) ('b"0"))
          (_get_Minterrupts_SEI v))
       (_get_Minterrupts_STI v))
    (_get_Minterrupts_SSI v).

Lemma exec_legalize_mideleg (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_mideleg o v) s = Some (mideleg_legalized o v, s).
Proof.
  intro HS. unfold legalize_mideleg, mideleg_legalized.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sscofpmf s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  apply exec_returnM.
Qed.

Definition csr_mideleg : mword 12 := mword_of_int 0x303.

Lemma exec_write_CSR_mideleg (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_mideleg v) s
    = Some (Ok (mideleg_legalized (register_lookup mideleg s.(sregs)) v),
            set_reg s mideleg (mideleg_legalized (register_lookup mideleg s.(sregs)) v)).
Proof.
  intro HS. unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  (* reached the 0x303 clause *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_mideleg (register_lookup mideleg s.(sregs)) v s HS)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mideleg _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_mideleg (d : mword 64) s :
  exec (csr_id_write_callback csr_mideleg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_mideleg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_mideleg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mideleg (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mideleg
              (mideleg_legalized (register_lookup mideleg s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS.
  apply (exec_execute_csrw_gpr csr_mideleg rs1 s _
           (mideleg_legalized (register_lookup mideleg s.(sregs))
              (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_S csr_mideleg s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_mideleg; exact HS.
  - apply exec_csr_id_write_callback_mideleg.
Qed.
(* ====================================================================== *)
(* mideleg (0x303, Ext_S, legalize_mideleg) — MONADIC legalize; symbolic.  *)
(* WRITTEN register coincides with the interrupt-zero frame (coercion).    *)
(* ====================================================================== *)
Definition sXcw_mid (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) mideleg
    (mideleg_legalized (register_lookup mideleg (s_pccw s pc b).(sregs))
       (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_mid (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_mid s pc b rs1) PC (register_lookup nextPC (sXcw_mid s pc b rs1).(sregs)).
Definition sFcw_mid (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_mid s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_mid s pc b rs1).(sregs)) 1)
       else sTcw_mid s pc b rs1.

Lemma mideleg_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup mideleg s.(sregs) = v ->
  register_lookup mideleg (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwMideleg.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_mideleg :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFcw_mid s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LmIE Lelp LS.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (LSC : eq_vec (_get_Misa_S (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LS. }
    assert (HexecC : exec (execute (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_mid s pc b rs1)).
    { change (execute (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mideleg (Regidx rs1) zreg CSRRW).
      unfold sXcw_mid. exact (exec_execute_csrw_mideleg rs1 (s_pccw s pc b) Hrs1 LprivC LSC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_mid s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_mid s pc b rs1) (sAcw s b) w
               (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_mid s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_mid, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_mid, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwMideleg.

Section CleanCsrwMideleg.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_mid : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         mideleg
         (mideleg_legalized (register_lookup mideleg (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_mid : mstate :=
    if b then set_reg base_upd_cw_mid minstret (add_vec_int mst0 1) else base_upd_cw_mid.
  Lemma sFcw_mid_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_mid s pc b rs1 = sFccw_mid.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_mid s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_mid; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_mid s pc b rs1 = base_upd_cw_mid).
    { unfold sTcw_mid. rewrite Enpc. unfold sXcw_mid, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_mid, s_pccw, sAcw. reflexivity. }
    unfold sFcw_mid, sFccw_mid. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_mid.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_mid, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwMideleg.

Section WpCsrwMideleg.
  Context `{!riscvGS Σ}.
  (* The written register mideleg = R_bitvector_64 mideleg IS the
     interrupt-zero frame, so it appears ONCE (pre-value zeros' 64). *)
  Lemma wp_csrw_mideleg_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mideleg_legalized mdv0 vrs1 -∗
        (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmdv : register_lookup mideleg (s_pccw s pc b1).(sregs) = mdv0)
      by (apply mideleg_s_pccw; exact Lmdl).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_mid s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_mid_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_mideleg s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mideleg _
            (mideleg_legalized (register_lookup mideleg (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmdl") as "[Hreg Hmdl]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmdv Hrsv) in "Hmdl".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_mid, base_upd_cw_mid. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwMideleg.

Definition wp_csrw_mideleg_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_mideleg_gpr pc w (mword_of_int 5).

(* ===================================================================== *)
(* sie (0x104, _S): legalize_sie is PURE; write_CSR threads read mie +    *)
(* read mideleg + write mie + readback.  Writes mie (no frame collision). *)
(* ===================================================================== *)
Definition csr_sie : mword 12 := mword_of_int 0x104.

Definition sie_new_mie (mie0 mdl0 v : mword 64) : mword 64 := legalize_sie mie0 mdl0 v.

Lemma exec_write_CSR_sie (v : mword 64) s :
  exec (write_CSR csr_sie v) s
    = Some (Ok (lower_mie (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)) v)
                          (register_lookup mideleg s.(sregs))),
            set_reg s mie (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)) v)).
Proof.
  unfold write_CSR, sie_new_mie.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  (* reached the 0x104 clause *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mie _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie (set_reg s mie _))).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg (set_reg s mie _))).
  rewrite register_lookup_set.
  rewrite irrelevant_register_set; [|vm_compute; reflexivity].
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_sie (d : mword 64) s :
  exec (csr_id_write_callback csr_sie d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_sie d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_sie (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_sie (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mie
              (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS.
  apply (exec_execute_csrw_gpr csr_sie rs1 s _
           (lower_mie (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs))
                         (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))
                      (register_lookup mideleg s.(sregs)))).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_S csr_sie s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_sie.
  - apply exec_csr_id_write_callback_sie.
Qed.

(* ---- sie forward/clean/wp: writes mie; value reads mie + mideleg ---- *)
Definition sXcw_sie (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) mie
    (sie_new_mie (register_lookup mie (s_pccw s pc b).(sregs))
       (register_lookup mideleg (s_pccw s pc b).(sregs))
       (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_sie (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_sie s pc b rs1) PC (register_lookup nextPC (sXcw_sie s pc b rs1).(sregs)).
Definition sFcw_sie (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_sie s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_sie s pc b rs1).(sregs)) 1)
       else sTcw_sie s pc b rs1.

Lemma mie_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup mie s.(sregs) = v ->
  register_lookup mie (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwSie.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_sie :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFcw_sie s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LmIE Lelp LS.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (LSC : eq_vec (_get_Misa_S (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LS. }
    assert (HexecC : exec (execute (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_sie s pc b rs1)).
    { change (execute (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_sie (Regidx rs1) zreg CSRRW).
      unfold sXcw_sie. exact (exec_execute_csrw_sie rs1 (s_pccw s pc b) Hrs1 LprivC LSC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_sie s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_sie s pc b rs1) (sAcw s b) w
               (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_sie s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_sie, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_sie, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwSie.

Section CleanCsrwSie.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_sie : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         mie
         (sie_new_mie (register_lookup mie (s_pccw s pc b).(sregs))
            (register_lookup mideleg (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_sie : mstate :=
    if b then set_reg base_upd_cw_sie minstret (add_vec_int mst0 1) else base_upd_cw_sie.
  Lemma sFcw_sie_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_sie s pc b rs1 = sFccw_sie.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_sie s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_sie; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_sie s pc b rs1 = base_upd_cw_sie).
    { unfold sTcw_sie. rewrite Enpc. unfold sXcw_sie, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_sie, s_pccw, sAcw. reflexivity. }
    unfold sFcw_sie, sFccw_sie. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_sie.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_sie, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwSie.

Section WpCsrwSie.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_sie_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mie0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ mie ↦ᵣ mie0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        mie ↦ᵣ sie_new_mie mie0 mdv0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmie Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmie")   as %Lmie.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmiev : register_lookup mie (s_pccw s pc b1).(sregs) = mie0)
      by (apply mie_s_pccw; exact Lmie).
    assert (Hmdlv : register_lookup mideleg (s_pccw s pc b1).(sregs) = mdv0)
      by (apply mideleg_s_pccw; exact Lmdl).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_sie s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_sie_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_sie s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mie _
            (sie_new_mie (register_lookup mie (s_pccw s pc b1).(sregs))
               (register_lookup mideleg (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmie") as "[Hreg Hmie]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmiev Hmdlv Hrsv) in "Hmie".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_sie, base_upd_cw_sie. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmie Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmie Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwSie.

Definition wp_csrw_sie_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_sie_gpr pc w (mword_of_int 5).

(* ===== mstatus reduction tower (concrete-reclimit, Sscofpmf-style) ===== *)
Lemma exec_rec_cE_Zicsr_any (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true -> exec (_rec_currentlyEnabled Ext_Zicsr k acc) s = Some (true, s).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_hartSupports_Sv39 s : exec (hartSupports Ext_Sv39) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv39) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Sv32 s : exec (hartSupports Ext_Sv32) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv32) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb false (Z.eqb xlen 32)) with false by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_virtual_memory_supported s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (virtual_memory_supported tt) s = Some (true, s).
Proof.
  intro HS. unfold virtual_memory_supported. destruct (Defs.Zwf_guarded _).
  cbn [_rec_virtual_memory_supported]. unfold Defs.assert_exp'.
  replace (Z.geb 3 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* or_boolM (rec cE Sv32 2) (...) : reduce Sv32 -> false inline *)
  match goal with |- context[_rec_currentlyEnabled Ext_Sv32 ?k ?a] =>
    assert (H32 : exec (_rec_currentlyEnabled Ext_Sv32 k a) s = Some (false, s)) end.
  { match goal with |- exec (_rec_currentlyEnabled Ext_Sv32 ?k ?a) s = _ => destruct a end.
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (Z.sub 3 1) 0) with true by reflexivity. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv32 s)). reflexivity. }
  rewrite (exec_or_boolM_Some _ _ _ _ _ H32). cbn match.
  (* or_boolM (rec cE Sv39 2) (...) : reduce Sv39 -> true inline *)
  match goal with |- context[_rec_currentlyEnabled Ext_Sv39 ?k ?a] =>
    assert (H39 : exec (_rec_currentlyEnabled Ext_Sv39 k a) s = Some (true, s)) end.
  { match goal with |- exec (_rec_currentlyEnabled Ext_Sv39 ?k ?a) s = _ => destruct a end.
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (Z.sub 3 1) 0) with true by reflexivity. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv39 s)). cbn match.
    (* rec cE S at reclimit 1 inline *)
    match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
      assert (HSm : exec (_rec_currentlyEnabled Ext_S k a) s
                    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s)) end.
    { match goal with |- exec (_rec_currentlyEnabled Ext_S ?k ?a) s = _ => destruct a end.
      cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
      replace (Z.geb (Z.sub (Z.sub 3 1) 1) 0) with true by reflexivity. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)). cbn match.
      rewrite (exec_and_boolM_Some _ _ s
                 (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
      2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
      destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
      - match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
          exact (exec_rec_cE_Zicsr_any k2 a2 s ltac:(reflexivity)) end.
      - reflexivity. }
    rewrite HSm. rewrite HS. reflexivity. }
  rewrite (exec_or_boolM_Some _ _ _ _ _ H39). reflexivity.
Qed.

Lemma exec_lowest_supported_privLevel s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (lowest_supported_privLevel tt) s = Some (User, s).
Proof.
  intro HU. unfold lowest_supported_privLevel.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_U s HU)). cbn match.
  apply exec_returnM.
Qed.

Definition have_nom_val (priv : mword 2) : bool :=
  if eq_vec priv ('b"00") then true
  else if eq_vec priv ('b"01") then true
  else if eq_vec priv ('b"10") then false else true.

Lemma exec_have_nominal_privLevel (priv : mword 2) s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (have_nominal_privLevel priv) s = Some (have_nom_val priv, s).
Proof.
  intros HU HS. unfold have_nominal_privLevel, have_nom_val.
  destruct (eq_vec priv ('b"00")) eqn:E0.
  - exact (exec_currentlyEnabled_U s HU).
  - destruct (eq_vec priv ('b"01")) eqn:E1.
    + rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
    + apply exec_returnM.
Qed.

(* SYMBOLIC legalized mstatus (misa.S=misa.U=true; Zicfilp + Sv39 enabled). *)
Definition mstatus_legalized (o v : mword 64) : mword 64 :=
  let mv := Mk_Mstatus v in
  let w18 := if have_nom_val (_get_Mstatus_MPP mv)
             then _get_Mstatus_MPP mv else privLevel_to_bits User in
  let o' :=
    _update_Mstatus_SIE
      (_update_Mstatus_MIE
        (_update_Mstatus_SPIE
          (_update_Mstatus_MPIE
            (_update_Mstatus_SPP
              (_update_Mstatus_MPP
                (_update_Mstatus_VS
                  (_update_Mstatus_FS
                    (_update_Mstatus_XS
                      (_update_Mstatus_MPRV
                        (_update_Mstatus_SUM
                          (_update_Mstatus_MXR
                            (_update_Mstatus_TVM
                              (_update_Mstatus_TW
                                (_update_Mstatus_TSR
                                  (_update_Mstatus_SPELP
                                    (_update_Mstatus_MPELP o (_get_Mstatus_MPELP mv))
                                    (_get_Mstatus_SPELP mv))
                                  (_get_Mstatus_TSR mv))
                                (_get_Mstatus_TW mv))
                              (_get_Mstatus_TVM mv))
                            (_get_Mstatus_MXR mv))
                          (_get_Mstatus_SUM mv))
                        (_get_Mstatus_MPRV mv))
                      (extStatus_map_forwards Off))
                    (legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS mv)))
                  (legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS mv)))
                w18)
              (_get_Mstatus_SPP mv))
            (_get_Mstatus_MPIE mv))
          (_get_Mstatus_SPIE mv))
        (_get_Mstatus_MIE mv))
      (_get_Mstatus_SIE mv) in
  let dirty :=
    orb (generic_eq (extStatus_map_backwards (_get_Mstatus_FS o')) Dirty)
      (orb (generic_eq (extStatus_map_backwards (_get_Mstatus_XS o')) Dirty)
        (generic_eq (extStatus_map_backwards (_get_Mstatus_VS o')) Dirty)) in
  _update_Mstatus_SD o' (bool_to_bit dirty).

Lemma exec_legalize_mstatus (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_mstatus o v) s = Some (mstatus_legalized o v, s).
Proof.
  intros HS HU. unfold legalize_mstatus, mstatus_legalized.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_U s HU)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_virtual_memory_supported s HS)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_U s HU)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_have_nominal_privLevel (_get_Mstatus_MPP (Mk_Mstatus v)) s HU HS)).
  match goal with |- exec (Defs.bind ?IF _) s = _ =>
    assert (Hw18 : exec IF s
                   = Some (if have_nom_val (_get_Mstatus_MPP (Mk_Mstatus v))
                           then _get_Mstatus_MPP (Mk_Mstatus v) else privLevel_to_bits User, s)) end.
  { destruct (have_nom_val (_get_Mstatus_MPP (Mk_Mstatus v))).
    - cbn match. apply exec_returnM.
    - cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_lowest_supported_privLevel s HU)).
      apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hw18). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  apply exec_returnM.
Qed.

Definition csr_mstatus : mword 12 := mword_of_int 0x300.

Lemma exec_write_CSR_mstatus (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_mstatus v) s
    = Some (Ok (mstatus_legalized (register_lookup mstatus s.(sregs)) v),
            set_reg s mstatus (mstatus_legalized (register_lookup mstatus s.(sregs)) v)).
Proof.
  intros HS HU. unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  (* reached the xlen=64 0x300 clause; expose its body *)
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_legalize_mstatus (register_lookup mstatus s.(sregs)) v s HS HU)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_mstatus (d : mword 64) s :
  exec (csr_id_write_callback csr_mstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_mstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_mstatus (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mstatus (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s mstatus
              (mstatus_legalized (register_lookup mstatus s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS HU.
  apply (exec_execute_csrw_gpr csr_mstatus rs1 s _
           (mstatus_legalized (register_lookup mstatus s.(sregs))
              (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_mstatus s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_mstatus; assumption.
  - apply exec_csr_id_write_callback_mstatus.
Qed.

(* ====================================================================== *)
(* mstatus (0x300, _pure check, MONADIC legalize_mstatus). WRITTEN mstatus  *)
(* = R_bitvector_64 mstatus MIE frame -> own once (pre MIE=false). mideleg  *)
(* stays a separate pending frame. legalize needs misa.S AND misa.U.        *)
(* ====================================================================== *)
Definition sXcw_mst (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) mstatus
    (mstatus_legalized (register_lookup mstatus (s_pccw s pc b).(sregs))
       (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_mst (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_mst s pc b rs1) PC (register_lookup nextPC (sXcw_mst s pc b rs1).(sregs)).
Definition sFcw_mst (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_mst s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_mst s pc b rs1).(sregs)) 1)
       else sTcw_mst s pc b rs1.

Lemma mstatus_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup mstatus s.(sregs) = v ->
  register_lookup mstatus (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwMstatus.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_mstatus :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFcw_mst s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LmIE Lelp LS LU.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (LSC : eq_vec (_get_Misa_S (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LS. }
    assert (LUC : eq_vec (_get_Misa_U (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LU. }
    assert (HexecC : exec (execute (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_mst s pc b rs1)).
    { change (execute (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mstatus (Regidx rs1) zreg CSRRW).
      unfold sXcw_mst. exact (exec_execute_csrw_mstatus rs1 (s_pccw s pc b) Hrs1 LprivC LSC LUC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_mst s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_mst s pc b rs1) (sAcw s b) w
               (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_mst s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_mst, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_mst, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwMstatus.

Section CleanCsrwMstatus.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_mst : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         mstatus
         (mstatus_legalized (register_lookup mstatus (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_mst : mstate :=
    if b then set_reg base_upd_cw_mst minstret (add_vec_int mst0 1) else base_upd_cw_mst.
  Lemma sFcw_mst_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_mst s pc b rs1 = sFccw_mst.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_mst s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_mst; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_mst s pc b rs1 = base_upd_cw_mst).
    { unfold sTcw_mst. rewrite Enpc. unfold sXcw_mst, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_mst, s_pccw, sAcw. reflexivity. }
    unfold sFcw_mst, sFccw_mst. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_mst.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_mst, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwMstatus.

Section WpCsrwMstatus.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_mstatus_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mstatus0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗
        (R_bitvector_64 mstatus) ↦ᵣ mstatus_legalized mstatus0 vrs1 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS HU Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmsv : register_lookup mstatus (s_pccw s pc b1).(sregs) = mstatus0)
      by (apply mstatus_s_pccw; exact Lms).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_mst s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_mst_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_mstatus s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS.
      - rewrite Lmisa. exact HU. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mstatus _
            (mstatus_legalized (register_lookup mstatus (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmsv Hrsv) in "Hms".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_mst, base_upd_cw_mst. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwMstatus.

Definition wp_csrw_mstatus_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_mstatus_gpr pc w (mword_of_int 5).

(* ===================================================================== *)
(* satp (0x180): architecture(Supervisor) + legalize_satp mode case-split *)
(* ===================================================================== *)
Lemma exec_hartSupports_Sv48 s : exec (hartSupports Ext_Sv48) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv48) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Sv57 s : exec (hartSupports Ext_Sv57) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv57) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

(* discharge an inner `_rec_currentlyEnabled Ext_S k a` (concrete k) to misa.S *)
Ltac crush_rec_cE_S s :=
  match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
    let H := fresh "HrecS" in
    assert (H : exec (_rec_currentlyEnabled Ext_S k a) s
                = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s));
    [ destruct a; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?kk 0] => replace (Z.geb kk 0) with true by reflexivity end;
      cbn match; rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match;
      rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)); cbn match;
      rewrite (exec_and_boolM_Some _ _ s
                 (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s);
      [ destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:?;
        [ match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
            exact (exec_rec_cE_Zicsr_any k2 a2 s ltac:(reflexivity)) end
        | reflexivity ]
      | rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)); apply exec_returnM ]
    | rewrite H ]
  end.

Lemma exec_currentlyEnabled_Svbare s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Svbare) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svbare) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

Lemma exec_currentlyEnabled_Sv39w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Sv39) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv39) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv39 s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

Lemma exec_currentlyEnabled_Sv48w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Sv48) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv48) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv48 s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

Lemma exec_currentlyEnabled_Sv57w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Sv57) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv57) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv57 s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

Lemma exec_architecture_Supervisor s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (architecture Supervisor) s = Some (RV64, s).
Proof.
  intro HSXL. unfold architecture. cbn match.
  match goal with |- exec (Defs.bind ?L _) s = _ =>
    assert (Hin : exec L s = Some (_get_Mstatus_SXL (register_lookup mstatus s.(sregs)), s)) end.
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hin).
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity). cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

Definition csr_satp : mword 12 := mword_of_int 0x180.

Definition satp_legalized (prev value : mword 64) : mword 64 :=
  match satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 value)) with
  | Some Bare => Mk_Satp64 value
  | Some Sv39 => Mk_Satp64 value
  | Some Sv48 => Mk_Satp64 value
  | Some Sv57 => Mk_Satp64 value
  | Some Sv32 => prev
  | None => prev
  end.

Lemma exec_legalize_satp_rv64 (prev value : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_satp RV64 prev value) s = Some (satp_legalized prev value, s).
Proof.
  intro HS. unfold legalize_satp, satp_legalized.
  destruct (satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 value))) as [sv|] eqn:Hm.
  - destruct sv.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svbare s HS)). cbn match. apply exec_returnM.
    + apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sv39w s HS)). cbn match. apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sv48w s HS)). cbn match. apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sv57w s HS)). cbn match. apply exec_returnM.
  - apply exec_returnM.
Qed.

Lemma exec_write_CSR_satp (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (write_CSR csr_satp v) s
    = Some (Ok (satp_legalized (register_lookup satp s.(sregs)) v),
            set_reg s satp (satp_legalized (register_lookup satp s.(sregs)) v)).
Proof.
  intros HS HSXL. unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_satp_rv64 (register_lookup satp s.(sregs)) v s HS)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg satp _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_satp (d : mword 64) s :
  exec (csr_id_write_callback csr_satp d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_satp d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_satp s :
  exec (is_CSR_accessible csr_satp Machine CSRWrite) s = Some (true, s).
Proof.
  unfold is_CSR_accessible.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  unfold satp_accessible. cbn match. apply exec_hartSupports_S.
Qed.

Lemma exec_execute_csrw_satp (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (execute_CSRReg csr_satp (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s satp
              (satp_legalized (register_lookup satp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS HSXL.
  apply (exec_execute_csrw_gpr csr_satp rs1 s _
           (satp_legalized (register_lookup satp s.(sregs))
              (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_satp s);
      [ vm_compute; reflexivity
      | vm_compute; reflexivity
      | apply exec_is_CSR_accessible_satp
      | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_satp; assumption.
  - apply exec_csr_id_write_callback_satp.
Qed.

(* ---- satp forward/clean/wp: writes satp; reads mstatus (MIE + SXL) ---- *)
Definition sXcw_satp (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) satp
    (satp_legalized (register_lookup satp (s_pccw s pc b).(sregs))
       (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_satp (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_satp s pc b rs1) PC (register_lookup nextPC (sXcw_satp s pc b rs1).(sregs)).
Definition sFcw_satp (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_satp s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_satp s pc b rs1).(sregs)) 1)
       else sTcw_satp s pc b rs1.

Lemma satp_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup satp s.(sregs) = v ->
  register_lookup satp (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwSatp.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_satp :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    exec riscv_step s = Some (tt, sFcw_satp s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LmIE Lelp LS LSXL.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (LSC : eq_vec (_get_Misa_S (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LS. }
    assert (LSXLC : _get_Mstatus_SXL (register_lookup mstatus (s_pccw s pc b).(sregs)) = 'b"10").
    { rewrite (mstatus_s_pccw s pc b (register_lookup mstatus s.(sregs)) eq_refl). exact LSXL. }
    assert (HexecC : exec (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_satp s pc b rs1)).
    { change (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_satp (Regidx rs1) zreg CSRRW).
      unfold sXcw_satp. exact (exec_execute_csrw_satp rs1 (s_pccw s pc b) Hrs1 LprivC LSC LSXLC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_satp s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_satp s pc b rs1) (sAcw s b) w
               (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_satp s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_satp, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_satp, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwSatp.

Section CleanCsrwSatp.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_satp : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         satp
         (satp_legalized (register_lookup satp (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_satp : mstate :=
    if b then set_reg base_upd_cw_satp minstret (add_vec_int mst0 1) else base_upd_cw_satp.
  Lemma sFcw_satp_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_satp s pc b rs1 = sFccw_satp.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_satp s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_satp; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_satp s pc b rs1 = base_upd_cw_satp).
    { unfold sTcw_satp. rewrite Enpc. unfold sXcw_satp, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_satp, s_pccw, sAcw. reflexivity. }
    unfold sFcw_satp, sFccw_satp. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_satp.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_satp, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwSatp.

Section WpCsrwSatp.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_satp_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mstatus0 satp0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ satp ↦ᵣ satp0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        satp ↦ᵣ satp_legalized satp0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS HSXL Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hsatp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hsatp")  as %Lsatp.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hsatpv : register_lookup satp (s_pccw s pc b1).(sregs) = satp0)
      by (apply satp_s_pccw; exact Lsatp).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_satp s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_satp_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_satp s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HSXL. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ satp _
            (satp_legalized (register_lookup satp (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hsatp") as "[Hreg Hsatp]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hsatpv Hrsv) in "Hsatp".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_satp, base_upd_cw_satp. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hsatp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hsatp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwSatp.

Definition wp_csrw_satp_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_satp_gpr pc w (mword_of_int 5).

(* PROBE: does reg_update work on a VEC register (pmpaddr_n)? *)
Lemma probe_vec_reg_update `{!riscvGS Σ} rs
    (v v' : type_of_register pmpaddr_n) :
  reg_interp rs -∗ pmpaddr_n ↦ᵣ v ==∗
    reg_interp (register_set pmpaddr_n v' rs) ∗ pmpaddr_n ↦ᵣ v'.
Proof.
  iIntros "Hi Hr". iMod (reg_update _ pmpaddr_n _ v' with "Hi Hr") as "[Hi Hr]".
  iModIntro. iFrame.
Qed.

(* ===================================================================== *)
(* pmpaddr0 (0x3b0): NO currentlyEnabled — pure pmpWriteAddrReg threading  *)
(* + pmpReadAddrReg readback. Config: usable=16, grain=0 (no mask).        *)
(* ===================================================================== *)
Definition csr_pmpaddr0 : mword 12 := mword_of_int 0x3b0.

Definition pmp0_newaddr (cfg : vec (mword 8) 64) (addr : vec (mword 64) 64) (v : mword 64)
  : vec (mword 64) 64 :=
  vec_update_dec addr 0
    (pmpWriteAddr (pmpLocked (vec_access_dec cfg 0)) (pmpTORLocked (vec_access_dec cfg (Z.add 0 1)))
       (vec_access_dec addr 0) v).

Lemma exec_pmpWriteAddrReg_0 (v : mword 64) s :
  exec (pmpWriteAddrReg 0 v) s
    = Some (tt, set_reg s pmpaddr_n
              (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                 (register_lookup pmpaddr_n s.(sregs)) v)).
Proof.
  unfold pmpWriteAddrReg.
  replace (Z.ltb 0 sys_pmp_usable_count) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  replace (Z.ltb (Z.add 0 1) 64) with true by (vm_compute; reflexivity). cbn match.
  match goal with |- exec (Defs.bind ?L _) s = _ =>
    assert (Hin : exec L s
                  = Some (pmpTORLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) (Z.add 0 1)), s)) end.
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hin).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)).
  unfold pmp0_newaddr. apply exec_write_reg.
Qed.

Lemma exec_pmpReadAddrReg_0 s :
  exec (pmpReadAddrReg 0) s = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0, s).
Proof.
  unfold pmpReadAddrReg.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)).
  replace (Z.geb sys_pmp_grain 2) with false by (vm_compute; reflexivity).
  replace (Z.geb sys_pmp_grain 1) with false by (vm_compute; reflexivity).
  cbn match. apply exec_returnM.
Qed.

(* readback + Ok-wrap, proved while pmpReadAddrReg is still FOLDED *)
Lemma exec_pmpReadAddrReg_0_ok s :
  exec (Defs.bind (pmpReadAddrReg 0) (fun w => returnM (Ok w) : M (result (mword 64) unit))) s
    = Some (Ok (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0), s).
Proof.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpReadAddrReg_0 s)). apply exec_returnM.
Qed.

Lemma exec_write_CSR_pmpaddr0 (v : mword 64) s :
  exec (write_CSR csr_pmpaddr0 v) s
    = Some (Ok (vec_access_dec
                  (register_lookup pmpaddr_n
                     (set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                        (register_lookup pmpaddr_n s.(sregs)) v)).(sregs)) 0),
            set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
              (register_lookup pmpaddr_n s.(sregs)) v)).
Proof.
  unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  cbn zeta.
  replace (uint (concat_vec ('b"00") (subrange_vec_dec csr_pmpaddr0 3 0))) with 0
    by (vm_compute; reflexivity).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_pmpWriteAddrReg_0 v s)).
  exact (exec_pmpReadAddrReg_0_ok
           (set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
              (register_lookup pmpaddr_n s.(sregs)) v))).
Qed.

Lemma exec_csr_id_write_callback_pmpaddr0 (d : mword 64) s :
  exec (csr_id_write_callback csr_pmpaddr0 d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_pmpaddr0 d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_pmpaddr0 (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_pmpaddr0 (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s pmpaddr_n
              (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                 (register_lookup pmpaddr_n s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv.
  apply (exec_execute_csrw_gpr csr_pmpaddr0 rs1 s _
           (vec_access_dec
              (register_lookup pmpaddr_n
                 (set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                    (register_lookup pmpaddr_n s.(sregs))
                    (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).(sregs)) 0)).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_pmpaddr0 s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_pmpaddr0.
  - apply exec_csr_id_write_callback_pmpaddr0.
Qed.

(* ---- pmpaddr0 forward/clean/wp: writes vec pmpaddr_n; reads pmpcfg_n ---- *)
Definition sXcw_pa (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) pmpaddr_n
    (pmp0_newaddr (register_lookup pmpcfg_n (s_pccw s pc b).(sregs))
       (register_lookup pmpaddr_n (s_pccw s pc b).(sregs))
       (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_pa (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_pa s pc b rs1) PC (register_lookup nextPC (sXcw_pa s pc b rs1).(sregs)).
Definition sFcw_pa (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_pa s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_pa s pc b rs1).(sregs)) 1)
       else sTcw_pa s pc b rs1.

Lemma pmpaddr_n_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : type_of_register pmpaddr_n) :
  register_lookup pmpaddr_n s.(sregs) = v ->
  register_lookup pmpaddr_n (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Lemma pmpcfg_n_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : type_of_register pmpcfg_n) :
  register_lookup pmpcfg_n s.(sregs) = v ->
  register_lookup pmpcfg_n (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwPmpaddr0.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_pmpaddr0 :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFcw_pa s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (HexecC : exec (execute (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_pa s pc b rs1)).
    { change (execute (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_pmpaddr0 (Regidx rs1) zreg CSRRW).
      unfold sXcw_pa. exact (exec_execute_csrw_pmpaddr0 rs1 (s_pccw s pc b) Hrs1 LprivC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_pa s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_pa s pc b rs1) (sAcw s b) w
               (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_pa s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_pa, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_pa, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwPmpaddr0.

Section CleanCsrwPmpaddr0.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_pa : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         pmpaddr_n
         (pmp0_newaddr (register_lookup pmpcfg_n (s_pccw s pc b).(sregs))
            (register_lookup pmpaddr_n (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_pa : mstate :=
    if b then set_reg base_upd_cw_pa minstret (add_vec_int mst0 1) else base_upd_cw_pa.
  Lemma sFcw_pa_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_pa s pc b rs1 = sFccw_pa.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_pa s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_pa; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_pa s pc b rs1 = base_upd_cw_pa).
    { unfold sTcw_pa. rewrite Enpc. unfold sXcw_pa, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_pa, s_pccw, sAcw. reflexivity. }
    unfold sFcw_pa, sFccw_pa. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_pa.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_pa, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwPmpaddr0.

Section WpCsrwPmpaddr0.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_pmpaddr0_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr00 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hpa Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hpa")    as %Lpa.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hpav : register_lookup pmpaddr_n (s_pccw s pc b1).(sregs) = pmpaddr00)
      by (apply pmpaddr_n_s_pccw; exact Lpa).
    assert (Hpcv : register_lookup pmpcfg_n (s_pccw s pc b1).(sregs) = pmpcfg0)
      by (apply pmpcfg_n_s_pccw; exact Lpmpc).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_pa s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_pa_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_pmpaddr0 s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ pmpaddr_n _
            (pmp0_newaddr (register_lookup pmpcfg_n (s_pccw s pc b1).(sregs))
               (register_lookup pmpaddr_n (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hpa") as "[Hreg Hpa]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hpcv Hpav Hrsv) in "Hpa".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_pa, base_upd_cw_pa. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hpa Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hpa Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwPmpaddr0.

Definition wp_csrw_pmpaddr0_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_pmpaddr0_gpr pc w (mword_of_int 5).

(* ===================================================================== *)
(* pmpcfg0 (0x3a0): pmpWriteCfgReg foreach_ZM_up loop (8 iters, state-      *)
(* threading) writing one pmpcfg_n byte each. pmpWriteCfg is total         *)
(* (PMP_ClearPermissions). Keep results symbolic.                          *)
(* ===================================================================== *)
Definition pmpWriteCfg_val (cfg v : mword 8) : mword 8 :=
  if pmpLocked cfg then cfg
  else
    let c := Mk_Pmpcfg_ent (and_vec v (Ox"9F")) in
    let c := if andb (eq_vec (_get_Pmpcfg_ent_W c) ('b"1")) (eq_vec (_get_Pmpcfg_ent_R c) ('b"0"))
             then _update_Pmpcfg_ent_R
                    (_update_Pmpcfg_ent_W (_update_Pmpcfg_ent_X c ('b"0")) ('b"0")) ('b"0")
             else c in
    if (match pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A c) with
        | OFF => true | TOR => true
        | NA4 => andb true (Z.eqb sys_pmp_grain 0) | NAPOT => true end)
    then c else _update_Pmpcfg_ent_A c (pmpAddrMatchType_encdec_forwards OFF).

Lemma exec_pmpWriteCfg (cfg v : mword 8) s :
  exec (pmpWriteCfg cfg v) s = Some (pmpWriteCfg_val cfg v, s).
Proof.
  unfold pmpWriteCfg, pmpWriteCfg_val.
  destruct (pmpLocked cfg).
  - apply exec_returnM.
  - destruct (andb (eq_vec (_get_Pmpcfg_ent_W (Mk_Pmpcfg_ent (and_vec v (Ox"9F")))) ('b"1"))
                   (eq_vec (_get_Pmpcfg_ent_R (Mk_Pmpcfg_ent (and_vec v (Ox"9F")))) ('b"0"))).
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). apply exec_returnM.
Qed.

Definition pmp_cfg_step (v : mword 64) (s : mstate) (i : Z) : mstate :=
  set_reg s pmpcfg_n
    (vec_update_dec (register_lookup pmpcfg_n s.(sregs)) (Z.add (Z.mul 0 4) i)
       (pmpWriteCfg_val
          (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) (Z.add (Z.mul 0 4) i))
          (autocast (T := mword) (subrange_vec_dec v (Z.add (Z.mul 8 i) 7) (Z.mul 8 i))))).

Definition pmpcfg0_final (v : mword 64) (s : mstate) : mstate :=
  pmp_cfg_step v (pmp_cfg_step v (pmp_cfg_step v (pmp_cfg_step v
    (pmp_cfg_step v (pmp_cfg_step v (pmp_cfg_step v (pmp_cfg_step v s 0) 1) 2) 3) 4) 5) 6) 7.

Ltac do_cfg_step vv ii :=
  rewrite Defs.unroll_foreach_ZM_up'; [ | lia ];
  match goal with
  | |- exec (Defs.bind ?body0 _) ?si = _ =>
    let Hb := fresh "Hb" in
    assert (Hb : exec body0 si = Some (tt, pmp_cfg_step vv si ii));
    [ replace (Z.ltb (Z.add (Z.mul 0 4) ii) sys_pmp_usable_count) with true by (vm_compute; reflexivity);
      cbn match;
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n si));
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n si));
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpWriteCfg _ _ si));
      unfold pmp_cfg_step; apply exec_write_reg
    | rewrite (exec_bind_Some _ _ _ _ _ Hb) ]
  end.

Lemma exec_pmpWriteCfgReg_0 (v : mword 64) s :
  exec (pmpWriteCfgReg 0 v) s = Some (tt, pmpcfg0_final v s).
Proof.
  unfold pmpWriteCfgReg, Defs.assert_exp'.
  replace (Z.eqb (Z.rem 0 2) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  unfold Defs.foreach_ZM_up.
  do_cfg_step v 0. do_cfg_step v 1. do_cfg_step v 2. do_cfg_step v 3.
  do_cfg_step v 4. do_cfg_step v 5. do_cfg_step v 6. do_cfg_step v 7.
  cbn [Defs.foreach_ZM_up']. apply exec_returnM.
Qed.

Definition csr_pmpcfg0 : mword 12 := mword_of_int 0x3a0.

Definition pmpcfg0_readback (cfg : vec (mword 8) 64) : mword 64 :=
  concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 7))
   (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 6))
    (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 5))
     (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 4))
      (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 3))
       (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 2))
        (concat_vec (vec_access_dec cfg (Z.add (Z.mul 0 4) 1))
         (vec_access_dec cfg (Z.add (Z.mul 0 4) 0)))))))).

Lemma exec_pmpReadCfgReg_0 s :
  exec (pmpReadCfgReg 0) s = Some (pmpcfg0_readback (register_lookup pmpcfg_n s.(sregs)), s).
Proof.
  unfold pmpReadCfgReg, Defs.assert_exp'.
  replace (Z.eqb (Z.rem 0 2) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)).
  apply exec_returnM.
Qed.

Lemma exec_pmpReadCfgReg_0_ok s :
  exec (Defs.bind (pmpReadCfgReg 0) (fun w => returnM (Ok w) : M (result (mword 64) unit))) s
    = Some (Ok (pmpcfg0_readback (register_lookup pmpcfg_n s.(sregs))), s).
Proof.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpReadCfgReg_0 s)). apply exec_returnM.
Qed.

Lemma exec_write_CSR_pmpcfg0 (v : mword 64) s :
  exec (write_CSR csr_pmpcfg0 v) s
    = Some (Ok (pmpcfg0_readback (register_lookup pmpcfg_n (pmpcfg0_final v s).(sregs))),
            pmpcfg0_final v s).
Proof.
  unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  cbn zeta.
  assert (Hidx : uint (subrange_vec_dec csr_pmpcfg0 3 0) = 0) by (vm_compute; reflexivity).
  rewrite !Hidx.
  assert (Hwr : exec (Defs.bind0 (pmpWriteCfgReg 0 v) (pmpReadCfgReg 0)) s
                = Some (pmpcfg0_readback (register_lookup pmpcfg_n (pmpcfg0_final v s).(sregs)),
                        pmpcfg0_final v s)).
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_pmpWriteCfgReg_0 v s)).
    exact (exec_pmpReadCfgReg_0 (pmpcfg0_final v s)). }
  rewrite (exec_bind_Some _ _ _ _ _ Hwr). apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_pmpcfg0 (d : mword 64) s :
  exec (csr_id_write_callback csr_pmpcfg0 d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_pmpcfg0 d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_pmpcfg0 (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_pmpcfg0 (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            pmpcfg0_final (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) s).
Proof.
  intros Hrs1 Hpriv.
  apply (exec_execute_csrw_gpr csr_pmpcfg0 rs1 s _
           (pmpcfg0_readback (register_lookup pmpcfg_n
              (pmpcfg0_final (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) s).(sregs)))).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_pure csr_pmpcfg0 s);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_pmpcfg0.
  - apply exec_csr_id_write_callback_pmpcfg0.
Qed.

(* ---- collapse the 8 nested set_reg pmpcfg_n into a single set_reg ---- *)
Lemma register_set_pmpcfg_n_overwrite (a b : type_of_register pmpcfg_n) (regs : regstate) :
  register_set pmpcfg_n b (register_set pmpcfg_n a regs) = register_set pmpcfg_n b regs.
Proof.
  destruct regs. unfold register_set. cbn.
  f_equal. apply functional_extensionality; intro x.
  destruct (register_vector_64_bitvector_8_beq x pmpcfg_n); reflexivity.
Qed.

Lemma set_reg_pmpcfg_n_overwrite (a b : type_of_register pmpcfg_n) (s : mstate) :
  set_reg (set_reg s pmpcfg_n a) pmpcfg_n b = set_reg s pmpcfg_n b.
Proof. unfold set_reg; cbn [sregs mem]. f_equal. apply register_set_pmpcfg_n_overwrite. Qed.

Definition pmpcfg0_vecupd (v : mword 64) (cfg : vec (mword 8) 64) (i : Z) : vec (mword 8) 64 :=
  vec_update_dec cfg (Z.add (Z.mul 0 4) i)
    (pmpWriteCfg_val (vec_access_dec cfg (Z.add (Z.mul 0 4) i))
       (autocast (T := mword) (subrange_vec_dec v (Z.add (Z.mul 8 i) 7) (Z.mul 8 i)))).

Definition pmpcfg0_finalvec (v : mword 64) (cfg0 : vec (mword 8) 64) : vec (mword 8) 64 :=
  pmpcfg0_vecupd v (pmpcfg0_vecupd v (pmpcfg0_vecupd v (pmpcfg0_vecupd v
    (pmpcfg0_vecupd v (pmpcfg0_vecupd v (pmpcfg0_vecupd v (pmpcfg0_vecupd v cfg0 0) 1) 2) 3) 4) 5) 6) 7.

Lemma pmp_cfg_step_on_set (v : mword 64) (s : mstate) (X : vec (mword 8) 64) (i : Z) :
  pmp_cfg_step v (set_reg s pmpcfg_n X) i = set_reg s pmpcfg_n (pmpcfg0_vecupd v X i).
Proof.
  unfold pmp_cfg_step, pmpcfg0_vecupd.
  rewrite !register_lookup_set. rewrite set_reg_pmpcfg_n_overwrite. reflexivity.
Qed.

Lemma pmpcfg0_final_collapse (v : mword 64) (s : mstate) :
  pmpcfg0_final v s = set_reg s pmpcfg_n (pmpcfg0_finalvec v (register_lookup pmpcfg_n s.(sregs))).
Proof.
  unfold pmpcfg0_final, pmpcfg0_finalvec.
  change (pmp_cfg_step v s 0)
    with (set_reg s pmpcfg_n (pmpcfg0_vecupd v (register_lookup pmpcfg_n s.(sregs)) 0)).
  rewrite !pmp_cfg_step_on_set. reflexivity.
Qed.

(* ---- pmpcfg0 forward/clean/wp: writes vec pmpcfg_n (= fetch frame) ---- *)
Definition sXcw_pc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) pmpcfg_n
    (pmpcfg0_finalvec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))
       (register_lookup pmpcfg_n (s_pccw s pc b).(sregs))).
Definition sTcw_pc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_pc s pc b rs1) PC (register_lookup nextPC (sXcw_pc s pc b rs1).(sregs)).
Definition sFcw_pc (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_pc s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_pc s pc b rs1).(sregs)) 1)
       else sTcw_pc s pc b rs1.

Section ForwardCsrwPmpcfg0.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_pmpcfg0 :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFcw_pc s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (HexecC : exec (execute (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_pc s pc b rs1)).
    { change (execute (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_pmpcfg0 (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_pmpcfg0 rs1 (s_pccw s pc b) Hrs1 LprivC).
      unfold sXcw_pc. rewrite pmpcfg0_final_collapse. reflexivity. }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_pc s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_pc s pc b rs1) (sAcw s b) w
               (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_pc s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_pc, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_pc, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwPmpcfg0.

Section CleanCsrwPmpcfg0.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_pc : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         pmpcfg_n
         (pmpcfg0_finalvec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))
            (register_lookup pmpcfg_n (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_pc : mstate :=
    if b then set_reg base_upd_cw_pc minstret (add_vec_int mst0 1) else base_upd_cw_pc.
  Lemma sFcw_pc_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_pc s pc b rs1 = sFccw_pc.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_pc s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_pc; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_pc s pc b rs1 = base_upd_cw_pc).
    { unfold sTcw_pc. rewrite Enpc. unfold sXcw_pc, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_pc, s_pccw, sAcw. reflexivity. }
    unfold sFcw_pc, sFccw_pc. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_pc.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_pc, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwPmpcfg0.

Section WpCsrwPmpcfg0.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_pmpcfg0_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0_finalvec vrs1 pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hpcv : register_lookup pmpcfg_n (s_pccw s pc b1).(sregs) = pmpcfg0)
      by (apply pmpcfg_n_s_pccw; exact Lpmpc).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_pc s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_pc_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_pmpcfg0 s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ pmpcfg_n _
            (pmpcfg0_finalvec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs))
               (register_lookup pmpcfg_n (s_pccw s pc b1).(sregs)))
            with "Hreg Hpmpc") as "[Hreg Hpmpc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hpcv Hrsv) in "Hpmpc".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_pc, base_upd_cw_pc. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwPmpcfg0.

Definition wp_csrw_pmpcfg0_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_pmpcfg0_gpr pc w (mword_of_int 5).

(* ===================================================================== *)
(* 2-ALIGNED fetch variants (_2): 4-byte CSR instr at addr%4=2 PCs.        *)
(* fetch_from_pts_minstret_2 (halfword PMA split + misa.C). forward/clean   *)
(* lemmas are REUSED unchanged.                                            *)
(* ===================================================================== *)
Section WpCsrw2.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_satp_gpr_2 (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mstatus0 satp0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ satp ↦ᵣ satp0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        satp ↦ᵣ satp_legalized satp0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS HSXL Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "Hpc Hfile Hsatp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hsatp")  as %Lsatp.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hsatpv : register_lookup satp (s_pccw s pc b1).(sregs) = satp0)
      by (apply satp_s_pccw; exact Lsatp).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_satp s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_satp_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_satp s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HSXL. }
    iIntros "!>".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ satp _
            (satp_legalized (register_lookup satp (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hsatp") as "[Hreg Hsatp]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hsatpv Hrsv) in "Hsatp".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_satp, base_upd_cw_satp. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hsatp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hsatp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrw2.

Section WpCsrw2More.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_medeleg_gpr_2 (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 medeleg0 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ medeleg ↦ᵣ medeleg0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        medeleg ↦ᵣ legalize_medeleg medeleg0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmde Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmde")   as %Lmde.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmdv : register_lookup medeleg (s_pccw s pc b1).(sregs) = medeleg0)
      by (apply medeleg_s_pccw; exact Lmde).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_medeleg s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS. }
    iIntros "!>".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ medeleg _
            (legalize_medeleg (register_lookup medeleg (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmde") as "[Hreg Hmde]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmdv Hrsv) in "Hmde".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw, base_upd_cw. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmde Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmde Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

  Lemma wp_csrw_mideleg_gpr_2 (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mideleg_legalized mdv0 vrs1 -∗
        (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmdv : register_lookup mideleg (s_pccw s pc b1).(sregs) = mdv0)
      by (apply mideleg_s_pccw; exact Lmdl).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_mid s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_mid_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_mideleg s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS. }
    iIntros "!>".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mideleg _
            (mideleg_legalized (register_lookup mideleg (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmdl") as "[Hreg Hmdl]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmdv Hrsv) in "Hmdl".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_mid, base_upd_cw_mid. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

  Lemma wp_csrw_sie_gpr_2 (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mie0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ mie ↦ᵣ mie0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        mie ↦ᵣ sie_new_mie mie0 mdv0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmie Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmie")   as %Lmie.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmiev : register_lookup mie (s_pccw s pc b1).(sregs) = mie0)
      by (apply mie_s_pccw; exact Lmie).
    assert (Hmdlv : register_lookup mideleg (s_pccw s pc b1).(sregs) = mdv0)
      by (apply mideleg_s_pccw; exact Lmdl).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_sie s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_sie_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_sie s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS. }
    iIntros "!>".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mie _
            (sie_new_mie (register_lookup mie (s_pccw s pc b1).(sregs))
               (register_lookup mideleg (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmie") as "[Hreg Hmie]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmiev Hmdlv Hrsv) in "Hmie".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_sie, base_upd_cw_sie. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmie Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmie Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

End WpCsrw2More.

Section WpCsrw2Pmp.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_pmpaddr0_gpr_2 (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr00 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "Hpc Hfile Hpa Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hpa")    as %Lpa.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hpav : register_lookup pmpaddr_n (s_pccw s pc b1).(sregs) = pmpaddr00)
      by (apply pmpaddr_n_s_pccw; exact Lpa).
    assert (Hpcv : register_lookup pmpcfg_n (s_pccw s pc b1).(sregs) = pmpcfg0)
      by (apply pmpcfg_n_s_pccw; exact Lpmpc).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_pa s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_pa_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_pmpaddr0 s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ pmpaddr_n _
            (pmp0_newaddr (register_lookup pmpcfg_n (s_pccw s pc b1).(sregs))
               (register_lookup pmpaddr_n (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hpa") as "[Hreg Hpa]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hpcv Hpav Hrsv) in "Hpa".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_pa, base_upd_cw_pa. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hpa Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hpa Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

End WpCsrw2Pmp.


(* ===================================================================== *)
(* menvcfg (0x30A) + stimecmp (0x14D): the last monadic-legalize boot   *)
(* CSRs. menvcfg legalize chains currentlyEnabled over Zicfilp/Zicfiss/  *)
(* Zicboz/Zicbom/Sstc/Smnpm/Svadu/Svpbmt + legalize_xenvcfg_cbie.        *)
(* stimecmp is Sstc-gated; legalize = update_subrange 63 0 (pure).       *)
(* NOTE: exec_hartSupports_Zicfilp is reused from WpDecode.v.            *)
(* ===================================================================== *)

Lemma exec_hartSupports_Zicfiss s : exec (hartSupports Ext_Zicfiss) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicfiss) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicboz s : exec (hartSupports Ext_Zicboz) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicboz) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicbom s : exec (hartSupports Ext_Zicbom) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicbom) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Sstc s : exec (hartSupports Ext_Sstc) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Smnpm s : exec (hartSupports Ext_Smnpm) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Smnpm) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  (* andb true (xlen==64) *)
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Svadu s : exec (hartSupports Ext_Svadu) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Svadu) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_hartSupports_Svpbmt s : exec (hartSupports Ext_Svpbmt) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Svpbmt) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

(* currentlyEnabled for the simple extensions (body = hartSupports X) *)
Lemma exec_currentlyEnabled_Zicboz s : exec (currentlyEnabled Ext_Zicboz) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicboz) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicboz.
Qed.

Lemma exec_currentlyEnabled_Zicbom s : exec (currentlyEnabled Ext_Zicbom) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicbom) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicbom.
Qed.

Lemma exec_currentlyEnabled_Sstc s : exec (currentlyEnabled Ext_Sstc) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Sstc.
Qed.

Lemma exec_currentlyEnabled_Smnpm s : exec (currentlyEnabled Ext_Smnpm) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Smnpm) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Smnpm.
Qed.

Lemma exec_currentlyEnabled_Svadu s : exec (currentlyEnabled Ext_Svadu) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svadu) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Svadu.
Qed.

(* reduce an inner `_rec_currentlyEnabled Ext_S k a` (concrete k) to misa.S
   (same as crush_rec_cE_S in WpGprCsrw, replicated here for the probe) *)
Ltac crush_inner_cE_S s :=
  match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
    let H := fresh "HSm" in
    assert (H : exec (_rec_currentlyEnabled Ext_S k a) s
                = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s));
    [ destruct a; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?kk 0] => replace (Z.geb kk 0) with true by reflexivity end;
      cbn match; rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match;
      rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)); cbn match;
      rewrite (exec_and_boolM_Some _ _ s
                 (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s);
      [ destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:?;
        [ match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
            exact (exec_rec_cE_Zicsr_any k2 a2 s ltac:(reflexivity)) end
        | reflexivity ]
      | rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)); apply exec_returnM ]
    | rewrite H ]
  end.

Lemma exec_currentlyEnabled_Svpbmt s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Svpbmt) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svpbmt) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Svpbmt s)). cbn match.
  (* inner rec cE Sv39 at concrete reclimit *)
  match goal with |- context[_rec_currentlyEnabled Ext_Sv39 ?k ?a] =>
    destruct a end.
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  match goal with |- context[Z.geb ?kk 0] => replace (Z.geb kk 0) with true by reflexivity end.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv39 s)). cbn match.
  crush_inner_cE_S s. rewrite HS. reflexivity.
Qed.

(* ===================================================================== *)
(* menvcfg (0x30A): legalize_menvcfg via the extension tower above       *)
(* ===================================================================== *)
Definition csr_menvcfg : mword 12 := mword_of_int 0x30a.

(* symbolic cbie legalization (pure: neq_vec test) *)
Definition menvcfg_cbie (v : mword 64) : mword 2 :=
  if neq_vec (_get_MEnvcfg_CBIE (Mk_MEnvcfg v)) ('b"10")
  then _get_MEnvcfg_CBIE (Mk_MEnvcfg v)
  else ('b"00").

Lemma exec_legalize_xenvcfg_cbie (cbie : mword 2) s :
  exec (legalize_xenvcfg_cbie cbie) s
    = Some (if neq_vec cbie ('b"10") then cbie else ('b"00"), s).
Proof.
  unfold legalize_xenvcfg_cbie.
  destruct (neq_vec cbie ('b"10")).
  - apply exec_returnM.
  - (* xenvcfg_cbie_reserved_behavior = Xenvcfg_ClearPermissions -> returnM 00 *)
    cbn match. apply exec_returnM.
Qed.

(* symbolic legalized menvcfg: all enabled extensions -> use v's field;
   STCE/PMM/ADUE/PBMTE per the legalize result. *)
Definition menvcfg_legalized (o v : mword 64) : mword 64 :=
  let v' := Mk_MEnvcfg v in
  _update_MEnvcfg_PBMTE
    (_update_MEnvcfg_ADUE
       (_update_MEnvcfg_PMM
          (_update_MEnvcfg_STCE
             (_update_MEnvcfg_CBIE
                (_update_MEnvcfg_CBCFE
                   (_update_MEnvcfg_CBZE
                      (_update_MEnvcfg_SSE
                         (_update_MEnvcfg_LPE
                            (_update_MEnvcfg_FIOM o
                               (if sys_enable_writable_fiom then _get_MEnvcfg_FIOM v' else ('b"0")))
                            (_get_MEnvcfg_LPE v'))
                         (_get_MEnvcfg_SSE v'))
                      (_get_MEnvcfg_CBZE v'))
                   (_get_MEnvcfg_CBCFE v'))
                (menvcfg_cbie v))
             (_get_MEnvcfg_STCE v'))
          (if andb true (is_supported_pmm PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM v')))
           then _get_MEnvcfg_PMM v' else _get_MEnvcfg_PMM o))
       (_get_MEnvcfg_ADUE v'))
    (_get_MEnvcfg_PBMTE v').

Lemma exec_legalize_menvcfg (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_menvcfg o v) s = Some (menvcfg_legalized o v, s).
Proof.
  intro HS. unfold legalize_menvcfg, menvcfg_legalized, menvcfg_cbie.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zicfiss s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicboz s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicbom s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicbom s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_xenvcfg_cbie (_get_MEnvcfg_CBIE (Mk_MEnvcfg v)) s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Sstc s)). cbn match.
  (* and_boolM (cE Smnpm) (returnM (is_supported_pmm ...)) *)
  match goal with |- context[Defs.and_boolM ?l ?r] =>
    assert (Hsm : exec (Defs.and_boolM l r) s
                  = Some (andb true (is_supported_pmm PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM (Mk_MEnvcfg v)))), s)) end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Smnpm s)). cbn match.
    apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hsm). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svpbmt s HS)). cbn match.
  apply exec_returnM.
Qed.

Lemma exec_write_CSR_menvcfg (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_menvcfg v) s
    = Some (Ok (menvcfg_legalized (register_lookup menvcfg s.(sregs)) v),
            set_reg s menvcfg (menvcfg_legalized (register_lookup menvcfg s.(sregs)) v)).
Proof.
  intro HS. unfold write_CSR.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_legalize_menvcfg (register_lookup menvcfg s.(sregs)) v s HS)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg menvcfg _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_menvcfg (d : mword 64) s :
  exec (csr_id_write_callback csr_menvcfg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_menvcfg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_menvcfg s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (is_CSR_accessible csr_menvcfg Machine CSRWrite) s = Some (true, s).
Proof.
  intro HU. unfold is_CSR_accessible.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  apply (exec_currentlyEnabled_U s HU).
Qed.

Lemma exec_execute_csrw_menvcfg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_menvcfg (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s menvcfg
              (menvcfg_legalized (register_lookup menvcfg s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS HU.
  apply (exec_execute_csrw_gpr csr_menvcfg rs1 s _
           (menvcfg_legalized (register_lookup menvcfg s.(sregs))
              (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_U csr_menvcfg s HU);
      [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_menvcfg; assumption.
  - apply exec_csr_id_write_callback_menvcfg.
Qed.

(* ---- menvcfg forward/clean/wp: writes menvcfg; reads misa.S/.U, mstatus.MIE ---- *)
Definition sXcw_menvcfg (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) menvcfg
    (menvcfg_legalized (register_lookup menvcfg (s_pccw s pc b).(sregs))
       (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_menvcfg (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_menvcfg s pc b rs1) PC (register_lookup nextPC (sXcw_menvcfg s pc b rs1).(sregs)).
Definition sFcw_menvcfg (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_menvcfg s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_menvcfg s pc b rs1).(sregs)) 1)
       else sTcw_menvcfg s pc b rs1.

Lemma menvcfg_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup menvcfg s.(sregs) = v ->
  register_lookup menvcfg (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwMenvcfg.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_menvcfg :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFcw_menvcfg s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LmIE Lelp LS LU.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (LSC : eq_vec (_get_Misa_S (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LS. }
    assert (LUC : eq_vec (_get_Misa_U (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LU. }
    assert (HexecC : exec (execute (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_menvcfg s pc b rs1)).
    { change (execute (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_menvcfg (Regidx rs1) zreg CSRRW).
      unfold sXcw_menvcfg. exact (exec_execute_csrw_menvcfg rs1 (s_pccw s pc b) Hrs1 LprivC LSC LUC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_menvcfg s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_menvcfg s pc b rs1) (sAcw s b) w
               (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_menvcfg s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_menvcfg, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_menvcfg, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwMenvcfg.

Section CleanCsrwMenvcfg.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_menvcfg : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         menvcfg
         (menvcfg_legalized (register_lookup menvcfg (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_menvcfg : mstate :=
    if b then set_reg base_upd_cw_menvcfg minstret (add_vec_int mst0 1) else base_upd_cw_menvcfg.
  Lemma sFcw_menvcfg_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_menvcfg s pc b rs1 = sFccw_menvcfg.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_menvcfg s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_menvcfg; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_menvcfg s pc b rs1 = base_upd_cw_menvcfg).
    { unfold sTcw_menvcfg. rewrite Enpc. unfold sXcw_menvcfg, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_menvcfg, s_pccw, sAcw. reflexivity. }
    unfold sFcw_menvcfg, sFccw_menvcfg. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_menvcfg.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_menvcfg, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwMenvcfg.

Section WpCsrwMenvcfg.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_menvcfg_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mstatus0 menvcfg0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ menvcfg ↦ᵣ menvcfg0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        menvcfg ↦ᵣ menvcfg_legalized menvcfg0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS HU Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmenvcfg Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmenvcfg") as %Lmenvcfg.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmenvcfgv : register_lookup menvcfg (s_pccw s pc b1).(sregs) = menvcfg0)
      by (apply menvcfg_s_pccw; exact Lmenvcfg).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_menvcfg s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_menvcfg_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_menvcfg s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS.
      - rewrite Lmisa. exact HU. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ menvcfg _
            (menvcfg_legalized (register_lookup menvcfg (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmenvcfg") as "[Hreg Hmenvcfg]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmenvcfgv Hrsv) in "Hmenvcfg".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_menvcfg, base_upd_cw_menvcfg. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmenvcfg Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmenvcfg Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwMenvcfg.

Definition wp_csrw_menvcfg_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_menvcfg_gpr pc w (mword_of_int 5).

(* ===================================================================== *)
(* stimecmp (0x14D): Sstc-gated; legalize = update_subrange 63 0 (pure)  *)
(* ===================================================================== *)
Definition csr_stimecmp : mword 12 := mword_of_int 0x14d.

Definition stimecmp_legalized (prev v : mword 64) : mword 64 :=
  update_subrange_vec_dec prev (Z.sub xlen 1) 0 v.

Lemma exec_is_stimecmp_accessible_M s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (is_stimecmp_accessible Machine) s = Some (true, s).
Proof.
  intro HS. unfold is_stimecmp_accessible.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Sstc s)). cbn match.
  apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_stimecmp s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (is_CSR_accessible csr_stimecmp Machine CSRWrite) s = Some (true, s).
Proof.
  intro HS. unfold is_CSR_accessible.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  apply (exec_is_stimecmp_accessible_M s HS).
Qed.

Lemma exec_write_CSR_stimecmp (v : mword 64) s :
  exec (write_CSR csr_stimecmp v) s
    = Some (Ok (subrange_vec_dec (stimecmp_legalized (register_lookup stimecmp s.(sregs)) v) (Z.sub xlen 1) 0),
            set_reg s stimecmp (stimecmp_legalized (register_lookup stimecmp s.(sregs)) v)).
Proof.
  unfold write_CSR, stimecmp_legalized.
  repeat (erewrite exec_if_false_g by (vm_compute; reflexivity)).
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg stimecmp s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg stimecmp _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg stimecmp _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

Lemma exec_csr_id_write_callback_stimecmp (d : mword 64) s :
  exec (csr_id_write_callback csr_stimecmp d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_stimecmp d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrw_stimecmp (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS,
            set_reg s stimecmp
              (stimecmp_legalized (register_lookup stimecmp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS.
  apply (exec_execute_csrw_gpr csr_stimecmp rs1 s _
           (subrange_vec_dec (stimecmp_legalized (register_lookup stimecmp s.(sregs))
              (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))) (Z.sub xlen 1) 0)).
  - exact Hrs1.
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw csr_stimecmp s).
    apply exec_check_CSR_csrw;
      [ vm_compute; reflexivity
      | vm_compute; reflexivity
      | apply (exec_is_CSR_accessible_stimecmp s HS)
      | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_stimecmp.
  - apply exec_csr_id_write_callback_stimecmp.
Qed.

(* ---- stimecmp forward/clean/wp: writes stimecmp; reads misa.S, mstatus.MIE ---- *)
Definition sXcw_stimecmp (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (s_pccw s pc b) stimecmp
    (stimecmp_legalized (register_lookup stimecmp (s_pccw s pc b).(sregs))
       (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))).
Definition sTcw_stimecmp (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  set_reg (sXcw_stimecmp s pc b rs1) PC (register_lookup nextPC (sXcw_stimecmp s pc b rs1).(sregs)).
Definition sFcw_stimecmp (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) : mstate :=
  if b then set_reg (sTcw_stimecmp s pc b rs1) minstret
                (add_vec_int (register_lookup minstret (sTcw_stimecmp s pc b rs1).(sregs)) 1)
       else sTcw_stimecmp s pc b rs1.

Lemma stimecmp_s_pccw (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
  register_lookup stimecmp s.(sregs) = v ->
  register_lookup stimecmp (s_pccw s pc b).(sregs) = v.
Proof.
  intro H. unfold s_pccw, sAcw, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact H.
Qed.

Section ForwardCsrwStimecmp.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW), s0).

  Lemma forward_exec_csrw_stimecmp :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFcw_stimecmp s pc b rs1).
  Proof using All.
    intros Lpc Lpriv Lhs LmIE Lelp LS.
    assert (LpcA : register_lookup PC (sAcw s b).(sregs) = pc).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege (sAcw s b).(sregs) = Machine).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA : register_lookup hart_state (sAcw s b).(sregs) = HART_ACTIVE tt).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAcw s b).(sregs))) ('b"1") = true).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) (sAcw s b).(sregs))) ('b"1") = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp (sAcw s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAcw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) (sAcw s b) = Some (None, (sAcw s b))).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none (sAcw s b) _ (exec_currentlyEnabled_S (sAcw s b)) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) (sAcw s b) = Some (F_Base w, (sAcw s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) (sAcw s b) = Some (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW), (sAcw s b)))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege (s_pccw s pc b).(sregs) = Machine).
    { unfold s_pccw, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (LSC : eq_vec (_get_Misa_S (register_lookup misa (s_pccw s pc b).(sregs))) ('b"1") = true).
    { unfold s_pccw, sAcw, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact LS. }
    assert (HexecC : exec (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW))) (s_pccw s pc b)
              = Some (RETIRE_SUCCESS, sXcw_stimecmp s pc b rs1)).
    { change (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW).
      unfold sXcw_stimecmp. exact (exec_execute_csrw_stimecmp rs1 (s_pccw s pc b) Hrs1 LprivC LSC). }
    assert (Hha : exec (run_hart_active 0) (sAcw s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXcw_stimecmp s pc b rs1)).
    { exact (exec_hart_active_progress (sAcw s b) (sAcw s b) (sXcw_stimecmp s pc b rs1) (sAcw s b) w
               (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s (sXcw_stimecmp s pc b rs1) w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXcw_stimecmp, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXcw_stimecmp, s_pccw, sAcw; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrwStimecmp.

Section CleanCsrwStimecmp.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (mst0 : mword 64).
  Definition base_upd_cw_stimecmp : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         stimecmp
         (stimecmp_legalized (register_lookup stimecmp (s_pccw s pc b).(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b).(sregs))))
      PC (add_vec_int pc 4).
  Definition sFccw_stimecmp : mstate :=
    if b then set_reg base_upd_cw_stimecmp minstret (add_vec_int mst0 1) else base_upd_cw_stimecmp.
  Lemma sFcw_stimecmp_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFcw_stimecmp s pc b rs1 = sFccw_stimecmp.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXcw_stimecmp s pc b rs1).(sregs) = add_vec_int pc 4).
    { unfold sXcw_stimecmp; cbv zeta. unfold set_reg; cbn [sregs].
      tmiw. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTcw_stimecmp s pc b rs1 = base_upd_cw_stimecmp).
    { unfold sTcw_stimecmp. rewrite Enpc. unfold sXcw_stimecmp, s_pccw, sAcw; cbv zeta.
      unfold base_upd_cw_stimecmp, s_pccw, sAcw. reflexivity. }
    unfold sFcw_stimecmp, sFccw_stimecmp. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_cw_stimecmp.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_cw_stimecmp, set_reg; cbn [sregs]. tmiw. tmiw. tmiw. tmiw. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrwStimecmp.

Section WpCsrwStimecmp.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_stimecmp_gpr (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mstatus0 stimecmp0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ stimecmp ↦ᵣ stimecmp0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        stimecmp ↦ᵣ stimecmp_legalized stimecmp0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hstimecmp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hstimecmp") as %Lstimecmp.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hstimecmpv : register_lookup stimecmp (s_pccw s pc b1).(sregs) = stimecmp0)
      by (apply stimecmp_s_pccw; exact Lstimecmp).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_stimecmp s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_stimecmp_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_stimecmp s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ stimecmp _
            (stimecmp_legalized (register_lookup stimecmp (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hstimecmp") as "[Hreg Hstimecmp]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hstimecmpv Hrsv) in "Hstimecmp".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_stimecmp, base_upd_cw_stimecmp. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hstimecmp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hstimecmp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrwStimecmp.

Definition wp_csrw_stimecmp_x5 `{!riscvGS Σ} (pc : mword 64) (w : mword 32) := wp_csrw_stimecmp_gpr pc w (mword_of_int 5).


(* ===================================================================== *)
(* 2-ALIGNED variants: menvcfg (0x8000002e) + mcounteren (0x8000003a)   *)
(* in timerinit land at addr%4=2. Mechanical _2 transform of the        *)
(* 4-aligned WPs: fetch_from_pts_minstret -> _2, halfword PMA split +    *)
(* misa.C hyps + misa iEval dance. forward/clean lemmas reused unchanged. *)
(* ===================================================================== *)
Section WpCsrw2Probe.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_menvcfg_gpr_2 (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mstatus0 menvcfg0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ menvcfg ↦ᵣ menvcfg0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        menvcfg ↦ᵣ menvcfg_legalized menvcfg0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS HU Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmenvcfg Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmenvcfg") as %Lmenvcfg.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmenvcfgv : register_lookup menvcfg (s_pccw s pc b1).(sregs) = menvcfg0)
      by (apply menvcfg_s_pccw; exact Lmenvcfg).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_menvcfg s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_menvcfg_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_menvcfg s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HS.
      - rewrite Lmisa. exact HU. }
    iIntros "!>".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ menvcfg _
            (menvcfg_legalized (register_lookup menvcfg (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmenvcfg") as "[Hreg Hmenvcfg]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmenvcfgv Hrsv) in "Hmenvcfg".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_menvcfg, base_upd_cw_menvcfg. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmenvcfg Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmenvcfg Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrw2Probe.

Section WpCsrw2ProbeMc.
  Context `{!riscvGS Σ}.
  Lemma wp_csrw_mcounteren_gpr_2 (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vrs1 misa0 mdv0 : mword 64) (mcounteren0 : mword 32)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rs1 <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some vrs1 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ mcounteren ↦ᵣ mcounteren0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗ gpr_file m -∗
        mcounteren ↦ᵣ legalize_mcounteren mcounteren0 vrs1 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hm HS HU Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "Hpc Hfile Hmc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmc")    as %Lmcen.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hfile") as "[Hrs1c Hfins]".
    iDestruct (reg_valid with "Hreg Hrs1c")  as %Lrs1.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hmcv : register_lookup mcounteren (s_pccw s pc b1).(sregs) = mcounteren0)
      by (apply mcounteren_s_pccw; exact Lmcen).
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs) = vrs1)
      by (apply gpr_s_pccw; exact Lrs1).
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFccw_mc s pc b1 rs1 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFcw_mc_eq s pc b1 rs1 mst0 Lpc Lmst).
      apply (forward_exec_csrw_mcounteren s pc b1 w rs1 Hfetch_at Hsi_s Hrs1 Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HU. }
    iIntros "!>".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mcounteren _
            (legalize_mcounteren (register_lookup mcounteren (s_pccw s pc b1).(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (s_pccw s pc b1).(sregs)))
            with "Hreg Hmc") as "[Hreg Hmc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmcv Hrsv) in "Hmc".
    iDestruct ("Hfins" with "Hrs1c") as "Hfile".
    unfold sFccw_mc, base_upd_cw_mc. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrw2ProbeMc.
