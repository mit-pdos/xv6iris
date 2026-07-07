From Stdlib Require Import ZArith.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
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

(* execute_CSRReg for csrw (rd=x0=zreg, op=CSRRW): reads rs1 (generic -- rs1=0
   is a legitimate "write literal 0" and is handled like any other index, by
   baking the same if-guard [rX_bits] itself uses directly into the [write_CSR]
   premise, rather than imposing a [uint rs1 <> 0] side condition). *)
Lemma exec_execute_csrw_gpr (csr : mword 12) (rs1 : mword 5) (s s' : mstate) (cfinal : mword 64) :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr Machine CSRWrite) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Machine CSRWrite = true ->
  eq_vec csr (Ox"344") = false ->
  eq_vec csr (Ox"144") = false ->
  exec (write_CSR csr (if Z.eqb (uint rs1) 0 then zero_reg
                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))) s
    = Some (Ok cfinal, s') ->
  exec (csr_id_write_callback csr cfinal) s' = Some (tt, s') ->
  exec (execute_CSRReg csr (Regidx rs1) zreg CSRRW) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hpriv Hchk Hext H344 H144 Hwr Hcb.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRW (generic_eq zreg zreg) (generic_eq (Regidx rs1) zreg))
    with CSRWrite by (replace (generic_eq zreg zreg) with true by reflexivity; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  apply (exec_doCSR_csrw csr _ s s' cfinal); assumption.
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

Lemma exec_hartSupports_Sstc s : exec (hartSupports Ext_Sstc) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Sstc s : exec (currentlyEnabled Ext_Sstc) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Sstc.
Qed.
