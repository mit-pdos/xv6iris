From Stdlib Require Import Eqdep_dec ZArith Lia FunctionalExtensionality.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr.
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

(* ---- clean-form post-state for csrw medeleg (for the Iris WP layer) ---- *)


(* Demonstration: ONE engine serves many CSRs/source regs. *)

(* ====================================================================== *)
(* mcounteren (0x306, Ext_U, legalize_mcounteren) — full forward + wp.      *)
(* Reuses the CSR-agnostic sAcw/s_pccw/gpr_s_pccw from the medeleg block.   *)
(* ====================================================================== *)


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


Lemma pmp_cfg_step_on_set (v : mword 64) (s : mstate) (X : vec (mword 8) 64) (i : Z) :
  pmp_cfg_step v (set_reg s pmpcfg_n X) i = set_reg s pmpcfg_n (pmpcfg0_vecupd v X i).
Proof.
  unfold pmp_cfg_step, pmpcfg0_vecupd.
  rewrite !register_lookup_set. rewrite set_reg_pmpcfg_n_overwrite. reflexivity.
Qed.


(* ---- pmpcfg0 forward/clean/wp: writes vec pmpcfg_n (= fetch frame) ---- *)


(* ===================================================================== *)
(* 2-ALIGNED fetch variants (_2): 4-byte CSR instr at addr%4=2 PCs.        *)
(* fetch_from_pts_minstret_2 (halfword PMA split + misa.C). forward/clean   *)
(* lemmas are REUSED unchanged.                                            *)
(* ===================================================================== *)


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

(* ====================================================================== *)
(* NEW-STYLE register-generic CSR-WRITE WPs (csrw csr, rs1 = csrrw x0,csr,rs1) *)
(* on the [instr] / [mmode_config] / [gpr_file] layer, built on [wp_instr]. *)
(* Dual of [wp_csrr_mhartid_gpr]: reads rs1 off the [gpr_file] and WRITES    *)
(* the CSR cell, which is threaded as an extra points-to premise (old value  *)
(* in, new/legalized value out).  Reuses the representation-independent      *)
(* execute helpers [exec_execute_csrw_*] verbatim.  A HALF of [mmode_config] *)
(* is kept to recover cur_privilege = Machine (and, where the execute        *)
(* legalizes with misa.S/misa.U or mstatus.SXL, those facts from hw_config / *)
(* the kept mstatus) at the execute state; the halves are recombined for the *)
(* continuation.                                                             *)
(* ====================================================================== *)



Section WpCsrwGprNew.
  Context `{!riscvGS Σ}.
  (* ---- medeleg (Ext_S, pure legalize) ---- *)
  Lemma wp_csrw_medeleg_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (medeleg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    medeleg ↦ᵣ medeleg0 -∗
    instr pc false (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      medeleg ↦ᵣ legalize_medeleg medeleg0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    (* config facts at s_pc *)
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup medeleg s_pc.(sregs) = medeleg0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    (* write medeleg *)
    iMod (reg_update _ medeleg _ (legalize_medeleg medeleg0 (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc medeleg (legalize_medeleg medeleg0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_medeleg (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_medeleg rs1 s_pc Hrs1 Lprivp
                 ltac:(rewrite Lmisap; exact HmisaS)).
      rewrite Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc medeleg (legalize_medeleg medeleg0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- mideleg ---- *)
  Lemma wp_csrw_mideleg_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (mideleg0 : type_of_register mideleg)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mideleg ↦ᵣ mideleg0 -∗
    instr pc false (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mideleg ↦ᵣ mideleg_legalized mideleg0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup mideleg s_pc.(sregs) = mideleg0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ mideleg _ (mideleg_legalized mideleg0 (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc mideleg (mideleg_legalized mideleg0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mideleg (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_mideleg rs1 s_pc Hrs1 Lprivp
                 ltac:(rewrite Lmisap; exact HmisaS)).
      rewrite ?Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc mideleg (mideleg_legalized mideleg0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- stimecmp ---- *)
  Lemma wp_csrw_stimecmp_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (stimecmp0 : type_of_register stimecmp)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    instr pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup stimecmp s_pc.(sregs) = stimecmp0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ stimecmp _ (stimecmp_legalized stimecmp0 (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc stimecmp (stimecmp_legalized stimecmp0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_stimecmp rs1 s_pc Hrs1 Lprivp
                 ltac:(rewrite Lmisap; exact HmisaS)).
      rewrite ?Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc stimecmp (stimecmp_legalized stimecmp0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- mcounteren ---- *)
  Lemma wp_csrw_mcounteren_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (mcounteren0 : type_of_register mcounteren)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    instr pc false (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mcounteren ↦ᵣ legalize_mcounteren mcounteren0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup mcounteren s_pc.(sregs) = mcounteren0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ mcounteren _ (legalize_mcounteren mcounteren0 (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc mcounteren (legalize_mcounteren mcounteren0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mcounteren (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_mcounteren_full rs1 s_pc Hrs1 Lprivp
                 ltac:(rewrite Lmisap; exact HmisaU)).
      rewrite ?Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc mcounteren (legalize_mcounteren mcounteren0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- menvcfg ---- *)
  Lemma wp_csrw_menvcfg_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (menvcfg0 : type_of_register menvcfg)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    instr pc false (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      menvcfg ↦ᵣ menvcfg_legalized menvcfg0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ menvcfg _ (menvcfg_legalized menvcfg0 (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc menvcfg (menvcfg_legalized menvcfg0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_menvcfg (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_menvcfg rs1 s_pc Hrs1 Lprivp
                 ltac:(rewrite Lmisap; exact HmisaS)
                 ltac:(rewrite Lmisap; exact HmisaU)).
      rewrite ?Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc menvcfg (menvcfg_legalized menvcfg0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- mepc ---- *)
  Lemma wp_csrw_mepc_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (mepc0 : type_of_register mepc)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mepc ↦ᵣ mepc0 -∗
    instr pc false (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mepc ↦ᵣ mepc_val (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup mepc s_pc.(sregs) = mepc0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ mepc _ (mepc_val (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc mepc (mepc_val (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mepc (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_mepc rs1 s_pc Hrs1 Lprivp).
      rewrite ?Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc mepc (mepc_val (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* ---- mscratch ---- *)
  Lemma wp_csrw_mscratch_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (mscratch0 : type_of_register mscratch)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mscratch ↦ᵣ mscratch0 -∗
    instr pc false (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mscratch ↦ᵣ (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup mscratch s_pc.(sregs) = mscratch0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ mscratch _ (m !!! Regidx rs1)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc mscratch (m !!! Regidx rs1)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_mscratch, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mscratch (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_mscratch rs1 s_pc Hrs1 Lprivp).
      rewrite ?Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc mscratch (m !!! Regidx rs1)).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- sie (Ext_S): writes mie; value reads old mie + old mideleg ---- *)
  Lemma wp_csrw_sie_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (mie0 mideleg0 : type_of_register mie)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mie ↦ᵣ mie0 -∗
    mideleg ↦ᵣ mideleg0 -∗
    instr pc false (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mie ↦ᵣ sie_new_mie mie0 mideleg0 (m !!! Regidx rs1) -∗
      mideleg ↦ᵣ mideleg0 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hmie Hmdl Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid    with "Hreg Hmdl")     as %Lmdl.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmiep : register_lookup mie s_pc.(sregs) = mie0)
      by (unfold s_pc; tmig; exact Lmie).
    assert (Lmdlp : register_lookup mideleg s_pc.(sregs) = mideleg0)
      by (unfold s_pc; tmig; exact Lmdl).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ mie _ (sie_new_mie mie0 mideleg0 (m !!! Regidx rs1))
            with "Hreg Hmie") as "[Hreg Hmie]".
    iModIntro.
    iExists (set_reg s_pc mie (sie_new_mie mie0 mideleg0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_sie (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_sie rs1 s_pc Hrs1 Lprivp
                 ltac:(rewrite Lmisap; exact HmisaS)).
      rewrite Lmiep Lmdlp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc mie (sie_new_mie mie0 mideleg0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hmie Hmdl").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- satp (Ext_S, mstatus.SXL=SXLEN64): the SXL fact is drawn from the
     kept-half [mstatus] (mstatus.SXL is part of the mmode_config mstatus). ---- *)
  Lemma wp_csrw_satp_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (satp0 : type_of_register satp)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    satp ↦ᵣ satp0 -∗
    instr pc false (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      satp ↦ᵣ satp_legalized satp0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms_k")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lcsrp : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ satp _ (satp_legalized satp0 (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc satp (satp_legalized satp0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_satp (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_satp rs1 s_pc Hrs1 Lprivp
                 ltac:(rewrite Lmisap; exact HmisaS)
                 ltac:(rewrite Lmsp; exact HSXL)).
      rewrite Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc satp (satp_legalized satp0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- pmpaddr0 (pure): writes pmpaddr_n; value reads old pmpaddr_n AND
     pmpcfg_n.  pmpcfg_n is held (read-only) by [wp_instr] at the split
     fraction; we recover its value at the execute state via a kept half. ---- *)
  Lemma wp_csrw_pmpaddr0_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (pmpaddr0 : type_of_register pmpaddr_n)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    pmpaddr_n ↦ᵣ pmpaddr0 -∗
    instr pc false (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrs1) "Hmm [Hpmpc_wp Hpmpc_k] [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k") as %Lpmpc.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lcsrp : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m !!! Regidx rs1).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ pmpaddr_n _ (pmp0_newaddr pmpcfg0 pmpaddr0 (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iModIntro.
    iExists (set_reg s_pc pmpaddr_n (pmp0_newaddr pmpcfg0 pmpaddr0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_pmpaddr0 (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_pmpaddr0 rs1 s_pc Hrs1 Lprivp).
      rewrite Lpmpcp Lcsrp Lrs1p. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc pmpaddr_n (pmp0_newaddr pmpcfg0 pmpaddr0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpCsrwGprNew.

(* Demonstration: each ONE register-generic csrw WP serves any source reg. *)
Section WpCsrwGprNewDemo.
  Context `{!riscvGS Σ}.
  (* csrw medeleg, x5  and  csrw mepc, x28  (source register generalized) *)
  Definition wp_csrw_medeleg_x5 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_csrw_medeleg_gpr E Φ pc (mword_of_int 5).
  Definition wp_csrw_mepc_x28 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_csrw_mepc_gpr E Φ pc (mword_of_int 28).
  Definition wp_csrw_satp_x5 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_csrw_satp_gpr E Φ pc (mword_of_int 5).
  Goal gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 5 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpCsrwGprNewDemo.
