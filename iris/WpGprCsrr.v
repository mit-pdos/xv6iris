From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.

(* [subrange_vec_dec a (xlen-1) 0] extracts all 64 bits of a 64-bit word -- a
   noop (cf. WpGprLoad.subrange_id, but stated with the [Z.sub xlen 1] form the
   CSR reads use).  Lets the CSR-read WPs state the read value without the
   subrange. *)
Lemma subrange64_id (a : mword 64) : subrange_vec_dec a (Z.sub xlen 1) 0 = a.
Proof.
  apply bv_eq. unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (Z.sub xlen 1 - 0 + 1)) with 64%N.
  apply bv_wrap_bv_unsigned.
Qed.

(* ====================================================================== *)
(* Register-generic CSR-read execute: csrr rd, mhartid (= csrrs rd,mhartid,x0).*)
(* The CSR read (mhartid) and the x0 source stay fixed; only the           *)
(* destination [rd] is generalized.  CSRRS with a zero source always yields  *)
(* access type CSRRead, independent of rd.                                   *)
(* ====================================================================== *)
Lemma csr_access_type_CSRRS_true (b : bool) : csr_access_type CSRRS b true = CSRRead.
Proof. destruct b; reflexivity. Qed.

Lemma exec_execute_CSRReg_gpr_aux (rd : mword 5) s s_w :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (wX_bits (Regidx rd) (register_lookup mhartid s.(sregs))) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr_csrr zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Hpriv Hwx.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRS (generic_eq (Regidx rd) zreg)
             (generic_eq zreg zreg)) with CSRRead
    by (replace (generic_eq zreg zreg) with true by (vm_compute; reflexivity);
        symmetry; apply csr_access_type_CSRRS_true).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x0 (zero_extend' 5 ('b"00")) s ltac:(vm_compute; reflexivity))).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_csrr s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  replace (not (ext_check_CSR csr_csrr Machine CSRRead)) with false
    by (vm_compute; reflexivity).
  replace (if generic_neq CSRRead CSRWrite then read_CSR csr_csrr else returnM (zeros' 64))
    with (read_CSR csr_csrr) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_csrr s)).
  match goal with |- exec (Defs.bind ?D ?K) s = _ =>
    replace D with (returnM (register_lookup mhartid s.(sregs)) : M (mword 64))
      by (vm_compute; reflexivity) end.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (register_lookup mhartid s.(sregs)) s)).
  replace (generic_eq CSRRead CSRRead) with true by reflexivity.
  rewrite (exec_bind0_Some _ _ _ _ _ (_ :
    exec (Defs.bind0 (csr_id_read_callback csr_csrr (register_lookup mhartid s.(sregs)))
            (wX_bits (Regidx rd) (register_lookup mhartid s.(sregs)))) s
      = Some (tt, s_w))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
        (exec_csr_id_read_callback_csrr s (register_lookup mhartid s.(sregs)))).
      exact Hwx. }
  apply exec_returnM.
Qed.

Lemma exec_execute_CSRReg_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_csrr zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup mhartid s.(sregs)))).
Proof.
  intros Hrd Hpriv.
  apply (exec_execute_CSRReg_gpr_aux rd s
           (set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup mhartid s.(sregs)))) Hpriv).
  rewrite (exec_wX_bits_gpr rd (register_lookup mhartid s.(sregs)) s).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  reflexivity.
Qed.

(* mhartid is untouched by [set_reg _ nextPC _], so its value carries into the
   execute state unchanged. *)
Lemma mhartid_set_nextPC (s : mstate) (v : mword 64) :
  register_lookup mhartid (set_reg s nextPC v).(sregs)
  = register_lookup mhartid s.(sregs).
Proof.
  unfold set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ].
Qed.

(* ====================================================================== *)
(* Representation-independent CSR-read execute helpers, ported (verbatim in  *)
(* their pure content) from the old WpGprCsrrAny.v.  They reduce             *)
(* [execute_CSRReg csr x0 rd CSRRS] to a single [wX rd (read_CSR csr)] write, *)
(* per CSR (mstatus / mcounteren / menvcfg / sie / time).  The new-style WPs  *)
(* below feed these to [wp_instr]'s execute obligation.                       *)
(* ====================================================================== *)

(* Generic register-generic CSR-read step: csrr rd, csr  (= csrrs rd,csr,rs1z
   with rs1z = x0).  Parameterised over the CSR; the per-CSR facts
   (accessibility, read value, callback) are supplied as hypotheses. *)
Lemma csrr_read_step (csr : mword 12) (rd : mword 5) (readval : mword 64) (s s_w : mstate) :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr Machine CSRRead) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Machine CSRRead = true ->
  exec (read_CSR csr) s = Some (readval, s) ->
  eq_vec csr ((Ox"344") : mword 12) = false ->
  eq_vec csr ((Ox"144") : mword 12) = false ->
  exec (csr_id_read_callback csr readval) s = Some (tt, s) ->
  exec (wX_bits (Regidx rd) readval) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr zreg (Regidx rd) CSRRS) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Hpriv Hchk Hext Hread H344 H144 Hcb Hwx.
  unfold execute_CSRReg.
  replace (generic_eq zreg zreg) with true by (vm_compute; reflexivity).
  rewrite csr_access_type_CSRRS_true.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x0 (zero_extend' 5 ('b"00")) s ltac:(vm_compute; reflexivity))).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hext. cbn match.
  replace (if generic_neq CSRRead CSRWrite then read_CSR csr else returnM (zeros' 64))
    with (read_CSR csr) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hread).
  rewrite H344. rewrite H144. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM readval s)).
  replace (generic_eq CSRRead CSRRead) with true by reflexivity. cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
    (_ : exec (Defs.bind0 (csr_id_read_callback csr readval) (wX_bits (Regidx rd) readval)) s
         = Some (tt, s_w))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _ Hcb). exact Hwx. }
  apply exec_returnM.
Qed.

(* ===== mstatus (0x300): machine CSR, accessible (vm), read = subrange ===== *)
Definition csr_mstatus : mword 12 := Ox"300".
Definition mstatus_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup mstatus s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_read_CSR_mstatus s :
  exec (read_CSR csr_mstatus) s = Some (mstatus_rdval s, s).
Proof.
  unfold read_CSR, csr_mstatus, mstatus_rdval.
  replace (eq_vec (Ox"300" : mword 12) (Ox"301")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (andb (Z.eqb xlen 64) (eq_vec (Ox"300" : mword 12) (Ox"300"))) with true
    by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_mstatus s :
  exec (check_CSR_result csr_mstatus Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  unfold check_CSR_result, csr_mstatus.
  assert (H : check_CSR (Ox"300") Machine CSRRead = returnM true) by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (check_CSR (Ox"300") Machine CSRRead) s = Some (true, s))).
  2:{ rewrite H. apply exec_returnm. }
  apply (exec_returnM (CSR_Check_OK tt) s).
Qed.

Lemma exec_csr_id_read_callback_mstatus s d :
  exec (csr_id_read_callback csr_mstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_mstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_mstatus_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_mstatus zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mstatus_rdval s))).
Proof.
  intros Hrd Hpriv.
  apply (csrr_read_step csr_mstatus rd (mstatus_rdval s) s _ Hpriv).
  - apply exec_check_CSR_result_mstatus.
  - vm_compute; reflexivity.
  - apply exec_read_CSR_mstatus.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_mstatus.
  - rewrite (exec_wX_bits_gpr rd (mstatus_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* Walk the [read_CSR] dispatch; see WpGprCsrrAny provenance / build-perf note. *)
Ltac drive_csr :=
  unfold read_CSR;
  repeat first
    [ erewrite exec_if_false_g by (vm_compute; reflexivity)
    | match goal with
      | |- context[if ?g then _ else _] =>
          let v := eval vm_compute in g in
          lazymatch v with
          | true  => replace g with true by (vm_compute; reflexivity)
          | false => replace g with false by (vm_compute; reflexivity)
          end
      end; cbn match ].

Lemma exec_read_CSR_menvcfg s :
  exec (read_CSR (Ox"30A")) s
    = Some (subrange_vec_dec (register_lookup menvcfg s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). apply exec_returnM. Qed.

Lemma exec_read_CSR_mcounteren s :
  exec (read_CSR (Ox"306")) s
    = Some (zero_extend' 64 (register_lookup mcounteren s.(sregs)), s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)). apply exec_returnM. Qed.

Lemma exec_read_CSR_sie s :
  exec (read_CSR (Ox"104")) s
    = Some (lower_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)), s).
Proof.
  drive_csr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)). apply exec_returnM.
Qed.

Lemma exec_read_CSR_time s :
  exec (read_CSR (Ox"C01")) s
    = Some (subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mtime s)). apply exec_returnM. Qed.

(* Gated check_CSR_result engine for CSRRead. *)
Lemma exec_check_CSR_read (csr : mword 12) s :
  exec (check_CSR_priv csr Machine) s = Some (true, s) ->
  check_CSR_access csr CSRRead = true ->
  exec (is_CSR_accessible csr Machine CSRRead) s = Some (true, s) ->
  exec (stateen_allows_CSR_access csr Machine CSRRead) s = Some (true, s) ->
  exec (check_CSR csr Machine CSRRead) s = Some (true, s).
Proof.
  intros Hpriv Hca Hacc Hst. unfold check_CSR.
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hpriv). cbn match.
  assert (HB : exec (returnM (check_CSR_access csr CSRRead) : M bool) s = Some (true, s))
    by (rewrite exec_returnm; rewrite Hca; reflexivity).
  rewrite (exec_and_boolM_Some _ _ _ _ _ HB). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hacc). cbn match.
  exact Hst.
Qed.

Lemma exec_check_CSR_result_read (csr : mword 12) s :
  exec (check_CSR csr Machine CSRRead) s = Some (true, s) ->
  exec (check_CSR_result csr Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro Hcc. unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ Hcc). cbn match. apply exec_returnm.
Qed.

(* currentlyEnabled Ext_U. *)
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

(* ===== mcounteren (0x306): Ext_U-gated, read = zero_extend' 64 mcounteren ===== *)
Definition csr_mcounteren : mword 12 := Ox"306".
Definition mcounteren_rdval (s : mstate) : mword 64 :=
  zero_extend' 64 (register_lookup mcounteren s.(sregs)).

Lemma exec_check_CSR_result_mcounteren s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_mcounteren Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HU. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_mcounteren Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hacceq : is_CSR_accessible csr_mcounteren Machine CSRRead = currentlyEnabled Ext_U)
      by (vm_compute; reflexivity).
    rewrite Hacceq. apply (exec_currentlyEnabled_U s HU).
  - assert (H : stateen_allows_CSR_access csr_mcounteren Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_mcounteren s d :
  exec (csr_id_read_callback csr_mcounteren d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_mcounteren d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_mcounteren_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mcounteren zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mcounteren_rdval s))).
Proof.
  intros Hrd Hpriv HU.
  apply (csrr_read_step csr_mcounteren rd (mcounteren_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_mcounteren s HU).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_mcounteren.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_mcounteren.
  - rewrite (exec_wX_bits_gpr rd (mcounteren_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===== menvcfg (0x30A): Ext_U-gated, read = subrange of menvcfg ===== *)
Definition csr_menvcfg : mword 12 := Ox"30A".
Definition menvcfg_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup menvcfg s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_check_CSR_result_menvcfg s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_menvcfg Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HU. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_menvcfg Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hacceq : is_CSR_accessible csr_menvcfg Machine CSRRead = currentlyEnabled Ext_U)
      by (vm_compute; reflexivity).
    rewrite Hacceq. apply (exec_currentlyEnabled_U s HU).
  - assert (H : stateen_allows_CSR_access csr_menvcfg Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_menvcfg s d :
  exec (csr_id_read_callback csr_menvcfg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_menvcfg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_menvcfg_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_menvcfg zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (menvcfg_rdval s))).
Proof.
  intros Hrd Hpriv HU.
  apply (csrr_read_step csr_menvcfg rd (menvcfg_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_menvcfg s HU).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_menvcfg.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_menvcfg.
  - rewrite (exec_wX_bits_gpr rd (menvcfg_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===== sie (0x104): Ext_S-gated, read = lower_mie mie mideleg (TWO regs) ===== *)
Definition csr_sie : mword 12 := Ox"104".
Definition sie_rdval (s : mstate) : mword 64 :=
  lower_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)).

Lemma exec_check_CSR_result_sie s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sie Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_sie Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hacceq : is_CSR_accessible csr_sie Machine CSRRead = currentlyEnabled Ext_S)
      by (vm_compute; reflexivity).
    rewrite Hacceq. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - assert (H : stateen_allows_CSR_access csr_sie Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_sie s d :
  exec (csr_id_read_callback csr_sie d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sie d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_sie_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_sie zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sie_rdval s))).
Proof.
  intros Hrd Hpriv HS.
  apply (csrr_read_step csr_sie rd (sie_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_sie s HS).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_sie.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_sie.
  - rewrite (exec_wX_bits_gpr rd (sie_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===== time (0xC01): Ext_Zicntr-gated + counter_enabled 1 priv (Machine =>  *)
(* true unconditionally).  Read = subrange of mtime. ===== *)
Definition csr_time : mword 12 := Ox"C01".
Definition time_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_hartSupports_Zicntr s : exec (hartSupports Ext_Zicntr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicntr) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Zicntr s :
  exec (currentlyEnabled Ext_Zicntr) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicntr) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicntr s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  apply exec_hartSupports_Zicntr.
Qed.

Lemma exec_counter_enabled_machine (index : Z) s :
  exec (counter_enabled index Machine) s = Some (true, s).
Proof.
  unfold counter_enabled.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg scounteren s)).
  unfold feature_enabled_for_priv_bool.
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (feature_enabled_for_priv Machine _ _ _) s = Some (FEATURE_ENABLED, s))).
  2:{ unfold feature_enabled_for_priv. apply exec_returnM. }
  apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_time s :
  exec (is_CSR_accessible csr_time Machine CSRRead) s = Some (true, s).
Proof.
  assert (Hred : is_CSR_accessible csr_time Machine CSRRead
                 = Defs.and_boolM (currentlyEnabled Ext_Zicntr) (counter_enabled 1 Machine))
    by (vm_compute; reflexivity).
  rewrite Hred.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zicntr s)). cbn match.
  apply exec_counter_enabled_machine.
Qed.

Lemma exec_check_CSR_result_time s :
  exec (check_CSR_result csr_time Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_time Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - apply exec_is_CSR_accessible_time.
  - assert (H : stateen_allows_CSR_access csr_time Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_time s d :
  exec (csr_id_read_callback csr_time d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_time d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_time_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_time zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (time_rdval s))).
Proof.
  intros Hrd Hpriv.
  apply (csrr_read_step csr_time rd (time_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_time s).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_time.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_time.
  - rewrite (exec_wX_bits_gpr rd (time_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* Each CSR read value, and misa's U/S bits, are untouched by [set_reg _ nextPC _],
   so they carry into the execute state (set_reg σ nextPC (pc+4)) unchanged. *)
Lemma mstatus_rdval_set_nextPC (s : mstate) (v : mword 64) :
  mstatus_rdval (set_reg s nextPC v) = mstatus_rdval s.
Proof. unfold mstatus_rdval, set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.
Lemma mcounteren_rdval_set_nextPC (s : mstate) (v : mword 64) :
  mcounteren_rdval (set_reg s nextPC v) = mcounteren_rdval s.
Proof. unfold mcounteren_rdval, set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.
Lemma menvcfg_rdval_set_nextPC (s : mstate) (v : mword 64) :
  menvcfg_rdval (set_reg s nextPC v) = menvcfg_rdval s.
Proof. unfold menvcfg_rdval, set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.
Lemma sie_rdval_set_nextPC (s : mstate) (v : mword 64) :
  sie_rdval (set_reg s nextPC v) = sie_rdval s.
Proof. unfold sie_rdval, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [| vm_compute; reflexivity]). reflexivity. Qed.
Lemma time_rdval_set_nextPC (s : mstate) (v : mword 64) :
  time_rdval (set_reg s nextPC v) = time_rdval s.
Proof. unfold time_rdval, set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.
Lemma misa_set_nextPC (s : mstate) (v : mword 64) :
  register_lookup misa (set_reg s nextPC v).(sregs) = register_lookup misa s.(sregs).
Proof. unfold set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.

(* ====================================================================== *)
(* The register-GENERIC csrr WP for [csrr rd, mhartid], stated on the new    *)
(* [instr] / [mmode_config] / [gpr_file] layer (cf. [wp_auipc_gpr]).  Like    *)
(* AUIPC, csrr-mhartid has no GPR source: it writes rd := mhartid.  The value  *)
(* of mhartid is threaded through as its own register points-to premise         *)
(* [mhartid ↦ᵣ mhartid_in] (mhartid is not part of [mmode_config]); it is read  *)
(* and returned unchanged.  Built on [wp_instr]; reuses the representation-      *)
(* independent execute helper [exec_execute_CSRReg_gpr].                        *)
(* ====================================================================== *)
Section WpCsrrMhartidGpr.
  Context `{!riscvGS Σ}.

  Global Instance reg_pointsto_fractional_csrr (r : register) (v : type_of_register r) :
    Fractional (fun q => reg_pointsto r (DfracOwn q) v).
  Proof. rewrite /reg_pointsto. apply _. Qed.
  Global Instance reg_pointsto_as_fractional_csrr (r : register) (q : Qp) (v : type_of_register r) :
    AsFractional (reg_pointsto r (DfracOwn q) v) (fun q => reg_pointsto r (DfracOwn q) v) q.
  Proof. rewrite /reg_pointsto. split; [done | apply _]. Qed.

  Lemma reg_pointsto_agree_csrr (r : register) (dq1 dq2 : dfrac) (v1 v2 : type_of_register r) :
    reg_pointsto r dq1 v1 -∗ reg_pointsto r dq2 v2 -∗ ⌜ v1 = v2 ⌝.
  Proof.
    rewrite /reg_pointsto. iIntros "H1 H2".
    iDestruct (pointsto_agree with "H1 H2") as %Heq.
    iPureIntro. exact (Eqdep_dec.inj_pair2_eq_dec _ Decidable_eq_register _ r v1 v2 Heq).
  Qed.

  (* Split [mmode_config (DfracOwn 1)] into two halves: one to hand to
     [wp_instr], the other kept to read [cur_privilege = Machine] at the
     execute state (the CSR read needs M-privilege). *)
  Lemma mmode_config_split_half_csrr :
    mmode_config (DfracOwn 1) ⊢
      mmode_config (DfracOwn (1/2)) ∗ mmode_config (DfracOwn (1/2)).
  Proof.
    iIntros "(#Hhw & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (ms0) "(Hms & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhs" as "[Hhs1 Hhs2]".
    iDestruct "Hpriv" as "[Hpriv1 Hpriv2]".
    iDestruct "Hms" as "[Hms1 Hms2]".
    iSplitL "Hhs1 Hpriv1 Hms1".
    - iFrame "Hhw Hinv Hhs1 Hpriv1". iExists ms0. iFrame "Hms1 %".
    - iFrame "Hhw Hinv Hhs2 Hpriv2". iExists ms0. iFrame "Hms2 %".
  Qed.

  Lemma mmode_config_combine_half_csrr :
    mmode_config (DfracOwn (1/2)) -∗ mmode_config (DfracOwn (1/2)) -∗
    mmode_config (DfracOwn 1).
  Proof.
    iIntros "(#Hhw & #Hinv & Hhs1 & Hpriv1 & Hmst1) (_ & _ & Hhs2 & Hpriv2 & Hmst2)".
    iDestruct "Hmst1" as (ms0) "(Hms1 & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hmst2" as (ms0') "(Hms2 & _ & _ & _)".
    iDestruct (reg_pointsto_agree_csrr with "Hms1 Hms2") as %<-.
    iCombine "Hhs1 Hhs2" as "Hhs".
    iCombine "Hpriv1 Hpriv2" as "Hpriv".
    iCombine "Hms1 Hms2" as "Hms".
    iFrame "Hhw Hinv Hhs Hpriv". iExists ms0. iFrame "Hms %".
  Qed.

  Lemma wp_csrr_mhartid_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mhartid_in : mword 64) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    instr pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg mhartid_in]> m) -∗
      mhartid ↦ᵣ mhartid_in -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hmh Hinstr Hcont".
    (* keep half of [mmode_config] to read cur_privilege at the execute state *)
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    (* the destination entry is a real register (rd <> 0) *)
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* read cur_privilege (kept half) and mhartid off their points-to (against σ) *)
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hmh") as %Lmh.
    (* tick nextPC; PC/cur_privilege/mhartid unchanged *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LprivS : register_lookup cur_privilege
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = Machine).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LmhS : register_lookup mhartid
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = mhartid_in).
    { rewrite mhartid_set_nextPC. exact Lmh. }
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg mhartid_in)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg mhartid_in)
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg mhartid_in)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_csrr zreg (Regidx rd) CSRRS).
      rewrite (exec_execute_CSRReg_gpr rd (set_reg σ nextPC (add_vec_int pc 4)) Hrd LprivS).
      rewrite LmhS. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: PC/nextPC are both pc+4; reassemble mmode_config and hand
       everything back *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg mhartid_in)).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    (* rebuild the kept half of mmode_config and recombine with the returned half *)
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hmh").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End WpCsrrMhartidGpr.

(* Demonstration: ONE lemma [wp_csrr_mhartid_gpr] serves many destination regs. *)
Section WpCsrrMhartidGprDemo.
  Context `{!riscvGS Σ}.
  Definition wp_csrr_mhartid_x5 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64)
      (mhartid_in : mword 64) :=
    wp_csrr_mhartid_gpr E Φ pc (mword_of_int 5) mhartid_in.   (* csrr x5, mhartid *)
  Definition wp_csrr_mhartid_x28 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64)
      (mhartid_in : mword 64) :=
    wp_csrr_mhartid_gpr E Φ pc (mword_of_int 28) mhartid_in.  (* csrr x28, mhartid *)
  Goal gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 5 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpCsrrMhartidGprDemo.

(* ====================================================================== *)
(* Register-generic csrr WPs for arbitrary readable CSRs (mstatus /          *)
(* mcounteren / menvcfg / sie / time), stated on the new                     *)
(* [instr] / [mmode_config] / [gpr_file] layer -- ported from the old        *)
(* WpGprCsrrAny.v.  Each is [csrr rd, csr] (= csrrs rd,csr,x0): no GPR        *)
(* source, writes rd := (CSR read value).  The read CSR cell(s) are threaded  *)
(* as extra register points-to premises (returned unchanged); cur_privilege   *)
(* = Machine (and, for the U/S-gated CSRs, the misa.U/misa.S bit) is          *)
(* recovered at the execute state from the [mmode_config] / [hw_config]        *)
(* split, exactly as in [wp_csrr_mhartid_gpr].  Built on [wp_instr]; each      *)
(* reuses the representation-independent [exec_execute_csrr_<csr>_gpr] helper. *)
(* ====================================================================== *)
Section WpCsrrGpr.
  Context `{!riscvGS Σ}.

  (* mstatus (0x300): machine CSR, no extra gate. *)
  Lemma wp_csrr_mstatus_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mstatus_in : mword 64) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mstatus ↦ᵣ mstatus_in -∗
    instr pc false (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (mstatus_in)]> m) -∗
      mstatus ↦ᵣ mstatus_in -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LprivS : register_lookup cur_privilege
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = Machine).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Hrv : mstatus_rdval (set_reg σ nextPC (add_vec_int pc 4))
             = mstatus_in).
    { rewrite mstatus_rdval_set_nextPC. unfold mstatus_rdval. rewrite Lcsr. apply subrange64_id. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (mstatus_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (mstatus_in))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (mstatus_in))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_mstatus zreg (Regidx rd) CSRRS).
      rewrite (exec_execute_csrr_mstatus_gpr rd
                 (set_reg σ nextPC (add_vec_int pc 4)) Hrd LprivS).
      rewrite Hrv. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (mstatus_in))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* time (0xC01): Ext_Zicntr-gated, no misa premise needed (holds for any state). *)
  Lemma wp_csrr_time_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mtime_in : mword 64) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mtime ↦ᵣ mtime_in -∗
    instr pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (mtime_in)]> m) -∗
      mtime ↦ᵣ mtime_in -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LprivS : register_lookup cur_privilege
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = Machine).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Hrv : time_rdval (set_reg σ nextPC (add_vec_int pc 4))
             = mtime_in).
    { rewrite time_rdval_set_nextPC. unfold time_rdval. rewrite Lcsr. apply subrange64_id. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (mtime_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (mtime_in))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (mtime_in))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_time, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_time zreg (Regidx rd) CSRRS).
      rewrite (exec_execute_csrr_time_gpr rd
                 (set_reg σ nextPC (add_vec_int pc 4)) Hrd LprivS).
      rewrite Hrv. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (mtime_in))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* mcounteren (0x306): Ext_U-gated; misa.U recovered from hw_config. *)
  Lemma wp_csrr_mcounteren_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mcen_in : mword 32) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mcounteren ↦ᵣ mcen_in -∗
    instr pc false (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (zero_extend' 64 mcen_in)]> m) -∗
      mcounteren ↦ᵣ mcen_in -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LprivS : register_lookup cur_privilege
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = Machine).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (HUS : eq_vec (_get_Misa_U (register_lookup misa
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs))) ('b"1") = true).
    { rewrite misa_set_nextPC. rewrite Lmisa. exact HmisaU. }
    assert (Hrv : mcounteren_rdval (set_reg σ nextPC (add_vec_int pc 4))
             = zero_extend' 64 mcen_in).
    { rewrite mcounteren_rdval_set_nextPC. unfold mcounteren_rdval. rewrite Lcsr. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (zero_extend' 64 mcen_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (zero_extend' 64 mcen_in))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (zero_extend' 64 mcen_in))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_mcounteren zreg (Regidx rd) CSRRS).
      rewrite (exec_execute_csrr_mcounteren_gpr rd
                 (set_reg σ nextPC (add_vec_int pc 4)) Hrd LprivS HUS).
      rewrite Hrv. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (zero_extend' 64 mcen_in))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* menvcfg (0x30A): Ext_U-gated; misa.U recovered from hw_config. *)
  Lemma wp_csrr_menvcfg_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (menvcfg_in : mword 64) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menvcfg_in -∗
    instr pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (menvcfg_in)]> m) -∗
      menvcfg ↦ᵣ menvcfg_in -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LprivS : register_lookup cur_privilege
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = Machine).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (HUS : eq_vec (_get_Misa_U (register_lookup misa
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs))) ('b"1") = true).
    { rewrite misa_set_nextPC. rewrite Lmisa. exact HmisaU. }
    assert (Hrv : menvcfg_rdval (set_reg σ nextPC (add_vec_int pc 4))
             = menvcfg_in).
    { rewrite menvcfg_rdval_set_nextPC. unfold menvcfg_rdval. rewrite Lcsr. apply subrange64_id. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (menvcfg_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (menvcfg_in))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (menvcfg_in))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_menvcfg zreg (Regidx rd) CSRRS).
      rewrite (exec_execute_csrr_menvcfg_gpr rd
                 (set_reg σ nextPC (add_vec_int pc 4)) Hrd LprivS HUS).
      rewrite Hrv. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (menvcfg_in))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hcsr").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* sie (0x104): Ext_S-gated; misa.S recovered from hw_config.  Read =
     lower_mie mie mideleg, so BOTH mie and mideleg cells are threaded. *)
  Lemma wp_csrr_sie_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mie_in mideleg_in : mword 64) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mie ↦ᵣ mie_in -∗
    (R_bitvector_64 mideleg) ↦ᵣ mideleg_in -∗
    instr pc false (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (lower_mie mie_in mideleg_in)]> m) -∗
      mie ↦ᵣ mie_in -∗
      (R_bitvector_64 mideleg) ↦ᵣ mideleg_in -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hmie Hmdl Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_instr E Φ pc false (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid with "Hreg Hmdl") as %Lmdl.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LprivS : register_lookup cur_privilege
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = Machine).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (HSS : eq_vec (_get_Misa_S (register_lookup misa
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs))) ('b"1") = true).
    { rewrite misa_set_nextPC. rewrite Lmisa. exact HmisaS. }
    assert (Hrv : sie_rdval (set_reg σ nextPC (add_vec_int pc 4))
             = lower_mie mie_in mideleg_in).
    { rewrite sie_rdval_set_nextPC. unfold sie_rdval. rewrite Lmie Lmdl. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (lower_mie mie_in mideleg_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (lower_mie mie_in mideleg_in))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (lower_mie mie_in mideleg_in))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_sie zreg (Regidx rd) CSRRS).
      rewrite (exec_execute_csrr_sie_gpr rd
                 (set_reg σ nextPC (add_vec_int pc 4)) Hrd LprivS HSS).
      rewrite Hrv. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (lower_mie mie_in mideleg_in))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hinv Hhs_k Hpriv_k". iSplitR "Hms_k".
      - iExists misa0, mseccfg0, pmar0, elp0.
        iFrame "Hmisa Hmseccfg Hpma Hhtif Help %".
      - iExists ms0. iFrame "Hms_k %". }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hmie Hmdl").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End WpCsrrGpr.
