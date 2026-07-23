From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec ExecCommon WpGpr.
Require Import RegFile.
Require Import InstrBytes.
Local Open Scope Z_scope.
Require Import WpGprCsrwCommon.

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
  skip_csr_false_clauses.
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
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_mideleg rs1 s _
           (mideleg_legalized (register_lookup mideleg s.(sregs))
              ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_S csr_mideleg s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | csr_dispatch_eq | vm_compute; reflexivity ].
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
  skip_csr_false_clauses.
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
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_sie rs1 s _
           (lower_mie (sie_new_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs))
                         ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))
                      (register_lookup mideleg s.(sregs)))).
  
  - exact Hpriv.
  - apply (exec_check_CSR_result_csrw_S csr_sie s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | csr_dispatch_eq | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_sie.
  - apply exec_csr_id_write_callback_sie.
Qed.

(* ---- sie forward/clean/wp: writes mie; value reads mie + mideleg ---- *)


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

(* [exec_architecture_Supervisor] is a privilege-generic model fact, not a
   CSRW one -- it lives in ExecCommon.v so the page-table files can reach
   it without importing this whole family. *)

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
  skip_csr_false_clauses.
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
  skip_csr_false_clauses.
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
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_satp rs1 s _
           (satp_legalized (register_lookup satp s.(sregs))
              ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).
  
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
  skip_csr_false_clauses.
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
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_pmpaddr0 rs1 s _
           (vec_access_dec
              (register_lookup pmpaddr_n
                 (set_reg s pmpaddr_n (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                    (register_lookup pmpaddr_n s.(sregs))
                    ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))))).(sregs)) 0)).
  
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
  skip_csr_false_clauses.
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
  skip_csr_false_clauses.
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
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr csr_stimecmp rs1 s _
           (subrange_vec_dec (stimecmp_legalized (register_lookup stimecmp s.(sregs))
              ((if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))) (Z.sub xlen 1) 0)).
  
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



Section WpCsrwGprNewB.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  (* ---- mideleg ---- *)
  Lemma wp_csrw_mideleg_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (mideleg0 : type_of_register mideleg)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mideleg ↦ᵣ mideleg0 -∗
    instr pc false (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mideleg ↦ᵣ mideleg_legalized mideleg0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup mideleg s_pc.(sregs) = mideleg0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m (Regidx rs1)).
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hcsr").
  Qed.

  (* ---- stimecmp ---- *)
  Lemma wp_csrw_stimecmp_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (stimecmp0 : type_of_register stimecmp)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    instr pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup stimecmp s_pc.(sregs) = stimecmp0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m (Regidx rs1)).
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hcsr").
  Qed.

  (* ---- sie (Ext_S): writes mie; value reads old mie + old mideleg ---- *)
  Lemma wp_csrw_sie_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (mie0 mideleg0 : type_of_register mie)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mie ↦ᵣ mie0 -∗
    mideleg ↦ᵣ mideleg0 -∗
    instr pc false (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      mie ↦ᵣ sie_new_mie mie0 mideleg0 (m !!! Regidx rs1) -∗
      mideleg ↦ᵣ mideleg0 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hmie Hmdl Hinstr Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid    with "Hreg Hmdl")     as %Lmdl.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lrs1u.
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
                    = m (Regidx rs1)).
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hmie Hmdl").
  Qed.

  (* ---- satp (Ext_S, mstatus.SXL=SXLEN64): the SXL fact is drawn from the
     kept-half [mstatus] (mstatus.SXL is part of the mmode_config mstatus). ---- *)
  Lemma wp_csrw_satp_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (satp0 : type_of_register satp)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    satp ↦ᵣ satp0 -∗
    instr pc false (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      satp ↦ᵣ satp_legalized satp0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hrs1) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms_k")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lrs1u.
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
                    = m (Regidx rs1)).
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hcsr").
  Qed.

  (* ---- pmpaddr0 (pure): writes pmpaddr_n; value reads old pmpaddr_n AND
     pmpcfg_n.  pmpcfg_n is held (read-only) by [wp_instr] at the split
     fraction; we recover its value at the execute state via a kept half. ---- *)
  Lemma wp_csrw_pmpaddr0_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (pmpaddr0 : type_of_register pmpaddr_n)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    pmpaddr_n ↦ᵣ pmpaddr0 -∗
    instr pc false (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hrs1) "Hmm [Hpmpc_wp Hpmpc_k] [Hpc Hnpc] Hfmap Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k") as %Lpmpc.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lcsrp : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m (Regidx rs1)).
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hcsr").
  Qed.

End WpCsrwGprNewB.
