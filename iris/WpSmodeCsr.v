(* S-mode Csr leaf lemmas (smode_config/Supervisor, decode family Csr).
   Relocated from function proof files (per-(mode,family) leaf reorg). *)
Require Import WpSmodeLeafBase.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes WpDecode WpLeafCommon WpGpr WpGprCsrwCommon.
Require Import SmodeCore WpSmodeGpr WpEntryNew StackOwn CalleeSaved.
Require Import WpMmodeLeafBase WpSmodeLeafBase.
Import Defs.
From Stdlib Require Import FunctionalExtensionality.
Require Import WpSmodeToBeDeleted.

(* helper: csr_sstatus *)
Definition csr_sstatus : mword 12 := Ox"100".

(* helper: exec_csr_id_read_callback_sstatus *)
Lemma exec_csr_id_read_callback_sstatus (d : mword 64) s :
  exec (csr_id_read_callback csr_sstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

(* helper: exec_csr_id_write_callback_sstatus *)
Lemma exec_csr_id_write_callback_sstatus (d : mword 64) s :
  exec (csr_id_write_callback csr_sstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_write_callback csr_sstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

(* helper: exec_hartSupports_H *)
Lemma exec_hartSupports_H s : exec (hartSupports Ext_H) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_H) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

(* helper: exec_hartSupports_Sv32 *)
Lemma exec_hartSupports_Sv32 s : exec (hartSupports Ext_Sv32) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv32) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  replace (andb false (Z.eqb xlen 32)) with false by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

(* helper: exec_have_nominal_privLevel *)
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

(* helper: exec_lowest_supported_privLevel *)
Lemma exec_lowest_supported_privLevel s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (lowest_supported_privLevel tt) s = Some (User, s).
Proof.
  intro HU. unfold lowest_supported_privLevel.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_U s HU)). cbn match.
  apply exec_returnM.
Qed.

(* helper: exec_read_CSR_sstatus *)
Lemma exec_read_CSR_sstatus s :
  exec (read_CSR csr_sstatus) s
    = Some (sstatus_read (register_lookup mstatus s.(sregs)), s).
Proof.
  unfold read_CSR. skip_csr_false_clauses.
  replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  unfold sstatus_read. apply exec_returnM.
Qed.

(* helper: exec_virtual_memory_supported *)
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

(* helper: register_set_bv64_id *)
Lemma register_set_bv64_id (r : register_bitvector_64) (rs : regstate) :
  register_set (R_bitvector_64 r) (register_lookup (R_bitvector_64 r) rs) rs = rs.
Proof.
  destruct rs. unfold register_set, register_lookup. cbn.
  f_equal. apply functional_extensionality. intro r'.
  destruct (register_bitvector_64_beq r' r) eqn:E.
  - apply register_bitvector_64_beq_iff in E. subst r'. reflexivity.
  - reflexivity.
Qed.

(* helper: exec_currentlyEnabled_H_false *)
Lemma exec_currentlyEnabled_H_false s : exec (currentlyEnabled Ext_H) s = Some (false, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_H) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_H s)). reflexivity.
Qed.

(* helper: exec_legalize_mstatus *)
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

(* helper: exec_legalize_sstatus *)
Lemma exec_legalize_sstatus (m v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (legalize_sstatus m v) s = Some (legalize_sstatus_val m v, s).
Proof.
  intros HS HU. unfold legalize_sstatus, legalize_sstatus_val.
  apply (exec_legalize_mstatus m (lift_sstatus m (Mk_Sstatus (zero_extend' 64 v))) s HS HU).
Qed.

(* helper: exec_write_CSR_sstatus *)
Lemma exec_write_CSR_sstatus (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (write_CSR csr_sstatus v) s
    = Some (Ok (subrange_vec_dec
                  (lower_mstatus (legalize_sstatus_val (register_lookup mstatus s.(sregs)) v))
                  (Z.sub xlen 1) 0),
            set_reg s mstatus (legalize_sstatus_val (register_lookup mstatus s.(sregs)) v)).
Proof.
  intros HS HU. unfold write_CSR. skip_csr_false_clauses.
  replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_legalize_sstatus (register_lookup mstatus s.(sregs)) v s HS HU)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus _)).
  rewrite register_lookup_set.
  apply exec_returnM.
Qed.

(* helper: exec_check_CSR_priv_sstatus_S *)
Lemma exec_check_CSR_priv_sstatus_S s :
  exec (check_CSR_priv csr_sstatus Supervisor) s = Some (true, s).
Proof.
  unfold check_CSR_priv.
  assert (Hp : exec (privLevel_to_CSR_privbits Supervisor) s = Some ('b"01" : mword 2, s)).
  { unfold privLevel_to_CSR_privbits.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_H_false s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hp). rewrite exec_returnM.
  replace (zopz0zKzJ_u ('b"01" : mword 2) (csrPriv csr_sstatus)) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* helper: exec_check_CSR_sstatus_S *)
Lemma exec_check_CSR_sstatus_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR csr_sstatus Supervisor CSRReadWrite) s = Some (true, s).
Proof.
  intro HS. unfold check_CSR.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_check_CSR_priv_sstatus_S s)). cbn match.
  assert (HA : exec (returnM (check_CSR_access csr_sstatus CSRReadWrite) : M bool) s
               = Some (true, s)).
  { rewrite exec_returnM.
    replace (check_CSR_access csr_sstatus CSRReadWrite) with true by (vm_compute; reflexivity).
    reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ HA). cbn match.
  assert (Hacc : exec (is_CSR_accessible csr_sstatus Supervisor CSRReadWrite) s = Some (true, s)).
  { unfold is_CSR_accessible. skip_csr_false_clauses.
    replace (eq_vec csr_sstatus (Ox"100")) with true by (vm_compute; reflexivity). cbn match.
    rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hacc). cbn match.
  unfold stateen_allows_CSR_access. cbn match. skip_csr_false_clauses.
  apply exec_returnM.
Qed.

(* helper: exec_check_CSR_result_sstatus_S *)
Lemma exec_check_CSR_result_sstatus_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sstatus Supervisor CSRReadWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS. unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_sstatus_S s HS)). cbn match.
  apply exec_returnM.
Qed.

(* helper: exec_execute_csrr_sstatus *)
Lemma exec_execute_csrr_sstatus (rd : mword 5) (m : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  uint rd <> 0 ->
  exec (execute (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sstatus_read m))).
Proof.
  intros Hpriv Hm HS Hrd.
  change (execute (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)))
    with (execute_CSRReg csr_sstatus (Regidx (mword_of_int 0)) (Regidx rd) CSRRS).
  unfold execute_CSRReg.
  (* access_type = csr_access_type CSRRS _ true = CSRRead *)
  replace (generic_eq (Regidx (mword_of_int 0 : mword 5)) zreg) with true
    by (vm_compute; reflexivity).
  cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr (mword_of_int 0) s)).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  unfold ext_check_CSR. cbn match.
  replace (generic_neq (csr_access_type CSRRS (generic_eq (Regidx rd) zreg) true) CSRWrite)
    with true by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
  replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
  replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
  replace (generic_eq (csr_access_type CSRRS (generic_eq (Regidx rd) zreg) true) CSRRead)
    with true by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_csr_id_read_callback_sstatus (sstatus_read m) s)).
  assert (HwX : exec (wX_bits (Regidx rd) (sstatus_read m)) s
                = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sstatus_read m)))).
  { rewrite (exec_wX_bits_gpr rd _ s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ HwX).
  apply exec_returnM.
Qed.

(* helper: exec_execute_csrrci_sstatus *)
Lemma exec_execute_csrrci_sstatus (imm5 rd : mword 5) (m : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec imm5 (zeros' 5) = false ->
  uint rd <> 0 ->
  legalize_sstatus_val m (sstatus_write_val m imm5) = m ->
  exec (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sstatus_read m))).
Proof.
  intros Hpriv Hm HS HU Himm Hrd Hcollapse.
  change (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC)))
    with (execute_CSRImm csr_sstatus imm5 (Regidx rd) CSRRC).
  unfold execute_CSRImm.
  rewrite Himm.
  (* access_type = CSRReadWrite *)
  cbn match.
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  unfold ext_check_CSR. cbn match.
  replace (generic_neq CSRReadWrite CSRWrite) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
  replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
  replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
  replace (generic_eq CSRReadWrite CSRRead) with false by (vm_compute; reflexivity). cbn match.
  (* write path: write_val = and_vec read_val (not_vec (zext imm5)) = sstatus_write_val m imm5 *)
  assert (Hid : set_reg s mstatus m = s).
  { unfold set_reg. rewrite <- Hm.
    rewrite (register_set_bv64_id mstatus s.(sregs)).
    destruct s; reflexivity. }
  assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_val m imm5)) s
                   = Some (Ok (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0), s)).
  { rewrite (exec_write_CSR_sstatus (sstatus_write_val m imm5) s HS HU).
    rewrite Hm. rewrite Hcollapse. rewrite Hid. reflexivity. }
  change (and_vec (sstatus_read m) (not_vec (zero_extend' 64 imm5)))
    with (sstatus_write_val m imm5).
  rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
  (* [>>] is left-associative: (wX >> callback) >> returnM.  Peel inner first. *)
  assert (Hwc : exec (wX_bits (Regidx rd) (sstatus_read m) >>
                      csr_id_write_callback csr_sstatus
                        (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0)) s
                = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sstatus_read m)))).
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd (sstatus_read m) s)).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    apply (exec_csr_id_write_callback_sstatus
             (subrange_vec_dec (lower_mstatus m) (Z.sub xlen 1) 0) _). }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
  apply exec_returnM.
Qed.

Section WpSmodeCsr.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_csrr_sstatus_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sstatus_read mstatus0)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false
              (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sstatus_read mstatus0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sstatus_read mstatus0)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sstatus_read mstatus0))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrr_sstatus rd mstatus0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS) Hrd). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sstatus_read mstatus0))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Lemma wp_csrr_sstatus_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)) -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      (∃ ms : mword 64, ⌜ eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ⌝ ∗
         gpr_file (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csrr_sstatus_s root_ppn E Φ pc rd m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc [Hfile]").
    iExists mstatus0. iFrame "Hfile". iPureIntro. exact HSIE.
  Qed.

  Lemma wp_csrrci_sstatus_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd imm5 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rd <> 0 ->
    eq_vec imm5 (zeros' 5) = false ->
    legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 imm5) = mstatus0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sstatus_read mstatus0)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd Himm5 Hcollapse)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false
              (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = mstatus0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lms | vm_compute; reflexivity ]. }
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sstatus_read mstatus0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sstatus_read mstatus0)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sstatus_read mstatus0))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrrci_sstatus imm5 rd mstatus0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)
               ltac:(rewrite Lmisa_spc; exact HmisaU)
               Himm5 Hrd Hcollapse). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sstatus_read mstatus0))).(sregs)
             = add_vec_int pc 4)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Lemma wp_csrrci_sstatus_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : gmap regidx (mword 64)) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC)) -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      (∃ ms : mword 64, ⌜ eq_vec (_get_Mstatus_SIE ms) ('b"1") = false ⌝ ∗
         gpr_file (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csrrci_sstatus_s root_ppn E Φ pc rd (mword_of_int 2) m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrd
              ltac:(vm_compute; reflexivity) Hleg
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc [Hfile]").
    iExists mstatus0. iFrame "Hfile". iPureIntro. exact HSIE.
  Qed.

End WpSmodeCsr.
