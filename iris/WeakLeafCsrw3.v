(** * WeakLeafCsrw3.v — the BOOT-PATH csrw leaves: satp / sie / pmpaddr0 (M4)

    The third register-only csrw batch, and the last three the [start()]
    boot path needs.  Each section is [WeakLeafCsrw2]'s medeleg TEMPLATE
    with the cell and value names substituted; what differs per CSR is only
    the [write_CSR] cone underneath:

      §1  satp (0x180) — the deepest cone of the three: [legalize_satp]'s
          mode dispatch runs [currentlyEnabled] at four Sv extensions, and
          [write_CSR] first asks [architecture Supervisor].  So this section
          mirrors [WpGprCsrwB]'s [exec_hartSupports_Sv48]/[_Sv57],
          [exec_currentlyEnabled_Svbare]/[_Sv39w]/[_Sv48w]/[_Sv57w] and
          [ExecCommon.exec_architecture_Supervisor] at [exec_eff] before it
          can state [exec_eff_write_CSR_satp].  The [Ext_S]/[Ext_U]/
          [Ext_Sv32]/[Ext_Sv39]/[Ext_Zicsr] enablement chain is already in
          [WeakLeafEffCommon] and is reused, not restated.
          The SXL premise ([mstatus.SXL = SXL64]) is not in
          [WeakFunnel.wcfg_regs], so the satp leaf keeps a HALF of
          [mmode_config] across the funnel call (exactly as the SC
          [WpGprCsrwB.wp_csrw_satp_gpr] does) and reads the fact off it.
      §2  sie (0x104) — [legalize_sie] is pure but [write_CSR] READS
          [mideleg] and WRITES [mie]; the leaf therefore threads TWO extra
          cells, the written [mie] and the unchanged [mideleg].
      §3  pmpaddr0 (0x3b0) — writes the [pmpaddr_n] VECTOR register with a
          value that reads [pmpcfg_n] for the lock check.  [pmpcfg_n]'s
          value is already pinned by the funnel ([wcfg_regs]), so the leaf
          holds only the [pmpaddr_n] cell and the read-only [pmpcfg_n]
          premise cell the template already carries.

    Every PURE definition ([satp_legalized], [sie_new_mie], [pmp0_newaddr],
    the csr constants, [legalize_sie], [pmpWriteAddr], …) is REUSED from the
    SC files — this file restates none of them. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetch2.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr.
Require Import WeakLeafWin.
Require Import ExecCommon WpDecode.
Require Import WpGprCsrwCommon WpGprCsrwA WpGprCsrwB.
Require Import WeakLeafCsrw WeakLeafRegOnly.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. satp (0x180) *)

(** *** 1a. The Sv extension enablement mirrors
    ([WpGprCsrwB.exec_hartSupports_Sv48] / [_Sv57] and the four
    [exec_currentlyEnabled_*] the [legalize_satp] mode dispatch enters). *)

Lemma exec_eff_hartSupports_Sv48 s :
  exec_eff (hartSupports Ext_Sv48) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv48) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Sv57 s :
  exec_eff (hartSupports Ext_Sv57) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv57) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

(** [WpGprCsrwB.crush_rec_cE_S]'s mirror: discharge an inner
    [_rec_currentlyEnabled Ext_S k a] (concrete [k]) to misa.S. *)
Ltac crush_rec_cE_S_eff s :=
  match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
    let H := fresh "HrecS" in
    assert (H : exec_eff (_rec_currentlyEnabled Ext_S k a) s
                = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs)))
                          ('b"1"), s, []));
    [ destruct a; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?kk 0] =>
        replace (Z.geb kk 0) with true by reflexivity end;
      cbn match;
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s));
      cbn match;
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_S s));
      cbn match;
      match goal with |- context[Defs.and_boolM ?l _] =>
        let Hmb := fresh "Hmb" in
        assert (Hmb : exec_eff l s
                      = Some (eq_vec (_get_Misa_S
                                (register_lookup misa s.(sregs))) ('b"1"),
                              s, []))
          by (rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg misa s));
              apply exec_eff_returnM);
        rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hmb)
      end;
      destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"))
        eqn:?;
      [ match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
          exact (exec_eff_rec_cE_Zicsr_any k2 a2 s ltac:(reflexivity)) end
      | reflexivity ]
    | rewrite H ]
  end.

Lemma exec_eff_currentlyEnabled_Svbare s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (currentlyEnabled Ext_Svbare) s = Some (true, s, []).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svbare) 0) with true
    by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  crush_rec_cE_S_eff s. rewrite HS. reflexivity.
Qed.

Lemma exec_eff_currentlyEnabled_Sv39w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (currentlyEnabled Ext_Sv39) s = Some (true, s, []).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv39) 0) with true
    by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Sv39 s)).
  cbn match.
  crush_rec_cE_S_eff s. rewrite HS. reflexivity.
Qed.

Lemma exec_eff_currentlyEnabled_Sv48w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (currentlyEnabled Ext_Sv48) s = Some (true, s, []).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv48) 0) with true
    by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Sv48 s)).
  cbn match.
  crush_rec_cE_S_eff s. rewrite HS. reflexivity.
Qed.

Lemma exec_eff_currentlyEnabled_Sv57w s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (currentlyEnabled Ext_Sv57) s = Some (true, s, []).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sv57) 0) with true
    by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Sv57 s)).
  cbn match.
  crush_rec_cE_S_eff s. rewrite HS. reflexivity.
Qed.

(** [ExecCommon.exec_architecture_Supervisor]'s mirror.  (An identical twin
    lives in [WeakWalkEff]; restated here under a distinct name so this file
    does not pull the whole page-table-walk cone in for fifteen lines.) *)
Lemma exec_eff_architecture_Supervisor_sxl s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec_eff (architecture Supervisor) s = Some (RV64, s, []).
Proof.
  intro HSXL. unfold architecture. cbn match.
  match goal with |- exec_eff (Defs.bind ?L _) s = _ =>
    assert (Hin : exec_eff L s
                  = Some (_get_Mstatus_SXL (register_lookup mstatus s.(sregs)),
                          s, [])) end.
  { rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hin).
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity).
  cbn match.
  apply exec_eff_returnM.
Qed.

(** *** 1b. legalize_satp / write_CSR / check / callback, at [exec_eff] *)

Lemma exec_eff_legalize_satp_rv64 (prev value : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (legalize_satp RV64 prev value) s
    = Some (satp_legalized prev value, s, []).
Proof.
  intro HS. unfold legalize_satp, satp_legalized.
  cbn zeta.
  rewrite satp_ppn_mask_id.
  destruct (satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64 value)))
    as [sv|] eqn:Hm.
  - destruct sv.
    + rewrite (exec_eff_bind_nil _ _ _ _ _
                 (exec_eff_currentlyEnabled_Svbare s HS)). cbn match.
      apply exec_eff_returnM.
    + apply exec_eff_returnM.
    + rewrite (exec_eff_bind_nil _ _ _ _ _
                 (exec_eff_currentlyEnabled_Sv39w s HS)). cbn match.
      apply exec_eff_returnM.
    + rewrite (exec_eff_bind_nil _ _ _ _ _
                 (exec_eff_currentlyEnabled_Sv48w s HS)). cbn match.
      apply exec_eff_returnM.
    + rewrite (exec_eff_bind_nil _ _ _ _ _
                 (exec_eff_currentlyEnabled_Sv57w s HS)). cbn match.
      apply exec_eff_returnM.
  - apply exec_eff_returnM.
Qed.

Lemma exec_eff_write_CSR_satp (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec_eff (write_CSR csr_satp v) s
    = Some (Ok (satp_legalized (register_lookup satp s.(sregs)) v),
            set_reg s satp
              (satp_legalized (register_lookup satp s.(sregs)) v), []).
Proof.
  intros HS HSXL. unfold write_CSR.
  skip_csr_false_clauses_eff.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_architecture_Supervisor_sxl s HSXL)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg satp s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_legalize_satp_rv64 (register_lookup satp s.(sregs))
                v s HS)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg satp _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg satp _)).
  rewrite register_lookup_set.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_satp (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_satp d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_satp d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_is_CSR_accessible_satp s :
  exec_eff (is_CSR_accessible csr_satp Machine CSRWrite) s
    = Some (true, s, []).
Proof.
  unfold is_CSR_accessible.
  skip_csr_false_clauses_eff.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  unfold satp_accessible. cbn match. apply exec_eff_hartSupports_S.
Qed.

(** *** 1c. The end-to-end satp [execute], trace [] *)

Lemma exec_eff_execute_csrw_satp (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec_eff (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s satp
            (satp_legalized (register_lookup satp s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv HS HSXL.
  change (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_satp (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_satp rs1 s _
           (satp_legalized (register_lookup satp s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                      s.(sregs)))).
  - exact Hpriv.
  - apply (exec_eff_check_CSR_result_csrw_pure csr_satp s);
      [ vm_compute; reflexivity
      | vm_compute; reflexivity
      | apply exec_eff_is_CSR_accessible_satp
      | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_satp; assumption.
  - apply exec_eff_csr_id_write_callback_satp.
Qed.

(* ====================================================================== *)
(** ** 2. sie (0x104; Ext_S-gated — WRITES [mie], READS [mideleg]) *)

Lemma exec_eff_write_CSR_sie (v : mword 64) s :
  exec_eff (write_CSR csr_sie v) s
    = Some (Ok (lower_mie
                  (sie_new_mie (register_lookup mie s.(sregs))
                     (register_lookup mideleg s.(sregs)) v)
                  (register_lookup mideleg s.(sregs))),
            set_reg s mie
              (sie_new_mie (register_lookup mie s.(sregs))
                 (register_lookup mideleg s.(sregs)) v), []).
Proof.
  unfold write_CSR, sie_new_mie.
  skip_csr_false_clauses_eff.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mie s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mideleg s)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg mie _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mie (set_reg s mie _))).
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_read_reg mideleg (set_reg s mie _))).
  rewrite register_lookup_set.
  rewrite irrelevant_register_set; [|vm_compute; reflexivity].
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_sie (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_sie d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_sie d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_csrw_sie (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s mie
            (sie_new_mie (register_lookup mie s.(sregs))
               (register_lookup mideleg s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv HS.
  change (execute (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_sie (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_sie rs1 s _
           (lower_mie
              (sie_new_mie (register_lookup mie s.(sregs))
                 (register_lookup mideleg s.(sregs))
                 (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                         s.(sregs)))
              (register_lookup mideleg s.(sregs)))).
  - exact Hpriv.
  - apply (exec_eff_check_CSR_result_csrw_S csr_sie s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | csr_dispatch_eq | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_sie.
  - apply exec_eff_csr_id_write_callback_sie.
Qed.

(* ====================================================================== *)
(** ** 3. pmpaddr0 (0x3b0; pure check — WRITES [pmpaddr_n], READS [pmpcfg_n]) *)

Lemma exec_eff_pmpWriteAddrReg_0 (v : mword 64) s :
  exec_eff (pmpWriteAddrReg 0 v) s
    = Some (tt, set_reg s pmpaddr_n
              (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                 (register_lookup pmpaddr_n s.(sregs)) v), []).
Proof.
  unfold pmpWriteAddrReg.
  replace (Z.ltb 0 sys_pmp_usable_count) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpaddr_n s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  replace (Z.ltb (Z.add 0 1) 64) with true by (vm_compute; reflexivity).
  cbn match.
  match goal with |- exec_eff (Defs.bind ?L _) s = _ =>
    assert (Hin : exec_eff L s
                  = Some (pmpTORLocked
                            (vec_access_dec
                               (register_lookup pmpcfg_n s.(sregs))
                               (Z.add 0 1)), s, [])) end.
  { rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
    apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hin).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpaddr_n s)).
  unfold pmp0_newaddr. apply exec_eff_write_reg.
Qed.

Lemma exec_eff_pmpReadAddrReg_0 s :
  exec_eff (pmpReadAddrReg 0) s
    = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0, s, []).
Proof.
  unfold pmpReadAddrReg.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpaddr_n s)).
  replace (Z.geb sys_pmp_grain 2) with false by (vm_compute; reflexivity).
  replace (Z.geb sys_pmp_grain 1) with false by (vm_compute; reflexivity).
  cbn match. apply exec_eff_returnM.
Qed.

Lemma exec_eff_pmpReadAddrReg_0_ok s :
  exec_eff (Defs.bind (pmpReadAddrReg 0)
              (fun w => returnM (Ok w) : M (result (mword 64) unit))) s
    = Some (Ok (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0), s, []).
Proof.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_pmpReadAddrReg_0 s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_write_CSR_pmpaddr0 (v : mword 64) s :
  exec_eff (write_CSR csr_pmpaddr0 v) s
    = Some (Ok (vec_access_dec
                  (register_lookup pmpaddr_n
                     (set_reg s pmpaddr_n
                        (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                           (register_lookup pmpaddr_n s.(sregs)) v)).(sregs)) 0),
            set_reg s pmpaddr_n
              (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                 (register_lookup pmpaddr_n s.(sregs)) v), []).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses_eff.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  cbn zeta.
  replace (uint (concat_vec ('b"00") (subrange_vec_dec csr_pmpaddr0 3 0))) with 0
    by (vm_compute; reflexivity).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_pmpWriteAddrReg_0 v s)).
  exact (exec_eff_pmpReadAddrReg_0_ok
           (set_reg s pmpaddr_n
              (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                 (register_lookup pmpaddr_n s.(sregs)) v))).
Qed.

Lemma exec_eff_csr_id_write_callback_pmpaddr0 (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_pmpaddr0 d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_pmpaddr0 d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_csrw_pmpaddr0 (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (execute (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s pmpaddr_n
            (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
               (register_lookup pmpaddr_n s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv.
  change (execute (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_pmpaddr0 (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_pmpaddr0 rs1 s _
           (vec_access_dec
              (register_lookup pmpaddr_n
                 (set_reg s pmpaddr_n
                    (pmp0_newaddr (register_lookup pmpcfg_n s.(sregs))
                       (register_lookup pmpaddr_n s.(sregs))
                       (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint rs1)))
                               s.(sregs)))).(sregs)) 0)).
  - exact Hpriv.
  - apply (exec_eff_check_CSR_result_csrw_pure csr_pmpaddr0 s);
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_pmpaddr0.
  - apply exec_eff_csr_id_write_callback_pmpaddr0.
Qed.

(* ====================================================================== *)
(** ** 4. THE LEAVES

    Each is [WeakLeafCsrw2.wwp_csrw_medeleg_leaf] — the batch-2 TEMPLATE —
    with the written cell and its value substituted, plus whatever extra
    cells the CSR's [write_CSR] touches. *)

Section leaves.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  (* -------------------------------------------------------------------- *)
  (** *** 4a. csrw satp — the ONE deviation from the template: the SXL fact
      is not in [wcfg_regs], so the leaf splits [mmode_config] and keeps a
      half across the funnel call (the SC [wp_csrw_satp_gpr] does the same),
      recombining it for the continuation.  The leaf's INTERFACE is the
      template's: a whole [mmode_config (DfracOwn q)] in, the same out. *)
  Lemma wwp_csrw_satp_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (satp0 rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    satp ↦ᵣ satp0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       satp ↦ᵣ satp_legalized satp0 rs1v -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont".
    (* keep a half of the config: [wcfg_regs] does not carry mstatus.SXL *)
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct (mmode_config_unbundle with "Hmm_k")
      as "(#Hhw & #Hmiv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr Φ pc false (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn (q/2))
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm_wp Hpmpc_wp Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the registers the funnel does not hand over: source, CSR, mstatus *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat satp σ b eq_refl)) Lcsr_a)
      as Lcsr.
    iDestruct (reg_valid_dq with "Hreg Hms_k") as %Lms_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mstatus σ b eq_refl)) Lms_a)
      as Lms.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hmsc : register_lookup mstatus
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = ms0).
      { rewrite (set_lookup_ne mstatus nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup mstatus _ b' eq_refl). exact Lms. }
      assert (Hcsrc : register_lookup satp
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = satp0).
      { rewrite (set_lookup_ne satp nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne satp (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lcsr. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      assert (HSc : eq_vec (_get_Misa_S (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      assert (HSXLc : _get_Mstatus_SXL (register_lookup mstatus
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4)))) = 'b"10")
        by (rewrite Hmsc; exact HSXL).
      pose proof (exec_eff_execute_csrw_satp rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc HSc HSXLc) as He.
      rewrite Hcsrc Hrs1c' in He.
      destruct (csrw_sexec_facts_r satp s0c b' (add_vec_int pc 4)
                  (satp_legalized satp0 rs1v)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hmsf : register_lookup mstatus
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = ms0).
    { rewrite (set_lookup_ne mstatus nextPC _ _ ltac:(reg_ne)).
      exact Lms_a. }
    assert (Hcsrf : register_lookup satp
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = satp0).
    { rewrite (set_lookup_ne satp nextPC _ _ ltac:(reg_ne)).
      exact Lcsr_a. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    assert (HSf : eq_vec (_get_Misa_S (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    assert (HSXLf : _get_Mstatus_SXL (register_lookup mstatus
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4)))) = 'b"10")
      by (rewrite Hmsf; exact HSXL).
    pose proof (exec_eff_execute_csrw_satp rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf HSf HSXLf) as Hef.
    rewrite Hcsrf Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ satp _ (satp_legalized satp0 rs1v)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     satp (satp_legalized satp0 rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r satp (wflat_st σ) b (add_vec_int pc 4)
                (satp_legalized satp0 rs1v)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    (* rebuild the config from the kept half *)
    iDestruct (mmode_config_rebuild (DfracOwn (q/2)) ms0 HmIE HMPRV HSXL HKF
                 with "Hhw Hmiv Hhs_k Hpriv_k Hms_k") as "Hmm_k'".
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hrs1c Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (* -------------------------------------------------------------------- *)
  (** *** 4b. csrw sie — the template with TWO extra cells: [mie] (written)
      and [mideleg] (read, returned unchanged). *)
  Lemma wwp_csrw_sie_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (mie0 mdl0 rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mie ↦ᵣ mie0 -∗
    mideleg ↦ᵣ mdl0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       mie ↦ᵣ sie_new_mie mie0 mdl0 rs1v -∗
       mideleg ↦ᵣ mdl0 -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hmie Hmdl #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr Φ pc false (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the three registers the funnel does not read *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hmie") as %Lmie_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mie σ b eq_refl)) Lmie_a)
      as Lmie.
    iDestruct (reg_valid with "Hreg Hmdl") as %Lmdl_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mideleg σ b eq_refl)) Lmdl_a)
      as Lmdl.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hmiec : register_lookup mie
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = mie0).
      { rewrite (set_lookup_ne mie nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne mie (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lmie. }
      assert (Hmdlc : register_lookup mideleg
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = mdl0).
      { rewrite (set_lookup_ne mideleg nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne mideleg (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lmdl. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      assert (HSc : eq_vec (_get_Misa_S (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrw_sie rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc HSc) as He.
      rewrite Hmiec Hmdlc Hrs1c' in He.
      destruct (csrw_sexec_facts_r mie s0c b' (add_vec_int pc 4)
                  (sie_new_mie mie0 mdl0 rs1v)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_sie, Regidx rs1, zreg, CSRRW)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hmief : register_lookup mie
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = mie0).
    { rewrite (set_lookup_ne mie nextPC _ _ ltac:(reg_ne)).
      exact Lmie_a. }
    assert (Hmdlf : register_lookup mideleg
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = mdl0).
    { rewrite (set_lookup_ne mideleg nextPC _ _ ltac:(reg_ne)).
      exact Lmdl_a. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    assert (HSf : eq_vec (_get_Misa_S (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrw_sie rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf HSf) as Hef.
    rewrite Hmief Hmdlf Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ mie _ (sie_new_mie mie0 mdl0 rs1v)
            with "Hreg Hmie") as "[Hreg Hmie]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     mie (sie_new_mie mie0 mdl0 rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r mie (wflat_st σ) b (add_vec_int pc 4)
                (sie_new_mie mie0 mdl0 rs1v)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hmie Hmdl Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (* -------------------------------------------------------------------- *)
  (** *** 4c. csrw pmpaddr0 — the template with the VECTOR cell [pmpaddr_n]
      in place of the CSR; the [pmpcfg_n] value the written value reads is
      the funnel's own ([wcfg_regs]'s [Lpmpc]), so no extra cell is held. *)
  Lemma wwp_csrw_pmpaddr0_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpaddr00 : type_of_register pmpaddr_n)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr00 rs1v -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr Φ pc false
              (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the two registers the funnel does not read: the source and pmpaddr_n *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat pmpaddr_n σ b eq_refl)) Lcsr_a)
      as Lcsr.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hpmpcc : register_lookup pmpcfg_n
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = pmpcfg0).
      { rewrite (set_lookup_ne pmpcfg_n nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup pmpcfg_n _ b' eq_refl). exact Lpmpc. }
      assert (Hcsrc : register_lookup pmpaddr_n
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = pmpaddr00).
      { rewrite (set_lookup_ne pmpaddr_n nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne pmpaddr_n (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lcsr. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      pose proof (exec_eff_execute_csrw_pmpaddr0 rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc) as He.
      rewrite Hpmpcc Hcsrc Hrs1c' in He.
      destruct (csrw_sexec_facts_r pmpaddr_n s0c b' (add_vec_int pc 4)
                  (pmp0_newaddr pmpcfg0 pmpaddr00 rs1v)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_pmpaddr0, Regidx rs1, zreg, CSRRW)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hpmpcf : register_lookup pmpcfg_n
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = pmpcfg0).
    { rewrite (set_lookup_ne pmpcfg_n nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat pmpcfg_n σ b eq_refl). exact Lpmpc. }
    assert (Hcsrf : register_lookup pmpaddr_n
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = pmpaddr00).
    { rewrite (set_lookup_ne pmpaddr_n nextPC _ _ ltac:(reg_ne)).
      exact Lcsr_a. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    pose proof (exec_eff_execute_csrw_pmpaddr0 rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf) as Hef.
    rewrite Hpmpcf Hcsrf Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ pmpaddr_n _ (pmp0_newaddr pmpcfg0 pmpaddr00 rs1v)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     pmpaddr_n (pmp0_newaddr pmpcfg0 pmpaddr00 rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r pmpaddr_n (wflat_st σ) b (add_vec_int pc 4)
                (pmp0_newaddr pmpcfg0 pmpaddr00 rs1v)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaves.

(* ====================================================================== *)
(** ** 5. Soundness check *)

Print Assumptions exec_eff_execute_csrw_satp.
Print Assumptions exec_eff_execute_csrw_sie.
Print Assumptions exec_eff_execute_csrw_pmpaddr0.
Print Assumptions wwp_csrw_satp_leaf.
Print Assumptions wwp_csrw_sie_leaf.
Print Assumptions wwp_csrw_pmpaddr0_leaf.
