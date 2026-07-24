From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec ExecCommon WpGpr.
Require Import InstrBytes.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.
Require Import WpGprCsrrCommon.

Lemma exec_read_CSR_menvcfg s :
  exec (read_CSR (Ox"30A")) s
    = Some (subrange_vec_dec (register_lookup menvcfg s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). apply exec_returnM. Qed.

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
      by csr_dispatch_eq.
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
      by csr_dispatch_eq.
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
    by csr_dispatch_eq.
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

Lemma menvcfg_rdval_set_nextPC (s : mstate) (v : mword 64) :
  menvcfg_rdval (set_reg s nextPC v) = menvcfg_rdval s.
Proof. unfold menvcfg_rdval, set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.
Lemma sie_rdval_set_nextPC (s : mstate) (v : mword 64) :
  sie_rdval (set_reg s nextPC v) = sie_rdval s.
Proof. unfold sie_rdval, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [| vm_compute; reflexivity]). reflexivity. Qed.

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
Section WpCsrrGprB.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* time (0xC01): Ext_Zicntr-gated, no misa premise needed (holds for any state).
     [mtime] lives in [clock_inv] and advances nondeterministically with the
     clock tick, so this leaf owns NO mtime cell and cannot pin the value the
     instruction reads: the continuation is ∀-quantified over the read value
     [tv].  (No clock_inv opening is needed either -- the exec witness reads
     mtime straight off the abstract step state σ.) *)
  Lemma wp_csrr_time_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) -∗
    ( ∀ tv : mword 64,
      mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg tv]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) pmpcfg0
              Hpmp Hstat with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LprivS : register_lookup cur_privilege
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = Machine).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    set (tv := time_rdval (set_reg σ nextPC (add_vec_int pc 4))).
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg tv) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg tv)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg tv)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_time, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_time zreg (Regidx rd) CSRRS).
      rewrite (exec_execute_csrr_time_gpr rd
                 (set_reg σ nextPC (add_vec_int pc 4)) Hrd LprivS).
      reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg tv)).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" $! tv with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap").
  Qed.

  (* menvcfg (0x30A): Ext_U-gated; misa.U recovered from hw_config. *)
  Lemma wp_csrr_menvcfg_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (menvcfg_in : mword 64) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menvcfg_in -∗
    instr pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (menvcfg_in)]> m) -∗
      menvcfg ↦ᵣ menvcfg_in -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) pmpcfg0
              Hpmp Hstat with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
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
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg menvcfg_in) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (menvcfg_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hcsr").
  Qed.
  (* sie (0x104): Ext_S-gated; misa.S recovered from hw_config.  The read
     value is a VIEW over TWO registers ([lower_mie mie mideleg]), so both
     cells are threaded (returned unchanged). *)
  Lemma wp_csrr_sie_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mie_in mideleg_in : mword 64) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mie ↦ᵣ mie_in -∗
    mideleg ↦ᵣ mideleg_in -∗
    instr pc false (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (lower_mie mie_in mideleg_in)]> m) -∗
      mie ↦ᵣ mie_in -∗
      mideleg ↦ᵣ mideleg_in -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hmie Hmdl Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)) pmpcfg0
              Hpmp Hstat with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
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
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (lower_mie mie_in mideleg_in)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (lower_mie mie_in mideleg_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hmie Hmdl").
  Qed.

End WpCsrrGprB.
