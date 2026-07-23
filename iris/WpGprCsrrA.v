From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec ExecCommon WpGpr.
Require Import RegFile.
Require Import InstrBytes.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.
Require Import WpGprCsrrCommon.

(* ====================================================================== *)
(* Register-generic CSR-read execute: csrr rd, mhartid (= csrrs rd,mhartid,x0).*)
(* The CSR read (mhartid) and the x0 source stay fixed; only the           *)
(* destination [rd] is generalized.  CSRRS with a zero source always yields  *)
(* access type CSRRead, independent of rd.                                   *)
(* ====================================================================== *)
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

Lemma exec_read_CSR_mcounteren s :
  exec (read_CSR (Ox"306")) s
    = Some (zero_extend' 64 (register_lookup mcounteren s.(sregs)), s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)). apply exec_returnM. Qed.

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
      by csr_dispatch_eq.
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

Lemma mstatus_rdval_set_nextPC (s : mstate) (v : mword 64) :
  mstatus_rdval (set_reg s nextPC v) = mstatus_rdval s.
Proof. unfold mstatus_rdval, set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. Qed.
Lemma mcounteren_rdval_set_nextPC (s : mstate) (v : mword 64) :
  mcounteren_rdval (set_reg s nextPC v) = mcounteren_rdval s.
Proof. unfold mcounteren_rdval, set_reg; cbn [sregs].
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
  Context `{CID : CpuId}.

  Lemma wp_csrr_mhartid_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mhartid_in : mword 64) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    instr pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg mhartid_in]> m) -∗
      mhartid ↦ᵣ mhartid_in -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hmh Hinstr Hcont".
    (* keep half of [mmode_config] to read cur_privilege at the execute state *)
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
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
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg mhartid_in)
                 with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg mhartid_in)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hmh").
  Qed.
End WpCsrrMhartidGpr.
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
Section WpCsrrGprA.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* mstatus (0x300): machine CSR, no extra gate. *)
  (* [dqm]-generic mstatus cell: mstatus lives INSIDE [mmode_config], so a
     chain can only ever hand this WP a FRACTION of the cell (the half it
     kept outside its working bundle to pin the value).  Only the value is
     read, so any fraction works. *)
  Lemma wp_csrr_mstatus_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mstatus_in : mword 64) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) {dqm : dfrac} :
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mstatus ↦ᵣ{dqm} mstatus_in -∗
    instr pc false (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (mstatus_in)]> m) -∗
      mstatus ↦ᵣ{dqm} mstatus_in -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hcsr") as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (LprivS : register_lookup cur_privilege
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = Machine).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Hrv : mstatus_rdval (set_reg σ nextPC (add_vec_int pc 4))
             = mstatus_in).
    { rewrite mstatus_rdval_set_nextPC. unfold mstatus_rdval. rewrite Lcsr. apply subrange64_id. }
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (mstatus_in))
                 with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (mstatus_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hcsr").
  Qed.

  (* mcounteren (0x306): Ext_U-gated; misa.U recovered from hw_config. *)
  Lemma wp_csrr_mcounteren_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (mcen_in : mword 32) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    mcounteren ↦ᵣ mcen_in -∗
    instr pc false (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (zero_extend' 64 mcen_in)]> m) -∗
      mcounteren ↦ᵣ mcen_in -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split_half_csrr with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr Φ pc false (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
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
    assert (Hrv : mcounteren_rdval (set_reg σ nextPC (add_vec_int pc 4))
             = zero_extend' 64 mcen_in).
    { rewrite mcounteren_rdval_set_nextPC. unfold mcounteren_rdval. rewrite Lcsr. reflexivity. }
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (zero_extend' 64 mcen_in))
                 with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (zero_extend' 64 mcen_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
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
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine_half_csrr with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hcsr").
  Qed.
End WpCsrrGprA.
