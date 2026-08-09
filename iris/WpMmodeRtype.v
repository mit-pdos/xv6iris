(* M-mode Rtype leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvFetchExec WpGpr InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import RegFile.
Import Defs.
Import Defs.

(* from WpGprLogic.v *)
Section WpLogicRTypeGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {dqc : dfrac}.

  Lemma wp_or_gpr (pc : mword 64) (is_rvc : bool) (rs2 rs1 rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    assert (Hm2 : rf_to_gmap m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    assert (Hmd : rf_to_gmap m !! Regidx rd = Some (m !!! Regidx rd))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Hmv : gpr_or_val rs2 rs1 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)).
    { unfold gpr_or_val. rewrite Hrv1. rewrite Hrv2. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) Hrd).
      rewrite Hmv. reflexivity. }
    iSplitL "Hreg Hmem".
    { rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { rewrite ?sregs_set_reg.
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. apply rf_to_gmap_dom. }
    rewrite rf_to_gmap_upd. iExact "Hfmap".
  Qed.

  Lemma wp_and_gpr (pc : mword 64) (is_rvc : bool) (rs2 rs1 rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    assert (Hm2 : rf_to_gmap m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    assert (Hmd : rf_to_gmap m !! Regidx rd = Some (m !!! Regidx rd))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Hmv : gpr_and_val rs2 rs1 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)).
    { unfold gpr_and_val. rewrite Hrv1. rewrite Hrv2. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_RTYPE_AND_gpr rs2 rs1 rd (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) Hrd).
      rewrite Hmv. reflexivity. }
    iSplitL "Hreg Hmem".
    { rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { rewrite ?sregs_set_reg.
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. apply rf_to_gmap_dom. }
    rewrite rf_to_gmap_upd. iExact "Hfmap".
  Qed.

  (* wp_add_gpr -- the RTYPE ADD member of the family (the ExecuteAs target of
     c.mv / c.add, hence [is_rvc]-generic like its siblings).  Uses WpGpr's
     [exec_execute_RTYPE_ADD_gpr] / [gpr_rd_val]. *)
  Lemma wp_add_gpr (pc : mword 64) (is_rvc : bool) (rs2 rs1 rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr pc is_rvc (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    assert (Hm2 : rf_to_gmap m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    assert (Hmd : rf_to_gmap m !! Regidx rd = Some (m !!! Regidx rd))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Hmv : gpr_rd_val rs2 rs1 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)).
    { unfold gpr_rd_val. rewrite Hrv1. rewrite Hrv2. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hmv. reflexivity. }
    iSplitL "Hreg Hmem".
    { rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { rewrite ?sregs_set_reg.
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. apply rf_to_gmap_dom. }
    rewrite rf_to_gmap_upd. iExact "Hfmap".
  Qed.

End WpLogicRTypeGpr.
