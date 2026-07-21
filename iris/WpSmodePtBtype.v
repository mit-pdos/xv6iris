(* S-mode Btype (branch) leaf lemmas over the generalized page-table
   invariant [tlb_inv_pt] (ptree abstraction, Svadu/ADUE).
   Ports of the WpSmodeBtype leaves. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes WpLeafCommon WpGpr RegFile.
Require Import SRegime.
Require Import SmodeCore.
Require Import KptTree SmodeCorePt.
Import Defs.

(* ---- Local helpers copied from WpSmodeBtype.v ---- *)
Local Definition rvv (r : mword 5) (s : mstate) : mword 64 :=
    if Z.eqb (uint r) 0 then zero_reg
    else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s.(sregs).

Local Lemma exec_BTYPE_cmp_BNE (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (neq_vec w2 w3)))) s
      = Some (neq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

(* helper: exec_BTYPE_cmp_BEQ *)
Local Lemma exec_BTYPE_cmp_BEQ (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (eq_vec w2 w3)))) s
      = Some (eq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

(* helper: exec_execute_BTYPE_BNE_fall *)
Local Lemma exec_execute_BTYPE_BNE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

(* helper: exec_execute_BTYPE_BEQ_fall *)
Local Lemma exec_execute_BTYPE_BEQ_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

(* helper: exec_BTYPE_cmp_BGE *)
Local Lemma exec_BTYPE_cmp_BGE (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zKzJ_s w2 w3)))) s
    = Some (zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

(* helper: exec_BTYPE_cmp_BLTU *)

(* helper: exec_execute_BTYPE_BLTU_fall *)

(* helper: exec_execute_BTYPE_BEQ_taken *)

(* helper: exec_execute_BTYPE_BGE_fall *)

(* helper: exec_execute_BTYPE_BNE_taken *)

(* helper: exec_jump_to_zca *)
Local Lemma exec_jump_to_zca (target : mword 64) s :
    eq_vec (access_vec_dec target 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
  Proof.
    intros Halign Hzca.
    unfold jump_to. rewrite exec_catch_early_return.
    change (ext_control_check_pc target) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold Defs.bind0.
        erewrite execR_bind_Some.
        2:{ erewrite execR_bind_Some.
            2:{ apply execR_returnR_fwd. }
            rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
            rewrite exec_returnm. reflexivity. }
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
        2:{ apply execR_returnR_fwd. }
        destruct (bit_to_bool (access_vec_dec target 1)).
        - cbv iota beta.
          rewrite (execR_bind_Some _ _ _ true s).
          2:{ rewrite execR_liftR. rewrite Hzca. reflexivity. }
          cbv iota beta. apply execR_returnR_fwd.
        - cbv iota beta. apply execR_returnR_fwd. }
    cbv iota beta.
    unfold Defs.bind0.
    rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
    2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
    rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
    reflexivity.
  Qed.

(* helper: exec_execute_BTYPE_BNE_taken_zca *)
Local Lemma exec_execute_BTYPE_BNE_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

(* helper: exec_execute_BTYPE_BEQ_taken_zca *)
Local Lemma exec_execute_BTYPE_BEQ_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.


Section WpSmodePtBtype.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_beq_fall_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_regime R Φ pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs1)) with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs2)) with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.


  Lemma wp_beq_fall_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hsm Htlbinv Hpc Hgpr Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_beq_fall_s_config_r R Φ pc imm rs2 rs1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hgpr").
  Qed.


  Lemma wp_beq_taken_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    (* only 2-alignment of the target is required: the C extension (Zca,
       derived internally from misa.C) legalizes a bit1 = 1 branch target. *)
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp Hal0)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_config_regime R Φ pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs1)) with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs2)) with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : eq_vec (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BEQ_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.


  Lemma wp_beq_taken_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    eq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal) "Hsm Htlbinv Hpc Hgpr Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_beq_taken_s_config_r R Φ pc imm rs2 rs1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp Hal
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hgpr").
  Qed.


  (* beq rs1, x0 (beqz) FALL-THROUGH: the x0 side reads zero_reg; the
     catalog spells the rs2 slot [zreg] *)






  Lemma wp_bne_fall_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_regime R Φ pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs1)) with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs2)) with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BNE_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.


  Lemma wp_bne_fall_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp) "Hsm Htlbinv Hpc Hgpr Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_bne_fall_s_config_r R Φ pc imm rs2 rs1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hgpr").
  Qed.




  Lemma wp_bne_taken_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    (* only 2-alignment of the target is required: the C extension (Zca,
       derived internally from misa.C) legalizes a bit1 = 1 branch target. *)
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp Hal0)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_config_regime R Φ pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs1)) with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs2)) with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : neq_vec (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.


  Lemma wp_bne_taken_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : regfile) {dq : dfrac} :
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hrs2 Hcmp Hal) "Hsm Htlbinv Hpc Hgpr Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_bne_taken_s_config_r R Φ pc imm rs2 rs1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs1 Hrs2 Hcmp Hal
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hgpr".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hgpr").
  Qed.


  Lemma wp_cbeqz_fall_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs Hrd1 Hcmp)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_regime R Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rd1)) with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.


  Lemma wp_cbeqz_fall_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile) {dq : dfrac} :
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = false ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs Hrd1 Hcmp) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cbeqz_fall_s_config_r R Φ pc imm8 rs rd1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs Hrd1 Hcmp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.








  Lemma wp_cbeqz_taken_s_config_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let imm : mword 13 := sign_extend' 13 (concat_vec imm8 ('b"0")) in
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (imm, zreg, creg2reg_idx rs, BEQ)) -∗
    (* The continuation is under a LATER.  A branch-taken leaf is the back edge
       of a loop, and the caller's Löb IH is itself under a later, so a leaf
       that silently consumed the step's later would make the IH unusable and
       force the caller down to the raw engine.  Handing the later out costs
       nothing (any caller can weaken with [iNext]) and is what lets an
       unbounded loop close against a packaged leaf. *)
    ( ▷ ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs Hrd1 Hcmp Hal0)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_config_regime R Φ pc true (BTYPE (imm, zreg, creg2reg_idx rs, BEQ))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rd1)) with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : eq_vec (rvv rd1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BEQ_taken_zca imm (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
                     (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
                   = add_vec pc (sign_extend' 64 imm))
      by (rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    (* the step's later, handed straight through to the continuation *)
    iNext.
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.


  Lemma wp_cbeqz_taken_s_config_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile) {dq : dfrac} :
    let imm : mword 13 := sign_extend' 13 (concat_vec imm8 ('b"0")) in
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (imm, zreg, creg2reg_idx rs, BEQ)) -∗
    (* under a LATER, so a loop's Löb IH can be discharged here -- see
       [wp_cbeqz_taken_s_config_pt] *)
    ( ▷ ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros imm.
    iIntros (Hrs Hrd1 Hcmp Hal0) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cbeqz_taken_s_config_r R Φ pc imm8 rs rd1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs Hrd1 Hcmp Hal0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iNext.
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.








  Lemma wp_cbnez_fall_s_r (R : s_regime) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (m !!! Regidx rd1) zero_reg = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs Hrd1 Hcmp)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_regime R Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              mstatus0 mie_v mdv0 menvcfg0
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq)
      "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rd1)) with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m (Regidx rd1)) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BNE_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.


  Lemma wp_cbnez_fall_s_scfg_r (R : s_regime) (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : regfile) {dq : dfrac} :
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (m !!! Regidx rd1) zero_reg = false ->
    smode_config γ dq -∗ sr_inv R -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE)) -∗
    ( smode_config γ dq -∗ sr_inv R -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs Hrd1 Hcmp) "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_cbnez_fall_s_r R Φ pc imm8 rs rd1 m mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
 HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs Hrd1 Hcmp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile").
  Qed.


















End WpSmodePtBtype.
