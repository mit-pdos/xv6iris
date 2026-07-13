(* M-mode Utype leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvFetchExec WpGpr MinstretInv InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values WpAuipc.
Import Defs.
Import Defs.

(* from WpGprAuipc.v *)
Section WpAuipcGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic AUIPC WP, built on
     [wp_instr] -- stated exactly like [wp_addi_gpr] but with no source
     register: the result is [pc + auipc_off imm].  [gpr_file] is indexed by
     [regidx] and complete, so no membership obligation; [rd <> 0] is kept
     (the write to x0 is a no-op). *)
  Lemma wp_auipc_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (imm : mword 20) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc false (UTYPE (imm, Regidx rd, AUIPC)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC; PC is unchanged, still [pc] *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (Hpcv : register_lookup PC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec pc (auipc_off imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec pc (auipc_off imm)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec pc (auipc_off imm)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm (set_reg σ nextPC (add_vec_int pc 4))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hpcv. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: PC/nextPC are both pc+4; hand everything back *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec pc (auipc_off imm)))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End WpAuipcGpr.

(* from WpGprLui.v *)
Section WpLuiGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic LUI WP, built on
     [wp_instr] -- stated exactly like [wp_auipc_gpr] but the written value is
     the ABSOLUTE [luival imm] (not PC-relative).  [gpr_file] is indexed by
     [regidx] and complete, so no membership obligation; [rd <> 0] is kept
     (the write to x0 is a no-op). *)
  Lemma wp_lui_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rd : mword 5)
      (imm : mword 20) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (UTYPE (imm, Regidx rd, LUI)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc is_rvc (UTYPE (imm, Regidx rd, LUI)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC; PC is unchanged, still [pc] *)
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival imm))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (luival imm))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (luival imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_UTYPE_LUI_gpr rd imm (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: PC/nextPC are both pc+4; hand everything back *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (luival imm))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End WpLuiGpr.
