(* M-mode Itype leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RegFile RiscvPtsto RiscvFetchExec WpGpr InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Import Defs.
Import Defs.

(* from WpGprAddi.v *)
Section WpAddiGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {dqc : dfrac}.

  (* [instr]/[mmode_config]-formulated register-generic ADDI WP, built on
     [wp_instr].  All the fetch/decode/config machinery is now packaged: the
     caller supplies [mmode_config] (ambient M-mode config, incl. the minstret
     invariant and the mstatus.MIE fact) and [instr pc false (ITYPE .. ADDI)]
     (the instruction at pc decodes to ADDI, 4-byte).  This lemma's only real
     work is the ADDI execute: read rs1 and rd off the [gpr_file], run the
     register-generic execute, and rebuild the file.  [wp_instr] discharges
     fetch / decode / dispatchInterrupt / minstret and hands [mmode_config]
     back to the continuation. *)
  Lemma wp_addi_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hgf Hinstr Hcont".
    iApply (wp_instr Φ pc is_rvc (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    (* tick nextPC first, so we read rs1 against the execute state *)
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* read the rs1 entry (x0 or a real register) -> the ADDI value *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hgf") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 _
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hgf".
    assert (Hav : gpr_addi_val rs1 imm (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_addi_val. rewrite Hrv. reflexivity. }
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
                 with "Hgf") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hgf".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: PC/nextPC are both pc+4; hand back mmode_config, pmpcfg,
       the reassembled [pc_is (pc+4)], and the updated file *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec (m !!! Regidx rs1)
                   (sign_extend' 64 imm)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] Hgf").
  Qed.
End WpAddiGpr.

(* from WpGprLogic.v *)
Section WpLogicITypeGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {dqc : dfrac}.

  Lemma wp_ori_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 rd : mword 5)
      (imm : mword 12) (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hgf Hinstr Hcont".
    iApply (wp_instr Φ pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hgf") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 _
                 (set_reg σ nextPC (add_vec_int pc 4)) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hgf".
    assert (Hav : gpr_ori_val rs1 imm (set_reg σ nextPC (add_vec_int pc 4))
                  = or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_ori_val. rewrite Hrv. reflexivity. }
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
                 with "Hgf") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hgf".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_ITYPE_ORI_gpr rs1 rd imm (set_reg σ nextPC (add_vec_int pc 4))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (or_vec (m !!! Regidx rs1)
                   (sign_extend' 64 imm)))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] Hgf").
  Qed.


End WpLogicITypeGpr.
