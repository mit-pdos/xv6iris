(* M-mode Addiw leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpLeafCommon WpGpr MinstretInv InstrBytes RiscvModelBytes RiscvTryStep RiscvExtras WpLoad SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values WpAuipc WpDecode.
Import Defs.
Import Defs.

(* from WpGprAddi.v *)
Section WpAddiwGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Lemma wp_addiw_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5) (immv : mword 12)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (ADDIW (immv, Regidx rs1, Regidx rd)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (sign_extend' 64
          (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc is_rvc (ADDIW (immv, Regidx rs1, Regidx rd)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Hav : gpr_addiw_val rs1 immv (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = sign_extend' 64
                      (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)).
    { unfold gpr_addiw_val. rewrite Hrv. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sign_extend' 64
               (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sign_extend' 64
               (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sign_extend' 64
                  (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_ADDIW_gpr rs1 rd immv (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sign_extend' 64
                   (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpAddiwGpr.
