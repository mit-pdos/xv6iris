(* M-mode Addiw leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvFetchExec WpGpr RegFile InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Import Defs.
Import Defs.

(* from WpGprAddi.v *)
Section WpAddiwGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Lemma wp_addiw_gpr (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5) (immv : mword 12)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
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
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfile Hinstr Hcont".
    iApply (wp_instr pc is_rvc (ADDIW (immv, Regidx rs1, Regidx rd)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hav : gpr_addiw_val rs1 immv (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = sign_extend' 64
                      (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)).
    { unfold gpr_addiw_val. rewrite Hrv. reflexivity. }
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (sign_extend' 64
                    (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))
               with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sign_extend' 64
               (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
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
    { rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sign_extend' 64
                   (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { rewrite ?sregs_set_reg. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile").
  Qed.

End WpAddiwGpr.
