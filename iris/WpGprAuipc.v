(* WpGprAuipc.v -- the AUIPC family, stated on the new [instr] / [mmode_config]
   / [gpr_file] layer (cf. wp_addi_gpr).  AUIPC has no source register: it
   writes rd := pc + sign_extend(imm << 12).  Built on [wp_instr]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr WpAuipc.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* register-generic AUIPC execute: read PC, add auipc_off, write rd -- ANY rd,
   via the file-generic wX lemma ([exec_wX_bits_gpr]). *)
Lemma exec_execute_UTYPE_AUIPC_gpr (rd : mword 5) (imm : mword 20) s :
  exec (execute (UTYPE (imm, Regidx rd, AUIPC))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (add_vec (register_lookup PC s.(sregs)) (auipc_off imm)))).
Proof.
  change (execute (UTYPE (imm, Regidx rd, AUIPC)))
    with (execute_UTYPE imm (Regidx rd) AUIPC).
  unfold execute_UTYPE, auipc_off. cbn match.
  rewrite (exec_bind_Some _ _ _
             (add_vec (register_lookup PC s.(sregs))
                      (sign_extend' 64 (concat_vec imm (Ox"000")))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_get_arch_pc s)). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)). apply exec_returnm.
Qed.

Section WpAuipcGpr.
  Context `{!riscvGS Σ}.

  (* [instr]/[mmode_config]-formulated register-generic AUIPC WP, built on
     [wp_instr] -- stated exactly like [wp_addi_gpr] but with no source
     register: the result is [pc + auipc_off imm].  [gpr_file] is indexed by
     [regidx] and complete, so no membership obligation; [rd <> 0] is kept
     (the write to x0 is a no-op). *)
  Lemma wp_auipc_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5)
      (imm : mword 20) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc false (UTYPE (imm, Regidx rd, AUIPC)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
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
