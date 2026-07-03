(* WpGprLui.v -- the LUI family, stated on the new [instr] / [mmode_config]
   / [gpr_file] layer (cf. wp_auipc_gpr / wp_addi_gpr).  LUI has no source
   register: it writes rd := sign_extend(imm << 12) -- an ABSOLUTE value, not
   PC-relative.  Built on [wp_instr]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* The value LUI writes: imm in bits [31:12], sign-extended to 64. *)
Definition luival (imm : mword 20) : mword 64 :=
  sign_extend' 64 (concat_vec imm ((Ox"000") : mword 12)).

(* register-GENERIC LUI execute: writes rd := luival imm (no source register),
   via the file-generic wX lemma ([exec_wX_bits_gpr]).  Independent of the
   gpr_file representation, so reused unchanged from the old development. *)
Lemma exec_execute_UTYPE_LUI_gpr (rd : mword 5) (imm : mword 20) s :
  exec (execute (UTYPE (imm, Regidx rd, LUI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (luival imm))).
Proof.
  change (execute (UTYPE (imm, Regidx rd, LUI)))
    with (execute_UTYPE imm (Regidx rd) LUI).
  unfold execute_UTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

Section WpLuiGpr.
  Context `{!riscvGS Σ}.

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
    iIntros (σ ns κs nt Hpceq) "Hsi".
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

(* Demonstration: ONE lemma [wp_lui_gpr] serves many destination regs. *)
Section WpLuiGprDemo.
  Context `{!riscvGS Σ}.
  Definition wp_lui_x5  (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 20) :=
    wp_lui_gpr E Φ pc false (mword_of_int 5) imm.
  Definition wp_lui_x28 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 20) :=
    wp_lui_gpr E Φ pc false (mword_of_int 28) imm.
  Goal gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 5 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpLuiGprDemo.
