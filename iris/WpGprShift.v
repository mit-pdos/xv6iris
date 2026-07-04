From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ---- base execute lemmas (take rX/wX facts), mirror exec_execute_ITYPE_ADDI ---- *)
Lemma exec_execute_SHIFTIOP_SLLI (shamt : mword 6) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) s = Some (tt, s') ->
  exec (execute (SHIFTIOP (shamt, rs1, rd, SLLI))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIOP (shamt, rs1, rd, SLLI))) with (execute_SHIFTIOP shamt rs1 rd SLLI).
  unfold execute_SHIFTIOP. cbn match.
  rewrite (exec_bind_Some _ _ _ (shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Lemma exec_execute_SHIFTIOP_SRLI (shamt : mword 6) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) s = Some (tt, s') ->
  exec (execute (SHIFTIOP (shamt, rs1, rd, SRLI))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIOP (shamt, rs1, rd, SRLI))) with (execute_SHIFTIOP shamt rs1 rd SRLI).
  unfold execute_SHIFTIOP. cbn match.
  rewrite (exec_bind_Some _ _ _ (shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

(* ---- register-generic value functions + execute lemmas ---- *)
Definition gpr_src (rs1 : mword 5) (s : mstate) : mword 64 :=
  if Z.eqb (uint rs1) 0 then zero_reg
  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs).

Definition gpr_slli_val (rs1 : mword 5) (shamt : mword 6) (s : mstate) : mword 64 :=
  shift_bits_left (gpr_src rs1 s) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).
Definition gpr_srli_val (rs1 : mword 5) (shamt : mword 6) (s : mstate) : mword 64 :=
  shift_bits_right (gpr_src rs1 s) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).

Lemma exec_execute_SHIFTIOP_SLLI_gpr (rs1 rd : mword 5) (shamt : mword 6) s :
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_slli_val rs1 shamt s))).
Proof.
  unfold gpr_slli_val, gpr_src.
  eapply exec_execute_SHIFTIOP_SLLI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Lemma exec_execute_SHIFTIOP_SRLI_gpr (rs1 rd : mword 5) (shamt : mword 6) s :
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_srli_val rs1 shamt s))).
Proof.
  unfold gpr_srli_val, gpr_src.
  eapply exec_execute_SHIFTIOP_SRLI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* ====================================================================== *)
(* New-style register-GENERIC shift-immediate WPs, built on [wp_instr].    *)
(* Each is like [wp_addi_gpr] (one source reg + an immediate/shamt): the    *)
(* caller supplies [mmode_config] + [instr pc false (<shift AST>)]; the WP  *)
(* reads rs1 off the [gpr_file], runs the register-generic execute, and     *)
(* rebuilds the file with rd updated.  Sources may be x0 ([gpr_pt_value]    *)
(* reads them uniformly, matching [gpr_src]); [rd <> 0] is kept.            *)
(* ====================================================================== *)

(* ===== slli ===== *)
Section Wp_slli.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.
  Lemma wp_slli_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (shift_bits_left (m !!! Regidx rs1)
          (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc is_rvc (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) pmpcfg0
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
    assert (Hav : gpr_slli_val rs1 shamt (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = shift_bits_left (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)).
    { unfold gpr_slli_val, gpr_src. rewrite Hrv. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
               (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
               (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                  (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                   (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End Wp_slli.

(* ===== srli ===== *)
Section Wp_srli.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.
  Lemma wp_srli_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (shift_bits_right (m !!! Regidx rs1)
          (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc is_rvc (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) pmpcfg0
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
    assert (Hav : gpr_srli_val rs1 shamt (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)).
    { unfold gpr_srli_val, gpr_src. rewrite Hrv. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
               (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
               (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                  (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hav. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                   (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold set_reg; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End Wp_srli.


(* Demonstrations: ONE lemma per type serves many register operands. *)
Section WpGprShiftDemo.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.
  Definition wp_slli_x5_x6  (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (sh : mword 6) :=
    wp_slli_gpr E Φ pc false (mword_of_int 6) (mword_of_int 5) sh.    (* slli x5, x6, sh *)
  Definition wp_slli_x28_x1 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (sh : mword 6) :=
    wp_slli_gpr E Φ pc false (mword_of_int 1) (mword_of_int 28) sh.   (* slli x28, x1, sh *)
  Definition wp_srli_x5_x6  (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (sh : mword 6) :=
    wp_srli_gpr E Φ pc false (mword_of_int 6) (mword_of_int 5) sh.
  Definition wp_srli_x28_x1 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (sh : mword 6) :=
    wp_srli_gpr E Φ pc false (mword_of_int 1) (mword_of_int 28) sh.
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 15 : mword 5)) = x15
    /\ uint (mword_of_int 28 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpGprShiftDemo.
