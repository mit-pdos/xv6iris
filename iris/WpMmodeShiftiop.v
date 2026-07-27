From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpGpr RegFile.
Require Import InstrBytes.
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

(* the 32-bit (W) shift-immediate: the source is truncated to 32 bits, shifted
   by a 5-bit shamt, and the 32-bit result is sign-extended back to 64. *)
Lemma exec_execute_SHIFTIWOP_SLLIW (shamt : mword 5) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (sign_extend' 64 (shift_bits_left (subrange_vec_dec a 31 0 : mword 32) shamt)))
       s = Some (tt, s') ->
  exec (execute (SHIFTIWOP (shamt, rs1, rd, SLLIW))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIWOP (shamt, rs1, rd, SLLIW))) with (execute_SHIFTIWOP shamt rs1 rd SLLIW).
  unfold execute_SHIFTIWOP. cbn match.
  rewrite (exec_bind_Some _ _ _ a s Ha).
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

Definition gpr_slliw_val (rs1 : mword 5) (shamt : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64 (shift_bits_left (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32) shamt).

Lemma exec_execute_SHIFTIWOP_SLLIW_gpr (rs1 rd : mword 5) (shamt : mword 5) s :
  exec (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_slliw_val rs1 shamt s))).
Proof.
  unfold gpr_slliw_val, gpr_src.
  eapply exec_execute_SHIFTIWOP_SLLIW.
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
  Lemma wp_slli_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5) (shamt : mword 6)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
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
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfile Hinstr Hcont".
    iApply (wp_instr Φ pc is_rvc (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hav : gpr_slli_val rs1 shamt (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = shift_bits_left (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)).
    { unfold gpr_slli_val, gpr_src. rewrite Hrv. reflexivity. }
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
               (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
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
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile").
  Qed.
End Wp_slli.

(* ===== srli ===== *)
Section Wp_srli.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.
  Lemma wp_srli_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5) (shamt : mword 6)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
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
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfile Hinstr Hcont".
    iApply (wp_instr Φ pc is_rvc (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hav : gpr_srli_val rs1 shamt (set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
                  = shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)).
    { unfold gpr_srli_val, gpr_src. rewrite Hrv. reflexivity. }
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
               (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
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
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile").
  Qed.
End Wp_srli.

(* ===================================================================== *)
(* SRAI / MUL / ADDW: the exec bridges.  Lifted out of ProofProcMapstacks *)
(* -- a Proof file must not be imported -- so any function stepping these *)
(* opcodes can reach them; procinit's KSTACK(i) computation is the next.  *)
(* They live HERE rather than in WpMmodeLeafBase because they are stated  *)
(* over [gpr_src], which this file owns.  See code-organization.md.       *)
(* ===================================================================== *)

(* ---- SRAI exec leaf (mirror SRLI) ---- *)
Lemma exec_execute_SHIFTIOP_SRAI (shamt : mword 6) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (shift_bits_right_arith a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))) s = Some (tt, s') ->
  exec (execute (SHIFTIOP (shamt, rs1, rd, SRAI))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIOP (shamt, rs1, rd, SRAI))) with (execute_SHIFTIOP shamt rs1 rd SRAI).
  unfold execute_SHIFTIOP. cbn match.
  rewrite (exec_bind_Some _ _ _ (shift_bits_right_arith a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Definition gpr_srai_val (rs1 : mword 5) (shamt : mword 6) (s : mstate) : mword 64 :=
  shift_bits_right_arith (gpr_src rs1 s) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).

Lemma exec_execute_SHIFTIOP_SRAI_gpr (rs1 rd : mword 5) (shamt : mword 6) s :
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRAI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_srai_val rs1 shamt s))).
Proof.
  unfold gpr_srai_val, gpr_src.
  eapply exec_execute_SHIFTIOP_SRAI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* ---- RTYPEW ADDW exec leaf ---- *)
Definition gpr_addw_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64 (add_vec (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32)
                           (subrange_vec_dec (gpr_src rs2 s) 31 0 : mword 32)).

Lemma exec_execute_RTYPEW_ADDW_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_addw_val rs2 rs1 s))).
Proof.
  unfold gpr_addw_val, gpr_src.
  change (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW)))
    with (execute_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) ADDW).
  unfold execute_RTYPEW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

(* ---- RTYPEW SUBW exec leaf (mirror ADDW): the 32-bit [subw] whose
   sign-extended result is what C's [int] subtraction leaves in the
   register.  sys_pause's [ticks - ticks0] is the first user. ---- *)
Definition gpr_subw_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64 (sub_vec (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32)
                           (subrange_vec_dec (gpr_src rs2 s) 31 0 : mword 32)).

Lemma exec_execute_RTYPEW_SUBW_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (gpr_subw_val rs2 rs1 s))).
Proof.
  unfold gpr_subw_val, gpr_src.
  change (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)))
    with (execute_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) SUBW).
  unfold execute_RTYPEW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.
