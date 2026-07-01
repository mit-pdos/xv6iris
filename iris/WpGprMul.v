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

(* ====================================================================== *)
(* Register-GENERIC MUL: ONE WP for 32-bit `mul rd,rs1,rs2`, ANY triple.   *)
(* Structurally identical to the generic ADD (WpGpr.v): reads rs1/rs2,     *)
(* writes rd; only the written value differs (the M-extension product      *)
(* [mult_to_bits_half] instead of [add_vec]).  Reuses [mulop_mul] (the      *)
(* funct3=000 signed/signed/Low op) from WpEntry.v.                         *)
(* ====================================================================== *)

(* The value MUL writes to rd, expressed over the file-generic reads. *)
Definition gpr_mul_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
    (mulop_mul.(mul_op_result_part)).

Lemma exec_execute_MUL_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_mul_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_mul_val.
  change (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)))
    with (execute_MUL (Regidx rs2) (Regidx rs1) (Regidx rd) mulop_mul).
  unfold execute_MUL.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

Lemma gpr_mul_val_lookup (rs2 rs1 : mword 5) (t : mstate) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  gpr_mul_val rs2 rs1 t
  = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
      (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs))
      (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) t.(sregs))
      (mulop_mul.(mul_op_result_part)).
Proof.
  intros H1 H2. unfold gpr_mul_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (Z.eqb (uint rs2) 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  reflexivity.
Qed.

(* ====================================================================== *)
(* The register-GENERIC MUL WP: ONE lemma for `mul rd,rs1,rs2`, ANY        *)
(* register triple (rs1/rs2/rd arbitrary; rs1 may equal rs2), with all     *)
(* GPRs held as the single [gpr_file] resource.  Stated on the new         *)
(* [instr] / [mmode_config] / [gpr_file] layer, built on [wp_instr]        *)
(* (cf. [wp_addi_gpr]).  MUL is like ADDI but reads TWO source registers   *)
(* (rs1, rs2) instead of one source + immediate, writing                   *)
(*   rd := (rs1 * rs2) truncated to XLEN bits                              *)
(* (the M-extension product [mult_to_bits_half]).                          *)
(* ====================================================================== *)
Section WpMulGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  (* [instr]/[mmode_config]-formulated register-generic MUL WP, built on
     [wp_instr].  As with [wp_addi_gpr], all fetch/decode/config machinery is
     packaged: the caller supplies [mmode_config] and
     [instr pc false (MUL .. mulop_mul)] (the instruction at pc decodes to MUL,
     4-byte).  This lemma's only work is the MUL execute: read rs1 AND rs2 off
     the [gpr_file] (each source borrowed independently, so rs1 = rs2 is fine),
     run the register-generic execute, and rebuild the file.  Sources may be x0
     ([gpr_pt_value] reads them uniformly); [rd <> 0] is kept (write to x0 is a
     no-op, and [exec_execute_MUL_gpr] assumes it). *)
  Lemma wp_mul_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs2 rs1 rd : mword 5)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg
          (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
             (mulop_mul.(mul_op_signed_rs2))
             (m !!! Regidx rs1) (m !!! Regidx rs2)
             (mulop_mul.(mul_op_result_part)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc false (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)) pmpcfg0
              HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    (* completeness gives the (total) lookups for rs1, rs2 and rd *)
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC first, so we read the sources against the execute state *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* read rs1 (x0 or a real register) -- borrow, read, return, so that
       reading rs2 (possibly = rs1) is an independent borrow *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1)
                 (set_reg σ nextPC (add_vec_int pc 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    (* read rs2 (independent borrow; rs1 = rs2 is fine) *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2)
                 (set_reg σ nextPC (add_vec_int pc 4)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Hmv : gpr_mul_val rs2 rs1 (set_reg σ nextPC (add_vec_int pc 4))
                  = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                      (mulop_mul.(mul_op_signed_rs2))
                      (m !!! Regidx rs1) (m !!! Regidx rs2)
                      (mulop_mul.(mul_op_result_part))).
    { unfold gpr_mul_val. rewrite Hrv1. rewrite Hrv2. reflexivity. }
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg
               (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                  (mulop_mul.(mul_op_signed_rs2))
                  (m !!! Regidx rs1) (m !!! Regidx rs2)
                  (mulop_mul.(mul_op_result_part))))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg
               (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                  (mulop_mul.(mul_op_signed_rs2))
                  (m !!! Regidx rs1) (m !!! Regidx rs2)
                  (mulop_mul.(mul_op_result_part))))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ nextPC (add_vec_int pc 4))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg
                  (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                     (mulop_mul.(mul_op_signed_rs2))
                     (m !!! Regidx rs1) (m !!! Regidx rs2)
                     (mulop_mul.(mul_op_result_part))))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      rewrite (exec_execute_MUL_gpr rs2 rs1 rd (set_reg σ nextPC (add_vec_int pc 4)) Hrd).
      rewrite Hmv. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: PC/nextPC are both pc+4; hand back mmode_config, pmpcfg,
       the reassembled [pc_is (pc+4)], and the updated file *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg
                   (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                      (mulop_mul.(mul_op_signed_rs2))
                      (m !!! Regidx rs1) (m !!! Regidx rs2)
                      (mulop_mul.(mul_op_result_part))))).(sregs)
             = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End WpMulGpr.

(* ====================================================================== *)
(* Demonstration: ONE lemma [wp_mul_gpr] serves many register triples.     *)
(* ====================================================================== *)
Section WpMulGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  (* `mul x5, x6, x7` : rd=x5, rs1=x6, rs2=x7. *)
  Definition wp_mul_x5_x6_x7 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_mul_gpr E Φ pc (mword_of_int 7) (mword_of_int 6) (mword_of_int 5).
  (* `mul x28, x1, x2` : rd=x28, rs1=x1, rs2=x2.  SAME lemma, different regs. *)
  Definition wp_mul_x28_x1_x2 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_mul_gpr E Φ pc (mword_of_int 2) (mword_of_int 1) (mword_of_int 28).
  (* `mul x5, x6, x6` : rs1 = rs2 = x6.  SAME lemma. *)
  Definition wp_mul_x5_x6_x6 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_mul_gpr E Φ pc (mword_of_int 6) (mword_of_int 6) (mword_of_int 5).

  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 7 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpMulGprDemo.
