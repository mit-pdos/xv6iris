From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvExec RiscvFetchExec ExecCommon WpGpr.
Require Import InstrBytes.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* Register-GENERIC MUL: ONE WP for 32-bit `mul rd,rs1,rs2`, ANY triple.   *)
(* Structurally identical to the generic ADD (WpGpr.v): reads rs1/rs2,     *)
(* writes rd; only the written value differs (the M-extension product      *)
(* [mult_to_bits_half] instead of [add_vec]).  Reuses [mulop_mul] (the      *)
(* funct3=000 signed/signed/Low op).                                       *)
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


(* ====================================================================== *)
(* The other two M-extension ops the kernel uses: DIVU and REMU (printint's *)
(* `x /= base` / `x % base`).  Both are structurally the MUL above -- read  *)
(* rs1 and rs2, write rd -- so only the written value differs.  Both are    *)
(* taken at [is_unsigned = true], which is what collapses the model's       *)
(* signed-overflow fixup ([andb (not is_unsigned) ..] is [false]); the      *)
(* divide-by-zero cases are the architectural ones (quotient -1, remainder  *)
(* the dividend), NOT a stuck state, so no side condition is needed.        *)
(* ====================================================================== *)

Definition gpr_uint_src (rs : mword 5) (s : mstate) : Z :=
  uint (if Z.eqb (uint rs) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs))) s.(sregs)).

Definition gpr_divu_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  to_bits_truncate 64
    (if Z.eqb (gpr_uint_src rs2 s) 0 then (-1)%Z
     else Z.quot (gpr_uint_src rs1 s) (gpr_uint_src rs2 s)).

Definition gpr_remu_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  to_bits_truncate 64
    (if Z.eqb (gpr_uint_src rs2 s) 0 then gpr_uint_src rs1 s
     else Z.rem (gpr_uint_src rs1 s) (gpr_uint_src rs2 s)).

Lemma exec_execute_DIVU_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, true))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_divu_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_divu_val, gpr_uint_src.
  change (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, true)))
    with (execute_DIV (Regidx rs2) (Regidx rs1) (Regidx rd) true).
  unfold execute_DIV.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn zeta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

Lemma exec_execute_REMU_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, true))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_remu_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_remu_val, gpr_uint_src.
  change (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, true)))
    with (execute_REM (Regidx rs2) (Regidx rs1) (Regidx rd) true).
  unfold execute_REM.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn zeta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
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
  Context `{GEN : GenId} `{CID : CpuId}.
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
  Lemma wp_mul_gpr (Φ : mval -> iProp Σ) (pc : mword 64) (rs2 rs1 rd : mword 5)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
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
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrd) "Hmm Hpmpc [Hpc Hnpc] Hfile Hinstr Hcont".
    iApply (wp_instr Φ pc false (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)) pmpcfg0
              Hpmp Hstat with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    (* tick nextPC first, so we read the sources against the execute state *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* read rs1 (x0 or a real register) -- borrow, read, return, so that
       reading rs2 (possibly = rs1) is an independent borrow *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg σ nextPC (add_vec_int pc 4)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    (* read rs2 (independent borrow; rs1 = rs2 is fine) *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2))
                 (set_reg σ nextPC (add_vec_int pc 4)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hmv : gpr_mul_val rs2 rs1 (set_reg σ nextPC (add_vec_int pc 4))
                  = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                      (mulop_mul.(mul_op_signed_rs2))
                      (m !!! Regidx rs1) (m !!! Regidx rs2)
                      (mulop_mul.(mul_op_result_part))).
    { unfold gpr_mul_val. rewrite Hrv1. rewrite Hrv2. reflexivity. }
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg
                    (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                       (mulop_mul.(mul_op_signed_rs2))
                       (m !!! Regidx rs1) (m !!! Regidx rs2)
                       (mulop_mul.(mul_op_result_part))))
                 with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg
               (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                  (mulop_mul.(mul_op_signed_rs2))
                  (m !!! Regidx rs1) (m !!! Regidx rs2)
                  (mulop_mul.(mul_op_result_part))))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
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
    { rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
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
    { rewrite ?sregs_set_reg.
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile").
  Qed.
End WpMulGpr.
