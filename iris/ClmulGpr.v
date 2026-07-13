(* ClmulGpr.v -- register-generic execute facts for the carryless-multiply
   ops CLMUL / CLMULH / CLMULR (Zbc, in the U-mode decode image).  Each reads
   rs1 and rs2, applies a pure carryless product, and writes rd; loop-free at
   the exec level (carryless_mul/carryless_mulr are pure functions under a
   let).  The nonzero-rd forms feed the two-source compute arm ustep_rtype2. *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpGpr ZicondGpr.
Local Open Scope Z_scope.
Import Defs.

(* CLMUL rd, rs1, rs2 : rd := low xlen bits of carryless_mul(rs1, rs2). *)
Lemma exec_execute_CLMUL_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (CLMUL (Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (subrange_vec_dec (carryless_mul (gpr_val rs1 s) (gpr_val rs2 s))
                       (Z.sub xlen 1) 0))).
Proof.
  change (execute (CLMUL (Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_CLMUL (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_CLMUL. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbv zeta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

Lemma exec_execute_CLMUL_gpr_nz (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (CLMUL (Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (subrange_vec_dec (carryless_mul (gpr_val rs1 s) (gpr_val rs2 s))
                  (Z.sub xlen 1) 0))).
Proof.
  intro Hrd.
  change (execute (CLMUL (Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_CLMUL (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_CLMUL. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbv zeta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

(* CLMULH rd, rs1, rs2 : rd := high xlen bits of carryless_mul(rs1, rs2). *)
Lemma exec_execute_CLMULH_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (CLMULH (Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (subrange_vec_dec (carryless_mul (gpr_val rs1 s) (gpr_val rs2 s))
                       (Z.sub (Z.mul 2 xlen) 1) xlen))).
Proof.
  change (execute (CLMULH (Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_CLMULH (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_CLMULH. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbv zeta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

Lemma exec_execute_CLMULH_gpr_nz (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (CLMULH (Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (subrange_vec_dec (carryless_mul (gpr_val rs1 s) (gpr_val rs2 s))
                  (Z.sub (Z.mul 2 xlen) 1) xlen))).
Proof.
  intro Hrd.
  change (execute (CLMULH (Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_CLMULH (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_CLMULH. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbv zeta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

(* CLMULR rd, rs1, rs2 : rd := carryless_mulr(rs1, rs2) (reversed product). *)
Lemma exec_execute_CLMULR_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (CLMULR (Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (carryless_mulr (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  change (execute (CLMULR (Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_CLMULR (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_CLMULR. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

Lemma exec_execute_CLMULR_gpr_nz (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (CLMULR (Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (carryless_mulr (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  intro Hrd.
  change (execute (CLMULR (Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_CLMULR (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_CLMULR. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.
