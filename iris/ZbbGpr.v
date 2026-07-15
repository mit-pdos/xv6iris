(* ZbbGpr.v -- register-generic execute facts for the single-source Zbb
   ops kept in the U-mode decode image: REV8, RORI, RORIW (their decode gate
   is Zbb OR Zbkb, and Zbkb is on).  Each reads rs1, applies a pure bit
   transform, and writes rd; the register-generic (x0-aware) execute fact is
   the classification-time input to the single-source compute arm
   ustep_compute1. *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec.
Require Import WpGpr ZicondGpr.
Local Open Scope Z_scope.
Import Defs.

(* REV8 rd, rs1 : rd := byte-reverse(rs1). *)
Lemma exec_execute_REV8_gpr (rs1 rd : mword 5) s :
  exec (execute (REV8 (Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (rev8 (gpr_val rs1 s)))).
Proof.
  change (execute (REV8 (Regidx rs1, Regidx rd)))
    with (execute_REV8 (Regidx rs1) (Regidx rd)).
  unfold execute_REV8. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

(* RORI rd, rs1, shamt : rd := rotate-right(rs1, shamt[log2_xlen-1:0]). *)
Lemma exec_execute_RORI_gpr (shamt : mword 6) (rs1 rd : mword 5) s :
  exec (execute (RORI (shamt, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (rotate_bits_right (gpr_val rs1 s)
                       (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))).
Proof.
  change (execute (RORI (shamt, Regidx rs1, Regidx rd)))
    with (execute_RORI shamt (Regidx rs1) (Regidx rd)).
  unfold execute_RORI. cbv zeta. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

(* RORIW rd, rs1, shamt : rd := sext32(rotate-right(rs1[31:0], shamt)). *)
Lemma exec_execute_RORIW_gpr (shamt : mword 5) (rs1 rd : mword 5) s :
  exec (execute (RORIW (shamt, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (sign_extend' 64
                       (rotate_bits_right (subrange_vec_dec (gpr_val rs1 s) 31 0) shamt)))).
Proof.
  change (execute (RORIW (shamt, Regidx rs1, Regidx rd)))
    with (execute_RORIW shamt (Regidx rs1) (Regidx rd)).
  unfold execute_RORIW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.
