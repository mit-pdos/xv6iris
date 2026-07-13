(* ZbbRtypeGpr.v -- register-generic execute facts for the two-source Zbb
   register ops kept in the U-mode decode image: ZBB_RTYPE (ANDN/ORN/XNOR/
   MAX{,U}/MIN{,U}/ROL/ROR) and ZBB_RTYPEW (ROLW/RORW).  Each reads rs1 and
   rs2, selects a pure result by [op], and writes rd; loop-free (the result
   is a [let result' := match op …]).  The nonzero-rd forms feed the
   two-source compute arm ustep_rtype2. *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpGpr ZicondGpr.
Local Open Scope Z_scope.
Import Defs.

(* The value ZBB_RTYPE writes to rd, as a function of the two source reads. *)
Definition zbb_rtype_val (op : brop_zbb) (rs1v rs2v : mword 64) : mword 64 :=
  match op with
  | ANDN => and_vec rs1v (not_vec rs2v)
  | ORN => or_vec rs1v (not_vec rs2v)
  | XNOR => not_vec (xor_vec rs1v rs2v)
  | MAX => if zopz0zK_s rs1v rs2v then rs1v else rs2v
  | MAXU => if zopz0zK_u rs1v rs2v then rs1v else rs2v
  | MIN => if zopz0zI_s rs1v rs2v then rs1v else rs2v
  | MINU => if zopz0zI_u rs1v rs2v then rs1v else rs2v
  | ROL => rotate_bits_left rs1v (subrange_vec_dec rs2v (Z.sub log2_xlen 1) 0)
  | ROR => rotate_bits_right rs1v (subrange_vec_dec rs2v (Z.sub log2_xlen 1) 0)
  end.

Lemma exec_execute_ZBB_RTYPE_gpr_nz (rs2 rs1 rd : mword 5) (op : brop_zbb) s :
  uint rd <> 0 ->
  exec (execute (ZBB_RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (zbb_rtype_val op (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  intro Hrd.
  change (execute (ZBB_RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op)))
    with (execute_ZBB_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) op).
  unfold execute_ZBB_RTYPE, zbb_rtype_val. cbn match. cbv zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

(* The value ZBB_RTYPEW writes: sext32 of a 32-bit rotate of rs1[31:0] by
   rs2[4:0]. *)
Definition zbb_rtypew_val (op : bropw_zbb) (rs1v rs2v : mword 64) : mword 64 :=
  sign_extend' 64
    (match op with
     | ROLW => rotate_bits_left (subrange_vec_dec rs1v 31 0) (subrange_vec_dec rs2v 4 0)
     | RORW => rotate_bits_right (subrange_vec_dec rs1v 31 0) (subrange_vec_dec rs2v 4 0)
     end).

Lemma exec_execute_ZBB_RTYPEW_gpr_nz (rs2 rs1 rd : mword 5) (op : bropw_zbb) s :
  uint rd <> 0 ->
  exec (execute (ZBB_RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (zbb_rtypew_val op (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  intro Hrd.
  change (execute (ZBB_RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op)))
    with (execute_ZBB_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) op).
  unfold execute_ZBB_RTYPEW, zbb_rtypew_val. cbn match. cbv zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.
