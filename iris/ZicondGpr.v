(* ZicondGpr.v -- register-generic execute fact for Zicond (CZERO.EQZ/NEZ).

   ZICOND_RTYPE is a loop-free, register-only conditional-zero: it reads rs2,
   forms a condition (rs2 == 0 for CZERO_EQZ, rs2 <> 0 for CZERO_NEZ), and
   writes rd := if condition then 0 else rs1.  The register-generic execute
   fact (any rs1/rs2/rd, x0-aware via the file-generic rX/wX lemmas) is the
   classification-time input to the two-source compute arm ustep_rtype2. *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep.
Require Import WpGpr.
Local Open Scope Z_scope.
Import Defs.

(* x0-aware value read out of register index [i] (what rX_bits returns). *)
Definition gpr_val (i : mword 5) (s : mstate) : mword 64 :=
  if Z.eqb (uint i) 0 then zero_reg
  else register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) s.(sregs).

(* The condition CZERO tests on rs2. *)
Definition zicond_cond (op : zicondop) (rs2 : mword 5) (s : mstate) : bool :=
  match op with
  | CZERO_EQZ => eq_vec (gpr_val rs2 s) (zeros' 64)
  | CZERO_NEZ => neq_vec (gpr_val rs2 s) (zeros' 64)
  end.

(* The value written to rd. *)
Definition zicond_rd_val (op : zicondop) (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  if zicond_cond op rs2 s then zeros' 64 else gpr_val rs1 s.

Lemma exec_execute_ZICOND_RTYPE_gpr (rs2 rs1 rd : mword 5) (op : zicondop) s :
  exec (execute_ZICOND_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) op) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (zicond_rd_val op rs2 rs1 s))).
Proof.
  unfold execute_ZICOND_RTYPE, zicond_rd_val, zicond_cond, gpr_val.
  (* reduce the head condition to the read-out value *)
  assert (Hab : exec (match op with
                      | CZERO_EQZ => Defs.bind (rX_bits (Regidx rs2))
                                       (fun w => returnM (eq_vec w (zeros' 64)))
                      | CZERO_NEZ => Defs.bind (rX_bits (Regidx rs2))
                                       (fun w => returnM (neq_vec w (zeros' 64)))
                      end) s
                = Some (match op with
                        | CZERO_EQZ => eq_vec (if Z.eqb (uint rs2) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
                                          (zeros' 64)
                        | CZERO_NEZ => neq_vec (if Z.eqb (uint rs2) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
                                          (zeros' 64)
                        end, s)).
  { destruct op;
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s));
      apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hab).
  (* case on the condition boolean *)
  destruct op; cbn match; destruct (eq_vec _ _) eqn:Hc || destruct (neq_vec _ _) eqn:Hc.
  (* CZERO_EQZ, cond true: writes 0 *)
  1:{ rewrite (exec_bind_Some _ _ _ (zeros' 64) s (exec_returnM (zeros' 64) s)).
      rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd (zeros' 64) s)).
      apply exec_returnM. }
  (* CZERO_EQZ, cond false: writes rs1 value *)
  1:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      rewrite (exec_bind0_Some _ _ _ _ _
                 (exec_wX_bits_gpr rd (if Z.eqb (uint rs1) 0 then zero_reg
                    else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) s)).
      apply exec_returnM. }
  (* CZERO_NEZ, cond true *)
  1:{ rewrite (exec_bind_Some _ _ _ (zeros' 64) s (exec_returnM (zeros' 64) s)).
      rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd (zeros' 64) s)).
      apply exec_returnM. }
  (* CZERO_NEZ, cond false *)
  1:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      rewrite (exec_bind0_Some _ _ _ _ _
                 (exec_wX_bits_gpr rd (if Z.eqb (uint rs1) 0 then zero_reg
                    else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) s)).
      apply exec_returnM. }
Qed.

(* Nonzero-rd form, dispatched through [execute], as ustep_rtype2 expects. *)
