(* ===================================================================== *)
(* UserMemArms.v -- the memory-family EXECUTE facts (execute-level).      *)
(*                                                                        *)
(* The pure execute-level reductions that turn a vmem access into an       *)
(* ExecutionResult, premise-shaped over the vmem result (the iris          *)
(* invariant absorption is supplied by the UserMemAccess composers).       *)
(* These are the family execute facts the base/RVC execute totalities      *)
(* (UserExecProducer) plug in per instruction.  LOAD first:                *)
(*   - exec_vmem_read_u: vmem_read = get_transformed_data_addr (rX rs +     *)
(*     offset, transform) then vmem_read_addr; at U-mode the transform is   *)
(*     the identity (UserMemAccess SS9), so the va is exactly rX rs+offset. *)
(*   - exec_execute_LOAD_u_ok/_err (width-generic): execute_LOAD = assert   *)
(*     width<=8 ; vmem_read ; (Ok d -> wX rd (extend d) -> RETIRE | Err e   *)
(*     -> e).  An Ok from the composer is the RETIRE (left) classification, *)
(*     an Err is the delegated-trap (right) -- matching exec_step_result_ok.*)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr WpLeafCommon.
Require Import SRegime UserMemAccess.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Lemma exec_vmem_read_u (rs : mword 5) (offset : mword 64) (width : Z)
    (acc : MemoryAccessType mem_payload) (aq rl res : bool) (md : SATPMode)
    (result : result (mword (8 * width)) ExecutionResult) (s s' : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen acc User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  exec (vmem_read_addr
          (Virtaddr (add_vec (if Z.eqb (uint rs) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs))) s.(sregs))
                             offset))
          width acc aq rl res) s = Some (result, s') ->
  exec (vmem_read (Regidx rs) offset width acc aq rl res) s = Some (result, s').
Proof.
  intros Hcp Heff Hpml Htm Hvra.
  unfold vmem_read. rewrite exec_catch_early_return.
  (* get_transformed_data_addr -> OK (transform (rX rs + offset)) = OK (rX rs + offset) *)
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs) offset acc width) s
                  = Some (Ext_DataAddr_OK
                            (Virtaddr (add_vec (if Z.eqb (uint rs) 0 then zero_reg
                                                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs))) s.(sregs))
                                               offset)), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs) offset acc width) s
              = Some (Ext_DataAddr_OK
                        (Virtaddr (add_vec (if Z.eqb (uint rs) 0 then zero_reg
                                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs))) s.(sregs))
                                           offset)), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u acc md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite execR_liftR. rewrite Hvra. reflexivity.
Qed.

Lemma exec_execute_LOAD_u_ok (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
    (width : Z) (data : mword (8 * width)) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  uint rd <> 0 ->
  exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data) false false false) s
    = Some (Ok data, s') ->
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, width))) s
    = Some (RETIRE_SUCCESS,
            set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (extend_value is_unsigned data))).
Proof.
  intros Hw Hrd Hvr.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, width)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned width).
  unfold execute_LOAD. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ Hvr). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (extend_value is_unsigned data)) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value is_unsigned data)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value is_unsigned data) s').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw2).
  apply exec_returnM.
Qed.
Lemma exec_execute_LOAD_u_err (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
    (width : Z) (e : ExecutionResult) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data) false false false) s
    = Some (Err e, s') ->
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, width))) s = Some (e, s').
Proof.
  intros Hw Hvr.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, width)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned width).
  unfold execute_LOAD. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ Hvr). cbn match.
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* STORE family.  vmem_write mirrors vmem_read; execute_STORE reads rs2   *)
(* (the store data = its low width*8 bits), writes via vmem_write, and     *)
(* retires on Ok / delegates the trap on Err (no rd write).               *)
(* ===================================================================== *)
Lemma exec_vmem_write_u (rs : mword 5) (offset : mword 64) (width : Z) (data : mword (8 * width))
    (acc : MemoryAccessType mem_payload) (aq rl res : bool) (md : SATPMode)
    (result : result bool ExecutionResult) (s s' : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen acc User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  exec (vmem_write_addr
          (Virtaddr (add_vec (if Z.eqb (uint rs) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs))) s.(sregs))
                             offset))
          width data acc aq rl res) s = Some (result, s') ->
  exec (vmem_write (Regidx rs) offset width data acc aq rl res) s = Some (result, s').
Proof.
  intros Hcp Heff Hpml Htm Hvwa.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs) offset acc width) s
                  = Some (Ext_DataAddr_OK
                            (Virtaddr (add_vec (if Z.eqb (uint rs) 0 then zero_reg
                                                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs))) s.(sregs))
                                               offset)), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs) offset acc width) s
              = Some (Ext_DataAddr_OK
                        (Virtaddr (add_vec (if Z.eqb (uint rs) 0 then zero_reg
                                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs))) s.(sregs))
                                           offset)), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u acc md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite execR_liftR. rewrite Hvwa. reflexivity.
Qed.
Lemma exec_execute_STORE_u_ok (imm : mword 12) (rs2 rs1 : mword 5) (width : Z)
    (b : bool) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
          (autocast (T := mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul width 8) 1) 0))
          (Store Data) false false false) s = Some (Ok b, s') ->
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, width))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hw Hvw.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, width)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) width).
  unfold execute_STORE. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind_Some _ _ _ _ _ Hvw). cbn match.
  apply exec_returnM.
Qed.
Lemma exec_execute_STORE_u_err (imm : mword 12) (rs2 rs1 : mword 5) (width : Z)
    (e : ExecutionResult) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
          (autocast (T := mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul width 8) 1) 0))
          (Store Data) false false false) s = Some (Err e, s') ->
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, width))) s = Some (e, s').
Proof.
  intros Hw Hvw.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, width)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) width).
  unfold execute_STORE. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind_Some _ _ _ _ _ Hvw). cbn match.
  apply exec_returnM.
Qed.
