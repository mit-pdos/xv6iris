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

(* ===================================================================== *)
(* LR / SC (Zalrsc).  LR = LOAD with offset 0, LoadReserved, res=true,     *)
(* sign-extended rd (the reserved read is the res-generic vmem_read_addr   *)
(* composer).  SC = STORE with StoreConditional, con=true; the Ok case     *)
(* writes rd := negb success, cancels the reservation, and retires (its    *)
(* conditional-write composer's Ok/Err is the retire/trap classification). *)
(* ===================================================================== *)
Lemma exec_execute_LOADRES_u_ok (aq rl : bool) (rs1 rd : mword 5) (width : Z)
    (data : mword (8 * width)) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  uint rd <> 0 ->
  exec (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved Data) aq (andb aq rl) true) s
    = Some (Ok data, s') ->
  exec (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (sign_extend' 64 data))).
Proof.
  intros Hw Hrd Hvr.
  change (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd)))
    with (execute_LOADRES aq rl (Regidx rs1) width (Regidx rd)).
  unfold execute_LOADRES. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/A/zalrsc_insts.sail:43.28-43.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ Hvr). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (sign_extend' 64 data)) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 data)))).
  { rewrite (exec_wX_bits_gpr rd (sign_extend' 64 data) s').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw2). apply exec_returnM.
Qed.
Lemma exec_execute_LOADRES_u_err (aq rl : bool) (rs1 rd : mword 5) (width : Z)
    (e : ExecutionResult) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  exec (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved Data) aq (andb aq rl) true) s
    = Some (Err e, s') ->
  exec (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd))) s = Some (e, s').
Proof.
  intros Hw Hvr.
  change (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd)))
    with (execute_LOADRES aq rl (Regidx rs1) width (Regidx rd)).
  unfold execute_LOADRES. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/A/zalrsc_insts.sail:43.28-43.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ Hvr). cbn match. apply exec_returnM.
Qed.
Lemma exec_execute_STORECON_u_ok (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
    (b : bool) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  uint rd <> 0 ->
  exec (vmem_write (Regidx rs1) (zeros' 64) width
          (autocast (T := mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul width 8) 1) 0))
          (StoreConditional Data) (andb aq rl) rl true) s = Some (Ok b, s') ->
  exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (zero_extend' 64 (bool_bit_forwards (negb b))))).
Proof.
  intros Hw Hrd Hvw.
  change (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_STORECON aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_STORECON. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/A/zalrsc_insts.sail:68.28-68.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind_Some _ _ _ _ _ Hvw). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (zero_extend' 64 (bool_bit_forwards (negb b)))) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (zero_extend' 64 (bool_bit_forwards (negb b)))))).
  { rewrite (exec_wX_bits_gpr rd (zero_extend' 64 (bool_bit_forwards (negb b))) s').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  assert (Hwc : exec (Defs.bind0 (wX_bits (Regidx rd) (zero_extend' 64 (bool_bit_forwards (negb b))))
                        (cancel_reservation tt)) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (zero_extend' 64 (bool_bit_forwards (negb b)))))).
  { rewrite (exec_bind0_Some _ _ _ _ _ Hw2). apply exec_cancel_reservation. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwc). apply exec_returnM.
Qed.
Lemma exec_execute_STORECON_u_err (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
    (e : ExecutionResult) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  exec (vmem_write (Regidx rs1) (zeros' 64) width
          (autocast (T := mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul width 8) 1) 0))
          (StoreConditional Data) (andb aq rl) rl true) s = Some (Err e, s') ->
  exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s = Some (e, s').
Proof.
  intros Hw Hvw.
  change (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_STORECON aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_STORECON. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/A/zalrsc_insts.sail:68.28-68.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind_Some _ _ _ _ _ Hvw). cbn match. apply exec_returnM.
Qed.

(* ===================================================================== *)
(* AMO family.  Unlike LOAD/STORE/LR/SC, execute_AMO does not go through   *)
(* vmem_read/write: it inlines the read-modify-write (own alignment check, *)
(* translate, mem_write_ea, mem_read, per-op result, the AMOCAS guard,     *)
(* mem_write_value, wX).  But the RMW is OP-GENERIC: the written value is   *)
(* symbolic (mem_write_value is stated forall-v by the composer) and the    *)
(* w__18 CAS-check short-circuits to false for every non-AMOCAS op, so ONE   *)
(* retire lemma covers all 9 non-CAS ops.  The RAM pins atomic_support =    *)
(* AMOSwap, so only AMOSWAP actually retires; the other ops (and misalign / *)
(* walk faults) take the op-generic fault lemmas below.                     *)
(* ===================================================================== *)
Lemma exec_execute_AMO_u_ok
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (loaded : mword (8 * width)) (md : SATPMode) (s s' s'' : mstate) :
  let rs2_val : bits (width * 8) :=
    trunc (Z.mul (__id width) 8)
      (if Z.eqb (uint rs2) 0 then zero_reg
       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs)) in
  let lc : bits (width * 8) := autocast (T := mword) loaded in
  let result' : bits (width * 8) :=
    match op with
    | AMOSWAP => rs2_val | AMOADD => add_vec rs2_val lc | AMOXOR => xor_vec rs2_val lc
    | AMOAND => and_vec rs2_val lc | AMOOR => or_vec rs2_val lc
    | AMOMIN => if zopz0zI_s rs2_val lc then rs2_val else lc
    | AMOMAX => if zopz0zK_s rs2_val lc then rs2_val else lc
    | AMOMINU => if zopz0zI_u rs2_val lc then rs2_val else lc
    | AMOMAXU => if zopz0zK_u rs2_val lc then rs2_val else lc
    | AMOCAS => rs2_val end in
  (width <=? xlen_bytes) = true ->
  (width <=? Z.mul xlen_bytes 2) = true ->
  uint rd <> 0 ->
  generic_eq op AMOCAS = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) width = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (mem_write_ea addr width (andb aq rl) rl true) s' = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, Data, Data)) pbmt addr width aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  exec (mem_write_value addr width (sign_extend' (Z.mul 8 (__id width)) result') (Atomic (op, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok true, s'') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg s'' (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (sign_extend' 64 lc))).
Proof.
  intros rs2_val lc result'.
  intros Hw Hw2 Hrd Hop Hcp Heff Hpml Htm Hal Htr Hea Hrdm Hwv.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return. rewrite Hw2.
  (* assert width <= 2*xlen_bytes *)
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  (* gtda -> OK vaddr *)
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  (* alignment: is_aligned true -> not true = false -> else branch (translate) *)
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  (* rX rs2 branch: width <= xlen_bytes -> rX_bits rs2 (nested bind) *)
  rewrite Hw.
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_bits (Regidx rs2)))
                    (fun w6 : mword 64 => returnR ExecutionResult (trunc (__id width * 8) w6))) s'
               = Some (inr rs2_val, s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s')). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  (* mem_write_ea addr -> Ok tt *)
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  (* mem_read -> Ok loaded (nested bind: outer via execR_bind, inner via liftR_seq) *)
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite execR_returnR_fwd. cbn match.
  (* and_boolM (returnR (op=?AMOCAS)) B: op<>AMOCAS -> short-circuits to false *)
  rewrite Hop.
  assert (Hab : forall (B : Defs.monadR ExecutionResult exception bool),
           execR (and_boolM (returnR ExecutionResult false) B) s' = Some (inr false, s')).
  { intro B. unfold and_boolM.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd false s')). cbn match.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ (Hab _)). cbn match.
  (* else branch (w__18 = false): mem_write_value -> Ok true *)
  rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match.
  (* wX_bits rd (sign_extend' 64 loaded) >> RETIRE *)
  assert (Hwx : exec (wX_bits (Regidx rd) (sign_extend' 64 lc)) s''
                = Some (tt, set_reg s'' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 lc)))).
  { rewrite (exec_wX_bits_gpr rd (sign_extend' 64 lc) s'').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  assert (Hwxr : execR (R := ExecutionResult) (Defs.liftR (wX_bits (Regidx rd) (sign_extend' 64 lc))) s''
               = Some (inr tt, set_reg s'' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sign_extend' 64 lc)))).
  { rewrite execR_liftR. rewrite Hwx. reflexivity. }
  rewrite (execR_bind0_Some _ _ _ _ Hwxr).
  rewrite execR_returnR_fwd. reflexivity.
Qed.

(* mem_read Err -> delegated trap.  This is the pma-deny path (non-AMOSWAP ops
   the RAM does not support, atomic_support = AMOSwap), and any read fault.    *)
Lemma exec_execute_AMO_u_read_err
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
    (addr : physaddr) (pbmt : page_based_mem_type) (e : ExceptionType)
    (pc : mword 64) (md : SATPMode) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  (width <=? Z.mul xlen_bytes 2) = true ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) width = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (mem_write_ea addr width (andb aq rl) rl true) s' = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, Data, Data)) pbmt addr width aq (andb aq rl) true) s' = Some (Err e, s') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s
    = Some (Trap (User, make_sync_exception e
                    (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                             (zeros' 64)), pc), s').
Proof.
  intros Hw Hw2 Hcp Heff Hpml Htm Hcp' Hpc' Hal Htr Hea Hrdm.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return. rewrite Hw2.
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  rewrite Hw.
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_bits (Regidx rs2)))
                    (fun w6 : mword 64 => returnR ExecutionResult (trunc (__id width * 8) w6))) s'
               = Some (inr (trunc (Z.mul (__id width) 8)
                              (if Z.eqb (uint rs2) 0 then zero_reg
                               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs))), s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s')). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  (* mem_read -> Err e: early_return the memory_exception trap *)
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception _ pc e User s' Hcp' Hpc')).
  reflexivity.
Qed.

(* translateAddr Err -> delegated trap (page fault / access fault on walk). *)
Lemma exec_execute_AMO_u_translate_err
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
    (e : ExceptionType) (pc : mword 64) (md : SATPMode) (s s' : mstate) :
  (width <=? Z.mul xlen_bytes 2) = true ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) width = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, Data, Data))) s = Some (Err (e, tt), s') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s
    = Some (Trap (User, make_sync_exception e
                    (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                             (zeros' 64)), pc), s').
Proof.
  intros Hw2 Hcp Heff Hpml Htm Hcp' Hpc' Hal Htr.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return. rewrite Hw2.
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  (* translate -> Err e: early_return the memory_exception trap *)
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception _ pc e User s' Hcp' Hpc')).
  reflexivity.
Qed.

(* misaligned AMO -> E_SAMO_Access_Fault trap (plat amo policy = AccessFault). *)
Lemma exec_execute_AMO_u_misaligned
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
    (pc : mword 64) (md : SATPMode) (s : mstate) :
  (width <=? Z.mul xlen_bytes 2) = true ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  register_lookup PC s.(sregs) = pc ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) width = false ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s
    = Some (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt)
                    (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                             (zeros' 64)), pc), s).
Proof.
  intros Hw2 Hcp Heff Hpml Htm Hpc Hal.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return. rewrite Hw2.
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  (* misaligned: not false = true -> then branch (memory_exception) *)
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  cbv [plat_misaligned_access GlobalMisalignedExceptions_amo]. cbn match.
  rewrite execR_liftR.
  rewrite (exec_memory_exception _ pc (E_SAMO_Access_Fault tt) User s Hcp Hpc).
  reflexivity.
Qed.
