(* WpUserClassify.v -- the decode -> classification connection.

   [decode_total_u_set] (DecodeSetU.v) says every 32-bit word decodes to a
   constructor of the explicit image [decodable_u].  [ustep_case]
   (WpUserSteps.v) is the disjunction the step dispatcher consumes.  This
   file starts wiring the two together: given the shared "fetch-hit" premise
   bundle for a word [w] at [va], route the constructor [w] decodes to into
   its [ustep_case] disjunct.

   The connection is PARTIAL by construction.  Several [decodable_u]
   constructors have no [ustep_case] home -- LOAD/STORE/AMO/LOADRES/STORECON
   are standalone spatial theorems, and BTYPE/JAL/JALR carry runtime
   [g]-dependent guards (branch-taken, target alignment) that cannot be
   decided generically.  So this file covers the guard-free constructors and
   grows over time; [covered_u] names exactly the constructors handled so
   far.  This first slice: the unconditional trap/no-op ops ILLEGAL (-> the
   trap disjunct), PAUSE and NTL (-> the no-op disjunct). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpGpr.
Require Import WpDecodeBridge.
Require Import WpAuipc.
Require Import WpMmodeLeafBase WpMmodeShiftiop WpMmodeMul.
Require Import UmodeFetch UmodeFetchC UmodeEcall.
Require Import ZbbGpr ClmulGpr ZbbRtypeGpr ZicondGpr.
Require Import UptInv WpUserBase.
Require Import WpUserSteps.
Require Import DecodeSetU.
Local Open Scope Z_scope.
Import Defs.

(* ---------------------------------------------------------------------- *)
(* Unconditional execute facts for the trivially-direct ops.  Each
   dispatches to [returnM <direct result>]; the [change ... with] keeps the
   [execute] dispatcher out of the proof term (no reservation-axiom leak). *)

Lemma exec_execute_ILLEGAL_any (z : mword 32) s :
  exec (execute (ILLEGAL z)) s = Some (Illegal_Instruction tt, s).
Proof.
  change (execute (ILLEGAL z)) with (returnM (execute_ILLEGAL z) : M ExecutionResult).
  unfold execute_ILLEGAL. apply exec_returnM.
Qed.

Lemma exec_execute_PAUSE_any (u : unit) s :
  exec (execute (PAUSE u)) s = Some (RETIRE_SUCCESS, s).
Proof.
  destruct u.
  change (execute (PAUSE tt)) with (returnM (execute_PAUSE tt) : M ExecutionResult).
  unfold execute_PAUSE. apply exec_returnM.
Qed.

Lemma exec_execute_NTL_any (nt : ntl_type) s :
  exec (execute (NTL nt)) s = Some (RETIRE_SUCCESS, s).
Proof.
  change (execute (NTL nt)) with (returnM (execute_NTL nt) : M ExecutionResult).
  unfold execute_NTL. apply exec_returnM.
Qed.

(* A memory barrier is state-preserving under exec (local copy to keep this
   U-mode file off the S-mode fence file). *)
Lemma exec_sail_barrier (b : Arch.barrier) s :
  exec (sail_barrier b) s = Some (tt, s).
Proof. reflexivity. Qed.

(* FENCE.TSO and FENCE.I: a single [sail_barrier] (state-preserving) then
   [returnM RETIRE_SUCCESS].  Unconditional -- no pred/succ dispatch. *)
Lemma exec_execute_FENCE_TSO_any (u : unit) s :
  exec (execute (FENCE_TSO u)) s = Some (RETIRE_SUCCESS, s).
Proof.
  destruct u.
  change (execute (FENCE_TSO tt)) with (execute_FENCE_TSO tt).
  unfold execute_FENCE_TSO.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_sail_barrier _ s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_FENCEI_any (p : mword 12 * regidx * regidx) s :
  exec (execute (FENCEI p)) s = Some (RETIRE_SUCCESS, s).
Proof.
  destruct p as [[imm rs] rd].
  change (execute (FENCEI (imm, rs, rd))) with (execute_FENCEI imm rs rd).
  unfold execute_FENCEI.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_sail_barrier _ s)).
  apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* The one missing ITYPE per-op fact: SLTI (signed set-less-than-imm).  It
   is the SLTIU proof with the signed comparison [zopz0zI_s]. *)
Definition gpr_slti_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  zero_extend' 64 (bool_to_bit (zopz0zI_s
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    (sign_extend' 64 imm))).

Lemma exec_execute_ITYPE_SLTI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, SLTI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_slti_val rs1 imm s))).
Proof.
  change (execute (ITYPE (imm, Regidx rs1, Regidx rd, SLTI)))
    with (execute_ITYPE imm (Regidx rs1) (Regidx rd) SLTI).
  unfold execute_ITYPE. cbn zeta match.
  rewrite (exec_bind_Some _ _ _ (gpr_slti_val rs1 imm s) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      apply exec_returnm. }
  unfold gpr_slti_val.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  destruct (Z.eqb (uint rd) 0); apply exec_returnm.
Qed.

(* ITYPE with rd = x0: the write is discarded, so it retires state-preserving
   for every op -- the [rd = 0] leg of the ITYPE classification (-> no-op
   disjunct).  Built from the per-op [_gpr] facts. *)
Lemma exec_execute_ITYPE_rd0 (op : iop) (imm : mword 12) (rs1 rd : mword 5) s :
  uint rd = 0 ->
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, op))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hrd0.
  assert (Hz : Z.eqb (uint rd) 0 = true) by (apply Z.eqb_eq; exact Hrd0).
  destruct op;
    [ rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm s)
    | rewrite (exec_execute_ITYPE_SLTI_gpr rs1 rd imm s)
    | rewrite (exec_execute_ITYPE_SLTIU_gpr rs1 rd imm s)
    | rewrite (exec_execute_ITYPE_XORI_gpr rs1 rd imm s)
    | rewrite (exec_execute_ITYPE_ORI_gpr rs1 rd imm s)
    | rewrite (exec_execute_ITYPE_ANDI_gpr rs1 rd imm s) ];
    rewrite Hz; reflexivity.
Qed.

(* The missing SHIFTIOP per-op fact: SRAI (arithmetic shift-right-imm), the
   SLLI/SRLI proof with [shift_bits_right_arith]. *)
Definition gpr_srai_val (rs1 : mword 5) (shamt : mword 6) (s : mstate) : mword 64 :=
  shift_bits_right_arith (gpr_src rs1 s) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0).

Lemma exec_execute_SHIFTIOP_SRAI_gpr (rs1 rd : mword 5) (shamt : mword 6) s :
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRAI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_srai_val rs1 shamt s))).
Proof.
  change (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRAI)))
    with (execute_SHIFTIOP shamt (Regidx rs1) (Regidx rd) SRAI).
  unfold execute_SHIFTIOP. cbn zeta match.
  rewrite (exec_bind_Some _ _ _ (gpr_srai_val rs1 shamt s) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      apply exec_returnm. }
  unfold gpr_srai_val, gpr_src.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  destruct (Z.eqb (uint rd) 0); apply exec_returnm.
Qed.

Lemma exec_execute_SHIFTIOP_rd0 (op : sop) (shamt : mword 6) (rs1 rd : mword 5) s :
  uint rd = 0 ->
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hrd0.
  assert (Hz : Z.eqb (uint rd) 0 = true) by (apply Z.eqb_eq; exact Hrd0).
  destruct op;
    [ rewrite (exec_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt s)
    | rewrite (exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt s)
    | rewrite (exec_execute_SHIFTIOP_SRAI_gpr rs1 rd shamt s) ];
    rewrite Hz; reflexivity.
Qed.

Definition shiftiop_f (op : sop) : mword 64 -> mword 6 -> mword 64 :=
  match op with
  | SLLI => fun v sh => shift_bits_left v (subrange_vec_dec sh (Z.sub log2_xlen 1) 0)
  | SRLI => fun v sh => shift_bits_right v (subrange_vec_dec sh (Z.sub log2_xlen 1) 0)
  | SRAI => fun v sh => shift_bits_right_arith v (subrange_vec_dec sh (Z.sub log2_xlen 1) 0)
  end.

Lemma exec_execute_SHIFTIOP_op_gpr (op : sop) (rs1 rd : mword 5) (shamt : mword 6) s :
  exec (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (shiftiop_f op
                       (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       shamt))).
Proof.
  destruct op;
    [ exact (exec_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt s)
    | exact (exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt s)
    | exact (exec_execute_SHIFTIOP_SRAI_gpr rs1 rd shamt s) ].
Qed.

(* The per-op value functions, packaged so the ITYPE disjunct's [f] is a
   single [itype_f op].  Each matches its [gpr_<op>_val] definitionally. *)
Definition itype_f (op : iop) : mword 64 -> mword 12 -> mword 64 :=
  match op with
  | ADDI  => fun v i => add_vec v (sign_extend' 64 i)
  | SLTI  => fun v i => zero_extend' 64 (bool_to_bit (zopz0zI_s v (sign_extend' 64 i)))
  | SLTIU => fun v i => zero_extend' 64 (bool_to_bit (zopz0zI_u v (sign_extend' 64 i)))
  | XORI  => fun v i => xor_vec v (sign_extend' 64 i)
  | ORI   => fun v i => or_vec v (sign_extend' 64 i)
  | ANDI  => fun v i => and_vec v (sign_extend' 64 i)
  end.

Lemma exec_execute_ITYPE_op_gpr (op : iop) (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (itype_f op
                       (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       imm))).
Proof.
  destruct op;
    [ exact (exec_execute_ITYPE_ADDI_gpr rs1 rd imm s)
    | exact (exec_execute_ITYPE_SLTI_gpr rs1 rd imm s)
    | exact (exec_execute_ITYPE_SLTIU_gpr rs1 rd imm s)
    | exact (exec_execute_ITYPE_XORI_gpr rs1 rd imm s)
    | exact (exec_execute_ITYPE_ORI_gpr rs1 rd imm s)
    | exact (exec_execute_ITYPE_ANDI_gpr rs1 rd imm s) ].
Qed.

(* UTYPE (LUI/AUIPC).  Disjunct 7 splits the written value into a
   state-dependent [V imm s] (AUIPC reads PC) and a pc-pinned witness [v];
   the extra premise ties them at PC = va. *)
Definition utype_V (op : uop) : mword 20 -> mstate -> mword 64 :=
  match op with
  | LUI => fun imm s => luival imm
  | AUIPC => fun imm s => add_vec (register_lookup PC s.(sregs)) (auipc_off imm)
  end.

Definition utype_v (op : uop) (imm : mword 20) (va : mword 64) : mword 64 :=
  match op with
  | LUI => luival imm
  | AUIPC => add_vec va (auipc_off imm)
  end.

Lemma exec_execute_UTYPE_rd0 (op : uop) (imm : mword 20) (rd : mword 5) s :
  uint rd = 0 ->
  exec (execute (UTYPE (imm, Regidx rd, op))) s = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hrd0.
  assert (Hz : Z.eqb (uint rd) 0 = true) by (apply Z.eqb_eq; exact Hrd0).
  destruct op;
    [ rewrite (exec_execute_UTYPE_LUI_gpr rd imm s)
    | rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm s) ];
    rewrite Hz; reflexivity.
Qed.

Lemma exec_execute_UTYPE_op_gpr (op : uop) (rd : mword 5) (imm : mword 20) s :
  exec (execute (UTYPE (imm, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (utype_V op imm s))).
Proof.
  destruct op;
    [ exact (exec_execute_UTYPE_LUI_gpr rd imm s)
    | exact (exec_execute_UTYPE_AUIPC_gpr rd imm s) ].
Qed.

(* RTYPE (register-register, two sources).  One op-generic if-form fact,
   proved by a uniform reduction over all ten ops (including the four with no
   prior [_gpr] fact: SLL/SLT/SRL/SRA), keyed by [rtype_f].  [gpr_src rs s]
   is the x0-aware read (reused from WpMmodeShiftiop). *)
Definition rtype_f (op : rop) : mword 64 -> mword 64 -> mword 64 :=
  match op with
  | ADD  => fun a b => add_vec a b
  | SUB  => fun a b => sub_vec a b
  | SLL  => fun a b => shift_bits_left a (subrange_vec_dec b (Z.sub log2_xlen 1) 0)
  | SLT  => fun a b => zero_extend' 64 (bool_to_bit (zopz0zI_s a b))
  | SLTU => fun a b => zero_extend' 64 (bool_to_bit (zopz0zI_u a b))
  | XOR  => fun a b => xor_vec a b
  | SRL  => fun a b => shift_bits_right a (subrange_vec_dec b (Z.sub log2_xlen 1) 0)
  | SRA  => fun a b => shift_bits_right_arith a (subrange_vec_dec b (Z.sub log2_xlen 1) 0)
  | OR   => fun a b => or_vec a b
  | AND  => fun a b => and_vec a b
  end.

Lemma exec_execute_RTYPE_op_gpr (op : rop) (rs2 rs1 rd : mword 5) s :
  exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (rtype_f op (gpr_src rs1 s) (gpr_src rs2 s)))).
Proof.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) op).
  unfold execute_RTYPE.
  destruct op; cbn match;
    match goal with
    | |- context [regval_into_reg ?V] =>
      rewrite (exec_bind_Some _ _ _ V s);
        [ rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s));
          destruct (Z.eqb (uint rd) 0); apply exec_returnm
        | rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s));
          rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s));
          apply exec_returnm ]
    end.
Qed.

(* ---------------------------------------------------------------------- *)
(* If-form (compute-shape, rd=x0-guarded) execute facts for the two-source
   families whose armed [_gpr] facts are stated only in the nonzero-rd form
   (MULW / DIV{,W} / REM{,W} and the two-source Zbb ops).  Each is the same
   pure rX/rX/wX chain as the nonzero-rd proof; keeping the [if uint rd = 0]
   guard (rather than [replace]-ing it away) makes the fact usable for BOTH
   legs of [classify_two] (rd=x0 -> no-op, rd<>0 -> the two-source arm). *)

Lemma exec_execute_MULW_if (rs2 rs1 rd : mword 5) s :
  exec (execute (MULW (Regidx rs2, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_mulw_val (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  change (execute (MULW (Regidx rs2, Regidx rs1, Regidx rd)))
    with (execute_MULW (Regidx rs2) (Regidx rs1) (Regidx rd)).
  unfold execute_MULW, gpr_mulw_val. cbv beta zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_DIV_if (u : bool) (rs2 rs1 rd : mword 5) s :
  exec (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, u))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_div_val u (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  change (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, u)))
    with (execute_DIV (Regidx rs2) (Regidx rs1) (Regidx rd) u).
  unfold execute_DIV, gpr_div_val. cbv beta zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_DIVW_if (u : bool) (rs2 rs1 rd : mword 5) s :
  exec (execute (DIVW (Regidx rs2, Regidx rs1, Regidx rd, u))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_divw_val u (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  change (execute (DIVW (Regidx rs2, Regidx rs1, Regidx rd, u)))
    with (execute_DIVW (Regidx rs2) (Regidx rs1) (Regidx rd) u).
  unfold execute_DIVW, gpr_divw_val. cbv beta zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_REM_if (u : bool) (rs2 rs1 rd : mword 5) s :
  exec (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, u))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_rem_val u (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  change (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, u)))
    with (execute_REM (Regidx rs2) (Regidx rs1) (Regidx rd) u).
  unfold execute_REM, gpr_rem_val. cbv beta zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_REMW_if (u : bool) (rs2 rs1 rd : mword 5) s :
  exec (execute (REMW (Regidx rs2, Regidx rs1, Regidx rd, u))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_remw_val u (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  change (execute (REMW (Regidx rs2, Regidx rs1, Regidx rd, u)))
    with (execute_REMW (Regidx rs2) (Regidx rs1) (Regidx rd) u).
  unfold execute_REMW, gpr_remw_val. cbv beta zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_ZBB_RTYPE_if (op : brop_zbb) (rs2 rs1 rd : mword 5) s :
  exec (execute (ZBB_RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (zbb_rtype_val op (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  change (execute (ZBB_RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op)))
    with (execute_ZBB_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) op).
  unfold execute_ZBB_RTYPE, zbb_rtype_val. cbn match. cbv zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

Lemma exec_execute_ZBB_RTYPEW_if (op : bropw_zbb) (rs2 rs1 rd : mword 5) s :
  exec (execute (ZBB_RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (zbb_rtypew_val op (gpr_val rs1 s) (gpr_val rs2 s)))).
Proof.
  change (execute (ZBB_RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op)))
    with (execute_ZBB_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) op).
  unfold execute_ZBB_RTYPEW, zbb_rtypew_val. cbn match. cbv zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

(* MUL (all four M-extension products): execute_MUL is uniform over the
   [mul_op] record (rX/rX/wX with a pure [mult_to_bits_half]), so one
   op-generic if-form fact covers MUL/MULH/MULHSU/MULHU. *)
Lemma exec_execute_MUL_if (mop : mul_op) (rs2 rs1 rd : mword 5) s :
  exec (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mop))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (mult_to_bits_half xlen (mop.(mul_op_signed_rs1))
                       (mop.(mul_op_signed_rs2)) (gpr_val rs1 s) (gpr_val rs2 s)
                       (mop.(mul_op_result_part))))).
Proof.
  change (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mop)))
    with (execute_MUL (Regidx rs2) (Regidx rs1) (Regidx rd) mop).
  unfold execute_MUL.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnM.
Qed.

Section WpUserClassify.
  Context `{CID : CpuId}.
  Context (U : WpUserBase.uctx).

  Local Notation code := (WpUserBase.code U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation ustep_case := (WpUserSteps.ustep_case U).

  (* The fetch-hit premise bundle shared by [ustep_case]'s decode disjuncts
     (5-15): the word [w] is fetched from a mapped, checked, non-PBMT,
     4-aligned canonical code page and is not compressed. *)
  Definition ufetch_hit (va : mword 64) (vpn : mword 27) (i : uwalk_info)
      (w : mword 32) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
    uw_check_ok (InstructionFetch tt) i /\
    update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
    is_aligned_vaddr (Virtaddr va) 4 = true /\
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
    isRVC (subrange_vec_dec w 15 0) = false.

  (* A word whose execute is unconditionally state-preserving RETIRE lands in
     the no-op disjunct (11). *)
  Lemma classify_nop (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (ii : instruction) :
    (forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) ->
    is_lpad_instruction ii = false ->
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hexec Hlpad
      (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC) Hdec.
    unfold ustep_case, WpUserSteps.ustep_case.
    right; right; right; right; right; right; right; right; right; right; left.
    exists vpn, i, w, ii. repeat split; assumption.
  Qed.

  (* A word whose execute is unconditionally Illegal lands in the trap
     disjunct (12). *)
  Lemma classify_illegal (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (ii : instruction) :
    (forall s, exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    is_lpad_instruction ii = false ->
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hexec Hlpad
      (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC) Hdec.
    unfold ustep_case, WpUserSteps.ustep_case.
    right; right; right; right; right; right; right; right; right; right; right; left.
    exists vpn, i, w, ii. repeat split; assumption.
  Qed.

  (* A word decoding to any ITYPE op is classified: rd = x0 -> the no-op
     disjunct (11); rd <> 0 -> the ITYPE compute disjunct (5), with
     [f := itype_f op].  Unlike the nullary trap/no-op constructors this
     carries the instruction fields, so it is its own classify lemma. *)
  Lemma classify_itype (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5) (op : iop) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    destruct (Z.eq_dec (uint rd) 0) as [Hrd0 | Hrd].
    - (* rd = x0: no-op disjunct 11 *)
      apply (classify_nop va ms_v g tlbvec vpn i w (ITYPE (imm, Regidx rs1, Regidx rd, op))).
      + intro s. exact (exec_execute_ITYPE_rd0 op imm rs1 rd s Hrd0).
      + reflexivity.
      + exact Hf.
      + exact Hdec.
    - (* rd <> 0: ITYPE compute disjunct 5 *)
      destruct Hf as (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC).
      unfold ustep_case, WpUserSteps.ustep_case.
      right; right; right; right; left.
      exists vpn, i, w, op, (itype_f op), imm, rs1, rd.
      repeat split; try assumption.
      exact (fun rs1' rd' imm' s => exec_execute_ITYPE_op_gpr op rs1' rd' imm' s).
  Qed.

  (* SHIFTIOP (SLLI/SRLI/SRAI): rd = x0 -> no-op (11); rd <> 0 -> shift
     disjunct (8), [f := shiftiop_f op]. *)
  Lemma classify_shiftiop (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (shamt : mword 6) (rs1 rd : mword 5) (op : sop) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    destruct (Z.eq_dec (uint rd) 0) as [Hrd0 | Hrd].
    - apply (classify_nop va ms_v g tlbvec vpn i w (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op))).
      + intro s. exact (exec_execute_SHIFTIOP_rd0 op shamt rs1 rd s Hrd0).
      + reflexivity.
      + exact Hf.
      + exact Hdec.
    - destruct Hf as (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC).
      unfold ustep_case, WpUserSteps.ustep_case.
      right; right; right; right; right; right; right; left.
      exists vpn, i, w, op, (shiftiop_f op), shamt, rs1, rd.
      repeat split; try assumption.
      exact (fun rs1' rd' shamt' s => exec_execute_SHIFTIOP_op_gpr op rs1' rd' shamt' s).
  Qed.

  (* UTYPE (LUI/AUIPC): rd = x0 -> no-op (11); rd <> 0 -> the UTYPE disjunct
     (7), with [V := utype_V op] and the pc-pinned witness [utype_v op imm va]. *)
  Lemma classify_utype (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (imm : mword 20) (rd : mword 5) (op : uop) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    destruct (Z.eq_dec (uint rd) 0) as [Hrd0 | Hrd].
    - apply (classify_nop va ms_v g tlbvec vpn i w (UTYPE (imm, Regidx rd, op))).
      + intro s. exact (exec_execute_UTYPE_rd0 op imm rd s Hrd0).
      + reflexivity.
      + exact Hf.
      + exact Hdec.
    - destruct Hf as (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC).
      unfold ustep_case, WpUserSteps.ustep_case.
      right; right; right; right; right; right; left.
      exists vpn, i, w, op, (utype_V op), (utype_v op imm va), imm, rd.
      repeat split; try assumption.
      + intros s' Hpc. destruct op; cbn [utype_V utype_v];
          [ reflexivity | rewrite Hpc; reflexivity ].
      + intros rd' imm' s. exact (exec_execute_UTYPE_op_gpr op rd' imm' s).
  Qed.

  (* RTYPE (ADD/SUB/SLL/SLT/SLTU/XOR/SRL/SRA/OR/AND): rd = x0 -> no-op (11);
     rd <> 0 -> the register-register disjunct (6), [f := rtype_f op].  Both
     legs come from the single op-generic if-form fact. *)
  Lemma classify_rtype (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (rs2 rs1 rd : mword 5) (op : rop) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    destruct (Z.eq_dec (uint rd) 0) as [Hrd0 | Hrd].
    - apply (classify_nop va ms_v g tlbvec vpn i w (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op))).
      + intro s. rewrite (exec_execute_RTYPE_op_gpr op rs2 rs1 rd s).
        replace (Z.eqb (uint rd) 0) with true by (symmetry; apply Z.eqb_eq; exact Hrd0).
        reflexivity.
      + reflexivity.
      + exact Hf.
      + exact Hdec.
    - destruct Hf as (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC).
      unfold ustep_case, WpUserSteps.ustep_case.
      right; right; right; right; right; left.
      exists vpn, i, w, op, (rtype_f op), rs2, rs1, rd.
      repeat split; try assumption.
      intros rs2' rs1' rd' s Hrd'.
      rewrite (exec_execute_RTYPE_op_gpr op rs2' rs1' rd' s).
      replace (Z.eqb (uint rd') 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd').
      reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Generic single-source compute classifier (-> disjunct 15).  Any
     constructor built by [mk : rs1 -> rd -> instruction] whose execute is
     the compute1 if-shape (write [F (rs1 value)] to rd, guarded by rd=x0)
     and which is not a landing pad: rd = x0 -> the no-op disjunct (11);
     rd <> 0 -> the single-source compute disjunct (15).  ADDIW, the W-shifts
     (SHIFTIWOP), and the single-source Zbb ops (REV8/RORI/RORIW) all ride
     this helper. *)
  Lemma classify_single (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (mk : mword 5 -> mword 5 -> instruction) (F : mword 64 -> mword 64)
      (rs1 rd : mword 5) :
    (forall (rs1' rd' : mword 5) s,
       exec (execute (mk rs1' rd')) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg (F (gpr_val rs1' s))))) ->
    is_lpad_instruction (mk rs1 rd) = false ->
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (mk rs1 rd, s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hexec Hlpad Hf Hdec.
    destruct (Z.eq_dec (uint rd) 0) as [Hrd0 | Hrd].
    - apply (classify_nop va ms_v g tlbvec vpn i w (mk rs1 rd)).
      + intro s. rewrite (Hexec rs1 rd s).
        replace (Z.eqb (uint rd) 0) with true by (symmetry; apply Z.eqb_eq; exact Hrd0).
        reflexivity.
      + exact Hlpad.
      + exact Hf.
      + exact Hdec.
    - destruct Hf as (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC).
      unfold ustep_case, WpUserSteps.ustep_case.
      do 14 right; left.
      exists vpn, i, w, mk, F, rs1, rd.
      repeat split; try assumption; try exact Hexec.
  Qed.

  (* Generic two-source compute classifier (-> disjunct 33).  Any constructor
     built by [mk2 : rs2 -> rs1 -> rd -> instruction] whose execute is the
     RTYPE if-shape (write [f (rs1 value) (rs2 value)] to rd, guarded by
     rd=x0) and which is not a landing pad: rd = x0 -> no-op (11); rd <> 0 ->
     the generic two-source compute disjunct (33).  RTYPEW, MUL(W)/DIV(W)/
     REM(W), CLMUL{,H,R}, the two-source Zbb ops and ZICOND ride this. *)
  Lemma classify_two (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (mk2 : mword 5 -> mword 5 -> mword 5 -> instruction)
      (f : mword 64 -> mword 64 -> mword 64)
      (rs2 rs1 rd : mword 5) :
    (forall (rs2' rs1' rd' : mword 5) s,
       exec (execute (mk2 rs2' rs1' rd')) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd') 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                      (regval_into_reg (f (gpr_val rs1' s) (gpr_val rs2' s))))) ->
    is_lpad_instruction (mk2 rs2 rs1 rd) = false ->
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (mk2 rs2 rs1 rd, s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hexec Hlpad Hf Hdec.
    destruct (Z.eq_dec (uint rd) 0) as [Hrd0 | Hrd].
    - apply (classify_nop va ms_v g tlbvec vpn i w (mk2 rs2 rs1 rd)).
      + intro s. rewrite (Hexec rs2 rs1 rd s).
        replace (Z.eqb (uint rd) 0) with true by (symmetry; apply Z.eqb_eq; exact Hrd0).
        reflexivity.
      + exact Hlpad.
      + exact Hf.
      + exact Hdec.
    - destruct Hf as (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC).
      unfold ustep_case, WpUserSteps.ustep_case.
      do 32 right; left.
      exists vpn, i, w, mk2, f, rs2, rs1, rd.
      repeat split; try assumption.
      intros rs2' rs1' rd' s Hrd'.
      rewrite (Hexec rs2' rs1' rd' s).
      replace (Z.eqb (uint rd') 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd').
      reflexivity.
  Qed.

  (* --- single-source families (disjunct 15) --- *)

  (* ADDIW rd, rs1, imm : rd := sext32(rs1 + sext(imm)). *)
  Lemma classify_addiw (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ADDIW (imm, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_single va ms_v g tlbvec vpn i w
             (fun a b => ADDIW (imm, Regidx a, Regidx b))
             (fun v => sign_extend' 64 (subrange_vec_dec
                         (add_vec v (sign_extend' 64 imm)) 31 0))
             rs1 rd).
    - intros rs1' rd' s. exact (exec_execute_ADDIW_gpr rs1' rd' imm s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* SHIFTIWOP rd, rs1, shamt (SLLIW/SRLIW/SRAIW). *)
  Lemma classify_shiftiwop (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (shamt : mword 5) (rs1 rd : mword 5) (op : sopw) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_single va ms_v g tlbvec vpn i w
             (fun a b => SHIFTIWOP (shamt, Regidx a, Regidx b, op))
             (fun v => gpr_shiftiwop_val op shamt v) rs1 rd).
    - intros rs1' rd' s. exact (exec_execute_SHIFTIWOP_gpr op shamt rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* REV8 rd, rs1. *)
  Lemma classify_rev8 (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (REV8 (Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_single va ms_v g tlbvec vpn i w
             (fun a b => REV8 (Regidx a, Regidx b)) (fun v => rev8 v) rs1 rd).
    - intros rs1' rd' s. exact (exec_execute_REV8_gpr rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* RORI rd, rs1, shamt. *)
  Lemma classify_rori (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (shamt : mword 6) (rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (RORI (shamt, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_single va ms_v g tlbvec vpn i w
             (fun a b => RORI (shamt, Regidx a, Regidx b))
             (fun v => rotate_bits_right v (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
             rs1 rd).
    - intros rs1' rd' s. exact (exec_execute_RORI_gpr shamt rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* RORIW rd, rs1, shamt. *)
  Lemma classify_roriw (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (shamt : mword 5) (rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (RORIW (shamt, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_single va ms_v g tlbvec vpn i w
             (fun a b => RORIW (shamt, Regidx a, Regidx b))
             (fun v => sign_extend' 64 (rotate_bits_right (subrange_vec_dec v 31 0) shamt))
             rs1 rd).
    - intros rs1' rd' s. exact (exec_execute_RORIW_gpr shamt rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* --- two-source families with an if-form execute fact (disjunct 33) --- *)

  (* RTYPEW rd, rs1, rs2 (ADDW/SUBW/SLLW/SRLW/SRAW). *)
  Lemma classify_rtypew (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (rs2 rs1 rd : mword 5) (op : ropw) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => RTYPEW (Regidx a, Regidx b, Regidx c, op))
             (gpr_rtypew_val op) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_RTYPEW_gpr op rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* CLMUL rd, rs1, rs2. *)
  Lemma classify_clmul (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (CLMUL (Regidx rs2, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => CLMUL (Regidx a, Regidx b, Regidx c))
             (fun v1 v2 => subrange_vec_dec (carryless_mul v1 v2) (Z.sub xlen 1) 0)
             rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_CLMUL_gpr rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* CLMULH rd, rs1, rs2. *)
  Lemma classify_clmulh (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (CLMULH (Regidx rs2, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => CLMULH (Regidx a, Regidx b, Regidx c))
             (fun v1 v2 => subrange_vec_dec (carryless_mul v1 v2) (Z.sub (Z.mul 2 xlen) 1) xlen)
             rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_CLMULH_gpr rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* CLMULR rd, rs1, rs2. *)
  Lemma classify_clmulr (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (CLMULR (Regidx rs2, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => CLMULR (Regidx a, Regidx b, Regidx c))
             (fun v1 v2 => carryless_mulr v1 v2) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_CLMULR_gpr rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* --- two-source families via the local if-form facts (disjunct 33) --- *)

  (* MULW rd, rs1, rs2. *)
  Lemma classify_mulw (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (MULW (Regidx rs2, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => MULW (Regidx a, Regidx b, Regidx c))
             gpr_mulw_val rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_MULW_if rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* DIV rd, rs1, rs2 (u selects signed/unsigned). *)
  Lemma classify_div (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) (u : bool) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (DIV (Regidx rs2, Regidx rs1, Regidx rd, u), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => DIV (Regidx a, Regidx b, Regidx c, u))
             (gpr_div_val u) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_DIV_if u rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* DIVW rd, rs1, rs2. *)
  Lemma classify_divw (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) (u : bool) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (DIVW (Regidx rs2, Regidx rs1, Regidx rd, u), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => DIVW (Regidx a, Regidx b, Regidx c, u))
             (gpr_divw_val u) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_DIVW_if u rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* REM rd, rs1, rs2. *)
  Lemma classify_rem (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) (u : bool) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (REM (Regidx rs2, Regidx rs1, Regidx rd, u), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => REM (Regidx a, Regidx b, Regidx c, u))
             (gpr_rem_val u) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_REM_if u rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* REMW rd, rs1, rs2. *)
  Lemma classify_remw (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) (u : bool) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (REMW (Regidx rs2, Regidx rs1, Regidx rd, u), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => REMW (Regidx a, Regidx b, Regidx c, u))
             (gpr_remw_val u) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_REMW_if u rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* ZBB_RTYPE rd, rs1, rs2 (ANDN/ORN/XNOR/MAX{,U}/MIN{,U}/ROL/ROR). *)
  Lemma classify_zbb_rtype (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) (op : brop_zbb) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ZBB_RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => ZBB_RTYPE (Regidx a, Regidx b, Regidx c, op))
             (zbb_rtype_val op) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_ZBB_RTYPE_if op rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* ZBB_RTYPEW rd, rs1, rs2 (ROLW/RORW). *)
  Lemma classify_zbb_rtypew (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) (op : bropw_zbb) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ZBB_RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => ZBB_RTYPEW (Regidx a, Regidx b, Regidx c, op))
             (zbb_rtypew_val op) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_ZBB_RTYPEW_if op rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* ZICOND_RTYPE rd, rs1, rs2 (CZERO.EQZ/CZERO.NEZ). *)
  Lemma classify_zicond (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (rs2 rs1 rd : mword 5) (op : zicondop) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ZICOND_RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => ZICOND_RTYPE (Regidx a, Regidx b, Regidx c, op))
             (fun v1 v2 =>
                if (match op with
                    | CZERO_EQZ => eq_vec v2 (zeros' 64)
                    | CZERO_NEZ => neq_vec v2 (zeros' 64)
                    end)
                then zeros' 64 else v1) rs2 rs1 rd).
    - intros rs2' rs1' rd' s.
      exact (exec_execute_ZICOND_RTYPE_gpr rs2' rs1' rd' op s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* MUL rd, rs1, rs2 (any of MUL/MULH/MULHSU/MULHU). *)
  Lemma classify_mul (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (rs2 rs1 rd : mword 5) (mop : mul_op) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (MUL (Regidx rs2, Regidx rs1, Regidx rd, mop), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => MUL (Regidx a, Regidx b, Regidx c, mop))
             (fun v1 v2 => mult_to_bits_half xlen (mop.(mul_op_signed_rs1))
                             (mop.(mul_op_signed_rs2)) v1 v2 (mop.(mul_op_result_part)))
             rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_MUL_if mop rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* --- the ZIMOP may-be-operations (write 0 to rd, retire) --- *)

  (* ZIMOP_MOP_R rd, rs1: rd := 0 (single-source, const-zero value). *)
  Lemma classify_zimop_r (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (mop : mword 5) (rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ZIMOP_MOP_R (mop, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_single va ms_v g tlbvec vpn i w
             (fun a b => ZIMOP_MOP_R (mop, Regidx a, Regidx b))
             (fun _ => zeros' 64) rs1 rd).
    - intros rs1' rd' s. exact (exec_execute_ZIMOP_MOP_R_gpr mop rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* ZIMOP_MOP_RR rd, rs1, rs2: rd := 0 (two-source, const-zero value). *)
  Lemma classify_zimop_rr (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (mop : mword 3) (rs2 rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ZIMOP_MOP_RR (mop, Regidx rs2, Regidx rs1, Regidx rd), s0)) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec.
    apply (classify_two va ms_v g tlbvec vpn i w
             (fun a b c => ZIMOP_MOP_RR (mop, Regidx a, Regidx b, Regidx c))
             (fun _ _ => zeros' 64) rs2 rs1 rd).
    - intros rs2' rs1' rd' s. exact (exec_execute_ZIMOP_MOP_RR_gpr mop rs2' rs1' rd' s).
    - reflexivity.
    - exact Hf.
    - exact Hdec.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Control-flow classifiers.  Unlike the compute families these carry
     RUNTIME guards (rd<>x0, target alignment, branch condition) that are
     decided from the frame's register map [g] / pc [va] -- NOT from the
     decoded word alone -- so they are CONDITIONAL classifiers (extra
     hypotheses) and do NOT join the unconditional [classify_word]
     dispatcher.  They route to the pre-existing jump/branch disjuncts
     (9/10/13/14); the caller discharges the guards for its program. *)

  (* JAL rd, imm: aligned pc-relative jump, rd<>x0 -> disjunct 9. *)
  Lemma classify_jal (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (imm : mword 21) (rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (JAL (imm, Regidx rd), s0)) ->
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC)
      Hdec Hrd H0 H1.
    unfold ustep_case, WpUserSteps.ustep_case.
    do 8 right; left.
    exists vpn, i, w, imm, rd.
    repeat split; assumption.
  Qed.

  (* JALR rd, rs1, imm: aligned register-indirect jump, rd<>x0 -> disjunct 10. *)
  Lemma classify_jalr (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (JALR (imm, Regidx rs1, Regidx rd), s0)) ->
    uint rd <> 0 ->
    eq_vec (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 1) = false ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros (Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC)
      Hdec Hrd H0 H1.
    unfold ustep_case, WpUserSteps.ustep_case.
    do 9 right; left.
    exists vpn, i, w, imm, rs1, rd.
    repeat split; assumption.
  Qed.

  (* The constructors this file classifies so far. *)
  Definition covered_u (ii : instruction) : bool :=
    match ii with
    | ILLEGAL _ => true
    | PAUSE _ => true
    | NTL _ => true
    | FENCE_TSO _ => true
    | FENCEI _ => true
    | _ => false
    end.

  (* A [covered_u] constructor executes unconditionally: it is not a landing
     pad, and either it always retires state-preserving (PAUSE/NTL -> the
     no-op disjunct) or it always traps Illegal (ILLEGAL -> the trap
     disjunct).  The goal mentions [ii], so the field of the surviving
     constructor is tied by unification (no dangling evar). *)
  Lemma covered_u_exec (ii : instruction) :
    covered_u ii = true ->
    is_lpad_instruction ii = false /\
    ((forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) \/
     (forall s, exec (execute ii) s = Some (Illegal_Instruction tt, s))).
  Proof.
    intros Hcov. destruct ii; try discriminate Hcov; clear Hcov;
      (split; [ reflexivity | ]);
      first [ left; apply exec_execute_PAUSE_any
            | left; apply exec_execute_NTL_any
            | left; apply exec_execute_FENCE_TSO_any
            | left; apply exec_execute_FENCEI_any
            | right; apply exec_execute_ILLEGAL_any ].
  Qed.

  (* The connection: given the fetch-hit bundle and the decode fact for the
     word, any [covered_u] constructor is placed into [ustep_case].  The
     caller obtains the decode fact and [decodable_u]-membership from
     [decode_total_u_set w] and checks [covered_u] by computation. *)
  Lemma classify_covered (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (ii : instruction) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    covered_u ii = true ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec Hcov.
    destruct (covered_u_exec ii Hcov) as (Hlpad & [Hnop | Hill]).
    - exact (classify_nop va ms_v g tlbvec vpn i w ii Hnop Hlpad Hf Hdec).
    - exact (classify_illegal va ms_v g tlbvec vpn i w ii Hill Hlpad Hf Hdec).
  Qed.

  (* The full pipeline: [decode_total_u_set] supplies the (unique, agreeing)
     decoded instruction and its [decodable_u] membership; the caller only
     has to confirm -- by computation on that constructor -- that it is
     [covered_u].  Uncovered words (LOAD/STORE/AMO/branches/jumps) fall
     outside this lemma and are handled by their own step theorems. *)
  Lemma classify_of_decode (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) :
    ufetch_hit va vpn i w tlbvec ->
    (forall ii, decodable_u ii = true ->
       (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
       covered_u ii = true) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hcov.
    destruct (decode_total_u_set w) as (ii & Hdu & Hdec).
    exact (classify_covered va ms_v g tlbvec vpn i w ii Hf Hdec (Hcov ii Hdu Hdec)).
  Qed.

  (* Everything classified so far, as one predicate + one dispatcher: the four
     base-integer compute families plus the [covered_u] trap/no-op set. *)
  Definition classifiable_u (ii : instruction) : bool :=
    match ii with
    | ITYPE _ => true | RTYPE _ => true | UTYPE _ => true | SHIFTIOP _ => true
    | ADDIW _ => true | SHIFTIWOP _ => true
    | REV8 _ => true | RORI _ => true | RORIW _ => true
    | RTYPEW _ => true | MUL _ => true | MULW _ => true
    | DIV _ => true | DIVW _ => true | REM _ => true | REMW _ => true
    | CLMUL _ => true | CLMULH _ => true | CLMULR _ => true
    | ZBB_RTYPE _ => true | ZBB_RTYPEW _ => true | ZICOND_RTYPE _ => true
    | ZIMOP_MOP_R _ => true | ZIMOP_MOP_RR _ => true
    | _ => covered_u ii
    end.

  Lemma classify_word (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) (ii : instruction) :
    ufetch_hit va vpn i w tlbvec ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
    classifiable_u ii = true ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hdec Hcl.
    destruct ii; try discriminate Hcl;
      try (exact (classify_covered va ms_v g tlbvec vpn i w _ Hf Hdec eq_refl)).
    all: lazymatch goal with
    | Hdec : forall _, _ -> exec _ _ = Some (ITYPE ?p, _) |- _ =>
        destruct p as [[[imm r1] r2] op]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_itype va ms_v g tlbvec vpn i w imm rs1 rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (RTYPE ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] op];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_rtype va ms_v g tlbvec vpn i w rs2 rs1 rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (UTYPE ?p, _) |- _ =>
        destruct p as [[imm r1] op]; destruct r1 as [rd];
        exact (classify_utype va ms_v g tlbvec vpn i w imm rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (SHIFTIOP ?p, _) |- _ =>
        destruct p as [[[shamt r1] r2] op]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_shiftiop va ms_v g tlbvec vpn i w shamt rs1 rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (ADDIW ?p, _) |- _ =>
        destruct p as [[imm r1] r2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_addiw va ms_v g tlbvec vpn i w imm rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (SHIFTIWOP ?p, _) |- _ =>
        destruct p as [[[shamt r1] r2] op]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_shiftiwop va ms_v g tlbvec vpn i w shamt rs1 rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (REV8 ?p, _) |- _ =>
        destruct p as [r1 r2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_rev8 va ms_v g tlbvec vpn i w rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (RORI ?p, _) |- _ =>
        destruct p as [[shamt r1] r2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_rori va ms_v g tlbvec vpn i w shamt rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (RORIW ?p, _) |- _ =>
        destruct p as [[shamt r1] r2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_roriw va ms_v g tlbvec vpn i w shamt rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (RTYPEW ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] op];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_rtypew va ms_v g tlbvec vpn i w rs2 rs1 rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (MUL ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] mop];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_mul va ms_v g tlbvec vpn i w rs2 rs1 rd mop Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (MULW ?p, _) |- _ =>
        destruct p as [[rs2r r1] r2];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_mulw va ms_v g tlbvec vpn i w rs2 rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (DIV ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] u];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_div va ms_v g tlbvec vpn i w rs2 rs1 rd u Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (DIVW ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] u];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_divw va ms_v g tlbvec vpn i w rs2 rs1 rd u Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (REM ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] u];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_rem va ms_v g tlbvec vpn i w rs2 rs1 rd u Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (REMW ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] u];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_remw va ms_v g tlbvec vpn i w rs2 rs1 rd u Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (CLMUL ?p, _) |- _ =>
        destruct p as [[rs2r r1] r2];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_clmul va ms_v g tlbvec vpn i w rs2 rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (CLMULH ?p, _) |- _ =>
        destruct p as [[rs2r r1] r2];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_clmulh va ms_v g tlbvec vpn i w rs2 rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (CLMULR ?p, _) |- _ =>
        destruct p as [[rs2r r1] r2];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_clmulr va ms_v g tlbvec vpn i w rs2 rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (ZBB_RTYPE ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] op];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_zbb_rtype va ms_v g tlbvec vpn i w rs2 rs1 rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (ZBB_RTYPEW ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] op];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_zbb_rtypew va ms_v g tlbvec vpn i w rs2 rs1 rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (ZICOND_RTYPE ?p, _) |- _ =>
        destruct p as [[[rs2r r1] r2] op];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_zicond va ms_v g tlbvec vpn i w rs2 rs1 rd op Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (ZIMOP_MOP_R ?p, _) |- _ =>
        destruct p as [[mop r1] r2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_zimop_r va ms_v g tlbvec vpn i w mop rs1 rd Hf Hdec)
    | Hdec : forall _, _ -> exec _ _ = Some (ZIMOP_MOP_RR ?p, _) |- _ =>
        destruct p as [[[mop rs2r] r1] r2];
        destruct rs2r as [rs2]; destruct r1 as [rs1]; destruct r2 as [rd];
        exact (classify_zimop_rr va ms_v g tlbvec vpn i w mop rs2 rs1 rd Hf Hdec)
    end.
  Qed.

  (* The full pipeline over the wider [classifiable_u] set. *)
  Lemma classify_word_of_decode (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (vpn : mword 27) (i : uwalk_info) (w : mword 32) :
    ufetch_hit va vpn i w tlbvec ->
    (forall ii, decodable_u ii = true ->
       (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
       classifiable_u ii = true) ->
    ustep_case va ms_v g tlbvec.
  Proof.
    intros Hf Hcl.
    destruct (decode_total_u_set w) as (ii & Hdu & Hdec).
    exact (classify_word va ms_v g tlbvec vpn i w ii Hf Hdec (Hcl ii Hdu Hdec)).
  Qed.

End WpUserClassify.
