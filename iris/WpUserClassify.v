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
Require Import WpMmodeLeafBase WpMmodeShiftiop.
Require Import UmodeFetch UmodeEcall.
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

End WpUserClassify.
