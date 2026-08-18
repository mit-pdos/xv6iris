(* ====================================================================== *)
(* UserMemArmsBase.v -- the U-mode memory arms: the EXECUTE-LEVEL half.    *)
(*                                                                        *)
(* Package P4b.  An arm of [UserTotalU]'s frozen nineteen has two halves:  *)
(*                                                                        *)
(*   (a) the ACCESS half -- classify the runtime effective address         *)
(*       ([UserMemClassify.data_classify] / [in_one_page_dec]) and run the *)
(*       translation and the physical access ([UserMemCert]'s pure         *)
(*       composers, [UserFaultCert]'s fault translate);                    *)
(*   (b) the EXECUTE half -- turn the vmem result into an                  *)
(*       [ExecutionResult] and close [UserClassifyAsm.base_post].          *)
(*                                                                        *)
(* (b) does not depend on (a) at all: it takes the vmem [exec] fact and    *)
(* its [goodmb] certificate as a PAIR (the section-9 convention) and is    *)
(* the same four lemmas for every width and every arm.  It is here, proved *)
(* once, so that each arm is only its own case tree.                       *)
(*                                                                        *)
(* THE POST-STATE, ONCE.  A retiring load lands on                          *)
(* [gpr_write_state rd v (u_state rs' mm')] where [rs'] is [rs] or [rs]    *)
(* with ONE [tlb] write (the fill) -- so the [reg_agree_on u_Dfix]         *)
(* obligation is [u_fix_gpr_state] after [u_fix_tlb], the [tlb_ok_pt] one  *)
(* rides the gpr write by [u_tlb_gpr], and [u_mem_step] rides it by        *)
(* [u_mem_gpr].  A store and a delegated trap are the same with the gpr    *)
(* step dropped.  [tlb] is deliberately NOT in [u_Dfix] (worklist section  *)
(* 14.1: the footprint minus nextPC, tlb and the 31 gprs), which is what   *)
(* makes the fill invisible to the post-register fact.                     *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
(* for ssreflect's [rewrite /x] and [by]; nothing in this file is an [iProp] *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr RegFile UserBits.
Require Import HartLift HartSpan HartGoodb HartMemRun HartMemAsm PtBytes.
Require Import PtreeType PtTree SmodePte UptTree.
Require Import UserFrame UserBytes.
Require Import UserPtTree UserExec UserCompute UserClassify UserClassifyAsm.
Require Import UserExecFacts UserMemArms UserMemAccess UserMemPt UserMemMis.
Require Import UserTotalU UserMemTotal UserMemClassify.
Local Open Scope Z_scope.
Import Defs.

(* ---------------------------------------------------------------------- *)
(* THE TLB FILL IS INVISIBLE TO [u_Dfix].                                  *)
(* ---------------------------------------------------------------------- *)
Lemma tlb_not_u_Dfix : bool_decide ((tlb : register) ∈ u_Dfix) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma u_fix_tlb (tv : type_of_register tlb) (rs : regstate) :
  reg_agree_on u_Dfix (register_set tlb tv rs) rs.
Proof.
  intros r Hr. apply irrelevant_register_set.
  destruct (register_beq r tlb) eqn:Hb; [|reflexivity].
  exfalso. apply register_beq_true in Hb. subst r.
  pose proof tlb_not_u_Dfix as H.
  rewrite (bool_decide_eq_true_2 _ Hr) in H. discriminate.
Qed.

(* the landing file of a walk agrees with its entry file on [u_Dfix] *)
Lemma u_fix_land (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) ->
  reg_agree_on u_Dfix rs' rs.
Proof.
  intros [-> | (tv & ->)]; [ apply u_fix_refl | apply u_fix_tlb ].
Qed.

Section UserMemArmsBase.
  Context (pt : uptd).

  Local Notation s0r rsf va := (register_set nextPC (add_vec_int va 4) rsf).
  Local Notation s0 rsf mm va :=
    (u_state (register_set nextPC (add_vec_int va 4) rsf) mm).

  (* ------------------------------------------------------------------- *)
  (* (b) THE FOUR EXECUTE-LEVEL CLOSERS.                                  *)
  (* ------------------------------------------------------------------- *)

  (* a LOAD that retires, writing one gpr *)
  Lemma arm_load_retire (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5) (us : bool) (width : Z)
      (data : mword (8 * width)) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (LOAD (imm, Regidx rs1, Regidx rd, us, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (LOAD (imm, Regidx rs1, Regidx rd, us, width)) rsf ->
    (width <=? xlen_bytes) = true ->
    uint rd <> 0 ->
    exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data)
            false false false) (s0 rsf mm va)
      = Some (Ok data, u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_read (Regidx rs1) (sign_extend' 64 imm) width
            (Load Data) false false false) (s0 rsf mm va) mm = true ->
    (rs' = s0r rsf va \/ exists tv, rs' = register_set tlb tv (s0r rsf va)) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hrd Hvr Hvg Hland Htlb Hst.
    pose proof (Du_gpr_of_Z rd Hrd) as HDw.
    apply (finish_mem_base pt t t' mm rsf va
             (LOAD (imm, Regidx rs1, Regidx rd, us, width)) RETIRE_SUCCESS w
             (gpr_write_state rd (extend_value us data) (u_state rs' mm'))
             Hdec Hhv eq_refl).
    - rewrite (exec_execute_LOAD_u_ok imm rs1 rd us width data
                 (s0 rsf mm va) (u_state rs' mm') Hwok Hrd Hvr).
      unfold gpr_write_state.
      rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity.
    - exact (goodmb_execute_LOAD_u_ok Du_r Du_w imm rs1 rd us width data
               (s0 rsf mm va) (u_state rs' mm') mm HDw Hwok Hrd Hvr Hvg).
    - exact u_ok_retire.
    - exact I.
    - eapply u_fix_trans; [ apply u_fix_gpr_state | ].
      rewrite u_state_sregs. exact (u_fix_land _ _ Hland).
    - rewrite u_tlb_gpr u_state_sregs. exact Htlb.
    - rewrite u_mem_gpr u_state_mem. exact Hst.
  Qed.

  (* a LOAD whose access faulted: the arm delegates the trap *)
  Lemma arm_load_trap (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5) (us : bool) (width : Z)
      (e : ExceptionType) (xv pcx : mword 64) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (LOAD (imm, Regidx rs1, Regidx rd, us, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (LOAD (imm, Regidx rs1, Regidx rd, us, width)) rsf ->
    (width <=? xlen_bytes) = true ->
    user_exc e = true ->
    exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data)
            false false false) (s0 rsf mm va)
      = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
              u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_read (Regidx rs1) (sign_extend' 64 imm) width
            (Load Data) false false false) (s0 rsf mm va) mm = true ->
    (rs' = s0r rsf va \/ exists tv, rs' = register_set tlb tv (s0r rsf va)) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hue Hvr Hvg Hland Htlb Hst.
    apply (finish_mem_base pt t t' mm rsf va
             (LOAD (imm, Regidx rs1, Regidx rd, us, width))
             (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) w
             (u_state rs' mm') Hdec Hhv eq_refl).
    - exact (exec_execute_LOAD_u_err imm rs1 rd us width _
               (s0 rsf mm va) (u_state rs' mm') Hwok Hvr).
    - exact (goodmb_execute_LOAD_u_err Du_r Du_w imm rs1 rd us width _
               (s0 rsf mm va) (u_state rs' mm') mm Hwok Hvr Hvg).
    - exact (u_ok_trap e xv pcx Hue).
    - exact I.
    - rewrite u_state_sregs. exact (u_fix_land _ _ Hland).
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

  (* a STORE that retires: no gpr moves, only the byte map *)
  Lemma arm_store_retire (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (imm : mword 12) (rs2 rs1 : mword 5) (width : Z) (b : bool) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (STORE (imm, Regidx rs2, Regidx rs1, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (STORE (imm, Regidx rs2, Regidx rs1, width)) rsf ->
    (width <=? xlen_bytes) = true ->
    exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s0r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (Store Data) false false false) (s0 rsf mm va)
      = Some (Ok b, u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s0r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (Store Data) false false false) (s0 rsf mm va) mm = true ->
    (rs' = s0r rsf va \/ exists tv, rs' = register_set tlb tv (s0r rsf va)) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hvw Hvg Hland Htlb Hst.
    apply (finish_mem_base pt t t' mm rsf va
             (STORE (imm, Regidx rs2, Regidx rs1, width)) RETIRE_SUCCESS w
             (u_state rs' mm') Hdec Hhv eq_refl).
    - exact (exec_execute_STORE_u_ok imm rs2 rs1 width b
               (s0 rsf mm va) (u_state rs' mm') Hwok Hvw).
    - exact (goodmb_execute_STORE_u_ok Du_r Du_w imm rs2 rs1 width b
               (s0 rsf mm va) (u_state rs' mm') mm
               (fun H => Du_gpr_of_Z_r rs2 H) Hwok Hvw Hvg).
    - exact u_ok_retire.
    - exact I.
    - rewrite u_state_sregs. exact (u_fix_land _ _ Hland).
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

  (* a STORE whose access faulted *)
  Lemma arm_store_trap (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (imm : mword 12) (rs2 rs1 : mword 5) (width : Z)
      (e : ExceptionType) (xv pcx : mword 64) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (STORE (imm, Regidx rs2, Regidx rs1, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (STORE (imm, Regidx rs2, Regidx rs1, width)) rsf ->
    (width <=? xlen_bytes) = true ->
    user_exc e = true ->
    exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s0r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (Store Data) false false false) (s0 rsf mm va)
      = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
              u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s0r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (Store Data) false false false) (s0 rsf mm va) mm = true ->
    (rs' = s0r rsf va \/ exists tv, rs' = register_set tlb tv (s0r rsf va)) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hue Hvw Hvg Hland Htlb Hst.
    apply (finish_mem_base pt t t' mm rsf va
             (STORE (imm, Regidx rs2, Regidx rs1, width))
             (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) w
             (u_state rs' mm') Hdec Hhv eq_refl).
    - exact (exec_execute_STORE_u_err imm rs2 rs1 width _
               (s0 rsf mm va) (u_state rs' mm') Hwok Hvw).
    - exact (goodmb_execute_STORE_u_err Du_r Du_w imm rs2 rs1 width _
               (s0 rsf mm va) (u_state rs' mm') mm
               (fun H => Du_gpr_of_Z_r rs2 H) Hwok Hvw Hvg).
    - exact (u_ok_trap e xv pcx Hue).
    - exact I.
    - rewrite u_state_sregs. exact (u_fix_land _ _ Hland).
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

End UserMemArmsBase.
