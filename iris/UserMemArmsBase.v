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

Require Import WpDecodeBridge DecodeTotalU PtWalkCert UserFetchCert.
Require Import UserMemCert UserFaultCert MemAccessGen UserTranslate CommonWalk.
Set Printing Depth 40.

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


(* the U-mode pointer-masking probe's certificate *)
Lemma goodb_currentlyEnabled_S (Db : register -> bool) (s : mstate) :
  Db misa = true -> goodb Db (currentlyEnabled Ext_S) s = true.
Proof.
  intros Hm.
  gb_ce_open; apply goodb_and_boolM; [ gb_hs | ].
  apply goodb_and_boolM;
    [ apply goodb_bind_read_reg; [ exact Hm | reflexivity ] | gb_ce_next; gb_hs ].
Qed.

Lemma goodb_read_senvcfg_pinned (Db : register -> bool) (st : mstate) :
  Db menvcfg = true -> Db senvcfg = true ->
  goodb Db (read_senvcfg tt) st = true.
Proof.
  intros HDm HDs. unfold read_senvcfg.
  apply goodb_bind_read_reg; [ exact HDs |].
  apply goodb_bind_read_reg; [ exact HDm |].
  apply goodb_bind_read_reg; [ exact HDs |].
  reflexivity.
Qed.

Lemma goodb_is_pmm_applicable_u (Db : register -> bool)
    (acc : MemoryAccessType mem_payload) (s : mstate) :
  Db mstatus = true -> goodb Db (is_pmm_applicable acc User) s = true.
Proof.
  intros HDms. unfold is_pmm_applicable.
  repeat apply goodb_and_boolM; try reflexivity.
  apply goodb_or_boolM; [ reflexivity |].
  apply goodb_bind_read_reg; [ exact HDms | reflexivity ].
Qed.

Lemma goodb_get_pmm_u_disabled (Db : register -> bool) (s : mstate) :
  Db misa = true -> Db menvcfg = true -> Db senvcfg = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  goodb Db (get_pmm User) s = true.
Proof.
  intros HDmisa HDmenv HDsenv Hmisa.
  unfold get_pmm. cbn match.
  rewrite (goodb_bind Db _ _ s _ (goodb_currentlyEnabled_S Db s HDmisa)
             (exec_currentlyEnabled_S s)).
  rewrite Hmisa.
  replace (eq_vec (_get_Misa_S MISA_C) ('b"1")) with true
    by (vm_compute; reflexivity).
  cbn match.
  apply goodb_bind_forall; [ exact (goodb_read_senvcfg_pinned Db s HDmenv HDsenv) |].
  intros ?. reflexivity.
Qed.

Lemma goodb_get_pmlen_u (Db : register -> bool)
    (acc : MemoryAccessType mem_payload) (s : mstate) :
  Db mstatus = true -> Db misa = true -> Db menvcfg = true -> Db senvcfg = true ->
  generic_neq acc (InstructionFetch tt) = true ->
  generic_neq acc (Load PageTableEntry) = true ->
  generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
  goodb Db (get_pmlen acc User) s = true.
Proof.
  intros HDms HDmisa HDmenv HDsenv Hif Hlp Hsp Hmxr Hmisa Hmenv Hsenv.
  unfold get_pmlen.
  rewrite (goodb_bind Db _ _ s _ (goodb_is_pmm_applicable_u Db acc s HDms)
             (exec_is_pmm_applicable_u acc s Hif Hlp Hsp Hmxr)).
  cbn match.
  rewrite (goodb_bind Db _ _ s _ (goodb_get_pmm_u_disabled Db s HDmisa HDmenv HDsenv Hmisa)
             (exec_get_pmm_u_disabled s Hmisa Hmenv Hsenv)).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE LOAD's EXECUTE STEP, rd-GENERIC.  [UserMemArms]' pair splits on      *)
(* [uint rd <> 0]; [UserExecFacts.gpr_write_state] already carries the      *)
(* x0 case, so ONE pair covers both -- and the certificate's footprint      *)
(* obligation becomes the CONDITIONAL [Du_gpr_of_Z], which is exactly what  *)
(* [goodmb_wX_bits_gpr] asks for.                                          *)
(* ---------------------------------------------------------------------- *)
Lemma exec_execute_LOAD_u_retire (imm : mword 12) (rs1 rd : mword 5) (us : bool)
    (width : Z) (data : mword (8 * width)) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data)
          false false false) s = Some (Ok data, s') ->
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, us, width))) s
    = Some (RETIRE_SUCCESS, gpr_write_state rd (extend_value us data) s').
Proof.
  intros Hw Hvr.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, us, width)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) us width).
  unfold execute_LOAD. rewrite Hw.
  assert (Hass : exec (assert_exp' true
                   "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ Hvr). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (extend_value us data)) s'
                = Some (tt, gpr_write_state rd (extend_value us data) s'))
    by (rewrite (exec_wX_bits_gpr rd (extend_value us data) s'); reflexivity).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw2).
  apply exec_returnM.
Qed.

Lemma goodmb_execute_LOAD_u_retire (Dr Dw : register -> bool)
    (imm : mword 12) (rs1 rd : mword 5) (us : bool)
    (width : Z) (data : mword (8 * width)) (s s' : mstate) mm :
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  (width <=? xlen_bytes) = true ->
  exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data)
          false false false) s = Some (Ok data, s') ->
  goodmb Dr Dw (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data)
          false false false) s mm = true ->
  goodmb Dr Dw (execute (LOAD (imm, Regidx rs1, Regidx rd, us, width))) s mm = true.
Proof.
  intros HDrd Hw Hvr Hgvr.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, us, width)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) us width).
  unfold execute_LOAD. rewrite Hw.
  assert (Hass : exec (assert_exp' true
                   "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  assert (Hgass : goodmb Dr Dw (assert_exp' true
                   "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s mm
                 = true) by reflexivity.
  erewrite (gm_bind _ _ _ _ _ _ _ _ Hgass Hass).
  erewrite (gm_bind _ _ _ _ _ _ _ _ Hgvr Hvr). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (extend_value us data)) s'
                = Some (tt, gpr_write_state rd (extend_value us data) s'))
    by (rewrite (exec_wX_bits_gpr rd (extend_value us data) s'); reflexivity).
  erewrite (gm_bind0 _ _ _ _ _ _ _ (goodmb_wX_bits_gpr Dr Dw rd _ s' mm HDrd) Hw2).
  apply goodmb_returnm.
Qed.

Section UserMemArmsBase.
  Context (pt : uptd).

  Local Notation s0r rsf va := (register_set nextPC (add_vec_int va 4) rsf).
  Local Notation s0 rsf mm va :=
    (u_state (register_set nextPC (add_vec_int va 4) rsf) mm).

  (* ------------------------------------------------------------------- *)
  (* (b) THE FOUR EXECUTE-LEVEL CLOSERS.                                  *)
  (* ------------------------------------------------------------------- *)

  (* a LOAD that retires, writing one gpr (vacuously when rd is x0) *)
  Lemma arm_load_retire (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (imm : mword 12) (rs1 rd : mword 5) (us : bool) (width : Z)
      (data : mword (8 * width)) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (LOAD (imm, Regidx rs1, Regidx rd, us, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (LOAD (imm, Regidx rs1, Regidx rd, us, width)) rsf ->
    (width <=? xlen_bytes) = true ->
    exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data)
            false false false) (s0 rsf mm va)
      = Some (Ok data, u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_read (Regidx rs1) (sign_extend' 64 imm) width
            (Load Data) false false false) (s0 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s0r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hvr Hvg Hland Htlb Hst.
    apply (finish_mem_base pt t t' mm rsf va
             (LOAD (imm, Regidx rs1, Regidx rd, us, width)) RETIRE_SUCCESS w
             (gpr_write_state rd (extend_value us data) (u_state rs' mm'))
             Hdec Hhv eq_refl).
    - exact (exec_execute_LOAD_u_retire imm rs1 rd us width data
               (s0 rsf mm va) (u_state rs' mm') Hwok Hvr).
    - exact (goodmb_execute_LOAD_u_retire Du_r Du_w imm rs1 rd us width data
               (s0 rsf mm va) (u_state rs' mm') mm (Du_gpr_of_Z rd) Hwok Hvr Hvg).
    - exact u_ok_retire.
    - exact I.
    - eapply u_fix_trans; [ apply u_fix_gpr_state | ].
      rewrite u_state_sregs. exact Hland.
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
    reg_agree_on u_Dfix rs' (s0r rsf va) ->
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
    - rewrite u_state_sregs. exact Hland.
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
    reg_agree_on u_Dfix rs' (s0r rsf va) ->
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
    - rewrite u_state_sregs. exact Hland.
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
    reg_agree_on u_Dfix rs' (s0r rsf va) ->
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
    - rewrite u_state_sregs. exact Hland.
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

  (* a certificate read back at the map a step LANDED on is the same
     certificate: [goodmb] consults the map only through its domain. *)
  Lemma u_goodmb_step (t t' : ptree) (mm mm' : PtBytes.pamap) {E X}
      (m : Defs.monad E X) (s : mstate) :
    u_mem_wf pt t mm -> u_mem_step pt t t' mm mm' ->
    goodmb Du_r Du_w m s mm' = goodmb Du_r Du_w m s mm.
  Proof.
    intros Hwf Hst. apply goodmb_dom.
    exact (u_mem_step_dom pt t t' mm mm' Hwf Hst).
  Qed.


  (* the landing file of a walk is [u_Dfix]-invisible: [tlb] is not in it *)
  Lemma u_fix_of_tlb_only (rs rs' : regstate) :
    u_tlb_only rs rs' -> reg_agree_on u_Dfix rs' rs.
  Proof.
    intros H r Hr. apply H.
    destruct (register_beq r tlb) eqn:Hb; [| reflexivity].
    exfalso. apply register_beq_true in Hb. subst r.
    pose proof tlb_not_u_Dfix as Ht.
    rewrite (bool_decide_eq_true_2 _ Hr) in Ht. discriminate.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* (a) THE ACCESS HALF.  [UserMemCert] gives the effectivePrivilege and  *)
  (* translationMode probes; the two still missing are the pointer-masking *)
  (* length (which is where the U-mode senvcfg/misa pins are consumed) and *)
  (* the shadow-stack probe.                                              *)
  (* ------------------------------------------------------------------- *)
  Lemma u_pmlen_pure (t : ptree) (mm mb : PtBytes.pamap) (rs : regstate)
      (acc : MemoryAccessType mem_payload) :
    generic_neq acc (InstructionFetch tt) = true ->
    generic_neq acc (Load PageTableEntry) = true ->
    generic_neq acc (Store PageTableEntry) = true ->
    u_data_cfg rs -> u_exec_pins pt t rs ->
    exec (get_pmlen acc User) (u_state rs mm) = Some (0, u_state rs mm)
    /\ goodmb Du_r Du_w (get_pmlen acc User) (u_state rs mm) mb = true.
  Proof.
    intros Hif Hlp Hsp (_ & Lms & Lmenv) (Hhw & _).
    destruct Lms as (_ & _ & Lmxr & _).
    destruct Hhw as (Hmisa & _ & Hsenv & _ & _ & _).
    split.
    - exact (exec_get_pmlen_u acc (u_state rs mm) Hif Hlp Hsp Lmxr Hmisa Lmenv Hsenv).
    - exact (goodmb_of_goodb Du_r Du_w _ (u_state rs mm) mb
               (goodb_get_pmlen_u Du_r acc (u_state rs mm)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  Hif Hlp Hsp Lmxr Hmisa Lmenv Hsenv)).
  Qed.

  (* THE TRANSLATE-FAULT PAIR, access-type generic: [UserFaultCert]'s pure
     translate plus the [memory_exception] that turns it into the delegated
     trap.  The reported vaddr is the ACCESS's own [va] and the reported pc
     is the file's [PC] -- a faulting walk lands where it started. *)
  Lemma u_fault_pair (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
      (acc : MemoryAccessType mem_payload) (e : ExceptionType) (va : mword 64) :
    u_acc acc ->
    exec (translationException acc (PTW_Invalid_Addr tt)) (u_state rs mm)
      = Some (e, u_state rs mm) ->
    exec (translationException acc (PTW_Invalid_PTE tt)) (u_state rs mm)
      = Some (e, u_state rs mm) ->
    exec (translationException acc (PTW_No_Permission tt)) (u_state rs mm)
      = Some (e, u_state rs mm) ->
    u_fault_flavor acc (ud_tfp pt) (ud_um pt) va ->
    u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_wf pt t mm ->
    exec (translateAddr (Virtaddr va) acc) (u_state rs mm)
      = Some (Err (e, tt), u_state rs mm)
    /\ goodmb Du_r Du_w (translateAddr (Virtaddr va) acc) (u_state rs mm) mm = true
    /\ exec (memory_exception (Virtaddr va) e) (u_state rs mm)
         = Some (rv64d_types.Trap (User, make_sync_exception e va,
                                   register_lookup PC rs), u_state rs mm)
    /\ goodmb Du_r Du_w (memory_exception (Virtaddr va) e) (u_state rs mm) mm = true.
  Proof.
    intros Hacc Hte1 Hte2 Hte3 Hflavor Hcfg Hpins Hwf.
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (Lsxl & Lmprv & _).
    assert (Heff : exec (effectivePrivilege acc (register_lookup mstatus rs) User)
                     (u_state rs mm) = Some (User, u_state rs mm))
      by exact (exec_effectivePrivilege_mprv0 acc (register_lookup mstatus rs) User
                  (u_state rs mm) Lmprv).
    destruct (u_translate_fault_pure pt t mm rs acc e va Hflavor Hte1 Hte2 Hte3
                Heff (exec_is_shadow_stack_u_acc acc (u_state rs mm) Hacc)
                Lcp Lsxl Hpins Hwf) as (Htr & Htrg).
    split_and!; [ exact Htr | exact Htrg | | ].
    - exact (exec_memory_exception va (register_lookup PC rs) e User
               (u_state rs mm) Lcp eq_refl).
    - exact (goodmb_memory_exception Du_r Du_w va (register_lookup PC rs) e User
               (u_state rs mm) mm ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) Lcp eq_refl).
  Qed.

  (* the three [translationException] reductions a data access can meet *)
  Lemma u_texc_load (s : mstate) :
    exec (translationException (Load Data) (PTW_Invalid_Addr tt)) s
      = Some (E_Load_Page_Fault tt, s)
    /\ exec (translationException (Load Data) (PTW_Invalid_PTE tt)) s
      = Some (E_Load_Page_Fault tt, s)
    /\ exec (translationException (Load Data) (PTW_No_Permission tt)) s
      = Some (E_Load_Page_Fault tt, s).
  Proof. split_and!; unfold translationException; cbn match; apply exec_returnm. Qed.

  Lemma u_texc_store (s : mstate) :
    exec (translationException (Store Data) (PTW_Invalid_Addr tt)) s
      = Some (E_SAMO_Page_Fault tt, s)
    /\ exec (translationException (Store Data) (PTW_Invalid_PTE tt)) s
      = Some (E_SAMO_Page_Fault tt, s)
    /\ exec (translationException (Store Data) (PTW_No_Permission tt)) s
      = Some (E_SAMO_Page_Fault tt, s).
  Proof. split_and!; unfold translationException; cbn match; apply exec_returnm. Qed.

  (* the FAULT twins of [UserMemCert]'s [u_tarv_page] / [u_tawv_page] *)
  Lemma u_tarv_fault (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
      (k : Z) (va : mword 64) :
    u_fault_flavor (Load Data) (ud_tfp pt) (ud_um pt) va ->
    u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_wf pt t mm ->
    exec (translate_and_read_value (Virtaddr va) k (Load Data) false false false)
      (u_state rs mm)
      = Some (Err (rv64d_types.Trap (User,
                     make_sync_exception (E_Load_Page_Fault tt) va,
                     register_lookup PC rs)), u_state rs mm)
    /\ goodmb Du_r Du_w
         (translate_and_read_value (Virtaddr va) k (Load Data) false false false)
         (u_state rs mm) mm = true.
  Proof.
    intros Hflavor Hcfg Hpins Hwf.
    destruct (u_fault_pair t mm rs (Load Data) (E_Load_Page_Fault tt) va
                (or_intror (or_introl eq_refl))
                (proj1 (u_texc_load (u_state rs mm)))
                (proj1 (proj2 (u_texc_load (u_state rs mm))))
                (proj2 (proj2 (u_texc_load (u_state rs mm))))
                Hflavor Hcfg Hpins Hwf) as (Htr & Htrg & Hme & Hmeg).
    split.
    - exact (exec_translate_and_read_value_err k va (Load Data) false false false
               (E_Load_Page_Fault tt) _ (u_state rs mm) (u_state rs mm) Htr Hme).
    - exact (goodmb_translate_and_read_value_err Du_r Du_w k va (Load Data)
               false false false (E_Load_Page_Fault tt) _
               (u_state rs mm) (u_state rs mm) mm Htrg Htr Hmeg Hme).
  Qed.

  Lemma u_tawv_fault (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
      (k : Z) (va : mword 64) (v : mword (8 * k)) :
    u_fault_flavor (Store Data) (ud_tfp pt) (ud_um pt) va ->
    u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_wf pt t mm ->
    exec (translate_and_write_value (Virtaddr va) k v (Store Data) false false false)
      (u_state rs mm)
      = Some (Err (rv64d_types.Trap (User,
                     make_sync_exception (E_SAMO_Page_Fault tt) va,
                     register_lookup PC rs)), u_state rs mm)
    /\ goodmb Du_r Du_w
         (translate_and_write_value (Virtaddr va) k v (Store Data) false false false)
         (u_state rs mm) mm = true.
  Proof.
    intros Hflavor Hcfg Hpins Hwf.
    destruct (u_fault_pair t mm rs (Store Data) (E_SAMO_Page_Fault tt) va
                (or_intror (or_intror (or_introl eq_refl)))
                (proj1 (u_texc_store (u_state rs mm)))
                (proj1 (proj2 (u_texc_store (u_state rs mm))))
                (proj2 (proj2 (u_texc_store (u_state rs mm))))
                Hflavor Hcfg Hpins Hwf) as (Htr & Htrg & Hme & Hmeg).
    split.
    - exact (exec_translate_and_write_value_err k va v (Store Data) false false false
               (E_SAMO_Page_Fault tt) _ (u_state rs mm) (u_state rs mm) Htr Hme).
    - exact (goodmb_translate_and_write_value_err Du_r Du_w k va v (Store Data)
               false false false (E_SAMO_Page_Fault tt) _
               (u_state rs mm) (u_state rs mm) mm Htrg Htr Hmeg Hme).
  Qed.

End UserMemArmsBase.
