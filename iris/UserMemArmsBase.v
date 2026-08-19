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

(* ---------------------------------------------------------------------- *)
(* THE STORE'S TRANSLATE-FAULT CERTIFICATE.  [MemAccessGen] has the [exec]  *)
(* half ([exec_vmem_write_addr_intra_terr]) and [UserMemAccess] the [goodmb]*)
(* twin of every OTHER vmem_write_addr arm; this is the one that was        *)
(* missing.  The region THROWS, so [goodmb_cer] is unavailable and the      *)
(* [catch_early_return] wrapper stays on -- the [gm_cer_*] peel of          *)
(* [UserMemMis.goodmb_vmem_write_addr_split2_err1], at [q = 0].             *)
(* ---------------------------------------------------------------------- *)
Lemma goodmb_vmem_write_addr_intra_terr (Dr Dw : register -> bool) (width : Z)
    (va : mword 64) (dat : mword (8*width))
    (acc : MemoryAccessType mem_payload) (aq rl res : bool) (e : ExceptionType)
    (er : ExecutionResult) (ep : Privilege) (md : SATPMode) (s s2 : mstate) mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < width ->
  exec (split_on_page_boundary va width) s = Some ((width, 0), s) ->
  goodmb Dr Dw (split_on_page_boundary va width) s mm = true ->
  (is_aligned_vaddr (Virtaddr va) width = true \/
   plat_misaligned_exception acc res = None) ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translateAddr (Virtaddr va) acc) s = Some (Err (e, tt), s2) ->
  goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true ->
  exec (memory_exception (Virtaddr va) e) s2 = Some (er, s2) ->
  goodmb Dr Dw (memory_exception (Virtaddr va) e) s2 mm = true ->
  goodmb Dr Dw (vmem_write_addr (Virtaddr va) width dat acc aq rl res) s mm = true.
Proof.
  intros HDm HDc Hpos Hsplit Hsplitg Hguard Heff Heffg Htm Htmg Htr Htrg Hme Hmeg.
  assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDc).
  unfold vmem_write_addr.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hgg : goodmb Dr Dw G s mm = true);
    [ | assert (Hg : execR G s = Some (inr tt, s)) ] end.
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply goodmb_returnm. }
  { destruct (is_aligned_vaddr (Virtaddr va) width) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb].
      destruct Hguard as [Hal | Hmis]; [ rewrite Hal in E; discriminate |].
      rewrite Hmis. apply execR_returnR_fwd. }
  erewrite gm_cer_bind0; [ | exact Hgg | exact Hg ].
  cbn [bits_of_virtaddr]. cbn zeta.
  gmm_lift Hsplitg Hsplit. cbn beta zeta match.
  gmm_lift Hmst (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpr (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true);
    [ | assert (Hds : execR (Defs.and_boolM A B) s = Some (inr false, s)) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s));
      [ | assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true) ] end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    { gmm_lift Htmg Htm. cbn beta. apply goodmb_returnm. }
    erewrite gm_bindR; [ | exact Hlg | exact Hl ]. cbn match beta.
    destruct (generic_neq md Bare); apply goodmb_returnm. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). cbn match beta.
    destruct (generic_neq md Bare); apply execR_returnR_fwd. }
  erewrite gm_cer_bind; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  erewrite gm_cer_bind;
    [ | apply goodmb_returnm | apply (execR_returnR_fwd true s) ]. cbn beta zeta.
  gmm_lift Htrg Htr. cbn match beta.
  gmm_lift Hmeg Hme. cbn match beta.
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
                Lcp Lsxl Hpins (u_mem_wf_ok pt t mm Hwf)) as (Htr & Htrg).
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

  (* ------------------------------------------------------------------- *)
  (* THE LOAD'S CASE TREE, at the [vmem_read_addr] level.                  *)
  (*                                                                     *)
  (* The effective address is an ARBITRARY 64-bit word, so this is a       *)
  (* TRICHOTOMY crossed with the page-straddle decision, not a             *)
  (* composition: [UserMemClassify.in_one_page_dec] picks the geometry and *)
  (* [data_classify] picks mapped-vs-faulting at EACH page the access      *)
  (* touches.  Four arms retire (one page, or two), three fault.           *)
  (* ------------------------------------------------------------------- *)
  Lemma u_vmem_read_pure (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
      (k : Z) (va : mword 64) :
    0 < k -> k <= 8 ->
    u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_wf pt t mm ->
    (exists (dv : mword (8 * k)) (rs' : regstate) (mm' : PtBytes.pamap)
            (t' : ptree),
        exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false)
          (u_state rs mm) = Some (Ok dv, u_state rs' mm')
        /\ goodmb Du_r Du_w
             (vmem_read_addr (Virtaddr va) k (Load Data) false false false)
             (u_state rs mm) mm = true
        /\ u_tlb_only rs rs'
        /\ tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs')
        /\ u_mem_step pt t t' mm mm')
    \/ (exists (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree)
               (e : ExceptionType) (xv pcx : mword 64),
        exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false)
          (u_state rs mm)
          = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
                  u_state rs' mm')
        /\ goodmb Du_r Du_w
             (vmem_read_addr (Virtaddr va) k (Load Data) false false false)
             (u_state rs mm) mm = true
        /\ user_exc e = true
        /\ u_tlb_only rs rs'
        /\ tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs')
        /\ u_mem_step pt t t' mm mm').
  Proof.
    intros Hk Hk8 Hcfg Hpins Hwf.
    pose proof Hwf as (md0 & _ & _ & _ & _ & _ & _ & Hacc & _ & _).
    pose proof Hpins as (_ & _ & _ & Htlb0).
    assert (Hpm : plat_misaligned_exception (Load Data) false = None)
      by (apply plat_misaligned_loadstore_none; vm_compute; reflexivity).
    pose proof (u_effectivePrivilege_pure (Load Data) rs mm Hcfg) as Heff.
    pose proof (u_goodmb_effectivePrivilege_pure (Load Data) rs mm mm Hcfg) as Heffg.
    pose proof (u_translationMode_pure pt t rs mm Hcfg Hpins) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t rs mm mm Hcfg Hpins) as Htmg.
    destruct (in_one_page_dec va k) as [Hin | Hout].
    - (* ONE PAGE: one classification, one walk, whatever the alignment *)
      pose proof (exec_split_on_page_boundary_intra va k (u_state rs mm) Hk Hin)
        as Hsp.
      pose proof (goodmb_split_on_page_boundary Du_r Du_w va k
                    (u_state rs mm) (u_state rs mm) (k, 0) mm Hsp) as Hspg.
      destruct (data_classify (Load Data) (ud_tfp pt) (ud_um pt) va
                  (or_intror (or_introl eq_refl)) Hacc)
        as [ (w & Hum & Hok & Hcanon) | Hfault ].
      + destruct (u_tarv_page pt t mm rs k w va Hk Hk8 Hin Hum Hok Hcanon
                    Hcfg Hpins Hwf)
          as (dv & rs' & mm' & t' & Htrv & Htrvg & Honly & Htlbok & Hstep & _).
        left. exists dv, rs', mm', t'. split_and!;
          [ exact (exec_vmem_read_addr_intra k va (u_walk_pa w va) dv (Load Data)
                     false false false User Sv39 (u_state rs mm) (u_state rs' mm')
                     Hk Hsp (or_intror Hpm) Heff Htm Htrv ltac:(discriminate))
          | exact (goodmb_vmem_read_addr_intra Du_r Du_w k va (u_walk_pa w va) dv
                     (Load Data) false false false User Sv39
                     (u_state rs mm) (u_state rs' mm') mm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hk Hsp Hspg (or_intror Hpm) Heff Heffg Htm Htmg Htrv Htrvg)
          | exact Honly | exact Htlbok | exact Hstep ].
      + destruct (u_tarv_fault t mm rs k va Hfault Hcfg Hpins Hwf) as (Htrv & Htrvg).
        right. exists rs, mm, t, (E_Load_Page_Fault tt), va, (register_lookup PC rs).
        split_and!;
          [ exact (exec_vmem_read_addr_intra_err k va _ (Load Data)
                     false false false User Sv39 (u_state rs mm) (u_state rs mm)
                     Hk Hsp (or_intror Hpm) Heff Htm Htrv)
          | exact (goodmb_vmem_read_addr_intra_err Du_r Du_w k va _ (Load Data)
                     false false false User Sv39 (u_state rs mm) (u_state rs mm) mm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hk Hsp Hspg (or_intror Hpm) Heff Heffg Htm Htmg Htrv Htrvg)
          | vm_compute; reflexivity
          | exact (u_tlb_only_refl rs) | exact Htlb0
          | exact (u_mem_step_refl pt t mm Hwf) ].
    - (* TWO PAGES: the access ends one page and starts the next *)
      destruct (straddle_bounds va k Hk Hk8 Hout) as (Hp0 & Hq0 & Hp8 & Hq8).
      pose proof (exec_split_on_page_boundary_straddle va k (u_state rs mm)
                    Hk Hk8 Hout) as Hsp.
      pose proof (goodmb_split_on_page_boundary Du_r Du_w va k
                    (u_state rs mm) (u_state rs mm) _ mm Hsp) as Hspg.
      set (pp := 4096 - bv_unsigned va mod 4096) in *.
      destruct (data_classify (Load Data) (ud_tfp pt) (ud_um pt) va
                  (or_intror (or_introl eq_refl)) Hacc)
        as [ Hok1 | Hf1 ].
      + destruct Hok1 as (w1 & Hum1 & Hleaf1 & Hcanon1).
        destruct (data_classify (Load Data) (ud_tfp pt) (ud_um pt)
                    (add_vec_int va pp) (or_intror (or_introl eq_refl)) Hacc)
          as [ Hok2 | Hf2 ].
        * destruct Hok2 as (w2 & Hum2 & Hleaf2 & Hcanon2).
          destruct (u_load_pure_two pt t mm rs pp (k - pp) w1 w2 va
                      Hp0 Hp8 (straddle_part1_in_page va k)
                      Hq0 Hq8 (straddle_part2_in_page va k Hk Hk8 Hout)
                      Hum1 Hum2 Hleaf1 Hleaf2 Hcanon1 Hcanon2 Hcfg Hpins Hwf)
            as (v1 & v2 & rs1 & mm1 & t1 & rs2 & mm2 & t2
                & H1 & H1g & H2 & H2g & Honly & Htlb2 & Hst2 & _).
          destruct (exec_vmem_read_addr_split2 k pp (k - pp) va
                      (u_walk_pa w1 va) (u_walk_pa w2 (add_vec_int va pp))
                      v1 v2 (Load Data) false false User Sv39
                      (u_state rs mm) (u_state rs1 mm1) (u_state rs2 mm2)
                      Hp0 Hq0 Hsp Hpm Heff Htm
                      ltac:(vm_compute; reflexivity) H1 H2) as (dvv & Hvr).
          left. exists dvv, rs2, mm2, t2. split_and!;
            [ exact Hvr
            | exact (goodmb_vmem_read_addr_split2 Du_r Du_w k pp (k - pp) va
                       (u_walk_pa w1 va) (u_walk_pa w2 (add_vec_int va pp))
                       v1 v2 (Load Data) false false User Sv39
                       (u_state rs mm) (u_state rs1 mm1) (u_state rs2 mm2) mm
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       Hp0 Hq0 Hspg Hsp Hpm Heffg Heff Htmg Htm
                       ltac:(vm_compute; reflexivity) H1g H1 H2g H2)
            | exact Honly | exact Htlb2 | exact Hst2 ].
        * (* the FIRST page lands, the SECOND faults *)
          destruct (u_tarv_page pt t mm rs pp w1 va Hp0 Hp8
                      (straddle_part1_in_page va k) Hum1 Hleaf1 Hcanon1
                      Hcfg Hpins Hwf)
            as (v1 & rs1 & mm1 & t1 & H1 & H1g & Ho1 & Htlb1 & Hst1
                & Hcfg1 & Hpins1 & Hwf1).
          destruct (u_tarv_fault t1 mm1 rs1 (k - pp) (add_vec_int va pp)
                      Hf2 Hcfg1 Hpins1 Hwf1) as (H2 & H2g0).
          assert (H2g : goodmb Du_r Du_w
                    (translate_and_read_value (Virtaddr (add_vec_int va pp))
                       (k - pp) (Load Data) false false false)
                    (u_state rs1 mm1) mm = true)
            by (rewrite <- (u_goodmb_step t t1 mm mm1 _ _ Hwf Hst1); exact H2g0).
          right. exists rs1, mm1, t1, (E_Load_Page_Fault tt),
            (add_vec_int va pp), (register_lookup PC rs1).
          split_and!;
            [ exact (exec_vmem_read_addr_split2_err2 k pp (k - pp) va
                       (u_walk_pa w1 va) v1 _ (Load Data) false false User Sv39
                       (u_state rs mm) (u_state rs1 mm1) (u_state rs1 mm1)
                       Hp0 Hq0 Hsp Hpm Heff Htm
                       ltac:(vm_compute; reflexivity) H1 H2)
            | exact (goodmb_vmem_read_addr_split2_err2 Du_r Du_w k pp (k - pp) va
                       (u_walk_pa w1 va) v1 _ (Load Data) false false User Sv39
                       (u_state rs mm) (u_state rs1 mm1) (u_state rs1 mm1) mm
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       Hp0 Hq0 Hspg Hsp Hpm Heffg Heff Htmg Htm
                       ltac:(vm_compute; reflexivity) H1g H1 H2g H2)
            | vm_compute; reflexivity
            | exact Ho1 | exact Htlb1 | exact Hst1 ].
      + (* the FIRST page faults: the model never reaches the second *)
        destruct (u_tarv_fault t mm rs pp va Hf1 Hcfg Hpins Hwf) as (H1 & H1g).
        right. exists rs, mm, t, (E_Load_Page_Fault tt), va, (register_lookup PC rs).
        split_and!;
          [ exact (exec_vmem_read_addr_split2_err1 k pp (k - pp) va _ (Load Data)
                     false false User Sv39 (u_state rs mm) (u_state rs mm)
                     Hp0 Hq0 Hsp Hpm Heff Htm
                     ltac:(vm_compute; reflexivity) H1)
          | exact (goodmb_vmem_read_addr_split2_err1 Du_r Du_w k pp (k - pp) va
                     _ (Load Data) false false User Sv39
                     (u_state rs mm) (u_state rs mm) mm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hp0 Hq0 Hspg Hsp Hpm Heffg Heff Htmg Htm
                     ltac:(vm_compute; reflexivity) H1g H1)
          | vm_compute; reflexivity
          | exact (u_tlb_only_refl rs) | exact Htlb0
          | exact (u_mem_step_refl pt t mm Hwf) ].
  Qed.

  (* the data-access config rides the nextPC tick (the twin of
     [UserTotalU.u_pins_tick]: none of its three cells is nextPC) *)
  Lemma u_data_cfg_tick (rsf : regstate) (va : mword 64) (n : Z) :
    u_data_cfg rsf ->
    u_data_cfg (register_set nextPC (add_vec_int va n) rsf).
  Proof.
    intros (Lcp & Lms & Lmenv). split_and!;
      [ rewrite (u_tick_reg cur_privilege rsf va n eq_refl); exact Lcp
      | rewrite (u_tick_reg (R_bitvector_64 mstatus) rsf va n eq_refl); exact Lms
      | rewrite (u_tick_reg (R_bitvector_64 menvcfg) rsf va n eq_refl);
        exact Lmenv ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE ARM.  [UserTotalU]'s frozen [arm_LOAD_u], proved.                 *)
  (* ------------------------------------------------------------------- *)
  Lemma arm_LOAD_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (imm : bits 12) (rs1 rd : regidx) (is_unsigned : bool)
      (width : word_width) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (LOAD (imm, rs1, rd, is_unsigned, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (LOAD (imm, rs1, rd, is_unsigned, width)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hpfc Hag Hwid Hdec Hhv Hpins Hwf.
    destruct rs1 as [ir1]. destruct rd as [ird].
    assert (Hk : 0 < width) by (destruct Hwid as [-> | [-> | [-> | ->]]]; lia).
    assert (Hk8 : width <= 8) by (destruct Hwid as [-> | [-> | [-> | ->]]]; lia).
    assert (Hwok : (width <=? xlen_bytes) = true)
      by (destruct Hwid as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity).
    (* everything runs at the TICKED file *)
    pose proof (u_data_cfg_tick rsf va 4
                  (u_data_cfg_of_post_fetch rsf mm va mi Hpfc)) as Hcfg.
    pose proof (u_pins_tick pt t rsf va 4 Hpins) as Hpins'.
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    assert (Heff : exec (effectivePrivilege (Load Data)
                     (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                     (s0 rsf mm va) = Some (User, s0 rsf mm va))
      by exact (exec_effectivePrivilege_mprv0 (Load Data) _ User (s0 rsf mm va) Lmprv).
    assert (Heffg : goodmb Du_r Du_w (effectivePrivilege (Load Data)
                      (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                      (s0 rsf mm va) mm = true)
      by exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Load Data) _ User
                  (s0 rsf mm va) mm Lmprv).
    destruct (u_pmlen_pure t mm mm (s0r rsf va) (Load Data)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hcfg Hpins') as (Hpml & Hpmlg).
    pose proof (u_translationMode_pure pt t (s0r rsf va) mm Hcfg Hpins') as Htm.
    pose proof (u_goodmb_translationMode_pure pt t (s0r rsf va) mm mm Hcfg Hpins')
      as Htmg.
    destruct (u_vmem_read_pure t mm (s0r rsf va) width
                (add_vec (if Z.eqb (uint ir1) 0 then zero_reg
                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint ir1)))
                                 (s0 rsf mm va).(sregs))
                         (sign_extend' 64 imm))
                Hk Hk8 Hcfg Hpins' Hwf)
      as [ (dv & rs' & mm' & t' & Hvr & Hvrg & Honly & Htlbok & Hstep)
         | (rs' & mm' & t' & e & xv & pcx & Hvr & Hvrg & Hue & Honly & Htlbok & Hstep) ].
    - apply (arm_load_retire t t' mm mm' rsf rs' va w imm ir1 ird is_unsigned
               width dv Hdec Hhv Hwok);
        [ exact (exec_vmem_read_u ir1 (sign_extend' 64 imm) width (Load Data)
                   false false false Sv39 (Ok dv) (s0 rsf mm va) (u_state rs' mm')
                   Lcp Heff Hpml Htm Hvr)
        | exact (goodmb_vmem_read_u Du_r Du_w ir1 (sign_extend' 64 imm) width
                   (Load Data) false false false Sv39 (Ok dv)
                   (s0 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvr Hvrg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
    - apply (arm_load_trap t t' mm mm' rsf rs' va w imm ir1 ird is_unsigned
               width e xv pcx Hdec Hhv Hwok Hue);
        [ exact (exec_vmem_read_u ir1 (sign_extend' 64 imm) width (Load Data)
                   false false false Sv39 (Err _) (s0 rsf mm va) (u_state rs' mm')
                   Lcp Heff Hpml Htm Hvr)
        | exact (goodmb_vmem_read_u Du_r Du_w ir1 (sign_extend' 64 imm) width
                   (Load Data) false false false Sv39 (Err _)
                   (s0 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvr Hvrg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE STORE'S CASE TREE, at the [vmem_write_addr] level -- the LOAD's,  *)
  (* with the read replaced by the announce-then-write pair.               *)
  (* ------------------------------------------------------------------- *)
  Lemma u_vmem_write_pure (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
      (k : Z) (va : mword 64) (dat : mword (8 * k)) :
    0 < k -> k <= 8 ->
    u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_wf pt t mm ->
    (exists (b : bool) (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree),
        exec (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false)
          (u_state rs mm) = Some (Ok b, u_state rs' mm')
        /\ goodmb Du_r Du_w
             (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false)
             (u_state rs mm) mm = true
        /\ u_tlb_only rs rs'
        /\ tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs')
        /\ u_mem_step pt t t' mm mm')
    \/ (exists (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree)
               (e : ExceptionType) (xv pcx : mword 64),
        exec (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false)
          (u_state rs mm)
          = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
                  u_state rs' mm')
        /\ goodmb Du_r Du_w
             (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false)
             (u_state rs mm) mm = true
        /\ user_exc e = true
        /\ u_tlb_only rs rs'
        /\ tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs')
        /\ u_mem_step pt t t' mm mm').
  Proof.
    intros Hk Hk8 Hcfg Hpins Hwf.
    pose proof Hwf as (md0 & _ & _ & _ & _ & _ & _ & Hacc & _ & _).
    pose proof Hpins as (_ & _ & _ & Htlb0).
    assert (Hpm : plat_misaligned_exception (Store Data) false = None)
      by (apply plat_misaligned_loadstore_none; vm_compute; reflexivity).
    pose proof (u_effectivePrivilege_pure (Store Data) rs mm Hcfg) as Heff.
    pose proof (u_goodmb_effectivePrivilege_pure (Store Data) rs mm mm Hcfg) as Heffg.
    pose proof (u_translationMode_pure pt t rs mm Hcfg Hpins) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t rs mm mm Hcfg Hpins) as Htmg.
    destruct (in_one_page_dec va k) as [Hin | Hout].
    - (* ONE PAGE *)
      pose proof (exec_split_on_page_boundary_intra va k (u_state rs mm) Hk Hin)
        as Hsp.
      pose proof (goodmb_split_on_page_boundary Du_r Du_w va k
                    (u_state rs mm) (u_state rs mm) (k, 0) mm Hsp) as Hspg.
      destruct (data_classify (Store Data) (ud_tfp pt) (ud_um pt) va
                  (or_intror (or_intror (or_introl eq_refl))) Hacc)
        as [ (w & Hum & Hok & Hcanon) | Hfault ].
      + destruct (u_store_pure_page pt t mm rs k w va
                    (autocast (T := mword) (subrange_vec_dec dat (8 * k - 1) 0))
                    Hk Hk8 Hin Hum Hok Hcanon Hcfg Hpins Hwf)
          as (rs' & mm' & mm2 & t' & Htr & Htrg & Hea & Heag & Hwv & Hwvg
              & Hfile & Htlbok & Hstep & Hstep2 & _).
        assert (Heag' : goodmb Du_r Du_w
                  (mem_write_ea (Physaddr (u_walk_pa w va)) k (Store Data) PBMT_PMA
                     false false false) (u_state rs' mm') mm = true)
          by (rewrite <- (u_goodmb_step t t' mm mm' _ _ Hwf Hstep); exact Heag).
        assert (Hwvg' : goodmb Du_r Du_w
                  (mem_write_value (Physaddr (u_walk_pa w va)) k
                     (autocast (T := mword) (subrange_vec_dec dat (8 * k - 1) 0))
                     (Store Data) PBMT_PMA false false false)
                  (u_state rs' mm') mm = true)
          by (rewrite <- (u_goodmb_step t t' mm mm' _ _ Hwf Hstep); exact Hwvg).
        left. exists true, rs', mm2, t'. split_and!;
          [ exact (exec_vmem_write_addr_intra k va (u_walk_pa w va) dat User Sv39
                     (u_state rs mm) (u_state rs' mm') (u_state rs' mm2)
                     Hk Hsp (or_intror Hpm) Heff Htm Htr Hea Hwv)
          | exact (goodmb_vmem_write_addr_intra Du_r Du_w k va (u_walk_pa w va) dat
                     User Sv39 (u_state rs mm) (u_state rs' mm') (u_state rs' mm2) mm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hk Hsp Hspg (or_intror Hpm) Heff Heffg Htm Htmg
                     Htr Htrg Hea Heag' Hwv Hwvg')
          | exact (u_tlb_only_land rs rs' Hfile) | exact Htlbok | exact Hstep2 ].
      + destruct (u_fault_pair t mm rs (Store Data) (E_SAMO_Page_Fault tt) va
                    (or_intror (or_intror (or_introl eq_refl)))
                    (proj1 (u_texc_store (u_state rs mm)))
                    (proj1 (proj2 (u_texc_store (u_state rs mm))))
                    (proj2 (proj2 (u_texc_store (u_state rs mm))))
                    Hfault Hcfg Hpins Hwf) as (Htr & Htrg & Hme & Hmeg).
        right. exists rs, mm, t, (E_SAMO_Page_Fault tt), va, (register_lookup PC rs).
        split_and!;
          [ exact (exec_vmem_write_addr_intra_terr k va dat (Store Data)
                     false false false (E_SAMO_Page_Fault tt) _ User Sv39
                     (u_state rs mm) (u_state rs mm)
                     Hk Hsp (or_intror Hpm) Heff Htm Htr Hme)
          | exact (goodmb_vmem_write_addr_intra_terr Du_r Du_w k va dat (Store Data)
                     false false false (E_SAMO_Page_Fault tt) _ User Sv39
                     (u_state rs mm) (u_state rs mm) mm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hk Hsp Hspg (or_intror Hpm) Heff Heffg Htm Htmg
                     Htr Htrg Hme Hmeg)
          | vm_compute; reflexivity
          | exact (u_tlb_only_refl rs) | exact Htlb0
          | exact (u_mem_step_refl pt t mm Hwf) ].
    - (* TWO PAGES *)
      destruct (straddle_bounds va k Hk Hk8 Hout) as (Hp0 & Hq0 & Hp8 & Hq8).
      pose proof (exec_split_on_page_boundary_straddle va k (u_state rs mm)
                    Hk Hk8 Hout) as Hsp.
      pose proof (goodmb_split_on_page_boundary Du_r Du_w va k
                    (u_state rs mm) (u_state rs mm) _ mm Hsp) as Hspg.
      set (pp := 4096 - bv_unsigned va mod 4096) in *.
      destruct (data_classify (Store Data) (ud_tfp pt) (ud_um pt) va
                  (or_intror (or_intror (or_introl eq_refl))) Hacc)
        as [ Hok1 | Hf1 ].
      + destruct Hok1 as (w1 & Hum1 & Hleaf1 & Hcanon1).
        destruct (data_classify (Store Data) (ud_tfp pt) (ud_um pt)
                    (add_vec_int va pp)
                    (or_intror (or_intror (or_introl eq_refl))) Hacc)
          as [ Hok2 | Hf2 ].
        * destruct Hok2 as (w2 & Hum2 & Hleaf2 & Hcanon2).
          destruct (u_store_pure_two pt t mm rs pp (k - pp) w1 w2 va
                      (autocast (T := mword) (subrange_vec_dec dat (8 * pp - 1) 0))
                      (autocast (T := mword)
                         (subrange_vec_dec dat (8 * k - 1) (8 * pp)))
                      Hp0 Hp8 (straddle_part1_in_page va k)
                      Hq0 Hq8 (straddle_part2_in_page va k Hk Hk8 Hout)
                      Hum1 Hum2 Hleaf1 Hleaf2 Hcanon1 Hcanon2 Hcfg Hpins Hwf)
            as (rs1 & mm1 & mm1w & t1 & rs2 & mm2 & t2
                & Htr & Htrg & Hea & Heag & Hwv & Hwvg & Htwv & Htwvg
                & Honly & Htlb2 & Hst2 & _).
          left. exists true, rs2, mm2, t2. split_and!;
            [ exact (exec_vmem_write_addr_split2 k pp (k - pp) va
                       (u_walk_pa w1 va) dat User Sv39
                       (u_state rs mm) (u_state rs1 mm1) (u_state rs1 mm1w)
                       (u_state rs2 mm2) (conj Hp0 Hq0) Hsp Hpm Heff Htm
                       ltac:(vm_compute; reflexivity) true Htr Hea Hwv Htwv)
            | exact (goodmb_vmem_write_addr_split2 k pp (k - pp) va
                       (u_walk_pa w1 va) dat User Sv39
                       (u_state rs mm) (u_state rs1 mm1) (u_state rs1 mm1w)
                       (u_state rs2 mm2) (conj Hp0 Hq0) Hsp Hpm Heff Htm
                       ltac:(vm_compute; reflexivity) Du_r Du_w true mm
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       Hspg Heffg Htmg Htrg Htr Heag Hea Hwvg Hwv Htwvg Htwv)
            | exact Honly | exact Htlb2 | exact Hst2 ].
        * (* the FIRST page lands, the SECOND faults *)
          destruct (u_store_pure_page pt t mm rs pp w1 va
                      (autocast (T := mword) (subrange_vec_dec dat (8 * pp - 1) 0))
                      Hp0 Hp8 (straddle_part1_in_page va k) Hum1 Hleaf1 Hcanon1
                      Hcfg Hpins Hwf)
            as (rs1 & mm1 & mm1w & t1 & Htr & Htrg & Hea & Heag0 & Hwv & Hwvg0
                & Hfile & Htlb1 & Hst1 & Hst1w & Hcfg1 & Hpins1).
          assert (Hwf1w : u_mem_wf pt t1 mm1w)
            by exact (u_mem_step_wf pt t t1 mm mm1w Hwf Hst1w).
          assert (Heag : goodmb Du_r Du_w
                    (mem_write_ea (Physaddr (u_walk_pa w1 va)) pp (Store Data)
                       PBMT_PMA false false false) (u_state rs1 mm1) mm = true)
            by (rewrite <- (u_goodmb_step t t1 mm mm1 _ _ Hwf Hst1); exact Heag0).
          assert (Hwvg : goodmb Du_r Du_w
                    (mem_write_value (Physaddr (u_walk_pa w1 va)) pp
                       (autocast (T := mword) (subrange_vec_dec dat (8 * pp - 1) 0))
                       (Store Data) PBMT_PMA false false false)
                    (u_state rs1 mm1) mm = true)
            by (rewrite <- (u_goodmb_step t t1 mm mm1 _ _ Hwf Hst1); exact Hwvg0).
          destruct (u_tawv_fault t1 mm1w rs1 (k - pp) (add_vec_int va pp)
                      (autocast (T := mword)
                         (subrange_vec_dec dat (8 * k - 1) (8 * pp)))
                      Hf2 Hcfg1 Hpins1 Hwf1w) as (Htwv & Htwvg0).
          assert (Htwvg : goodmb Du_r Du_w
                    (translate_and_write_value (Virtaddr (add_vec_int va pp)) (k - pp)
                       (autocast (T := mword)
                          (subrange_vec_dec dat (8 * k - 1) (8 * pp)))
                       (Store Data) false false false) (u_state rs1 mm1w) mm = true)
            by (rewrite <- (u_goodmb_step t t1 mm mm1w _ _ Hwf Hst1w); exact Htwvg0).
          right. exists rs1, mm1w, t1, (E_SAMO_Page_Fault tt),
            (add_vec_int va pp), (register_lookup PC rs1).
          split_and!;
            [ exact (exec_vmem_write_addr_split2_err2 k pp (k - pp) va
                       (u_walk_pa w1 va) dat User Sv39
                       (u_state rs mm) (u_state rs1 mm1) (u_state rs1 mm1w)
                       (u_state rs1 mm1w) (conj Hp0 Hq0) Hsp Hpm Heff Htm
                       ltac:(vm_compute; reflexivity) _ Htr Hea Hwv Htwv)
            | exact (goodmb_vmem_write_addr_split2_err2 k pp (k - pp) va
                       (u_walk_pa w1 va) dat User Sv39
                       (u_state rs mm) (u_state rs1 mm1) (u_state rs1 mm1w)
                       (u_state rs1 mm1w) (conj Hp0 Hq0) Hsp Hpm Heff Htm
                       ltac:(vm_compute; reflexivity) Du_r Du_w _ mm
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       Hspg Heffg Htmg Htrg Htr Heag Hea Hwvg Hwv Htwvg Htwv)
            | vm_compute; reflexivity
            | exact (u_tlb_only_land rs rs1 Hfile) | exact Htlb1 | exact Hst1w ].
      + (* the FIRST page faults *)
        destruct (u_fault_pair t mm rs (Store Data) (E_SAMO_Page_Fault tt) va
                    (or_intror (or_intror (or_introl eq_refl)))
                    (proj1 (u_texc_store (u_state rs mm)))
                    (proj1 (proj2 (u_texc_store (u_state rs mm))))
                    (proj2 (proj2 (u_texc_store (u_state rs mm))))
                    Hf1 Hcfg Hpins Hwf) as (Htr & Htrg & Hme & Hmeg).
        right. exists rs, mm, t, (E_SAMO_Page_Fault tt), va, (register_lookup PC rs).
        split_and!;
          [ exact (exec_vmem_write_addr_split2_err1 k pp (k - pp) va dat
                     User Sv39 (u_state rs mm) (u_state rs mm)
                     (conj Hp0 Hq0) Hsp Hpm Heff Htm
                     ltac:(vm_compute; reflexivity) (E_SAMO_Page_Fault tt) _ Htr Hme)
          | exact (goodmb_vmem_write_addr_split2_err1 k pp (k - pp) va dat
                     User Sv39 (u_state rs mm) (u_state rs mm)
                     (conj Hp0 Hq0) Hsp Hpm Heff Htm
                     ltac:(vm_compute; reflexivity) Du_r Du_w (E_SAMO_Page_Fault tt)
                     _ mm ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity) Hspg Heffg Htmg Htrg Htr Hmeg Hme)
          | vm_compute; reflexivity
          | exact (u_tlb_only_refl rs) | exact Htlb0
          | exact (u_mem_step_refl pt t mm Hwf) ].
  Qed.

  Lemma arm_STORE_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (imm : bits 12) (rs2 rs1 : regidx) (width : word_width) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (STORE (imm, rs2, rs1, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (STORE (imm, rs2, rs1, width)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hpfc Hag Hwid Hdec Hhv Hpins Hwf.
    destruct rs2 as [ir2]. destruct rs1 as [ir1].
    assert (Hk : 0 < width) by (destruct Hwid as [-> | [-> | [-> | ->]]]; lia).
    assert (Hk8 : width <= 8) by (destruct Hwid as [-> | [-> | [-> | ->]]]; lia).
    assert (Hwok : (width <=? xlen_bytes) = true)
      by (destruct Hwid as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity).
    pose proof (u_data_cfg_tick rsf va 4
                  (u_data_cfg_of_post_fetch rsf mm va mi Hpfc)) as Hcfg.
    pose proof (u_pins_tick pt t rsf va 4 Hpins) as Hpins'.
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    assert (Heff : exec (effectivePrivilege (Store Data)
                     (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                     (s0 rsf mm va) = Some (User, s0 rsf mm va))
      by exact (exec_effectivePrivilege_mprv0 (Store Data) _ User (s0 rsf mm va) Lmprv).
    assert (Heffg : goodmb Du_r Du_w (effectivePrivilege (Store Data)
                      (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                      (s0 rsf mm va) mm = true)
      by exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Store Data) _ User
                  (s0 rsf mm va) mm Lmprv).
    destruct (u_pmlen_pure t mm mm (s0r rsf va) (Store Data)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hcfg Hpins') as (Hpml & Hpmlg).
    pose proof (u_translationMode_pure pt t (s0r rsf va) mm Hcfg Hpins') as Htm.
    pose proof (u_goodmb_translationMode_pure pt t (s0r rsf va) mm mm Hcfg Hpins')
      as Htmg.
    destruct (u_vmem_write_pure t mm (s0r rsf va) width
                (add_vec (if Z.eqb (uint ir1) 0 then zero_reg
                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint ir1)))
                                 (s0 rsf mm va).(sregs))
                         (sign_extend' 64 imm))
                (autocast (T := mword) (subrange_vec_dec
                   (if Z.eqb (uint ir2) 0 then zero_reg
                    else register_lookup (R_bitvector_64 (gpr_of_Z (uint ir2)))
                           (s0r rsf va))
                   (Z.sub (Z.mul width 8) 1) 0))
                Hk Hk8 Hcfg Hpins' Hwf)
      as [ (b & rs' & mm' & t' & Hvw & Hvwg & Honly & Htlbok & Hstep)
         | (rs' & mm' & t' & e & xv & pcx & Hvw & Hvwg & Hue & Honly & Htlbok & Hstep) ].
    - apply (arm_store_retire t t' mm mm' rsf rs' va w imm ir2 ir1 width b
               Hdec Hhv Hwok);
        [ exact (exec_vmem_write_u ir1 (sign_extend' 64 imm) width _ (Store Data)
                   false false false Sv39 (Ok b) (s0 rsf mm va) (u_state rs' mm')
                   Lcp Heff Hpml Htm Hvw)
        | exact (goodmb_vmem_write_u Du_r Du_w ir1 (sign_extend' 64 imm) width _
                   (Store Data) false false false Sv39 (Ok b)
                   (s0 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvw Hvwg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
    - apply (arm_store_trap t t' mm mm' rsf rs' va w imm ir2 ir1 width e xv pcx
               Hdec Hhv Hwok Hue);
        [ exact (exec_vmem_write_u ir1 (sign_extend' 64 imm) width _ (Store Data)
                   false false false Sv39 (Err _) (s0 rsf mm va) (u_state rs' mm')
                   Lcp Heff Hpml Htm Hvw)
        | exact (goodmb_vmem_write_u Du_r Du_w ir1 (sign_extend' 64 imm) width _
                   (Store Data) false false false Sv39 (Err _)
                   (s0 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvw Hvwg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
  Qed.

End UserMemArmsBase.
