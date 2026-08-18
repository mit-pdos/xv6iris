(* ====================================================================== *)
(* UserMemArmsC.v -- the THIRTEEN COMPRESSED memory arms.                  *)
(*                                                                        *)
(* Package P4b, the second half of [UserTotalU]'s frozen nineteen.  Every  *)
(* compressed memory instruction's [execute] is a single [returnm] of an   *)
(* [ExecuteAs (LOAD ...)] / [ExecuteAs (STORE ...)] -- the whole family    *)
(* EXPANDS to the base form and only then touches memory.  So the thirteen *)
(* arms are not thirteen case trees: they are two engines                  *)
(* ([arm_c_load_u] / [arm_c_store_u]) at an arbitrary width and an         *)
(* arbitrary pair of register operands, plus thirteen one-line             *)
(* instantiations that say which expansion the instruction makes.          *)
(*                                                                        *)
(* THE ONLY DIFFERENCE FROM [UserMemArmsBase]'s [arm_LOAD_u] /             *)
(* [arm_STORE_u] IS THE TICK AND THE CLOSER: the execute runs at [va+2]    *)
(* rather than [va+4], and it closes [UserClassifyAsm.rvc_post] through    *)
(* [UserMemTotal.finish_mem_rvc] (which carries the [Ext_Zca] gate and the *)
(* [ExecuteAs] redirect) rather than [finish_mem_base].  The ACCESS half   *)
(* -- [u_vmem_read_pure] / [u_vmem_write_pure], the trichotomy over        *)
(* [in_one_page_dec] x [data_classify] -- is tick-agnostic and is reused   *)
(* verbatim: it only ever sees the ticked file as an opaque [regstate].    *)
(* That is why the two engines below are short.                           *)
(*                                                                        *)
(* THE REDIRECT'S OWN STEP IS FREE.  [finish_mem_rvc] asks for a [goodmb]  *)
(* certificate on [execute ci] as well as on [execute other]; [execute ci] *)
(* is a [returnm], so its certificate is [reflexivity] and the thirteen    *)
(* [goodmb_execute_C_*_U] twins below are one line each.                   *)
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
Require Import UserTotalU UserMemTotal UserMemClassify UserMemArmsBase.
Local Open Scope Z_scope.
Import Defs.

Require Import WpDecodeBridge DecodeTotalU PtWalkCert UserFetchCert.
Require Import UserMemCert UserFaultCert MemAccessGen UserTranslate CommonWalk.
Set Printing Depth 40.

(* ---------------------------------------------------------------------- *)
(* 0. THE THIRTEEN EXPANSIONS, AND THEIR CERTIFICATES.                     *)
(*                                                                        *)
(* Each is the model's own [execute] on the compressed constructor, which  *)
(* is a [returnm] of the base instruction it expands to.  The [exec] half  *)
(* is [exec_returnm]; the [goodmb] half is [reflexivity] -- a [returnm]    *)
(* reads nothing, so no footprint obligation arises.                       *)
(* ---------------------------------------------------------------------- *)

Lemma exec_execute_C_LBU_U (uimm : mword 2) (rdc rsc1 : cregidx) (s : mstate) :
  exec (execute (C_LBU (uimm, rdc, rsc1))) s
    = Some (ExecuteAs (LOAD (zero_extend' 12 uimm, creg2reg_idx rsc1,
                             creg2reg_idx rdc, true, 1)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_LBU_U (Dr Dw : register -> bool)
    (uimm : mword 2) (rdc rsc1 : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_LBU (uimm, rdc, rsc1))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_LH_U (uimm : mword 2) (rdc rsc1 : cregidx) (s : mstate) :
  exec (execute (C_LH (uimm, rdc, rsc1))) s
    = Some (ExecuteAs (LOAD (zero_extend' 12 uimm, creg2reg_idx rsc1,
                             creg2reg_idx rdc, false, 2)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_LH_U (Dr Dw : register -> bool)
    (uimm : mword 2) (rdc rsc1 : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_LH (uimm, rdc, rsc1))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_LHU_U (uimm : mword 2) (a b : cregidx) (s : mstate) :
  exec (execute (C_LHU (uimm, a, b))) s
    = Some (ExecuteAs (LOAD (zero_extend' 12 uimm, creg2reg_idx b,
                             creg2reg_idx a, true, 2)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_LHU_U (Dr Dw : register -> bool)
    (uimm : mword 2) (a b : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_LHU (uimm, a, b))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_LW_U (uimm : mword 5) (a b : cregidx) (s : mstate) :
  exec (execute (C_LW (uimm, a, b))) s
    = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")),
                             creg2reg_idx a, creg2reg_idx b, false, 4)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_LW_U (Dr Dw : register -> bool)
    (uimm : mword 5) (a b : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_LW (uimm, a, b))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_LD_U (uimm : mword 5) (a b : cregidx) (s : mstate) :
  exec (execute (C_LD (uimm, a, b))) s
    = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                             creg2reg_idx a, creg2reg_idx b, false, 8)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_LD_U (Dr Dw : register -> bool)
    (uimm : mword 5) (a b : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_LD (uimm, a, b))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_LWSP_U (uimm : mword 6) (rd : regidx) (s : mstate) :
  exec (execute (C_LWSP (uimm, rd))) s
    = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")),
                             sp, rd, false, 4)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_LWSP_U (Dr Dw : register -> bool)
    (uimm : mword 6) (rd : regidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_LWSP (uimm, rd))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_LDSP_U (uimm : mword 6) (rd : regidx) (s : mstate) :
  exec (execute (C_LDSP (uimm, rd))) s
    = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                             sp, rd, false, 8)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_LDSP_U (Dr Dw : register -> bool)
    (uimm : mword 6) (rd : regidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_LDSP (uimm, rd))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_SB_U (uimm : mword 2) (rsc1 rsc2 : cregidx) (s : mstate) :
  exec (execute (C_SB (uimm, rsc1, rsc2))) s
    = Some (ExecuteAs (STORE (zero_extend' 12 uimm, creg2reg_idx rsc2,
                              creg2reg_idx rsc1, 1)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_SB_U (Dr Dw : register -> bool)
    (uimm : mword 2) (rsc1 rsc2 : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_SB (uimm, rsc1, rsc2))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_SH_U (uimm : mword 2) (a b : cregidx) (s : mstate) :
  exec (execute (C_SH (uimm, a, b))) s
    = Some (ExecuteAs (STORE (zero_extend' 12 uimm, creg2reg_idx b,
                              creg2reg_idx a, 2)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_SH_U (Dr Dw : register -> bool)
    (uimm : mword 2) (a b : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_SH (uimm, a, b))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_SW_U (uimm : mword 5) (a b : cregidx) (s : mstate) :
  exec (execute (C_SW (uimm, a, b))) s
    = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"00")),
                              creg2reg_idx b, creg2reg_idx a, 4)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_SW_U (Dr Dw : register -> bool)
    (uimm : mword 5) (a b : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_SW (uimm, a, b))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_SD_U (uimm : mword 5) (a b : cregidx) (s : mstate) :
  exec (execute (C_SD (uimm, a, b))) s
    = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                              creg2reg_idx b, creg2reg_idx a, 8)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_SD_U (Dr Dw : register -> bool)
    (uimm : mword 5) (a b : cregidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_SD (uimm, a, b))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_SWSP_U (uimm : mword 6) (rs2 : regidx) (s : mstate) :
  exec (execute (C_SWSP (uimm, rs2))) s
    = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"00")),
                              rs2, sp, 4)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_SWSP_U (Dr Dw : register -> bool)
    (uimm : mword 6) (rs2 : regidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_SWSP (uimm, rs2))) s mm = true.
Proof. reflexivity. Qed.

Lemma exec_execute_C_SDSP_U (uimm : mword 6) (rs2 : regidx) (s : mstate) :
  exec (execute (C_SDSP (uimm, rs2))) s
    = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                              rs2, sp, 8)), s).
Proof. apply exec_returnm. Qed.

Lemma goodmb_execute_C_SDSP_U (Dr Dw : register -> bool)
    (uimm : mword 6) (rs2 : regidx) (s : mstate) (mm : PtBytes.pamap) :
  goodmb Dr Dw (execute (C_SDSP (uimm, rs2))) s mm = true.
Proof. reflexivity. Qed.

Section UserMemArmsC.
  Context (pt : uptd).

  (* the compressed tick, spelled exactly as [rvc_post] spells it *)
  Local Notation s2r rsf va := (register_set nextPC (add_vec_int va 2) rsf).
  Local Notation s2 rsf mm va :=
    (u_state (register_set nextPC (add_vec_int va 2) rsf) mm).

  (* ------------------------------------------------------------------- *)
  (* 1. THE FOUR RVC EXECUTE-LEVEL CLOSERS.                               *)
  (*                                                                     *)
  (* [UserMemArmsBase]'s four, with [finish_mem_base] replaced by         *)
  (* [finish_mem_rvc] and the tick moved to [va+2].  The expansion is a   *)
  (* hypothesis ([Hfwd]) rather than a case split: only the caller knows  *)
  (* which base instruction its compressed opcode expands to.            *)
  (* ------------------------------------------------------------------- *)

  Lemma arm_c_load_retire (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (h : mword 16) (ci : instruction)
      (imm : mword 12) (rs1 rd : mword 5) (us : bool) (width : Z)
      (data : mword (8 * width)) :
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (ci, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) ci rsf ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm)
      = Some (true, u_state rsf mm) ->
    (forall st : mstate, exec (execute ci) st
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, us, width)), st)) ->
    (forall (st : mstate) (mm0 : PtBytes.pamap),
       goodmb Du_r Du_w (execute ci) st mm0 = true) ->
    (width <=? xlen_bytes) = true ->
    exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data)
            false false false) (s2 rsf mm va)
      = Some (Ok data, u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_read (Regidx rs1) (sign_extend' 64 imm) width
            (Load Data) false false false) (s2 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s2r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hdec Hhv Hzca Hfwd Hfwdg Hwok Hvr Hvg Hland Htlb Hst.
    apply (finish_mem_rvc pt t t' mm rsf va ci
             (LOAD (imm, Regidx rs1, Regidx rd, us, width)) RETIRE_SUCCESS h
             (gpr_write_state rd (extend_value us data) (u_state rs' mm'))
             Hdec Hhv Hzca (Hfwd (s2 rsf mm va)) (Hfwdg (s2 rsf mm va) mm)).
    - exact (exec_execute_LOAD_u_retire imm rs1 rd us width data
               (s2 rsf mm va) (u_state rs' mm') Hwok Hvr).
    - exact (goodmb_execute_LOAD_u_retire Du_r Du_w imm rs1 rd us width data
               (s2 rsf mm va) (u_state rs' mm') mm (Du_gpr_of_Z rd) Hwok Hvr Hvg).
    - exact u_ok_retire.
    - exact I.
    - eapply u_fix_trans; [ apply u_fix_gpr_state | ].
      rewrite u_state_sregs. exact Hland.
    - rewrite u_tlb_gpr u_state_sregs. exact Htlb.
    - rewrite u_mem_gpr u_state_mem. exact Hst.
  Qed.

  Lemma arm_c_load_trap (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (h : mword 16) (ci : instruction)
      (imm : mword 12) (rs1 rd : mword 5) (us : bool) (width : Z)
      (e : ExceptionType) (xv pcx : mword 64) :
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (ci, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) ci rsf ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm)
      = Some (true, u_state rsf mm) ->
    (forall st : mstate, exec (execute ci) st
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, us, width)), st)) ->
    (forall (st : mstate) (mm0 : PtBytes.pamap),
       goodmb Du_r Du_w (execute ci) st mm0 = true) ->
    (width <=? xlen_bytes) = true ->
    user_exc e = true ->
    exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data)
            false false false) (s2 rsf mm va)
      = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
              u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_read (Regidx rs1) (sign_extend' 64 imm) width
            (Load Data) false false false) (s2 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s2r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hdec Hhv Hzca Hfwd Hfwdg Hwok Hue Hvr Hvg Hland Htlb Hst.
    apply (finish_mem_rvc pt t t' mm rsf va ci
             (LOAD (imm, Regidx rs1, Regidx rd, us, width))
             (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) h
             (u_state rs' mm')
             Hdec Hhv Hzca (Hfwd (s2 rsf mm va)) (Hfwdg (s2 rsf mm va) mm)).
    - exact (exec_execute_LOAD_u_err imm rs1 rd us width _
               (s2 rsf mm va) (u_state rs' mm') Hwok Hvr).
    - exact (goodmb_execute_LOAD_u_err Du_r Du_w imm rs1 rd us width _
               (s2 rsf mm va) (u_state rs' mm') mm Hwok Hvr Hvg).
    - exact (u_ok_trap e xv pcx Hue).
    - exact I.
    - rewrite u_state_sregs. exact Hland.
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

  Lemma arm_c_store_retire (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (h : mword 16) (ci : instruction)
      (imm : mword 12) (rs2 rs1 : mword 5) (width : Z) (b : bool) :
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (ci, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) ci rsf ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm)
      = Some (true, u_state rsf mm) ->
    (forall st : mstate, exec (execute ci) st
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, width)), st)) ->
    (forall (st : mstate) (mm0 : PtBytes.pamap),
       goodmb Du_r Du_w (execute ci) st mm0 = true) ->
    (width <=? xlen_bytes) = true ->
    exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s2r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (Store Data) false false false) (s2 rsf mm va)
      = Some (Ok b, u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s2r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (Store Data) false false false) (s2 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s2r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hdec Hhv Hzca Hfwd Hfwdg Hwok Hvw Hvg Hland Htlb Hst.
    apply (finish_mem_rvc pt t t' mm rsf va ci
             (STORE (imm, Regidx rs2, Regidx rs1, width)) RETIRE_SUCCESS h
             (u_state rs' mm')
             Hdec Hhv Hzca (Hfwd (s2 rsf mm va)) (Hfwdg (s2 rsf mm va) mm)).
    - exact (exec_execute_STORE_u_ok imm rs2 rs1 width b
               (s2 rsf mm va) (u_state rs' mm') Hwok Hvw).
    - exact (goodmb_execute_STORE_u_ok Du_r Du_w imm rs2 rs1 width b
               (s2 rsf mm va) (u_state rs' mm') mm
               (fun H => Du_gpr_of_Z_r rs2 H) Hwok Hvw Hvg).
    - exact u_ok_retire.
    - exact I.
    - rewrite u_state_sregs. exact Hland.
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

  Lemma arm_c_store_trap (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (h : mword 16) (ci : instruction)
      (imm : mword 12) (rs2 rs1 : mword 5) (width : Z)
      (e : ExceptionType) (xv pcx : mword 64) :
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (ci, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) ci rsf ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm)
      = Some (true, u_state rsf mm) ->
    (forall st : mstate, exec (execute ci) st
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, width)), st)) ->
    (forall (st : mstate) (mm0 : PtBytes.pamap),
       goodmb Du_r Du_w (execute ci) st mm0 = true) ->
    (width <=? xlen_bytes) = true ->
    user_exc e = true ->
    exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s2r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (Store Data) false false false) (s2 rsf mm va)
      = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
              u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_write (Regidx rs1) (sign_extend' 64 imm) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s2r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (Store Data) false false false) (s2 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s2r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hdec Hhv Hzca Hfwd Hfwdg Hwok Hue Hvw Hvg Hland Htlb Hst.
    apply (finish_mem_rvc pt t t' mm rsf va ci
             (STORE (imm, Regidx rs2, Regidx rs1, width))
             (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) h
             (u_state rs' mm')
             Hdec Hhv Hzca (Hfwd (s2 rsf mm va)) (Hfwdg (s2 rsf mm va) mm)).
    - exact (exec_execute_STORE_u_err imm rs2 rs1 width _
               (s2 rsf mm va) (u_state rs' mm') Hwok Hvw).
    - exact (goodmb_execute_STORE_u_err Du_r Du_w imm rs2 rs1 width _
               (s2 rsf mm va) (u_state rs' mm') mm
               (fun H => Du_gpr_of_Z_r rs2 H) Hwok Hvw Hvg).
    - exact (u_ok_trap e xv pcx Hue).
    - exact I.
    - rewrite u_state_sregs. exact Hland.
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 2. THE TWO ENGINES.                                                  *)
  (*                                                                     *)
  (* [arm_LOAD_u] / [arm_STORE_u]'s bodies at the compressed tick.  The   *)
  (* access half is [u_vmem_read_pure] / [u_vmem_write_pure] verbatim --  *)
  (* they take the ticked file as an opaque [regstate], so nothing about  *)
  (* the trichotomy has to be restated at [va+2].                        *)
  (* ------------------------------------------------------------------- *)

  Lemma arm_c_load_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (ci : instruction)
      (imm : mword 12) (rs1 rd : mword 5) (us : bool) (width : Z) :
    0 < width -> width <= 8 -> (width <=? xlen_bytes) = true ->
    (forall st : mstate, exec (execute ci) st
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, us, width)), st)) ->
    (forall (st : mstate) (mm0 : PtBytes.pamap),
       goodmb Du_r Du_w (execute ci) st mm0 = true) ->
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (ci, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) ci rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hk Hk8 Hwok Hfwd Hfwdg Hpfc Hag Hdec Hhv Hpins Hwf.
    (* the [Ext_Zca] gate rides [u_exec_pins]' misa pin, not [post_fetch_cfg]
       (which does not carry misa at all) *)
    pose proof (s0_zca (u_state rsf mm) (proj1 (proj1 Hpins))) as Hzca.
    pose proof (u_data_cfg_tick rsf va 2
                  (u_data_cfg_of_post_fetch rsf mm va mi Hpfc)) as Hcfg.
    pose proof (u_pins_tick pt t rsf va 2 Hpins) as Hpins'.
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    assert (Heff : exec (effectivePrivilege (Load Data)
                     (register_lookup mstatus (s2 rsf mm va).(sregs)) User)
                     (s2 rsf mm va) = Some (User, s2 rsf mm va))
      by exact (exec_effectivePrivilege_mprv0 (Load Data) _ User (s2 rsf mm va) Lmprv).
    assert (Heffg : goodmb Du_r Du_w (effectivePrivilege (Load Data)
                      (register_lookup mstatus (s2 rsf mm va).(sregs)) User)
                      (s2 rsf mm va) mm = true)
      by exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Load Data) _ User
                  (s2 rsf mm va) mm Lmprv).
    destruct (u_pmlen_pure pt t mm mm (s2r rsf va) (Load Data)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hcfg Hpins') as (Hpml & Hpmlg).
    pose proof (u_translationMode_pure pt t (s2r rsf va) mm Hcfg Hpins') as Htm.
    pose proof (u_goodmb_translationMode_pure pt t (s2r rsf va) mm mm Hcfg Hpins')
      as Htmg.
    destruct (u_vmem_read_pure pt t mm (s2r rsf va) width
                (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                                 (s2 rsf mm va).(sregs))
                         (sign_extend' 64 imm))
                Hk Hk8 Hcfg Hpins' Hwf)
      as [ (dv & rs' & mm' & t' & Hvr & Hvrg & Honly & Htlbok & Hstep)
         | (rs' & mm' & t' & e & xv & pcx & Hvr & Hvrg & Hue & Honly & Htlbok & Hstep) ].
    - apply (arm_c_load_retire t t' mm mm' rsf rs' va h ci imm rs1 rd us
               width dv Hdec Hhv Hzca Hfwd Hfwdg Hwok);
        [ exact (exec_vmem_read_u rs1 (sign_extend' 64 imm) width (Load Data)
                   false false false Sv39 (Ok dv) (s2 rsf mm va) (u_state rs' mm')
                   Lcp Heff Hpml Htm Hvr)
        | exact (goodmb_vmem_read_u Du_r Du_w rs1 (sign_extend' 64 imm) width
                   (Load Data) false false false Sv39 (Ok dv)
                   (s2 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r rs1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvr Hvrg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
    - apply (arm_c_load_trap t t' mm mm' rsf rs' va h ci imm rs1 rd us
               width e xv pcx Hdec Hhv Hzca Hfwd Hfwdg Hwok Hue);
        [ exact (exec_vmem_read_u rs1 (sign_extend' 64 imm) width (Load Data)
                   false false false Sv39 (Err _) (s2 rsf mm va) (u_state rs' mm')
                   Lcp Heff Hpml Htm Hvr)
        | exact (goodmb_vmem_read_u Du_r Du_w rs1 (sign_extend' 64 imm) width
                   (Load Data) false false false Sv39 (Err _)
                   (s2 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r rs1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvr Hvrg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
  Qed.

  Lemma arm_c_store_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (ci : instruction)
      (imm : mword 12) (rs2 rs1 : mword 5) (width : Z) :
    0 < width -> width <= 8 -> (width <=? xlen_bytes) = true ->
    (forall st : mstate, exec (execute ci) st
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, width)), st)) ->
    (forall (st : mstate) (mm0 : PtBytes.pamap),
       goodmb Du_r Du_w (execute ci) st mm0 = true) ->
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (ci, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) ci rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hk Hk8 Hwok Hfwd Hfwdg Hpfc Hag Hdec Hhv Hpins Hwf.
    (* the [Ext_Zca] gate rides [u_exec_pins]' misa pin, not [post_fetch_cfg]
       (which does not carry misa at all) *)
    pose proof (s0_zca (u_state rsf mm) (proj1 (proj1 Hpins))) as Hzca.
    pose proof (u_data_cfg_tick rsf va 2
                  (u_data_cfg_of_post_fetch rsf mm va mi Hpfc)) as Hcfg.
    pose proof (u_pins_tick pt t rsf va 2 Hpins) as Hpins'.
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    assert (Heff : exec (effectivePrivilege (Store Data)
                     (register_lookup mstatus (s2 rsf mm va).(sregs)) User)
                     (s2 rsf mm va) = Some (User, s2 rsf mm va))
      by exact (exec_effectivePrivilege_mprv0 (Store Data) _ User (s2 rsf mm va) Lmprv).
    assert (Heffg : goodmb Du_r Du_w (effectivePrivilege (Store Data)
                      (register_lookup mstatus (s2 rsf mm va).(sregs)) User)
                      (s2 rsf mm va) mm = true)
      by exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Store Data) _ User
                  (s2 rsf mm va) mm Lmprv).
    destruct (u_pmlen_pure pt t mm mm (s2r rsf va) (Store Data)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hcfg Hpins') as (Hpml & Hpmlg).
    pose proof (u_translationMode_pure pt t (s2r rsf va) mm Hcfg Hpins') as Htm.
    pose proof (u_goodmb_translationMode_pure pt t (s2r rsf va) mm mm Hcfg Hpins')
      as Htmg.
    destruct (u_vmem_write_pure pt t mm (s2r rsf va) width
                (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                                 (s2 rsf mm va).(sregs))
                         (sign_extend' 64 imm))
                (autocast (T := mword) (subrange_vec_dec
                   (if Z.eqb (uint rs2) 0 then zero_reg
                    else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                           (s2r rsf va))
                   (Z.sub (Z.mul width 8) 1) 0))
                Hk Hk8 Hcfg Hpins' Hwf)
      as [ (b & rs' & mm' & t' & Hvw & Hvwg & Honly & Htlbok & Hstep)
         | (rs' & mm' & t' & e & xv & pcx & Hvw & Hvwg & Hue & Honly & Htlbok & Hstep) ].
    - apply (arm_c_store_retire t t' mm mm' rsf rs' va h ci imm rs2 rs1 width b
               Hdec Hhv Hzca Hfwd Hfwdg Hwok);
        [ exact (exec_vmem_write_u rs1 (sign_extend' 64 imm) width _ (Store Data)
                   false false false Sv39 (Ok b) (s2 rsf mm va) (u_state rs' mm')
                   Lcp Heff Hpml Htm Hvw)
        | exact (goodmb_vmem_write_u Du_r Du_w rs1 (sign_extend' 64 imm) width _
                   (Store Data) false false false Sv39 (Ok b)
                   (s2 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r rs1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvw Hvwg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
    - apply (arm_c_store_trap t t' mm mm' rsf rs' va h ci imm rs2 rs1 width
               e xv pcx Hdec Hhv Hzca Hfwd Hfwdg Hwok Hue);
        [ exact (exec_vmem_write_u rs1 (sign_extend' 64 imm) width _ (Store Data)
                   false false false Sv39 (Err _) (s2 rsf mm va) (u_state rs' mm')
                   Lcp Heff Hpml Htm Hvw)
        | exact (goodmb_vmem_write_u Du_r Du_w rs1 (sign_extend' 64 imm) width _
                   (Store Data) false false false Sv39 (Err _)
                   (s2 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r rs1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvw Hvwg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
  Qed.


  (* ------------------------------------------------------------------- *)
  (* 3. THE THIRTEEN ARMS.                                                *)
  (*                                                                     *)
  (* One [exact] each: the compressed opcode names its expansion, the     *)
  (* engine does the rest.  The register operands are spelled as the      *)
  (* [mword 5] payloads [creg2reg_idx] / [sp] reduce to, which is what    *)
  (* makes [Regidx rs1] in the engine's statement and [creg2reg_idx rsc]  *)
  (* in the model's own expansion the SAME term.                         *)
  (* ------------------------------------------------------------------- *)

  Lemma arm_C_LBU_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LBU p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LBU p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm rdc] rsc1]. destruct rdc as [i0]. destruct rsc1 as [i1].
    exact (arm_c_load_u t mm rsf va mi h (C_LBU (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 uimm)
             (zero_extend' 5 (concat_vec ('b"1") i1))
             (zero_extend' 5 (concat_vec ('b"1") i0)) true 1
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_LBU_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_LBU_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_LH_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LH p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LH p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm rdc] rsc1]. destruct rdc as [i0]. destruct rsc1 as [i1].
    exact (arm_c_load_u t mm rsf va mi h (C_LH (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 uimm)
             (zero_extend' 5 (concat_vec ('b"1") i1))
             (zero_extend' 5 (concat_vec ('b"1") i0)) false 2
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_LH_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_LH_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_LHU_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LHU p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LHU p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm a] b]. destruct a as [i0]. destruct b as [i1].
    exact (arm_c_load_u t mm rsf va mi h (C_LHU (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 uimm)
             (zero_extend' 5 (concat_vec ('b"1") i1))
             (zero_extend' 5 (concat_vec ('b"1") i0)) true 2
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_LHU_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_LHU_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_LW_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 5 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LW p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LW p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm a] b]. destruct a as [i0]. destruct b as [i1].
    exact (arm_c_load_u t mm rsf va mi h (C_LW (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 (concat_vec uimm ('b"00")))
             (zero_extend' 5 (concat_vec ('b"1") i0))
             (zero_extend' 5 (concat_vec ('b"1") i1)) false 4
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_LW_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_LW_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_LD_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 5 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LD p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LD p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm a] b]. destruct a as [i0]. destruct b as [i1].
    exact (arm_c_load_u t mm rsf va mi h (C_LD (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 (concat_vec uimm ('b"000")))
             (zero_extend' 5 (concat_vec ('b"1") i0))
             (zero_extend' 5 (concat_vec ('b"1") i1)) false 8
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_LD_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_LD_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_LWSP_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 6 * regidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LWSP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LWSP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [uimm rdr]. destruct rdr as [r].
    exact (arm_c_load_u t mm rsf va mi h (C_LWSP (uimm, Regidx r))
             (zero_extend' 12 (concat_vec uimm ('b"00")))
             (zero_extend' 5 ('b"10"))
             (r) false 4
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_LWSP_U uimm (Regidx r))
             (fun st mm0 => goodmb_execute_C_LWSP_U Du_r Du_w uimm (Regidx r) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_LDSP_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 6 * regidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LDSP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LDSP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [uimm rdr]. destruct rdr as [r].
    exact (arm_c_load_u t mm rsf va mi h (C_LDSP (uimm, Regidx r))
             (zero_extend' 12 (concat_vec uimm ('b"000")))
             (zero_extend' 5 ('b"10"))
             (r) false 8
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_LDSP_U uimm (Regidx r))
             (fun st mm0 => goodmb_execute_C_LDSP_U Du_r Du_w uimm (Regidx r) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_SB_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SB p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SB p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm rsc1] rsc2]. destruct rsc1 as [i0]. destruct rsc2 as [i1].
    exact (arm_c_store_u t mm rsf va mi h (C_SB (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 uimm)
             (zero_extend' 5 (concat_vec ('b"1") i1))
             (zero_extend' 5 (concat_vec ('b"1") i0)) 1
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_SB_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_SB_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_SH_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SH p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SH p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm a] b]. destruct a as [i0]. destruct b as [i1].
    exact (arm_c_store_u t mm rsf va mi h (C_SH (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 uimm)
             (zero_extend' 5 (concat_vec ('b"1") i1))
             (zero_extend' 5 (concat_vec ('b"1") i0)) 2
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_SH_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_SH_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_SW_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 5 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SW p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SW p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm a] b]. destruct a as [i0]. destruct b as [i1].
    exact (arm_c_store_u t mm rsf va mi h (C_SW (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 (concat_vec uimm ('b"00")))
             (zero_extend' 5 (concat_vec ('b"1") i1))
             (zero_extend' 5 (concat_vec ('b"1") i0)) 4
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_SW_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_SW_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_SD_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 5 * cregidx * cregidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SD p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SD p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [[uimm a] b]. destruct a as [i0]. destruct b as [i1].
    exact (arm_c_store_u t mm rsf va mi h (C_SD (uimm, Cregidx i0, Cregidx i1))
             (zero_extend' 12 (concat_vec uimm ('b"000")))
             (zero_extend' 5 (concat_vec ('b"1") i1))
             (zero_extend' 5 (concat_vec ('b"1") i0)) 8
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_SD_U uimm (Cregidx i0) (Cregidx i1))
             (fun st mm0 => goodmb_execute_C_SD_U Du_r Du_w uimm (Cregidx i0) (Cregidx i1) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_SWSP_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 6 * regidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SWSP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SWSP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [uimm r2]. destruct r2 as [r].
    exact (arm_c_store_u t mm rsf va mi h (C_SWSP (uimm, Regidx r))
             (zero_extend' 12 (concat_vec uimm ('b"00")))
             (r)
             (zero_extend' 5 ('b"10")) 4
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_SWSP_U uimm (Regidx r))
             (fun st mm0 => goodmb_execute_C_SWSP_U Du_r Du_w uimm (Regidx r) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

  Lemma arm_C_SDSP_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 6 * regidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SDSP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SDSP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hpfc Hag Hdec Hhv Hpins Hwf.
    destruct p as [uimm r2]. destruct r2 as [r].
    exact (arm_c_store_u t mm rsf va mi h (C_SDSP (uimm, Regidx r))
             (zero_extend' 12 (concat_vec uimm ('b"000")))
             (r)
             (zero_extend' 5 ('b"10")) 8
             ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
             (exec_execute_C_SDSP_U uimm (Regidx r))
             (fun st mm0 => goodmb_execute_C_SDSP_U Du_r Du_w uimm (Regidx r) st mm0)
             Hpfc Hag Hdec Hhv Hpins Hwf).
  Qed.

End UserMemArmsC.
