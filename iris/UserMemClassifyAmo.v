(* ===================================================================== *)
(* UserMemClassifyAmo.v -- the ATOMIC half of the U-mode memory-family     *)
(* execute totalities: the AMO leaves / composers / engines (widths        *)
(* {1,2,4,8} and the AMOCAS.Q width 16), and the ZICBOP prefetch arm.      *)
(*                                                                         *)
(* Split out of UserMemClassify.v, which carries everything below the      *)
(* atomics (the plain load/store pipeline, the misaligned pipeline and the *)
(* LR/SC stacks) and is this file's only project-local prerequisite.       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import RegFile PtAdBits.
Require Import WpGpr UserBits.
Require Import SmodeCore.
Require Import UptTree UserPtTree UserExec UserCompute.
Require Import UserMemArms WpMmodeLeafBase.
Require Import WpGprCsrwC.
Require Import UserMemAccess UserMemPt.
Require Import UserTotalU.
Require Import RiscvModelBytes CommonWalk MemAmo4.
Require Import UserMemClassify UserMemTotal.
Require Import UserClassifyAsm UserBytes HartMemRun HartMemAsm PtBytes UserFrame.
Local Open Scope Z_scope.
Import Defs.

(* A failing tactic at this altitude otherwise prints a goal that takes tens
   of minutes to format -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

(* ===================================================================== *)
(* op/width/aq-rl-generic AMO memory leaves (Atomic acc, RAM).            *)
(* ===================================================================== *)

(* ===================================================================== *)
(* Translate-fault composer at the Atomic acc (width-generic).            *)
(* ===================================================================== *)

(* ===================================================================== *)
(* The width-generic AMO execute engine (k in {1,2,4,8}).                 *)
(* ===================================================================== *)

(* ===================================================================== *)
(* Width-16 (AMOCAS) read-deny trap: the width>xlen (rX_pair) branch.     *)
(* ===================================================================== *)
Lemma exec_rX_pair_bits_gpr (rs : mword 5) s :
  exists v : mword (64 * 2), exec (rX_pair_bits (Regidx rs)) s = Some (v, s).
Proof.
  unfold rX_pair_bits.
  destruct (generic_neq (Regidx rs) zreg) eqn:Hz.
  - eexists.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr (add_vec_int rs 1) s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs s)).
    apply exec_returnM.
  - eexists. apply exec_returnM.
Qed.

Lemma exec_execute_AMO_u_read_err_16
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type) (e : ExceptionType)
    (pc : mword 64) (md : SATPMode) (s s' : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s'
    = Some (Err (addr, e), s') ->
  (* the fault is AT the access base, which is what the model asserts here *)
  generic_eq addr addr = true ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
    = Some (Trap (User, make_sync_exception e
                    (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                             (zeros' 64)), pc), s').
Proof.
  intros Hcp Heff Hpml Htm Hcp' Hpc' Hal Htr Hea Hrdm Hgeq.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, aq, rl, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite execR_bind. rewrite execR_bind0. rewrite execR_returnR. cbn match.
  rewrite execR_liftR. rewrite Htr. cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  (* mem_read -> Err (addr, e): the model asserts the fault address is the
     access base, then early_returns the memory_exception trap *)
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  assert (Hae : execR (Defs.liftR (assert_exp (generic_eq addr addr)
                         "extensions/A/zaamo_insts.sail:110.31-110.32")
                       : Defs.monadR ExecutionResult exception unit) s'
                = Some (inr tt, s'))
    by (rewrite execR_liftR; unfold assert_exp; rewrite Hgeq; reflexivity).
  rewrite execR_bind. rewrite (execR_bind0_Some _ _ _ _ Hae).
  rewrite execR_liftR.
  rewrite (exec_memory_exception _ pc e User s' Hcp' Hpc'). cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* Width-generic AMO read DENY (op != AMOSWAP): mem_read = Err, no bytes.  *)
(* ===================================================================== *)

(* ===================================================================== *)
(* addr_is_ram at any data address (from udata_own), + width-16 deny.      *)
(* ===================================================================== *)

(* ===================================================================== *)
(* Width-16 support (the AMOCAS.Q width): every op RETIRES, through the    *)
(* 128-bit register-pair path (rX_pair / wX_pair).  Same two arms as the    *)
(* narrow widths -- store, or AMOCAS-mismatch -- with the pair reads given  *)
(* as premises (the caller gets them from exec_rX_pair_bits_gpr).           *)
(* ===================================================================== *)

(* 128-bit RAM read/write leaves (clones of the width-8 versions). *)
Lemma exec_read_ram_resv_kinds_16 (rk : rv64d_types.read_kind) (addr : mword 64) (w : bv 128) s :
  (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 16)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rk (Physaddr addr) 16 false) s = Some ((w, default_meta), s).
Proof.
  intros Hrk Hdev Hbytes.
  assert (Hrun : run (read_ram rk (Physaddr addr) 16 false) s (w, default_meta) s).
  { destruct Hrk as [ -> | [ -> | -> ] ];
      (unfold read_ram; cbn match;
       apply (proj2 (run_bind _ _ _ _ _));
       eexists _, s; split; [ apply run_returnM_fwd | ]; cbn beta zeta;
       apply (proj2 (run_bind _ _ _ _ _));
       unfold Defs.sail_mem_read; cbn beta zeta;
       eexists _, s; split;
       [ eapply run_MemRead_ram_intro;
         [ exact Hdev | intros j Hj; exact (Hbytes j Hj) | apply run_returnM_fwd ]
       | cbn match beta; apply run_returnM_fwd ]). }
  apply (run_to_exec _ _ _ _ Hrun).
  destruct Hrk as [ -> | [ -> | -> ] ];
    (unfold read_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     rewrite exec_MemRead; [| exact Hdev];
     cbn [Interface.ReadReq.pa];
     case_match eqn:Hrb;
     [ cbn [Interface.iMon_bind]; cbn match beta iota; discriminate
     | exfalso;
       refine (read_bytes_ne (mem s) addr (Z.to_N 16) w _ Hrb);
       intros j Hj;
       change (RiscvModelBytes.pa_add addr j) with (pa_add addr j);
       change (RiscvModelBytes.nth_byte w j) with (nth_byte w j);
       exact (Hbytes j Hj) ]).
Qed.

Lemma exec_write_ram_cond_kinds_16 (wk : rv64d_types.write_kind) (addr : mword 64) (data : bv 128) s :
  (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
  dev_addr addr = false ->
  exec (write_ram wk (Physaddr addr) 16 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 16 data) s.(mdev)).
Proof.
  intros Hwk Hdev. destruct Hwk as [ -> | [ -> | -> ] ];
    (unfold write_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     cbn [Mem_write_request_value]; cbn match; cbn [Interface.iMon_bind];
     rewrite exec_MemWrite; [ reflexivity | exact Hdev ]).
Qed.

(* rd = 0 bridge: relate the wX_pair zreg guard to the uint. *)
Lemma neq_rd_zreg_uint (rd : mword 5) :
  generic_neq (Regidx rd) zreg = true -> Z.eqb (uint rd) 0 = false.
Proof.
  intro Hz. apply generic_neq_true in Hz.
  apply Z.eqb_neq. intro E.
  apply Hz. unfold zreg. f_equal.
  apply bv_eq.
  replace (bv_unsigned (zero_extend' 5 ('b"00"))) with 0%Z by (vm_compute; reflexivity).
  rewrite <- (uint_unsigned_n 5 rd). exact E.
Qed.

(* wX_pair reduction: writes rd (low 64) and rd+1 (high 64) when rd<>0. *)
Definition wpair_state (rd : mword 5) (data : mword (64 * 2)) (s : mstate) : mstate :=
  if generic_neq (Regidx rd) zreg
  then
    let s1 := (if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (subrange_vec_dec data (Z.sub xlen 1) 0))) in
    (if Z.eqb (uint (add_vec_int rd 1)) 0 then s1
     else set_reg s1 (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1))))
            (regval_into_reg (subrange_vec_dec data (Z.sub (Z.mul xlen 2) 1) xlen)))
  else s.

Lemma exec_wX_pair_bits_gpr (rd : mword 5) (data : mword (64 * 2)) s :
  exec (wX_pair_bits (Regidx rd) data) s = Some (tt, wpair_state rd data s).
Proof.
  unfold wX_pair_bits, wpair_state.
  destruct (generic_neq (Regidx rd) zreg) eqn:Hz.
  - rewrite (exec_bind0_Some _ _ _ _ _
               (exec_wX_bits_gpr rd (subrange_vec_dec data (Z.sub xlen 1) 0) s)).
    change (regidx_offset_range (Regidx rd) 1) with (Regidx (add_vec_int rd 1)).
    apply exec_wX_bits_gpr.
  - apply exec_returnM.
Qed.

(* THE STORE ARM AT WIDTH 16, op-generic: rs2 via rX_pair, rd written via
   wX_pair.  [result'] is the model's per-op value at the pair-read operand. *)
Lemma exec_execute_AMO_u_store_16
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (rp rpd : mword (64 * 2)) (loaded : mword (8 * 16)) (md : SATPMode) (s s' s'' : mstate) :
  let rs2_val : bits (16 * 8) := trunc (Z.mul (__id 16) 8) rp in
  let lc : bits (16 * 8) := autocast (T := mword) loaded in
  let result' : bits (16 * 8) :=
    match op with
    | AMOSWAP => rs2_val | AMOADD => add_vec rs2_val lc | AMOXOR => xor_vec rs2_val lc
    | AMOAND => and_vec rs2_val lc | AMOOR => or_vec rs2_val lc
    | AMOMIN => if zopz0zI_s rs2_val lc then rs2_val else lc
    | AMOMAX => if zopz0zK_s rs2_val lc then rs2_val else lc
    | AMOMINU => if zopz0zI_u rs2_val lc then rs2_val else lc
    | AMOMAXU => if zopz0zK_u rs2_val lc then rs2_val else lc
    | AMOCAS => rs2_val end in
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (rX_pair_bits (Regidx rs2)) s' = Some (rp, s') ->
  exec (rX_pair_bits (Regidx rd)) s' = Some (rpd, s') ->
  andb (generic_eq op AMOCAS) (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd)) = false ->
  exec (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  exec (mem_write_value addr 16
          (sign_extend' (Z.mul 8 (__id 16)) result')
          (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s' = Some (Ok true, s'') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s'').
Proof.
  intros rs2_val lc result'.
  intros Hcp Heff Hpml Htm Hal Htr Hrp Hrpd Hguard Hea Hrdm Hwv.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, aq, rl, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite execR_bind. rewrite execR_bind0. rewrite execR_returnR. cbn match.
  rewrite execR_liftR. rewrite Htr. cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  (* upstream reordered the body: the effective-address announcement and the
     load now run BEFORE rs2 is read *)
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite execR_returnR_fwd. cbn match zeta.
  replace (Z.leb 16 xlen_bytes) with false by (vm_compute; reflexivity).
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s'
               = Some (inr (trunc (Z.mul (__id 16) 8) rp), s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ Hrp). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  (* THE CAS GUARD at the pair width -- see UserMemArms for the shape. *)
  match goal with |- context[and_boolM ?A ?B] =>
    assert (Hab : execR (and_boolM A B) s'
                  = Some (inr (andb (generic_eq op AMOCAS)
                                 (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd))), s')) end.
  { assert (Hrdt : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rd)))
                     (fun w16 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w16))) s'
                 = Some (inr (trunc (Z.mul (__id 16) 8) rpd), s')).
    { rewrite (execR_liftR_seq _ _ _ _ _ Hrpd). apply execR_returnR_fwd. }
    unfold and_boolM.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (generic_eq op AMOCAS) s')).
    destruct (generic_eq op AMOCAS); cbn match; cbn [andb].
    - rewrite (execR_bind_Some _ _ _ _ _ Hrdt). apply execR_returnR_fwd.
    - first [ apply execR_returnR_fwd | reflexivity ]. }
  rewrite (execR_bind_Some _ _ _ _ _ Hab). rewrite Hguard. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match.
  assert (Hwxpr : execR (R := ExecutionResult)
                    (Defs.liftR (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))))) s''
                = Some (inr tt, wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s'')).
  { rewrite execR_liftR. rewrite exec_wX_pair_bits_gpr. reflexivity. }
  rewrite (execR_bind0_Some _ _ _ _ Hwxpr).
  rewrite execR_returnR_fwd. reflexivity.
Qed.
(* AMOCAS.Q, COMPARE MISMATCH: rd (the pair) := the loaded value, no store. *)
Lemma exec_execute_AMO_u_cas_ne_16
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (rp rpd : mword (64 * 2)) (loaded : mword (8 * 16)) (md : SATPMode) (s s' : mstate) :
  let lc : bits (16 * 8) := autocast (T := mword) loaded in
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (rX_pair_bits (Regidx rs2)) s' = Some (rp, s') ->
  exec (rX_pair_bits (Regidx rd)) s' = Some (rpd, s') ->
  andb (generic_eq op AMOCAS) (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd)) = true ->
  exec (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s').
Proof.
  intros lc.
  intros Hcp Heff Hpml Htm Hal Htr Hrp Hrpd Hguard Hea Hrdm.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, aq, rl, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite execR_bind. rewrite execR_bind0. rewrite execR_returnR. cbn match.
  rewrite execR_liftR. rewrite Htr. cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  (* upstream reordered the body: the effective-address announcement and the
     load now run BEFORE rs2 is read *)
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite execR_returnR_fwd. cbn match zeta.
  replace (Z.leb 16 xlen_bytes) with false by (vm_compute; reflexivity).
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s'
               = Some (inr (trunc (Z.mul (__id 16) 8) rp), s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ Hrp). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  match goal with |- context[and_boolM ?A ?B] =>
    assert (Hab : execR (and_boolM A B) s'
                  = Some (inr (andb (generic_eq op AMOCAS)
                                 (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd))), s')) end.
  { assert (Hrdt : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rd)))
                     (fun w16 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w16))) s'
                 = Some (inr (trunc (Z.mul (__id 16) 8) rpd), s')).
    { rewrite (execR_liftR_seq _ _ _ _ _ Hrpd). apply execR_returnR_fwd. }
    unfold and_boolM.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (generic_eq op AMOCAS) s')).
    destruct (generic_eq op AMOCAS); cbn match; cbn [andb].
    - rewrite (execR_bind_Some _ _ _ _ _ Hrdt). apply execR_returnR_fwd.
    - first [ apply execR_returnR_fwd | reflexivity ]. }
  rewrite (execR_bind_Some _ _ _ _ _ Hab). rewrite Hguard. cbn match.
  assert (Hwxpr : execR (R := ExecutionResult)
                    (Defs.liftR (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))))) s'
                = Some (inr tt, wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s')).
  { rewrite execR_liftR. rewrite exec_wX_pair_bits_gpr. reflexivity. }
  rewrite (execR_bind0_Some _ _ _ _ Hwxpr).
  rewrite execR_returnR_fwd. reflexivity.
Qed.


(* ===================================================================== *)
(* Width-16 AMO execute engine: AMOSWAP retires (128-bit, register pair), *)
(* every other op denies (mem_read Err) -> trap; misalign / walk-fault    *)
(* -> trap.  Mirrors mem_exec_amo_k but at the fixed wide width 16.        *)
(* ===================================================================== *)

(* ===================================================================== *)
(* arm_AMO_u : the AMO memory arm.  Widths {1,2,4,8} via mem_exec_amo_k    *)
(* (AMOSWAP retires, all other ops trap); width 16 via mem_exec_amo_16     *)
(* (AMOSWAP retires with a register-pair write, all other ops trap).       *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  arm_ZICBOP_u : the ZICBOP prefetch memory arm (19th memory arm).       *)
(*  execute_ZICBOP runs a CacheAccess(CB_prefetch) translateAddr and ALWAYS *)
(*  RETIRES (fault suppressed to nop-retire).  The CacheAccess leaf-check   *)
(*  equals the corresponding u_acc check (check_ca_eq), so upt_acc_wf       *)
(*  classifies it; the Ok branch's phys_access_check grants over the owned  *)
(*  RAM page; both outcomes reframe (finish-unchanged-shaped) to base_post. *)
(* ===================================================================== *)
Definition uacc_of (cbop : cbop_zicbop) : MemoryAccessType mem_payload :=
  match cbop with
  | PREFETCH_R => Load Data
  | PREFETCH_W => Store Data
  | PREFETCH_I => InstructionFetch tt
  end.

Lemma exec_is_shadow_stack_ca (cbop : cbop_zicbop) s :
  exec (is_shadow_stack_access (CacheAccess (CB_prefetch cbop))) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

(* ===================================================================== *)
(* THE SHADOW-STACK PTE, and why the CacheAccess/u_acc leaf checks agree.  *)
(*                                                                         *)
(* [check_PTE_permission] gained a branch for the SHADOW-STACK PTE encoding *)
(* (W set, R and X clear), and it is the ONE place where a prefetch and its *)
(* corresponding plain access disagree: with menvcfg.SSE enabled, a         *)
(* [Load Data] on such a PTE succeeds while [CacheAccess] is denied.  The   *)
(* branch's guard used to be unreachable -- the leading assert was          *)
(* [W -> R] -- but it is now [W -> (R \/ ~X)], which such a PTE satisfies.   *)
(*                                                                         *)
(* It stays unreachable HERE for a different reason: a PTE that both        *)
(* carries U and is shadow-stack-encoded has NO state-independent check     *)
(* result at all, because at menvcfg.SSE = 0 the branch's assert fails and  *)
(* [exec] is [None].  [pte_check_ok] / [pte_check_denied] are [forall s],   *)
(* so either of them RULES THE ENCODING OUT -- which is exactly the side    *)
(* condition [check_ca_eq] needs.                                          *)
(* ===================================================================== *)
Definition sspte (flags : mword 8) : bool :=
  andb (Riscv.rv64d.not (bit_to_bool (_get_PTE_Flags_R flags)))
       (andb (bit_to_bool (_get_PTE_Flags_W flags))
             (Riscv.rv64d.not (bit_to_bool (_get_PTE_Flags_X flags)))).

(* the witness state: any state with menvcfg cleared has SSE = 0 *)
Definition sse0 (s : mstate) : mstate :=
  MState (register_set menvcfg (zeros' 64 : mword 64) s.(sregs)) s.(mem) s.(mdev).

Lemma pte_check_no_sspte (acc : MemoryAccessType mem_payload) (mxr ds : bool)
    (w : mword 64) (r : PTE_Check) (s : mstate) :
  (forall s0, exec (check_PTE_permission acc User mxr ds
                      (Mk_PTE_Flags (subrange_vec_dec w 7 0)) (ext_bits_of_PTE w) tt) s0
              = Some (r, s0)) ->
  andb (bit_to_bool (_get_PTE_Flags_U (Mk_PTE_Flags (subrange_vec_dec w 7 0))))
       (sspte (Mk_PTE_Flags (subrange_vec_dec w 7 0))) = false.
Proof.
  intros H.
  destruct (bit_to_bool (_get_PTE_Flags_U (Mk_PTE_Flags (subrange_vec_dec w 7 0)))) eqn:EU;
    [ cbn [andb] | reflexivity ].
  destruct (sspte (Mk_PTE_Flags (subrange_vec_dec w 7 0))) eqn:E; [ exfalso | reflexivity ].
  unfold sspte in E.
  apply andb_true_iff in E. destruct E as (ER & E2).
  apply andb_true_iff in E2. destruct E2 as (EW & EX).
  apply negb_true_iff in ER. apply negb_true_iff in EX.
  assert (Hcalc : exec (check_PTE_permission acc User mxr ds
                          (Mk_PTE_Flags (subrange_vec_dec w 7 0)) (ext_bits_of_PTE w) tt) (sse0 s)
                  = None).
  { unfold check_PTE_permission.
    rewrite ER. rewrite EW. rewrite EX.
    cbn [Riscv.rv64d.not negb orb andb].
    replace (zopz0zJzJzK true true) with true by (vm_compute; reflexivity).
    unfold Defs.assert_exp. cbn match.
    rewrite exec_bind.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_returnm tt (sse0 s))).
    rewrite exec_returnm. rewrite EU. cbn match.
    { cbn [Riscv.rv64d.not negb]. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg (sse0 s))).
      unfold sse0. cbn [sregs].
      rewrite register_lookup_set.
      replace (bool_bit_backwards (_get_MEnvcfg_SSE (zeros' 64 : mword 64))) with false
        by (vm_compute; reflexivity).
      unfold Defs.assert_exp. cbn match.
      rewrite exec_bind. rewrite exec_bind0.
      unfold Defs.fail. cbn [exec]. reflexivity. } }
  rewrite (H (sse0 s)) in Hcalc. discriminate.
Qed.

(* the prefetch's leaf check IS its plain access's, away from the
   shadow-stack encoding *)
Lemma check_ca_eq (cbop : cbop_zicbop) (mxr ds : bool) (flags : mword 8) (ext : mword 10) s :
  andb (bit_to_bool (_get_PTE_Flags_U flags)) (sspte flags) = false ->
  exec (check_PTE_permission (CacheAccess (CB_prefetch cbop)) User mxr ds flags ext tt) s
  = exec (check_PTE_permission (uacc_of cbop) User mxr ds flags ext tt) s.
Proof.
  intros Hss.
  unfold check_PTE_permission, uacc_of.
  destruct cbop; cbn match; [ reflexivity | | ].
  all: destruct (zopz0zJzJzK (bit_to_bool (_get_PTE_Flags_W flags))
                   (orb (bit_to_bool (_get_PTE_Flags_R flags))
                        (Riscv.rv64d.not (bit_to_bool (_get_PTE_Flags_X flags))))) eqn:Hass.
  all: unfold Defs.assert_exp; cbn match.
  (* the leading assert fails: both sides are [None] *)
  2,4: rewrite !exec_bind; unfold Defs.fail; cbn [exec]; reflexivity.
  all: rewrite !exec_bind.
  all: rewrite !exec_returnm; cbn match.
  all: destruct (bit_to_bool (_get_PTE_Flags_U flags)) eqn:EU;
       [ change (Riscv.rv64d.not true) with false
       | change (Riscv.rv64d.not false) with true ];
       cbn match; [| reflexivity].
  all: cbn [andb] in Hss; unfold sspte in Hss.
  all: rewrite Hss; cbn match.
  all: rewrite !exec_bind.
  all: reflexivity.
Qed.

(* transfer the leaf classification from the u_acc access to the CacheAccess *)
Lemma uleaf_ok_ca (cbop : cbop_zicbop) (w : mword 64) :
  uleaf_ok (uacc_of cbop) w -> uleaf_ok (CacheAccess (CB_prefetch cbop)) w.
Proof.
  intros H a d mxr do_sum s.
  rewrite (check_ca_eq cbop mxr do_sum _ _ s
             (pte_check_no_sspte (uacc_of cbop) mxr do_sum (pte_set_ad w a d) _ s
                (H a d mxr do_sum))).
  apply H.
Qed.

Lemma uleaf_denied_ca (cbop : cbop_zicbop) (w : mword 64) :
  uleaf_denied (uacc_of cbop) w -> uleaf_denied (CacheAccess (CB_prefetch cbop)) w.
Proof.
  intros H a d mxr do_sum s.
  rewrite (check_ca_eq cbop mxr do_sum _ _ s
             (pte_check_no_sspte (uacc_of cbop) mxr do_sum (pte_set_ad w a d) _ s
                (H a d mxr do_sum))).
  apply H.
Qed.

(* ===== block alignment ===== *)
Lemma block_aligned (addr : mword 64) :
  is_aligned_vaddr (Virtaddr (and_vec addr (not_vec (zero_extend' 64 (ones (plat_cache_block_size_exp)))))) (pow2 (plat_cache_block_size_exp)) = true.
Proof.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  replace (pow2 plat_cache_block_size_exp) with 64 by (vm_compute; reflexivity).
  rewrite uint_unsigned. rewrite WpGprCsrwC.and_vec_unsigned.
  assert (HM : bv_unsigned (not_vec (zero_extend' 64 (ones plat_cache_block_size_exp)) : mword 64)
             = 18446744073709551552) by (vm_compute; reflexivity).
  rewrite HM.
  rewrite Z.rem_mod_nonneg; [ | apply Z.land_nonneg; left; apply (proj1 (bv_unsigned_in_range 64 addr)) | lia ].
  change 64 with (2 ^ 6).
  rewrite <- Z.land_ones by lia.
  replace (Z.ones 6) with 63 by (vm_compute; reflexivity).
  rewrite <- Z.land_assoc.
  replace (Z.land 18446744073709551552 63) with 0 by (vm_compute; reflexivity).
  apply Z.land_0_r.
Qed.

(* ===== pmpCheck CacheAccess grant (User) : entry-0 TOR RWX match -> None ===== *)
Lemma exec_pmpCheck_user_grant_ca (cbop : cbop_zicbop) (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (CacheAccess (CB_prefetch cbop)) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HX HW HR.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (CacheAccess (CB_prefetch cbop))) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. destruct cbop; cbn match;
        [ rewrite HX | rewrite HR | rewrite HW ]; apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* ===== pmaCheck CacheAccess : aligned RAM page -> Ok ===== *)
Lemma exec_pmaCheck_ca (cbop : cbop_zicbop) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) (width : Z) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) width (CacheAccess (CB_prefetch cbop)) pbmt false) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hx Hr Hw.
  destruct region as [rbase rsize rattr rdtree].
  destruct cbop;
    [ pma_ok_peel Hmatch Hx (exec_is_mag_applicable_cache (CB_prefetch PREFETCH_I) width s) Halign
    | pma_ok_peel Hmatch Hr (exec_is_mag_applicable_cache (CB_prefetch PREFETCH_R) width s) Halign
    | pma_ok_peel Hmatch Hw (exec_is_mag_applicable_cache (CB_prefetch PREFETCH_W) width s) Halign ].
Qed.

(* ===== phys_access_check CacheAccess -> Ok ===== *)
Lemma exec_phys_access_check_ca (cbop : cbop_zicbop) (pbmt : page_based_mem_type)
    (a : mword 64) (region : PMA_Region) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a) width = Some region ->
  is_aligned_paddr (Physaddr a) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (phys_access_check (CacheAccess (CB_prefetch cbop)) pbmt User (Physaddr a) width false) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros HA Hord Hrange HX HW HR Hmatch Halign Hx Hr Hw.
  unfold phys_access_check.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_ca cbop a width s HA Hord Hrange HX HW HR)).
  cbn match.
  exact (exec_pmaCheck_ca cbop a pbmt region width s Hmatch Halign Hx Hr Hw).
Qed.

(* ===== small pure helpers ===== *)
Lemma add_sub_cancel (a b : mword 64) : add_vec a (sub_vec b a) = b.
Proof.
  apply bv_eq.
  unfold add_vec, sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word,
    MachineWord.MachineWord.add, MachineWord.MachineWord.sub.
  rewrite bv_add_unsigned. rewrite bv_sub_unsigned.
  rewrite bv_wrap_add_idemp_r.
  replace (bv_unsigned a + (bv_unsigned b - bv_unsigned a)) with (bv_unsigned b) by lia.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma uacc_of_u_acc (cbop : cbop_zicbop) : u_acc (uacc_of cbop).
Proof. destruct cbop; unfold u_acc, uacc_of; auto. Qed.

Lemma u_fault_flavor_ca (cbop : cbop_zicbop) (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) :
  u_fault_flavor (uacc_of cbop) tfp um va -> u_fault_flavor (CacheAccess (CB_prefetch cbop)) tfp um va.
Proof.
  unfold u_fault_flavor. intros [H|[H|H]].
  - left; exact H.
  - right; left; exact H.
  - right; right. destruct H as (Hc & w & Hleaf & Hden).
    split; [exact Hc|]. exists w. split; [exact Hleaf | apply uleaf_denied_ca; exact Hden].
Qed.

Lemma ca_classify (cbop : cbop_zicbop) (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) :
  upt_acc_wf um ->
  u_data_ok (CacheAccess (CB_prefetch cbop)) um va \/ u_fault_flavor (CacheAccess (CB_prefetch cbop)) tfp um va.
Proof.
  intro Hwf.
  destruct (data_classify (uacc_of cbop) tfp um va (uacc_of_u_acc cbop) Hwf) as [Hok|Hf].
  - left. destruct Hok as (w & Hm & Hok & Hc). exists w.
    split; [exact Hm | split; [ apply uleaf_ok_ca; exact Hok | exact Hc ]].
  - right. apply u_fault_flavor_ca; exact Hf.
Qed.

(* the CacheAccess translationException maps every non-No_Access PTW error to
   the same page-fault exception (result discarded by ZICBOP) *)
Lemma exec_translationException_ca_pf (cbop : cbop_zicbop) (f : PTW_Error) s :
  (f = PTW_Invalid_Addr tt \/ f = PTW_Invalid_PTE tt \/ f = PTW_No_Permission tt) ->
  exec (translationException (CacheAccess (CB_prefetch cbop)) f) s
    = Some (match cbop with
            | PREFETCH_R => E_Load_Page_Fault tt
            | PREFETCH_W => E_SAMO_Page_Fault tt
            | PREFETCH_I => E_Fetch_Page_Fault tt end, s).
Proof.
  intro Hf. unfold translationException.
  destruct Hf as [-> | [-> | ->]]; destruct cbop; cbn match; apply exec_returnM.
Qed.


