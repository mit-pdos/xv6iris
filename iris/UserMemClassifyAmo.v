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
(* for [goodmb_rX_bits_gpr] / [goodmb_wX_bits_gpr], which the width-16 AMO
   certificate twins need and which [UserMemArms] only LOADS (Import is not
   transitive) *)
Require Import UserExecFacts.
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

(* THE PAIR-REGISTER CERTIFICATES.  [goodmb] is not determined by [exec], so
   the width-16 AMO twins below need these as well as [exec_rX_pair_bits_gpr]
   / [exec_wX_pair_bits_gpr].  A pair op touches TWO gprs -- [i] and [i+1] --
   so each takes two footprint side conditions, in the CONDITIONAL
   [Du_gpr_of_Z] shape [goodmb_rX_bits_gpr] / [goodmb_wX_bits_gpr] want. *)
Lemma goodmb_rX_pair_bits_gpr (Dr Dw : register -> bool) (rs : mword 5) s mm :
  (uint rs <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rs))) = true) ->
  (uint (add_vec_int rs 1) <> 0 ->
     Dr (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rs 1)))) = true) ->
  goodmb Dr Dw (rX_pair_bits (Regidx rs)) s mm = true.
Proof.
  intros HD0 HD1. unfold rX_pair_bits.
  destruct (generic_neq (Regidx rs) zreg); [ | apply goodmb_returnm ].
  change (regidx_offset_range (Regidx rs) 1) with (Regidx (add_vec_int rs 1)).
  erewrite (gm_bind _ _ _ _ _ _ _ _
              (goodmb_rX_bits_gpr Dr Dw (add_vec_int rs 1) s mm HD1)
              (exec_rX_bits_gpr (add_vec_int rs 1) s)).
  erewrite (gm_bind _ _ _ _ _ _ _ _
              (goodmb_rX_bits_gpr Dr Dw rs s mm HD0) (exec_rX_bits_gpr rs s)).
  apply goodmb_returnm.
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

Lemma goodmb_wX_pair_bits_gpr (Dr Dw : register -> bool) (rd : mword 5)
    (data : mword (64 * 2)) s mm :
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  (uint (add_vec_int rd 1) <> 0 ->
     Dw (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) = true) ->
  goodmb Dr Dw (wX_pair_bits (Regidx rd) data) s mm = true.
Proof.
  intros HD0 HD1. unfold wX_pair_bits.
  destruct (generic_neq (Regidx rd) zreg); [ | apply goodmb_returnm ].
  erewrite (gm_bind0 _ _ _ _ _ _ _
              (goodmb_wX_bits_gpr Dr Dw rd
                 (subrange_vec_dec data (Z.sub xlen 1) 0) s mm HD0)
              (exec_wX_bits_gpr rd (subrange_vec_dec data (Z.sub xlen 1) 0) s)).
  change (regidx_offset_range (Regidx rd) 1) with (Regidx (add_vec_int rd 1)).
  apply (goodmb_wX_bits_gpr Dr Dw (add_vec_int rd 1) _ _ mm HD1).
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

(* The certificate twin of the store arm at width 16.  Transcription of
   [UserMemArms.goodmb_execute_AMO_u_store] with the two width branches taken
   the other way ([16 <=? 2*xlen_bytes] true, [16 <=? xlen_bytes] FALSE, which
   is what routes rs2/rd through the PAIR reads) and the rd write through
   [wX_pair_bits].  [goodmb] recurses on the continuation applied to what the
   state holds, so every case needs that case's [exec] fact beside its
   certificate -- which is why each pair read is handed in twice. *)
Lemma goodmb_execute_AMO_u_store_16 (Dr Dw : register -> bool)
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (rp rpd : mword (64 * 2)) (loaded : mword (8 * 16)) (md : SATPMode)
    (s s' s'' : mstate) mm :
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
  (uint rs1 <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rs1))) = true) ->
  (uint rs2 <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rs2))) = true) ->
  (uint (add_vec_int rs2 1) <> 0 ->
     Dr (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rs2 1)))) = true) ->
  (uint rd <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  (uint (add_vec_int rd 1) <> 0 ->
     Dr (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) = true) ->
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  (uint (add_vec_int rd 1) <> 0 ->
     Dw (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) = true) ->
  Dr mstatus = true ->
  Dr cur_privilege = true ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  goodmb Dr Dw (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s mm = true ->
  exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s) ->
  goodmb Dr Dw (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s mm = true ->
  exec (translationMode User) s = Some (md, s) ->
  goodmb Dr Dw (translationMode User) s mm = true ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s mm = true ->
  exec (rX_pair_bits (Regidx rs2)) s' = Some (rp, s') ->
  exec (rX_pair_bits (Regidx rd)) s' = Some (rpd, s') ->
  andb (generic_eq op AMOCAS) (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd)) = false ->
  exec (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok tt, s') ->
  goodmb Dr Dw (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s' mm = true ->
  exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  goodmb Dr Dw (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' mm = true ->
  exec (mem_write_value addr 16
          (sign_extend' (Z.mul 8 (__id 16)) result')
          (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s' = Some (Ok true, s'') ->
  goodmb Dr Dw (mem_write_value addr 16
          (sign_extend' (Z.mul 8 (__id 16)) result')
          (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s' mm = true ->
  goodmb Dr Dw (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s mm = true.
Proof.
  intros rs2_val lc result'.
  intros HDrs1 HDrs2 HDrs2' HDrdr HDrdr' HDrdw HDrdw' HDms HDcp.
  intros Hcp Heff Hgeff Hpml Hgpml Htm Hgtm Hal Htr Hgtr Hrp Hrpd Hguard
         Hea Hgea Hrdm Hgrdm Hwv Hgwv.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. apply goodmb_cer.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  assert (Hgass : goodmb Dr Dw (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s mm = true)
    by reflexivity.
  erewrite (gm_liftR_seq _ _ _ _ _ _ _ _ Hgass Hass).
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
  assert (Hggtda : goodmb Dr Dw (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s mm = true).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    assert (Hgedga : goodmb Dr Dw (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s mm = true).
    { unfold ext_data_get_addr.
      erewrite gm_bind; [ | apply goodmb_rX_bits_gpr, HDrs1 | apply (exec_rX_bits_gpr rs1 s) ].
      apply goodmb_returnm. }
    erewrite (gm_bind _ _ _ _ _ _ _ _ Hgedga Hedga). cbn match.
    assert (Hgtea : goodmb Dr Dw (transform_effective_address
                       (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                          (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s mm = true).
    { unfold transform_effective_address.
      gmm_rr mstatus HDms.
      gmm_rr cur_privilege HDcp. rewrite Hcp.
      erewrite (gm_bind _ _ _ _ _ _ _ _ Hgeff Heff).
      erewrite (gm_bind _ _ _ _ _ _ _ _ Hgpml Hpml).
      erewrite (gm_bind _ _ _ _ _ _ _ _ Hgtm Htm).
      destruct (generic_eq md Bare); apply goodmb_returnm. }
    erewrite (gm_bind _ _ _ _ _ _ _ _ Hgtea
                (exec_transform_effective_address_u (Atomic (op, aq, rl, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply goodmb_returnm. }
  erewrite (gm_liftR_seq _ _ _ _ _ _ _ _ Hggtda Hgtda). cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  gmxlR Hgtr Htr.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn match.
  erewrite (gm_liftR_seq _ _ _ _ _ _ _ _ Hgea Hea). cbn match.
  gmxlR Hgrdm Hrdm. rewrite mbind_Ret. cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn zeta.
  replace (Z.leb 16 xlen_bytes) with false by (vm_compute; reflexivity).
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s'
               = Some (inr rs2_val, s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ Hrp). apply execR_returnR_fwd. }
  assert (Hgrs2 : goodmb Dr Dw (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s' mm = true).
  { erewrite (gm_liftR_seq _ _ _ _ _ _ _ _
                (goodmb_rX_pair_bits_gpr Dr Dw rs2 s' mm HDrs2 HDrs2') Hrp).
    apply goodmb_returnm. }
  erewrite (gm_bindR _ _ _ _ _ _ _ _ Hgrs2 Hrs2).
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
  match goal with |- context[and_boolM ?A ?B] =>
    assert (Hgab : goodmb Dr Dw (and_boolM A B) s' mm = true) end.
  { assert (Hrdt : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rd)))
                     (fun w16 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w16))) s'
                 = Some (inr (trunc (Z.mul (__id 16) 8) rpd), s')).
    { rewrite (execR_liftR_seq _ _ _ _ _ Hrpd). apply execR_returnR_fwd. }
    assert (Hgrdt : goodmb Dr Dw (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rd)))
                     (fun w16 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w16))) s' mm = true).
    { erewrite (gm_liftR_seq _ _ _ _ _ _ _ _
                  (goodmb_rX_pair_bits_gpr Dr Dw rd s' mm HDrdr HDrdr') Hrpd).
      apply goodmb_returnm. }
    unfold and_boolM.
    erewrite gm_bindR;
      [ | apply goodmb_returnm | apply (execR_returnR_fwd (generic_eq op AMOCAS) s') ].
    destruct (generic_eq op AMOCAS); cbn match.
    - erewrite (gm_bindR _ _ _ _ _ _ _ _ Hgrdt Hrdt). apply goodmb_returnm.
    - apply goodmb_returnm. }
  erewrite (gm_bindR _ _ _ _ _ _ _ _ Hgab Hab). rewrite Hguard. cbn match.
  erewrite (gm_liftR_seq _ _ _ _ _ _ _ _ Hgwv Hwv). cbn match.
  assert (Hwxpr : execR (R := ExecutionResult)
                    (Defs.liftR (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) lc))) s''
                = Some (inr tt, wpair_state rd (sign_extend' (Z.mul 64 2) lc) s'')).
  { rewrite execR_liftR. rewrite exec_wX_pair_bits_gpr. reflexivity. }
  assert (Hgwxpr : goodmb Dr Dw (Defs.liftR (R := ExecutionResult)
                     (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) lc))) s'' mm = true).
  { apply goodmb_liftR. exact (goodmb_wX_pair_bits_gpr Dr Dw rd _ s'' mm HDrdw HDrdw'). }
  erewrite (gm_bind0R _ _ _ _ _ _ _ Hgwxpr Hwxpr).
  apply goodmb_returnm.
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

(* The certificate twin of the failed-compare arm at width 16.  Identical to
   [goodmb_execute_AMO_u_store_16] up to the guard's polarity, with the
   [mem_write_value] step gone: a failed AMOCAS.Q is architecturally a read
   (plus the [mem_write_ea] intent), so the state never moves past [s']. *)
Lemma goodmb_execute_AMO_u_cas_ne_16 (Dr Dw : register -> bool)
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (rp rpd : mword (64 * 2)) (loaded : mword (8 * 16)) (md : SATPMode)
    (s s' : mstate) mm :
  let lc : bits (16 * 8) := autocast (T := mword) loaded in
  (uint rs1 <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rs1))) = true) ->
  (uint rs2 <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rs2))) = true) ->
  (uint (add_vec_int rs2 1) <> 0 ->
     Dr (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rs2 1)))) = true) ->
  (uint rd <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  (uint (add_vec_int rd 1) <> 0 ->
     Dr (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) = true) ->
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  (uint (add_vec_int rd 1) <> 0 ->
     Dw (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) = true) ->
  Dr mstatus = true ->
  Dr cur_privilege = true ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  goodmb Dr Dw (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s mm = true ->
  exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s) ->
  goodmb Dr Dw (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s mm = true ->
  exec (translationMode User) s = Some (md, s) ->
  goodmb Dr Dw (translationMode User) s mm = true ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s mm = true ->
  exec (rX_pair_bits (Regidx rs2)) s' = Some (rp, s') ->
  exec (rX_pair_bits (Regidx rd)) s' = Some (rpd, s') ->
  andb (generic_eq op AMOCAS) (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd)) = true ->
  exec (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok tt, s') ->
  goodmb Dr Dw (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s' mm = true ->
  exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  goodmb Dr Dw (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' mm = true ->
  goodmb Dr Dw (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s mm = true.
Proof.
  intros lc.
  intros HDrs1 HDrs2 HDrs2' HDrdr HDrdr' HDrdw HDrdw' HDms HDcp.
  intros Hcp Heff Hgeff Hpml Hgpml Htm Hgtm Hal Htr Hgtr Hrp Hrpd Hguard
         Hea Hgea Hrdm Hgrdm.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. apply goodmb_cer.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  assert (Hgass : goodmb Dr Dw (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s mm = true)
    by reflexivity.
  erewrite (gm_liftR_seq _ _ _ _ _ _ _ _ Hgass Hass).
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
  assert (Hggtda : goodmb Dr Dw (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s mm = true).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    assert (Hgedga : goodmb Dr Dw (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s mm = true).
    { unfold ext_data_get_addr.
      erewrite gm_bind; [ | apply goodmb_rX_bits_gpr, HDrs1 | apply (exec_rX_bits_gpr rs1 s) ].
      apply goodmb_returnm. }
    erewrite (gm_bind _ _ _ _ _ _ _ _ Hgedga Hedga). cbn match.
    assert (Hgtea : goodmb Dr Dw (transform_effective_address
                       (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                          (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s mm = true).
    { unfold transform_effective_address.
      gmm_rr mstatus HDms.
      gmm_rr cur_privilege HDcp. rewrite Hcp.
      erewrite (gm_bind _ _ _ _ _ _ _ _ Hgeff Heff).
      erewrite (gm_bind _ _ _ _ _ _ _ _ Hgpml Hpml).
      erewrite (gm_bind _ _ _ _ _ _ _ _ Hgtm Htm).
      destruct (generic_eq md Bare); apply goodmb_returnm. }
    erewrite (gm_bind _ _ _ _ _ _ _ _ Hgtea
                (exec_transform_effective_address_u (Atomic (op, aq, rl, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply goodmb_returnm. }
  erewrite (gm_liftR_seq _ _ _ _ _ _ _ _ Hggtda Hgtda). cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  gmxlR Hgtr Htr.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn match.
  erewrite (gm_liftR_seq _ _ _ _ _ _ _ _ Hgea Hea). cbn match.
  gmxlR Hgrdm Hrdm. rewrite mbind_Ret. cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]. cbn zeta.
  replace (Z.leb 16 xlen_bytes) with false by (vm_compute; reflexivity).
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s'
               = Some (inr (trunc (Z.mul (__id 16) 8) rp), s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ Hrp). apply execR_returnR_fwd. }
  assert (Hgrs2 : goodmb Dr Dw (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s' mm = true).
  { erewrite (gm_liftR_seq _ _ _ _ _ _ _ _
                (goodmb_rX_pair_bits_gpr Dr Dw rs2 s' mm HDrs2 HDrs2') Hrp).
    apply goodmb_returnm. }
  erewrite (gm_bindR _ _ _ _ _ _ _ _ Hgrs2 Hrs2).
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
  match goal with |- context[and_boolM ?A ?B] =>
    assert (Hgab : goodmb Dr Dw (and_boolM A B) s' mm = true) end.
  { assert (Hrdt : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rd)))
                     (fun w16 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w16))) s'
                 = Some (inr (trunc (Z.mul (__id 16) 8) rpd), s')).
    { rewrite (execR_liftR_seq _ _ _ _ _ Hrpd). apply execR_returnR_fwd. }
    assert (Hgrdt : goodmb Dr Dw (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rd)))
                     (fun w16 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w16))) s' mm = true).
    { erewrite (gm_liftR_seq _ _ _ _ _ _ _ _
                  (goodmb_rX_pair_bits_gpr Dr Dw rd s' mm HDrdr HDrdr') Hrpd).
      apply goodmb_returnm. }
    unfold and_boolM.
    erewrite gm_bindR;
      [ | apply goodmb_returnm | apply (execR_returnR_fwd (generic_eq op AMOCAS) s') ].
    destruct (generic_eq op AMOCAS); cbn match.
    - erewrite (gm_bindR _ _ _ _ _ _ _ _ Hgrdt Hrdt). apply goodmb_returnm.
    - apply goodmb_returnm. }
  erewrite (gm_bindR _ _ _ _ _ _ _ _ Hgab Hab). rewrite Hguard. cbn match.
  assert (Hwxpr : execR (R := ExecutionResult)
                    (Defs.liftR (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) lc))) s'
                = Some (inr tt, wpair_state rd (sign_extend' (Z.mul 64 2) lc) s')).
  { rewrite execR_liftR. rewrite exec_wX_pair_bits_gpr. reflexivity. }
  assert (Hgwxpr : goodmb Dr Dw (Defs.liftR (R := ExecutionResult)
                     (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) lc))) s' mm = true).
  { apply goodmb_liftR. exact (goodmb_wX_pair_bits_gpr Dr Dw rd _ s' mm HDrdw HDrdw'). }
  erewrite (gm_bind0R _ _ _ _ _ _ _ Hgwxpr Hwxpr).
  apply goodmb_returnm.
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



(* ===================================================================== *)
(* THE ZICBOP PREFETCH ARM (worklist section 15).                          *)
(*                                                                        *)
(* [execute_ZICBOP] runs a REAL [translateAddr] on the runtime cache-block *)
(* address and then does nothing to memory at all: the physical-access     *)
(* check's result is discarded and a translation fault is suppressed to a  *)
(* nop.  So the arm is the TRICHOTOMY of section 15 with the access half   *)
(* empty -- [ca_classify] splits mapped-and-permitted from faulting,       *)
(* [UserMemCert]'s walk answers the first and [UserFaultCert]'s fault      *)
(* translate the second, and both land on [UserMemTotal.finish_mem_base]   *)
(* with [RETIRE_SUCCESS].                                                  *)
(*                                                                        *)
(* These requires sit HERE, not at the head of the file: everything above  *)
(* is the AMO exec layer and the ZICBOP classification, and a new import   *)
(* at the top would put the certificate layer's names in scope for it      *)
(* (the shadowing trap of worklist section 15).                            *)
(* ===================================================================== *)
Require Import WpDecodeBridge HartGoodb DecodeTotalU.
Require Import UserExecFacts MemAccessGen HartLift HartSpan SmodePte.
Require Import UserTranslate PtreeType PtTree KptPt PtTreeAdue KptTree PtWalkCert.
Require Import UserFetchCert UserMemCert UserFaultCert.
Local Open Scope Z_scope.

Lemma goodb_is_shadow_stack_ca (Db : register -> bool) (cbop : cbop_zicbop)
    (s : mstate) :
  goodb Db (is_shadow_stack_access (CacheAccess (CB_prefetch cbop))) s = true.
Proof. unfold is_shadow_stack_access. cbn match. reflexivity. Qed.

Lemma goodb_check_PTE_permission_ca (cbop : cbop_zicbop)
    (w' : mword 64) (mxr do_sum : bool) (Db : register -> bool) (s : mstate) :
  pte_check_ok (CacheAccess (CB_prefetch cbop)) User mxr do_sum w' ->
  goodb Db (check_PTE_permission (CacheAccess (CB_prefetch cbop)) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec w' 7 0))
              (ext_bits_of_PTE w') tt) s = true.
Proof.
  unfold pte_check_ok. intros Hchk.
  pose proof (Hchk dstateM) as Hc0.
  destruct cbop;
  destruct (mword1_cases (_get_PTE_Flags_U (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HU|HU];
  destruct (mword1_cases (_get_PTE_Flags_R (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HR|HR];
  destruct (mword1_cases (_get_PTE_Flags_W (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HW|HW];
  destruct (mword1_cases (_get_PTE_Flags_X (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HX|HX];
  unfold check_PTE_permission in Hc0 |- *;
  rewrite ?HU ?HR ?HW ?HX;
  rewrite ?HU ?HR ?HW ?HX in Hc0;
  first [ solve [ vm_compute; reflexivity ]
        | solve [ vm_compute in Hc0; discriminate Hc0 ] ].
Time Qed.
Lemma u_walk_pure_gen (acc : MemoryAccessType mem_payload)
    (P : uptd) (t : ptree) (mm : PtBytes.pamap) (rs : regstate) (w va : mword 64) :
  (forall s : mstate, exec (is_shadow_stack_access acc) s = Some (false, s)) ->
  (forall (Db : register -> bool) (s : mstate),
     goodb Db (is_shadow_stack_access acc) s = true) ->
  (forall (a d : mword 1) (mxr do_sum : bool) (Db : register -> bool) (s : mstate),
     goodb Db (check_PTE_permission acc User mxr do_sum
                 (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                 (ext_bits_of_PTE (pte_set_ad w a d)) tt) s = true) ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok acc w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) acc) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) acc) (u_state rs mm) mm = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm' /\
    u_data_cfg rs' /\ u_exec_pins P t' rs' /\ u_mem_wf P t' mm'.
Proof.
  intros Hssa Hssb Hchkb Hl Hleaf Hcanon Hcfg Hpins Hwf.
  pose proof Hcfg as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  pose proof Hpins as Hpins0.
  destruct Hpins as (Hhw & Hcfgp & Hpt & Htlbok).
  destruct Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
  destruct Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
  pose proof Hwf as (md & Hdisj & Hdj & Hmm & Hdm & Hram & Hacc0 & Hwfm & Hspec).
  pose proof Hspec as (Hbase & _).
  destruct (upt_spec_maps (ud_root P) (ud_tfp P) (ud_um P) t (svpn_of va) w
              Hspec (or_intror (or_intror Hl)))
    as (p2 & p1 & a0 & d0 & Hmaps).
  pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                       Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
  assert (Hvar : forall a d : mword 1,
            pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
            pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d))
    by exact (upt_variant (ud_tfp P) (ud_um P) (svpn_of va) w Hwfm
                (or_intror (or_intror Hl))).
  (* the three slots, as reads and as ownership *)
  (* the tree projections are stated at the WEAKER [u_mem_ok]; one lemma
     application, never a re-proof *)
  pose proof (u_mem_wf_ok P t mm Hwf) as Hokm.
  assert (Hsm2 : pt_slot_mem (u_state rs mm) (pt_addr2 t (svpn_of va)) p2)
    by exact (u_slot_mem_at P t mm rs (pt_base t) (vpn_idx 2 (svpn_of va)) p2 Hokm
                (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm1 : pt_slot_mem (u_state rs mm) (pt_addr1 p2 (svpn_of va)) p1)
    by exact (u_slot_mem_at P t mm rs (u_next_base p2) (vpn_idx 1 (svpn_of va)) p1 Hokm
                (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm0 : pt_slot_mem (u_state rs mm) (pt_addr0 p1 (svpn_of va))
                   (pte_set_ad w a0 d0))
    by exact (u_slot_mem_at P t mm rs (u_next_base p1) (vpn_idx 0 (svpn_of va)) _ Hokm
                (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown2 : bytes_owned mm (pt_addr2 t (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ p2 Hokm (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown1 : bytes_owned mm (pt_addr1 p2 (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ p1 Hokm (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown0 : bytes_owned mm (pt_addr0 p1 (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ _ Hokm (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  (* the three read-only probes of [translateAddr]'s front matter *)
  assert (Htm : exec (translationMode User) (u_state rs mm)
                = Some (Sv39, u_state rs mm))
    by exact (exec_translationMode_U_sv39 usatp (u_state rs mm) Lsxl Hsatp Hmode).
  assert (Htmg : goodb Du_r (translationMode User) (u_state rs mm) = true)
    by exact (goodb_translationMode_U Du_r usatp (u_state rs mm)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Lsxl Hsatp Hmode).
  assert (Heff : exec (effectivePrivilege acc
                        (register_lookup mstatus (u_state rs mm).(sregs)) User)
                   (u_state rs mm) = Some (User, u_state rs mm))
    by exact (exec_effectivePrivilege_mprv0 acc _ User (u_state rs mm) Lmprv).
  assert (Heffg : goodb Du_r (effectivePrivilege acc
                        (register_lookup mstatus (u_state rs mm).(sregs)) User)
                    (u_state rs mm) = true)
    by exact (goodb_effectivePrivilege_mprv0 Du_r acc _ User (u_state rs mm) Lmprv).
  assert (Hssx : exec (is_shadow_stack_access acc) (u_state rs mm)
                 = Some (false, u_state rs mm))
    by exact (Hssa (u_state rs mm)).
  assert (Hssg : goodb Du_r (is_shadow_stack_access acc) (u_state rs mm) = true)
    by exact (Hssb Du_r (u_state rs mm)).
  (* the PMA grants *)
  assert (Hpmar : pma_allows_pte_read
                    (register_lookup pma_regions (u_state rs mm).(sregs)))
    by exact (pma_allows_all_pte_read _ Hall).
  assert (Hpmaw : pma_allows_pte_write
                    (register_lookup pma_regions (u_state rs mm).(sregs)))
    by exact (Hpmaw_of _ Hall).
  (* the leaf's permission check and the three validity tests, certified *)
  assert (Hgchk : forall (a d : mword 1) (mxr do_sum : bool)
                    (Db : register -> bool) (s0 : mstate),
            goodb Db (check_PTE_permission acc User mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                        (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true).
  { intros a d mxr do_sum Db s0.
    exact (Hchkb a d mxr do_sum Db s0). }
  assert (Hg2 : forall (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                        (ext_bits_of_PTE p2)) s0 = true)
    by (intros Db s0; exact (goodb_pte_is_invalid_valid p2 Db s0 Hv2)).
  assert (Hg1 : forall (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                        (ext_bits_of_PTE p1)) s0 = true)
    by (intros Db s0; exact (goodb_pte_is_invalid_valid p1 Db s0 Hv1)).
  assert (Hg0 : forall (a d : mword 1) (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid
                        (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                        (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true)
    by (intros a d Db s0;
        exact (goodb_pte_is_invalid_valid _ Db s0 (proj1 (Hvar a d)))).
  (* THE TRANSLATION, exec side and certificate side *)
  destruct (KptTree.ptree_translateAddr_cases acc User
              (ud_root P) va w (u_walk_pa w va) usatp t (register_lookup tlb rs)
              p2 p1 a0 d0 (u_state rs mm)
              Hleaf Hcanon eq_refl (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
              Hbase Hmaps Htlbok Hsm2 Hsm1 Hsm0
              Hmisa Lmenv Hhtif Lcp Htm Heff Hssx Hsatp Hppn Hasid eq_refl
              HA Hord HRp HWp Hcovp Hpmar Hpmaw)
    as (sf & Htr & Harms).
  assert (Htrg : goodmb Du_r Du_w (translateAddr (Virtaddr va) acc)
                   (u_state rs mm) mm = true).
  { apply (goodmb_ptree_translateAddr Du_r Du_w acc User
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             (ud_root P) t va w (u_walk_pa w va) usatp (register_lookup tlb rs)
             p2 p1 a0 d0 (u_state rs mm) mm
             Hleaf Hgchk Hcanon eq_refl
             (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
             Hbase Hmaps Htlbok Hg2 Hg1 Hg0 Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
             Hmisa Lmenv Hhtif Lcp Htm Htmg Heff Heffg Hssx Hssg
             Hsatp Hppn Hasid eq_refl HA Hord HRp HWp Hcovp Hpmar Hpmaw). }
  (* WHERE THE TRANSLATION LANDED: the three arms, each with its tree, its
     file and its [u_mem_step].  Nothing after this point looks at which. *)
  assert (Hland : exists (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree),
            sf = u_state rs' mm' /\
            (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
            tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
            u_mem_step P t t' mm mm').
  { destruct Harms as [-> | [-> | (a1 & d1 & ->)]].
    - exists rs, mm, t. split_and!;
        [ reflexivity | left; reflexivity | exact Htlbok
        | exact (u_mem_step_refl P t mm Hwf) ].
    - eexists _, mm, t. split_and!.
      + reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0) t (register_lookup tlb rs)
                 (svpn_of va) p2 p1 _ Hmaps Htlbok).
      + exact (u_mem_step_refl P t mm Hwf).
    - assert (Habs : pte_set_ad (pte_set_ad w a0 d0) a1 d1 = pte_set_ad w a1 d1)
        by exact (pte_set_ad_absorb w a0 d0 a1 d1).
      assert (Hv' : pte_valid (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (Hvar a1 d1))).
      assert (Hl' : pte_leaf (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (proj2 (Hvar a1 d1)))).
      assert (Hn' : pte_no_napot (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hp' : pte_pbmt0 (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj2 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hspec' : upt_tree_spec (ud_root P) (ud_tfp P) (ud_um P)
                (ptree_set_leaf t (svpn_of va)
                   (pte_set_ad (pte_set_ad w a0 d0) a1 d1))).
      { rewrite Habs.
        exact (upt_tree_spec_set_leaf (ud_root P) (ud_tfp P) (ud_um P) t
                 (svpn_of va) w p2 p1 a0 d0 a1 d1 Hwfm Hspec
                 (or_intror (or_intror Hl)) Hmaps). }
      eexists _, _,
        (ptree_set_leaf t (svpn_of va) (pte_set_ad (pte_set_ad w a0 d0) a1 d1)).
      split_and!.
      + reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0)
                 (ptree_set_leaf t (svpn_of va)
                    (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
                 (register_lookup tlb rs) (svpn_of va) p2 p1 _
                 (ptree_set_leaf_maps_self t (svpn_of va) p2 p1
                    (pte_set_ad w a0 d0) _ Hmaps Hv' Hl' Hn' Hp')
                 (tlb_ok_pt_set_leaf (mword_of_int 0) t (register_lookup tlb rs)
                    (svpn_of va) p2 p1 (pte_set_ad w a0 d0) a1 d1
                    Hmaps Hv' Hl' Hn' Hp' Htlbok)).
      + exact (u_mem_step_writeback P t mm (svpn_of va) p2 p1
                 (pte_set_ad w a0 d0) _ Hwf Hmaps Hspec'). }
  destruct Hland as (rs' & mm' & t' & Hsf & Hfile & Htlbok' & Hstep).
  rewrite Hsf in Htr.
  exists rs', mm', t'. split_and!.
  - exact Htr.
  - exact Htrg.
  - exact Hfile.
  - exact Htlbok'.
  - exact Hstep.
  - exact (u_data_cfg_tlb rs rs' Hfile Hcfg).
  - exact (u_exec_pins_tlb P t t' rs rs' Hfile Htlbok' Hpins0).
  - exact (u_mem_step_wf P t t' mm mm' Hwf Hstep).
Qed.

(* ===================================================================== *)
(* THE POINTER-MASKING PROBE'S CERTIFICATE.                               *)
(* ===================================================================== *)
Lemma u_gm_pmm_applicable (acc : MemoryAccessType mem_payload) (s : mstate)
    (mm : PtBytes.pamap) :
  generic_neq acc (InstructionFetch tt) = true ->
  generic_neq acc (Load PageTableEntry) = true ->
  generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  goodmb Du_r Du_w (is_pmm_applicable acc User) s mm = true.
Proof.
  intros Hif Hlp Hsp Hmxr.
  assert (HDms : Du_r mstatus = true) by (vm_compute; reflexivity).
  unfold is_pmm_applicable.
  rewrite (gm_and_boolM Du_r Du_w _ _ s s mm _
             (goodmb_returnm Du_r Du_w _ s mm) (exec_returnM _ s)).
  rewrite Hif. cbn match.
  rewrite (gm_and_boolM Du_r Du_w _ _ s s mm _
             (goodmb_returnm Du_r Du_w _ s mm) (exec_returnM _ s)).
  rewrite Hlp. cbn match.
  rewrite (gm_and_boolM Du_r Du_w _ _ s s mm _
             (goodmb_returnm Du_r Du_w _ s mm) (exec_returnM _ s)).
  rewrite Hsp. cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] =>
      assert (HorE : exec orb s = Some (true, s));
      [ | assert (HorG : goodmb Du_r Du_w orb s mm = true) ]
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq User Machine) with false by (vm_compute; reflexivity).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite Hmxr.
    apply exec_returnm. }
  { rewrite (gm_or_boolM Du_r Du_w _ _ s s mm _
               (goodmb_returnm Du_r Du_w _ s mm) (exec_returnM _ s)).
    replace (generic_eq User Machine) with false by (vm_compute; reflexivity).
    cbn match.
    gmm_rr mstatus HDms. apply goodmb_returnm. }
  rewrite (gm_and_boolM Du_r Du_w _ _ s s mm true HorG HorE). cbn match.
  apply goodmb_returnm.
Qed.

(* [get_pmm User] reads [misa] / [menvcfg] / [senvcfg] only -- all of [D_u] --
   so its certificate is [UserTotalU.u_gm_gate]'s: compute at [dstateU] and
   transport by agreement. *)
Lemma u_gm_pmm (s : mstate) (mm : PtBytes.pamap) :
  agree_on D_u s dstateU ->
  goodmb Du_r Du_w (get_pmm User) s mm = true.
Proof. intro Hag. apply UserTotalU.u_gm_lift0. apply (UserTotalU.u_gm_gate s _ Hag). reflexivity. Qed.

Lemma u_gm_pmlen (acc : MemoryAccessType mem_payload) (s : mstate)
    (mm : PtBytes.pamap) :
  agree_on D_u s dstateU ->
  generic_neq acc (InstructionFetch tt) = true ->
  generic_neq acc (Load PageTableEntry) = true ->
  generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
  goodmb Du_r Du_w (get_pmlen acc User) s mm = true.
Proof.
  intros Hag Hif Hlp Hsp Hmxr Hmisa Hmenv Hsenv. unfold get_pmlen.
  rewrite (gm_bind Du_r Du_w _ _ s s mm true
             (u_gm_pmm_applicable acc s mm Hif Hlp Hsp Hmxr)
             (exec_is_pmm_applicable_u acc s Hif Hlp Hsp Hmxr)).
  cbn match.
  rewrite (gm_bind Du_r Du_w _ _ s s mm PMM_Disabled (u_gm_pmm s mm Hag)
             (exec_get_pmm_u_disabled s Hmisa Hmenv Hsenv)).
  cbn match. apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* THE PHYSICAL-ACCESS CHECK'S CERTIFICATE, at the prefetch access type.   *)
(* ===================================================================== *)
Lemma goodmb_pmpCheck_user_grant_ca (Dr Dw : register -> bool)
    (cbop : cbop_zicbop) (a : mword 64) (width : Z) s mm :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (CacheAccess (CB_prefetch cbop)) User)
    s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HX HW HR.
  apply (goodmb_pmpCheck_grant Dr Dw a width (CacheAccess (CB_prefetch cbop)) User
           s mm HDc HDa HA Hord Hrange).
  - unfold pmpCheckRWX. cbn match. destruct cbop; cbn match;
      [ rewrite HX | rewrite HR | rewrite HW ]; apply exec_returnm.
  - unfold pmpCheckRWX. cbn match. destruct cbop; cbn match; apply goodmb_returnm.
Qed.

Lemma goodmb_pmaCheck_ca (Dr Dw : register -> bool) (cbop : cbop_zicbop)
    (addr : mword 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (width : Z) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width
    = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) width (CacheAccess (CB_prefetch cbop))
                  pbmt false) s mm = true.
Proof.
  intros HD Hmatch Halign Hx Hr Hw.
  destruct region as [rbase rsize rattr rdtree].
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  destruct cbop;
    [ pose proof Hx as Hfield;
      pose (CB_prefetch PREFETCH_I) as cop
    | pose proof Hr as Hfield;
      pose (CB_prefetch PREFETCH_R) as cop
    | pose proof Hw as Hfield;
      pose (CB_prefetch PREFETCH_W) as cop ];
  unfold pmaCheck; apply goodmb_cer;
  gmm_lift Hrg (exec_read_reg pma_regions s);
  rewrite Hmatch; cbn [PMA_Region_attributes] in Hfield |- *; cbn match;
  (erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]);
  cbn match beta;
  (erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ]);
  rewrite Hfield; cbn [Riscv.rv64d.not negb];
  gmm_lift (goodmb_mag_pma_check_aligned Dr Dw (override_PMA rattr pbmt)
              (CacheAccess cop) (Physaddr addr) width false s mm
              (goodmb_returnm Dr Dw false s mm)
              (exec_is_mag_applicable_cache cop width s) Halign)
           (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
              (CacheAccess cop) (Physaddr addr) width false s
              (exec_is_mag_applicable_cache cop width s) Halign);
  cbn match beta; reflexivity.
Qed.

Lemma goodmb_phys_access_check_ca (Dr Dw : register -> bool) (cbop : cbop_zicbop)
    (pbmt : page_based_mem_type) (a : mword 64) (region : PMA_Region)
    (width : Z) s mm :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true -> Dr pma_regions = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a) width
    = Some region ->
  is_aligned_paddr (Physaddr a) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  goodmb Dr Dw (phys_access_check (CacheAccess (CB_prefetch cbop)) pbmt User
                  (Physaddr a) width false) s mm = true.
Proof.
  intros HDc HDa HDp HA Hord Hrange HX HW HR Hmatch Halign Hx Hr Hw.
  unfold phys_access_check.
  erewrite (gm_bind Dr Dw _ _ s s mm None
              (goodmb_pmpCheck_user_grant_ca Dr Dw cbop a width s mm
                 HDc HDa HA Hord Hrange HX HW HR)
              (exec_pmpCheck_user_grant_ca cbop a width s HA Hord Hrange HX HW HR)).
  cbn match.
  exact (goodmb_pmaCheck_ca Dr Dw cbop a pbmt region width s mm
           HDp Hmatch Halign Hx Hr Hw).
Qed.

(* ===================================================================== *)
(* THE ZICBOP EXECUTE LAYER: the runtime block address, and the two        *)
(* outcomes of its translation.  [execute_ZICBOP] ALWAYS retires -- the    *)
(* translation fault is suppressed to a nop -- and the physical access     *)
(* check's own result is discarded, so both twins are stated over an       *)
(* ARBITRARY [phys_access_check] result.                                   *)
(* ===================================================================== *)

(* the runtime cache-block address, spelled as the model builds it *)
Local Notation ca_blk rs1 offset s :=
  (and_vec
     (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
              (sign_extend' 64 offset))
     (not_vec (zero_extend' 64 (ones (plat_cache_block_size_exp))))).

Local Notation ca_off rs1 offset s :=
  (sub_vec
     (and_vec
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                 (sign_extend' 64 offset))
        (not_vec (zero_extend' 64 (ones (plat_cache_block_size_exp)))))
     (if Z.eqb (uint rs1) 0 then zero_reg
      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).

Lemma exec_execute_ZICBOP_u_ok (cbop : cbop_zicbop) (rs1 : mword 5)
    (offset : mword 12) (md : SATPMode) (pa : mword 64)
    (rr : result Phys_Mem_Access_Info ExceptionType) (s s' : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (CacheAccess (CB_prefetch cbop)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  exec (translateAddr (Virtaddr (ca_blk rs1 offset s))
          (CacheAccess (CB_prefetch cbop))) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  register_lookup cur_privilege s'.(sregs) = User ->
  exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s'.(sregs)) User) s' = Some (User, s') ->
  exec (phys_access_check (CacheAccess (CB_prefetch cbop)) PBMT_PMA User
          (Physaddr pa) 64 false) s' = Some (rr, s') ->
  exec (execute (ZICBOP (cbop, Regidx rs1, offset))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Lcp Heff Hpml Htm Htr Lcp' Heff' Hphys.
  change (execute (ZICBOP (cbop, Regidx rs1, offset)))
    with (execute_ZICBOP cbop (Regidx rs1) offset).
  unfold execute_ZICBOP.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). cbn zeta.
  match goal with
  | |- exec (Defs.bind (get_transformed_data_addr _ ?off _ _) _) _ = _ =>
      assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) off
                        (CacheAccess (CB_prefetch cbop))
                        (pow2 (plat_cache_block_size_exp))) s
                      = Some (Ext_DataAddr_OK (Virtaddr (ca_blk rs1 offset s)), s))
  end.
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 _
               (CacheAccess (CB_prefetch cbop))
               (pow2 (plat_cache_block_size_exp)) s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u
               (CacheAccess (CB_prefetch cbop)) md _ s Lcp Heff Hpml Htm)).
    rewrite add_sub_cancel. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgtda). cbn match.
  match goal with |- exec (Defs.bind0 ?A _) s = _ =>
    assert (HAbody : exec A s = Some (tt, s')) end.
  { rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s')).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s')).
    rewrite Lcp'.
    rewrite (exec_bind_Some _ _ _ _ _ Heff').
    replace (pow2 (plat_cache_block_size_exp)) with 64
      by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ Hphys). cbn match. apply exec_returnm. }
  unfold Defs.bind0. rewrite (exec_bind_Some _ _ _ _ _ HAbody).
  apply exec_returnM.
Qed.

Lemma goodmb_execute_ZICBOP_u_ok (Dr Dw : register -> bool) (cbop : cbop_zicbop)
    (rs1 : mword 5) (offset : mword 12) (md : SATPMode) (pa : mword 64)
    (rr : result Phys_Mem_Access_Info ExceptionType) (s s' : mstate) mm :
  (uint rs1 <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rs1))) = true) ->
  Dr mstatus = true -> Dr cur_privilege = true ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  goodmb Dr Dw (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s.(sregs)) User) s mm = true ->
  exec (get_pmlen (CacheAccess (CB_prefetch cbop)) User) s = Some (0, s) ->
  goodmb Dr Dw (get_pmlen (CacheAccess (CB_prefetch cbop)) User) s mm = true ->
  exec (translationMode User) s = Some (md, s) ->
  goodmb Dr Dw (translationMode User) s mm = true ->
  exec (translateAddr (Virtaddr (ca_blk rs1 offset s))
          (CacheAccess (CB_prefetch cbop))) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  goodmb Dr Dw (translateAddr (Virtaddr (ca_blk rs1 offset s))
          (CacheAccess (CB_prefetch cbop))) s mm = true ->
  register_lookup cur_privilege s'.(sregs) = User ->
  exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s'.(sregs)) User) s' = Some (User, s') ->
  goodmb Dr Dw (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s'.(sregs)) User) s' mm = true ->
  exec (phys_access_check (CacheAccess (CB_prefetch cbop)) PBMT_PMA User
          (Physaddr pa) 64 false) s' = Some (rr, s') ->
  goodmb Dr Dw (phys_access_check (CacheAccess (CB_prefetch cbop)) PBMT_PMA User
          (Physaddr pa) 64 false) s' mm = true ->
  goodmb Dr Dw (execute (ZICBOP (cbop, Regidx rs1, offset))) s mm = true.
Proof.
  intros HDrs HDms HDcp Lcp Heff Heffg Hpml Hpmlg Htm Htmg Htr Htrg
         Lcp' Heff' Heffg' Hphys Hphysg.
  change (execute (ZICBOP (cbop, Regidx rs1, offset)))
    with (execute_ZICBOP cbop (Regidx rs1) offset).
  unfold execute_ZICBOP.
  erewrite (gm_bind Dr Dw _ _ s s mm _
              (goodmb_rX_bits_gpr Dr Dw rs1 s mm HDrs) (exec_rX_bits_gpr rs1 s)).
  cbn zeta.
  match goal with
  | |- goodmb _ _ (Defs.bind (get_transformed_data_addr _ ?off _ _) _) _ _ = _ =>
      assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) off
                        (CacheAccess (CB_prefetch cbop))
                        (pow2 (plat_cache_block_size_exp))) s
                      = Some (Ext_DataAddr_OK (Virtaddr (ca_blk rs1 offset s)), s));
      [ | assert (Hgtdag : goodmb Dr Dw (get_transformed_data_addr (Regidx rs1) off
                        (CacheAccess (CB_prefetch cbop))
                        (pow2 (plat_cache_block_size_exp))) s mm = true) ]
  end.
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 _
               (CacheAccess (CB_prefetch cbop))
               (pow2 (plat_cache_block_size_exp)) s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u
               (CacheAccess (CB_prefetch cbop)) md _ s Lcp Heff Hpml Htm)).
    rewrite add_sub_cancel. apply exec_returnm. }
  { unfold get_transformed_data_addr.
    assert (Hedgag : goodmb Dr Dw (ext_data_get_addr (Regidx rs1)
                       (ca_off rs1 offset s)
                       (CacheAccess (CB_prefetch cbop))
                       (pow2 (plat_cache_block_size_exp))) s mm = true).
    { unfold ext_data_get_addr.
      erewrite (gm_bind Dr Dw _ _ s s mm _
                  (goodmb_rX_bits_gpr Dr Dw rs1 s mm HDrs) (exec_rX_bits_gpr rs1 s)).
      apply goodmb_returnm. }
    erewrite (gm_bind Dr Dw _ _ s s mm _ Hedgag
                (exec_ext_data_get_addr_gpr rs1 _
                   (CacheAccess (CB_prefetch cbop))
                   (pow2 (plat_cache_block_size_exp)) s)).
    cbn match.
    erewrite (gm_bind Dr Dw _ _ s s mm _
                (goodmb_transform_effective_address_u Dr Dw
                   (CacheAccess (CB_prefetch cbop)) md _ s mm HDms HDcp Lcp
                   Heff Heffg Hpml Hpmlg Htm Htmg)
                (exec_transform_effective_address_u
                   (CacheAccess (CB_prefetch cbop)) md _ s Lcp Heff Hpml Htm)).
    apply goodmb_returnm. }
  erewrite (gm_bind Dr Dw _ _ s s mm _ Hgtdag Hgtda). cbn match.
  match goal with |- goodmb _ _ (Defs.bind0 ?A _) s mm = _ =>
    assert (HAe : exec A s = Some (tt, s'));
    [ | assert (HAg : goodmb Dr Dw A s mm = true) ] end.
  { rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s')).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s')).
    rewrite Lcp'.
    rewrite (exec_bind_Some _ _ _ _ _ Heff').
    replace (pow2 (plat_cache_block_size_exp)) with 64
      by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ Hphys). cbn match. apply exec_returnm. }
  { erewrite (gm_bind Dr Dw _ _ s s' mm _ Htrg Htr). cbn match.
    gmm_rr mstatus HDms.
    gmm_rr cur_privilege HDcp. rewrite Lcp'.
    erewrite (gm_bind Dr Dw _ _ s' s' mm User Heffg' Heff').
    replace (pow2 (plat_cache_block_size_exp)) with 64
      by (vm_compute; reflexivity).
    erewrite (gm_bind Dr Dw _ _ s' s' mm rr Hphysg Hphys). cbn match.
    apply goodmb_returnm. }
  erewrite (gm_bind0 Dr Dw _ _ s s' mm HAg HAe).
  apply goodmb_returnm.
Qed.

Lemma exec_execute_ZICBOP_u_err (cbop : cbop_zicbop) (rs1 : mword 5)
    (offset : mword 12) (md : SATPMode) (e : ExceptionType) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (CacheAccess (CB_prefetch cbop)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  exec (translateAddr (Virtaddr (ca_blk rs1 offset s))
          (CacheAccess (CB_prefetch cbop))) s = Some (Err (e, tt), s) ->
  exec (execute (ZICBOP (cbop, Regidx rs1, offset))) s = Some (RETIRE_SUCCESS, s).
Proof.
  intros Lcp Heff Hpml Htm Htr.
  change (execute (ZICBOP (cbop, Regidx rs1, offset)))
    with (execute_ZICBOP cbop (Regidx rs1) offset).
  unfold execute_ZICBOP.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). cbn zeta.
  match goal with
  | |- exec (Defs.bind (get_transformed_data_addr _ ?off _ _) _) _ = _ =>
      assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) off
                        (CacheAccess (CB_prefetch cbop))
                        (pow2 (plat_cache_block_size_exp))) s
                      = Some (Ext_DataAddr_OK (Virtaddr (ca_blk rs1 offset s)), s))
  end.
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 _
               (CacheAccess (CB_prefetch cbop))
               (pow2 (plat_cache_block_size_exp)) s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u
               (CacheAccess (CB_prefetch cbop)) md _ s Lcp Heff Hpml Htm)).
    rewrite add_sub_cancel. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgtda). cbn match.
  match goal with |- exec (Defs.bind0 ?A _) s = _ =>
    assert (HAbody : exec A s = Some (tt, s)) end.
  { rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match. apply exec_returnm. }
  unfold Defs.bind0. rewrite (exec_bind_Some _ _ _ _ _ HAbody).
  apply exec_returnM.
Qed.

Lemma goodmb_execute_ZICBOP_u_err (Dr Dw : register -> bool) (cbop : cbop_zicbop)
    (rs1 : mword 5) (offset : mword 12) (md : SATPMode) (e : ExceptionType)
    (s : mstate) mm :
  (uint rs1 <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rs1))) = true) ->
  Dr mstatus = true -> Dr cur_privilege = true ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  goodmb Dr Dw (effectivePrivilege (CacheAccess (CB_prefetch cbop))
          (register_lookup mstatus s.(sregs)) User) s mm = true ->
  exec (get_pmlen (CacheAccess (CB_prefetch cbop)) User) s = Some (0, s) ->
  goodmb Dr Dw (get_pmlen (CacheAccess (CB_prefetch cbop)) User) s mm = true ->
  exec (translationMode User) s = Some (md, s) ->
  goodmb Dr Dw (translationMode User) s mm = true ->
  exec (translateAddr (Virtaddr (ca_blk rs1 offset s))
          (CacheAccess (CB_prefetch cbop))) s = Some (Err (e, tt), s) ->
  goodmb Dr Dw (translateAddr (Virtaddr (ca_blk rs1 offset s))
          (CacheAccess (CB_prefetch cbop))) s mm = true ->
  goodmb Dr Dw (execute (ZICBOP (cbop, Regidx rs1, offset))) s mm = true.
Proof.
  intros HDrs HDms HDcp Lcp Heff Heffg Hpml Hpmlg Htm Htmg Htr Htrg.
  change (execute (ZICBOP (cbop, Regidx rs1, offset)))
    with (execute_ZICBOP cbop (Regidx rs1) offset).
  unfold execute_ZICBOP.
  erewrite (gm_bind Dr Dw _ _ s s mm _
              (goodmb_rX_bits_gpr Dr Dw rs1 s mm HDrs) (exec_rX_bits_gpr rs1 s)).
  cbn zeta.
  match goal with
  | |- goodmb _ _ (Defs.bind (get_transformed_data_addr _ ?off _ _) _) _ _ = _ =>
      assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) off
                        (CacheAccess (CB_prefetch cbop))
                        (pow2 (plat_cache_block_size_exp))) s
                      = Some (Ext_DataAddr_OK (Virtaddr (ca_blk rs1 offset s)), s));
      [ | assert (Hgtdag : goodmb Dr Dw (get_transformed_data_addr (Regidx rs1) off
                        (CacheAccess (CB_prefetch cbop))
                        (pow2 (plat_cache_block_size_exp))) s mm = true) ]
  end.
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 _
               (CacheAccess (CB_prefetch cbop))
               (pow2 (plat_cache_block_size_exp)) s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u
               (CacheAccess (CB_prefetch cbop)) md _ s Lcp Heff Hpml Htm)).
    rewrite add_sub_cancel. apply exec_returnm. }
  { unfold get_transformed_data_addr.
    assert (Hedgag : goodmb Dr Dw (ext_data_get_addr (Regidx rs1)
                       (ca_off rs1 offset s)
                       (CacheAccess (CB_prefetch cbop))
                       (pow2 (plat_cache_block_size_exp))) s mm = true).
    { unfold ext_data_get_addr.
      erewrite (gm_bind Dr Dw _ _ s s mm _
                  (goodmb_rX_bits_gpr Dr Dw rs1 s mm HDrs) (exec_rX_bits_gpr rs1 s)).
      apply goodmb_returnm. }
    erewrite (gm_bind Dr Dw _ _ s s mm _ Hedgag
                (exec_ext_data_get_addr_gpr rs1 _
                   (CacheAccess (CB_prefetch cbop))
                   (pow2 (plat_cache_block_size_exp)) s)).
    cbn match.
    erewrite (gm_bind Dr Dw _ _ s s mm _
                (goodmb_transform_effective_address_u Dr Dw
                   (CacheAccess (CB_prefetch cbop)) md _ s mm HDms HDcp Lcp
                   Heff Heffg Hpml Hpmlg Htm Htmg)
                (exec_transform_effective_address_u
                   (CacheAccess (CB_prefetch cbop)) md _ s Lcp Heff Hpml Htm)).
    apply goodmb_returnm. }
  erewrite (gm_bind Dr Dw _ _ s s mm _ Hgtdag Hgtda). cbn match.
  match goal with |- goodmb _ _ (Defs.bind0 ?A _) s mm = _ =>
    assert (HAe : exec A s = Some (tt, s));
    [ | assert (HAg : goodmb Dr Dw A s mm = true) ] end.
  { rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match. apply exec_returnm. }
  { erewrite (gm_bind Dr Dw _ _ s s mm _ Htrg Htr). cbn match.
    apply goodmb_returnm. }
  erewrite (gm_bind0 Dr Dw _ _ s s mm HAg HAe).
  apply goodmb_returnm.
Qed.

(* the landing file of a walk agrees with its entry file on [u_Dfix]: [tlb]
   is deliberately NOT in [u_Dfix], so a TLB fill is invisible here. *)
Lemma ca_fix_land (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) ->
  reg_agree_on u_Dfix rs' rs.
Proof.
  intros [-> | (tv & ->)]; [ apply u_fix_refl |].
  intros r Hr. apply irrelevant_register_set.
  destruct (register_beq r tlb) eqn:Hb; [| reflexivity].
  exfalso. apply register_beq_true in Hb. subst r. exact (u_fix_tlb Hr).
Qed.

Section ZicbopArm.
  Context (pt : uptd).

  Lemma arm_ZICBOP_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (p : cbop_zicbop * regidx * bits 12) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode w) (u_state rsf mm) = Some (ZICBOP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (ZICBOP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hcfg Hag Hdec Hhv Hpins Hwf.
    destruct p as [[cbop rs1] offset]. destruct rs1 as [rs1].
    (* the pins, moved across the nextPC tick *)
    pose proof (UserTotalU.u_pins_tick pt t rsf va 4 Hpins) as Hpinsx.
    pose proof (UserTotalU.u_agree_tick rsf mm va 4 Hag) as Hagx.
    destruct Hcfg as (_ & Lcp0 & Hms0 & Lmenv0 & _ & _).
    pose proof Hms0 as (Lsxl0 & Lmprv0 & Lmxr0 & _).
    pose proof Hpinsx as (Hhw & Hcfgp & Hpt & Htlbok).
    destruct Hhw as (Hmisa & _ & Hsenv & Hhtif & Hall & _).
    destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
    pose proof Hsatpok as (Hmode & _ & _ & _).
    assert (Lcp : register_lookup cur_privilege
              (register_set nextPC (add_vec_int va 4) rsf) = User)
      by (rewrite (UserTotalU.u_tick_reg cur_privilege rsf va 4 eq_refl); exact Lcp0).
    assert (Lms : register_lookup mstatus
              (register_set nextPC (add_vec_int va 4) rsf)
              = register_lookup mstatus rsf)
      by (apply (UserTotalU.u_tick_reg (R_bitvector_64 mstatus) rsf va 4 eq_refl)).
    assert (Lmenv : register_lookup menvcfg
              (register_set nextPC (add_vec_int va 4) rsf) = MENVCFG_S)
      by (rewrite (UserTotalU.u_tick_reg (R_bitvector_64 menvcfg) rsf va 4 eq_refl); exact Lmenv0).
    assert (Hdcfg : u_data_cfg (register_set nextPC (add_vec_int va 4) rsf)).
    { split_and!; [ exact Lcp | rewrite Lms; exact Hms0 | exact Lmenv ]. }
    (* the four read-only probes at the execute state *)
    assert (Htm : exec (translationMode User)
              (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
              = Some (Sv39, u_state (register_set nextPC (add_vec_int va 4) rsf) mm))
      by (apply (exec_translationMode_U_sv39 usatp);
          [ rewrite u_state_sregs Lms; exact Lsxl0
          | rewrite u_state_sregs; exact Hsatp | exact Hmode ]).
    assert (Htmg : goodmb Du_r Du_w (translationMode User)
              (u_state (register_set nextPC (add_vec_int va 4) rsf) mm) mm = true).
    { apply goodmb_of_goodb.
      apply (goodb_translationMode_U Du_r usatp);
        [ vm_compute; reflexivity | vm_compute; reflexivity
        | rewrite u_state_sregs Lms; exact Lsxl0
        | rewrite u_state_sregs; exact Hsatp | exact Hmode ]. }
    assert (Heff : exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
              (register_lookup mstatus
                 (u_state (register_set nextPC (add_vec_int va 4) rsf) mm).(sregs)) User)
              (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
              = Some (User, u_state (register_set nextPC (add_vec_int va 4) rsf) mm)).
    { apply exec_effectivePrivilege_mprv0. rewrite u_state_sregs Lms. exact Lmprv0. }
    assert (Heffg : goodmb Du_r Du_w (effectivePrivilege (CacheAccess (CB_prefetch cbop))
              (register_lookup mstatus
                 (u_state (register_set nextPC (add_vec_int va 4) rsf) mm).(sregs)) User)
              (u_state (register_set nextPC (add_vec_int va 4) rsf) mm) mm = true).
    { apply goodmb_effectivePrivilege_mprv0. rewrite u_state_sregs Lms. exact Lmprv0. }
    assert (Hneq1 : generic_neq (CacheAccess (CB_prefetch cbop) : MemoryAccessType mem_payload) (InstructionFetch tt) = true)
      by (destruct cbop; vm_compute; reflexivity).
    assert (Hneq2 : generic_neq (CacheAccess (CB_prefetch cbop) : MemoryAccessType mem_payload) (Load PageTableEntry) = true)
      by (destruct cbop; vm_compute; reflexivity).
    assert (Hneq3 : generic_neq (CacheAccess (CB_prefetch cbop) : MemoryAccessType mem_payload) (Store PageTableEntry) = true)
      by (destruct cbop; vm_compute; reflexivity).
    assert (Hpml : exec (get_pmlen (CacheAccess (CB_prefetch cbop)) User)
              (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
              = Some (0, u_state (register_set nextPC (add_vec_int va 4) rsf) mm)).
    { apply exec_get_pmlen_u; try assumption;
        rewrite u_state_sregs; first [ rewrite Lms; exact Lmxr0 | assumption ]. }
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (CacheAccess (CB_prefetch cbop)) User)
              (u_state (register_set nextPC (add_vec_int va 4) rsf) mm) mm = true).
    { apply u_gm_pmlen; try assumption;
        rewrite u_state_sregs; first [ rewrite Lms; exact Lmxr0 | assumption ]. }
    (* the runtime block address, classified *)
    pose proof Hwf as (md0 & _ & _ & _ & _ & _ & Haccwf & _ & _).
    destruct (ca_classify cbop (ud_tfp pt) (ud_um pt)
                (ca_blk rs1 offset
                   (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)) Haccwf)
      as [Hok | Hflt].
    - (* MAPPED and permitted: the walk succeeds, the physical check grants *)
      destruct Hok as (w0 & Hm & Hleaf & Hcanon).
      destruct (u_walk_pure_gen (CacheAccess (CB_prefetch cbop)) pt t mm
                  (register_set nextPC (add_vec_int va 4) rsf) w0
                  (ca_blk rs1 offset
                     (u_state (register_set nextPC (add_vec_int va 4) rsf) mm))
                  (fun s => exec_is_shadow_stack_ca cbop s)
                  (fun Db s => goodb_is_shadow_stack_ca Db cbop s)
                  (fun a d mxr ds Db s =>
                     goodb_check_PTE_permission_ca cbop _ mxr ds Db s (Hleaf a d mxr ds))
                  Hm Hleaf Hcanon Hdcfg Hpinsx Hwf)
        as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hdcfg' & Hpins' & Hwf').
      (* the physical access check at the landing state *)
      assert (Halb : is_aligned_vaddr (Virtaddr (ca_blk rs1 offset
                (u_state (register_set nextPC (add_vec_int va 4) rsf) mm))) 64 = true).
      { replace 64 with (pow2 (plat_cache_block_size_exp)) by (vm_compute; reflexivity).
        apply block_aligned. }
      destruct (u_data_ram pt t' mm' 64 w0 _ ltac:(lia) ltac:(exists 64; reflexivity)
                  Halb Hwf' Hm) as (Hram0 & Hram63).
      pose proof Hdcfg' as (Lcp' & Lms' & Lmenv').
      destruct Lms' as (Lsxl' & Lmprv' & _).
      destruct Hpins' as (Hhw' & _ & Hpt' & _).
      destruct Hhw' as (_ & _ & _ & _ & Hall' & _).
      destruct Hpt' as (_ & HA' & Hord' & HX' & HW' & HR' & Hcovp').
      destruct (pma_all_ram Hall' _ 64
                  (pma_access_ram _ 64 (Z.to_nat 64 - 1) Hram0 Hram63
                     (pma_width_ok 64 eq_refl eq_refl)
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)))
        as (region & Hpmam & Hxr & Hrr & Hwr & _).
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n rs') 0)) 4)
                (uint (u_walk_pa w0 (ca_blk rs1 offset
                   (u_state (register_set nextPC (add_vec_int va 4) rsf) mm))))
                (uint (to_bits 64 64)) = PMP_Match).
      { pose proof Hram0 as [Halo Hahi]. pose proof Hram63 as [_ Hhilast].
        replace (Z.to_nat 64 - 1)%nat with 63%nat in Hhilast
          by (vm_compute; reflexivity).
        assert (Hnw : uint (u_walk_pa w0 (ca_blk rs1 offset
                        (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)))
                      + Z.of_nat 63 < 18446744073709551616).
        { rewrite uint_unsigned in Hahi. rewrite uint_unsigned.
          unfold ram_base, ram_size in Hahi. lia. }
        rewrite (uint_pa_add _ 63 Hnw) in Hhilast.
        assert (Hfit : uint (u_walk_pa w0 (ca_blk rs1 offset
                         (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)))
                       + 64 <= ram_base + ram_size) by lia.
        exact (ram_pmp_match_w _ _ 64 ltac:(lia) ltac:(vm_compute; reflexivity)
                 Halo Hfit Hcovp'). }
      assert (Halgnp : is_aligned_paddr (Physaddr (u_walk_pa w0 (ca_blk rs1 offset
                 (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)))) 64 = true)
        by exact (pa_aligned_div _ _ 64 ltac:(lia) ltac:(exists 64; reflexivity) Halb).
      assert (Hphys : exec (phys_access_check (CacheAccess (CB_prefetch cbop)) PBMT_PMA
                User (Physaddr (u_walk_pa w0 (ca_blk rs1 offset
                  (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)))) 64 false)
                (u_state rs' mm') = Some (Ok pma_ok_aligned, u_state rs' mm'))
        by exact (exec_phys_access_check_ca cbop PBMT_PMA _ region 64 (u_state rs' mm')
                    HA' Hord' Hrange HX' HW' HR' Hpmam Halgnp Hxr Hrr Hwr).
      assert (Hphysg : goodmb Du_r Du_w
                (phys_access_check (CacheAccess (CB_prefetch cbop)) PBMT_PMA
                   User (Physaddr (u_walk_pa w0 (ca_blk rs1 offset
                     (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)))) 64 false)
                (u_state rs' mm') mm = true)
        by exact (goodmb_phys_access_check_ca Du_r Du_w cbop PBMT_PMA _ region 64
                    (u_state rs' mm') mm
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    HA' Hord' Hrange HX' HW' HR' Hpmam Halgnp Hxr Hrr Hwr).
      assert (Heff' : exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
                (register_lookup mstatus (u_state rs' mm').(sregs)) User)
                (u_state rs' mm') = Some (User, u_state rs' mm'))
        by (apply exec_effectivePrivilege_mprv0; rewrite u_state_sregs; exact Lmprv').
      assert (Heffg' : goodmb Du_r Du_w (effectivePrivilege (CacheAccess (CB_prefetch cbop))
                (register_lookup mstatus (u_state rs' mm').(sregs)) User)
                (u_state rs' mm') mm = true)
        by (apply goodmb_effectivePrivilege_mprv0; rewrite u_state_sregs; exact Lmprv').
      apply (finish_mem_base pt t t' mm rsf va
               (ZICBOP (cbop, Regidx rs1, offset)) RETIRE_SUCCESS w
               (u_state rs' mm') Hdec Hhv eq_refl).
      + exact (exec_execute_ZICBOP_u_ok cbop rs1 offset Sv39 _ (Ok pma_ok_aligned)
                 (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
                 (u_state rs' mm')
                 ltac:(rewrite u_state_sregs; exact Lcp) Heff Hpml Htm Htr
                 ltac:(rewrite u_state_sregs; exact Lcp') Heff' Hphys).
      + exact (goodmb_execute_ZICBOP_u_ok Du_r Du_w cbop rs1 offset Sv39 _
                 (Ok pma_ok_aligned)
                 (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
                 (u_state rs' mm') mm
                 (fun H => Du_gpr_of_Z_r rs1 H)
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                 ltac:(rewrite u_state_sregs; exact Lcp) Heff Heffg Hpml Hpmlg Htm Htmg
                 Htr Htrg ltac:(rewrite u_state_sregs; exact Lcp') Heff' Heffg' Hphys Hphysg).
      + exact u_ok_retire.
      + exact I.
      + rewrite u_state_sregs. exact (ca_fix_land _ rs' Hfile).
      + rewrite u_state_sregs. exact Htlbok'.
      + rewrite u_state_mem. exact Hstep.
    - (* the translation FAULTS: the prefetch is a nop and nothing moves *)
      destruct (u_translate_fault_pure pt t mm
                  (register_set nextPC (add_vec_int va 4) rsf)
                  (CacheAccess (CB_prefetch cbop))
                  (match cbop with
                   | PREFETCH_R => E_Load_Page_Fault tt
                   | PREFETCH_W => E_SAMO_Page_Fault tt
                   | PREFETCH_I => E_Fetch_Page_Fault tt end)
                  (ca_blk rs1 offset
                     (u_state (register_set nextPC (add_vec_int va 4) rsf) mm))
                  Hflt
                  (exec_translationException_ca_pf cbop (PTW_Invalid_Addr tt) _
                     (or_introl eq_refl))
                  (exec_translationException_ca_pf cbop (PTW_Invalid_PTE tt) _
                     (or_intror (or_introl eq_refl)))
                  (exec_translationException_ca_pf cbop (PTW_No_Permission tt) _
                     (or_intror (or_intror eq_refl)))
                  Heff (exec_is_shadow_stack_ca cbop _) Lcp
                  ltac:(rewrite Lms; exact Lsxl0) Hpinsx
                  (u_mem_wf_ok pt t mm Hwf))
        as (Htr & Htrg).
      apply (finish_mem_base pt t t mm rsf va
               (ZICBOP (cbop, Regidx rs1, offset)) RETIRE_SUCCESS w
               (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
               Hdec Hhv eq_refl).
      + exact (exec_execute_ZICBOP_u_err cbop rs1 offset Sv39 _
                 (u_state (register_set nextPC (add_vec_int va 4) rsf) mm)
                 ltac:(rewrite u_state_sregs; exact Lcp) Heff Hpml Htm Htr).
      + exact (goodmb_execute_ZICBOP_u_err Du_r Du_w cbop rs1 offset Sv39 _
                 (u_state (register_set nextPC (add_vec_int va 4) rsf) mm) mm
                 (fun H => Du_gpr_of_Z_r rs1 H)
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                 ltac:(rewrite u_state_sregs; exact Lcp) Heff Heffg Hpml Hpmlg
                 Htm Htmg Htr Htrg).
      + exact u_ok_retire.
      + exact I.
      + rewrite u_state_sregs. apply u_fix_refl.
      + rewrite u_state_sregs. exact Htlbok.
      + rewrite u_state_mem. exact (u_mem_step_refl pt t mm Hwf).
  Qed.

End ZicbopArm.
