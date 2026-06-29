(* WpEntry.v — extending the kernel-boot WP to all of _entry (auipc; ld; lui;
   csrr; addi; mul; add; jal start).  This file builds the RVC fetch path and
   the per-opcode step lemmas for the new instructions. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.

(* ---------------------------------------------------------------------- *)
(* RVC fetch: a 4-byte-aligned 16-bit instruction reads 4 bytes and takes  *)
(* the F_RVC branch (low 16 bits).  Mirror of exec_fetch_done with isRVC=1. *)
(* ---------------------------------------------------------------------- *)

Section FetchRVC.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.

  Lemma exec_fetch_RVC_4 : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s).
  Proof using All.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_4 pc region w s HpcPC Hpriv Hpmp Hmatch Hexec Hc Hsig Hh Hbytes Hvalign)).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

End FetchRVC.

(* ---------------------------------------------------------------------- *)
(* currentlyEnabled Ext_Zca = true (needs the C extension enabled in misa). *)
(* ---------------------------------------------------------------------- *)

Lemma exec_hartSupports_Zca s : exec (hartSupports Ext_Zca) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zca) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

(* reduce one const-arm hartSupports leaf [_rec_hartSupports X k acc] to Some(b,s). *)
Ltac ehs_leaf s :=
  match goal with
  | |- exec (_rec_hartSupports ?e ?k ?a) s = _ =>
      destruct a; cbn [_rec_hartSupports]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?x 0] =>
        replace (Z.geb x 0) with true by (vm_compute; reflexivity) end;
      cbn match; rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s));
      apply exec_returnM
  end.

(* hartSupports Ext_C = true: mirror of run_hartSupports_C at the exec level. *)
Lemma exec_hartSupports_C s : exec (hartSupports Ext_C) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_C) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* and_boolM Zca (and_boolM A B) ; Zca = true *)
  erewrite exec_and_boolM_Some; [| ehs_leaf s]. cbn match.
  (* and_boolM A B *)
  erewrite exec_and_boolM_Some.
  2:{ (* A = or_boolM Zcf (or_boolM (F>>=not) (returnM (neq xlen 32))) *)
      erewrite exec_or_boolM_Some; [| ehs_leaf s]. cbn match.   (* Zcf=false *)
      erewrite exec_or_boolM_Some.
      2:{ erewrite exec_bind_Some; [| ehs_leaf s]. apply exec_returnM. }   (* F=true -> not=false *)
      cbn match. apply exec_returnM. }
  (* A's value is [neq_int xlen 32]; make it concrete then take B *)
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  (* B = or_boolM Zcd (..) = true (Zcd = true) *)
  erewrite exec_or_boolM_Some; [| ehs_leaf s]. reflexivity.
Qed.

(* currentlyEnabled Ext_C = (misa.C bit), at any Acc level. *)
Lemma exec_rec_cE_C_misa (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true ->
  exec (_rec_currentlyEnabled Ext_C k acc) s
    = Some (eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_C s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Zca s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s).
Proof.
  intro HC. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zca) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zca s)). cbn match.
  rewrite (exec_or_boolM_Some _ _ _ _ _
            (exec_rec_cE_C_misa (currentlyEnabled_measure Ext_Zca - 1) _ s
               ltac:(vm_compute; reflexivity))).
  rewrite HC. cbn match. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* run_hart_active reduction for the F_RVC (compressed) branch.            *)
(* Mirror of exec_hart_active_progress; nextPC := pc+2, decode via         *)
(* ext_decode_compressed, gated on currentlyEnabled Ext_Zca = true.        *)
(* ---------------------------------------------------------------------- *)

Section HartActiveRVC.
  Context (s s_x : mstate) (h : mword 16) (instr other : instruction)
          (pc : mword 64) (resf : ExecutionResult).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hdisp : exec (dispatchInterrupt Machine) s = Some (None, s).
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_RVC h, s).
  Hypothesis Hdec : exec (ext_decode_compressed h) s = Some (instr, s).
  Hypothesis Hlpad : eq_vec (register_lookup elp s.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis HpcF : register_lookup PC s.(sregs) = pc.
  Hypothesis Hzca : exec (currentlyEnabled Ext_Zca) s = Some (true, s).
  Let s_pc : mstate := set_reg s nextPC (add_vec_int pc 2).
  (* RVC instructions expand via [ExecuteAs] to a base instruction [other]. *)
  Hypothesis Hexec : exec (execute instr) s_pc = Some (ExecuteAs other, s_pc).
  Hypothesis Hexec2 : exec (execute other) s_pc = Some (resf, s_x).

  Lemma exec_hart_active_progress_RVC :
    exec (run_hart_active 0) s
    = Some (Step_Execute (resf, zero_extend' 32 h), s_x).
  Proof using All.
    unfold run_hart_active.
    rewrite exec_catch_early_return.
    rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
    rewrite execR_bind execR_liftR Hdisp. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    rewrite execR_liftR Hfetch. cbn match. cbn match.
    unfold ext_fetch_hook. cbn match. cbn beta iota.
    rewrite execR_bind execR_liftR Hdec. cbn match.
    unfold get_config_print_instr. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    (* is_landing_pad_expected -> false (plain, no and_boolM in the RVC branch) *)
    rewrite execR_liftR exec_is_landing_pad Hlpad. cbn match.
    (* currentlyEnabled Ext_Zca -> true *)
    rewrite execR_bind execR_liftR Hzca. cbn match.
    (* read PC -> pc ; write nextPC (pc+2) ; execute instr -> ExecuteAs other *)
    rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
    fold s_pc. rewrite execR_liftR Hexec. cbn match. cbn match.
    (* w11 = ExecuteAs other -> liftR (execute other) -> resf, fed to Step_Execute *)
    rewrite execR_bind execR_liftR Hexec2. cbn match.
    rewrite execR_returnR. cbn match. reflexivity.
  Qed.

End HartActiveRVC.

(* ==== compressed decode: walker + decode_C_lui ==== *)
Definition h_lui : mword 16 := mword_of_int 0x6505.

(* a cE-Zca decode clause whose pattern is false collapses the and_boolM to false. *)
Lemma exec_cezca_false s pat :
  eq_vec (_get_Misa_C (register_lookup misa (sregs s))) ('b"1") = true ->
  pat = false ->
  exec (Defs.and_boolM (currentlyEnabled Ext_Zca) (returnM pat)) s = Some (false, s).
Proof.
  intros HmisaC Hpat.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zca s HmisaC)).
  cbn match. rewrite Hpat. apply exec_returnm.
Qed.

(* and_boolM of two true-reducing computations (no cbn -> no driving into cE Zca). *)
Lemma exec_returnM_true (b : bool) s : b = true -> exec (returnM b) s = Some (true, s).
Proof. intro H. rewrite exec_returnm. rewrite H. reflexivity. Qed.
Lemma exec_andM_true (l r : M bool) s :
  exec l s = Some (true, s) -> exec r s = Some (true, s) ->
  exec (Defs.and_boolM l r) s = Some (true, s).
Proof. intros Hl Hr. rewrite (exec_and_boolM_Some _ _ _ _ _ Hl). exact Hr. Qed.

(* reduce a settled bool-guard WITHOUT cbn (which would drive exec into cE Zca). *)
Lemma exec_if_true {X} (A B : M X) s : exec (if true then A else B) s = exec A s.
Proof. reflexivity. Qed.
Lemma exec_if_false {X} (A B : M X) s : exec (if false then A else B) s = exec B s.
Proof. reflexivity. Qed.

(* HEAD-position guarded if-elimination, for walking a deep nested-if decision
   tree (e.g. [read_CSR]/[write_CSR]'s ~90-way CSR-address dispatch).  The
   obvious idiom
     [repeat (match goal with |- context[if ?g then _ else _] =>
              replace g with false by (vm_compute; reflexivity) end; cbn match)]
   is O(#clauses^2): every iteration re-scans the whole (huge) goal for [context]
   and then [cbn match]-traverses it.  Rewriting at the HEAD instead
     [repeat (erewrite exec_if_false_g by (vm_compute; reflexivity))]
   peels one guard per step with no goal-wide scan and no [cbn match], leaving the
   goal in the same shape (the matching [if g then _ else _] at head).  See the
   "Build-perf note" in README.md. *)
Lemma exec_if_false_g {X} (g : bool) (A B : M X) s :
  g = false -> exec (if g then A else B) s = exec B s.
Proof. intros ->. reflexivity. Qed.

(* walk one non-matching level of the nested compressed-decode tree. *)
Ltac cstep s HmisaC :=
  first
  [ match goal with
    | |- context[Defs.bind (Defs.and_boolM (currentlyEnabled Ext_Zca) (returnM ?pat)) _] =>
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_cezca_false s pat HmisaC ltac:(vm_compute; reflexivity)));
        cbn match
    end
  | match goal with |- context[if ?g then _ else returnM None] =>
      replace g with false by (vm_compute; reflexivity) end; cbn match
  | match goal with |- context[if ?g then _ else _] =>
      replace g with false by (vm_compute; reflexivity) end; cbn match ].

Definition imm_clui : mword 6 :=
  concat_vec (subrange_vec_dec h_lui 12 12) (subrange_vec_dec h_lui 6 2).
Definition rd_clui : regidx :=
  Regidx (autocast (T := mword)
            (subrange_vec_dec (subrange_vec_dec h_lui 11 7) (Z.sub regidx_bit_width 1) 0)).

Lemma decode_C_lui s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed h_lui) s = Some (C_LUI (imm_clui, rd_clui), s).
Proof.
  intro HmisaC. unfold imm_clui, rd_clui.
  unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
  skip_pure_clause.                 (* C_NTL: pure guard false (flat) *)
  do 11 (cstep s HmisaC).
  (* encdec_reg_backwards (subrange 11 7) -> Regidx rd, reduced in ISOLATION
     (so it stays folded in the main goal and cbn match below cannot drive
     exec through it into cE Zca). *)
  assert (Hrd : exec (encdec_reg_backwards (subrange_vec_dec h_lui 11 7)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec h_lui 11 7)
                           (Z.sub regidx_bit_width 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. apply exec_returnM. }
  (* C_LUI clause: outer guard true -> BODY ; cbn match stops at folded encdec_reg *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  (* peel the OUTER clause bind (the [match Some/None]) to expose the body *)
  rewrite exec_bind.
  (* body: peel encdec_reg (folded -> via Hrd), then the w51 and_boolM (=true) *)
  rewrite (exec_bind_Some _ _ _ _ _ Hrd). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                          (currentlyEnabled Ext_Zca))) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply (exec_currentlyEnabled_Zca s HmisaC). }
  cbn beta iota.
  (* body = returnM (Some C_LUI) ; collapse the outer match -> returnM C_LUI *)
  rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
Qed.

(* ==== execute lemmas (generic register write) ==== *)

(* write any GPR (given the reflexivity equation for its concrete index). *)
Lemma exec_wX_bits_at (i : mword 5) (r : register_bitvector_64) s (v : mword 64) :
  wX (Regno (uint i)) v
    = Defs.bind0 (Defs.write_reg (R_bitvector_64 r) (regval_into_reg v)) (returnM tt) ->
  exec (wX_bits (Regidx i) v) s = Some (tt, set_reg s (R_bitvector_64 r) (regval_into_reg v)).
Proof.
  intro Heq. unfold wX_bits. rewrite Heq.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bitvector_64 r) _ s)).
  apply exec_returnm.
Qed.

(* C_LUI decodes-and-expands to UTYPE LUI via ExecuteAs. *)
Lemma exec_execute_C_LUI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LUI (imm, rd))) s
  = Some (ExecuteAs (UTYPE (sign_extend' 20 imm, rd, LUI)), s).
Proof. unfold execute. cbn match. unfold execute_C_LUI. apply exec_returnM. Qed.

(* execute_UTYPE LUI: rd := sext(imm ++ 0x000). *)
Lemma exec_execute_UTYPE_LUI (imm : mword 20) (i : mword 5) (r : register_bitvector_64) s :
  wX (Regno (uint i)) (sign_extend' 64 (concat_vec imm ((Ox"000") : mword 12)))
    = Defs.bind0 (Defs.write_reg (R_bitvector_64 r)
        (regval_into_reg (sign_extend' 64 (concat_vec imm ((Ox"000") : mword 12))))) (returnM tt) ->
  exec (execute_UTYPE imm (Regidx i) LUI) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 r)
            (regval_into_reg (sign_extend' 64 (concat_vec imm ((Ox"000") : mword 12))))).
Proof.
  intro Heq. unfold execute_UTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_at i r s _ Heq)).
  apply exec_returnm.
Qed.

(* ==== generalized try_step wrapper (announce word arbitrary, for RVC) ==== *)
Section StepGen.
  Context (s s_exec : mstate) (iw : mword 32) (b : bool).
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hsi   : exec (should_inc_minstret Machine) s = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a = Some (Step_Execute (RETIRE_SUCCESS, iw), s_exec).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec : register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.
  Hypothesis Hrvfi : get_config_rvfi tt = false.
  Let s_tick : mstate := set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_riscv_step_gen : exec riscv_step s = Some (tt, s_final).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_final))).
    { reflexivity. }
    unfold try_step. cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    cbn beta. rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    unfold RETIRE_SUCCESS. cbn beta iota.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some.
            2:{ apply exec_read_reg. }
            rewrite Hhart_exec. unfold Defs.assert_exp. cbn [hart_is_active].
            reflexivity. }
        apply exec_read_reg. }
    rewrite Hhart_exec. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ reflexivity. }
        cbn beta iota. apply (exec_read_reg minstret_increment). }
    rewrite Hrvfi.
    replace (register_lookup minstret_increment
               (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs))
      with b.
    2:{ unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set;
          [ (exact Hmi_exec || (symmetry; exact Hmi_exec)) | reflexivity ]. }
    unfold s_final, s_tick.
    destruct b.
    - erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ erewrite exec_bind_Some.
              2:{ apply (exec_read_reg minstret). }
              apply exec_write_reg. }
          cbn beta iota. reflexivity. }
      reflexivity.
    - erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ cbn beta iota. reflexivity. }
          cbn beta iota. reflexivity. }
      reflexivity.
  Qed.
End StepGen.

(* ==== lui exec-step (forward_exec_lui) ==== *)
Definition i_lui : mword 5 :=
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec h_lui 11 7) (Z.sub regidx_bit_width 1) 0).
Definition luival : mword 64 :=
  sign_extend' 64 (concat_vec (sign_extend' 20 imm_clui) ((Ox"000") : mword 12)).

Lemma rd_clui_eq : rd_clui = Regidx i_lui.
Proof. reflexivity. Qed.

Lemma wX_lui_a0 (v : mword 64) :
  wX (Regno (uint i_lui)) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x10) (regval_into_reg v)) (returnM tt).
Proof. replace (uint i_lui) with 10%Z by (vm_compute; reflexivity). reflexivity. Qed.

Section ForwardLUI.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC h_lui, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAlu : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pclu : mstate := set_reg sAlu nextPC (add_vec_int pc 2).
  Definition sXlu : mstate := set_reg s_pclu (R_bitvector_64 x10) (regval_into_reg luival).
  Definition sTlu : mstate := set_reg sXlu PC (register_lookup nextPC sXlu.(sregs)).
  Definition sFlu : mstate :=
    if b then set_reg sTlu minstret (add_vec_int (register_lookup minstret sTlu.(sregs)) 1)
         else sTlu.

  Lemma forward_exec_lui :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFlu).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp Lmisa LS.
    assert (LpcA  : register_lookup PC sAlu.(sregs) = pc).
    { unfold sAlu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAlu.(sregs) = Machine).
    { unfold sAlu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAlu.(sregs) = HART_ACTIVE tt).
    { unfold sAlu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAlu.(sregs) = zeros' 64).
    { unfold sAlu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAlu.(sregs))) ('b"1") = false).
    { unfold sAlu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAlu.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAlu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa sAlu.(sregs))) ('b"1") = true).
    { unfold sAlu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (LmisaSA : eq_vec (_get_Misa_S (register_lookup misa sAlu.(sregs))) ('b"1") = true).
    { unfold sAlu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAlu = Some (None, sAlu)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAlu _ (exec_currentlyEnabled_S sAlu) LmisaSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAlu = Some (F_RVC h_lui, sAlu)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed h_lui) sAlu = Some (C_LUI (imm_clui, rd_clui), sAlu))
      by (apply decode_C_lui; exact LmisaA).
    assert (HpcPCpc : register_lookup PC s_pclu.(sregs) = pc).
    { unfold s_pclu, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LpcA | vm_compute; reflexivity ]. }
    assert (Hexec1 : exec (execute (C_LUI (imm_clui, rd_clui))) s_pclu = Some (ExecuteAs (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)), s_pclu))
      by apply exec_execute_C_LUI.
    assert (Hexec2 : exec (execute (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI))) s_pclu = Some (RETIRE_SUCCESS, sXlu)).
    { change (execute (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)))
        with (execute_UTYPE (sign_extend' 20 imm_clui) rd_clui LUI).
      rewrite rd_clui_eq. unfold sXlu, luival, s_pclu, sAlu.
      apply (exec_execute_UTYPE_LUI (sign_extend' 20 imm_clui) i_lui x10). apply wX_lui_a0. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) sAlu = Some (true, sAlu))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) sAlu = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h_lui), sXlu)).
    { exact (exec_hart_active_progress_RVC sAlu sXlu h_lui (C_LUI (imm_clui, rd_clui))
               (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hexec1 Hexec2). }
    apply (exec_riscv_step_gen s sXlu (zero_extend' 32 h_lui) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXlu, s_pclu, sAlu; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXlu, s_pclu, sAlu; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardLUI.

(* ==== add (C_ADD, RVC) ==== *)
Definition h_add : mword 16 := mword_of_int 0x912a.
Definition rsd_cadd : regidx :=
  Regidx (autocast (T := mword) (subrange_vec_dec (subrange_vec_dec h_add 11 7) (Z.sub regidx_bit_width 1) 0)).
Definition rs2_cadd : regidx :=
  Regidx (autocast (T := mword) (subrange_vec_dec (subrange_vec_dec h_add 6 2) (Z.sub regidx_bit_width 1) 0)).

Lemma decode_C_ADD s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed h_add) s = Some (C_ADD (rsd_cadd, rs2_cadd), s).
Proof.
  intro HmisaC. unfold rsd_cadd, rs2_cadd.
  assert (Hrsd : exec (encdec_reg_backwards (subrange_vec_dec h_add 11 7)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec h_add 11 7) (Z.sub regidx_bit_width 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end. cbn match. apply exec_returnM. }
  assert (Hrs2 : exec (encdec_reg_backwards (subrange_vec_dec h_add 6 2)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec h_add 6 2) (Z.sub regidx_bit_width 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end. cbn match. apply exec_returnM. }
  unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
  skip_pure_clause.
  do 16 (cstep s HmisaC).
  (* C_ADD clause: guard true *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match. rewrite exec_bind.
  rewrite (exec_bind_Some _ _ _ _ _ Hrsd). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hrs2). cbn beta. cbn iota.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
Qed.

Definition i_add_rsd : mword 5 :=
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec h_add 11 7) (Z.sub regidx_bit_width 1) 0).
Definition i_add_rs2 : mword 5 :=
  autocast (T := mword) (subrange_vec_dec (subrange_vec_dec h_add 6 2) (Z.sub regidx_bit_width 1) 0).

Lemma exec_execute_C_ADD (rsd rs2 : regidx) s :
  exec (execute (C_ADD (rsd, rs2))) s = Some (ExecuteAs (RTYPE (rs2, rsd, rsd, ADD)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADD. apply exec_returnM. Qed.

Section ForwardADD.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC h_add, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAad : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcad : mstate := set_reg sAad nextPC (add_vec_int pc 2).
  Definition addval : mword 64 :=
    add_vec (register_lookup (R_bitvector_64 x2) s_pcad.(sregs))
            (register_lookup (R_bitvector_64 x10) s_pcad.(sregs)).
  Definition sXad : mstate := set_reg s_pcad (R_bitvector_64 x2) (regval_into_reg addval).
  Definition sTad : mstate := set_reg sXad PC (register_lookup nextPC sXad.(sregs)).
  Definition sFad : mstate :=
    if b then set_reg sTad minstret (add_vec_int (register_lookup minstret sTad.(sregs)) 1)
         else sTad.

  Lemma forward_exec_add :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFad).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp Lmisa LS.
    assert (LpcA  : register_lookup PC sAad.(sregs) = pc).
    { unfold sAad, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAad.(sregs) = Machine).
    { unfold sAad, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAad.(sregs) = HART_ACTIVE tt).
    { unfold sAad, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAad.(sregs) = zeros' 64).
    { unfold sAad, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAad.(sregs))) ('b"1") = false).
    { unfold sAad, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAad.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAad, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa sAad.(sregs))) ('b"1") = true).
    { unfold sAad, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (LmisaSA : eq_vec (_get_Misa_S (register_lookup misa sAad.(sregs))) ('b"1") = true).
    { unfold sAad, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAad = Some (None, sAad)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAad _ (exec_currentlyEnabled_S sAad) LmisaSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAad = Some (F_RVC h_add, sAad)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed h_add) sAad = Some (C_ADD (rsd_cadd, rs2_cadd), sAad))
      by (apply decode_C_ADD; exact LmisaA).
    assert (Hexec1 : exec (execute (C_ADD (rsd_cadd, rs2_cadd))) s_pcad
                   = Some (ExecuteAs (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)), s_pcad))
      by apply exec_execute_C_ADD.
    assert (Hexec2 : exec (execute (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD))) s_pcad
                   = Some (RETIRE_SUCCESS, sXad)).
    { change (execute (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)))
        with (execute_RTYPE rs2_cadd rsd_cadd rsd_cadd ADD).
      unfold sXad, addval. unfold rsd_cadd, rs2_cadd.
      apply (exec_execute_RTYPE_ADD _ _ _
               (register_lookup (R_bitvector_64 x2) s_pcad.(sregs))
               (register_lookup (R_bitvector_64 x10) s_pcad.(sregs))).
      - apply exec_rX_bits_x2. vm_compute; reflexivity.
      - apply exec_rX_bits_x10. vm_compute; reflexivity.
      - apply exec_wX_bits_x2. vm_compute; reflexivity. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) sAad = Some (true, sAad))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) sAad = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h_add), sXad)).
    { exact (exec_hart_active_progress_RVC sAad sXad h_add (C_ADD (rsd_cadd, rs2_cadd))
               (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hexec1 Hexec2). }
    apply (exec_riscv_step_gen s sXad (zero_extend' 32 h_add) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXad, s_pcad, sAad; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXad, s_pcad, sAad; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardADD.

(* ====================================================================== *)
(* JAL (control flow) -- the "jump to start" capstone.                     *)
(* ====================================================================== *)
Lemma exec_set_next_pc (target : mword 64) s :
  exec (set_next_pc target) s = Some (tt, set_reg s nextPC target).
Proof.
  unfold set_next_pc. cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg nextPC target s)).
  apply exec_returnm.
Qed.

Lemma exec_jump_to (target : mword 64) s :
  eq_vec (access_vec_dec target 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec target 1) = false ->
  exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
Proof.
  intros Halign Hbit1.
  unfold jump_to. rewrite exec_catch_early_return.
  change (ext_control_check_pc target) with (@None unit). cbv iota beta.
  (* outer bind: w1 = false (target[1]=0 short-circuits and_boolM) *)
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold Defs.bind0.
      (* INNER = bind (bind (returnR())(fun _ => liftR assert)) (fun _ => and_boolM..) *)
      erewrite execR_bind_Some.
      2:{ erewrite execR_bind_Some.
          2:{ apply execR_returnR_fwd. }
          rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
          rewrite exec_returnm. reflexivity. }
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
      2:{ apply execR_returnR_fwd. }
      rewrite Hbit1. cbv iota beta. apply execR_returnR_fwd. }
  cbv iota beta.
  (* K false = liftR (set_next_pc target) >> returnR RETIRE_SUCCESS *)
  unfold Defs.bind0.
  rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
  2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
  rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
  reflexivity.
Qed.

Lemma exec_execute_JAL (imm : mword 21) (rd : regidx) s s_w :
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 1) = false ->
  exec (wX_bits rd (register_lookup nextPC s.(sregs)))
       (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))) = Some (tt, s_w) ->
  exec (execute_JAL imm rd) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Halign Hbit1 Hwx.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to _ s Halign Hbit1)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

Definition w_jal : mword 32 := mword_of_int 0x42000ef.
Definition i_jal : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_jal 11 7) (regidx_bit_width - 1) 0).
Definition imm_jal : mword 21 :=
  concat_vec (concat_vec (concat_vec (concat_vec
    (subrange_vec_dec w_jal 31 31) (subrange_vec_dec w_jal 19 12))
    (subrange_vec_dec w_jal 20 20)) (subrange_vec_dec w_jal 30 21)) ('b"0").

Lemma decode_jal s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode w_jal) s = Some (JAL (imm_jal, Regidx i_jal), s).
Proof.
  intro Hpriv. unfold imm_jal, i_jal.
  unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
  skip_pure_clause.                       (* ZICBOP *)
  skip_pure_clause.                       (* NTL    *)
  match goal with |- context[eq_vec w_jal ?c] =>
    replace (eq_vec w_jal c) with false by (vm_compute; reflexivity) end.
  match goal with |- context[eq_vec (subrange_vec_dec w_jal 11 0) ?c] =>
    replace (eq_vec (subrange_vec_dec w_jal 11 0) c) with false by (vm_compute; reflexivity) end.
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_pause s) as [bp Hbp].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp). destruct bp; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match.
  rewrite exec_bind.
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz). destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
  (* UTYPE guard false for JAL -> returnM None -> skip to JAL clause *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with false by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_returnM (@None instruction) s). cbn match.
  (* JAL clause guard true *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite exec_bind.
  unfold encdec_reg_backwards.
  match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn match.
  match goal with |- context[exec (returnM ?x) s] => rewrite (exec_returnM x s) end.
  cbn match. cbn match.
  apply exec_returnM.
Qed.

Lemma wX_jal_x1 (v : mword 64) :
  wX (Regno (uint i_jal)) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x1) (regval_into_reg v)) (returnM tt).
Proof. replace (uint i_jal) with 1%Z by (vm_compute; reflexivity). reflexivity. Qed.

Section ForwardJAL.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w_jal, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAj : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcj : mstate := set_reg sAj nextPC (add_vec_int pc 4).
  Definition jtgt : mword 64 :=
    add_vec (register_lookup PC s_pcj.(sregs)) (sign_extend' 64 imm_jal).
  Definition jlink : mword 64 := register_lookup nextPC s_pcj.(sregs).
  Definition sXj : mstate :=
    set_reg (set_reg s_pcj nextPC jtgt) (R_bitvector_64 x1) (regval_into_reg jlink).
  Definition sTj : mstate := set_reg sXj PC (register_lookup nextPC sXj.(sregs)).
  Definition sFj : mstate :=
    if b then set_reg sTj minstret (add_vec_int (register_lookup minstret sTj.(sregs)) 1)
         else sTj.

  Lemma forward_exec_jal :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (access_vec_dec jtgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec jtgt 1) = false ->
    exec riscv_step s = Some (tt, sFj).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp LS Halign Hbit1.
    assert (LpcA  : register_lookup PC sAj.(sregs) = pc).
    { unfold sAj, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAj.(sregs) = Machine).
    { unfold sAj, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAj.(sregs) = HART_ACTIVE tt).
    { unfold sAj, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAj.(sregs) = zeros' 64).
    { unfold sAj, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAj.(sregs))) ('b"1") = false).
    { unfold sAj, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAj.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAj, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaSA : eq_vec (_get_Misa_S (register_lookup misa sAj.(sregs))) ('b"1") = true).
    { unfold sAj, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAj = Some (None, sAj)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAj _ (exec_currentlyEnabled_S sAj) LmisaSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAj = Some (F_Base w_jal, sAj))
      by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w_jal) sAj = Some (JAL (imm_jal, Regidx i_jal), sAj))
      by (apply decode_jal; exact LprivA).
    assert (HexecJ : exec (execute (JAL (imm_jal, Regidx i_jal))) s_pcj
              = Some (RETIRE_SUCCESS, sXj)).
    { change (execute (JAL (imm_jal, Regidx i_jal)))
        with (execute_JAL imm_jal (Regidx i_jal)).
      apply (exec_execute_JAL imm_jal (Regidx i_jal) s_pcj sXj Halign Hbit1).
      unfold sXj, jtgt, jlink.
      apply (exec_wX_bits_at i_jal x1).
      apply wX_jal_x1. }
    assert (Hha : exec (run_hart_active 0) sAj
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w_jal), sXj)).
    { exact (exec_hart_active_progress sAj sAj sXj sAj w_jal
               (JAL (imm_jal, Regidx i_jal)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecJ I). }
    apply (exec_riscv_step_ADD s sXj w_jal b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXj, s_pcj, sAj; cbn zeta. trans_mi. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXj, s_pcj, sAj; cbn zeta. trans_mi. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardJAL.

(* ====================================================================== *)
(* MUL (M-extension) -- forward_exec_mul + Ext_M currentlyEnabled tower.    *)
(* ====================================================================== *)

(* hartSupports Ext_M = true (const arm). *)
Lemma exec_hartSupports_M s : exec (hartSupports Ext_M) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_M) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_rec_cE_M_misa (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true ->
  exec (_rec_currentlyEnabled Ext_M k acc) s
    = Some (eq_vec (_get_Misa_M (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_M s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_M s :
  eq_vec (_get_Misa_M (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_M) s = Some (true, s).
Proof.
  intro HM. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_M) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_M s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). cbn match.
  rewrite HM. apply exec_returnM.
Qed.

Definition w_mul : mword 32 := mword_of_int 0x2b50533.
Definition i_mul_rs2 : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_mul 24 20) (regidx_bit_width - 1) 0).
Definition i_mul_rs1 : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_mul 19 15) (regidx_bit_width - 1) 0).
Definition i_mul_rd : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_mul 11 7) (regidx_bit_width - 1) 0).
Definition mulop_mul : mul_op :=
  {| mul_op_result_part := Low; mul_op_signed_rs1 := Signed; mul_op_signed_rs2 := Signed |}.

Lemma decode_mul s :
  register_lookup cur_privilege (sregs s) = Machine ->
  eq_vec (_get_Misa_M (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode w_mul) s
    = Some (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul), s).
Proof.
  intros Hpriv HmisaM. unfold i_mul_rs2, i_mul_rs1, i_mul_rd, mulop_mul.
  unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
  skip_pure_clause.                       (* ZICBOP *)
  skip_pure_clause.                       (* NTL    *)
  match goal with |- context[eq_vec w_mul ?c] =>
    replace (eq_vec w_mul c) with false by (vm_compute; reflexivity) end.
  match goal with |- context[eq_vec (subrange_vec_dec w_mul 11 0) ?c] =>
    replace (eq_vec (subrange_vec_dec w_mul 11 0) c) with false by (vm_compute; reflexivity) end.
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_pause s) as [bp Hbp].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp). destruct bp; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match.
  rewrite exec_bind.
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz). destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with false by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_returnM (@None instruction) s). cbn match.
  do 33 skip_pure_clause.
  (* MUL clause guard true *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite exec_bind.
  (* reduce the 4 reg/mul_op decodes *)
  assert (Hr2 : exec (encdec_reg_backwards (subrange_vec_dec w_mul 24 20)) s
    = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w_mul 24 20) (regidx_bit_width - 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hr2).
  assert (Hr1 : exec (encdec_reg_backwards (subrange_vec_dec w_mul 19 15)) s
    = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w_mul 19 15) (regidx_bit_width - 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hr1).
  assert (Hmop : exec (encdec_mul_op_backwards (subrange_vec_dec w_mul 14 12)) s
    = Some ({| mul_op_result_part := Low; mul_op_signed_rs1 := Signed; mul_op_signed_rs2 := Signed |}, s)).
  { unfold encdec_mul_op_backwards.
    match goal with |- context[if ?g then returnM ?x else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hmop).
  assert (Hrd : exec (encdec_reg_backwards (subrange_vec_dec w_mul 11 7)) s
    = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w_mul 11 7) (regidx_bit_width - 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hrd).
  (* or_boolM (cE M)(cE Zmmul) = true *)
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_or_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_M s HmisaM))).
  cbn match.
  rewrite (exec_returnM _ s). cbn match.
  apply exec_returnM.
Qed.

Lemma wX_mul_x10 (v : mword 64) :
  wX (Regno (uint i_mul_rd)) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x10) (regval_into_reg v)) (returnM tt).
Proof. replace (uint i_mul_rd) with 10%Z by (vm_compute; reflexivity). reflexivity. Qed.

Definition mulprod (s : mstate) : mword 64 :=
  mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
    (register_lookup (R_bitvector_64 x10) s.(sregs))
    (register_lookup (R_bitvector_64 x11) s.(sregs)) (mulop_mul.(mul_op_result_part)).

Lemma exec_execute_MUL s :
  exec (execute (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul))) s
  = Some (RETIRE_SUCCESS, set_reg s (R_bitvector_64 x10) (regval_into_reg (mulprod s))).
Proof.
  change (execute (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul)))
    with (execute_MUL (Regidx i_mul_rs2) (Regidx i_mul_rs1) (Regidx i_mul_rd) mulop_mul).
  unfold execute_MUL.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x10 i_mul_rs1 s ltac:(vm_compute; reflexivity))).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x11 i_mul_rs2 s ltac:(vm_compute; reflexivity))).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_at i_mul_rd x10 s _ (wX_mul_x10 _))).
  apply exec_returnm.
Qed.

Section ForwardMUL.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w_mul, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAm : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcm : mstate := set_reg sAm nextPC (add_vec_int pc 4).
  Definition sXm : mstate :=
    set_reg s_pcm (R_bitvector_64 x10) (regval_into_reg (mulprod s_pcm)).
  Definition sTm : mstate := set_reg sXm PC (register_lookup nextPC sXm.(sregs)).
  Definition sFm : mstate :=
    if b then set_reg sTm minstret (add_vec_int (register_lookup minstret sTm.(sregs)) 1)
         else sTm.

  Lemma forward_exec_mul :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_M (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFm).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp LmisaM LS.
    assert (LpcA  : register_lookup PC sAm.(sregs) = pc).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAm.(sregs) = Machine).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAm.(sregs) = HART_ACTIVE tt).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAm.(sregs) = zeros' 64).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAm.(sregs))) ('b"1") = false).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAm.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaMA : eq_vec (_get_Misa_M (register_lookup misa sAm.(sregs))) ('b"1") = true).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmisaM | vm_compute; reflexivity ]. }
    assert (LmisaSA : eq_vec (_get_Misa_S (register_lookup misa sAm.(sregs))) ('b"1") = true).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAm = Some (None, sAm)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAm _ (exec_currentlyEnabled_S sAm) LmisaSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAm = Some (F_Base w_mul, sAm))
      by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w_mul) sAm
              = Some (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul), sAm))
      by (apply decode_mul; [ exact LprivA | exact LmisaMA ]).
    assert (HexecM : exec (execute (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul))) s_pcm
              = Some (RETIRE_SUCCESS, sXm)).
    { unfold sXm. fold s_pcm. apply exec_execute_MUL. }
    assert (Hha : exec (run_hart_active 0) sAm
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w_mul), sXm)).
    { exact (exec_hart_active_progress sAm sAm sXm sAm w_mul
               (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul))
               pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecM I). }
    apply (exec_riscv_step_ADD s sXm w_mul b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXm, s_pcm, sAm; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXm, s_pcm, sAm; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardMUL.

(* ====================================================================== *)
(* ADDI (RVC, 2-aligned) -- width-2 fetch stack + forward_exec_addi.        *)
(* ====================================================================== *)

(* ====================================================================== *)
(* Width-2 mem-read stack (mirror of the width-4 stack in RiscvFetchExec). *)
(* ====================================================================== *)

Lemma autocast_mword_id_16 (w : bv 16) :
  autocast (T := mword) (m := 8 * 2) (n := 2 * 8) w = w.
Proof.
  unfold autocast.
  destruct (Z.eq_dec (8 * 2) (2 * 8)) as [e | ne].
  - apply cast_Z_refl.
  - exfalso; apply ne; reflexivity.
Qed.

Lemma run_read_ram_plain_2_pin (addr : mword 64) (w : bv 16) s :
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 2 false) s (w, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_plain_2 (addr : mword 64) (w : bv 16) s :
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 2 false) s = Some ((w, default_meta), s).
Proof.
  intro Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_2_pin addr w s Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 2) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

Lemma exec_pmaCheck_ram_2 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (pmaCheck (Physaddr addr) 2 (InstructionFetch tt) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hexec.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hexec |- *.
  rewrite Halign. cbn [negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hexec. cbn [andb negb].
  apply exec_returnM.
Qed.

Lemma exec_checked_mem_read_ram_2 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Machine (Physaddr addr) 2 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_2 addr pbmt region s Hmatch Halign Hexec)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 2) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_fetch_2 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_2 with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Section FetchBytes2.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).

  Lemma exec_fetch_bytes_2 :
    exec (fetch_bytes pc pc 2) s = Some (@FetchBytes_Success 2 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite (exec_translateAddr_identity pc s Hpriv).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addr, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addr) 2 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2 PBMT_PMA addr region w s
                   Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchBytes2.

Section FetchRVC2.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HisRVC : isRVC w = true.

  Lemma exec_fetch_RVC_2 : exec (fetch tt) s = Some (F_RVC w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* w__7 (align error) = false *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* w__11 (4-aligned & Ziccif) = false because not 4-aligned *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* else branch: read PC twice, fetch_bytes pc pc 2 -> FetchBytes_Success w -> F_RVC w *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_2 pc region w s HpcPC Hpriv Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes)).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchRVC2.

Definition h_addi : mword 16 := mword_of_int 0x585.
Definition imm_caddi : mword 6 :=
  concat_vec (subrange_vec_dec h_addi 12 12) (subrange_vec_dec h_addi 6 2).
Definition rsd_caddi : regidx :=
  Regidx (autocast (T := mword)
            (subrange_vec_dec (subrange_vec_dec h_addi 11 7) (Z.sub regidx_bit_width 1) 0)).


Ltac dstep s HmisaC :=
  first
  [ cstep s HmisaC
  | rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None instruction) _)); cbn match ].

Lemma decode_C_ADDI s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed h_addi) s = Some (C_ADDI (imm_caddi, rsd_caddi), s).
Proof.
  intro HmisaC. unfold imm_caddi, rsd_caddi.
  assert (Hrsd : exec (encdec_reg_backwards (subrange_vec_dec h_addi 11 7)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec h_addi 11 7)
                           (Z.sub regidx_bit_width 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end. cbn match. apply exec_returnM. }
  unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
  skip_pure_clause.
  repeat (dstep s HmisaC).
  (* C_ADDI clause: outer guard true *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match. rewrite exec_bind.
  rewrite (exec_bind_Some _ _ _ _ _ Hrsd). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
Qed.

Definition i_addi : mword 5 :=
  autocast (T := mword)
    (subrange_vec_dec (subrange_vec_dec h_addi 11 7) (Z.sub regidx_bit_width 1) 0).

Lemma exec_execute_C_ADDI (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDI (imm, rsd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, rsd, rsd, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI. apply exec_returnM. Qed.

Lemma exec_execute_ITYPE_ADDI (imm : mword 12) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (add_vec a (sign_extend' 64 imm))) s = Some (tt, s') ->
  exec (execute (ITYPE (imm, rs1, rd, ADDI))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (ITYPE (imm, rs1, rd, ADDI))) with (execute_ITYPE imm rs1 rd ADDI).
  unfold execute_ITYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (add_vec a (sign_extend' 64 imm)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Lemma wX_addi_x11 (v : mword 64) :
  wX (Regno (uint i_addi)) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x11) (regval_into_reg v)) (returnM tt).
Proof. replace (uint i_addi) with 11%Z by (vm_compute; reflexivity). reflexivity. Qed.

Section ForwardADDI.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC h_addi, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAai : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcai : mstate := set_reg sAai nextPC (add_vec_int pc 2).
  Definition addival : mword 64 :=
    add_vec (register_lookup (R_bitvector_64 x11) s_pcai.(sregs))
            (sign_extend' 64 (sign_extend' 12 imm_caddi)).
  Definition sXai : mstate := set_reg s_pcai (R_bitvector_64 x11) (regval_into_reg addival).
  Definition sTai : mstate := set_reg sXai PC (register_lookup nextPC sXai.(sregs)).
  Definition sFai : mstate :=
    if b then set_reg sTai minstret (add_vec_int (register_lookup minstret sTai.(sregs)) 1)
         else sTai.

  Lemma forward_exec_addi :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFai).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp Lmisa LS.
    assert (LpcA  : register_lookup PC sAai.(sregs) = pc).
    { unfold sAai, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAai.(sregs) = Machine).
    { unfold sAai, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAai.(sregs) = HART_ACTIVE tt).
    { unfold sAai, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAai.(sregs) = zeros' 64).
    { unfold sAai, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAai.(sregs))) ('b"1") = false).
    { unfold sAai, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAai.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAai, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa sAai.(sregs))) ('b"1") = true).
    { unfold sAai, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (LmisaSA : eq_vec (_get_Misa_S (register_lookup misa sAai.(sregs))) ('b"1") = true).
    { unfold sAai, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAai = Some (None, sAai)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAai _ (exec_currentlyEnabled_S sAai) LmisaSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAai = Some (F_RVC h_addi, sAai)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed h_addi) sAai = Some (C_ADDI (imm_caddi, rsd_caddi), sAai))
      by (apply decode_C_ADDI; exact LmisaA).
    assert (Hexec1 : exec (execute (C_ADDI (imm_caddi, rsd_caddi))) s_pcai
                   = Some (ExecuteAs (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)), s_pcai))
      by apply exec_execute_C_ADDI.
    assert (Hexec2 : exec (execute (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI))) s_pcai
                   = Some (RETIRE_SUCCESS, sXai)).
    { unfold sXai, addival. unfold rsd_caddi. fold i_addi.
      apply (exec_execute_ITYPE_ADDI (sign_extend' 12 imm_caddi) (Regidx i_addi) (Regidx i_addi)
               (register_lookup (R_bitvector_64 x11) s_pcai.(sregs))).
      - apply exec_rX_bits_x11. vm_compute; reflexivity.
      - apply (exec_wX_bits_at i_addi x11). apply wX_addi_x11. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) sAai = Some (true, sAai))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) sAai = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h_addi), sXai)).
    { exact (exec_hart_active_progress_RVC sAai sXai h_addi (C_ADDI (imm_caddi, rsd_caddi))
               (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hexec1 Hexec2). }
    apply (exec_riscv_step_gen s sXai (zero_extend' 32 h_addi) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXai, s_pcai, sAai; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXai, s_pcai, sAai; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardADDI.

(* ====================================================================== *)
(* RVC 4-byte fetch SL wrapper + wp_step_lui + wp_step_add (4-aligned RVC). *)
(* ====================================================================== *)
Section WpFetchRVC.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma fetch_from_pts_minstret_RVC4
      (pc : mword 64) (w : mword 32) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (b : bool) (s : mstate) {dq : dfrac} :
    matching_pma_region pmar0 (Physaddr (fetch_pa pc)) 4 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    reg_interp s.(sregs) -∗
    gen_heap_interp s.(mem) -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ Machine -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC (subrange_vec_dec w 15 0), set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec Hpmp0 Halign Hbit0 Hbit1 Hvalign HisRVC)
            "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hbytes".
    iDestruct (reg_valid_dq with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    unfold addr_is_ram in Hram. destruct Hram as [Hnc Hns].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = pc).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Machine).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (Ltmem : forall j : nat, (N.of_nat j < 4)%N ->
              t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    assert (Hpmp : forall i, pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) i)) = OFF)
      by (rewrite Ltpmpc; exact Hpmp0).
    assert (Hmatch : matching_pma_region (register_lookup pma_regions t.(sregs))
              (Physaddr (fetch_pa pc)) 4 = Some region)
      by (rewrite Ltpma; exact Hmatch0).
    exact (exec_fetch_RVC_4 pc region w t Ltpc Ltpriv Hpmp Hmatch Hexec
             (within_clint_false (fetch_pa pc) 4 t Hnc ltac:(lia))
             (within_sig_false  (fetch_pa pc) 4 t Hns ltac:(lia))
             (within_htif_false (fetch_pa pc) 4 t Lthtif)
             Ltmem Hvalign HisRVC).
  Qed.
End WpFetchRVC.

Section StepLUI.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Section CleanLUI.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).
    Definition base_upd_lu : mstate :=
      set_reg
        (set_reg
           (set_reg (set_reg s (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2))
           (R_bitvector_64 x10) (regval_into_reg luival))
        PC (add_vec_int pc 2).
    Definition sFclu : mstate :=
      if b then set_reg base_upd_lu minstret (add_vec_int mst0 1) else base_upd_lu.

    Ltac tmilu := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

    Lemma sFlu_eq :
      register_lookup PC s.(sregs) = pc ->
      register_lookup minstret s.(sregs) = mst0 ->
      sFlu s pc b = sFclu.
    Proof.
      intros LpcS LmstS.
      assert (Enpc : register_lookup nextPC (sXlu s pc b).(sregs) = add_vec_int pc 2).
      { unfold sXlu; cbv zeta. unfold set_reg; cbn [sregs]. tmilu.
        rewrite register_lookup_set. reflexivity. }
      assert (HsT : sTlu s pc b = base_upd_lu).
      { unfold sTlu. rewrite Enpc. unfold sXlu, s_pclu, sAlu; cbv zeta.
        unfold base_upd_lu, s_pclu, sAlu. reflexivity. }
      unfold sFlu, sFclu. rewrite HsT. destruct b; [|reflexivity].
      assert (Emst : register_lookup minstret base_upd_lu.(sregs)
                     = register_lookup minstret s.(sregs)).
      { unfold base_upd_lu, set_reg; cbn [sregs]. tmilu. tmilu. tmilu. tmilu. reflexivity. }
      rewrite Emst LmstS. reflexivity.
    Qed.
  End CleanLUI.

  Lemma wp_step_lui (pc : mword 64) (w : mword 32)
      (b1 : bool) (x10_0 npc0 mstatus0 misa0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    subrange_vec_dec w 15 0 = h_lui ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ (R_bitvector_64 x10) ↦ᵣ x10_0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto misa dqc misa0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        (R_bitvector_64 x10) ↦ᵣ regval_into_reg luival -∗
        nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto misa dqc misa0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hsub Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hb1 HmIE Help Hmisa HmisaS)
      "#Hinv Hpc Hx10 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf
                 ltac:(rewrite Hsub; vm_compute; reflexivity)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    rewrite Hsub in Hfetch_at.
    iModIntro.
    iExists (sFclu s pc b1 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFlu_eq s pc b1 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_lui s pc b1 Hfetch_at Hsi_s Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa.
      - rewrite Lmisa. exact HmisaS. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x10) _ (regval_into_reg luival) with "Hreg Hx10") as "[Hreg Hx10]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    unfold sFclu, base_upd_lu. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hx10 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hx10 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End StepLUI.

Section StepADD.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma addval_eq (s : mstate) (pc : mword 64) (b : bool) (v2 v10 : mword 64) :
    register_lookup (R_bitvector_64 x2) s.(sregs) = v2 ->
    register_lookup (R_bitvector_64 x10) s.(sregs) = v10 ->
    addval s pc b = add_vec v2 v10.
  Proof.
    intros L2 L10. unfold addval, s_pcad, sAad. unfold set_reg; cbn [sregs].
    do 4 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]).
    rewrite L2 L10. reflexivity.
  Qed.

  Section CleanADD.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).
    Definition base_upd_ad : mstate :=
      set_reg
        (set_reg
           (set_reg (set_reg s (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2))
           (R_bitvector_64 x2) (regval_into_reg (addval s pc b)))
        PC (add_vec_int pc 2).
    Definition sFcad : mstate :=
      if b then set_reg base_upd_ad minstret (add_vec_int mst0 1) else base_upd_ad.

    Ltac tmiad := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

    Lemma sFad_eq :
      register_lookup PC s.(sregs) = pc ->
      register_lookup minstret s.(sregs) = mst0 ->
      sFad s pc b = sFcad.
    Proof.
      intros LpcS LmstS.
      assert (Enpc : register_lookup nextPC (sXad s pc b).(sregs) = add_vec_int pc 2).
      { unfold sXad; cbv zeta. unfold set_reg; cbn [sregs]. tmiad.
        rewrite register_lookup_set. reflexivity. }
      assert (HsT : sTad s pc b = base_upd_ad).
      { unfold sTad. rewrite Enpc. unfold sXad, s_pcad, sAad; cbv zeta.
        unfold base_upd_ad, s_pcad, sAad. reflexivity. }
      unfold sFad, sFcad. rewrite HsT. destruct b; [|reflexivity].
      assert (Emst : register_lookup minstret base_upd_ad.(sregs)
                     = register_lookup minstret s.(sregs)).
      { unfold base_upd_ad, set_reg; cbn [sregs]. tmiad. tmiad. tmiad. tmiad. reflexivity. }
      rewrite Emst LmstS. reflexivity.
    Qed.
  End CleanADD.

  Lemma wp_step_add (pc : mword 64) (w : mword 32)
      (b1 : bool) (sp_in a0_in npc0 mstatus0 misa0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    subrange_vec_dec w 15 0 = h_add ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ (R_bitvector_64 x2) ↦ᵣ sp_in -∗ (R_bitvector_64 x10) ↦ᵣ a0_in -∗
    nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto misa dqc misa0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (add_vec sp_in a0_in) -∗
        (R_bitvector_64 x10) ↦ᵣ a0_in -∗
        nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto misa dqc misa0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hsub Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hb1 HmIE Help Hmisa HmisaS)
      "#Hinv Hpc Hx2 Hx10 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hx2")    as %Lx2.
    iDestruct (reg_valid_dq with "Hreg Hx10")   as %Lx10.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    assert (Hav : addval s pc b1 = add_vec sp_in a0_in) by (apply addval_eq; assumption).
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC4 pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf
                 ltac:(rewrite Hsub; vm_compute; reflexivity)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    rewrite Hsub in Hfetch_at.
    iModIntro.
    iExists (sFcad s pc b1 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFad_eq s pc b1 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_add s pc b1 Hfetch_at Hsi_s Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa.
      - rewrite Lmisa. exact HmisaS. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x2) _ (regval_into_reg (addval s pc b1)) with "Hreg Hx2") as "[Hreg Hx2]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hx2".
    unfold sFcad, base_upd_ad. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hx2 Hx10 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hx2 Hx10 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End StepADD.

(* ====================================================================== *)
(* wp_step_mul (4-aligned F_Base, M-ext).                                  *)
(* ====================================================================== *)

Section StepMUL.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma mulprod_eq (s : mstate) (pc : mword 64) (b : bool) (a0 a1 : mword 64) :
    register_lookup (R_bitvector_64 x10) s.(sregs) = a0 ->
    register_lookup (R_bitvector_64 x11) s.(sregs) = a1 ->
    mulprod (s_pcm s pc b)
    = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
        a0 a1 (mulop_mul.(mul_op_result_part)).
  Proof.
    intros L10 L11. unfold mulprod, s_pcm, sAm. unfold set_reg; cbn [sregs].
    do 4 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]).
    rewrite L10 L11. reflexivity.
  Qed.

  Section CleanMUL.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).
    Definition base_upd_m : mstate :=
      set_reg
        (set_reg
           (set_reg (set_reg s (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 4))
           (R_bitvector_64 x10) (regval_into_reg (mulprod (s_pcm s pc b))))
        PC (add_vec_int pc 4).
    Definition sFcm : mstate :=
      if b then set_reg base_upd_m minstret (add_vec_int mst0 1) else base_upd_m.

    Ltac tmim := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

    Lemma sFm_eq :
      register_lookup PC s.(sregs) = pc ->
      register_lookup minstret s.(sregs) = mst0 ->
      sFm s pc b = sFcm.
    Proof.
      intros LpcS LmstS.
      assert (Enpc : register_lookup nextPC (sXm s pc b).(sregs) = add_vec_int pc 4).
      { unfold sXm; cbv zeta. unfold set_reg; cbn [sregs]. tmim.
        rewrite register_lookup_set. reflexivity. }
      assert (HsT : sTm s pc b = base_upd_m).
      { unfold sTm. rewrite Enpc. unfold sXm, s_pcm, sAm; cbv zeta.
        unfold base_upd_m, s_pcm, sAm. reflexivity. }
      unfold sFm, sFcm. rewrite HsT. destruct b; [|reflexivity].
      assert (Emst : register_lookup minstret base_upd_m.(sregs)
                     = register_lookup minstret s.(sregs)).
      { unfold base_upd_m, set_reg; cbn [sregs]. tmim. tmim. tmim. tmim. reflexivity. }
      rewrite Emst LmstS. reflexivity.
    Qed.
  End CleanMUL.

  Lemma wp_step_mul (pc : mword 64)
      (b1 : bool) (a0_in a1_in npc0 mstatus0 misa0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w_mul 15 0) = false ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_M misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ (R_bitvector_64 x10) ↦ᵣ a0_in -∗ (R_bitvector_64 x11) ↦ᵣ a1_in -∗
    nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto misa dqc misa0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_mul j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        (R_bitvector_64 x10) ↦ᵣ regval_into_reg
          (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
             a0_in a1_in (mulop_mul.(mul_op_result_part))) -∗
        (R_bitvector_64 x11) ↦ᵣ a1_in -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto misa dqc misa0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_mul j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hb1 HmIE Help Hmisa HmisaS)
      "#Hinv Hpc Hx10 Hx11 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hx10")   as %Lx10.
    iDestruct (reg_valid_dq with "Hreg Hx11")   as %Lx11.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    assert (Hpv : mulprod (s_pcm s pc b1)
      = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
          a0_in a1_in (mulop_mul.(mul_op_result_part))) by (apply mulprod_eq; assumption).
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret pc w_mul region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcm s pc b1 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFm_eq s pc b1 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_mul s pc b1 Hfetch_at Hsi_s Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa.
      - rewrite Lmisa. exact HmisaS. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x10) _ (regval_into_reg (mulprod (s_pcm s pc b1))) with "Hreg Hx10") as "[Hreg Hx10]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hpv) in "Hx10".
    unfold sFcm, base_upd_m. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hx10 Hx11 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hx10 Hx11 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End StepMUL.

(* ====================================================================== *)
(* CSRR (csrr a1,mhartid) -- forward_exec_csrr (F_Base, fetch-agnostic).    *)
(* ====================================================================== *)

Lemma exec_currentlyEnabled_Zicsr s : exec (currentlyEnabled Ext_Zicsr) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicsr.
Qed.

Definition w_csrr : mword 32 := mword_of_int 0xf14025f3.
Definition csr_csrr : mword 12 := subrange_vec_dec w_csrr 31 20.
Definition i_rs1_csrr : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_csrr 19 15) (regidx_bit_width - 1) 0).
Definition i_rd_csrr : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_csrr 11 7) (regidx_bit_width - 1) 0).

Lemma decode_csrr s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode w_csrr) s
    = Some (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx i_rd_csrr, CSRRS), s).
Proof.
  intro Hpriv. unfold csr_csrr, i_rs1_csrr, i_rd_csrr.
  unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
  skip_pure_clause.                       (* ZICBOP *)
  skip_pure_clause.                       (* NTL    *)
  match goal with |- context[eq_vec w_csrr ?c] =>
    replace (eq_vec w_csrr c) with false by (vm_compute; reflexivity) end.
  match goal with |- context[eq_vec (subrange_vec_dec w_csrr 11 0) ?c] =>
    replace (eq_vec (subrange_vec_dec w_csrr 11 0) c) with false by (vm_compute; reflexivity) end.
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_pause s) as [bp Hbp].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp). destruct bp; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match.
  rewrite exec_bind.
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz). destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
  (* UTYPE guard false -> returnM None -> reach JAL clause *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with false by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_returnM (@None instruction) s). cbn match.
  (* now at JAL clause (clause 6); skip clauses 6..91 to reach CSRReg (clause 92) *)
  repeat skip_pure_clause.
  (* CSRReg clause (guard true) *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite exec_bind.
  assert (Hr1 : exec (encdec_reg_backwards (subrange_vec_dec w_csrr 19 15)) s
      = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w_csrr 19 15)
                                 (regidx_bit_width - 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. apply exec_returnM. }
  assert (Hcsrop : exec (encdec_csrop_backwards (subrange_vec_dec w_csrr 13 12)) s
      = Some (CSRRS, s)).
  { unfold encdec_csrop_backwards.
    replace (eq_vec (subrange_vec_dec w_csrr 13 12) ('b"01")) with false
      by (vm_compute; reflexivity).
    replace (eq_vec (subrange_vec_dec w_csrr 13 12) ('b"10")) with true
      by (vm_compute; reflexivity).
    cbn match. apply exec_returnM. }
  assert (Hr2 : exec (encdec_reg_backwards (subrange_vec_dec w_csrr 11 7)) s
      = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w_csrr 11 7)
                                 (regidx_bit_width - 1) 0)), s)).
  { unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hr1).
  rewrite (exec_bind_Some _ _ _ _ _ Hcsrop).
  rewrite (exec_bind_Some _ _ _ _ _ Hr2).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicsr s)).
  rewrite (exec_returnM _ s). cbn match.
  apply exec_returnM.
Qed.

Lemma exec_check_CSR_csrr s : exec (check_CSR csr_csrr Machine CSRRead) s = Some (true, s).
Proof.
  assert (H : check_CSR csr_csrr Machine CSRRead = returnM true) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_csr_id_read_callback_csrr s d :
  exec (csr_id_read_callback csr_csrr d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_csrr d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_rX_bits_x0 (i : mword 5) s :
  uint i = 0 -> exec (rX_bits (Regidx i)) s = Some (zero_reg, s).
Proof.
  intro H. unfold rX_bits; cbn match. rewrite H. unfold rX.
  replace (Z.eqb 0 0) with true by reflexivity. cbn match. apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_csrr s :
  exec (check_CSR_result csr_csrr Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_csrr s)).
  exact (exec_returnM (CSR_Check_OK tt) s).
Qed.

Lemma exec_read_CSR_csrr s :
  exec (read_CSR csr_csrr) s = Some (register_lookup mhartid s.(sregs), s).
Proof. exact (exec_read_reg (R_bitvector_64 mhartid) s). Qed.

Lemma exec_execute_CSRReg s s_w :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (wX_bits (Regidx i_rd_csrr) (register_lookup mhartid s.(sregs))) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr_csrr (Regidx i_rs1_csrr) (Regidx i_rd_csrr) CSRRS) s
    = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Hpriv Hwx.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRS (generic_eq (Regidx i_rd_csrr) zreg)
             (generic_eq (Regidx i_rs1_csrr) zreg)) with CSRRead
    by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x0 i_rs1_csrr s ltac:(vm_compute; reflexivity))).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_csrr s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  (* ext_check_CSR = true -> not true = false -> else branch *)
  replace (not (ext_check_CSR csr_csrr Machine CSRRead)) with false
    by (vm_compute; reflexivity).
  (* generic_neq CSRRead CSRWrite = true -> read_CSR csr_csrr *)
  replace (if generic_neq CSRRead CSRWrite then read_CSR csr_csrr else returnM (zeros' 64))
    with (read_CSR csr_csrr) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_csrr s)).
  (* dest_val: csr not 0x344/0x144 -> returnM read_val *)
  match goal with |- exec (Defs.bind ?D ?K) s = _ =>
    replace D with (returnM (register_lookup mhartid s.(sregs)) : M (mword 64))
      by (vm_compute; reflexivity) end.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (register_lookup mhartid s.(sregs)) s)).
  (* read path: generic_eq CSRRead CSRRead = true *)
  replace (generic_eq CSRRead CSRRead) with true by reflexivity.
  rewrite (exec_bind0_Some _ _ _ _ _ (_ :
    exec (Defs.bind0 (csr_id_read_callback csr_csrr (register_lookup mhartid s.(sregs)))
            (wX_bits (Regidx i_rd_csrr) (register_lookup mhartid s.(sregs)))) s
      = Some (tt, s_w))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
        (exec_csr_id_read_callback_csrr s (register_lookup mhartid s.(sregs)))).
      exact Hwx. }
  apply exec_returnM.
Qed.

Lemma wX_csrr_a1 (v : mword 64) :
  wX (Regno (uint i_rd_csrr)) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x11) (regval_into_reg v)) (returnM tt).
Proof. replace (uint i_rd_csrr) with 11%Z by (vm_compute; reflexivity). reflexivity. Qed.

Section ForwardCSRR.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w_csrr, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAc : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcc : mstate := set_reg sAc nextPC (add_vec_int pc 4).
  Definition sXc : mstate :=
    set_reg s_pcc (R_bitvector_64 x11) (regval_into_reg (register_lookup mhartid s_pcc.(sregs))).
  Definition sTc : mstate := set_reg sXc PC (register_lookup nextPC sXc.(sregs)).
  Definition sFc : mstate :=
    if b then set_reg sTc minstret (add_vec_int (register_lookup minstret sTc.(sregs)) 1)
         else sTc.

  Lemma forward_exec_csrr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFc).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp LS.
    assert (LpcA  : register_lookup PC sAc.(sregs) = pc).
    { unfold sAc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAc.(sregs) = Machine).
    { unfold sAc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAc.(sregs) = HART_ACTIVE tt).
    { unfold sAc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAc.(sregs) = zeros' 64).
    { unfold sAc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAc.(sregs))) ('b"1") = false).
    { unfold sAc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAc.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaSA : eq_vec (_get_Misa_S (register_lookup misa sAc.(sregs))) ('b"1") = true).
    { unfold sAc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAc = Some (None, sAc)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAc _ (exec_currentlyEnabled_S sAc) LmisaSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAc = Some (F_Base w_csrr, sAc))
      by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w_csrr) sAc
              = Some (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx i_rd_csrr, CSRRS), sAc))
      by (apply decode_csrr; exact LprivA).
    assert (LprivC : register_lookup cur_privilege s_pcc.(sregs) = Machine).
    { unfold s_pcc; trans_mi. exact LprivA. }
    assert (HexecC : exec (execute (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx i_rd_csrr, CSRRS))) s_pcc
              = Some (RETIRE_SUCCESS, sXc)).
    { change (execute (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx i_rd_csrr, CSRRS)))
        with (execute_CSRReg csr_csrr (Regidx i_rs1_csrr) (Regidx i_rd_csrr) CSRRS).
      apply (exec_execute_CSRReg s_pcc sXc LprivC).
      unfold sXc. apply (exec_wX_bits_at i_rd_csrr x11). apply wX_csrr_a1. }
    assert (Hha : exec (run_hart_active 0) sAc
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w_csrr), sXc)).
    { exact (exec_hart_active_progress sAc sAc sXc sAc w_csrr
               (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx i_rd_csrr, CSRRS)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s sXc w_csrr b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXc, s_pcc, sAc; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXc, s_pcc, sAc; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCSRR.

(* ====================================================================== *)
(* RVC 2-byte fetch SL wrapper + wp_step_addi (2-aligned RVC).             *)
(* ====================================================================== *)

Section WpFetchRVC2.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma fetch_from_pts_minstret_RVC2
      (pc : mword 64) (w : mword 16) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (b : bool) (misa0 : mword 64) (s : mstate) {dq : dfrac} :
    matching_pma_region pmar0 (Physaddr (fetch_pa pc)) 2 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    isRVC w = true ->
    reg_interp s.(sregs) -∗
    gen_heap_interp s.(mem) -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ Machine -∗
    reg_pointsto misa dqc misa0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w, set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec Hpmp0 Halign Hbit0 Hbit1 Hvalign Hmisa HisRVC)
            "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hbytes".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
               s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 2)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    unfold addr_is_ram in Hram. destruct Hram as [Hnc Hns].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = pc).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Machine).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltmisa : register_lookup misa t.(sregs) = misa0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmisa | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (Ltmem : forall j : nat, (N.of_nat j < 2)%N ->
              t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    assert (Hpmp : forall i, pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) i)) = OFF)
      by (rewrite Ltpmpc; exact Hpmp0).
    assert (Hmatch : matching_pma_region (register_lookup pma_regions t.(sregs))
              (Physaddr (fetch_pa pc)) 2 = Some region)
      by (rewrite Ltpma; exact Hmatch0).
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true)
      by (rewrite Ltmisa; exact Hmisa).
    exact (exec_fetch_RVC_2 pc region w t Ltpc Ltpriv Hpmp Hmatch Halign Hexec
             (within_clint_false (fetch_pa pc) 2 t Hnc ltac:(lia))
             (within_sig_false  (fetch_pa pc) 2 t Hns ltac:(lia))
             (within_htif_false (fetch_pa pc) 2 t Lthtif)
             Ltmem Hbit0 Hbit1 Hvalign HmisaC HisRVC).
  Qed.
End WpFetchRVC2.

Section StepADDI.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma addival_eq (s : mstate) (pc : mword 64) (b : bool) (a1 : mword 64) :
    register_lookup (R_bitvector_64 x11) s.(sregs) = a1 ->
    addival s pc b = add_vec a1 (sign_extend' 64 (sign_extend' 12 imm_caddi)).
  Proof.
    intro L11. unfold addival, s_pcai, sAai. unfold set_reg; cbn [sregs].
    do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]).
    rewrite L11. reflexivity.
  Qed.

  Section CleanADDI.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).
    Definition base_upd_ai : mstate :=
      set_reg
        (set_reg
           (set_reg (set_reg s (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2))
           (R_bitvector_64 x11) (regval_into_reg (addival s pc b)))
        PC (add_vec_int pc 2).
    Definition sFcai : mstate :=
      if b then set_reg base_upd_ai minstret (add_vec_int mst0 1) else base_upd_ai.

    Ltac tmiai := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

    Lemma sFai_eq :
      register_lookup PC s.(sregs) = pc ->
      register_lookup minstret s.(sregs) = mst0 ->
      sFai s pc b = sFcai.
    Proof.
      intros LpcS LmstS.
      assert (Enpc : register_lookup nextPC (sXai s pc b).(sregs) = add_vec_int pc 2).
      { unfold sXai; cbv zeta. unfold set_reg; cbn [sregs]. tmiai.
        rewrite register_lookup_set. reflexivity. }
      assert (HsT : sTai s pc b = base_upd_ai).
      { unfold sTai. rewrite Enpc. unfold sXai, s_pcai, sAai; cbv zeta.
        unfold base_upd_ai, s_pcai, sAai. reflexivity. }
      unfold sFai, sFcai. rewrite HsT. destruct b; [|reflexivity].
      assert (Emst : register_lookup minstret base_upd_ai.(sregs)
                     = register_lookup minstret s.(sregs)).
      { unfold base_upd_ai, set_reg; cbn [sregs]. tmiai. tmiai. tmiai. tmiai. reflexivity. }
      rewrite Emst LmstS. reflexivity.
    Qed.
  End CleanADDI.

  Lemma wp_step_addi (pc : mword 64)
      (b1 : bool) (a1_in npc0 mstatus0 misa0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ (R_bitvector_64 x11) ↦ᵣ a1_in -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto misa dqc misa0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte h_addi j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        (R_bitvector_64 x11) ↦ᵣ regval_into_reg
          (add_vec a1_in (sign_extend' 64 (sign_extend' 12 imm_caddi))) -∗
        nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto misa dqc misa0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte h_addi j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hb1 HmIE Help Hmisa HmisaS)
      "#Hinv Hpc Hx11 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hx11")   as %Lx11.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    assert (Hav : addival s pc b1 = add_vec a1_in (sign_extend' 64 (sign_extend' 12 imm_caddi)))
      by (apply addival_eq; assumption).
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC2 pc h_addi region_f pmpcfg0 pmar0 b1 misa0 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hmisa
                 ltac:(vm_compute; reflexivity)
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcai s pc b1 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFai_eq s pc b1 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_addi s pc b1 Hfetch_at Hsi_s Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact Hmisa.
      - rewrite Lmisa. exact HmisaS. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x11) _ (regval_into_reg (addival s pc b1)) with "Hreg Hx11") as "[Hreg Hx11]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hx11".
    unfold sFcai, base_upd_ai. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hx11 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hx11 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End StepADDI.

(* ====================================================================== *)
(* 2-aligned 32-bit fetch (2+2 read) + SL wrapper (for csrr@0xa, jal@0x16). *)
(* ====================================================================== *)

(* ====================================================================== *)
(* 2-aligned 32-bit fetch: reads 2 bytes (ilo) at pc, isRVC=false, then 2  *)
(* more (ihi) at pc+2, returns F_Base (concat ihi ilo).  For csrr@0xa,     *)
(* jal@0x16.                                                                *)
(* ====================================================================== *)
Section FetchFBase2.
  Context (pc : mword 64) (regl regh : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.
  Let addrh := fetch_pa (add_vec_int pc 2).
  Let ilo : mword 16 := subrange_vec_dec w 15 0.
  Let ihi : mword 16 := subrange_vec_dec w 31 16.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatchl : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some regl.
  Hypothesis Hmatchh : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addrh) 2 = Some regh.
  Hypothesis Halignl : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Halignh : is_aligned_paddr (Physaddr addrh) 2 = true.
  Hypothesis Hexecl : (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hexech : (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hcl : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsigl : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hhl : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hch : exec (within_clint (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hsigh : exec (within_sig (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hhh : exec (within_htif_readable (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hbytesl : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte ilo j).
  Hypothesis Hbytesh : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addrh j) = Some (nth_byte ihi j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HnotRVC : isRVC ilo = false.
  Hypothesis Hconcat : concat_vec ihi ilo = w.

  Lemma exec_fetch_F_Base_2 : exec (fetch tt) s = Some (F_Base w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    assert (HrdPC2 : exec (Defs.read_reg PC) s = Some (pc, s)) by exact HrdPC.
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* else branch: read PC twice, fetch_bytes pc pc 2 -> Success ilo *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_2 pc regl ilo s HpcPC Hpriv Hpmp Hmatchl Halignl Hexecl Hcl Hsigl Hhl Hbytesl)).
    cbv iota beta. rewrite HnotRVC. cbv iota beta.
    (* isRVC false: read PC twice, fetch_bytes pc (pc+2) 2 -> Success ihi -> F_Base (concat ihi ilo) *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    assert (Hfb2hi : exec (fetch_bytes pc (add_vec_int pc 2) 2) s
                     = Some (@FetchBytes_Success 2 ihi, s)).
    { unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc pc (add_vec_int pc 2)) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr (add_vec_int pc 2)) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr addrh, PBMT_PMA, init_ext_ptw)), s))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR. rewrite (exec_translateAddr_identity (add_vec_int pc 2) s Hpriv).
          cbn match. reflexivity. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addrh, PBMT_PMA) s)).
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addrh) 2 false false false)) s
             = Some (inr (Ok ihi), s))).
      2:{ rewrite execR_liftR.
          rewrite (exec_mem_read_fetch_2 PBMT_PMA addrh regh ihi s
                     Hpmp Hmatchh Halignh Hexech Hch Hsigh Hhh Hbytesh Hpriv).
          cbn match. reflexivity. }
      cbv iota beta. rewrite autocast_mword_id_16.
      rewrite execR_returnR_fwd. cbn match. reflexivity. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hfb2hi).
    cbv iota beta. rewrite execR_returnR_fwd. cbn match.
    rewrite Hconcat. reflexivity.
  Qed.
End FetchFBase2.

Section WpFetchFBase2SL.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma fetch_from_pts_minstret_2
      (pc : mword 64) (w : mword 32) (regl regh : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (b : bool) (s : mstate) {dq : dfrac} :
    matching_pma_region pmar0 (Physaddr (fetch_pa pc)) 2 = Some regl ->
    matching_pma_region pmar0 (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = Some regh ->
    (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true ->
    (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    reg_interp s.(sregs) -∗
    gen_heap_interp s.(mem) -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ Machine -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto htif_tohost_base dqc None -∗
    reg_pointsto misa dqc (register_lookup misa s.(sregs)) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatchl Hmatchh Hexecl Hexech Hpmp0 Halignl Halignh Hbit0 Hbit1 Hvalign
             HnotRVC Hconcat Haddr Hlo Hhi HmisaC)
            "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hbytes".
    iDestruct (reg_valid_dq with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hoff : fetch_pa (add_vec_int pc 2) = pa_add (fetch_pa pc) 2).
    { specialize (Haddr 0%nat ltac:(lia)). rewrite pa_add_0 in Haddr. exact Haddr. }
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hraml.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (fetch_pa (add_vec_int pc 2))⌝)%I as %Hramh.
    { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb2") as %Hr2. rewrite Hoff. iPureIntro. exact Hr2. }
    iPureIntro.
    destruct Hraml as [Hncl Hnsl]. destruct Hramh as [Hnch Hnsh].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = pc).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Machine).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (LtmisaC : eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact HmisaC | vm_compute; reflexivity]. }
    assert (Hpmp : forall i, pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) i)) = OFF)
      by (rewrite Ltpmpc; exact Hpmp0).
    assert (Hml : matching_pma_region (register_lookup pma_regions t.(sregs))
              (Physaddr (fetch_pa pc)) 2 = Some regl) by (rewrite Ltpma; exact Hmatchl).
    assert (Hmh : matching_pma_region (register_lookup pma_regions t.(sregs))
              (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = Some regh) by (rewrite Ltpma; exact Hmatchh).
    assert (Htmem : forall j : nat, (N.of_nat j < 4)%N ->
              t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
              t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
    { intros j Hj. rewrite Hlo; [|exact Hj]. apply Htmem. lia. }
    assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
              t.(mem) !! (pa_add (fetch_pa (add_vec_int pc 2)) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
    { intros j Hj. rewrite Hhi; [|exact Hj]. rewrite (Haddr j Hj).
      apply Htmem. lia. }
    exact (exec_fetch_F_Base_2 pc regl regh w t Ltpc Ltpriv Hpmp Hml Hmh Halignl Halignh
             Hexecl Hexech
             (within_clint_false (fetch_pa pc) 2 t Hncl ltac:(lia))
             (within_sig_false  (fetch_pa pc) 2 t Hnsl ltac:(lia))
             (within_htif_false (fetch_pa pc) 2 t Lthtif)
             (within_clint_false (fetch_pa (add_vec_int pc 2)) 2 t Hnch ltac:(lia))
             (within_sig_false  (fetch_pa (add_vec_int pc 2)) 2 t Hnsh ltac:(lia))
             (within_htif_false (fetch_pa (add_vec_int pc 2)) 2 t Lthtif)
             Hbl Hbh Hbit0 Hbit1 Hvalign LtmisaC HnotRVC Hconcat).
  Qed.
End WpFetchFBase2SL.

(* ====================================================================== *)
(* wp_step_csrr (2-aligned F_Base).                                        *)
(* ====================================================================== *)

Section StepCSRR.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma mhartid_eq (s : mstate) (pc : mword 64) (b : bool) (v : mword 64) :
    register_lookup mhartid s.(sregs) = v ->
    register_lookup mhartid (s_pcc s pc b).(sregs) = v.
  Proof.
    intro Lm. unfold s_pcc, sAc. unfold set_reg; cbn [sregs].
    do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Lm.
  Qed.

  Section CleanCSRR.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).
    Definition base_upd_c : mstate :=
      set_reg
        (set_reg
           (set_reg (set_reg s (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 4))
           (R_bitvector_64 x11) (regval_into_reg (register_lookup mhartid (s_pcc s pc b).(sregs))))
        PC (add_vec_int pc 4).
    Definition sFcc : mstate :=
      if b then set_reg base_upd_c minstret (add_vec_int mst0 1) else base_upd_c.

    Ltac tmic := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

    Lemma sFc_eq :
      register_lookup PC s.(sregs) = pc ->
      register_lookup minstret s.(sregs) = mst0 ->
      sFc s pc b = sFcc.
    Proof.
      intros LpcS LmstS.
      assert (Enpc : register_lookup nextPC (sXc s pc b).(sregs) = add_vec_int pc 4).
      { unfold sXc; cbv zeta. unfold set_reg; cbn [sregs]. tmic.
        rewrite register_lookup_set. reflexivity. }
      assert (HsT : sTc s pc b = base_upd_c).
      { unfold sTc. rewrite Enpc. unfold sXc, s_pcc, sAc; cbv zeta.
        unfold base_upd_c, s_pcc, sAc. reflexivity. }
      unfold sFc, sFcc. rewrite HsT. destruct b; [|reflexivity].
      assert (Emst : register_lookup minstret base_upd_c.(sregs)
                     = register_lookup minstret s.(sregs)).
      { unfold base_upd_c, set_reg; cbn [sregs]. tmic. tmic. tmic. tmic. reflexivity. }
      rewrite Emst LmstS. reflexivity.
    Qed.
  End CleanCSRR.

  Lemma wp_step_csrr (pc : mword 64)
      (b1 : bool) (mhartid_in x11_0 npc0 mstatus0 misa0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ (R_bitvector_64 x11) ↦ᵣ x11_0 -∗ mhartid ↦ᵣ mhartid_in -∗
    nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto misa dqc misa0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_csrr j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        (R_bitvector_64 x11) ↦ᵣ regval_into_reg mhartid_in -∗ mhartid ↦ᵣ mhartid_in -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto misa dqc misa0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_csrr j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf Haddr Hb1 HmIE Help Hmisa HmisaS)
      "#Hinv Hpc Hx11 Hmhart Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hmhart") as %Lmhart.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    assert (Hmhv : register_lookup mhartid (s_pcc s pc b1).(sregs) = mhartid_in)
      by (apply mhartid_eq; exact Lmhart).
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iEval (rewrite <- Lmisa) in "Hmisa'".
    iDestruct (fetch_from_pts_minstret_2 pc w_csrr regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Haddr
                 ltac:(intros j Hj; destruct j as [|[|j]];
                       [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
                 ltac:(intros j Hj; destruct j as [|[|j]];
                       [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
                 ltac:(rewrite Lmisa; exact Hmisa)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa' Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcc s pc b1 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFc_eq s pc b1 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_csrr s pc b1 Hfetch_at Hsi_s Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaS. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iEval (rewrite Lmisa) in "Hmisa'".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x11) _
            (regval_into_reg (register_lookup mhartid (s_pcc s pc b1).(sregs))) with "Hreg Hx11") as "[Hreg Hx11]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hmhv) in "Hx11".
    unfold sFcc, base_upd_c. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hx11 Hmhart Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hx11 Hmhart Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End StepCSRR.

(* ====================================================================== *)
(* wp_step_jal (2-aligned F_Base, control flow -- jump to start).          *)
(* ====================================================================== *)

Section StepJAL2.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Section CleanJAL.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).
    Definition base_upd_j : mstate :=
      set_reg
        (set_reg
           (set_reg
              (set_reg (set_reg s (R_bool minstret_increment) b)
                       nextPC (add_vec_int pc 4))
              nextPC (jtgt s pc b))
           (R_bitvector_64 x1) (regval_into_reg (add_vec_int pc 4)))
        PC (jtgt s pc b).
    Definition sFcj : mstate :=
      if b then set_reg base_upd_j minstret (add_vec_int mst0 1) else base_upd_j.

    Ltac tmij := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

    Lemma sFj_eq :
      register_lookup PC s.(sregs) = pc ->
      register_lookup minstret s.(sregs) = mst0 ->
      sFj s pc b = sFcj.
    Proof.
      intros LpcS LmstS.
      assert (Enpc : register_lookup nextPC (sXj s pc b).(sregs) = jtgt s pc b).
      { unfold sXj; cbv zeta. unfold set_reg; cbn [sregs]. tmij.
        rewrite register_lookup_set. reflexivity. }
      assert (Ejlink : jlink s pc b = add_vec_int pc 4).
      { unfold jlink, s_pcj; cbv zeta. unfold set_reg; cbn [sregs].
        rewrite register_lookup_set. reflexivity. }
      assert (HsT : sTj s pc b = base_upd_j).
      { unfold sTj. rewrite Enpc. unfold sXj, s_pcj, sAj; cbv zeta.
        rewrite Ejlink. unfold base_upd_j, s_pcj, sAj. reflexivity. }
      unfold sFj, sFcj. rewrite HsT. destruct b; [|reflexivity].
      assert (Emst : register_lookup minstret base_upd_j.(sregs)
                     = register_lookup minstret s.(sregs)).
      { unfold base_upd_j, set_reg; cbn [sregs]. tmij. tmij. tmij. tmij. tmij. reflexivity. }
      rewrite Emst LmstS. reflexivity.
    Qed.
  End CleanJAL.

  Lemma jtgt_eq (s : mstate) (pc : mword 64) (b : bool) :
    register_lookup PC s.(sregs) = pc ->
    jtgt s pc b = add_vec pc (sign_extend' 64 imm_jal).
  Proof.
    intro Lpc. unfold jtgt, s_pcj, sAj. unfold set_reg; cbn [sregs].
    rewrite irrelevant_register_set; [|vm_compute; reflexivity].
    rewrite irrelevant_register_set; [|vm_compute; reflexivity].
    rewrite Lpc. reflexivity.
  Qed.

  Lemma wp_step_jal (pc : mword 64)
      (b1 : bool) (x1_0 npc0 mstatus0 misa0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm_jal)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec pc (sign_extend' 64 imm_jal)) 1) = false ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ (R_bitvector_64 x1) ↦ᵣ x1_0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto misa dqc misa0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_jal j) -∗
    ▷ ( PC ↦ᵣ add_vec pc (sign_extend' 64 imm_jal) -∗
        (R_bitvector_64 x1) ↦ᵣ regval_into_reg (add_vec_int pc 4) -∗
        nextPC ↦ᵣ add_vec pc (sign_extend' 64 imm_jal) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto misa dqc misa0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_jal j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf Haddr Hal0 Hal1 Hb1 HmIE Help Hmisa HmisaS)
      "#Hinv Hpc Hx1 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa'") as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hjt : jtgt s pc b1 = add_vec pc (sign_extend' 64 imm_jal))
      by (apply jtgt_eq; exact Lpc).
    iEval (rewrite <- Lmisa) in "Hmisa'".
    iDestruct (fetch_from_pts_minstret_2 pc w_jal regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Haddr
                 ltac:(intros j Hj; destruct j as [|[|j]];
                       [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
                 ltac:(intros j Hj; destruct j as [|[|j]];
                       [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
                 ltac:(rewrite Lmisa; exact Hmisa)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa' Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcj s pc b1 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFj_eq s pc b1 (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_jal s pc b1 Hfetch_at Hsi_s Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaS.
      - rewrite Hjt. exact Hal0.
      - rewrite Hjt. exact Hal1. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iEval (rewrite Lmisa) in "Hmisa'".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ nextPC _ (jtgt s pc b1) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x1) _ (regval_into_reg (add_vec_int pc 4))
            with "Hreg Hx1") as "[Hreg Hx1]".
    iMod (reg_update _ PC _ (jtgt s pc b1) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hjt) in "Hpc". iEval (rewrite Hjt) in "Hnpc".
    unfold sFcj, base_upd_j. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hx1 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hx1 Hnpc Hpriv Hhs Hmdl Hms Hmisa' Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End StepJAL2.
