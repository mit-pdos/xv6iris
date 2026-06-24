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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpDecode.

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
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = false.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.

  Lemma exec_fetch_RVC_4 : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s).
  Proof using All.
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
      (exec_fetch_bytes_4 pc region w s HpcPC Hpriv Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hbit0 Hbit1 Hvalign)).
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
