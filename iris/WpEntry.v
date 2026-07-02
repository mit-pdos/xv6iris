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
Require Export WpLeafCommon.

(* ---------------------------------------------------------------------- *)
(* RVC fetch: a 4-byte-aligned 16-bit instruction reads 4 bytes and takes  *)
(* the F_RVC branch (low 16 bits).  Mirror of exec_fetch_done with isRVC=1. *)
(* ---------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------- *)
(* currentlyEnabled Ext_Zca = true (needs the C extension enabled in misa). *)
(* ---------------------------------------------------------------------- *)



(* ==== compressed decode: walker + decode_C_lui ==== *)

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

End ForwardADD.

(* ====================================================================== *)
(* JAL (control flow) -- the "jump to start" capstone.                     *)
(* ====================================================================== *)
Definition w_jal : mword 32 := mword_of_int 0x42000ef.
Definition i_jal : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_jal 11 7) (regidx_bit_width - 1) 0).
Definition imm_jal : mword 21 :=
  concat_vec (concat_vec (concat_vec (concat_vec
    (subrange_vec_dec w_jal 31 31) (subrange_vec_dec w_jal 19 12))
    (subrange_vec_dec w_jal 20 20)) (subrange_vec_dec w_jal 30 21)) ('b"0").

Lemma decode_jal s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode w_jal) s = Some (JAL (imm_jal, Regidx i_jal), s).
Proof. intro Hpriv. unfold imm_jal, i_jal. decode_any s Hpriv. Qed.

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

Lemma decode_mul s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
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
  { destruct (exec_cE_zicfilp_mSU s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz). destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with false by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_returnM (@None instruction) s). cbn match.
  skip_pure_clauses.
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

End ForwardMUL.

(* ====================================================================== *)
(* ADDI (RVC, 2-aligned) -- width-2 fetch stack + forward_exec_addi.        *)
(* ====================================================================== *)

(* ====================================================================== *)
(* Width-2 mem-read stack (mirror of the width-4 stack in RiscvFetchExec). *)
(* ====================================================================== *)



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
    iIntros (Hmatch0 Hexec Hpmp0 Hvalign HisRVC)
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
    assert (Hpmp : forall i,
              pmpLocked (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) i) = false)
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

Lemma decode_csrr s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode w_csrr) s
    = Some (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx i_rd_csrr, CSRRS), s).
Proof. intro Hpriv. unfold csr_csrr, i_rs1_csrr, i_rd_csrr. decode_any s Hpriv. Qed.

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
    assert (Hpmp : forall i,
              pmpLocked (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) i) = false)
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

End StepADDI.

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

End StepJAL2.
