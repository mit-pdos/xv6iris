(* WpEntry.v — extending the kernel-boot WP to all of _entry (auipc; ld; lui;
   csrr; addi; mul; add; jal start).  This file builds the RVC fetch path and
   the per-opcode step lemmas for the new instructions. *)
From Stdlib Require Import ZArith.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpDecode.
Require Import WpRvcBridge.
From iris.base_logic.lib Require Import invariants.
Require Export WpLeafCommon.
Require Import WpDecodeBridge.

(* ---------------------------------------------------------------------- *)
(* RVC fetch: a 4-byte-aligned 16-bit instruction reads 4 bytes and takes  *)
(* the F_RVC branch (low 16 bits).  Mirror of exec_fetch_done with isRVC=1. *)
(* ---------------------------------------------------------------------- *)


(* ---------------------------------------------------------------------- *)
(* currentlyEnabled Ext_Zca = true (needs the C extension enabled in misa). *)
(* ---------------------------------------------------------------------- *)



(* ==== compressed decode: walker + decode_C_lui ==== *)

(* a cE-Zca decode clause whose pattern is false collapses the and_boolM to false. *)

Definition rd_clui : regidx :=
  Regidx (autocast (T := mword)
            (subrange_vec_dec (subrange_vec_dec h_lui 11 7) (Z.sub regidx_bit_width 1) 0)).

Lemma decode_C_lui s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed h_lui) s = Some (C_LUI (imm_clui, rd_clui), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* ==== execute lemmas (generic register write) ==== *)



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

End StepGen.




Section ForwardLUI.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC h_lui, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).


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
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.



Section ForwardADD.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC h_add, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).


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
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode w_jal) s = Some (JAL (imm_jal, Regidx i_jal), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; unfold imm_jal, i_jal; decode_any s Hpriv ]. Qed.


Section ForwardJAL.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w_jal, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).


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




Section ForwardMUL.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w_mul, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).


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


Lemma decode_C_ADDI s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed h_addi) s = Some (C_ADDI (imm_caddi, rsd_caddi), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

Definition i_addi : mword 5 :=
  autocast (T := mword)
    (subrange_vec_dec (subrange_vec_dec h_addi 11 7) (Z.sub regidx_bit_width 1) 0).



Section ForwardADDI.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC h_addi, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).


End ForwardADDI.

(* ====================================================================== *)
(* RVC 4-byte fetch SL wrapper + wp_step_lui + wp_step_add (4-aligned RVC). *)
(* ====================================================================== *)
Section WpFetchRVC.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.

End WpFetchRVC.

Section StepLUI.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.

  Section CleanLUI.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).

    Ltac tmilu := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  End CleanLUI.

End StepLUI.

Section StepADD.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.


  Section CleanADD.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).

    Ltac tmiad := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  End CleanADD.

End StepADD.

(* ====================================================================== *)
(* wp_step_mul (4-aligned F_Base, M-ext).                                  *)
(* ====================================================================== *)

Section StepMUL.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.


  Section CleanMUL.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).

    Ltac tmim := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  End CleanMUL.

End StepMUL.

(* ====================================================================== *)
(* CSRR (csrr a1,mhartid) -- forward_exec_csrr (F_Base, fetch-agnostic).    *)
(* ====================================================================== *)


Lemma decode_csrr s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode w_csrr) s
    = Some (CSRReg (csr_csrr, Regidx i_rs1_csrr, Regidx i_rd_csrr, CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; unfold csr_csrr, i_rs1_csrr, i_rd_csrr; decode_any s Hpriv ]. Qed.



Section ForwardCSRR.
  Context (s : mstate) (pc : mword 64) (b : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w_csrr, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).


End ForwardCSRR.

(* ====================================================================== *)
(* RVC 2-byte fetch SL wrapper + wp_step_addi (2-aligned RVC).             *)
(* ====================================================================== *)

Section WpFetchRVC2.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.

End WpFetchRVC2.

Section StepADDI.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.


  Section CleanADDI.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).

    Ltac tmiai := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  End CleanADDI.

End StepADDI.

(* ====================================================================== *)
(* wp_step_csrr (2-aligned F_Base).                                        *)
(* ====================================================================== *)

Section StepCSRR.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.


  Section CleanCSRR.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).

    Ltac tmic := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  End CleanCSRR.

End StepCSRR.

(* ====================================================================== *)
(* wp_step_jal (2-aligned F_Base, control flow -- jump to start).          *)
(* ====================================================================== *)

Section StepJAL2.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.

  Section CleanJAL.
    Context (s : mstate) (pc : mword 64) (b : bool) (mst0 : mword 64).

    Ltac tmij := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  End CleanJAL.


End StepJAL2.
