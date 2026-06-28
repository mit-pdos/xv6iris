(* WpStart2.v -- the chunked WP for start() (kernel_instrs idx 30..63), built
   on top of WpStartChain (decode lemmas, wp_auipc_gpr, ti_ctx, regroup/EW infra).
   Separate file so editing the chunks recompiles only this file, not the
   ~180-lemma WpStartChain.  COMPILE:
   coqc -R . xv6iris -R /shared/xv6rocq/model-xv6iris Riscv -R /shared/xv6rocq/kernel-rocq Kernel WpStart2.v *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpDecode WpEntry WpGpr WpRvc WpAlu2 WpGprCsrrAny WpGprCsrw KernelBoot WpStartText.
Require Import WpAuipc WpGprLui WpGprAddi WpGprJal.
Require Import WpStartChain.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.

Section WpStart2.
  Context `{!riscvGS Σ}.

  Local Ltac vmc := vm_compute; reflexivity.

  (* --- decode tactics (re-defined here; the WpStartChain copies are
         section-local Ltac and don't cross the file boundary). --- *)
  Ltac reg_step name w hi lo s :=
    assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
                = Some (Regidx (autocast (T := mword)
                          (subrange_vec_dec (subrange_vec_dec w hi lo)
                             (Z.sub regidx_bit_width 1) 0)), s));
    [ unfold encdec_reg_backwards;
      match goal with |- context[if ?g then returnM (Regidx _) else _] =>
        replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
    | idtac ].

  Ltac csr_prefix w s Hpriv :=
    unfold ext_decode, encdec_backwards; cbv beta; cbn zeta;
    skip_pure_clause; skip_pure_clause;
    match goal with |- context[eq_vec w ?c] =>
      replace (eq_vec w c) with false by (vm_compute; reflexivity) end;
    match goal with |- context[eq_vec (subrange_vec_dec w 11 0) ?c] =>
      replace (eq_vec (subrange_vec_dec w 11 0) c) with false by (vm_compute; reflexivity) end;
    let HA1 := fresh "HA1" in
    assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_pause s) as [bp Hbp]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp); destruct bp; [apply exec_returnm | reflexivity]);
    rewrite (exec_bind_Some _ _ _ _ _ HA1); cbn match; rewrite exec_bind;
    let HA2 := fresh "HA2" in
    assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]);
    rewrite (exec_bind_Some _ _ _ _ _ HA2); cbn match;
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with false by (vm_compute; reflexivity) end;
    cbn match; rewrite (exec_returnM (@None instruction) s); cbn match;
    repeat skip_pure_clause.

  Ltac csr_body w s op_eq :=
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end;
    cbn match; rewrite exec_bind;
    let Hr1 := fresh "Hr1" in
    assert (Hr1 : exec (encdec_reg_backwards (subrange_vec_dec w 19 15)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 19 15) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    let Hco := fresh "Hco" in
    assert (Hco : exec (encdec_csrop_backwards (subrange_vec_dec w 13 12)) s = Some (op_eq, s))
      by (unfold encdec_csrop_backwards;
          first [ replace (eq_vec (subrange_vec_dec w 13 12) ('b"01")) with true by (vm_compute; reflexivity)
                | replace (eq_vec (subrange_vec_dec w 13 12) ('b"01")) with false by (vm_compute; reflexivity);
                  replace (eq_vec (subrange_vec_dec w 13 12) ('b"10")) with true by (vm_compute; reflexivity) ];
          cbn match; apply exec_returnM);
    let Hr2 := fresh "Hr2" in
    assert (Hr2 : exec (encdec_reg_backwards (subrange_vec_dec w 11 7)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    rewrite (exec_bind_Some _ _ _ _ _ Hr1);
    rewrite (exec_bind_Some _ _ _ _ _ Hco);
    rewrite (exec_bind_Some _ _ _ _ _ Hr2); cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicsr s));
    rewrite (exec_returnM _ s); cbn match; apply exec_returnM.

  Ltac itype_body w s op_eq :=
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end;
    cbn match;
    let Hr1 := fresh "Hr1" in
    assert (Hr1 : exec (encdec_reg_backwards (subrange_vec_dec w 19 15)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 19 15) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    let Hio := fresh "Hio" in
    assert (Hio : exec (encdec_iop_backwards (subrange_vec_dec w 14 12)) s = Some (op_eq, s))
      by (unfold encdec_iop_backwards;
          repeat (match goal with |- context[if ?g then returnM _ else _] =>
            first [ replace g with true by (vm_compute; reflexivity)
                  | replace g with false by (vm_compute; reflexivity) ] end; cbn match);
          apply exec_returnM);
    let Hr2 := fresh "Hr2" in
    assert (Hr2 : exec (encdec_reg_backwards (subrange_vec_dec w 11 7)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    rewrite exec_bind;
    rewrite (exec_bind_Some _ _ _ _ _ Hr1);
    rewrite (exec_bind_Some _ _ _ _ _ Hio);
    rewrite (exec_bind_Some _ _ _ _ _ Hr2); cbn match; apply exec_returnM.

  (* ===================================================================== *)
  (* START program counters: kentry + offset, idx 30..63.                  *)
  (* ===================================================================== *)
  Definition spc30 : mword 64 := mword_of_int (kentry + 0x58).
  Definition spc31 : mword 64 := mword_of_int (kentry + 0x5a).
  Definition spc32 : mword 64 := mword_of_int (kentry + 0x5c).
  Definition spc33 : mword 64 := mword_of_int (kentry + 0x5e).
  Definition spc34 : mword 64 := mword_of_int (kentry + 0x60).
  Definition spc35 : mword 64 := mword_of_int (kentry + 0x64).
  Definition spc36 : mword 64 := mword_of_int (kentry + 0x66).
  Definition spc37 : mword 64 := mword_of_int (kentry + 0x6a).
  Definition spc38 : mword 64 := mword_of_int (kentry + 0x6c).
  Definition spc39 : mword 64 := mword_of_int (kentry + 0x6e).
  Definition spc40 : mword 64 := mword_of_int (kentry + 0x72).
  Definition spc41 : mword 64 := mword_of_int (kentry + 0x74).
  Definition spc42 : mword 64 := mword_of_int (kentry + 0x78).
  Definition spc43 : mword 64 := mword_of_int (kentry + 0x7c).
  Definition spc44 : mword 64 := mword_of_int (kentry + 0x80).
  Definition spc45 : mword 64 := mword_of_int (kentry + 0x84).
  Definition spc46 : mword 64 := mword_of_int (kentry + 0x86).
  Definition spc47 : mword 64 := mword_of_int (kentry + 0x8a).
  Definition spc48 : mword 64 := mword_of_int (kentry + 0x8c).
  Definition spc49 : mword 64 := mword_of_int (kentry + 0x8e).
  Definition spc50 : mword 64 := mword_of_int (kentry + 0x92).
  Definition spc51 : mword 64 := mword_of_int (kentry + 0x96).
  Definition spc52 : mword 64 := mword_of_int (kentry + 0x9a).
  Definition spc53 : mword 64 := mword_of_int (kentry + 0x9e).
  Definition spc54 : mword 64 := mword_of_int (kentry + 0xa2).
  Definition spc55 : mword 64 := mword_of_int (kentry + 0xa4).
  Definition spc56 : mword 64 := mword_of_int (kentry + 0xa6).
  Definition spc57 : mword 64 := mword_of_int (kentry + 0xaa).
  Definition spc58 : mword 64 := mword_of_int (kentry + 0xac).
  Definition spc59 : mword 64 := mword_of_int (kentry + 0xb0).
  Definition spc60 : mword 64 := mword_of_int (kentry + 0xb4).
  Definition spc61 : mword 64 := mword_of_int (kentry + 0xb8).
  Definition spc62 : mword 64 := mword_of_int (kentry + 0xba).
  Definition spc63 : mword 64 := mword_of_int (kentry + 0xbc).

  (* ===================================================================== *)
  (* 32-bit START decode lemmas.  CSRReg / ITYPE / UTYPE-AUIPC / JAL / MRET.*)
  (* ===================================================================== *)

  (* idx 34: csrr a5,mstatus  enc 0x300027f3 -> CSRRS. *)
  Definition sw34 : mword 32 := mword_of_int 0x300027f3.
  Definition srs1z34 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec sw34 19 15) (regidx_bit_width - 1) 0).
  Definition srd34   : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec sw34 11 7) (regidx_bit_width - 1) 0).
  Lemma decode_s34 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw34) s = Some (CSRReg (subrange_vec_dec sw34 31 20, Regidx srs1z34, Regidx srd34, CSRRS), s).
  Proof. intro Hpriv. unfold srs1z34, srd34. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 42: auipc a5  enc 0x00001797 -> UTYPE (imm, rd, AUIPC). *)
  Definition sw42 : mword 32 := mword_of_int 0x00001797.
  Definition srd42 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec sw42 11 7) (regidx_bit_width - 1) 0).
  Lemma decode_s42 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw42) s = Some (UTYPE (subrange_vec_dec sw42 31 12, Regidx srd42, AUIPC), s).
  Proof.
    intro Hpriv. unfold srd42.
    unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
    skip_pure_clause. skip_pure_clause.
    match goal with |- context[eq_vec sw42 ?c] =>
      replace (eq_vec sw42 c) with false by (vm_compute; reflexivity) end.
    match goal with |- context[eq_vec (subrange_vec_dec sw42 11 0) ?c] =>
      replace (eq_vec (subrange_vec_dec sw42 11 0) c) with false by (vm_compute; reflexivity) end.
    assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_pause s) as [bp Hbp]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp); destruct bp; [apply exec_returnm | reflexivity]).
    rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match. rewrite exec_bind.
    assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]).
    rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match.
    unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn match.
    unfold encdec_uop_backwards.
    match goal with |- context[if ?g then returnM LUI else _] =>
      replace g with false by (vm_compute; reflexivity) end.
    match goal with |- context[if ?g then returnM AUIPC else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn match.
    match goal with |- context[exec (returnM ?x) s] => rewrite (exec_returnM x s) end.
    cbn match. cbn match. apply exec_returnM.
  Qed.

  (* --- CSRReg decodes (csrr CSRRS / csrw CSRRW). --- *)
  Definition scsr_rs1z (w : mword 32) : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w 19 15) (regidx_bit_width - 1) 0).
  Definition scsr_rd   (w : mword 32) : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0).

  (* idx 41: csrw mstatus,a5  0x30079073 -> CSRRW (rs1=a5, zreg). *)
  Definition sw41 : mword 32 := mword_of_int 0x30079073.
  Lemma decode_s41 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw41) s = Some (CSRReg (subrange_vec_dec sw41 31 20, Regidx (scsr_rs1z sw41), Regidx (scsr_rd sw41), CSRRW), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 44: csrw mepc,a5  0x34179073 -> CSRRW. *)
  Definition sw44 : mword 32 := mword_of_int 0x34179073.
  Lemma decode_s44 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw44) s = Some (CSRReg (subrange_vec_dec sw44 31 20, Regidx (scsr_rs1z sw44), Regidx (scsr_rd sw44), CSRRW), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 46: csrw satp,a5  0x18079073 -> CSRRW. *)
  Definition sw46 : mword 32 := mword_of_int 0x18079073.
  Lemma decode_s46 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw46) s = Some (CSRReg (subrange_vec_dec sw46 31 20, Regidx (scsr_rs1z sw46), Regidx (scsr_rd sw46), CSRRW), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 49: csrw medeleg,a5  0x30279073 -> CSRRW. *)
  Definition sw49 : mword 32 := mword_of_int 0x30279073.
  Lemma decode_s49 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw49) s = Some (CSRReg (subrange_vec_dec sw49 31 20, Regidx (scsr_rs1z sw49), Regidx (scsr_rd sw49), CSRRW), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 50: csrw mideleg,a5  0x30379073 -> CSRRW. *)
  Definition sw50 : mword 32 := mword_of_int 0x30379073.
  Lemma decode_s50 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw50) s = Some (CSRReg (subrange_vec_dec sw50 31 20, Regidx (scsr_rs1z sw50), Regidx (scsr_rd sw50), CSRRW), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 51: csrr a5,sie  0x104027f3 -> CSRRS. *)
  Definition sw51 : mword 32 := mword_of_int 0x104027f3.
  Lemma decode_s51 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw51) s = Some (CSRReg (subrange_vec_dec sw51 31 20, Regidx (scsr_rs1z sw51), Regidx (scsr_rd sw51), CSRRS), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 53: csrw sie,a5  0x10479073 -> CSRRW. *)
  Definition sw53 : mword 32 := mword_of_int 0x10479073.
  Lemma decode_s53 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw53) s = Some (CSRReg (subrange_vec_dec sw53 31 20, Regidx (scsr_rs1z sw53), Regidx (scsr_rd sw53), CSRRW), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 56: csrw pmpaddr0,a5  0x3b079073 -> CSRRW. *)
  Definition sw56 : mword 32 := mword_of_int 0x3b079073.
  Lemma decode_s56 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw56) s = Some (CSRReg (subrange_vec_dec sw56 31 20, Regidx (scsr_rs1z sw56), Regidx (scsr_rd sw56), CSRRW), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 58: csrw pmpcfg0,a5  0x3a079073 -> CSRRW. *)
  Definition sw58 : mword 32 := mword_of_int 0x3a079073.
  Lemma decode_s58 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw58) s = Some (CSRReg (subrange_vec_dec sw58 31 20, Regidx (scsr_rs1z sw58), Regidx (scsr_rd sw58), CSRRW), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 60: csrr a5,mhartid  0xf14027f3 -> CSRRS. *)
  Definition sw60 : mword 32 := mword_of_int 0xf14027f3.
  Lemma decode_s60 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw60) s = Some (CSRReg (subrange_vec_dec sw60 31 20, Regidx (scsr_rs1z sw60), Regidx (scsr_rd sw60), CSRRS), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* --- ITYPE decodes (addi / ori). --- *)
  Definition sit_rs1 (w : mword 32) : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w 19 15) (regidx_bit_width - 1) 0).
  Definition sit_rd  (w : mword 32) : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0).

  (* idx 36: addi a4,a4,...  0x7ff70713 -> ITYPE ADDI. *)
  Definition sw36 : mword 32 := mword_of_int 0x7ff70713.
  Lemma decode_s36 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw36) s = Some (ITYPE (subrange_vec_dec sw36 31 20, Regidx (sit_rs1 sw36), Regidx (sit_rd sw36), ADDI), s).
  Proof. intro Hpriv. unfold sit_rs1, sit_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 39: addi a4,a4,...  0x80070713 -> ITYPE ADDI. *)
  Definition sw39 : mword 32 := mword_of_int 0x80070713.
  Lemma decode_s39 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw39) s = Some (ITYPE (subrange_vec_dec sw39 31 20, Regidx (sit_rs1 sw39), Regidx (sit_rd sw39), ADDI), s).
  Proof. intro Hpriv. unfold sit_rs1, sit_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 43: addi a5,a5,...  0xe0a78793 -> ITYPE ADDI. *)
  Definition sw43 : mword 32 := mword_of_int 0xe0a78793.
  Lemma decode_s43 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw43) s = Some (ITYPE (subrange_vec_dec sw43 31 20, Regidx (sit_rs1 sw43), Regidx (sit_rd sw43), ADDI), s).
  Proof. intro Hpriv. unfold sit_rs1, sit_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 52: ori a5,a5,...  0x2207e793 -> ITYPE ORI. *)
  Definition sw52 : mword 32 := mword_of_int 0x2207e793.
  Lemma decode_s52 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw52) s = Some (ITYPE (subrange_vec_dec sw52 31 20, Regidx (sit_rs1 sw52), Regidx (sit_rd sw52), ORI), s).
  Proof. intro Hpriv. unfold sit_rs1, sit_rd. decode_pause_prefix s Hpriv. decode_finish s. Qed.

  (* idx 59: jal ra,timerinit  0xf6dff0ef -> JAL (imm, rd=ra). *)
  Definition sw59 : mword 32 := mword_of_int 0xf6dff0ef.
  Definition sjal_imm : mword 21 :=
    concat_vec (concat_vec (concat_vec (concat_vec
      (subrange_vec_dec sw59 31 31) (subrange_vec_dec sw59 19 12))
      (subrange_vec_dec sw59 20 20)) (subrange_vec_dec sw59 30 21)) ('b"0").
  Definition sjal_rd : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec sw59 11 7) (regidx_bit_width - 1) 0).
  Lemma decode_s59 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw59) s = Some (JAL (sjal_imm, Regidx sjal_rd), s).
  Proof.
    intro Hpriv. unfold sjal_imm, sjal_rd.
    unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
    skip_pure_clause. skip_pure_clause.
    match goal with |- context[eq_vec sw59 ?c] =>
      replace (eq_vec sw59 c) with false by (vm_compute; reflexivity) end.
    match goal with |- context[eq_vec (subrange_vec_dec sw59 11 0) ?c] =>
      replace (eq_vec (subrange_vec_dec sw59 11 0) c) with false by (vm_compute; reflexivity) end.
    assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_pause s) as [bp Hbp]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp); destruct bp; [apply exec_returnm | reflexivity]).
    rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match. rewrite exec_bind.
    assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]).
    rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with false by (vm_compute; reflexivity) end.
    cbn match. rewrite (exec_returnM (@None instruction) s). cbn match.
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. rewrite exec_bind.
    unfold encdec_reg_backwards.
    match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn match.
    match goal with |- context[exec (returnM ?x) s] => rewrite (exec_returnM x s) end.
    cbn match. cbn match. apply exec_returnM.
  Qed.

  (* 4-aligned RVC fetch uses kinstr_rvc4 (WpStartText): the 4-byte window of
     skinstr N alone, no regrouping / stwin4 / strem. *)

  (* --- generalized decode4 lemmas: decode hyp over SOME w whose low 16 bits
         are the RVC encoding (kinstr_rvc4 supplies the [subrange] agreement). --- *)
  Lemma decode4_s30 (w : mword 32) :
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int 0x1141 : mword 32) 15 0 ->
    forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s = Some (C_ADDI (imm9, Regidx rd9), s).
  Proof.
    intros Hsub s HmisaC. rewrite Hsub.
    replace (subrange_vec_dec (mword_of_int 0x1141 : mword 32) 15 0) with w9
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode9; exact HmisaC.
  Qed.
  Lemma decode4_s32 (w : mword 32) :
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int 0xe022 : mword 32) 15 0 ->
    forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s = Some (C_SDSP (uimm11, Regidx rs2_11), s).
  Proof.
    intros Hsub s HmisaC. rewrite Hsub.
    replace (subrange_vec_dec (mword_of_int 0xe022 : mword 32) 15 0) with w11
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode11; exact HmisaC.
  Qed.
  Lemma decode4_s35 (w : mword 32) :
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int 0x7779 : mword 32) 15 0 ->
    forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s = Some (C_LUI (sclui_imm sw35, Regidx (sreg117 sw35)), s).
  Proof.
    intros Hsub s HmisaC. rewrite Hsub.
    replace (subrange_vec_dec (mword_of_int 0x7779 : mword 32) 15 0) with sw35
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode_s35; exact HmisaC.
  Qed.
  Lemma decode4_s38 (w : mword 32) :
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int 0x6705 : mword 32) 15 0 ->
    forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s = Some (C_LUI (sclui_imm sw38, Regidx (sreg117 sw38)), s).
  Proof.
    intros Hsub s HmisaC. rewrite Hsub.
    replace (subrange_vec_dec (mword_of_int 0x6705 : mword 32) 15 0) with sw38
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode_s38; exact HmisaC.
  Qed.
  Lemma decode4_s45 (w : mword 32) :
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int 0x4781 : mword 32) 15 0 ->
    forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s = Some (C_LI (scli_imm sw45, Regidx (sreg117 sw45)), s).
  Proof.
    intros Hsub s HmisaC. rewrite Hsub.
    replace (subrange_vec_dec (mword_of_int 0x4781 : mword 32) 15 0) with sw45
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode_s45; exact HmisaC.
  Qed.
  Lemma decode4_s48 (w : mword 32) :
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int 0x17fd : mword 32) 15 0 ->
    forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s = Some (C_ADDI (scli_imm sw48, Regidx (sreg117 sw48)), s).
  Proof.
    intros Hsub s HmisaC. rewrite Hsub.
    replace (subrange_vec_dec (mword_of_int 0x17fd : mword 32) 15 0) with sw48
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode_s48; exact HmisaC.
  Qed.
  Lemma decode4_s55 (w : mword 32) :
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int 0x83a9 : mword 32) 15 0 ->
    forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s = Some (C_SRLI (scsrli_sh sw55, scsrli_crsd), s).
  Proof.
    intros Hsub s HmisaC. rewrite Hsub.
    replace (subrange_vec_dec (mword_of_int 0x83a9 : mword 32) 15 0) with sw55
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode_s55; exact HmisaC.
  Qed.
  Lemma decode4_s61 (w : mword 32) :
    subrange_vec_dec w 15 0 = subrange_vec_dec (mword_of_int 0x2781 : mword 32) 15 0 ->
    forall s, eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s = Some (C_ADDIW (scaddiw_imm sw61, Regidx (sreg117 sw61)), s).
  Proof.
    intros Hsub s HmisaC. rewrite Hsub.
    replace (subrange_vec_dec (mword_of_int 0x2781 : mword 32) 15 0) with sw61
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode_s61; exact HmisaC.
  Qed.

  (* ===================================================================== *)
  (* CHUNK wp_st_c1 : idx 30-34.  Start's stack-frame setup + csrr mstatus. *)
  (* C_ADDI sp-16 ; c.sdsp ra ; c.sdsp s0 ; c.addi4spn s0 ; csrr a5,mstatus.*)
  (* Mirrors wp_ti_c1 exactly (same shapes; csrr is mstatus instead).       *)
  (* ===================================================================== *)
  Lemma wp_st_c1
      (sp0 vra vs0 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) (vold_ra vold_s0 : bv 64)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump := mbump b1 in
    let sp1  := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm9)) in
    let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
    let pa_ra  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
    let pa_s0  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let a8_ra  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
    let a8_s0  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
    let mout := <[gpr_of_Z (uint srd34) := regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0)]>
                (<[gpr_of_Z (uint r_s0) := regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12)))]>
                (<[gpr_of_Z (uint rd9) := regval_into_reg sp1]> m)) in
    m !! gpr_of_Z 1 = Some vra -> m !! gpr_of_Z 2 = Some sp0 ->
    m !! gpr_of_Z 8 = Some vs0 -> m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true -> is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true -> is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    PC ↦ᵣ spc30 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    ti_ctx misa0 mstatus0 mseccfg0 (zeros' 64) mc mcfg pmpcfg0 pmar0 elp0 -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vold_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vold_s0 j) -∗
    kernel_text -∗
    ▷ ( PC ↦ᵣ spc35 -∗ gpr_file mout -∗ nextPC ↦ᵣ spc35 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ bump (bump (bump (bump (bump mst0)))) -∗
        menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
        ti_ctx misa0 mstatus0 mseccfg0 (zeros' 64) mc mcfg pmpcfg0 pmar0 elp0 -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vra j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vs0 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 bump sp1 imm_ra pa_ra imm_s0 pa_s0 a8_ra a8_s0 mout.
    intros Hm1 Hm2 Hm8 Hm15 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm HmisaC HmisaS HmisaU Ha8ra Hpara Ha8s0 Hpas0.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx Hstkra Hstks0 #H".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iIntros "Hcont".
    (* idx 30: C_ADDI sp,sp,-16 (4-byte window from skinstr 30 ++ 31) *)
    iAssert (kinstr_bytes (skinstr 30)) as "#K30". { sg 30. }
    iAssert (kinstr_bytes (skinstr 31)) as "#K31". { sg 31. }
    assert (Hk_a : ki_addr (skinstr 30) = kentry + 0x58) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 30) = 0x1141) by (vm_compute; reflexivity); iDestruct (kinstr_rvc4 (skinstr 30) (kentry + 0x58) (0x1141) Hk_a Hk_e with "K30") as (wr_s30) "[%Hsub_s30 #W30]"; clear Hk_a Hk_e.
    assert (Hrd30 : m !! gpr_of_Z (uint rd9) = Some sp0)
      by (replace (uint rd9) with 2 by (vm_compute; reflexivity); exact Hm2).
    iApply (wp_caddi_gpr_4 spc30 wr_s30 rd9 imm9 m sp0 misa0 (zeros' 64) b1
              npc0 mst0 mstatus0 mc mcfg pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; discriminate) Hrd30 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s30; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s30 wr_s30 Hsub_s30) eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W30").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc30 2) with spc31 by (vm_compute; reflexivity).
    assert (Hk_a : ki_addr (skinstr 31) = (kentry + 0x5a)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 31) = 0xe406) by (vm_compute; reflexivity); assert (Hk_w : (2 <= ki_width (skinstr 31) / 8)%nat) by (vm_compute; lia); iDestruct (kinstr_window16 (skinstr 31) (kentry + 0x5a) 0xe406 Hk_a Hk_e Hk_w with "K31") as "#W31"; clear Hk_a Hk_e Hk_w.
    (* idx 31: c.sdsp ra,8(sp) *)
    set (m30 := <[gpr_of_Z (uint rd9) := regval_into_reg sp1]> m).
    assert (Hsp31 : m30 !! gpr_of_Z (uint csp_rs1) = Some sp1).
    { unfold m30. replace (uint csp_rs1) with 2 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hra31 : m30 !! gpr_of_Z (uint rs2_10) = Some vra).
    { unfold m30. replace (uint rs2_10) with 1 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [exact Hm1 | discriminate]. }
    iApply (wp_csdsp spc31 w10 uimm10 rs2_10 m30 sp1 vra misa0 (zeros' 64) b1 vold_ra
              spc31 (bump mst0) mstatus0 mseccfg0
              mc mcfg pmpcfg0 pmar0 b1 elp0 E Φ
              ltac:(vm_compute; discriminate) Hsp31 Hra31 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode10 eq_refl HmIE Hlp HMPRV Hpmm Ha8ra Hpara
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstkra W31").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstkra _".
    replace (add_vec_int spc31 2) with spc32 by (vm_compute; reflexivity).
    (* idx 32: c.sdsp s0,0(sp) (4-byte window from skinstr 32 ++ 33) *)
    iAssert (kinstr_bytes (skinstr 32)) as "#K32". { sg 32. }
    iAssert (kinstr_bytes (skinstr 33)) as "#K33". { sg 33. }
    assert (Hk_a : ki_addr (skinstr 32) = kentry + 0x5c) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 32) = 0xe022) by (vm_compute; reflexivity); iDestruct (kinstr_rvc4 (skinstr 32) (kentry + 0x5c) (0xe022) Hk_a Hk_e with "K32") as (wr_s32) "[%Hsub_s32 #W32]"; clear Hk_a Hk_e.
    assert (Hsp32 : m30 !! gpr_of_Z (uint csp_rs1) = Some sp1).
    { unfold m30. replace (uint csp_rs1) with 2 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hs032 : m30 !! gpr_of_Z (uint rs2_11) = Some vs0).
    { unfold m30. replace (uint rs2_11) with 8 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [exact Hm8 | discriminate]. }
    iApply (wp_csdsp_4 spc32 wr_s32 uimm11 rs2_11 m30 sp1 vs0 misa0 (zeros' 64) b1 vold_s0
              _ _ mstatus0 mseccfg0
              mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Hsp32 Hs032 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s32; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s32 wr_s32 Hsub_s32) eq_refl HmIE Hlp HMPRV Hpmm Ha8s0 Hpas0
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstks0 W32").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstks0 _".
    replace (add_vec_int spc32 2) with spc33 by (vm_compute; reflexivity).
    assert (Hk_a : ki_addr (skinstr 33) = (kentry + 0x5e)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 33) = 0x0800) by (vm_compute; reflexivity); assert (Hk_w : (2 <= ki_width (skinstr 33) / 8)%nat) by (vm_compute; lia); iDestruct (kinstr_window16 (skinstr 33) (kentry + 0x5e) 0x0800 Hk_a Hk_e Hk_w with "K33") as "#W33"; clear Hk_a Hk_e Hk_w.
    (* idx 33: c.addi4spn s0,sp,16 *)
    assert (Hsp33 : m30 !! gpr_of_Z (uint csp_rs1) = Some sp1).
    { unfold m30. replace (uint csp_rs1) with 2 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hs033 : m30 !! gpr_of_Z (uint r_s0) = Some vs0).
    { unfold m30. replace (uint r_s0) with 8 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [exact Hm8 | discriminate]. }
    iApply (wp_caddi4spn_gpr spc33 w12 nzimm12 crdc12 r_s0 m30 sp1 vs0 misa0 (zeros' 64) b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vm_compute; discriminate) Hsp33 Hs033 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode12 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W33").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc33 2) with spc34 by (vm_compute; reflexivity).
    set (m32 := <[gpr_of_Z (uint r_s0) := regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12)))]> m30).
    iAssert (kinstr_bytes (skinstr 34)) as "#K34". { sg 34. }
    assert (Hk_a : ki_addr (skinstr 34) = (kentry + 0x60)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 34) = 0x300027f3) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 34) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 34) (kentry + 0x60) 0x300027f3 Hk_a Hk_e Hk_w with "K34") as "#W34"; clear Hk_a Hk_e Hk_w.
    (* idx 34: csrr a5,mstatus *)
    assert (Ha534 : m32 !! gpr_of_Z (uint srd34) = Some va5).
    { unfold m32, m30. replace (uint srd34) with 15 by (vm_compute; reflexivity).
      replace (uint r_s0) with 8 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [| discriminate]. exact Hm15. }
    iApply (wp_csrr_mstatus_gpr spc34 sw34 srs1z34 srd34 m32 va5 b1
              _ _ mstatus0 misa0 (zeros' 64) mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vmc) ltac:(vm_compute; discriminate) Ha534 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode_s34 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W34").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc34 4) with spc35 by (vm_compute; reflexivity).
    (* kernel_text is duplicable: no reassembly, no window-return. *)
    with_strategy transparent [mbump] (iApply ("Hcont" with "Hpc [Hfile] Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc
              [Hmisa Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif]
              Hstkra Hstks0")).
    { unfold mout, m32, m30. iExact "Hfile". }
    { iFrame. }
  Qed.

  (* ===================================================================== *)
  (* CHUNK wp_st_c2 : idx 35-40.  C_LUI a4 ; addi a4 ; c.and a5,a5,a4 ;     *)
  (* C_LUI a4 ; addi a4 ; c.or a5,a5,a4.   Reads a4,a5; writes a4,a5.       *)
  (* ===================================================================== *)
  (* c.and (idx37, 0x8ff9): rsd=a5, rs2=a4 (cregidx). *)
  Definition scand37_rsd : cregidx := Cregidx (subrange_vec_dec sw37 9 7).
  Definition scand37_rs2 : cregidx := Cregidx (subrange_vec_dec sw37 4 2).

  Lemma wp_st_c2
      (va4 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump := mbump b1 in
    let va4_35 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw35)) in
    let va4_36 := add_vec va4_35 (sign_extend' 64 (subrange_vec_dec sw36 31 20)) in
    let va5_37 := and_vec va5 va4_36 in
    let va4_38 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw38)) in
    let va4_39 := add_vec va4_38 (sign_extend' 64 (subrange_vec_dec sw39 31 20)) in
    let va5_40 := or_vec va5_37 va4_39 in
    let mout := <[gpr_of_Z (uint r_a5) := regval_into_reg va5_40]>
                (<[gpr_of_Z (uint (sit_rd sw39)) := regval_into_reg va4_39]>
                (<[gpr_of_Z (uint (sreg117 sw38)) := regval_into_reg va4_38]>
                (<[gpr_of_Z (uint r_a5) := regval_into_reg va5_37]>
                (<[gpr_of_Z (uint (sit_rd sw36)) := regval_into_reg va4_36]>
                (<[gpr_of_Z (uint (sreg117 sw35)) := regval_into_reg va4_35]> m))))) in
    m !! gpr_of_Z 14 = Some va4 -> m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    PC ↦ᵣ spc35 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    ti_ctx misa0 mstatus0 mseccfg0 (zeros' 64) mc mcfg pmpcfg0 pmar0 elp0 -∗
    kernel_text -∗
    ▷ ( PC ↦ᵣ spc41 -∗ gpr_file mout -∗ nextPC ↦ᵣ spc41 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ bump (bump (bump (bump (bump (bump mst0))))) -∗
        menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
        ti_ctx misa0 mstatus0 mseccfg0 (zeros' 64) mc mcfg pmpcfg0 pmar0 elp0 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 bump va4_35 va4_36 va5_37 va4_38 va4_39 va5_40 mout.
    intros Hm14 Hm15 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaS.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx #H".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iIntros "Hcont".
    (* idx 35: C_LUI a4 (4-byte window from skinstr 35 ++ 36; idx 36 is 32-bit, 2 bytes remain) *)
    iAssert (kinstr_bytes (skinstr 35)) as "#K35". { sg 35. }
    iAssert (kinstr_bytes (skinstr 36)) as "#K36". { sg 36. }
    assert (Hk_a : ki_addr (skinstr 35) = kentry + 0x64) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 35) = 0x7779) by (vm_compute; reflexivity); iDestruct (kinstr_rvc4 (skinstr 35) (kentry + 0x64) (0x7779) Hk_a Hk_e with "K35") as (wr_s35) "[%Hsub_s35 #W35]"; clear Hk_a Hk_e.
    assert (Ha435 : m !! gpr_of_Z (uint (sreg117 sw35)) = Some va4)
      by (replace (uint (sreg117 sw35)) with 14 by (vm_compute; reflexivity); exact Hm14).
    iApply (wp_clui_gpr_4 spc35 wr_s35 (sreg117 sw35) (sclui_imm sw35) m va4 misa0 (zeros' 64) b1
              npc0 mst0 mstatus0 mc mcfg pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; discriminate) Ha435 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s35; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s35 wr_s35 Hsub_s35) eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W35").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc35 2) with spc36 by (vm_compute; reflexivity).
    set (m35 := <[gpr_of_Z (uint (sreg117 sw35)) := regval_into_reg va4_35]> m).
    assert (Hk_a : ki_addr (skinstr 36) = (kentry + 0x66)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 36) = 0x7ff70713) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 36) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 36) (kentry + 0x66) 0x7ff70713 Hk_a Hk_e Hk_w with "K36") as "#W36"; clear Hk_a Hk_e Hk_w.
    (* idx 36: addi a4,a4,imm *)
    assert (Ha436a : m35 !! gpr_of_Z (uint (sit_rs1 sw36)) = Some va4_35).
    { unfold m35, va4_35. replace (uint (sit_rs1 sw36)) with 14 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw35)) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Ha436b : m35 !! gpr_of_Z (uint (sit_rd sw36)) = Some va4_35).
    { unfold m35, va4_35. replace (uint (sit_rd sw36)) with 14 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw35)) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_addi_gpr_2 spc36 sw36 (sit_rs1 sw36) (sit_rd sw36) (subrange_vec_dec sw36 31 20) m35
              va4_35 va4_35 misa0 (zeros' 64) b1 _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha436a Ha436b Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC HmisaS decode_s36 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W36").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc36 4) with spc37 by (vm_compute; reflexivity).
    set (m36 := <[gpr_of_Z (uint (sit_rd sw36)) := regval_into_reg va4_36]> m35).
    iAssert (kinstr_bytes (skinstr 37)) as "#K37". { sg 37. }
    assert (Hk_a : ki_addr (skinstr 37) = (kentry + 0x6a)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 37) = 0x8ff9) by (vm_compute; reflexivity); assert (Hk_w : (2 <= ki_width (skinstr 37) / 8)%nat) by (vm_compute; lia); iDestruct (kinstr_window16 (skinstr 37) (kentry + 0x6a) 0x8ff9 Hk_a Hk_e Hk_w with "K37") as "#W37"; clear Hk_a Hk_e Hk_w.
    (* idx 37: c.and a5,a5,a4 *)
    assert (Ha537 : m36 !! gpr_of_Z (uint r_a5) = Some va5).
    { unfold m36, m35. replace (uint r_a5) with 15 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw36)) with 14 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw35)) with 14 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate]. rewrite lookup_insert_ne; [exact Hm15 | discriminate]. }
    assert (Ha437 : m36 !! gpr_of_Z (uint r_a4) = Some va4_36).
    { unfold m36, va4_36. replace (uint r_a4) with 14 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw36)) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_cand_gpr spc37 sw37 scand37_rsd scand37_rs2 r_a5 r_a4 m36 va5 va4_36 misa0 (zeros' 64) b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vmc) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Ha537 Ha437 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode_s37 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W37").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc37 2) with spc38 by (vm_compute; reflexivity).
    set (m37 := <[gpr_of_Z (uint r_a5) := regval_into_reg va5_37]> m36).
    (* idx 38: C_LUI a4 (4-byte window from skinstr 38 ++ 39; idx 39 is 32-bit, 2 bytes remain) *)
    iAssert (kinstr_bytes (skinstr 38)) as "#K38". { sg 38. }
    iAssert (kinstr_bytes (skinstr 39)) as "#K39". { sg 39. }
    assert (Hk_a : ki_addr (skinstr 38) = kentry + 0x6c) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 38) = 0x6705) by (vm_compute; reflexivity); iDestruct (kinstr_rvc4 (skinstr 38) (kentry + 0x6c) (0x6705) Hk_a Hk_e with "K38") as (wr_s38) "[%Hsub_s38 #W38]"; clear Hk_a Hk_e.
    assert (Ha438 : m37 !! gpr_of_Z (uint (sreg117 sw38)) = Some va4_36).
    { unfold m37, m36, va4_36. replace (uint (sreg117 sw38)) with 14 by (vm_compute; reflexivity).
      replace (uint r_a5) with 15 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw36)) with 14 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate]. rewrite lookup_insert. reflexivity. }
    iApply (wp_clui_gpr_4 spc38 wr_s38 (sreg117 sw38) (sclui_imm sw38) m37 va4_36 misa0 (zeros' 64) b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha438 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s38; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s38 wr_s38 Hsub_s38) eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W38").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc38 2) with spc39 by (vm_compute; reflexivity).
    set (m38 := <[gpr_of_Z (uint (sreg117 sw38)) := regval_into_reg va4_38]> m37).
    assert (Hk_a : ki_addr (skinstr 39) = (kentry + 0x6e)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 39) = 0x80070713) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 39) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 39) (kentry + 0x6e) 0x80070713 Hk_a Hk_e Hk_w with "K39") as "#W39"; clear Hk_a Hk_e Hk_w.
    (* idx 39: addi a4,a4,imm *)
    assert (Ha439a : m38 !! gpr_of_Z (uint (sit_rs1 sw39)) = Some va4_38).
    { unfold m38, va4_38. replace (uint (sit_rs1 sw39)) with 14 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw38)) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Ha439b : m38 !! gpr_of_Z (uint (sit_rd sw39)) = Some va4_38).
    { unfold m38, va4_38. replace (uint (sit_rd sw39)) with 14 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw38)) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_addi_gpr_2 spc39 sw39 (sit_rs1 sw39) (sit_rd sw39) (subrange_vec_dec sw39 31 20) m38
              va4_38 va4_38 misa0 (zeros' 64) b1 _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha439a Ha439b Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC HmisaS decode_s39 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W39").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc39 4) with spc40 by (vm_compute; reflexivity).
    set (m39 := <[gpr_of_Z (uint (sit_rd sw39)) := regval_into_reg va4_39]> m38).
    iAssert (kinstr_bytes (skinstr 40)) as "#K40". { sg 40. }
    assert (Hk_a : ki_addr (skinstr 40) = (kentry + 0x72)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 40) = 0x8fd9) by (vm_compute; reflexivity); assert (Hk_w : (2 <= ki_width (skinstr 40) / 8)%nat) by (vm_compute; lia); iDestruct (kinstr_window16 (skinstr 40) (kentry + 0x72) 0x8fd9 Hk_a Hk_e Hk_w with "K40") as "#W40"; clear Hk_a Hk_e Hk_w.
    (* idx 40: c.or a5,a5,a4 (reuse decode16 / crsd16 / crs2_16 = a5,a4) *)
    assert (Ha540 : m39 !! gpr_of_Z (uint r_a5) = Some va5_37).
    { unfold m39, m38, m37, va5_37. replace (uint r_a5) with 15 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw39)) with 14 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw38)) with 14 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate]. rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert. reflexivity. }
    assert (Ha440 : m39 !! gpr_of_Z (uint r_a4) = Some va4_39).
    { unfold m39, va4_39. replace (uint r_a4) with 14 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw39)) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_cor_gpr spc40 w16e crsd16 crs2_16 r_a5 r_a4 m39 va5_37 va4_39 misa0 (zeros' 64) b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vmc) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Ha540 Ha440 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode16 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W40").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc40 2) with spc41 by (vm_compute; reflexivity).
    (* kernel_text is duplicable: no reassembly, no window-return. *)
    with_strategy transparent [mbump] (iApply ("Hcont" with "Hpc [Hfile] Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc
              [Hmisa Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif]")).
    { unfold mout, m39, m38, m37, m36, m35. iExact "Hfile". }
    { iFrame. }
  Qed.

  (* ===================================================================== *)
  (* CHUNK wp_st_c3 : idx 41-46.  csrw mstatus (sets MPP=Supervisor) ;      *)
  (* auipc a5 ; addi a5 ; csrw mepc (sets mret target) ; c.li a5 ;          *)
  (* csrw satp.   Writes mstatus, a5, mepc, satp.                           *)
  (* ===================================================================== *)
  Lemma wp_st_c3
      (va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 mepc0 satp0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump := mbump b1 in
    let mstatus1 := mstatus_legalized mstatus0 va5 in
    let va5_42 := add_vec spc42 (auipc_off (subrange_vec_dec sw42 31 12)) in
    let va5_43 := add_vec va5_42 (sign_extend' 64 (subrange_vec_dec sw43 31 20)) in
    let va5_45 := cli_wval (scli_imm sw45) in
    let mout := <[gpr_of_Z (uint (sreg117 sw45)) := regval_into_reg va5_45]>
                (<[gpr_of_Z (uint (sit_rd sw43)) := regval_into_reg va5_43]>
                (<[gpr_of_Z (uint srd42) := regval_into_reg va5_42]> m)) in
    m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    (* mstatus after idx 41 keeps MIE=0 and has SXL=10 (needed by satp). *)
    eq_vec (_get_Mstatus_MIE mstatus1) ('b"1") = false ->
    _get_Mstatus_SXL mstatus1 = 'b"10" ->
    PC ↦ᵣ spc41 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    mepc ↦ᵣ mepc0 -∗ satp ↦ᵣ satp0 -∗
    ti_ctx misa0 mstatus0 mseccfg0 (zeros' 64) mc mcfg pmpcfg0 pmar0 elp0 -∗
    kernel_text -∗
    ▷ ( PC ↦ᵣ spc47 -∗ gpr_file mout -∗ nextPC ↦ᵣ spc47 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ bump (bump (bump (bump (bump (bump mst0))))) -∗
        menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
        mepc ↦ᵣ mepc_val va5_43 -∗ satp ↦ᵣ satp_legalized satp0 va5_45 -∗
        ti_ctx misa0 mstatus1 mseccfg0 (zeros' 64) mc mcfg pmpcfg0 pmar0 elp0 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 bump mstatus1 va5_42 va5_43 va5_45 mout.
    intros Hm15 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaS HmisaU HmIE1 HSXL1.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hmepc Hsatp Hctx #H".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iIntros "Hcont".
    iAssert (kinstr_bytes (skinstr 41)) as "#K41". { sg 41. }
    assert (Hk_a : ki_addr (skinstr 41) = (kentry + 0x74)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 41) = 0x30079073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 41) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 41) (kentry + 0x74) 0x30079073 Hk_a Hk_e Hk_w with "K41") as "#W41"; clear Hk_a Hk_e Hk_w.
    (* idx 41: csrw mstatus,a5 *)
    assert (Ha541 : m !! gpr_of_Z (uint (scsr_rs1z sw41)) = Some va5)
      by (replace (uint (scsr_rs1z sw41)) with 15 by (vm_compute; reflexivity); exact Hm15).
    iApply (wp_csrw_mstatus_gpr spc41 sw41 (scsr_rs1z sw41) m va5 misa0 mstatus0 (zeros' 64) b1
              _ _ mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha541 HmisaS HmisaU Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode_s41 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W41").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc41 4) with spc42 by (vm_compute; reflexivity).
    iAssert (kinstr_bytes (skinstr 42)) as "#K42". { sg 42. }
    assert (Hk_a : ki_addr (skinstr 42) = (kentry + 0x78)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 42) = 0x00001797) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 42) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 42) (kentry + 0x78) 0x00001797 Hk_a Hk_e Hk_w with "K42") as "#W42"; clear Hk_a Hk_e Hk_w.
    (* idx 42: auipc a5 *)
    assert (Ha542 : m !! gpr_of_Z (uint srd42) = Some va5)
      by (replace (uint srd42) with 15 by (vm_compute; reflexivity); exact Hm15).
    iApply (wp_auipc_gpr spc42 sw42 srd42 (subrange_vec_dec sw42 31 12) m va5 b1
              _ _ mstatus1 misa0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha542 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode_s42 eq_refl HmIE1 Hlp HmisaS
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W42").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc42 4) with spc43 by (vm_compute; reflexivity).
    set (m42 := <[gpr_of_Z (uint srd42) := regval_into_reg va5_42]> m).
    iAssert (kinstr_bytes (skinstr 43)) as "#K43". { sg 43. }
    assert (Hk_a : ki_addr (skinstr 43) = (kentry + 0x7c)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 43) = 0xe0a78793) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 43) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 43) (kentry + 0x7c) 0xe0a78793 Hk_a Hk_e Hk_w with "K43") as "#W43"; clear Hk_a Hk_e Hk_w.
    (* idx 43: addi a5,a5,imm *)
    assert (Ha543a : m42 !! gpr_of_Z (uint (sit_rs1 sw43)) = Some va5_42).
    { unfold m42, va5_42. replace (uint (sit_rs1 sw43)) with 15 by (vm_compute; reflexivity).
      replace (uint srd42) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Ha543b : m42 !! gpr_of_Z (uint (sit_rd sw43)) = Some va5_42).
    { unfold m42, va5_42. replace (uint (sit_rd sw43)) with 15 by (vm_compute; reflexivity).
      replace (uint srd42) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_addi_gpr spc43 sw43 (sit_rs1 sw43) (sit_rd sw43) (subrange_vec_dec sw43 31 20) m42
              va5_42 va5_42 misa0 (zeros' 64) b1 _ _ mstatus1 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha543a Ha543b HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode_s43 eq_refl HmIE1 Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W43").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc43 4) with spc44 by (vm_compute; reflexivity).
    set (m43 := <[gpr_of_Z (uint (sit_rd sw43)) := regval_into_reg va5_43]> m42).
    iAssert (kinstr_bytes (skinstr 44)) as "#K44". { sg 44. }
    assert (Hk_a : ki_addr (skinstr 44) = (kentry + 0x80)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 44) = 0x34179073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 44) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 44) (kentry + 0x80) 0x34179073 Hk_a Hk_e Hk_w with "K44") as "#W44"; clear Hk_a Hk_e Hk_w.
    (* idx 44: csrw mepc,a5 *)
    assert (Ha544 : m43 !! gpr_of_Z (uint (scsr_rs1z sw44)) = Some va5_43).
    { unfold m43, va5_43. replace (uint (scsr_rs1z sw44)) with 15 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw43)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_mepc_gpr spc44 sw44 (scsr_rs1z sw44) m43 va5_43 mepc0 misa0 (zeros' 64) b1
              _ _ mstatus1 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha544 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode_s44 eq_refl HmIE1 Hlp
              with "Hpc Hfile Hmepc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W44").
    iNext.
    iIntros "Hpc Hfile Hmepc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc44 4) with spc45 by (vm_compute; reflexivity).
    iAssert (kinstr_bytes (skinstr 45)) as "#K45". { sg 45. }
    iAssert (kinstr_bytes (skinstr 46)) as "#K46". { sg 46. }
    assert (Hk_a : ki_addr (skinstr 45) = kentry + 0x84) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 45) = 0x4781) by (vm_compute; reflexivity); iDestruct (kinstr_rvc4 (skinstr 45) (kentry + 0x84) (0x4781) Hk_a Hk_e with "K45") as (wr_s45) "[%Hsub_s45 #W45]"; clear Hk_a Hk_e.
    (* idx 45: c.li a5 (regroup with idx 46, remainder) *)
    assert (Ha545 : m43 !! gpr_of_Z (uint (sreg117 sw45)) = Some va5_43).
    { unfold m43, va5_43. replace (uint (sreg117 sw45)) with 15 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw43)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_cli_gpr_4 spc45 wr_s45 (sreg117 sw45) (scli_imm sw45) m43 va5_43 misa0 (zeros' 64) b1
              _ _ mstatus1 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha545 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s45; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s45 wr_s45 Hsub_s45) eq_refl HmIE1 Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W45").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc45 2) with spc46 by (vm_compute; reflexivity).
    set (m45 := <[gpr_of_Z (uint (sreg117 sw45)) := regval_into_reg va5_45]> m43).
    assert (Hk_a : ki_addr (skinstr 46) = (kentry + 0x86)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 46) = 0x18079073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 46) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 46) (kentry + 0x86) 0x18079073 Hk_a Hk_e Hk_w with "K46") as "#W46"; clear Hk_a Hk_e Hk_w.
    (* idx 46: csrw satp,a5 *)
    assert (Ha546 : m45 !! gpr_of_Z (uint (scsr_rs1z sw46)) = Some va5_45).
    { unfold m45, va5_45. replace (uint (scsr_rs1z sw46)) with 15 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw45)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_satp_gpr_2 spc46 sw46 (scsr_rs1z sw46) m45 va5_45 misa0 mstatus1 satp0 (zeros' 64) b1
              _ _ mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha546 HmisaS HSXL1 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode_s46 eq_refl HmIE1 Hlp
              with "Hpc Hfile Hsatp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W46").
    iNext.
    iIntros "Hpc Hfile Hsatp Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc46 4) with spc47 by (vm_compute; reflexivity).
    (* kernel_text is duplicable: no reassembly, no window-return. *)
    with_strategy transparent [mbump] (iApply ("Hcont" with "Hpc [Hfile] Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hmepc Hsatp
              [Hmisa Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif]")).
    { unfold mout, m43, m42. iExact "Hfile". }
    { iFrame. }
  Qed.

  (* ===================================================================== *)
  (* CHUNK wp_st_c4 : idx 47-50.  c.lui a5 ; C_ADDI a5 ; csrw medeleg ;     *)
  (* csrw mideleg.   idx 50's csrw mideleg writes mideleg :=               *)
  (* mideleg_legalized 0 a5 = 0x2222 (nonzero).  The WP library has been   *)
  (* GENERALIZED (keystone guard now via misa.S=1, not mideleg=0), so every*)
  (* instruction WP now accepts ANY mideleg value via its `mdv0` param —   *)
  (* idx 51+ and timerinit can be threaded with mdv0 := this nonzero value.*)
  (* c4 returns the raw post-idx-50 state (mideleg nonzero); the follow-on *)
  (* chunks (c5..) instantiate mdv0 to mideleg_legalized (zeros' 64) va5_48.*)
  (* ===================================================================== *)
  Lemma wp_st_c4
      (va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 medeleg0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump := mbump b1 in
    let va5_47 := WpGprLui.luival (sign_extend' 20 (sclui_imm sw47)) in
    let va5_48 := add_vec va5_47 (sign_extend' 64 (sign_extend' 12 (scli_imm sw48))) in
    let mout := <[gpr_of_Z (uint (sreg117 sw48)) := regval_into_reg va5_48]>
                (<[gpr_of_Z (uint (sreg117 sw47)) := regval_into_reg va5_47]> m) in
    m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    PC ↦ᵣ spc47 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    medeleg ↦ᵣ medeleg0 -∗
    ti_ctx misa0 mstatus0 mseccfg0 (zeros' 64) mc mcfg pmpcfg0 pmar0 elp0 -∗
    kernel_text -∗
    ▷ ( PC ↦ᵣ spc51 -∗ gpr_file mout -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ spc51 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ bump (bump (bump (bump mst0))) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (* *** mideleg is now NONZERO (0x2222) — blocks all further WPs *** *)
        (R_bitvector_64 mideleg) ↦ᵣ mideleg_legalized (zeros' 64) va5_48 -∗
        (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        medeleg ↦ᵣ legalize_medeleg medeleg0 va5_48 -∗
        elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 bump va5_47 va5_48 mout.
    intros Hm15 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaS.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmede Hctx #H".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iIntros "Hcont".
    iAssert (kinstr_bytes (skinstr 47)) as "#K47". { sg 47. }
    assert (Hk_a : ki_addr (skinstr 47) = (kentry + 0x8a)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 47) = 0x67c1) by (vm_compute; reflexivity); assert (Hk_w : (2 <= ki_width (skinstr 47) / 8)%nat) by (vm_compute; lia); iDestruct (kinstr_window16 (skinstr 47) (kentry + 0x8a) 0x67c1 Hk_a Hk_e Hk_w with "K47") as "#W47"; clear Hk_a Hk_e Hk_w.
    (* idx 47: c.lui a5 (2-aligned) *)
    assert (Ha547 : m !! gpr_of_Z (uint (sreg117 sw47)) = Some va5)
      by (replace (uint (sreg117 sw47)) with 15 by (vm_compute; reflexivity); exact Hm15).
    iApply (wp_clui_gpr spc47 sw47 (sreg117 sw47) (sclui_imm sw47) m va5 misa0 (zeros' 64) b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha547 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode_s47 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W47").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc47 2) with spc48 by (vm_compute; reflexivity).
    set (m47 := <[gpr_of_Z (uint (sreg117 sw47)) := regval_into_reg va5_47]> m).
    (* idx 48: C_ADDI a5 (4-byte window from skinstr 48 ++ 49; idx 49 is 32-bit, 2 bytes remain) *)
    iAssert (kinstr_bytes (skinstr 48)) as "#K48". { sg 48. }
    iAssert (kinstr_bytes (skinstr 49)) as "#K49". { sg 49. }
    assert (Hk_a : ki_addr (skinstr 48) = kentry + 0x8c) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 48) = 0x17fd) by (vm_compute; reflexivity); iDestruct (kinstr_rvc4 (skinstr 48) (kentry + 0x8c) (0x17fd) Hk_a Hk_e with "K48") as (wr_s48) "[%Hsub_s48 #W48]"; clear Hk_a Hk_e.
    assert (Ha548 : m47 !! gpr_of_Z (uint (sreg117 sw48)) = Some va5_47).
    { unfold m47, va5_47. replace (uint (sreg117 sw48)) with 15 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw47)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_caddi_gpr_4 spc48 wr_s48 (sreg117 sw48) (scli_imm sw48) m47 va5_47 misa0 (zeros' 64) b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha548 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s48; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s48 wr_s48 Hsub_s48) eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W48").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc48 2) with spc49 by (vm_compute; reflexivity).
    set (m48 := <[gpr_of_Z (uint (sreg117 sw48)) := regval_into_reg va5_48]> m47).
    assert (Hk_a : ki_addr (skinstr 49) = (kentry + 0x8e)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 49) = 0x30279073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 49) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 49) (kentry + 0x8e) 0x30279073 Hk_a Hk_e Hk_w with "K49") as "#W49"; clear Hk_a Hk_e Hk_w.
    (* idx 49: csrw medeleg,a5 *)
    assert (Ha549 : m48 !! gpr_of_Z (uint (scsr_rs1z sw49)) = Some va5_48).
    { unfold m48, va5_48. replace (uint (scsr_rs1z sw49)) with 15 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw48)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_medeleg_gpr_2 spc49 sw49 (scsr_rs1z sw49) m48 va5_48 medeleg0 misa0 (zeros' 64) b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha549 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode_s49 eq_refl HmIE Hlp
              with "Hpc Hfile Hmede Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W49").
    iNext.
    iIntros "Hpc Hfile Hmede Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc49 4) with spc50 by (vm_compute; reflexivity).
    iAssert (kinstr_bytes (skinstr 50)) as "#K50". { sg 50. }
    assert (Hk_a : ki_addr (skinstr 50) = (kentry + 0x92)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 50) = 0x30379073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 50) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 50) (kentry + 0x92) 0x30379073 Hk_a Hk_e Hk_w with "K50") as "#W50"; clear Hk_a Hk_e Hk_w.
    (* idx 50: csrw mideleg,a5  -- writes (R_bitvector_64 mideleg) to nonzero *)
    assert (Ha550 : m48 !! gpr_of_Z (uint (scsr_rs1z sw50)) = Some va5_48).
    { unfold m48, va5_48. replace (uint (scsr_rs1z sw50)) with 15 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw48)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_mideleg_gpr_2 spc50 sw50 (scsr_rs1z sw50) m48 va5_48 misa0 (zeros' 64) b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha550 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode_s50 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W50").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc50 4) with spc51 by (vm_compute; reflexivity).
    (* kernel_text is duplicable: no reassembly, no window-return. *)
    with_strategy transparent [mbump] (iApply ("Hcont" with "Hpc [Hfile] Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmede Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif")).
    { unfold mout, m48, m47. iExact "Hfile". }
  Qed.

  (* ===================================================================== *)
  (* CHUNK wp_st_c5 : idx 51-58.  csrr a5,sie ; ori a5 ; csrw sie ;         *)
  (* c.li a5 ; c.srli a5 ; csrw pmpaddr0 ; c.li a5 ; csrw pmpcfg0.          *)
  (* mideleg is now nonzero (mdv0 abstract); threads mie, pmpaddr_n.        *)
  (* ===================================================================== *)
  Lemma wp_st_c5
      (va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 mdv0 mie0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump := mbump b1 in
    let va5_51 := lower_mie mie0 mdv0 in
    let va5_52 := or_vec va5_51 (sign_extend' 64 (subrange_vec_dec sw52 31 20)) in
    let va5_54 := cli_wval (scli_imm sw54) in
    let va5_55 := csrli_wval (scsrli_sh sw55) va5_54 in
    let va5_57 := cli_wval (scli_imm sw57) in
    let mout := <[gpr_of_Z (uint (sreg117 sw57)) := regval_into_reg va5_57]>
                (<[gpr_of_Z (uint r_a5) := regval_into_reg va5_55]>
                (<[gpr_of_Z (uint (sreg117 sw54)) := regval_into_reg va5_54]>
                (<[gpr_of_Z (uint (sit_rd sw52)) := regval_into_reg va5_52]>
                (<[gpr_of_Z (uint (scsr_rd sw51)) := regval_into_reg va5_51]> m)))) in
    m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    PC ↦ᵣ spc51 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    mie ↦ᵣ mie0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    ti_ctx misa0 mstatus0 mseccfg0 mdv0 mc mcfg pmpcfg0 pmar0 elp0 -∗
    kernel_text -∗
    ▷ ( PC ↦ᵣ spc59 -∗ gpr_file mout -∗ nextPC ↦ᵣ spc59 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ bump (bump (bump (bump (bump (bump (bump (bump mst0))))))) -∗
        mie ↦ᵣ sie_new_mie mie0 mdv0 va5_52 -∗ pmpaddr_n ↦ᵣ pmp0_newaddr pmpcfg0 pmpaddr00 va5_55 -∗
        ti_ctx misa0 mstatus0 mseccfg0 mdv0 mc mcfg (pmpcfg0_finalvec va5_57 pmpcfg0) pmar0 elp0 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 bump va5_51 va5_52 va5_54 va5_55 va5_57 mout.
    intros Hm15 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaS.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmie Hpmpa Hctx #H".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iIntros "Hcont".
    iAssert (kinstr_bytes (skinstr 51)) as "#K51". { sg 51. }
    assert (Hk_a : ki_addr (skinstr 51) = (kentry + 0x96)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 51) = 0x104027f3) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 51) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 51) (kentry + 0x96) 0x104027f3 Hk_a Hk_e Hk_w with "K51") as "#W51"; clear Hk_a Hk_e Hk_w.
    (* idx 51: csrr a5,sie *)
    assert (Ha551 : m !! gpr_of_Z (uint (scsr_rd sw51)) = Some va5)
      by (replace (uint (scsr_rd sw51)) with 15 by (vm_compute; reflexivity); exact Hm15).
    iApply (wp_csrr_sie_gpr_2 spc51 sw51 (scsr_rs1z sw51) (scsr_rd sw51) m va5 b1
              _ _ mstatus0 misa0 mie0 mdv0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vmc) ltac:(vm_compute; discriminate) Ha551 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode_s51 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hmie Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W51").
    iNext.
    iIntros "Hpc Hfile Hmisa Hmie Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc51 4) with spc52 by (vm_compute; reflexivity).
    set (m51 := <[gpr_of_Z (uint (scsr_rd sw51)) := regval_into_reg va5_51]> m).
    iAssert (kinstr_bytes (skinstr 52)) as "#K52". { sg 52. }
    assert (Hk_a : ki_addr (skinstr 52) = (kentry + 0x9a)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 52) = 0x2207e793) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 52) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 52) (kentry + 0x9a) 0x2207e793 Hk_a Hk_e Hk_w with "K52") as "#W52"; clear Hk_a Hk_e Hk_w.
    (* idx 52: ori a5,a5,imm *)
    assert (Ha552a : m51 !! gpr_of_Z (uint (sit_rs1 sw52)) = Some va5_51).
    { unfold m51, va5_51. replace (uint (sit_rs1 sw52)) with 15 by (vm_compute; reflexivity).
      replace (uint (scsr_rd sw51)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Ha552b : m51 !! gpr_of_Z (uint (sit_rd sw52)) = Some va5_51).
    { unfold m51, va5_51. replace (uint (sit_rd sw52)) with 15 by (vm_compute; reflexivity).
      replace (uint (scsr_rd sw51)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_ori_gpr_2 spc52 sw52 (sit_rs1 sw52) (sit_rd sw52) (subrange_vec_dec sw52 31 20) m51
              va5_51 va5_51 misa0 mdv0 b1 _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha552a Ha552b Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC HmisaS decode_s52 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W52").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc52 4) with spc53 by (vm_compute; reflexivity).
    set (m52 := <[gpr_of_Z (uint (sit_rd sw52)) := regval_into_reg va5_52]> m51).
    iAssert (kinstr_bytes (skinstr 53)) as "#K53". { sg 53. }
    assert (Hk_a : ki_addr (skinstr 53) = (kentry + 0x9e)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 53) = 0x10479073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 53) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 53) (kentry + 0x9e) 0x10479073 Hk_a Hk_e Hk_w with "K53") as "#W53"; clear Hk_a Hk_e Hk_w.
    (* idx 53: csrw sie,a5 *)
    assert (Ha553 : m52 !! gpr_of_Z (uint (scsr_rs1z sw53)) = Some va5_52).
    { unfold m52, va5_52. replace (uint (scsr_rs1z sw53)) with 15 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw52)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_sie_gpr_2 spc53 sw53 (scsr_rs1z sw53) m52 va5_52 misa0 mie0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha553 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode_s53 eq_refl HmIE Hlp
              with "Hpc Hfile Hmie Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W53").
    iNext.
    iIntros "Hpc Hfile Hmie Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc53 4) with spc54 by (vm_compute; reflexivity).
    iAssert (kinstr_bytes (skinstr 54)) as "#K54". { sg 54. }
    assert (Hk_a : ki_addr (skinstr 54) = (kentry + 0xa2)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 54) = 0x57fd) by (vm_compute; reflexivity); assert (Hk_w : (2 <= ki_width (skinstr 54) / 8)%nat) by (vm_compute; lia); iDestruct (kinstr_window16 (skinstr 54) (kentry + 0xa2) 0x57fd Hk_a Hk_e Hk_w with "K54") as "#W54"; clear Hk_a Hk_e Hk_w.
    (* idx 54: c.li a5 *)
    assert (Ha554 : m52 !! gpr_of_Z (uint (sreg117 sw54)) = Some va5_52).
    { unfold m52, va5_52. replace (uint (sreg117 sw54)) with 15 by (vm_compute; reflexivity).
      replace (uint (sit_rd sw52)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_cli_gpr spc54 sw54 (sreg117 sw54) (scli_imm sw54) m52 va5_52 misa0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha554 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode_s54 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W54").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc54 2) with spc55 by (vm_compute; reflexivity).
    set (m54 := <[gpr_of_Z (uint (sreg117 sw54)) := regval_into_reg va5_54]> m52).
    (* idx 55: c.srli a5 (4-byte window from skinstr 55 ++ 56; idx 56 is 32-bit, 2 bytes remain) *)
    iAssert (kinstr_bytes (skinstr 55)) as "#K55". { sg 55. }
    iAssert (kinstr_bytes (skinstr 56)) as "#K56". { sg 56. }
    assert (Hk_a : ki_addr (skinstr 55) = kentry + 0xa4) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 55) = 0x83a9) by (vm_compute; reflexivity); iDestruct (kinstr_rvc4 (skinstr 55) (kentry + 0xa4) (0x83a9) Hk_a Hk_e with "K55") as (wr_s55) "[%Hsub_s55 #W55]"; clear Hk_a Hk_e.
    assert (Ha555 : m54 !! gpr_of_Z (uint r_a5) = Some va5_54).
    { unfold m54, va5_54. replace (uint r_a5) with 15 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw54)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrli_gpr_4 spc55 wr_s55 (scsrli_sh sw55) scsrli_crsd r_a5 m54 va5_54 misa0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vm_compute; discriminate) Ha555 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(rewrite Hsub_s55; vm_compute; reflexivity)
              HmisaC HmisaS (decode4_s55 wr_s55 Hsub_s55) eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W55").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc55 2) with spc56 by (vm_compute; reflexivity).
    set (m55 := <[gpr_of_Z (uint r_a5) := regval_into_reg va5_55]> m54).
    assert (Hk_a : ki_addr (skinstr 56) = (kentry + 0xa6)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 56) = 0x3b079073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 56) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 56) (kentry + 0xa6) 0x3b079073 Hk_a Hk_e Hk_w with "K56") as "#W56"; clear Hk_a Hk_e Hk_w.
    (* idx 56: csrw pmpaddr0,a5 *)
    assert (Ha556 : m55 !! gpr_of_Z (uint (scsr_rs1z sw56)) = Some va5_55).
    { unfold m55, va5_55. replace (uint (scsr_rs1z sw56)) with 15 by (vm_compute; reflexivity).
      replace (uint r_a5) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_pmpaddr0_gpr_2 spc56 sw56 (scsr_rs1z sw56) m55 va5_55 misa0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmpaddr00 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha556 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode_s56 eq_refl HmIE Hlp
              with "Hpc Hfile Hpmpa Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W56").
    iNext.
    iIntros "Hpc Hfile Hpmpa Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc56 4) with spc57 by (vm_compute; reflexivity).
    iAssert (kinstr_bytes (skinstr 57)) as "#K57". { sg 57. }
    assert (Hk_a : ki_addr (skinstr 57) = (kentry + 0xaa)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 57) = 0x47bd) by (vm_compute; reflexivity); assert (Hk_w : (2 <= ki_width (skinstr 57) / 8)%nat) by (vm_compute; lia); iDestruct (kinstr_window16 (skinstr 57) (kentry + 0xaa) 0x47bd Hk_a Hk_e Hk_w with "K57") as "#W57"; clear Hk_a Hk_e Hk_w.
    (* idx 57: c.li a5 *)
    assert (Ha557 : m55 !! gpr_of_Z (uint (sreg117 sw57)) = Some va5_55).
    { unfold m55, va5_55. replace (uint (sreg117 sw57)) with 15 by (vm_compute; reflexivity).
      replace (uint r_a5) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_cli_gpr spc57 sw57 (sreg117 sw57) (scli_imm sw57) m55 va5_55 misa0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha557 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode_s57 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W57").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc57 2) with spc58 by (vm_compute; reflexivity).
    set (m57 := <[gpr_of_Z (uint (sreg117 sw57)) := regval_into_reg va5_57]> m55).
    iAssert (kinstr_bytes (skinstr 58)) as "#K58". { sg 58. }
    assert (Hk_a : ki_addr (skinstr 58) = (kentry + 0xac)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 58) = 0x3a079073) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 58) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 58) (kentry + 0xac) 0x3a079073 Hk_a Hk_e Hk_w with "K58") as "#W58"; clear Hk_a Hk_e Hk_w.
    (* idx 58: csrw pmpcfg0,a5 *)
    assert (Ha558 : m57 !! gpr_of_Z (uint (scsr_rs1z sw58)) = Some va5_57).
    { unfold m57, va5_57. replace (uint (scsr_rs1z sw58)) with 15 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw57)) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_pmpcfg0_gpr spc58 sw58 (scsr_rs1z sw58) m57 va5_57 misa0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha558 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode_s58 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W58").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int spc58 4) with spc59 by (vm_compute; reflexivity).
    (* kernel_text is duplicable: no reassembly, no window-return. *)
    with_strategy transparent [mbump] (iApply ("Hcont" with "Hpc [Hfile] Hnpc Hmi Hmst Hmie Hpmpa
              [Hmisa Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif]")).
    { unfold mout, m57, m55, m54, m52, m51. iExact "Hfile". }
    { iFrame. }
  Qed.

  (* ===================================================================== *)
  (* CHUNK wp_st_c6 (THE NESTED CALL): idx 59 jal timerinit ; [wp_timerinit];*)
  (* idx 60 csrr a5,mhartid.   The jal sets ra:=0xb4, PC:=0x1c; wp_timerinit *)
  (* runs (using kernel_text + its own fresh stack frame below sp), returns  *)
  (* PC:=ra=0xb4 and kernel_text; then csrr mhartid at 0xb4.                 *)
  (* ===================================================================== *)
  Lemma wp_st_c6
      (sp0 vra_in vs0 va4 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 menvcfg0 mcounteren0c mtime0 stimecmp0 mdv0 mhartid0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) (vold_ra vold_s0 : bv 64)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    (* timerinit's own stack frame: sp1 = sp0 - 16, slots at sp1+8 (ra), sp1+0 (s0). *)
    let sp1   := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm9)) in
    let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
    let pa_ra  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let a8_ra  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
    let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
    let pa_s0  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let a8_s0  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
    (* ra after the jal = pc+4 = 0xb4 ; this is the value timerinit saves/loads. *)
    let vra := regval_into_reg (add_vec_int spc59 4) in
    let vra_ld := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vra)) in
    let tgt := update_vec_dec (add_vec vra_ld (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0") in
    (* gpr_file entering timerinit (after the jal wrote ra): *)
    let mti := <[gpr_of_Z 1 := vra]> m in
    m !! gpr_of_Z 1 = Some vra_in ->
    m !! gpr_of_Z 2 = Some sp0 ->
    m !! gpr_of_Z 8 = Some vs0 ->
    m !! gpr_of_Z 14 = Some va4 ->
    m !! gpr_of_Z 15 = Some va5 ->
    is_Some (m !! gpr_of_Z 4) ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true -> is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true -> is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    PC ↦ᵣ spc59 -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    mhartid ↦ᵣ mhartid0 -∗
    mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vold_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vold_s0 j) -∗
    kernel_text -∗
    (* after the jal + nested timerinit() call returns, PC = ra = spc60 = 0xb4.
       Expose the full post-call machine state (timerinit restored ra/s0/sp,
       clobbered a4/a5; its CSR writes menvcfg/mcounteren/stimecmp are consumed).
       The gpr_file is existential (x15/a5 present) since a5 is clobbered. *)
    ▷ ( PC ↦ᵣ spc60
        -∗ (∃ mfin, gpr_file mfin ∗ ⌜ is_Some (mfin !! gpr_of_Z 15) ∧ is_Some (mfin !! gpr_of_Z 4) ∧ is_Some (mfin !! gpr_of_Z 2) ⌝)
        -∗ misa ↦ᵣ misa0 -∗ mhartid ↦ᵣ mhartid0 -∗ nextPC ↦ᵣ spc60
        -∗ (R_bool minstret_increment) ↦ᵣ b1
        -∗ (∃ mstf : mword 64, minstret ↦ᵣ mstf)
        -∗ cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt
        -∗ (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0
        -∗ elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0
        -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg
        -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None
        -∗ kernel_text -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 sp1 imm_ra pa_ra a8_ra imm_s0 pa_s0 a8_s0 vra vra_ld tgt mti_def.
    intros Hm1 Hm2 Hm8 Hm14 Hm15 Hm4 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Hmlpe HmisaC HmisaS HmisaU Ha8ra Hpara Ha8s0 Hpas0.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hmenv Hmcen Hmtime Hstc Hmhartid
             Hmcinh Hmcfg Hpmpc Hpma Hhtif Hstkra Hstks0 #H Hcont".
    (* ---- idx 59: jal ra, timerinit (kernel_text duplicable: split off K59 here) ---- *)
    iAssert (kinstr_bytes (skinstr 59)) as "#K59". { sg 59. }
    assert (Hk_a : ki_addr (skinstr 59) = (kentry + 0xb0)) by (vm_compute; reflexivity); assert (Hk_e : ki_enc (skinstr 59) = 0xf6dff0ef) by (vm_compute; reflexivity); assert (Hk_w : ki_width (skinstr 59) = 32%nat) by (vm_compute; reflexivity); iDestruct (kinstr_window32 (skinstr 59) (kentry + 0xb0) 0xf6dff0ef Hk_a Hk_e Hk_w with "K59") as "#W59"; clear Hk_a Hk_e Hk_w.
    assert (Hra59 : m !! gpr_of_Z (uint sjal_rd) = Some vra_in)
      by (replace (uint sjal_rd) with 1 by (vm_compute; reflexivity); exact Hm1).
    iApply (wp_jal_gpr spc59 sw59 sjal_imm sjal_rd m vra_in misa0 mdv0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Hra59 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode_s59 ltac:(vmc) ltac:(vm_compute; reflexivity) eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W59").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    (* PC is now the jal target = tpc9 = 0x8000001c; nextPC too.  ra := 0xb4. *)
    replace (add_vec spc59 (sign_extend' 64 sjal_imm)) with tpc9 by (apply bv_eq; vm_compute; reflexivity).
    (* kernel_text is duplicable -> #Htext is still in context. *)
    (* Now the gpr_file is mti_def = <[1:=vra]> m (the jal wrote ra). *)
    replace (gpr_of_Z (uint sjal_rd)) with (gpr_of_Z 1) by (do 2 f_equal; vm_compute; reflexivity).
    replace (regval_into_reg (add_vec_int spc59 4)) with vra by reflexivity.
    fold mti_def.
    (* ---- the nested timerinit() call (idx 9-29) ---- *)
    (* lookups for the 5 registers timerinit reads, over mti_def = <[1:=vra]> m *)
    assert (Lti1 : mti_def !! gpr_of_Z 1 = Some vra)
      by (unfold mti_def; rewrite lookup_insert; reflexivity).
    assert (Lti2 : mti_def !! gpr_of_Z 2 = Some sp0)
      by (unfold mti_def; rewrite lookup_insert_ne; [exact Hm2 | vm_compute; discriminate]).
    assert (Lti8 : mti_def !! gpr_of_Z 8 = Some vs0)
      by (unfold mti_def; rewrite lookup_insert_ne; [exact Hm8 | vm_compute; discriminate]).
    assert (Lti14 : mti_def !! gpr_of_Z 14 = Some va4)
      by (unfold mti_def; rewrite lookup_insert_ne; [exact Hm14 | vm_compute; discriminate]).
    assert (Lti15 : mti_def !! gpr_of_Z 15 = Some va5)
      by (unfold mti_def; rewrite lookup_insert_ne; [exact Hm15 | vm_compute; discriminate]).
    assert (Lti4 : is_Some (mti_def !! gpr_of_Z 4))
      by (unfold mti_def; rewrite lookup_insert_ne; [exact Hm4 | vm_compute; discriminate]).
    iApply (wp_timerinit sp0 vra vs0 va4 va5 mti_def
              _ misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 mdv0
              mcounteren0 mc mcfg pmpcfg0 pmar0 b1 elp0 vold_ra vold_s0 E Φ
              Lti1 Lti2 Lti8 Lti14 Lti15 Lti4 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Hmlpe HmisaC HmisaS HmisaU
              Ha8ra Hpara Ha8s0 Hpas0
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hmenv Hmcen Hmtime Hstc
                    Hmcinh Hmcfg Hpmpc Hpma Hhtif Hstkra Hstks0 H").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    (* PC is now timerinit's return target tgt = the loaded ra = 0xb4 = spc60. *)
    replace (update_vec_dec
               (add_vec
                  (regval_into_reg (extend_value false
                     (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8)
                        (regval_into_reg (add_vec_int spc59 4)))))
                  (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0"))
      with spc60 by (apply bv_eq; vm_compute; reflexivity).
    with_strategy transparent [mbump] (iApply ("Hcont" with "Hpc Hfile Hmisa Hmhartid Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec
              Hmcinh Hmcfg Hpmpc Hpma Hhtif H")).
  Qed.

End WpStart2.
