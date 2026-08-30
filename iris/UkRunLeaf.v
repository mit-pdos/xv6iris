(* ===================================================================== *)
(* UkRunLeaf.v -- the REGISTER-ONLY and CONTROL-FLOW leaves, on [urun].    *)
(*                                                                        *)
(* One wrapper per instruction over the corresponding [UkLeaf] leaf.  The  *)
(* shape is uniform and is the whole point of [UkRun]:                     *)
(*                                                                        *)
(*   uinstr_is  -*  urun ... h m pc  -*                                    *)
(*   (forall h', urun ... h' m' pc' -* WP Loop)  -*  WP Loop               *)
(*                                                                        *)
(* No ambient, no [ukc], no [uvb], no postcondition.  The instruction's    *)
(* own side conditions (rd <> x0, the value it writes) survive as Coq      *)
(* premises; everything about the MACHINE -- which hart, which table,      *)
(* which permission map, what the image is -- is inside [urun].            *)
(*                                                                        *)
(* The 6-bit immediates are NORMALISED: a leaf states [sign_extend' 64     *)
(* imm], not the decoder's [sign_extend' 64 (sign_extend' 12 imm)].        *)
(*                                                                        *)
(* See claude-notes/design/uk-engine.md.  Memory leaves are in UkRunMem.v. *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile InstrBytes.
Require Import UserPtTree UserExec ProcPtOwn.
Require Import UmodeMem UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UptTree.
Require Import WpMmodeLeafBase.
Require Import UmodeFetch.
Require Import WpUmodeStore.
Require Import UkStep UkLeaf UkStore.
Require Import UserHeap.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
Require Import WpUmodeBranch.
Require Import UkBranch.
Require Import UkRun.

From Stdlib Require Import ZArith Bool Lia.
From iris.base_logic.lib Require Import invariants.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import InstrBytes WpGpr RegFile.
Require Import ExecCommon WpMmodeLeafBase WpMmodeShiftiop.
Require Import UserBits.
Require Import HartMemRun UserFrame UserExecFacts.
Require UserTotalU.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap.
Require Import WpUmodeStep.
Require Import ProcPtOwn UserPerm UsysMemOk UexecWp UexecSlot UexecRet UkStep.
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)

Section UkRunLeaf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* ------------------------------------------------------------------- *)
  (* c.li rd, imm -- rd := sext(imm).  Hand-cut rather than generated,     *)
  (* because the decoder ALSO adds x0 here, and [uimm6_norm] kills the     *)
  (* whole chain at once.                                                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_cli (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) :
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LI (imm, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h'
         (<[Regidx rd := regval_into_reg (sign_extend' 64 imm : mword 64)]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hrd. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cli C pt Rut pm sz Hlo Hpm M m pc imm rd
              (sign_extend' 64 imm) Hui Hrd (eq_sym (uimm6_norm imm))
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_caddi (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rd) (sign_extend' 64 imm) ->
    uinstr_is γt pc true (C_ADDI (imm, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddi C pt Rut pm sz Hlo Hpm M m pc imm rd wval
              Hui H1 ltac:(rewrite (sext6_12_64 imm); exact H2)
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_caddi4spn (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (cr : mword 3) (nzimm : mword 8) (rd : mword 5) (wval : mword 64) :
    creg2reg_idx (Cregidx cr) = Regidx rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)) ->
    uinstr_is γt pc true (C_ADDI4SPN (Cregidx cr, nzimm)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddi4spn C pt Rut pm sz Hlo Hpm M m pc cr nzimm rd wval
              Hui H1 H2 H3
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_jal (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 21) (rd : mword 5) (tgt wval : mword 64) :
    uint rd <> 0 ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    wval = add_vec_int pc 4 ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uinstr_is γt pc false (JAL (imm, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jal C pt Rut pm sz Hlo Hpm M m pc imm rd tgt wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_cjr (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 : mword 5) (tgt : mword 64) :
    uint rs1 <> 0 ->
    tgt = ret_pc (m !!! Regidx rs1) ->
    uinstr_is γt pc true (C_JR (Regidx rs1)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' m
         tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cjr C pt Rut pm sz Hlo Hpm M m pc rs1 tgt
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_caddi16sp (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (wval : mword 64) :
    wval = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm)) ->
    uinstr_is γt pc true (C_ADDI16SP imm) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx csp_rs1 := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddi16sp C pt Rut pm sz Hlo Hpm M m pc imm wval
              Hui H1
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_cmv (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rd rs2 : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = add_vec zero_reg (m !!! Regidx rs2) ->
    uinstr_is γt pc true (C_MV (Regidx rd, Regidx rs2)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cmv C pt Rut pm sz Hlo Hpm M m pc rd rs2 wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_caddiw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = sign_extend' 64 (subrange_vec_dec (add_vec (m !!! Regidx rd) (sign_extend' 64 imm)) 31 0) ->
    uinstr_is γt pc true (C_ADDIW (imm, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddiw C pt Rut pm sz Hlo Hpm M m pc imm rd wval
              Hui H1 ltac:(rewrite (sext6_12_64 imm); exact H2)
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_cj (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 11) (tgt : mword 64) :
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0")))) ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uinstr_is γt pc true (C_J imm) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' m
         tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cj C pt Rut pm sz Hlo Hpm M m pc imm tgt
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_addi (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addi C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_add (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is γt pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_add C pt Rut pm sz Hlo Hpm M m pc rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_slli (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rs1 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = shift_bits_left (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is γt pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_slli C pt Rut pm sz Hlo Hpm M m pc shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_srli (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rs1 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is γt pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_srli C pt Rut pm sz Hlo Hpm M m pc shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_subw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = sign_extend' 64 (sub_vec (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is γt pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_subw C pt Rut pm sz Hlo Hpm M m pc rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_auipc (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 20) (rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = add_vec pc (auipc_off imm) ->
    uinstr_is γt pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_auipc C pt Rut pm sz Hlo Hpm M m pc imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_sub (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is γt pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sub C pt Rut pm sz Hlo Hpm M m pc rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_and (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is γt pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_and C pt Rut pm sz Hlo Hpm M m pc rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_sltu (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) ->
    uinstr_is γt pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sltu C pt Rut pm sz Hlo Hpm M m pc rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_addw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = sign_extend' 64 (add_vec (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is γt pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addw C pt Rut pm sz Hlo Hpm M m pc rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_sltiu (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (sign_extend' 64 imm))) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sltiu C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_andi (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_andi C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_xori (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = xor_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, XORI)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_xori C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_addiw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = sign_extend' 64 (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 31 0) ->
    uinstr_is γt pc false (ADDIW (imm, Regidx rs1, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addiw C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_slliw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 5) (rs1 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = sign_extend' 64 (shift_bits_left (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) shamt) ->
    uinstr_is γt pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_slliw C pt Rut pm sz Hlo Hpm M m pc shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_lui (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 20) (rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = luival imm ->
    uinstr_is γt pc false (UTYPE (imm, Regidx rd, LUI)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_lui C pt Rut pm sz Hlo Hpm M m pc imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_divu (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = to_bits_truncate 64 (if Z.eqb (uint (m !!! Regidx rs2)) 0 then -1 else Z.quot (uint (m !!! Regidx rs1)) (uint (m !!! Regidx rs2))) ->
    uinstr_is γt pc false (DIV (Regidx rs2, Regidx rs1, Regidx rd, true)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_divu C pt Rut pm sz Hlo Hpm M m pc rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_remu (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = to_bits_truncate 64 (if Z.eqb (uint (m !!! Regidx rs2)) 0 then uint (m !!! Regidx rs1) else Z.rem (uint (m !!! Regidx rs1)) (uint (m !!! Regidx rs2))) ->
    uinstr_is γt pc false (REM (Regidx rs2, Regidx rs1, Regidx rd, true)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_remu C pt Rut pm sz Hlo Hpm M m pc rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_jalr (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wr : option (mword 5 * mword 64)) (tgt : mword 64) :
    uint rs1 <> 0 ->
    (uint rd = 0 /\ wr = None) \/ (uint rd <> 0 /\ wr = Some (rd, add_vec_int pc 4)) ->
    tgt = ret_pc (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ->
    uinstr_is γt pc false (JALR (imm, Regidx rs1, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (uv_upd m wr)
         tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jalr C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd wr tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_jr (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (tgt : mword 64) :
    uint rs1 <> 0 ->
    uint rd = 0 ->
    tgt = ret_pc (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ->
    uinstr_is γt pc false (JALR (imm, Regidx rs1, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' m
         tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jr C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_cadd (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rd rs2 : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rd) (m !!! Regidx rs2) ->
    uinstr_is γt pc true (C_ADD (Regidx rd, Regidx rs2)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cadd C pt Rut pm sz Hlo Hpm M m pc rd rs2 wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_cand (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (crd crs2 : mword 3) (rd rs2 : mword 5) (wval : mword 64) :
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    creg2reg_idx (Cregidx crs2) = Regidx rs2 ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rd) (m !!! Regidx rs2) ->
    uinstr_is γt pc true (C_AND (Cregidx crd, Cregidx crs2)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cand C pt Rut pm sz Hlo Hpm M m pc crd crs2 rd rs2 wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_caddw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (crd crs2 : mword 3) (rd rs2 : mword 5) (wval : mword 64) :
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    creg2reg_idx (Cregidx crs2) = Regidx rs2 ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (add_vec (subrange_vec_dec (m !!! Regidx rd) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is γt pc true (C_ADDW (Cregidx crd, Cregidx crs2)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddw C pt Rut pm sz Hlo Hpm M m pc crd crs2 rd rs2 wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_clui (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = luival (sign_extend' 20 imm) ->
    uinstr_is γt pc true (C_LUI (imm, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_clui C pt Rut pm sz Hlo Hpm M m pc imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_cslli (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is γt pc true (C_SLLI (shamt, Regidx rd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cslli C pt Rut pm sz Hlo Hpm M m pc shamt rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_csrli (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (crd : mword 3) (rd : mword 5) (wval : mword 64) :
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    wval = shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is γt pc true (C_SRLI (shamt, Cregidx crd)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_csrli C pt Rut pm sz Hlo Hpm M m pc shamt crd rd wval
              Hui H1 H2 H3
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_li (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rd : mword 5) (wval : mword 64) :
    uint rd <> 0 ->
    wval = add_vec zero_reg (sign_extend' 64 imm) ->
    uinstr_is γt pc false
      (ITYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rd, ADDI)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_li C pt Rut pm sz Hlo Hpm M m pc imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.


  (* ===================================================================== *)
  (* THE BRANCHES.  The one place [pc'] is not a constant offset: the       *)
  (* continuation is at [if taken then tgt else pc+k], and the program      *)
  (* discharges [taken] by computing it.                                    *)
  (* ===================================================================== *)

  Lemma wp_uk_btype (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop) (taken : bool) (tgt : mword 64) :
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' m
         (if taken then tgt else add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_btype C pt Rut pm sz Hlo Hpm M m pc imm rs2 rs1 op taken tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_cbeqz (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 8) (cr : mword 3) (rs : mword 5) (taken : bool) (tgt : mword 64) :
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = eq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc true (C_BEQZ (imm, Cregidx cr)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' m
         (if taken then tgt else add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_cbeqz C pt Rut pm sz Hlo Hpm M m pc imm cr rs taken tgt
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.

  Lemma wp_uk_cbnez (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 8) (cr : mword 3) (rs : mword 5) (taken : bool) (tgt : mword 64) :
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = neq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc true (C_BNEZ (imm, Cregidx cr)) -∗
    urun γt γd γs h m pc -∗
    (∀ h' : CpuId,
       urun γt γd γs h' m
         (if taken then tgt else add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_cbnez C pt Rut pm sz Hlo Hpm M m pc imm cr rs taken tgt
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hcont]").
    iApply (urun_close with "Hheap Hcont").
  Qed.


End UkRunLeaf.
