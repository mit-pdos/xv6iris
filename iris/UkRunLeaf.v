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
(* THE FREE STACK.  [urun] carries [avail], the words of free stack below  *)
(* sp, and every leaf here threads it UNCHANGED -- which is only sound if  *)
(* the instruction does not move sp, since that is the index the ownership *)
(* is keyed by.  So every leaf that writes a general register carries      *)
(* [unot_sp rd].  The exceptions are the two sp-adjust rules at the end of *)
(* the file, which are the TRANSFER points: [_dn] hands a frame out of the *)
(* free stack, [_up] takes one back.                                       *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import UmodeArith.
Require Import WpMmodeLeafBase.
Require Import UkLeaf.
Require Import UserHeap.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
Require Import WpUmodeBranch.
Require Import UkBranch.
Require Import UmodeAbi.
Require Import UkRun.

From Stdlib Require Import ZArith Bool Lia.
From iris.base_logic.lib Require Import invariants.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeStep.
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Section UkRunLeaf.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* ------------------------------------------------------------------- *)
  (* c.li rd, imm -- rd := sext(imm).  Hand-cut rather than generated,     *)
  (* because the decoder ALSO adds x0 here, and [uimm6_norm] kills the     *)
  (* whole chain at once.                                                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_cli (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LI (imm, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx rd := regval_into_reg (sign_extend' 64 imm : mword 64)]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Hrd. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cli C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rd
              (sign_extend' 64 imm) Hui Hrd (eq_sym (uimm6_norm imm))
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_caddi (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rd) (sign_extend' 64 imm) ->
    uinstr_is γt pc true (C_ADDI (imm, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddi C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rd wval
              Hui H1 ltac:(rewrite (sext6_12_64 imm); exact H2)
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_caddi4spn (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (cr : mword 3) (nzimm : mword 8) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx cr) = Regidx rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)) ->
    uinstr_is γt pc true (C_ADDI4SPN (Cregidx cr, nzimm)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddi4spn C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv cr nzimm rd wval
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_jal (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 21) (rd : mword 5) (tgt wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    wval = add_vec_int pc 4 ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uinstr_is γt pc false (JAL (imm, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         tgt avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jal C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rd tgt wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_cjr (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 : mword 5) (tgt : mword 64) (avail : nat) :
    uint rs1 <> 0 ->
    tgt = ret_pc (m !!! Regidx rs1) ->
    uinstr_is γt pc true (C_JR (Regidx rs1)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' m
         tgt avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cjr C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 tgt
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_cmv (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec zero_reg (m !!! Regidx rs2) ->
    uinstr_is γt pc true (C_MV (Regidx rd, Regidx rs2)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cmv C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rd rs2 wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_caddiw (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (subrange_vec_dec (add_vec (m !!! Regidx rd) (sign_extend' 64 imm)) 31 0) ->
    uinstr_is γt pc true (C_ADDIW (imm, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddiw C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rd wval
              Hui H1 ltac:(rewrite (sext6_12_64 imm); exact H2)
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_cj (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 11) (tgt : mword 64) (avail : nat) :
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0")))) ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uinstr_is γt pc true (C_J imm) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' m
         tgt avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cj C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm tgt
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_addi (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addi C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_add (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is γt pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_add C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_slli (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = shift_bits_left (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is γt pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_slli C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_srli (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is γt pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_srli C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_subw (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (sub_vec (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is γt pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_subw C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_auipc (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 20) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec pc (auipc_off imm) ->
    uinstr_is γt pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_auipc C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_sub (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is γt pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sub C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_and (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is γt pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_and C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_sltu (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) ->
    uinstr_is γt pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sltu C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_addw (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (add_vec (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is γt pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addw C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_sltiu (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (sign_extend' 64 imm))) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sltiu C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_andi (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_andi C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_xori (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = xor_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is γt pc false (ITYPE (imm, Regidx rs1, Regidx rd, XORI)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_xori C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_addiw (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 31 0) ->
    uinstr_is γt pc false (ADDIW (imm, Regidx rs1, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addiw C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_slliw (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 5) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (shift_bits_left (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) shamt) ->
    uinstr_is γt pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_slliw C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_lui (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 20) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = luival imm ->
    uinstr_is γt pc false (UTYPE (imm, Regidx rd, LUI)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_lui C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_divu (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = to_bits_truncate 64 (if Z.eqb (uint (m !!! Regidx rs2)) 0 then -1 else Z.quot (uint (m !!! Regidx rs1)) (uint (m !!! Regidx rs2))) ->
    uinstr_is γt pc false (DIV (Regidx rs2, Regidx rs1, Regidx rd, true)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_divu C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_remu (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = to_bits_truncate 64 (if Z.eqb (uint (m !!! Regidx rs2)) 0 then uint (m !!! Regidx rs1) else Z.rem (uint (m !!! Regidx rs1)) (uint (m !!! Regidx rs2))) ->
    uinstr_is γt pc false (REM (Regidx rs2, Regidx rs1, Regidx rd, true)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_remu C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_jalr (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wr : option (mword 5 * mword 64)) (tgt : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rs1 <> 0 ->
    (uint rd = 0 /\ wr = None) \/ (uint rd <> 0 /\ wr = Some (rd, add_vec_int pc 4)) ->
    tgt = ret_pc (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ->
    uinstr_is γt pc false (JALR (imm, Regidx rs1, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (uv_upd m wr)
         tgt avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jalr C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs1 rd wr tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (uv_upd_not_sp m rd wr (add_vec_int pc 4) Hns H2). iExact "Hstk".
  Qed.

  Lemma wp_uk_jr (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (tgt : mword 64) (avail : nat) :
    uint rs1 <> 0 ->
    uint rd = 0 ->
    tgt = ret_pc (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ->
    uinstr_is γt pc false (JALR (imm, Regidx rs1, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' m
         tgt avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jr C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs1 rd tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_cadd (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rd) (m !!! Regidx rs2) ->
    uinstr_is γt pc true (C_ADD (Regidx rd, Regidx rs2)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cadd C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv rd rs2 wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_cand (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (crd crs2 : mword 3) (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    creg2reg_idx (Cregidx crs2) = Regidx rs2 ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rd) (m !!! Regidx rs2) ->
    uinstr_is γt pc true (C_AND (Cregidx crd, Cregidx crs2)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cand C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv crd crs2 rd rs2 wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_caddw (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (crd crs2 : mword 3) (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    creg2reg_idx (Cregidx crs2) = Regidx rs2 ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (add_vec (subrange_vec_dec (m !!! Regidx rd) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is γt pc true (C_ADDW (Cregidx crd, Cregidx crs2)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddw C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv crd crs2 rd rs2 wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_clui (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = luival (sign_extend' 20 imm) ->
    uinstr_is γt pc true (C_LUI (imm, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_clui C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_cslli (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is γt pc true (C_SLLI (shamt, Regidx rd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cslli C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv shamt rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_csrli (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (crd : mword 3) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    wval = shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is γt pc true (C_SRLI (shamt, Cregidx crd)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_csrli C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv shamt crd rd wval
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_li (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec zero_reg (sign_extend' 64 imm) ->
    uinstr_is γt pc false
      (ITYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rd, ADDI)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_li C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.


  (* ===================================================================== *)
  (* THE BRANCHES.  The one place [pc'] is not a constant offset: the       *)
  (* continuation is at [if taken then tgt else pc+k], and the program      *)
  (* discharges [taken] by computing it.  No register is written, so no     *)
  (* [unot_sp] and [avail] rides through.                                   *)
  (* ===================================================================== *)

  Lemma wp_uk_btype (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop) (taken : bool) (tgt : mword 64) (avail : nat) :
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' m
         (if taken then tgt else add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_btype C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs2 rs1 op taken tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SAME BRANCH, HANDING THE STEP'S OWN [▷] OUT.  This is the only    *)
  (* rule that can close an UNBOUNDED loop: [iLöb] gives the induction     *)
  (* hypothesis under a later, and the back edge has to strip exactly one. *)
  (* Every loop in sync and echo is bounded and closes by ordinary         *)
  (* induction, which is why the tier has not needed this until now;       *)
  (* init's two -- the restart loop's [beq s1,a0] and the wait loop's      *)
  (* [bge a0,x0] -- are both BTYPE, so this is the one later-providing     *)
  (* leaf it takes.                                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_btype_later (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) (avail : nat) :
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) -∗
    urun γt γd γs γfd h m pc avail -∗
    ▷ (∀ h' : CpuId,
         urun γt γd γs γfd h' m
           (if taken then tgt else add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_btype_later C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm rs2 rs1
              op taken tgt Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcont]").
    iNext.
    iApply (urun_close with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_cbeqz (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 8) (cr : mword 3) (rs : mword 5) (taken : bool) (tgt : mword 64) (avail : nat) :
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = eq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc true (C_BEQZ (imm, Cregidx cr)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' m
         (if taken then tgt else add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_cbeqz C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm cr rs taken tgt
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcont").
  Qed.

  Lemma wp_uk_cbnez (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 8) (cr : mword 3) (rs : mword 5) (taken : bool) (tgt : mword 64) (avail : nat) :
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = neq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc true (C_BNEZ (imm, Cregidx cr)) -∗
    urun γt γd γs γfd h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h' m
         (if taken then tgt else add_vec_int pc 2) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_cbnez C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm cr rs taken tgt
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcont").
  Qed.


  (* ===================================================================== *)
  (* THE TWO SP-ADJUST RULES -- where the free stack changes hands.         *)
  (*                                                                       *)
  (* [c.addi sp, -8k] is a PUSH: sp drops by k words, the program gets      *)
  (* those k words as a frame, and [avail] drops by k.  [c.addi sp, +8k]    *)
  (* is the POP: the frame goes back and [avail] rises again.  They are the *)
  (* only leaves that move sp, which is why every other one carries         *)
  (* [unot_sp].                                                            *)
  (*                                                                       *)
  (* The displacement is given as [k] WORDS and the immediate's value as an *)
  (* equation, rather than decoding it here: a concrete immediate is one    *)
  (* [vm_compute] away from the equation, and a symbolic one has no         *)
  (* business moving sp.                                                    *)
  (* ===================================================================== *)

  (* the positive twin of [UmodeAbi.uv_avi_neg]: sp moving UP by [d] *)
  Lemma uv_avi_pos (a : mword 64) (d : Z) :
    0 <= d -> bv_unsigned a + d < Z64 ->
    bv_unsigned (add_vec_int a d) = bv_unsigned a + d.
  Proof.
    intros Hd Hlt. unfold add_vec_int.
    rewrite add_vec64_unsigned moi64_unsigned.
    unfold bv_wrap.
    assert (E64 : bv_modulus 64 = 18446744073709551616)
      by (vm_compute; reflexivity).
    rewrite E64.
    rewrite Zplus_mod_idemp_r.
    apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ a) as Hr. rewrite E64 in Hr.
    unfold Z64 in Hlt. lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE PUSH.  The caller says WHAT THE IMMEDIATE IS -- a frame of [k]    *)
  (* words down -- and nothing about how the decoder spells it; the new sp *)
  (* is then this leaf's own arithmetic, in the caller's vocabulary        *)
  (* ([add_vec_int]) rather than the model's.  At a concrete immediate the *)
  (* premise is one [vm_compute].                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_caddi_sp_dn (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (k n : nat) :
    (sign_extend' 64 imm : mword 64) = mword_of_int (- (8 * Z.of_nat k)) ->
    uinstr_is γt pc true (C_ADDI (imm, Regidx csp_rs1)) -∗
    urun γt γd γs γfd h m pc (k + n) -∗
    (ustack γd (m !!! Regidx csp_rs1) k -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h'
           (<[Regidx csp_rs1
              := regval_into_reg
                   (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))]> m)
           (add_vec_int pc 2) n -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Himm. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    (* the room below sp is a CONSEQUENCE of owning the free stack *)
    iDestruct (ustack_room with "Hheap Hstk") as %Hroom'.
    assert (Hroom : 8 * Z.of_nat k <= uint (m !!! Regidx csp_rs1)) by lia.
    assert (Hu : uint (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))
                 = uint (m !!! Regidx csp_rs1) - 8 * Z.of_nat k).
    { rewrite !uint_unsigned.
      exact (uv_avi_neg (m !!! Regidx csp_rs1) (8 * Z.of_nat k) ltac:(lia)
               ltac:(rewrite <- uint_unsigned; exact Hroom)). }
    rewrite (ustack_app γd (m !!! Regidx csp_rs1)
               (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k))) k n Hu).
    iDestruct "Hstk" as "(Hframe & Hstk)".
    iApply (UkLeaf.wp_uk_caddi C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm csp_rs1
              (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))
              Hui ltac:(vm_compute; discriminate)
              ltac:(rewrite (sext6_12_64 imm) Himm; reflexivity)
              with "Hb [Hheap Hstk Hufd Hframe Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd [Hframe Hcont]").
    - rewrite (upd_eq m (Regidx csp_rs1) (regval_into_reg _)). iExact "Hstk".
    - iIntros (h') "Hrun". iApply ("Hcont" with "Hframe Hrun").
  Qed.

  (* ...and THE POP, its mirror.  The extra premise is the absence of wrap,
     which the push does not need (sp only ever comes back down to where it
     started, but the leaf cannot see that). *)
  Lemma wp_uk_caddi_sp_up (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (k n : nat) :
    (sign_extend' 64 imm : mword 64) = mword_of_int (8 * Z.of_nat k) ->
    uinstr_is γt pc true (C_ADDI (imm, Regidx csp_rs1)) -∗
    ustack γd (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k)) k -∗
    urun γt γd γs γfd h m pc n -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx csp_rs1
            := regval_into_reg
                 (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))]> m)
         (add_vec_int pc 2) (k + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Himm. iIntros "#Hi Hframe Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    (* ...and so is the absence of wrap, off the frame being returned *)
    iDestruct (ustack_nowrap with "Hheap Hframe") as %Hnw.
    assert (Hu : uint (m !!! Regidx csp_rs1)
                 = uint (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
                   - 8 * Z.of_nat k).
    { rewrite !uint_unsigned.
      rewrite (uv_avi_pos (m !!! Regidx csp_rs1) (8 * Z.of_nat k) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; exact Hnw)). lia. }
    iApply (UkLeaf.wp_uk_caddi C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm csp_rs1
              (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
              Hui ltac:(vm_compute; discriminate)
              ltac:(rewrite (sext6_12_64 imm) Himm; reflexivity)
              with "Hb [Hheap Hstk Hufd Hframe Hcont]").
    iApply (urun_close with "Hheap [Hstk Hframe] Hufd Hcont").
    rewrite (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    rewrite (ustack_app γd (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
               (m !!! Regidx csp_rs1) k n Hu).
    iFrame "Hframe Hstk".
  Qed.

  (* c.addi16sp is the OTHER push: gcc uses it for frames of 32..512 bytes,
     which is echo's main (64).  Same shape, different immediate decoder --
     and the decoder is again the CALLER's one-line obligation, not part of
     the statement. *)
  Lemma wp_uk_caddi16sp_dn (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (k n : nat) :
    (sign_extend' 64 (caddi16sp_imm imm) : mword 64)
      = mword_of_int (- (8 * Z.of_nat k)) ->
    uinstr_is γt pc true (C_ADDI16SP imm) -∗
    urun γt γd γs γfd h m pc (k + n) -∗
    (ustack γd (m !!! Regidx csp_rs1) k -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h'
           (<[Regidx csp_rs1
              := regval_into_reg
                   (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))]> m)
           (add_vec_int pc 2) n -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Himm. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    (* the room below sp is a CONSEQUENCE of owning the free stack *)
    iDestruct (ustack_room with "Hheap Hstk") as %Hroom'.
    assert (Hroom : 8 * Z.of_nat k <= uint (m !!! Regidx csp_rs1)) by lia.
    assert (Hu : uint (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))
                 = uint (m !!! Regidx csp_rs1) - 8 * Z.of_nat k).
    { rewrite !uint_unsigned.
      exact (uv_avi_neg (m !!! Regidx csp_rs1) (8 * Z.of_nat k) ltac:(lia)
               ltac:(rewrite <- uint_unsigned; exact Hroom)). }
    rewrite (ustack_app γd (m !!! Regidx csp_rs1)
               (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k))) k n Hu).
    iDestruct "Hstk" as "(Hframe & Hstk)".
    iApply (UkLeaf.wp_uk_caddi16sp C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm
              (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))
              Hui ltac:(unfold add_vec_int; f_equal; exact (eq_sym Himm))
              with "Hb [Hheap Hstk Hufd Hframe Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd [Hframe Hcont]").
    - rewrite (upd_eq m (Regidx csp_rs1) (regval_into_reg _)). iExact "Hstk".
    - iIntros (h') "Hrun". iApply ("Hcont" with "Hframe Hrun").
  Qed.

  (* ...and ITS pop.  putc, printf and vprintf all pop with c.addi16sp
     (32 and 96 bytes), so the mirror is not optional; it is
     [wp_uk_caddi_sp_up]'s proof with [caddi16sp_imm] in the premise. *)
  Lemma wp_uk_caddi16sp_up (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (k n : nat) :
    (sign_extend' 64 (caddi16sp_imm imm) : mword 64)
      = mword_of_int (8 * Z.of_nat k) ->
    uinstr_is γt pc true (C_ADDI16SP imm) -∗
    ustack γd (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k)) k -∗
    urun γt γd γs γfd h m pc n -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx csp_rs1
            := regval_into_reg
                 (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))]> m)
         (add_vec_int pc 2) (k + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Himm. iIntros "#Hi Hframe Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (ustack_nowrap with "Hheap Hframe") as %Hnw.
    assert (Hu : uint (m !!! Regidx csp_rs1)
                 = uint (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
                   - 8 * Z.of_nat k).
    { rewrite !uint_unsigned.
      rewrite (uv_avi_pos (m !!! Regidx csp_rs1) (8 * Z.of_nat k) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; exact Hnw)). lia. }
    iApply (UkLeaf.wp_uk_caddi16sp C pt Rfd Rut pm sz Hlo Hpm HRut M m pc fdv imm
              (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
              Hui ltac:(unfold add_vec_int; f_equal; exact (eq_sym Himm))
              with "Hb [Hheap Hstk Hufd Hframe Hcont]").
    iApply (urun_close with "Hheap [Hstk Hframe] Hufd Hcont").
    rewrite (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    rewrite (ustack_app γd (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
               (m !!! Regidx csp_rs1) k n Hu).
    iFrame "Hframe Hstk".
  Qed.

End UkRunLeaf.
