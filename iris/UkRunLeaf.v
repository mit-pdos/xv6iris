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
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import ghost_map ghost_var invariants.
From transfinite.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import UmodeArith.
Require Import WpMmodeLeafBase.
Require Import UkLeaf.
Require Import UserHeap.
Require Import CtxIdDefs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import WpUmodeBranch.
Require Import UkBranch.
Require Import UmodeAbi.
Require Import UkRun.

From Stdlib Require Import ZArith Bool Lia.
From transfinite.base_logic.lib Require Import invariants.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeStep.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkRunLeaf.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  (* ------------------------------------------------------------------- *)
  (* c.li rd, imm -- rd := sext(imm).  Hand-cut rather than generated,     *)
  (* because the decoder ALSO adds x0 here, and [uimm6_norm] kills the     *)
  (* whole chain at once.                                                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_cli (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    uinstr_is (ukn_t N) pc true (C_LI (imm, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h'
         (<[Regidx rd := regval_into_reg (sign_extend' 64 imm : mword 64)]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns Hrd. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cli C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rd
              (sign_extend' 64 imm) Hui Hrd (eq_sym (uimm6_norm imm))
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_caddi (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rd) (sign_extend' 64 imm) ->
    uinstr_is (ukn_t N) pc true (C_ADDI (imm, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddi C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rd wval
              Hui H1 ltac:(rewrite (sext6_12_64 imm); exact H2)
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_caddi4spn (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (cr : mword 3) (nzimm : mword 8) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx cr) = Regidx rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)) ->
    uinstr_is (ukn_t N) pc true (C_ADDI4SPN (Cregidx cr, nzimm)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddi4spn C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv cr nzimm rd wval
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_jal (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 21) (rd : mword 5) (tgt wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    wval = add_vec_int pc 4 ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uinstr_is (ukn_t N) pc false (JAL (imm, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         tgt avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jal C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rd tgt wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_cjr (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 : mword 5) (tgt : mword 64) (avail : nat) :
    uint rs1 <> 0 ->
    tgt = ret_pc (m !!! Regidx rs1) ->
    uinstr_is (ukn_t N) pc true (C_JR (Regidx rs1)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' m
         tgt avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cjr C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 tgt
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
  Qed.

  Lemma wp_uk_cmv (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec zero_reg (m !!! Regidx rs2) ->
    uinstr_is (ukn_t N) pc true (C_MV (Regidx rd, Regidx rs2)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cmv C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rd rs2 wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_caddiw (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (subrange_vec_dec (add_vec (m !!! Regidx rd) (sign_extend' 64 imm)) 31 0) ->
    uinstr_is (ukn_t N) pc true (C_ADDIW (imm, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddiw C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rd wval
              Hui H1 ltac:(rewrite (sext6_12_64 imm); exact H2)
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_cj (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 11) (tgt : mword 64) (avail : nat) :
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0")))) ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uinstr_is (ukn_t N) pc true (C_J imm) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' m
         tgt avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cj C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm tgt
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
  Qed.

  Lemma wp_uk_addi (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is (ukn_t N) pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addi C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_add (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is (ukn_t N) pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_add C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_slli (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = shift_bits_left (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is (ukn_t N) pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_slli C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_srli (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is (ukn_t N) pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_srli C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_subw (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (sub_vec (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is (ukn_t N) pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_subw C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_auipc (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 20) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec pc (auipc_off imm) ->
    uinstr_is (ukn_t N) pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_auipc C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_sub (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is (ukn_t N) pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sub C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_and (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uinstr_is (ukn_t N) pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_and C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_sltu (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) ->
    uinstr_is (ukn_t N) pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sltu C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_addw (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (add_vec (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is (ukn_t N) pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addw C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_sltiu (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (sign_extend' 64 imm))) ->
    uinstr_is (ukn_t N) pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_sltiu C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_andi (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is (ukn_t N) pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_andi C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_xori (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = xor_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uinstr_is (ukn_t N) pc false (ITYPE (imm, Regidx rs1, Regidx rd, XORI)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_xori C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_addiw (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (subrange_vec_dec (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 31 0) ->
    uinstr_is (ukn_t N) pc false (ADDIW (imm, Regidx rs1, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_addiw C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_slliw (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 5) (rs1 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (shift_bits_left (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32) shamt) ->
    uinstr_is (ukn_t N) pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_slliw C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv shamt rs1 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_lui (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 20) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = luival imm ->
    uinstr_is (ukn_t N) pc false (UTYPE (imm, Regidx rd, LUI)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_lui C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_divu (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = to_bits_truncate 64 (if Z.eqb (uint (m !!! Regidx rs2)) 0 then -1 else Z.quot (uint (m !!! Regidx rs1)) (uint (m !!! Regidx rs2))) ->
    uinstr_is (ukn_t N) pc false (DIV (Regidx rs2, Regidx rs1, Regidx rd, true)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_divu C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_remu (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rs1 rs2 rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = to_bits_truncate 64 (if Z.eqb (uint (m !!! Regidx rs2)) 0 then uint (m !!! Regidx rs1) else Z.rem (uint (m !!! Regidx rs1)) (uint (m !!! Regidx rs2))) ->
    uinstr_is (ukn_t N) pc false (REM (Regidx rs2, Regidx rs1, Regidx rd, true)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_remu C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rs1 rs2 rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_jalr (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (wr : option (mword 5 * mword 64)) (tgt : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rs1 <> 0 ->
    (uint rd = 0 /\ wr = None) \/ (uint rd <> 0 /\ wr = Some (rd, add_vec_int pc 4)) ->
    tgt = ret_pc (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ->
    uinstr_is (ukn_t N) pc false (JALR (imm, Regidx rs1, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (uv_upd m wr)
         tgt avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jalr C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs1 rd wr tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (uv_upd_not_sp m rd wr (add_vec_int pc 4) Hns H2). iExact "Hstk".
  Qed.

  Lemma wp_uk_jr (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (tgt : mword 64) (avail : nat) :
    uint rs1 <> 0 ->
    uint rd = 0 ->
    tgt = ret_pc (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ->
    uinstr_is (ukn_t N) pc false (JALR (imm, Regidx rs1, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' m
         tgt avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_jr C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs1 rd tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
  Qed.

  Lemma wp_uk_cadd (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rd) (m !!! Regidx rs2) ->
    uinstr_is (ukn_t N) pc true (C_ADD (Regidx rd, Regidx rs2)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cadd C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv rd rs2 wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_cand (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (crd crs2 : mword 3) (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    creg2reg_idx (Cregidx crs2) = Regidx rs2 ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rd) (m !!! Regidx rs2) ->
    uinstr_is (ukn_t N) pc true (C_AND (Cregidx crd, Cregidx crs2)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cand C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv crd crs2 rd rs2 wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_caddw (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (crd crs2 : mword 3) (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    creg2reg_idx (Cregidx crs2) = Regidx rs2 ->
    uint rd <> 0 ->
    wval = sign_extend' 64 (add_vec (subrange_vec_dec (m !!! Regidx rd) 31 0 : mword 32) (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uinstr_is (ukn_t N) pc true (C_ADDW (Cregidx crd, Cregidx crs2)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_caddw C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv crd crs2 rd rs2 wval
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_clui (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 6) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = luival (sign_extend' 20 imm) ->
    uinstr_is (ukn_t N) pc true (C_LUI (imm, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_clui C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_cslli (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is (ukn_t N) pc true (C_SLLI (shamt, Regidx rd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_cslli C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv shamt rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_csrli (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (shamt : mword 6) (crd : mword 3) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    wval = shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uinstr_is (ukn_t N) pc true (C_SRLI (shamt, Cregidx crd)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_csrli C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv shamt crd rd wval
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.

  Lemma wp_uk_li (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rd : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec zero_reg (sign_extend' 64 imm) ->
    uinstr_is (ukn_t N) pc false
      (ITYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rd, ADDI)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' (<[Regidx rd := regval_into_reg wval]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkLeaf.wp_uk_li C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rd wval
              Hui H1 H2
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk".
  Qed.


  (* ===================================================================== *)
  (* THE BRANCHES.  The one place [pc'] is not a constant offset: the       *)
  (* continuation is at [if taken then tgt else pc+k], and the program      *)
  (* discharges [taken] by computing it.  No register is written, so no     *)
  (* [unot_sp] and [avail] rides through.                                   *)
  (* ===================================================================== *)

  Lemma wp_uk_btype (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 13) (rs2 rs1 : mword 5) (op : bop) (taken : bool) (tgt : mword 64) (avail : nat) :
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is (ukn_t N) pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' m
         (if taken then tgt else add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_btype C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs2 rs1 op taken tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
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
  Lemma wp_uk_btype_later (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) (avail : nat) :
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is (ukn_t N) pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) -∗
    urun N h m pc avail -∗
    ▷ (∀ h' : CpuId,
         urun N h' m
           (if taken then tgt else add_vec_int pc 4) avail -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_btype_later C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm rs2 rs1
              op taken tgt Hui H1 H2 H3
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iNext.
    iApply (urun_close with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
  Qed.

  Lemma wp_uk_cbeqz (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 8) (cr : mword 3) (rs : mword 5) (taken : bool) (tgt : mword 64) (avail : nat) :
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = eq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is (ukn_t N) pc true (C_BEQZ (imm, Cregidx cr)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' m
         (if taken then tgt else add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_cbeqz C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm cr rs taken tgt
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
  Qed.

  Lemma wp_uk_cbnez (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 8) (cr : mword 3) (rs : mword 5) (taken : bool) (tgt : mword 64) (avail : nat) :
    creg2reg_idx (Cregidx cr) = Regidx rs ->
    taken = neq_vec (m !!! Regidx rs) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0")))) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is (ukn_t N) pc true (C_BNEZ (imm, Cregidx cr)) -∗
    urun N h m pc avail -∗
    (∀ h' : CpuId,
       urun N h' m
         (if taken then tgt else add_vec_int pc 2) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros H1 H2 H3 H4. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_cbnez C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm cr rs taken tgt
              Hui H1 H2 H3 H4
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    iApply (urun_close with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
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
  Proof using .
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
  Lemma wp_uk_caddi_sp_dn (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (k n : nat) :
    (sign_extend' 64 imm : mword 64) = mword_of_int (- (8 * Z.of_nat k)) ->
    uinstr_is (ukn_t N) pc true (C_ADDI (imm, Regidx csp_rs1)) -∗
    urun N h m pc (k + n) -∗
    (ustack (ukn_d N) (m !!! Regidx csp_rs1) k -∗
       ∀ h' : CpuId,
         urun N h'
           (<[Regidx csp_rs1
              := regval_into_reg
                   (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))]> m)
           (add_vec_int pc 2) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Himm. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    (* the room below sp is a CONSEQUENCE of owning the free stack *)
    iDestruct (ustack_room with "Hheap Hstk") as %Hroom'.
    assert (Hroom : 8 * Z.of_nat k <= uint (m !!! Regidx csp_rs1)) by lia.
    assert (Hu : uint (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))
                 = uint (m !!! Regidx csp_rs1) - 8 * Z.of_nat k).
    { rewrite !uint_unsigned.
      exact (uv_avi_neg (m !!! Regidx csp_rs1) (8 * Z.of_nat k) ltac:(lia)
               ltac:(rewrite <- uint_unsigned; exact Hroom)). }
    rewrite (ustack_app (ukn_d N) (m !!! Regidx csp_rs1)
               (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k))) k n Hu).
    iDestruct "Hstk" as "(Hframe & Hstk)".
    iApply (UkLeaf.wp_uk_caddi C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm csp_rs1
              (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))
              Hui ltac:(vm_compute; discriminate)
              ltac:(rewrite (sext6_12_64 imm) Himm; reflexivity)
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hframe Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx [Hframe Hcont]").
    - rewrite (upd_eq m (Regidx csp_rs1) (regval_into_reg _)). iExact "Hstk".
    - iIntros (h') "Hrun". iApply ("Hcont" with "Hframe Hrun").
  Qed.

  (* ...and THE POP, its mirror.  The extra premise is the absence of wrap,
     which the push does not need (sp only ever comes back down to where it
     started, but the leaf cannot see that). *)
  Lemma wp_uk_caddi_sp_up (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (k n : nat) :
    (sign_extend' 64 imm : mword 64) = mword_of_int (8 * Z.of_nat k) ->
    uinstr_is (ukn_t N) pc true (C_ADDI (imm, Regidx csp_rs1)) -∗
    ustack (ukn_d N) (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k)) k -∗
    urun N h m pc n -∗
    (∀ h' : CpuId,
       urun N h'
         (<[Regidx csp_rs1
            := regval_into_reg
                 (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))]> m)
         (add_vec_int pc 2) (k + n) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Himm. iIntros "#Hi Hframe Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    (* ...and so is the absence of wrap, off the frame being returned *)
    iDestruct (ustack_nowrap with "Hheap Hframe") as %Hnw.
    assert (Hu : uint (m !!! Regidx csp_rs1)
                 = uint (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
                   - 8 * Z.of_nat k).
    { rewrite !uint_unsigned.
      rewrite (uv_avi_pos (m !!! Regidx csp_rs1) (8 * Z.of_nat k) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; exact Hnw)). lia. }
    iApply (UkLeaf.wp_uk_caddi C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm csp_rs1
              (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
              Hui ltac:(vm_compute; discriminate)
              ltac:(rewrite (sext6_12_64 imm) Himm; reflexivity)
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hframe Hcont]").
    iApply (urun_close with "Hheap [Hstk Hframe] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    rewrite (ustack_app (ukn_d N) (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
               (m !!! Regidx csp_rs1) k n Hu).
    iFrame "Hframe Hstk".
  Qed.

  (* c.addi16sp is the OTHER push: gcc uses it for frames of 32..512 bytes,
     which is echo's main (64).  Same shape, different immediate decoder --
     and the decoder is again the CALLER's one-line obligation, not part of
     the statement. *)
  Lemma wp_uk_caddi16sp_dn (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (k n : nat) :
    (sign_extend' 64 (caddi16sp_imm imm) : mword 64)
      = mword_of_int (- (8 * Z.of_nat k)) ->
    uinstr_is (ukn_t N) pc true (C_ADDI16SP imm) -∗
    urun N h m pc (k + n) -∗
    (ustack (ukn_d N) (m !!! Regidx csp_rs1) k -∗
       ∀ h' : CpuId,
         urun N h'
           (<[Regidx csp_rs1
              := regval_into_reg
                   (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))]> m)
           (add_vec_int pc 2) n -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Himm. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    (* the room below sp is a CONSEQUENCE of owning the free stack *)
    iDestruct (ustack_room with "Hheap Hstk") as %Hroom'.
    assert (Hroom : 8 * Z.of_nat k <= uint (m !!! Regidx csp_rs1)) by lia.
    assert (Hu : uint (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))
                 = uint (m !!! Regidx csp_rs1) - 8 * Z.of_nat k).
    { rewrite !uint_unsigned.
      exact (uv_avi_neg (m !!! Regidx csp_rs1) (8 * Z.of_nat k) ltac:(lia)
               ltac:(rewrite <- uint_unsigned; exact Hroom)). }
    rewrite (ustack_app (ukn_d N) (m !!! Regidx csp_rs1)
               (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k))) k n Hu).
    iDestruct "Hstk" as "(Hframe & Hstk)".
    iApply (UkLeaf.wp_uk_caddi16sp C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm
              (add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat k)))
              Hui ltac:(unfold add_vec_int; f_equal; exact (eq_sym Himm))
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hframe Hcont]").
    iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx [Hframe Hcont]").
    - rewrite (upd_eq m (Regidx csp_rs1) (regval_into_reg _)). iExact "Hstk".
    - iIntros (h') "Hrun". iApply ("Hcont" with "Hframe Hrun").
  Qed.

  (* ...and ITS pop.  putc, printf and vprintf all pop with c.addi16sp
     (32 and 96 bytes), so the mirror is not optional; it is
     [wp_uk_caddi_sp_up]'s proof with [caddi16sp_imm] in the premise. *)
  Lemma wp_uk_caddi16sp_up (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 6) (k n : nat) :
    (sign_extend' 64 (caddi16sp_imm imm) : mword 64)
      = mword_of_int (8 * Z.of_nat k) ->
    uinstr_is (ukn_t N) pc true (C_ADDI16SP imm) -∗
    ustack (ukn_d N) (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k)) k -∗
    urun N h m pc n -∗
    (∀ h' : CpuId,
       urun N h'
         (<[Regidx csp_rs1
            := regval_into_reg
                 (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))]> m)
         (add_vec_int pc 2) (k + n) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Himm. iIntros "#Hi Hframe Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (ustack_nowrap with "Hheap Hframe") as %Hnw.
    assert (Hu : uint (m !!! Regidx csp_rs1)
                 = uint (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
                   - 8 * Z.of_nat k).
    { rewrite !uint_unsigned.
      rewrite (uv_avi_pos (m !!! Regidx csp_rs1) (8 * Z.of_nat k) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; exact Hnw)). lia. }
    iApply (UkLeaf.wp_uk_caddi16sp C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv imm
              (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
              Hui ltac:(unfold add_vec_int; f_equal; exact (eq_sym Himm))
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hframe Hcont]").
    iApply (urun_close with "Hheap [Hstk Hframe] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
    rewrite (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    rewrite (ustack_app (ukn_d N) (add_vec_int (m !!! Regidx csp_rs1) (8 * Z.of_nat k))
               (m !!! Regidx csp_rs1) k n Hu).
    iFrame "Hframe Hstk".
  Qed.


  (* ===================================================================== *)
  (* THE [c.mv] LEAF THAT HANDS THE STEP'S OWN LATER OUT (lane             *)
  (* SH-PIPE-ROUND-7; design app-pipe SS4.3o, route (a), the first of the  *)
  (* two generic ADDITIONS).                                               *)
  (*                                                                       *)
  (* [wp_uk_btype_later] above and [UkRunBr.wp_uk_btype0_later] are the    *)
  (* only two leaves of this tier that hand the step's [▷] to the caller,  *)
  (* and both are BTYPE -- a branch.  A caller that must strip a [▷] at a  *)
  (* point where the next instruction is a REGISTER MOVE (the pipeline     *)
  (* era's fork re-entry: the parent redeems its child's exit payload out  *)
  (* of the escrow with the plain [ChildTok.gen_pay], which costs a later, *)
  (* and the two instructions it runs next are [0x938 c.mv a1,s3] and      *)
  (* [0x93a c.mv a0,s2]) had no leaf to do it at.  This is that leaf: the  *)
  (* statement of [wp_uk_cmv] with the continuation under a [▷], over      *)
  (* [UkStep.wp_uk_retire_later] -- the very lemma [UkLeaf.wp_uk_cmv]'s    *)
  (* [wp_uk_retire] is the later-free restatement of -- so the certificate *)
  (* (the redirect to [RTYPE ... ADD], the two totality facts and the      *)
  (* value equation) is [UkLeaf.wp_uk_cmv]'s, unchanged.                   *)
  (* ===================================================================== *)
  Lemma wp_uk_cmv_later (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (rd rs2 : mword 5) (wval : mword 64) (avail : nat) :
    unot_sp rd ->
    uint rd <> 0 ->
    wval = add_vec zero_reg (m !!! Regidx rs2) ->
    uinstr_is (ukn_t N) pc true (C_MV (Regidx rd, Regidx rs2)) -∗
    urun N h m pc avail -∗
    ▷ (∀ h' : CpuId,
         urun N h' (<[Regidx rd := regval_into_reg wval]> m)
           (add_vec_int pc 2) avail -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkStep.wp_uk_retire_later C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf
              M m pc fdv cw gn cs pidv true (C_MV (Regidx rd, Regidx rs2))
              (Some (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)))
              None (Some (rd, wval)) Hui
              ltac:(intro s; apply exec_execute_C_MV)
              eq_refl H1
              (fun s _ _ _ _ _ => UserTotalU.goodmb_execute_C_MV UserFrame.Du_r UserFrame.Du_w
                          (Regidx rd) (Regidx rs2) s)
              (fun s _ _ _ _ _ => UserExecFacts.goodmb_execute_RTYPE_total UserFrame.Du_r UserFrame.Du_w rs2
                          (zero_extend' 5 ('b"00")) rd ADD s
                          (UserFrame.Du_gpr_of_Z_r (zero_extend' 5 ('b"00")))
                          (UserFrame.Du_gpr_of_Z_r rs2) (UserFrame.Du_gpr_of_Z rd))
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    2:{ iNext.
        iApply (urun_close with "Hheap [Hstk] Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont").
        rewrite (unot_sp_upd rd _ m Hns). iExact "Hstk". }
    intros s_pc _ _ _ _ Hvals.
    cbn [uv_exp uv_post uv_jmp uv_wr].
    change zreg with (Regidx cli_rs1).
    change (execute (RTYPE (Regidx rs2, Regidx cli_rs1, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx cli_rs1) (Regidx rd) ADD).
    rewrite (WpGpr.exec_execute_RTYPE_ADD_gpr rs2 cli_rs1 rd s_pc).
    unfold WpGpr.gpr_rd_val.
    rewrite (Hvals rs2).
    replace (Z.eqb (uint cli_rs1) 0) with true by (vm_compute; reflexivity).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact H1).
    rewrite H2. reflexivity.
  Qed.


  (* ===================================================================== *)
  (* ...AND THE [c.jr] LEAF THAT HANDS THE STEP'S OWN LATER OUT (lane      *)
  (* SH-PIPE-ROUND-7, finding (2)).                                        *)
  (*                                                                       *)
  (* THIS IS THE LEAF THE LATER REPAIR ACTUALLY NEEDS, and the one         *)
  (* SH-PIPE-ROUND-6's measurement missed.  ROUND-6 looked for a           *)
  (* later-providing step BETWEEN THE WAIT'S RETURN (0x938) AND THE        *)
  (* PROMPT and found none; but the resource whose later has to be         *)
  (* stripped -- the child's exit payload, redeemed out of the escrow with *)
  (* [ChildTok.gen_pay] -- becomes available one instruction EARLIER, at   *)
  (* the [wait] ECALL's return (0xc90), and the [c.jr ra] at 0xc94 that    *)
  (* returns from [wait] stands between that point and 0x938              *)
  (* ([UkShRun.wp_kshr_wait_pid] is [c.li a7,3 ; ecall ; c.jr ra]).  So    *)
  (* the later CAN be paid -- by a wait twin that hands its answer at      *)
  (* 0xc94 and this leaf -- and the parent re-enters the command loop at   *)
  (* 0x938 with the payload LATER-FREE, which is the only shape the loop   *)
  (* head accepts (see the lane's report: stripping at 0x938 instead       *)
  (* consumes the head's own first instruction and there is no re-entry    *)
  (* at 0x93a).                                                            *)
  (* ===================================================================== *)
  Lemma wp_uk_cjr_later (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (rs1 : mword 5) (tgt : mword 64) (avail : nat) :
    uint rs1 <> 0 ->
    tgt = ret_pc (m !!! Regidx rs1) ->
    uinstr_is (ukn_t N) pc true (C_JR (Regidx rs1)) -∗
    urun N h m pc avail -∗
    ▷ (∀ h' : CpuId,
         urun N h' m tgt avail -∗ mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros H1 H2. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkStep.wp_uk_retire_later C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf
              M m pc fdv cw gn cs pidv true (C_JR (Regidx rs1))
              (Some (JALR (zeros' 12, Regidx rs1, zreg)))
              (Some tgt) None Hui
              ltac:(intro s; apply exec_execute_C_JR)
              eq_refl I
              (fun s _ _ _ _ _ =>
                 UserTotalU.goodmb_execute_C_JR UserFrame.Du_r UserFrame.Du_w
                   (Regidx rs1) s)
              ltac:(intros s _ _ _ Hag _;
                    exact (UserExecFacts.goodmb_execute_JALR_total
                             UserFrame.Du_r UserFrame.Du_w (zeros' 12) rs1
                             (zero_extend' 5 ('b"00")) s
                             UserTotalU.Du_r_nPC UserTotalU.Du_w_nPC
                             (UserFrame.Du_gpr_of_Z_r rs1)
                             (UserFrame.Du_gpr_of_Z (zero_extend' 5 ('b"00")))
                             (UserTotalU.u_gm_zicfilp s Hag)
                             (agree_u_zicfilp s Hag)
                             (UserTotalU.u_gm_zca s Hag) (agree_u_zca s Hag)))
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hcont]").
    2:{ iNext.
        iApply (urun_close with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx Hcont"). }
    intros s_pc _ _ _ Hag Hvals.
    cbn [uv_exp uv_post uv_jmp uv_wr uv_upd].
    assert (Hrsv : register_lookup (R_bitvector_64 (WpGpr.gpr_of_Z (uint rs1)))
                     s_pc.(sregs) = m !!! Regidx rs1).
    { pose proof (Hvals rs1) as Hv.
      replace (Z.eqb (uint rs1) 0) with false in Hv
        by (symmetry; apply Z.eqb_neq; exact H1).
      exact Hv. }
    change (execute (JALR (zeros' 12, Regidx rs1, zreg)))
      with (execute_JALR (zeros' 12) (Regidx rs1) zreg).
    change zreg with (Regidx cli_rs1).
    rewrite (exec_execute_JALR_ret_zca (zeros' 12) rs1 cli_rs1 s_pc H1
               ltac:(vm_compute; reflexivity)
               (agree_u_zicfilp s_pc Hag) (agree_u_zca s_pc Hag)
               ltac:(apply UserBits.bit0_update0_64)).
    rewrite Hrsv. rewrite ret_pc_jalr. rewrite H2. reflexivity.
  Qed.

End UkRunLeaf.
