(* ProofProcdumpParts.v -- procdump's three STRAIGHT-LINE blocks, as
   whole-block WP lemmas: the prologue (+0x00..+0x1a), the seven hoisted
   constants (+0x22..+0x54) and the epilogue (+0x8e..+0xa2).  The scan
   between them lives in its own file; nothing here mentions it.

   The frame is 80 bytes = 10 slots and NINE registers are saved
   (ra,s0,s1,s2..s7) at c.sdsp displacements 72..8, i.e. [pa_stk sp0 k] for
   k = 1..9; slot 10 (displacement 0) is never touched and is [pd_frame]'s
   [exists w] conjunct.  Structurally this is kwait's frame exactly, so the
   three blocks follow ProofKwait.v's prologue / [kw_epilogue] instruction
   for instruction.

   TWO SPELLINGS OF sp MEET HERE.  [ProcdumpAux.pdR 2] is
   [Regidx (mword_of_int 2)] while every leaf is stated over
   [Regidx csp_rs1] = [Regidx (zero_extend' 5 'b"10")].  The two are
   convertible but not syntactically equal, so each proof opens with
   [rewrite /pdR] followed by ONE [change ... with (Regidx csp_rs1)]; after
   that the whole body is spelled the way the leaves are. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSmodeIntr.
Require Import IntrDefs WpNext.
Require Import ArrCursor.
Require Import ProcGeom.
Require Import ProcdumpAux.
Require Import CodeProcdump.
From Kernel Require KernelInstrs KernelSyms.
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a whole-function WP otherwise spends tens of minutes
   FORMATTING the goal -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

Notation PD := KernelSyms.procdump.

(* ------------------------------------------------------------------ *)
(* Numeric side conditions, mword-free and at the top level (the        *)
(* [ap_K*] rule in durable-notes: [lia] misbehaves in a context full of  *)
(* [bv_unsigned]).                                                      *)
(* ------------------------------------------------------------------ *)
Lemma pd_K10 (K : nat) : (48 <= K)%nat -> (10 <= K)%nat.
Proof. lia. Qed.

Lemma pd_Kpop (K : nat) : (10 <= K)%nat -> ((K - 10) + 10)%nat = K.
Proof. lia. Qed.

Section ProofProcdumpParts.
  Context `{!riscvGS Σ, !sieG Σ}.

  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.
  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.
  (* peel ONE update layer at a time (unfold-then-peel on the whole chain is
     O(depth^2): claude-notes/optimization.md). *)
  Local Ltac peel_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].
  Local Ltac peel_reg := peel_step; reflexivity.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).

  (* ================================================================== *)
  (* +0x00 .. +0x1a -- push the 80-byte frame, save ra/s0/s1..s7, set s0 *)
  (* to the ENTRY sp, and materialise a0 = "\n" for the first printk.    *)
  (* ================================================================== *)
  Lemma wp_pd_prologue `{GEN : GenId} `{CID0 : CpuId}
      (m : regfile) (K : nat) (b : bool) (p : mword 64) :
    (48 <= K)%nat ->
    sie_cap_gpr m K b p -∗
    kernel_text -∗
    pc_is (mword_of_int KernelSyms.procdump) -∗
    wp_next (CID0 := CID0) b p (fun (CIDq : CpuId) =>
      ∀ (M : regfile),
        ⌜ pd_regs_pro m M ⌝ -∗
        sie_cap_gpr M (K - 10) b p -∗
        pd_frame (m !!! pdR 2) (m !!! pdR 1) (m !!! pdR 8) (m !!! pdR 9)
                 (m !!! pdR 18) (m !!! pdR 19) (m !!! pdR 20) (m !!! pdR 21)
                 (m !!! pdR 22) (m !!! pdR 23) -∗
        pc_is (mword_of_int (KernelSyms.procdump + 0x1e)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro HK.
    rewrite /pdR.
    change (Regidx (mword_of_int 2 : mword 5)) with (Regidx csp_rs1).
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (pdi_00 with "Htext") as "Hi00".
    iPoseProof (pdi_02 with "Htext") as "Hi02".
    iPoseProof (pdi_04 with "Htext") as "Hi04".
    iPoseProof (pdi_06 with "Htext") as "Hi06".
    iPoseProof (pdi_08 with "Htext") as "Hi08".
    iPoseProof (pdi_0a with "Htext") as "Hi0a".
    iPoseProof (pdi_0c with "Htext") as "Hi0c".
    iPoseProof (pdi_0e with "Htext") as "Hi0e".
    iPoseProof (pdi_10 with "Htext") as "Hi10".
    iPoseProof (pdi_12 with "Htext") as "Hi12".
    iPoseProof (pdi_14 with "Htext") as "Hi14".
    iPoseProof (pdi_16 with "Htext") as "Hi16".
    iPoseProof (pdi_1a with "Htext") as "Hi1a".
    (* ---- +0x00 c.addi16sp sp,-80 ---- *)
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int PD : mword 64)
              (mword_of_int 59 : mword 6) m K 10%nat b
              ltac:(exact (pd_K10 K HK)) (pd_stk_push_80 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (P0 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /P0 upd_eq; apply pd_stk_push_80).
    (* the nine save-slot addresses, as the c.sdsp displacements compute them *)
    assert (Hb1 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 1).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 2).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 3).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 5).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 6).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 7).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 8).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 9).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _)".
    iDestruct "F1" as (v1) "H1". iDestruct "F2" as (v2) "H2".
    iDestruct "F3" as (v3) "H3". iDestruct "F4" as (v4) "H4".
    iDestruct "F5" as (v5) "H5". iDestruct "F6" as (v6) "H6".
    iDestruct "F7" as (v7) "H7". iDestruct "F8" as (v8) "H8".
    iDestruct "F9" as (v9) "H9".
    assert (Hp02 : add_vec_int (mword_of_int PD : mword 64) 2 = mword_of_int (PD + 0x2)) by pcstep.
    iEval (rewrite Hp02) in "Hpc".
    (* ---- +0x02 .. +0x12: the nine c.sdsp ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0x2)) (mword_of_int 9 : mword 6) Rra
              P0 (K - 10)%nat v1 b with "Hcg Hpc Hi02 [H1] [-]").
    { iEval (rewrite Hb1). iExact "H1". }
    iIntros (CID2 Hs2) "Hcg Hpc H1". iEval (rewrite Hb1) in "H1". iEval (rgne) in "H1".
    assert (Hp04 : add_vec_int (mword_of_int (PD + 0x2) : mword 64) 2 = mword_of_int (PD + 0x4)) by pcstep.
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0x4)) (mword_of_int 8 : mword 6) Rs0
              P0 (K - 10)%nat v2 b with "Hcg Hpc Hi04 [H2] [-]").
    { iEval (rewrite Hb2). iExact "H2". }
    iIntros (CID3 Hs3) "Hcg Hpc H2". iEval (rewrite Hb2) in "H2". iEval (rgne) in "H2".
    assert (Hp06 : add_vec_int (mword_of_int (PD + 0x4) : mword 64) 2 = mword_of_int (PD + 0x6)) by pcstep.
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0x6)) (mword_of_int 7 : mword 6) Rs1
              P0 (K - 10)%nat v3 b with "Hcg Hpc Hi06 [H3] [-]").
    { iEval (rewrite Hb3). iExact "H3". }
    iIntros (CID4 Hs4) "Hcg Hpc H3". iEval (rewrite Hb3) in "H3". iEval (rgne) in "H3".
    assert (Hp08 : add_vec_int (mword_of_int (PD + 0x6) : mword 64) 2 = mword_of_int (PD + 0x8)) by pcstep.
    iEval (rewrite Hp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0x8)) (mword_of_int 6 : mword 6) Rs2
              P0 (K - 10)%nat v4 b with "Hcg Hpc Hi08 [H4] [-]").
    { iEval (rewrite Hb4). iExact "H4". }
    iIntros (CID5 Hs5) "Hcg Hpc H4". iEval (rewrite Hb4) in "H4". iEval (rgne) in "H4".
    assert (Hp0a : add_vec_int (mword_of_int (PD + 0x8) : mword 64) 2 = mword_of_int (PD + 0xa)) by pcstep.
    iEval (rewrite Hp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0xa)) (mword_of_int 5 : mword 6) Rs3
              P0 (K - 10)%nat v5 b with "Hcg Hpc Hi0a [H5] [-]").
    { iEval (rewrite Hb5). iExact "H5". }
    iIntros (CID6 Hs6) "Hcg Hpc H5". iEval (rewrite Hb5) in "H5". iEval (rgne) in "H5".
    assert (Hp0c : add_vec_int (mword_of_int (PD + 0xa) : mword 64) 2 = mword_of_int (PD + 0xc)) by pcstep.
    iEval (rewrite Hp0c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0xc)) (mword_of_int 4 : mword 6) Rs4
              P0 (K - 10)%nat v6 b with "Hcg Hpc Hi0c [H6] [-]").
    { iEval (rewrite Hb6). iExact "H6". }
    iIntros (CID7 Hs7) "Hcg Hpc H6". iEval (rewrite Hb6) in "H6". iEval (rgne) in "H6".
    assert (Hp0e : add_vec_int (mword_of_int (PD + 0xc) : mword 64) 2 = mword_of_int (PD + 0xe)) by pcstep.
    iEval (rewrite Hp0e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0xe)) (mword_of_int 3 : mword 6) Rs5
              P0 (K - 10)%nat v7 b with "Hcg Hpc Hi0e [H7] [-]").
    { iEval (rewrite Hb7). iExact "H7". }
    iIntros (CID8 Hs8) "Hcg Hpc H7". iEval (rewrite Hb7) in "H7". iEval (rgne) in "H7".
    assert (Hp10 : add_vec_int (mword_of_int (PD + 0xe) : mword 64) 2 = mword_of_int (PD + 0x10)) by pcstep.
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0x10)) (mword_of_int 2 : mword 6) Rs6
              P0 (K - 10)%nat v8 b with "Hcg Hpc Hi10 [H8] [-]").
    { iEval (rewrite Hb8). iExact "H8". }
    iIntros (CID9 Hs9) "Hcg Hpc H8". iEval (rewrite Hb8) in "H8". iEval (rgne) in "H8".
    assert (Hp12 : add_vec_int (mword_of_int (PD + 0x10) : mword 64) 2 = mword_of_int (PD + 0x12)) by pcstep.
    iEval (rewrite Hp12) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (PD + 0x12)) (mword_of_int 1 : mword 6) Rs7
              P0 (K - 10)%nat v9 b with "Hcg Hpc Hi12 [H9] [-]").
    { iEval (rewrite Hb9). iExact "H9". }
    iIntros (CID10 Hs10) "Hcg Hpc H9". iEval (rewrite Hb9) in "H9". iEval (rgne) in "H9".
    (* re-anchor the nine cells off [m] *)
    assert (HP0ra : P0 !!! Regidx Rra = m !!! Regidx Rra) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s0 : P0 !!! Regidx Rs0 = m !!! Regidx Rs0) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s1 : P0 !!! Regidx Rs1 = m !!! Regidx Rs1) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s2 : P0 !!! Regidx Rs2 = m !!! Regidx Rs2) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s3 : P0 !!! Regidx Rs3 = m !!! Regidx Rs3) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s4 : P0 !!! Regidx Rs4 = m !!! Regidx Rs4) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s5 : P0 !!! Regidx Rs5 = m !!! Regidx Rs5) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s6 : P0 !!! Regidx Rs6 = m !!! Regidx Rs6) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s7 : P0 !!! Regidx Rs7 = m !!! Regidx Rs7) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0ra) in "H1". iEval (rewrite HP0s0) in "H2".
    iEval (rewrite HP0s1) in "H3". iEval (rewrite HP0s2) in "H4".
    iEval (rewrite HP0s3) in "H5". iEval (rewrite HP0s4) in "H6".
    iEval (rewrite HP0s5) in "H7". iEval (rewrite HP0s6) in "H8".
    iEval (rewrite HP0s7) in "H9".
    iAssert (pd_frame (m !!! Regidx csp_rs1) (m !!! Regidx Rra) (m !!! Regidx Rs0)
               (m !!! Regidx Rs1) (m !!! Regidx Rs2) (m !!! Regidx Rs3)
               (m !!! Regidx Rs4) (m !!! Regidx Rs5) (m !!! Regidx Rs6)
               (m !!! Regidx Rs7))
      with "[H1 H2 H3 H4 H5 H6 H7 H8 H9 F10]" as "Hpdf".
    { rewrite /pd_frame. iFrame "H1 H2 H3 H4 H5 H6 H7 H8 H9". iExact "F10". }
    assert (Hp14 : add_vec_int (mword_of_int (PD + 0x12) : mword 64) 2 = mword_of_int (PD + 0x14)) by pcstep.
    iEval (rewrite Hp14) in "Hpc".
    (* ---- +0x14 c.addi4spn s0,sp,80 : s0 := the ENTRY sp ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (PD + 0x14)) (Cregidx (mword_of_int 0))
              (mword_of_int 20 : mword 8) Rs0 P0 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (P1 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (P0 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> P0).
    assert (HP1s0 : P1 !!! Regidx Rs0 = m !!! Regidx csp_rs1).
    { rewrite /P1 upd_eq HP0sp. apply pd_stk_fp_80. }
    assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /P1 upd_ne; [exact HP0sp | reg_neq]).
    assert (Hp16 : add_vec_int (mword_of_int (PD + 0x14) : mword 64) 2 = mword_of_int (PD + 0x16)) by pcstep.
    iEval (rewrite Hp16) in "Hpc".
    (* ---- +0x16 auipc a0,0x5 ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PD + 0x16)) Ra0 (mword_of_int 5 : mword 20)
              P1 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (P2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (PD + 0x16) : mword 64)
                     (auipc_off (mword_of_int 5 : mword 20)))]> P1).
    assert (Hp1a : add_vec_int (mword_of_int (PD + 0x16) : mword 64) 4 = mword_of_int (PD + 0x1a)) by pcstep.
    iEval (rewrite Hp1a) in "Hpc".
    (* ---- +0x1a addi a0,a0,-672 : a0 := "\n" ---- *)
    assert (Hrg1a : rget (CID := CID12) P2 Ra0 = P2 !!! Regidx Ra0) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (PD + 0x1a)) Ra0 Ra0 (mword_of_int 3384 : mword 12)
              P2 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    iEval (rewrite Hrg1a) in "Hcg".
    set (P3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (P2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 3384 : mword 12)))]> P2).
    assert (Hp1e : add_vec_int (mword_of_int (PD + 0x1a) : mword 64) 4 = mword_of_int (PD + 0x1e)) by pcstep.
    iEval (rewrite Hp1e) in "Hpc".
    (* ---- hand over ---- *)
    assert (HP3a0 : P3 !!! Regidx Ra0 = (mword_of_int pd_nl_a : mword 64)).
    { rewrite /P3 upd_eq /P2 upd_eq. unfold pd_nl_a. apply bv_eq; vm_compute; reflexivity. }
    assert (HP3s0 : P3 !!! Regidx Rs0 = m !!! Regidx csp_rs1).
    { rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq]. exact HP1s0. }
    assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10).
    { rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq]. exact HP1sp. }
    iSpecialize ("Hcont" $! CID13 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P3 with "[%] Hcg Hpdf Hpc").
    rewrite /pd_regs_pro /pdR.
    change (Regidx (mword_of_int 2 : mword 5)) with (Regidx csp_rs1).
    split_and!.
    - exact HP3sp.
    - exact HP3s0.
    - exact HP3a0.
    - intros r N2 N8 N10.
      assert (N2' : r <> csp_rs1)
        by (intro He; apply N2; rewrite He; apply bv_eq; vm_compute; reflexivity).
      rewrite /P3 upd_ne; [| reg_ne_side].
      rewrite /P2 upd_ne; [| reg_ne_side].
      rewrite /P1 upd_ne; [| reg_ne_side].
      rewrite /P0 upd_ne; [| reg_ne_side].
      reflexivity.
  Qed.

  (* ================================================================== *)
  (* +0x22 .. +0x54 -- the seven hoisted constants and the c.j into the  *)
  (* loop head.  Writes s1..s7 and nothing else.                        *)
  (* ================================================================== *)
  Lemma wp_pd_consts `{GEN : GenId} `{CID0 : CpuId}
      (M : regfile) (K' : nat) (b : bool) (p : mword 64) :
    sie_cap_gpr M K' b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.procdump + 0x22)) -∗
    wp_next (CID0 := CID0) b p (fun (CIDq : CpuId) =>
      ∀ (M' : regfile),
        ⌜ pd_regs_loop M' (M !!! pdR 2) 0 /\ pd_regs_hi M M' ⌝ -∗
        sie_cap_gpr M' K' b p -∗
        pc_is (mword_of_int (KernelSyms.procdump + 0x6e)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    rewrite /pdR.
    change (Regidx (mword_of_int 2 : mword 5)) with (Regidx csp_rs1).
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (pdi_22 with "Htext") as "Hi22".
    iPoseProof (pdi_26 with "Htext") as "Hi26".
    iPoseProof (pdi_2a with "Htext") as "Hi2a".
    iPoseProof (pdi_2e with "Htext") as "Hi2e".
    iPoseProof (pdi_32 with "Htext") as "Hi32".
    iPoseProof (pdi_34 with "Htext") as "Hi34".
    iPoseProof (pdi_38 with "Htext") as "Hi38".
    iPoseProof (pdi_3c with "Htext") as "Hi3c".
    iPoseProof (pdi_40 with "Htext") as "Hi40".
    iPoseProof (pdi_44 with "Htext") as "Hi44".
    iPoseProof (pdi_48 with "Htext") as "Hi48".
    iPoseProof (pdi_4c with "Htext") as "Hi4c".
    iPoseProof (pdi_50 with "Htext") as "Hi50".
    iPoseProof (pdi_54 with "Htext") as "Hi54".
    (* ---- +0x22 auipc s1,0x10 ; +0x26 addi s1,s1,1452 : s1 := &proc[0].name *)
    iApply (wp_auipc_s_sconf (mword_of_int (PD + 0x22)) Rs1 (mword_of_int 16 : mword 20)
              M K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (Q1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (PD + 0x22) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> M).
    assert (Hp26 : add_vec_int (mword_of_int (PD + 0x22) : mword 64) 4 = mword_of_int (PD + 0x26)) by pcstep.
    iEval (rewrite Hp26) in "Hpc".
    assert (Hrg26 : rget (CID := CID1) Q1 Rs1 = Q1 !!! Regidx Rs1) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (PD + 0x26)) Rs1 Rs1 (mword_of_int 1556 : mword 12)
              Q1 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc". iEval (rewrite Hrg26) in "Hcg".
    set (Q2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (Q1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 1556 : mword 12)))]> Q1).
    assert (HQ2s1 : Q2 !!! Regidx Rs1 = pd_cur 0).
    { rewrite /Q2 upd_eq /Q1 upd_eq.
      unfold pd_cur, acur, pd_base, pd_name_off, proc_size.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp2a : add_vec_int (mword_of_int (PD + 0x26) : mword 64) 4 = mword_of_int (PD + 0x2a)) by pcstep.
    iEval (rewrite Hp2a) in "Hpc".
    (* ---- +0x2a auipc s2,0x16 ; +0x2e addi s2,s2,-92 : the end sentinel ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PD + 0x2a)) Rs2 (mword_of_int 22 : mword 20)
              Q2 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [-]").
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (Q3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (mword_of_int (PD + 0x2a) : mword 64)
                     (auipc_off (mword_of_int 22 : mword 20)))]> Q2).
    assert (Hp2e : add_vec_int (mword_of_int (PD + 0x2a) : mword 64) 4 = mword_of_int (PD + 0x2e)) by pcstep.
    iEval (rewrite Hp2e) in "Hpc".
    assert (Hrg2e : rget (CID := CID3) Q3 Rs2 = Q3 !!! Regidx Rs2) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (PD + 0x2e)) Rs2 Rs2 (mword_of_int 12 : mword 12)
              Q3 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [-]").
    iIntros (CID4 Hs4) "Hcg Hpc". iEval (rewrite Hrg2e) in "Hcg".
    set (Q4 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (Q3 !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 12 : mword 12)))]> Q3).
    assert (HQ4s2 : Q4 !!! Regidx Rs2 = pd_cur NPROC).
    { rewrite /Q4 upd_eq /Q3 upd_eq.
      unfold pd_cur, acur, pd_base, pd_name_off, proc_size, NPROC.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp32 : add_vec_int (mword_of_int (PD + 0x2e) : mword 64) 4 = mword_of_int (PD + 0x32)) by pcstep.
    iEval (rewrite Hp32) in "Hpc".
    (* ---- +0x32 c.li s6,5 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (PD + 0x32)) Rs6 (mword_of_int 5 : mword 6)
              (mword_of_int 5 : mword 64) Q4 K' b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi32 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (Q5 := <[Regidx Rs6 := regval_into_reg (mword_of_int 5 : mword 64)]> Q4).
    assert (Hp34 : add_vec_int (mword_of_int (PD + 0x32) : mword 64) 2 = mword_of_int (PD + 0x34)) by pcstep.
    iEval (rewrite Hp34) in "Hpc".
    (* ---- +0x34 auipc s3,0x5 ; +0x38 addi s3,s3,-318 : s3 := "???" ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PD + 0x34)) Rs3 (mword_of_int 5 : mword 20)
              Q5 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (Q6 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (mword_of_int (PD + 0x34) : mword 64)
                     (auipc_off (mword_of_int 5 : mword 20)))]> Q5).
    assert (Hp38 : add_vec_int (mword_of_int (PD + 0x34) : mword 64) 4 = mword_of_int (PD + 0x38)) by pcstep.
    iEval (rewrite Hp38) in "Hpc".
    assert (Hrg38 : rget (CID := CID6) Q6 Rs3 = Q6 !!! Regidx Rs3) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (PD + 0x38)) Rs3 Rs3 (mword_of_int 3778 : mword 12)
              Q6 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38 [-]").
    iIntros (CID7 Hs7) "Hcg Hpc". iEval (rewrite Hrg38) in "Hcg".
    set (Q7 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (Q6 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 3778 : mword 12)))]> Q6).
    assert (HQ7s3 : Q7 !!! Regidx Rs3 = (mword_of_int pd_qqq_a : mword 64)).
    { rewrite /Q7 upd_eq /Q6 upd_eq. unfold pd_qqq_a. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp3c : add_vec_int (mword_of_int (PD + 0x38) : mword 64) 4 = mword_of_int (PD + 0x3c)) by pcstep.
    iEval (rewrite Hp3c) in "Hpc".
    (* ---- +0x3c auipc s5,0x5 ; +0x40 addi s5,s5,-318 : s5 := "%d %s %s" ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PD + 0x3c)) Rs5 (mword_of_int 5 : mword 20)
              Q7 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (Q8 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (mword_of_int (PD + 0x3c) : mword 64)
                     (auipc_off (mword_of_int 5 : mword 20)))]> Q7).
    assert (Hp40 : add_vec_int (mword_of_int (PD + 0x3c) : mword 64) 4 = mword_of_int (PD + 0x40)) by pcstep.
    iEval (rewrite Hp40) in "Hpc".
    assert (Hrg40 : rget (CID := CID8) Q8 Rs5 = Q8 !!! Regidx Rs5) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (PD + 0x40)) Rs5 Rs5 (mword_of_int 3778 : mword 12)
              Q8 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc". iEval (rewrite Hrg40) in "Hcg".
    set (Q9 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (Q8 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 3778 : mword 12)))]> Q8).
    assert (HQ9s5 : Q9 !!! Regidx Rs5 = (mword_of_int pd_fmt_a : mword 64)).
    { rewrite /Q9 upd_eq /Q8 upd_eq. unfold pd_fmt_a. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp44 : add_vec_int (mword_of_int (PD + 0x40) : mword 64) 4 = mword_of_int (PD + 0x44)) by pcstep.
    iEval (rewrite Hp44) in "Hpc".
    (* ---- +0x44 auipc s4,0x5 ; +0x48 addi s4,s4,-718 : s4 := "\n" ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PD + 0x44)) Rs4 (mword_of_int 5 : mword 20)
              Q9 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (Q10 := <[Regidx Rs4 := regval_into_reg
                   (add_vec (mword_of_int (PD + 0x44) : mword 64)
                      (auipc_off (mword_of_int 5 : mword 20)))]> Q9).
    assert (Hp48 : add_vec_int (mword_of_int (PD + 0x44) : mword 64) 4 = mword_of_int (PD + 0x48)) by pcstep.
    iEval (rewrite Hp48) in "Hpc".
    assert (Hrg48 : rget (CID := CID10) Q10 Rs4 = Q10 !!! Regidx Rs4) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (PD + 0x48)) Rs4 Rs4 (mword_of_int 3338 : mword 12)
              Q10 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc". iEval (rewrite Hrg48) in "Hcg".
    set (Q11 := <[Regidx Rs4 := regval_into_reg
                   (add_vec (Q10 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 3338 : mword 12)))]> Q10).
    assert (HQ11s4 : Q11 !!! Regidx Rs4 = (mword_of_int pd_nl_a : mword 64)).
    { rewrite /Q11 upd_eq /Q10 upd_eq. unfold pd_nl_a. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp4c : add_vec_int (mword_of_int (PD + 0x48) : mword 64) 4 = mword_of_int (PD + 0x4c)) by pcstep.
    iEval (rewrite Hp4c) in "Hpc".
    (* ---- +0x4c auipc s7,0x5 ; +0x50 addi s7,s7,978 : s7 := [states] ---- *)
    iApply (wp_auipc_s_sconf (mword_of_int (PD + 0x4c)) Rs7 (mword_of_int 5 : mword 20)
              Q11 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (Q12 := <[Regidx Rs7 := regval_into_reg
                   (add_vec (mword_of_int (PD + 0x4c) : mword 64)
                      (auipc_off (mword_of_int 5 : mword 20)))]> Q11).
    assert (Hp50 : add_vec_int (mword_of_int (PD + 0x4c) : mword 64) 4 = mword_of_int (PD + 0x50)) by pcstep.
    iEval (rewrite Hp50) in "Hpc".
    assert (Hrg50 : rget (CID := CID12) Q12 Rs7 = Q12 !!! Regidx Rs7) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (PD + 0x50)) Rs7 Rs7 (mword_of_int 978 : mword 12)
              Q12 K' b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50 [-]").
    iIntros (CID13 Hs13) "Hcg Hpc". iEval (rewrite Hrg50) in "Hcg".
    set (Q13 := <[Regidx Rs7 := regval_into_reg
                   (add_vec (Q12 !!! Regidx Rs7) (sign_extend' 64 (mword_of_int 978 : mword 12)))]> Q12).
    assert (HQ13s7 : Q13 !!! Regidx Rs7 = (mword_of_int pd_states_a : mword 64)).
    { rewrite /Q13 upd_eq /Q12 upd_eq. unfold pd_states_a, KernelSyms.states_0.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp54 : add_vec_int (mword_of_int (PD + 0x50) : mword 64) 4 = mword_of_int (PD + 0x54)) by pcstep.
    iEval (rewrite Hp54) in "Hpc".
    (* ---- +0x54 c.j +0x6e ---- *)
    iApply (wp_cj_s_sconf (mword_of_int (PD + 0x54))
              (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0")))
              Q13 K' b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi54 [-]").
    iIntros (CID14 Hs14). iNext. iIntros "Hcg Hpc".
    assert (Hp6e : add_vec (mword_of_int (PD + 0x54) : mword 64)
                     (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0"))))
                   = mword_of_int (PD + 0x6e)) by pcstep.
    iEval (rewrite Hp6e) in "Hpc".
    (* ---- hand over ---- *)
    iSpecialize ("Hcont" $! CID14 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Q13 with "[%] Hcg Hpc").
    rewrite /pd_regs_loop /pd_regs_hi /pdR.
    change (Regidx (mword_of_int 2 : mword 5)) with (Regidx csp_rs1).
    split; [split_and! | split_and!].
    - peel_reg.
    - rewrite -HQ2s1. peel_reg.
    - rewrite -HQ4s2. peel_reg.
    - rewrite -HQ7s3. peel_reg.
    - rewrite -HQ11s4. peel_reg.
    - rewrite -HQ9s5. peel_reg.
    - rewrite /Q13 upd_ne; [| reg_neq]. rewrite /Q12 upd_ne; [| reg_neq].
      rewrite /Q11 upd_ne; [| reg_neq]. rewrite /Q10 upd_ne; [| reg_neq].
      rewrite /Q9 upd_ne; [| reg_neq]. rewrite /Q8 upd_ne; [| reg_neq].
      rewrite /Q7 upd_ne; [| reg_neq]. rewrite /Q6 upd_ne; [| reg_neq].
      rewrite /Q5. apply upd_eq.
    - exact HQ13s7.
    - peel_reg.
    - peel_reg.
    - peel_reg.
    - peel_reg.
  Qed.

  (* ================================================================== *)
  (* +0x8e .. +0xa2 -- nine c.ldsp restores, the pop, and the ret.       *)
  (* ================================================================== *)
  Lemma wp_pd_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (m Mx : regfile) (K : nat) (b : bool) (p : mword 64) :
    (10 <= K)%nat ->
    Mx !!! pdR 2 = pa_stk (m !!! pdR 2 : mword 64) 10 ->
    pd_regs_hi m Mx ->
    sie_cap_gpr Mx (K - 10) b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.procdump + 0x8e)) -∗
    pd_frame (m !!! pdR 2) (m !!! pdR 1) (m !!! pdR 8) (m !!! pdR 9)
             (m !!! pdR 18) (m !!! pdR 19) (m !!! pdR 20) (m !!! pdR 21)
             (m !!! pdR 22) (m !!! pdR 23) -∗
    wp_next (CID0 := CID0) b p (fun (CIDq : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved m mf /\ mf !!! pdR 1 = (m !!! pdR 1 : mword 64) ⌝ -∗
        sie_cap_gpr mf K b p -∗
        pc_is (ret_pc (m !!! pdR 1 : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hxsp0 Hhi.
    assert (Hxsp : Mx !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10)
      by exact Hxsp0.
    assert (Hh24 : Mx !!! Regidx (mword_of_int 24 : mword 5)
                   = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by exact (proj1 Hhi).
    assert (Hh25 : Mx !!! Regidx (mword_of_int 25 : mword 5)
                   = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by exact (proj1 (proj2 Hhi)).
    assert (Hh26 : Mx !!! Regidx (mword_of_int 26 : mword 5)
                   = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by exact (proj1 (proj2 (proj2 Hhi))).
    assert (Hh27 : Mx !!! Regidx (mword_of_int 27 : mword 5)
                   = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by exact (proj2 (proj2 (proj2 Hhi))).
    rewrite /pdR.
    change (Regidx (mword_of_int 2 : mword 5)) with (Regidx csp_rs1).
    iIntros "Hcg #Htext Hpc Hpdf".
    rewrite /pd_frame.
    iDestruct "Hpdf" as "(Hc72 & Hc64 & Hc56 & Hc48 & Hc40 & Hc32 & Hc24 & Hc16 & Hc08 & Hc00)".
    iIntros "Hcont".
    iPoseProof (pdi_8e with "Htext") as "Hi8e".
    iPoseProof (pdi_90 with "Htext") as "Hi90".
    iPoseProof (pdi_92 with "Htext") as "Hi92".
    iPoseProof (pdi_94 with "Htext") as "Hi94".
    iPoseProof (pdi_96 with "Htext") as "Hi96".
    iPoseProof (pdi_98 with "Htext") as "Hi98".
    iPoseProof (pdi_9a with "Htext") as "Hi9a".
    iPoseProof (pdi_9c with "Htext") as "Hi9c".
    iPoseProof (pdi_9e with "Htext") as "Hi9e".
    iPoseProof (pdi_a0 with "Htext") as "Hia0".
    iPoseProof (pdi_a2 with "Htext") as "Hia2".
    (* the nine slot addresses, off the frame base the c.ldsp use *)
    assert (Hb1 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 3).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 5).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 7).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 8).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec (pa_stk (m !!! Regidx csp_rs1) 10)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 9).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- +0x8e ld ra,72(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x8e)) (mword_of_int 9 : mword 6) Rra
              Mx (K - 10)%nat (m !!! Regidx Rra) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8e [Hc72] [-]").
    { iEval (rewrite Hxsp Hb1). iExact "Hc72". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hc72". iEval (rewrite Hxsp Hb1) in "Hc72".
    set (E1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> Mx).
    assert (HspE1 : E1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E1 upd_ne; [exact Hxsp | reg_neq]).
    assert (Hq90 : add_vec_int (mword_of_int (PD + 0x8e) : mword 64) 2 = mword_of_int (PD + 0x90)) by pcstep.
    iEval (rewrite Hq90) in "Hpc".
    (* ---- +0x90 ld s0,64(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x90)) (mword_of_int 8 : mword 6) Rs0
              E1 (K - 10)%nat (m !!! Regidx Rs0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi90 [Hc64] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc64". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hc64". iEval (rewrite HspE1 Hb2) in "Hc64".
    set (E2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E1).
    assert (HspE2 : E2 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E2 upd_ne; [exact HspE1 | reg_neq]).
    assert (Hq92 : add_vec_int (mword_of_int (PD + 0x90) : mword 64) 2 = mword_of_int (PD + 0x92)) by pcstep.
    iEval (rewrite Hq92) in "Hpc".
    (* ---- +0x92 ld s1,56(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x92)) (mword_of_int 7 : mword 6) Rs1
              E2 (K - 10)%nat (m !!! Regidx Rs1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi92 [Hc56] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc56". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hc56". iEval (rewrite HspE2 Hb3) in "Hc56".
    set (E3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> E2).
    assert (HspE3 : E3 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E3 upd_ne; [exact HspE2 | reg_neq]).
    assert (Hq94 : add_vec_int (mword_of_int (PD + 0x92) : mword 64) 2 = mword_of_int (PD + 0x94)) by pcstep.
    iEval (rewrite Hq94) in "Hpc".
    (* ---- +0x94 ld s2,48(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x94)) (mword_of_int 6 : mword 6) Rs2
              E3 (K - 10)%nat (m !!! Regidx Rs2) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi94 [Hc48] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc48". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hc48". iEval (rewrite HspE3 Hb4) in "Hc48".
    set (E4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> E3).
    assert (HspE4 : E4 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E4 upd_ne; [exact HspE3 | reg_neq]).
    assert (Hq96 : add_vec_int (mword_of_int (PD + 0x94) : mword 64) 2 = mword_of_int (PD + 0x96)) by pcstep.
    iEval (rewrite Hq96) in "Hpc".
    (* ---- +0x96 ld s3,40(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x96)) (mword_of_int 5 : mword 6) Rs3
              E4 (K - 10)%nat (m !!! Regidx Rs3) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi96 [Hc40] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc40". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hc40". iEval (rewrite HspE4 Hb5) in "Hc40".
    set (E5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> E4).
    assert (HspE5 : E5 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E5 upd_ne; [exact HspE4 | reg_neq]).
    assert (Hq98 : add_vec_int (mword_of_int (PD + 0x96) : mword 64) 2 = mword_of_int (PD + 0x98)) by pcstep.
    iEval (rewrite Hq98) in "Hpc".
    (* ---- +0x98 ld s4,32(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x98)) (mword_of_int 4 : mword 6) Rs4
              E5 (K - 10)%nat (m !!! Regidx Rs4) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi98 [Hc32] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc32". }
    iIntros (CIDe6 Hse6) "Hcg Hpc Hc32". iEval (rewrite HspE5 Hb6) in "Hc32".
    set (E6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> E5).
    assert (HspE6 : E6 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E6 upd_ne; [exact HspE5 | reg_neq]).
    assert (Hq9a : add_vec_int (mword_of_int (PD + 0x98) : mword 64) 2 = mword_of_int (PD + 0x9a)) by pcstep.
    iEval (rewrite Hq9a) in "Hpc".
    (* ---- +0x9a ld s5,24(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x9a)) (mword_of_int 3 : mword 6) Rs5
              E6 (K - 10)%nat (m !!! Regidx Rs5) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9a [Hc24] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc24". }
    iIntros (CIDe7 Hse7) "Hcg Hpc Hc24". iEval (rewrite HspE6 Hb7) in "Hc24".
    set (E7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> E6).
    assert (HspE7 : E7 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E7 upd_ne; [exact HspE6 | reg_neq]).
    assert (Hq9c : add_vec_int (mword_of_int (PD + 0x9a) : mword 64) 2 = mword_of_int (PD + 0x9c)) by pcstep.
    iEval (rewrite Hq9c) in "Hpc".
    (* ---- +0x9c ld s6,16(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x9c)) (mword_of_int 2 : mword 6) Rs6
              E7 (K - 10)%nat (m !!! Regidx Rs6) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9c [Hc16] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc16". }
    iIntros (CIDe8 Hse8) "Hcg Hpc Hc16". iEval (rewrite HspE7 Hb8) in "Hc16".
    set (E8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> E7).
    assert (HspE8 : E8 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E8 upd_ne; [exact HspE7 | reg_neq]).
    assert (Hq9e : add_vec_int (mword_of_int (PD + 0x9c) : mword 64) 2 = mword_of_int (PD + 0x9e)) by pcstep.
    iEval (rewrite Hq9e) in "Hpc".
    (* ---- +0x9e ld s7,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf (mword_of_int (PD + 0x9e)) (mword_of_int 1 : mword 6) Rs7
              E8 (K - 10)%nat (m !!! Regidx Rs7) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9e [Hc08] [-]").
    { iEval (rewrite HspE8 Hb9). iExact "Hc08". }
    iIntros (CIDe9 Hse9) "Hcg Hpc Hc08". iEval (rewrite HspE8 Hb9) in "Hc08".
    set (E9 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> E8).
    assert (HspE9 : E9 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 10)
      by (rewrite /E9 upd_ne; [exact HspE8 | reg_neq]).
    assert (Hqa0 : add_vec_int (mword_of_int (PD + 0x9e) : mword 64) 2 = mword_of_int (PD + 0xa0)) by pcstep.
    iEval (rewrite Hqa0) in "Hpc".
    (* ---- +0xa0 c.addi16sp sp,+80 -- the frame pop ---- *)
    assert (Hwv : add_vec (E9 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite HspE9; apply pd_stk_pop_80).
    assert (Hpop : E9 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E9 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10)
      by (rewrite Hwv; exact HspE9).
    iAssert (stack_own (m !!! Regidx csp_rs1 : mword 64) 10)
      with "[Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc72". { iExists (m !!! Regidx Rra). iExact "Hc72". }
      iSplitL "Hc64". { iExists (m !!! Regidx Rs0). iExact "Hc64". }
      iSplitL "Hc56". { iExists (m !!! Regidx Rs1). iExact "Hc56". }
      iSplitL "Hc48". { iExists (m !!! Regidx Rs2). iExact "Hc48". }
      iSplitL "Hc40". { iExists (m !!! Regidx Rs3). iExact "Hc40". }
      iSplitL "Hc32". { iExists (m !!! Regidx Rs4). iExact "Hc32". }
      iSplitL "Hc24". { iExists (m !!! Regidx Rs5). iExact "Hc24". }
      iSplitL "Hc16". { iExists (m !!! Regidx Rs6). iExact "Hc16". }
      iSplitL "Hc08". { iExists (m !!! Regidx Rs7). iExact "Hc08". }
      iSplitL "Hc00". { iExact "Hc00". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (PD + 0xa0)) (mword_of_int 5 : mword 6)
              E9 (K - 10)%nat 10%nat b Hpop with "Hcg Hpc Hia0 Hframe [-]").
    iIntros (CIDe10 Hse10) "Hcg Hpc".
    set (E10 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (E9 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9).
    iEval (rewrite (pd_Kpop K HK)) in "Hcg".
    assert (Hqa2 : add_vec_int (mword_of_int (PD + 0xa0) : mword 64) 2 = mword_of_int (PD + 0xa2)) by pcstep.
    iEval (rewrite Hqa2) in "Hpc".
    (* ---- +0xa2 c.ret ---- *)
    assert (HE10ra : E10 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)) by peel_reg.
    assert (Hrt : ret_pc (E10 !!! Regidx Rra) = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HE10ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (PD + 0xa2)) Rra E10 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hia2 [-]").
    iIntros (CIDe11 Hse11) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CIDe11 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E10 with "[%] Hcg Hpc").
    split; [| exact HE10ra].
    unfold callee_saved.
    split_and!.
    - rewrite /E10 upd_eq. exact Hwv.
    - peel_reg.
    - peel_reg.
    - peel_reg.
    - peel_reg.
    - peel_reg.
    - peel_reg.
    - peel_reg.
    - peel_reg.
    - peel_step. exact Hh24.
    - peel_step. exact Hh25.
    - peel_step. exact Hh26.
    - peel_step. exact Hh27.
  Qed.

End ProofProcdumpParts.
