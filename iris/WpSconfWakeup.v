(* WpSconfWakeup.v -- wakeup over the SIE-agnostic sconf world (kalloc cone,
   stage 8).  Foundation for the sconf mirror of [wp_wakeup] (WpWakeup.v): a
   loop over the proc[] table that, per proc, acquires the proc lock, wakes it
   if SLEEPING on the given chan, and releases -- threading the counting token
   [intr_count] net-zero across each acquire/release pair.

   THIS FILE currently provides only [wp_myproc_sconf], the sconf-flavoured
   myproc axiom wakeup relies on (the loop skips the current proc).  The full
   loop/prologue/epilogue port is the remaining work (see CLAUDE.md). *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SRegime SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpGpr.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved StackOwn.
Require Import KptTree.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpWakeup.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ======================================================================= *)
(* myproc(), sconf-flavoured.  Like the smode [wp_myproc] (WpWakeup.v), the  *)
(* only fact wakeup needs is that a0 comes back a genuine proc[] entry and   *)
(* the callee-saved registers are preserved.  myproc internally push_off/    *)
(* pop_offs (net-zero) and manages its own stack frame from the lent deep    *)
(* custody, so it threads [sconf] + hart_state + [sie_cap] + [intr_count n]  *)
(* (unchanged) + [tlb_inv_pt] + a deep-K stack slice, exactly the resources  *)
(* the sconf acquire/release thread.                                         *)
(* ======================================================================= *)
Axiom wp_myproc_sconf :
  forall {Σ : gFunctors} {HR : riscvGS Σ} {HL : lockG Σ} {HS : sieG Σ} {CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (m : gmap regidx (mword 64)) (n K : nat),
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt :=
      update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                        (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (10 <= K)%nat ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    intr_count γ root_ppn n -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.myproc) -∗ gpr_file m -∗
    stack_own (pa_stk sp0 kv_frame_slots) K -∗
    (∀ (j : nat) (mret : gmap regidx (mword 64)),
       ⌜(j < NPROC)%nat⌝ -∗
       ⌜mret !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j⌝ -∗
       ⌜callee_saved m mret⌝ -∗
       sconf γ -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       sie_cap γ root_ppn mret -∗
       intr_count γ root_ppn n -∗
       tlb_inv_pt root_ppn -∗
       pc_is ret_tgt -∗ gpr_file mret -∗
       stack_own (pa_stk sp0 kv_frame_slots) K -∗
       WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.

Section WpSconfWakeupEpi.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation WK := KernelSyms.wakeup.

  (* wakeup's epilogue over sconf: restore ra/s0/s1..s5 from the 8-slot frame
     (7 c.ldsp), pop it (c.addi16sp sp,+64 via sie_cap_move_up 8), c.ret.
     Frame cells at [wk_fcell spF u] = [pa_stk sp0 (8-u)] (sp0 = spF+64); the
     deep-(K-8) custody recombines with the move_up output into deep-K. *)
  Lemma wp_wakeup_epilogue_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (M : gmap regidx (mword 64)) (K : nat)
      (vra vs0 vs1 vs2 vs3 vs4 vs5 vpad : mword 64) :
    let spF := M !!! Regidx csp_rs1 in
    let sp0 := add_vec spF (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) in
    let rettgt := update_vec_dec (add_vec vra (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (8 <= K)%nat ->
    (forall r : regidx, r ∈ dom M) ->
    eq_vec (access_vec_dec rettgt 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn M -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (WK + 0x58)) -∗ gpr_file M -∗
    stack_own (pa_stk spF kv_frame_slots) (K - 8) -∗
    wk_fcell spF 7 ↦₈ vra -∗ wk_fcell spF 6 ↦₈ vs0 -∗ wk_fcell spF 5 ↦₈ vs1 -∗
    wk_fcell spF 4 ↦₈ vs2 -∗ wk_fcell spF 3 ↦₈ vs3 -∗ wk_fcell spF 2 ↦₈ vs4 -∗
    wk_fcell spF 1 ↦₈ vs5 -∗ wk_fcell spF 0 ↦₈ vpad -∗
    ( ∀ Mf : gmap regidx (mword 64),
        ⌜ Mf !!! Regidx (mword_of_int 1)  = vra
        /\ Mf !!! Regidx (mword_of_int 8)  = vs0
        /\ Mf !!! Regidx (mword_of_int 9)  = vs1
        /\ Mf !!! Regidx (mword_of_int 18) = vs2
        /\ Mf !!! Regidx (mword_of_int 19) = vs3
        /\ Mf !!! Regidx (mword_of_int 20) = vs4
        /\ Mf !!! Regidx (mword_of_int 21) = vs5
        /\ Mf !!! Regidx csp_rs1 = sp0
        /\ Mf !!! Regidx (mword_of_int 4)  = M !!! Regidx (mword_of_int 4)
        /\ Mf !!! Regidx (mword_of_int 22) = M !!! Regidx (mword_of_int 22)
        /\ Mf !!! Regidx (mword_of_int 23) = M !!! Regidx (mword_of_int 23)
        /\ Mf !!! Regidx (mword_of_int 24) = M !!! Regidx (mword_of_int 24)
        /\ Mf !!! Regidx (mword_of_int 25) = M !!! Regidx (mword_of_int 25)
        /\ Mf !!! Regidx (mword_of_int 26) = M !!! Regidx (mword_of_int 26)
        /\ Mf !!! Regidx (mword_of_int 27) = M !!! Regidx (mword_of_int 27)
        /\ (forall r : regidx, r ∈ dom Mf) ⌝ -∗
        sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        sie_cap γ root_ppn Mf -∗ tlb_inv_pt root_ppn -∗
        pc_is rettgt -∗ gpr_file Mf -∗
        stack_own (pa_stk sp0 kv_frame_slots) K -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros spF sp0 rettgt HK8 Hdom Halign.
    iIntros "Hsc Hhs Hcap Htlbinv #Htext Hpc Hfile Hdeep Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1 Hf0 Hcont".
    iPoseProof (wki_58 with "Htext") as "Hi58".
    iPoseProof (wki_5a with "Htext") as "Hi5a".
    iPoseProof (wki_5c with "Htext") as "Hi5c".
    iPoseProof (wki_5e with "Htext") as "Hi5e".
    iPoseProof (wki_60 with "Htext") as "Hi60".
    iPoseProof (wki_62 with "Htext") as "Hi62".
    iPoseProof (wki_64 with "Htext") as "Hi64".
    iPoseProof (wki_66 with "Htext") as "Hi66".
    iPoseProof (wki_68 with "Htext") as "Hi68".
    (* the 7 c.ldsp restore ra/s0/s1..s5; each cell is at wk_fcell spF u,
       matching the leaf's [add_vec (Ei!!!csp) ...] once Ei!!!csp = spF. *)
    assert (HspE0 : M !!! Regidx csp_rs1 = spF) by reflexivity.
    (* +0x58 c.ldsp ra,56(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x58)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5)
              M vra ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi58 [Hf7] [-]").
    { unfold wk_fcell. iExact "Hf7". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hf7".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg vra]> M).
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spF) by (rewrite /E1 lookup_total_insert_ne; [ exact HspE0 | vm_compute; discriminate ]).
    assert (Hpp5a : add_vec_int (mword_of_int (WK + 0x58) : mword 64) 2 = mword_of_int (WK + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* +0x5a c.ldsp s0,48(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5a)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              E1 vs0 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi5a [Hf6] [-]").
    { unfold wk_fcell. iEval (rewrite HspE1). iExact "Hf6". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hf6".
    iEval (rewrite HspE1) in "Hf6".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg vs0]> E1).
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spF) by (rewrite /E2 lookup_total_insert_ne; [ exact HspE1 | vm_compute; discriminate ]).
    assert (Hpp5c : add_vec_int (mword_of_int (WK + 0x5a) : mword 64) 2 = mword_of_int (WK + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* +0x5c c.ldsp s1,40(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5c)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              E2 vs1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi5c [Hf5] [-]").
    { unfold wk_fcell. iEval (rewrite HspE2). iExact "Hf5". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hf5".
    iEval (rewrite HspE2) in "Hf5".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg vs1]> E2).
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spF) by (rewrite /E3 lookup_total_insert_ne; [ exact HspE2 | vm_compute; discriminate ]).
    assert (Hpp5e : add_vec_int (mword_of_int (WK + 0x5c) : mword 64) 2 = mword_of_int (WK + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* +0x5e c.ldsp s2,32(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5e)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              E3 vs2 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi5e [Hf4] [-]").
    { unfold wk_fcell. iEval (rewrite HspE3). iExact "Hf4". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hf4".
    iEval (rewrite HspE3) in "Hf4".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg vs2]> E3).
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spF) by (rewrite /E4 lookup_total_insert_ne; [ exact HspE3 | vm_compute; discriminate ]).
    assert (Hpp60 : add_vec_int (mword_of_int (WK + 0x5e) : mword 64) 2 = mword_of_int (WK + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    (* +0x60 c.ldsp s3,24(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x60)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              E4 vs3 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi60 [Hf3] [-]").
    { unfold wk_fcell. iEval (rewrite HspE4). iExact "Hf3". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hf3".
    iEval (rewrite HspE4) in "Hf3".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg vs3]> E4).
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spF) by (rewrite /E5 lookup_total_insert_ne; [ exact HspE4 | vm_compute; discriminate ]).
    assert (Hpp62 : add_vec_int (mword_of_int (WK + 0x60) : mword 64) 2 = mword_of_int (WK + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    (* +0x62 c.ldsp s4,16(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x62)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              E5 vs4 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi62 [Hf2] [-]").
    { unfold wk_fcell. iEval (rewrite HspE5). iExact "Hf2". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hf2".
    iEval (rewrite HspE5) in "Hf2".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg vs4]> E5).
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spF) by (rewrite /E6 lookup_total_insert_ne; [ exact HspE5 | vm_compute; discriminate ]).
    assert (Hpp64 : add_vec_int (mword_of_int (WK + 0x62) : mword 64) 2 = mword_of_int (WK + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* +0x64 c.ldsp s5,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x64)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              E6 vs5 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi64 [Hf1] [-]").
    { unfold wk_fcell. iEval (rewrite HspE6). iExact "Hf1". }
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hf1".
    iEval (rewrite HspE6) in "Hf1".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg vs5]> E6).
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spF) by (rewrite /E7 lookup_total_insert_ne; [ exact HspE6 | vm_compute; discriminate ]).
    assert (Hpp66 : add_vec_int (mword_of_int (WK + 0x64) : mword 64) 2 = mword_of_int (WK + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    (* +0x66 c.addi16sp sp,+64 -- move_up 8 *)
    set (E8 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E7).
    assert (HE8csp : E8 !!! Regidx csp_rs1 = sp0)
      by (rewrite /E8 lookup_total_insert; rewrite HspE7; reflexivity).
    assert (Hup : E7 !!! Regidx csp_rs1 = pa_stk (E8 !!! Regidx csp_rs1) 8).
    { rewrite HspE7 HE8csp. symmetry. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      match goal with |- add_vec spF (mword_of_int ?z) = spF =>
        replace z with 0%Z by (vm_compute; reflexivity) end.
      change (add_vec spF (mword_of_int 0)) with (add_vec_int spF 0). apply RiscvExtras.avi0. }
    (* the 8 frame cells [wk_fcell spF 7..0] = [pa_stk sp0 1..8] *)
    assert (Hb7 : wk_fcell spF 7 = pa_stk sp0 1).
    { unfold wk_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : wk_fcell spF 6 = pa_stk sp0 2).
    { unfold wk_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : wk_fcell spF 5 = pa_stk sp0 3).
    { unfold wk_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : wk_fcell spF 4 = pa_stk sp0 4).
    { unfold wk_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : wk_fcell spF 3 = pa_stk sp0 5).
    { unfold wk_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : wk_fcell spF 2 = pa_stk sp0 6).
    { unfold wk_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : wk_fcell spF 1 = pa_stk sp0 7).
    { unfold wk_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb0 : wk_fcell spF 0 = pa_stk sp0 8).
    { unfold wk_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_caddi16sp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x66)) (mword_of_int 4 : mword 6) E7
              (stack_own (pa_stk sp0 kv_frame_slots) 8)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi66 [Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1 Hf0] [-]").
    { iIntros "Hcap".
      iAssert (stack_own (E8 !!! Regidx csp_rs1) 8) with "[Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1 Hf0]" as "Hframe".
      { rewrite HE8csp. rewrite stack_own_slots. cbn [seq].
        iSplitL "Hf7"; [iEval (rewrite -Hb7); iExists _; iExact "Hf7"|].
        iSplitL "Hf6"; [iEval (rewrite -Hb6); iExists _; iExact "Hf6"|].
        iSplitL "Hf5"; [iEval (rewrite -Hb5); iExists _; iExact "Hf5"|].
        iSplitL "Hf4"; [iEval (rewrite -Hb4); iExists _; iExact "Hf4"|].
        iSplitL "Hf3"; [iEval (rewrite -Hb3); iExists _; iExact "Hf3"|].
        iSplitL "Hf2"; [iEval (rewrite -Hb2); iExists _; iExact "Hf2"|].
        iSplitL "Hf1"; [iEval (rewrite -Hb1); iExists _; iExact "Hf1"|].
        iSplitL "Hf0"; [iEval (rewrite -Hb0); iExists _; iExact "Hf0"|].
        done. }
      iDestruct (sie_cap_move_up γ root_ppn E7 E8 8 Hup with "Hframe Hcap") as "[Hcap Hdeep8]".
      iEval (rewrite HE8csp) in "Hdeep8". iFrame "Hcap Hdeep8". }
    iIntros "Hhs Hsc Hcap Hdeep8 Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E7) with E8.
    assert (Hpp68 : add_vec_int (mword_of_int (WK + 0x66) : mword 64) 2 = mword_of_int (WK + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* recombine deep-8 with deep-(K-8) into deep-K *)
    assert (Hda : pa_stk (pa_stk sp0 kv_frame_slots) 8 = pa_stk spF kv_frame_slots).
    { unfold sp0, pa_stk, add_vec_int, kv_frame_slots. rewrite !add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hda) in "Hdeep".
    iDestruct (stack_own_split_2 (pa_stk sp0 kv_frame_slots) 8 K ltac:(lia) with "[$Hdeep8 $Hdeep]") as "Hdeep".
    (* +0x68 c.ret *)
    assert (HE8ra : E8 !!! Regidx (mword_of_int 1 : mword 5) = vra).
    { rewrite /E8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /E1 lookup_total_insert. reflexivity. }
    assert (Hral : eq_vec (access_vec_dec (update_vec_dec (add_vec (E8 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE8ra; exact Halign).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x68)) (mword_of_int 1 : mword 5) E8
              ltac:(vm_compute; discriminate) Hral
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi68 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    assert (Hretf : update_vec_dec (add_vec (E8 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = rettgt)
      by (rewrite HE8ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! E8 with "[%] Hsc Hhs Hcap Htlbinv Hpc Hfile Hdeep").
    (* the E8 register facts *)
    rewrite /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
    repeat split.
    - rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert; reflexivity.
    - rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert; reflexivity.
    - rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert; reflexivity.
    - rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert; reflexivity.
    - rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert; reflexivity.
    - rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert; reflexivity.
    - rewrite lookup_total_insert_ne; [| vm_compute; discriminate];
      rewrite lookup_total_insert; reflexivity.
    - rewrite lookup_total_insert. rewrite HspE7. reflexivity.
    - do 8 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
    - do 8 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
    - do 8 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
    - do 8 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
    - do 8 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
    - do 8 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
    - do 8 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]); reflexivity.
    - intro r. rewrite !dom_insert_L. repeat apply elem_of_union_r. exact (Hdom r).
  Qed.

End WpSconfWakeupEpi.
