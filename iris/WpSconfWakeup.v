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
Require Import SmodeCore.
Require Import InstrBytes KernelText WpAuipc.
Require Import RegFile.
Require Import WpGpr.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved StackOwn.
Require Import KptTree.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpWakeup.
Require Import SpecWakeup.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ======================================================================= *)
(* myproc(), sconf-flavoured.  Like the smode [wp_myproc] (WpWakeup.v), the  *)
(* only fact wakeup needs is that a0 comes back a genuine proc[] entry and   *)
(* the callee-saved registers are preserved.  myproc internally push_off/    *)
(* pop_offs (net-zero) and manages its own stack frame from the capability's *)
(* free stack, so it threads [sconf] + hart_state + [sie_cap _ _ _ K]        *)
(* (net-zero, same K out) + [intr_count n] (unchanged) + [tlb_inv_pt],       *)
(* exactly the resources the sconf acquire/release thread.                   *)
(* ======================================================================= *)
Module WakeupProof : WAKEUP.

Section WpSconfWakeupEpi.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation WK := KernelSyms.wakeup.

  (* wakeup's epilogue over sconf: restore ra/s0/s1..s5 from the 8-slot frame
     (7 c.ldsp), pop it (c.addi16sp sp,+64 via wp_caddi16sp_pop_s_sconf 8),
     c.ret.  Frame cells at [wk_fcell spF u] = [pa_stk sp0 (8-u)] (sp0 =
     spF+64); the pop feeds the frame back and lifts the count K-8 -> K. *)
  Lemma wp_wakeup_epilogue_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (M : regfile) (K : nat)
      (vra vs0 vs1 vs2 vs3 vs4 vs5 vpad : mword 64)
    : wp_wakeup_epilogue_sconf_body γ root_ppn Φ M K vra vs0 vs1 vs2 vs3 vs4 vs5 vpad.
  Proof.
    cbv beta delta [wp_wakeup_epilogue_sconf_body].
    intros spF sp0 rettgt HK8 Hdom Halign.
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1 Hf0 Hcont".
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
              M (K - 8)%nat vra ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi58 [Hf7] [-]").
    { unfold wk_fcell. iExact "Hf7". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hf7".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg vra]> M).
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spF) by (rewrite /E1 upd_ne; [ exact HspE0 | vm_compute; discriminate ]).
    assert (Hpp5a : add_vec_int (mword_of_int (WK + 0x58) : mword 64) 2 = mword_of_int (WK + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* +0x5a c.ldsp s0,48(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5a)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 8)%nat vs0 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5a [Hf6] [-]").
    { unfold wk_fcell. iEval (rewrite HspE1). iExact "Hf6". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hf6".
    iEval (rewrite HspE1) in "Hf6".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg vs0]> E1).
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spF) by (rewrite /E2 upd_ne; [ exact HspE1 | vm_compute; discriminate ]).
    assert (Hpp5c : add_vec_int (mword_of_int (WK + 0x5a) : mword 64) 2 = mword_of_int (WK + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* +0x5c c.ldsp s1,40(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5c)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 8)%nat vs1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5c [Hf5] [-]").
    { unfold wk_fcell. iEval (rewrite HspE2). iExact "Hf5". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hf5".
    iEval (rewrite HspE2) in "Hf5".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg vs1]> E2).
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spF) by (rewrite /E3 upd_ne; [ exact HspE2 | vm_compute; discriminate ]).
    assert (Hpp5e : add_vec_int (mword_of_int (WK + 0x5c) : mword 64) 2 = mword_of_int (WK + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* +0x5e c.ldsp s2,32(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x5e)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5)
              E3 (K - 8)%nat vs2 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5e [Hf4] [-]").
    { unfold wk_fcell. iEval (rewrite HspE3). iExact "Hf4". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hf4".
    iEval (rewrite HspE3) in "Hf4".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg vs2]> E3).
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spF) by (rewrite /E4 upd_ne; [ exact HspE3 | vm_compute; discriminate ]).
    assert (Hpp60 : add_vec_int (mword_of_int (WK + 0x5e) : mword 64) 2 = mword_of_int (WK + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    (* +0x60 c.ldsp s3,24(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x60)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5)
              E4 (K - 8)%nat vs3 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi60 [Hf3] [-]").
    { unfold wk_fcell. iEval (rewrite HspE4). iExact "Hf3". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hf3".
    iEval (rewrite HspE4) in "Hf3".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg vs3]> E4).
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spF) by (rewrite /E5 upd_ne; [ exact HspE4 | vm_compute; discriminate ]).
    assert (Hpp62 : add_vec_int (mword_of_int (WK + 0x60) : mword 64) 2 = mword_of_int (WK + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    (* +0x62 c.ldsp s4,16(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x62)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5)
              E5 (K - 8)%nat vs4 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi62 [Hf2] [-]").
    { unfold wk_fcell. iEval (rewrite HspE5). iExact "Hf2". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hf2".
    iEval (rewrite HspE5) in "Hf2".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg vs4]> E5).
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spF) by (rewrite /E6 upd_ne; [ exact HspE5 | vm_compute; discriminate ]).
    assert (Hpp64 : add_vec_int (mword_of_int (WK + 0x62) : mword 64) 2 = mword_of_int (WK + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* +0x64 c.ldsp s5,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x64)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5)
              E6 (K - 8)%nat vs5 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi64 [Hf1] [-]").
    { unfold wk_fcell. iEval (rewrite HspE6). iExact "Hf1". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hf1".
    iEval (rewrite HspE6) in "Hf1".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg vs5]> E6).
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spF) by (rewrite /E7 upd_ne; [ exact HspE6 | vm_compute; discriminate ]).
    assert (Hpp66 : add_vec_int (mword_of_int (WK + 0x64) : mword 64) 2 = mword_of_int (WK + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    (* +0x66 c.addi16sp sp,+64 -- pop the 8-slot frame *)
    set (E8 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E7).
    assert (Hwv : add_vec (E7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0)
      by (rewrite HspE7; reflexivity).
    assert (Hup : E7 !!! Regidx csp_rs1 = pa_stk (add_vec (E7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HspE7. symmetry. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
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
    iAssert (stack_own sp0 8) with "[Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1 Hf0]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hf7"; [iEval (rewrite -Hb7); iExists _; iExact "Hf7"|].
      iSplitL "Hf6"; [iEval (rewrite -Hb6); iExists _; iExact "Hf6"|].
      iSplitL "Hf5"; [iEval (rewrite -Hb5); iExists _; iExact "Hf5"|].
      iSplitL "Hf4"; [iEval (rewrite -Hb4); iExists _; iExact "Hf4"|].
      iSplitL "Hf3"; [iEval (rewrite -Hb3); iExists _; iExact "Hf3"|].
      iSplitL "Hf2"; [iEval (rewrite -Hb2); iExists _; iExact "Hf2"|].
      iSplitL "Hf1"; [iEval (rewrite -Hb1); iExists _; iExact "Hf1"|].
      iSplitL "Hf0"; [iEval (rewrite -Hb0); iExists _; iExact "Hf0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x66)) (mword_of_int 4 : mword 6)
              E7 (K - 8)%nat 8 Hup
              with "Hsc Hhs Hcg Htlbinv Hpc Hi66 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> E7) with E8.
    assert (HKfix : ((K - 8) + 8)%nat = K) by lia.
    iEval (rewrite HKfix) in "Hcg".
    assert (Hpp68 : add_vec_int (mword_of_int (WK + 0x66) : mword 64) 2 = mword_of_int (WK + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* +0x68 c.ret *)
    assert (HE8ra : E8 !!! Regidx (mword_of_int 1 : mword 5) = vra).
    { rewrite /E8 upd_ne; [| vm_compute; discriminate].
      rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq. reflexivity. }
    assert (Hral : eq_vec (access_vec_dec (update_vec_dec (add_vec (E8 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE8ra; exact Halign).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x68)) (mword_of_int 1 : mword 5) E8 K
              ltac:(vm_compute; discriminate) Hral
              with "Hsc Hhs Hcg Htlbinv Hpc Hi68 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hretf : update_vec_dec (add_vec (E8 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = rettgt)
      by (rewrite HE8ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! E8 with "[%] Hsc Hhs Hcg Htlbinv Hpc").
    (* the E8 register facts *)
    rewrite /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
    repeat split.
    all: intro r; apply rf_to_gmap_dom.
  Qed.

End WpSconfWakeupEpi.

Section WpSconfWakeupPro.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation WK := KernelSyms.wakeup.

  (* wakeup's prologue over sconf: c.addi16sp sp,-64 (wp_caddi16sp_push_s_sconf
     8: count K -> K-8, frame handed out),
     7 c.sdsp saves (ra/s0/s1..s5), c.addi4spn s0, then loop-register setup
     (s4:=chan(a0), s1:=&proc[0], s3:=2, s5:=3, s2:=&proc[64]) and c.j to the
     loop test at wakeup+0x38. *)
  Lemma wp_wakeup_prologue_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat)
    : wp_wakeup_prologue_sconf_body γ root_ppn Φ m K.
  Proof.
    cbv beta delta [wp_wakeup_prologue_sconf_body].
    intros sp0 spF HK8 Hdom.
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hcont".
    iPoseProof (wki_00 with "Htext") as "Hi00".
    iPoseProof (wki_02 with "Htext") as "Hi02".
    iPoseProof (wki_04 with "Htext") as "Hi04".
    iPoseProof (wki_06 with "Htext") as "Hi06".
    iPoseProof (wki_08 with "Htext") as "Hi08".
    iPoseProof (wki_0a with "Htext") as "Hi0a".
    iPoseProof (wki_0c with "Htext") as "Hi0c".
    iPoseProof (wki_0e with "Htext") as "Hi0e".
    iPoseProof (wki_10 with "Htext") as "Hi10".
    iPoseProof (wki_12 with "Htext") as "Hi12".
    iPoseProof (wki_14 with "Htext") as "Hi14".
    iPoseProof (wki_18 with "Htext") as "Hi18".
    iPoseProof (wki_1c with "Htext") as "Hi1c".
    iPoseProof (wki_1e with "Htext") as "Hi1e".
    iPoseProof (wki_20 with "Htext") as "Hi20".
    iPoseProof (wki_24 with "Htext") as "Hi24".
    iPoseProof (wki_28 with "Htext") as "Hi28".
    (* frame trade: push 8 *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m).
    assert (Hsp1 : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 8).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spF) by (rewrite /R1 upd_eq; reflexivity).
    iApply (wp_caddi16sp_push_s_sconf γ root_ppn Φ (mword_of_int WK) (mword_of_int 60 : mword 6) m K 8 HK8 Hsp1
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    assert (Hsp0f : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    iEval (rewrite Hsp0f stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _)".
    iDestruct "C1" as (v1) "Hc1". iDestruct "C2" as (v2) "Hc2".
    iDestruct "C3" as (v3) "Hc3". iDestruct "C4" as (v4) "Hc4".
    iDestruct "C5" as (v5) "Hc5". iDestruct "C6" as (v6) "Hc6".
    iDestruct "C7" as (v7) "Hc7". iDestruct "C8" as (v8) "Hc8".
    (* cells at pa_stk sp0 1..8 = wk_fcell spF 7..0 *)
    assert (Hb7 : pa_stk sp0 1 = wk_fcell spF 7).
    { unfold wk_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : pa_stk sp0 2 = wk_fcell spF 6).
    { unfold wk_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : pa_stk sp0 3 = wk_fcell spF 5).
    { unfold wk_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : pa_stk sp0 4 = wk_fcell spF 4).
    { unfold wk_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 5 = wk_fcell spF 3).
    { unfold wk_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 6 = wk_fcell spF 2).
    { unfold wk_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : pa_stk sp0 7 = wk_fcell spF 1).
    { unfold wk_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb0 : pa_stk sp0 8 = wk_fcell spF 0).
    { unfold wk_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Hb7) in "Hc1". iEval (rewrite Hb6) in "Hc2". iEval (rewrite Hb5) in "Hc3".
    iEval (rewrite Hb4) in "Hc4". iEval (rewrite Hb3) in "Hc5". iEval (rewrite Hb2) in "Hc6".
    iEval (rewrite Hb1) in "Hc7". iEval (rewrite Hb0) in "Hc8".
    (* R1!!!K = m!!!K for the saved registers *)
    assert (Hra : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0 : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1 : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2 : R1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs3 : R1 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs4 : R1 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs5 : R1 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hpp02 : add_vec_int (mword_of_int WK : mword 64) 2 = mword_of_int (WK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,56(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x02)) (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5) R1 (K - 8)%nat v1
              with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspR1). iExact "Hc1". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc1".
    iEval (rewrite HspR1 Hra) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (WK + 0x02) : mword 64) 2 = mword_of_int (WK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,48(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x04)) (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5) R1 (K - 8)%nat v2
              with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspR1). iExact "Hc2". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc2".
    iEval (rewrite HspR1 Hs0) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (WK + 0x04) : mword 64) 2 = mword_of_int (WK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,40(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x06)) (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5) R1 (K - 8)%nat v3
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [Hc3] [-]").
    { iEval (rewrite HspR1). iExact "Hc3". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc3".
    iEval (rewrite HspR1 Hs1) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (WK + 0x06) : mword 64) 2 = mword_of_int (WK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,32(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x08)) (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5) R1 (K - 8)%nat v4
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [Hc4] [-]").
    { iEval (rewrite HspR1). iExact "Hc4". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc4".
    iEval (rewrite HspR1 Hs2) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (WK + 0x08) : mword 64) 2 = mword_of_int (WK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,24(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x0a)) (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5) R1 (K - 8)%nat v5
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [Hc5] [-]").
    { iEval (rewrite HspR1). iExact "Hc5". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc5".
    iEval (rewrite HspR1 Hs3) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (WK + 0x0a) : mword 64) 2 = mword_of_int (WK + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp s4,16(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x0c)) (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5) R1 (K - 8)%nat v6
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [Hc6] [-]").
    { iEval (rewrite HspR1). iExact "Hc6". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc6".
    iEval (rewrite HspR1 Hs4) in "Hc6".
    assert (Hpp0e : add_vec_int (mword_of_int (WK + 0x0c) : mword 64) 2 = mword_of_int (WK + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.sdsp s5,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x0e)) (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5) R1 (K - 8)%nat v7
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0e [Hc7] [-]").
    { iEval (rewrite HspR1). iExact "Hc7". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hc7".
    iEval (rewrite HspR1 Hs5) in "Hc7".
    assert (Hpp10 : add_vec_int (mword_of_int (WK + 0x0e) : mword 64) 2 = mword_of_int (WK + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.addi4spn s0,sp,64 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x10)) (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 8)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    assert (Hpp12 : add_vec_int (mword_of_int (WK + 0x10) : mword 64) 2 = mword_of_int (WK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.mv s4,a0 : s4 := a0 (chan) *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x12)) (mword_of_int 20 : mword 5) (mword_of_int 10 : mword 5)
              R2 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi12 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R3 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    assert (Hpp14 : add_vec_int (mword_of_int (WK + 0x12) : mword 64) 2 = mword_of_int (WK + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 auipc s1,0x11 ; +0x18 addi s1,s1,2066 : s1 := &proc[0] *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x14)) (mword_of_int 9 : mword 5) (mword_of_int 0x11 : mword 20)
              R3 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (WK + 0x14) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R3).
    assert (Hpp18 : add_vec_int (mword_of_int (WK + 0x14) : mword 64) 4 = mword_of_int (WK + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x18)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 2066 : mword 12)
              R4 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (R4 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 2066 : mword 12)))]> R4).
    assert (Hs1proc : R5 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr 0).
    { rewrite /R5 upd_eq. rewrite /R4 upd_eq. unfold proc_addr, proc_base, proc_size.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1c : add_vec_int (mword_of_int (WK + 0x18) : mword 64) 4 = mword_of_int (WK + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.li s3,2 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x1c)) (mword_of_int 19 : mword 5) (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
              R5 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R6 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mword_of_int 2 : mword 64)]> R5).
    assert (Hpp1e : add_vec_int (mword_of_int (WK + 0x1c) : mword 64) 2 = mword_of_int (WK + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.li s5,3 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x1e)) (mword_of_int 21 : mword 5) (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              R6 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mword_of_int 3 : mword 64)]> R6).
    assert (Hpp20 : add_vec_int (mword_of_int (WK + 0x1e) : mword 64) 2 = mword_of_int (WK + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 auipc s2,0x16 ; +0x24 addi s2,s2,518 : s2 := &proc[64] *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x20)) (mword_of_int 18 : mword 5) (mword_of_int 0x16 : mword 20)
              R7 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi20 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R8 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (mword_of_int (WK + 0x20) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> R7).
    assert (Hpp24 : add_vec_int (mword_of_int (WK + 0x20) : mword 64) 4 = mword_of_int (WK + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x24)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 518 : mword 12)
              R8 (K - 8)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi24 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R9 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (R8 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 518 : mword 12)))]> R8).
    assert (Hs2proc : R9 !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC).
    { rewrite /R9 upd_eq. rewrite /R8 upd_eq. unfold proc_addr, proc_base, NPROC, proc_size.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp28 : add_vec_int (mword_of_int (WK + 0x24) : mword 64) 4 = mword_of_int (WK + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 c.j -> wakeup+0x38 (loop test) *)
    iApply (wp_cj_s_sconf γ root_ppn Φ (mword_of_int (WK + 0x28))
              (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")))
              R9 (K - 8)%nat ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi28 [-]").
    iNext. iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Htgtj : add_vec (mword_of_int (WK + 0x28) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")))) = mword_of_int (WK + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtj) in "Hpc".
    (* the R9 register facts + hand the frame cells to the continuation *)
    iApply ("Hcont" $! R9 v8 with "[%] Hsc Hhs Hcg Htlbinv Hpc Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8").
    (* [ptp c]: peel R9..R1's own inserts (all keys distinct from an untouched
       reg) down to m. *)
    assert (Hthread : forall c : mword 5, c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 ->
              c <> mword_of_int 21 -> c <> csp_rs1 ->
              R9 !!! Regidx c = m !!! Regidx c).
    { intros c N8 N9 N18 N19 N20 N21 Ncsp.
      rewrite /R9 upd_ne; [| congruence].
      rewrite /R8 upd_ne; [| congruence].
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    (* Split the conjunction with [apply conj] -- NOT [repeat split]: over the
       transparent [regfile] tower, [split]'s [eq_refl] would close many
       conjuncts by kernel conversion, poisoning the async [Qed] (and scrambling
       which goals remain).  Peel every leaf with the upd_ne / upd_eq LEMMAS
       (values stay opaque) before each [exact]/[reflexivity]. *)
    repeat apply conj.
    - (* s1 (reg 9) = &proc[0] *)
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      exact Hs1proc.
    - (* s2 (reg 18) = &proc[64] *) exact Hs2proc.
    - (* s3 (reg 19) = 2 *)
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_eq. reflexivity.
    - (* s5 (reg 21) = 3 *)
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_eq. reflexivity.
    - (* s4 (reg 20) = a0 (chan) = m!!!10 *)
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_eq. unfold regval_into_reg. rewrite add_vec_zero_l.
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate].
    - (* csp = spF *)
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1.
    - (* ra (reg 1) = m!!!1 *) apply Hthread; vm_compute; discriminate.
    - (* tp (reg 4) = m!!!4 *) apply Hthread; vm_compute; discriminate.
    - (* s6 (reg 22) *) apply Hthread; vm_compute; discriminate.
    - (* s7 (reg 23) *) apply Hthread; vm_compute; discriminate.
    - (* s8 (reg 24) *) apply Hthread; vm_compute; discriminate.
    - (* s9 (reg 25) *) apply Hthread; vm_compute; discriminate.
    - (* s10 (reg 26) *) apply Hthread; vm_compute; discriminate.
    - (* s11 (reg 27) *) apply Hthread; vm_compute; discriminate.
    - intro r. apply rf_to_gmap_dom.
  Qed.

End WpSconfWakeupPro.

End WakeupProof.
