(* WpSconfKfree.v -- kfree over the SIE-agnostic sconf world (kalloc cone,
   stage 8).  The sconf mirror of [wp_kfree] (WpKfree.v): memset (before the
   lock, interrupts at ambient level) runs SIE-blind via wp_memset_page_sconf;
   the acquire/critical-section/release run at the disabled level, threading
   the counting token [intr_count] net-zero (acquire n->S n, release S n->n).
   sp moves only at the prologue/epilogue (4-slot frame), traded through
   sie_cap_move_down/_up 4; the sub-calls manage their own frames from the
   lent deep custody. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText WpAuipc.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv WpKallocDecode.
Require Import WpMycpu WpLock.
Require Import VcGen.
Require Import KptTree.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSconfMemsetPage WpSconfAcquire WpSconfRelease.
Require Import WpKfree.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section WpSconfKfree.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation KF := KernelSyms.kfree.

  Lemma wp_kfree_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γl : gname) (lk fl : mword 64)
      (m : gmap regidx (mword 64))
      (cpuold : mword 64) (noffv intena_old : mword 32)
      (n : nat) (K : nat) :
    let pcE : mword 64 := mword_of_int KF in
    let p := m !!! Regidx (mword_of_int 10 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    (* acquire's noff-increment store value (function of the ghost noff alone) *)
    let po_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let po_noff_store := (autocast (T := mword) (subrange_vec_dec po_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    (14 <= K)%nat ->
    eq_vec (cpuold : mword 64) cpuv = false ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    lk = mword_of_int KernelSyms.kmem ->
    fl = mword_of_int (KernelSyms.kmem + 24) ->
    (* the hardware noff counter is in lockstep with the ghost token level *)
    (neq_vec (sign_extend' 64 noffv) zero_reg = false <-> n = 0%nat) ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 po_noff_store) = false ->
    eq_vec (sign_extend' 64
       (if eq_vec (sign_extend' 64 noffv) zero_reg then (zeros' 32) else intena_old)) zero_reg = true ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    intr_count γ root_ppn n -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_lock γl lk (kmem_res fl) -∗
    kfree_pre p -∗
    stack_own (pa_stk sp0 kv_frame_slots) K -∗
    a_noff ↦₄ noffv -∗
    a_int ↦₄ intena_old -∗
    a_cpu ↦₈ cpuold -∗
    ( ∀ mr,
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap γ root_ppn mr -∗
      intr_count γ root_ppn n -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      stack_own (pa_stk sp0 kv_frame_slots) K -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE p sp0 ret_tgt cpuv a_noff a_int a_cpu po_noff_a5 po_noff_store
      HK Hcpune Hretm Hlk Hfl Hnoff_lvl Hnoffpos Hintena0.
    iIntros "Hsc Hhs Hcap Hcnt Htlbinv #Htext Hpc Hfile #Hkmem Hpre Hdeep Hqnoff Hqint Hqcpu Hcont".
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    (* the caller-supplied page precondition: validity + full ownership *)
    iDestruct "Hpre" as "[%Hpv Hpown]".
    assert (Hpal : (uint p) mod 4096 = 0) by (destruct Hpv as [Ha _]; exact Ha).
    assert (Hprlo : 0x80023558 <= uint p) by (destruct Hpv as [_ [Hlo _]]; exact Hlo).
    assert (Hprhi : uint p < 0x88000000) by (destruct Hpv as [_ [_ Hhi]]; exact Hhi).
    assert (Hsltu14 : zopz0zI_u p (mword_of_int 0x80023558 : mword 64) = false).
    { unfold zopz0zI_u. apply Z.ltb_ge.
      replace (uint (mword_of_int 0x80023558 : mword 64)) with 0x80023558 by (vm_compute; reflexivity).
      lia. }
    assert (Hsltu1e : zopz0zI_u (mword_of_int 0x87FFFFFF : mword 64) p = false).
    { unfold zopz0zI_u. apply Z.ltb_ge.
      replace (uint (mword_of_int 0x87FFFFFF : mword 64)) with 0x87FFFFFF by (vm_compute; reflexivity).
      lia. }
    iPoseProof (kfi_00 with "Htext") as "Hi00".
    iPoseProof (kfi_02 with "Htext") as "Hi02".
    iPoseProof (kfi_04 with "Htext") as "Hi04".
    iPoseProof (kfi_06 with "Htext") as "Hi06".
    iPoseProof (kfi_08 with "Htext") as "Hi08".
    iPoseProof (kfi_0a with "Htext") as "Hi0a".
    iPoseProof (kfi_0c with "Htext") as "Hi0c".
    iPoseProof (kfi_10 with "Htext") as "Hi10".
    iPoseProof (kfi_14 with "Htext") as "Hi14".
    iPoseProof (kfi_18 with "Htext") as "Hi18".
    iPoseProof (kfi_1a with "Htext") as "Hi1a".
    iPoseProof (kfi_1c with "Htext") as "Hi1c".
    iPoseProof (kfi_1e with "Htext") as "Hi1e".
    iPoseProof (kfi_22 with "Htext") as "Hi22".
    iPoseProof (kfi_24 with "Htext") as "Hi24".
    iPoseProof (kfi_26 with "Htext") as "Hi26".
    iPoseProof (kfi_28 with "Htext") as "Hi28".
    iPoseProof (kfi_2c with "Htext") as "Hi2c".
    iPoseProof (kfi_2e with "Htext") as "Hi2e".
    iPoseProof (kfi_30 with "Htext") as "Hi30".
    (* ===== PROLOGUE: 4-slot frame trade + saves ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hsp1 : R1 !!! Regidx csp_rs1 = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite /R1 lookup_total_insert. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* split the deep custody: top-4 feeds move_down, the rest [K-4] is lent to
       the sub-calls (memset/acquire/release) at the frame sp [spr]. *)
    iDestruct (stack_own_split_1 (pa_stk sp0 kv_frame_slots) 4 K ltac:(lia) with "Hdeep") as "[Hd4 Hdeep]".
    (* +0x00 c.addi16sp sp,-32 -- the frame trade *)
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ pcE (mword_of_int 32 : mword 6) m (stack_own sp0 4)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi00 [Hd4] [-]").
    { iIntros "Hcap".
      iDestruct (sie_cap_move_down γ root_ppn m R1 4 Hsp1 with "Hd4 Hcap") as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros "Hhs Hsc Hcap Hframe Htlbinv Hpc Hfile".
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 lookup_total_insert; reflexivity).
    (* frame cells at [pa_stk sp0 1..4] *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vr0)  "Hr0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hr0".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KF + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 vr24 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi02 Hr24 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KF + 0x02) : mword 64) 2 = mword_of_int (KF + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 vr16 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi04 Hr16 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KF + 0x04) : mword 64) 2 = mword_of_int (KF + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 vr8 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi06 Hr8 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KF + 0x06) : mword 64) 2 = mword_of_int (KF + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 vr0 with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi08 Hr0 [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (KF + 0x08) : mword 64) 2 = mword_of_int (KF + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (KF + 0x0a) : mword 64) 2 = mword_of_int (KF + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    admit.
  Admitted.

End WpSconfKfree.
