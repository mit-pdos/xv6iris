(* WpSconfKfree.v -- kfree over the SIE-agnostic sconf world (kalloc cone,
   stage 8).  The sconf mirror of [wp_kfree] (WpKfree.v): memset (before the
   lock, interrupts at ambient level) runs SIE-blind via wp_memset_page_sconf;
   the acquire/critical-section/release run at the disabled level, threading
   the counting token [intr_count] net-zero (acquire n->S n, release S n->n).
   sp moves only at the prologue/epilogue (4-slot frame), traded through
   sie_cap push/pop 4 (the avail param drops K -> K-4 across the body); the
   sub-calls carve their own frames from the threaded [sie_cap] avail. *)
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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv WpKallocDecode.
Require Import WpMycpu WpLock.
Require Import VcGen.
Require Import KptTree.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpIntenaBits.
Require Import WpSconfMemsetPage WpSconfAcquire WpSconfRelease.
Require Import WpKalloc WpKfree.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* [kfree_nv1_cancel_pure] moved to WpKalloc.v -- shared with kalloc's own
   acquire/release-shaped noff counter, next to [kalloc_sp_cancel]. *)

Section WpSconfKfree.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation KF := KernelSyms.kfree.

  Lemma wp_kfree_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γl : gname) (γk : gname * gname) (lk fl : mword 64)
      (m : regfile)
      (cpuold : mword 64) (noffv intena_old : mword 32)
      (on : option nat) (n : nat) (K : nat) :
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
    (* release's noff-decrement store value (its pop_off restores noff = noffv);
       returned in the [a_noff] cell so a repeated caller can re-thread it. *)
    let noff_ret := (autocast (T := mword) (subrange_vec_dec
        (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 po_noff_store)
            (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
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
    sie_cap_gpr γ root_ppn m K -∗
    intr_count γ root_ppn n -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗
    is_lock γl lk (kmem_res γk fl) -∗
    kfree_pre p -∗
    kalloc_avail γk on -∗
    a_noff ↦₄ noffv -∗
    a_int ↦₄ intena_old -∗
    a_cpu ↦₈ cpuold -∗
    ( ∀ mr,
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mr K -∗
      intr_count γ root_ppn n -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mr ⌝ -∗
      kalloc_avail γk (avail_inc on) -∗
      a_cpu ↦₈ (zero_reg : mword 64) -∗
      a_noff ↦₄ noff_ret -∗
      (∃ iv : mword 32, a_int ↦₄ iv) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE p sp0 ret_tgt cpuv a_noff a_int a_cpu po_noff_a5 po_noff_store noff_ret
      HK Hcpune Hretm Hlk Hfl Hnoff_lvl Hnoffpos Hintena0.
    iIntros "Hsc Hhs Hcg Hcnt Htlbinv #Htext Hpc #Hkmem Hpre Havail Hqnoff Hqint Hqcpu Hcont".
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
    { rewrite /R1 upd_eq. unfold regval_into_reg, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* +0x00 c.addi sp,-32 -- the frame trade (push k := 4) *)
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE (mword_of_int 32 : mword 6) m K 4 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 upd_eq; reflexivity).
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
              R1 (K - 4)%nat vr24 with "Hsc Hhs Hcg Htlbinv Hpc Hi02 Hr24 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KF + 0x02) : mword 64) 2 = mword_of_int (KF + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat vr16 with "Hsc Hhs Hcg Htlbinv Hpc Hi04 Hr16 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KF + 0x04) : mword 64) 2 = mword_of_int (KF + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 4)%nat vr8 with "Hsc Hhs Hcg Htlbinv Hpc Hi06 Hr8 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KF + 0x06) : mword 64) 2 = mword_of_int (KF + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 (K - 4)%nat vr0 with "Hsc Hhs Hcg Htlbinv Hpc Hi08 Hr0 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (KF + 0x08) : mword 64) 2 = mword_of_int (KF + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (KF + 0x0a) : mword 64) 2 = mword_of_int (KF + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== PANIC-CHECK ALU (0x0c..0x30): all bounds hold, both branches fall ===== *)
    (* +0x0c auipc a5,0x23 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x0c)) (mword_of_int 15 : mword 5) (mword_of_int 0x23 : mword 20)
              R2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KF + 0x0c) : mword 64) (auipc_off (mword_of_int 0x23 : mword 20)))]> R2).
    assert (Hpp10 : add_vec_int (mword_of_int (KF + 0x0c) : mword 64) 4 = mword_of_int (KF + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 addi a5,a5,-1260  (a5 := <end> = 0x80023558) *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 0xb06 : mword 12)
              R3 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 0xb06 : mword 12)))]> R3).
    assert (Hpp14 : add_vec_int (mword_of_int (KF + 0x10) : mword 64) 4 = mword_of_int (KF + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    assert (Hp10 : R4 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hend : R4 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x80023558).
    { rewrite /R4 upd_eq. rewrite /R3 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x14 sltu a4,a0,a5  (a4 := p <u end = 0) *)
    iApply (wp_sltu_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x14))
              (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5)
              (mword_of_int 0 : mword 64) R4 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hp10 Hend; exact (sltu_false_zero p (mword_of_int 0x80023558) Hsltu14))
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R4).
    assert (Hpp18 : add_vec_int (mword_of_int (KF + 0x14) : mword 64) 4 = mword_of_int (KF + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.li a5,17 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x18))
              (mword_of_int 15 : mword 5) (mword_of_int 17 : mword 6) (mword_of_int 17 : mword 64)
              R5 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 17 : mword 64)]> R5).
    assert (Hli : R6 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 17)
      by (rewrite /R6 upd_eq; reflexivity).
    assert (Hpp1a : add_vec_int (mword_of_int (KF + 0x18) : mword 64) 2 = mword_of_int (KF + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.slli a5,0x1b  (a5 := 17 << 27 = PHYSTOP) *)
    iApply (wp_cslli_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x1a)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 27 : mword 6)
              R6 (K - 4)%nat ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (shift_bits_left (R6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 27 : mword 6) (Z.sub log2_xlen 1) 0))]> R6).
    assert (Hphys : R7 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x88000000).
    { rewrite /R7 upd_eq. rewrite Hli. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1c : add_vec_int (mword_of_int (KF + 0x1a) : mword 64) 2 = mword_of_int (KF + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.addi a5,-1  (a5 := PHYSTOP - 1) *)
    iApply (wp_caddi_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              R7 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (R7 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> R7).
    assert (Hphysm1 : R8 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x87FFFFFF).
    { rewrite /R8 upd_eq. rewrite Hphys. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp10_8 : R8 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      exact Hp10. }
    assert (Hpp1e : add_vec_int (mword_of_int (KF + 0x1c) : mword 64) 2 = mword_of_int (KF + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e sltu a5,a5,a0  (a5 := (PHYSTOP-1) <u p = 0) *)
    iApply (wp_sltu_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x1e))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 64) R8 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hphysm1 Hp10_8; exact (sltu_false_zero (mword_of_int 0x87FFFFFF) p Hsltu1e))
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R8).
    assert (Hor14 : R9 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0).
    { rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_eq; reflexivity. }
    assert (Hor15 : R9 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R9 upd_eq; reflexivity).
    assert (Hpp22 : add_vec_int (mword_of_int (KF + 0x1e) : mword 64) 4 = mword_of_int (KF + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.or a5,a4  (a5 := a5 | a4 = 0) *)
    iApply (wp_cor_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x22))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (mword_of_int 0 : mword 64) R9 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hor15 Hor14; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi22 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R9).
    assert (Hbnez24 : R10 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R10 upd_eq; reflexivity).
    assert (Hp10_10 : R10 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R10 upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      exact Hp10_8. }
    assert (Hpp24 : add_vec_int (mword_of_int (KF + 0x22) : mword 64) 2 = mword_of_int (KF + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 c.bnez a5,+60  NOT taken (a5 = 0) *)
    iApply (wp_cbnez_fall_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x24)) (mword_of_int 30 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              R10 (K - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hbnez24; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi24 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp26 : add_vec_int (mword_of_int (KF + 0x24) : mword 64) 2 = mword_of_int (KF + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 c.mv s1,a0  (s1 := p) *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x26)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R10 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi26 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R11 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R10 !!! Regidx (mword_of_int 10 : mword 5)))]> R10).
    assert (Hp10_11 : R11 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R11 upd_ne; [| vm_compute; discriminate]. exact Hp10_10. }
    assert (Hpp28 : add_vec_int (mword_of_int (KF + 0x26) : mword 64) 2 = mword_of_int (KF + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 slli a5,a0,0x34  (a5 := p << 52 = 0) *)
    iApply (wp_slli_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x28))
              (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 52 : mword 6)
              (mword_of_int 0 : mword 64) R11 (K - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hp10_11; exact (shift_bits_left52_zero p Hpal))
              with "Hsc Hhs Hcg Htlbinv Hpc Hi28 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R12 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R11).
    assert (Hbnez2c : R12 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R12 upd_eq; reflexivity).
    assert (Hpp2c : add_vec_int (mword_of_int (KF + 0x28) : mword 64) 4 = mword_of_int (KF + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c c.bnez a5,+60  NOT taken (a5 = 0) *)
    iApply (wp_cbnez_fall_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x2c)) (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              R12 (K - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hbnez2c; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp2e : add_vec_int (mword_of_int (KF + 0x2c) : mword 64) 2 = mword_of_int (KF + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.lui a2,0x1  (a2 := 4096) *)
    iApply (wp_clui_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x2e))
              (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              R12 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(unfold luival; apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R13 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> R12).
    assert (Hpp30 : add_vec_int (mword_of_int (KF + 0x2e) : mword 64) 2 = mword_of_int (KF + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.li a1,1 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x30))
              (mword_of_int 11 : mword 5) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              R13 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi30 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R14 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> R13).
    assert (Hpp32 : add_vec_int (mword_of_int (KF + 0x30) : mword 64) 2 = mword_of_int (KF + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* ===== MEMSET(p, 1, 4096): jal + wp_memset_page_sconf (deep-2 lent) ===== *)
    assert (Hp10_14 : R14 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R14 upd_ne; [| vm_compute; discriminate].
      rewrite /R13 upd_ne; [| vm_compute; discriminate].
      rewrite /R12 upd_ne; [| vm_compute; discriminate].
      rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      exact Hp10. }
    assert (Hsp_14 : R14 !!! Regidx csp_rs1 = spr).
    { rewrite /R14 upd_ne; [| vm_compute; discriminate].
      rewrite /R13 upd_ne; [| vm_compute; discriminate].
      rewrite /R12 upd_ne; [| vm_compute; discriminate].
      rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    iPoseProof (kfi_32 with "Htext") as "Hi32".
    (* +0x32 jal ra,memset *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x32)) (mword_of_int 1 : mword 5) (mword_of_int 0x250 : mword 21)
              R14 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (Mms := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x32) : mword 64) 4)]> R14).
    assert (Htgtms : add_vec (mword_of_int (KF + 0x32) : mword 64) (sign_extend' 64 (mword_of_int 0x250 : mword 21)) = mword_of_int KernelSyms.memset)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtms) in "Hpc".
    assert (HMmsa0 : Mms !!! Regidx (mword_of_int 10 : mword 5) = p)
      by (rewrite /Mms upd_ne; [ exact Hp10_14 | vm_compute; discriminate ]).
    assert (HMmsa1 : Mms !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 1 : mword 64)).
    { rewrite /Mms upd_ne; [| vm_compute; discriminate].
      rewrite /R14 upd_eq. reflexivity. }
    assert (HMmsa2 : Mms !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int 4096 : mword 64)).
    { rewrite /Mms upd_ne; [| vm_compute; discriminate].
      rewrite /R14 upd_ne; [| vm_compute; discriminate].
      rewrite /R13 upd_eq. reflexivity. }
    assert (HMmsra : Mms !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KF + 0x36)).
    { rewrite /Mms upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HMmssp : Mms !!! Regidx csp_rs1 = spr)
      by (rewrite /Mms upd_ne; [ exact Hsp_14 | vm_compute; discriminate ]).
    iApply (wp_memset_page_sconf γ root_ppn Φ Mms (K - 4)%nat (mword_of_int 1 : mword 64)
              ltac:(lia)
              ltac:(rewrite HMmsa0; exact Hpv) HMmsa1 HMmsa2
              ltac:(rewrite HMmsra; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc [Hpown] [-]").
    { iEval (rewrite HMmsa0). iExact "Hpown". }
    iIntros (mfp) "Hsc Hhs Hcg Htlbinv Hpc Hpage %Hpinsf".
    iEval (rewrite HMmsa0) in "Hpage".
    pose proof Hpinsf as Hpinsf_cs.
    unfold callee_saved in Hpinsf.
    destruct Hpinsf as (Hfsp & Hftp & Hfs0 & Hfs1 & Hfs2 & Hfs3 & Hfs4 & Hfs5 & Hfs6 & Hfs7 & Hfs8 & Hfs9 & Hfs10 & Hfs11).
    assert (Hpc36 : update_vec_dec (add_vec (Mms !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x36)).
    { rewrite HMmsra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc36) in "Hpc".
    assert (Hmfpsp : mfp !!! Regidx csp_rs1 = spr) by (rewrite Hfsp HMmssp; reflexivity).
    assert (HMmstp : Mms !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Mms upd_ne; [| vm_compute; discriminate].
      rewrite /R14 upd_ne; [| vm_compute; discriminate].
      rewrite /R13 upd_ne; [| vm_compute; discriminate].
      rewrite /R12 upd_ne; [| vm_compute; discriminate].
      rewrite /R11 upd_ne; [| vm_compute; discriminate].
      rewrite /R10 upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hmfptp : mfp !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5))
      by (rewrite Hftp HMmstp; reflexivity).
    iPoseProof (kfi_36 with "Htext") as "Hi36".
    iPoseProof (kfi_3a with "Htext") as "Hi3a".
    iPoseProof (kfi_3e with "Htext") as "Hi3e".
    (* ===== ACQUIRE setup + call (intr_count n -> S n, deep-10 lent) ===== *)
    (* +0x36 auipc s2,0x12 *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x36)) (mword_of_int 18 : mword 5) (mword_of_int 0x12 : mword 20)
              mfp (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi36 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (S1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (mword_of_int (KF + 0x36) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> mfp).
    assert (Hpp3a : add_vec_int (mword_of_int (KF + 0x36) : mword 64) 4 = mword_of_int (KF + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* +0x3a addi s2,s2,-1862  (s2 := &kmem) *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x3a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x8ac : mword 12)
              S1 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi3a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (S2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (S1 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x8ac : mword 12)))]> S1).
    assert (Hs2kmem : S2 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /S2 upd_eq. rewrite /S1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp3e : add_vec_int (mword_of_int (KF + 0x3a) : mword 64) 4 = mword_of_int (KF + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* +0x3e c.mv a0,s2 *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x3e)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              S2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi3e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (S3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (S2 !!! Regidx (mword_of_int 18 : mword 5)))]> S2).
    assert (Hpp40 : add_vec_int (mword_of_int (KF + 0x3e) : mword 64) 2 = mword_of_int (KF + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* +0x40 jal ra,acquire *)
    iPoseProof (kfi_40 with "Htext") as "Hi40".
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x40)) (mword_of_int 1 : mword 5) (mword_of_int 0x182 : mword 21)
              S3 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi40 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (Kacq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x40) : mword 64) 4)]> S3).
    assert (Htgtacq : add_vec (mword_of_int (KF + 0x40) : mword 64) (sign_extend' 64 (mword_of_int 0x182 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HKacqcsp : Kacq !!! Regidx csp_rs1 = spr).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /S3 upd_ne; [| vm_compute; discriminate].
      rewrite /S2 upd_ne; [| vm_compute; discriminate].
      rewrite /S1 upd_ne; [| vm_compute; discriminate].
      exact Hmfpsp. }
    assert (HKacqtp : Kacq !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /S3 upd_ne; [| vm_compute; discriminate].
      rewrite /S2 upd_ne; [| vm_compute; discriminate].
      rewrite /S1 upd_ne; [| vm_compute; discriminate].
      exact Hmfptp. }
    assert (HKacqa0 : Kacq !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /S3 upd_eq. rewrite Hs2kmem. apply add_vec_zero_l. }
    assert (HKacqra : Kacq !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KF + 0x40) : mword 64) 4)
      by (rewrite /Kacq; apply upd_eq).
    assert (HKacqs2 : Kacq !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /S3 upd_ne; [| vm_compute; discriminate].
      exact Hs2kmem. }
    assert (Hmacq_s1 : Kacq !!! Regidx (mword_of_int 9 : mword 5) = p).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /S3 upd_ne; [| vm_compute; discriminate].
      rewrite /S2 upd_ne; [| vm_compute; discriminate].
      rewrite /S1 upd_ne; [| vm_compute; discriminate].
      rewrite Hfs1.
      rewrite /Mms upd_ne; [| vm_compute; discriminate].
      rewrite /R14 upd_ne; [| vm_compute; discriminate].
      rewrite /R13 upd_ne; [| vm_compute; discriminate].
      rewrite /R12 upd_ne; [| vm_compute; discriminate].
      rewrite /R11 upd_eq.
      rewrite /R10 upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite Hp10. apply add_vec_zero_l. }
    iApply (wp_acquire_sconf γ root_ppn Φ γl (kmem_res γk fl) Kacq
              cpuold noffv intena_old n (K - 4)%nat
              ltac:(rewrite HKacqtp; exact Hcpune)
              ltac:(rewrite HKacqra; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc [Hkmem] [Hqcpu] [Hqnoff] [Hqint] [-]").
    { iEval (rewrite HKacqa0 -Hlk). iExact "Hkmem". }
    { iEval (rewrite HKacqa0 -Hlk). iExact "Hqcpu". }
    { iEval (rewrite HKacqtp). iExact "Hqnoff". }
    { iEval (rewrite HKacqtp). iExact "Hqint". }
    iIntros (ms macq) "%Hmsfacts Hhs Hsc Hcg Htlbinv Hpc %Hacqpins Htok HRres Hacpu Hanoff Haint Hcnt".
    assert (Hpc44 : update_vec_dec (add_vec (Kacq !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x44)).
    { rewrite HKacqra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc44) in "Hpc".
    (* ===== FREELIST PUSH (0x44..0x4a): p->next := head; kmem.freelist := p ===== *)
    pose proof Hacqpins as Hacqpins_cs.
    unfold callee_saved in Hacqpins.
    destruct Hacqpins as (Hqsp & Hqtp & Hqs0 & Hqs1 & Hqs2 & Hqs3 & Hqs4 & Hqs5 & Hqs6 & Hqs7 & Hqs8 & Hqs9 & Hqs10 & Hqs11).
    assert (Hs1p : macq !!! Regidx (mword_of_int 9 : mword 5) = p) by (rewrite Hqs1; exact Hmacq_s1).
    assert (Hs2km : macq !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem) by (rewrite Hqs2; exact HKacqs2).
    iPoseProof (kfi_44 with "Htext") as "Hi44".
    iPoseProof (kfi_48 with "Htext") as "Hi48".
    iPoseProof (kfi_4a with "Htext") as "Hi4a".
    iDestruct "HRres" as (head pages) "(Hflw & Hchain & Hauth)".
    assert (Hldaddr : add_vec (macq !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x18 : mword 12)) = fl).
    { rewrite Hs2km Hfl. apply bv_eq; vm_compute; reflexivity. }
    (* +0x44 ld a5,24(s2) : a5 := head *)
    iApply (wp_ld_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x44)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x18 : mword 12)
              macq (K - 4)%nat head ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi44 [Hflw] [-]").
    { iEval (rewrite -Hldaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hflw".
    iEval (rewrite Hldaddr) in "Hflw".
    set (Rld := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg head]> macq).
    assert (HRlds1 : Rld !!! Regidx (mword_of_int 9 : mword 5) = p)
      by (rewrite /Rld upd_ne; [ exact Hs1p | vm_compute; discriminate ]).
    assert (HRlds2 : Rld !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem)
      by (rewrite /Rld upd_ne; [ exact Hs2km | vm_compute; discriminate ]).
    assert (HRlda5 : Rld !!! Regidx (mword_of_int 15 : mword 5) = head)
      by (rewrite /Rld; apply upd_eq).
    assert (Hpp48 : add_vec_int (mword_of_int (KF + 0x44) : mword 64) 4 = mword_of_int (KF + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 c.sd a5,0(s1) : p->next := head *)
    iEval (rewrite page_own_split) in "Hpage".
    iDestruct "Hpage" as "[Hpghead Hpgrest]".
    iDestruct (page_head8_word_at p Hpv with "Hpghead") as (wold) "Hpw".
    assert (Hsdaddr : add_vec (Rld !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = p).
    { replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      rewrite HRlds1. apply kv_addv_zero. }
    iApply (wp_csd_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x48)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              Rld (K - 4)%nat wold with "Hsc Hhs Hcg Htlbinv Hpc Hi48 [Hpw] [-]").
    { iEval (rewrite -Hsdaddr) in "Hpw". rewrite /word_at. iExact "Hpw". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hpw".
    iEval (rewrite Hsdaddr) in "Hpw".
    iEval (rewrite HRlda5) in "Hpw".
    iAssert (run_page p head) with "[Hpw Hpgrest]" as "Hrun".
    { rewrite /run_page. rewrite /word_at. iFrame "Hpw Hpgrest". }
    assert (Hpp4a : add_vec_int (mword_of_int (KF + 0x48) : mword 64) 2 = mword_of_int (KF + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a sd s1,24(s2) : kmem.freelist := p *)
    assert (Hsdaddr2 : add_vec (Rld !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x18 : mword 12)) = fl).
    { rewrite HRlds2 Hfl. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_sd_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x4a)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x18 : mword 12)
              Rld (K - 4)%nat head with "Hsc Hhs Hcg Htlbinv Hpc Hi4a [Hflw] [-]").
    { iEval (rewrite -Hsdaddr2) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hflw".
    iEval (rewrite Hsdaddr2) in "Hflw".
    iEval (rewrite HRlds1) in "Hflw".
    (* refold the freelist invariant with [p] pushed; the count ghost-steps up *)
    iMod (kmem_res_push γk fl p head pages on Hpv with "Havail [Hflw] Hrun Hchain Hauth")
      as "[Havail HRres]".
    { rewrite /word_at. iExact "Hflw". }
    assert (Hpp4e : add_vec_int (mword_of_int (KF + 0x4a) : mword 64) 4 = mword_of_int (KF + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    iPoseProof (kfi_4e with "Htext") as "Hi4e".
    iPoseProof (kfi_50 with "Htext") as "Hi50".
    (* ===== RELEASE setup + call (intr_count S n -> n, deep-10 lent) ===== *)
    (* +0x4e c.mv a0,s2 : a0 := &kmem *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x4e)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              Rld (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi4e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (Rae := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Rld !!! Regidx (mword_of_int 18 : mword 5)))]> Rld).
    assert (Hpp50 : add_vec_int (mword_of_int (KF + 0x4e) : mword 64) 2 = mword_of_int (KF + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 jal ra,release *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x50)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fa : mword 21)
              Rae (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi50 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (Rrel := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x50) : mword 64) 4)]> Rae).
    assert (Htgtrel : add_vec (mword_of_int (KF + 0x50) : mword 64) (sign_extend' 64 (mword_of_int 0x1fa : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HRrelcsp : Rrel !!! Regidx csp_rs1 = spr).
    { rewrite /Rrel upd_ne; [| vm_compute; discriminate].
      rewrite /Rae upd_ne; [| vm_compute; discriminate].
      rewrite /Rld upd_ne; [| vm_compute; discriminate].
      rewrite Hqsp. exact HKacqcsp. }
    assert (HRreltp : Rrel !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Rrel upd_ne; [| vm_compute; discriminate].
      rewrite /Rae upd_ne; [| vm_compute; discriminate].
      rewrite /Rld upd_ne; [| vm_compute; discriminate].
      rewrite Hqtp. exact HKacqtp. }
    assert (HRrela0 : Rrel !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Rrel upd_ne; [| vm_compute; discriminate].
      rewrite /Rae upd_eq. rewrite HRlds2. apply add_vec_zero_l. }
    assert (HRrelra : Rrel !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KF + 0x50) : mword 64) 4)
      by (rewrite /Rrel; apply upd_eq).
    (* the acquire (+1) / release (-1) noff cancellation makes release's nv1
       equal to [sign_extend' 64 noffv], so its coupling premise IS Hnoff_lvl. *)
    assert (Hnv1eq : sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 po_noff_store) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
                     = sign_extend' 64 noffv).
    { exact (kfree_nv1_cancel_pure noffv). }
    assert (kfree_nv1_cancel : neq_vec (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 po_noff_store) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)) zero_reg = false <-> n = 0%nat).
    { rewrite Hnv1eq. exact Hnoff_lvl. }
    iApply (wp_release_sconf γ root_ppn Φ γl lk (kmem_res γk fl) Rrel
              (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)))
              po_noff_store
              (if eq_vec (sign_extend' 64 noffv) zero_reg then po_intena_val ms else intena_old)
              n (K - 4)%nat (dqi:=DfracOwn 1)
              ltac:(rewrite HRrela0 Hlk; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HRreltp; apply eq_vec_true_iff; reflexivity)
              kfree_nv1_cancel
              Hnoffpos
              ltac:(rewrite HRrelra; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc [Hkmem] Htok HRres [Hacpu] [Hanoff] [Haint] Hcnt [-]").
    { iExact "Hkmem". }
    { iEval (rewrite HKacqa0 -Hlk HKacqtp) in "Hacpu". iEval (rewrite HRrela0 -Hlk). iExact "Hacpu". }
    { iEval (rewrite HKacqtp) in "Hanoff". iEval (rewrite HRreltp). iExact "Hanoff". }
    { iEval (rewrite HKacqtp) in "Haint". iEval (rewrite HRreltp). iExact "Haint". }
    iIntros (mrel) "Hhs Hsc Hcg Htlbinv Hpc %Hrelpins Hcpu2 Hnoff2 Hint2 Hcnt".
    assert (Hpc54 : update_vec_dec (add_vec (Rrel !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x54)).
    { rewrite HRrelra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc54) in "Hpc".
    (* ===== EPILOGUE (0x54..0x5e): restore ra/s0/s1/s2, frame trade back, ret ===== *)
    pose proof Hrelpins as Hrelpins_cs.
    unfold callee_saved in Hrelpins.
    destruct Hrelpins as (Hrsp & Hrtp & Hrs0 & Hrs1 & _ & Hrs3 & Hrs4 & Hrs5 & Hrs6 & Hrs7 & Hrs8 & Hrs9 & Hrs10 & Hrs11).
    assert (HspMrel : mrel !!! Regidx csp_rs1 = spr) by (rewrite Hrsp; exact HRrelcsp).
    iPoseProof (kfi_54 with "Htext") as "Hi54".
    iPoseProof (kfi_56 with "Htext") as "Hi56".
    iPoseProof (kfi_58 with "Htext") as "Hi58".
    iPoseProof (kfi_5a with "Htext") as "Hi5a".
    iPoseProof (kfi_5c with "Htext") as "Hi5c".
    iPoseProof (kfi_5e with "Htext") as "Hi5e".
    (* +0x54 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x54)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (K - 4)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi54 [Hr24] [-]").
    { iEval (rewrite HspMrel). iEval (rewrite HspR1) in "Hr24". iExact "Hr24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    iEval (rewrite HspMrel) in "Hr24".
    set (Q54 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    assert (HspQ54 : Q54 !!! Regidx csp_rs1 = spr) by (rewrite /Q54 upd_ne; [ exact HspMrel | vm_compute; discriminate ]).
    assert (Hpp56 : add_vec_int (mword_of_int (KF + 0x54) : mword 64) 2 = mword_of_int (KF + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* +0x56 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x56)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q54 (K - 4)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi56 [Hr16] [-]").
    { iEval (rewrite HspQ54). iEval (rewrite HspR1) in "Hr16". iExact "Hr16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    iEval (rewrite HspQ54) in "Hr16".
    set (Q56 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q54).
    assert (HspQ56 : Q56 !!! Regidx csp_rs1 = spr) by (rewrite /Q56 upd_ne; [ exact HspQ54 | vm_compute; discriminate ]).
    assert (Hpp58 : add_vec_int (mword_of_int (KF + 0x56) : mword 64) 2 = mword_of_int (KF + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* +0x58 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x58)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q56 (K - 4)%nat (R1 !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi58 [Hr8] [-]").
    { iEval (rewrite HspQ56). iEval (rewrite HspR1) in "Hr8". iExact "Hr8". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    iEval (rewrite HspQ56) in "Hr8".
    set (Q58 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q56).
    assert (HspQ58 : Q58 !!! Regidx csp_rs1 = spr) by (rewrite /Q58 upd_ne; [ exact HspQ56 | vm_compute; discriminate ]).
    assert (Hpp5a : add_vec_int (mword_of_int (KF + 0x58) : mword 64) 2 = mword_of_int (KF + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* +0x5a c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x5a)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              Q58 (K - 4)%nat (R1 !!! Regidx (mword_of_int 18 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5a [Hr0] [-]").
    { iEval (rewrite HspQ58). iEval (rewrite HspR1) in "Hr0". iExact "Hr0". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr0".
    iEval (rewrite HspQ58) in "Hr0".
    set (Q5a := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 18 : mword 5))]> Q58).
    assert (HspQ5a : Q5a !!! Regidx csp_rs1 = spr) by (rewrite /Q5a upd_ne; [ exact HspQ58 | vm_compute; discriminate ]).
    assert (Hpp5c : add_vec_int (mword_of_int (KF + 0x5a) : mword 64) 2 = mword_of_int (KF + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* +0x5c c.addi16sp sp,32 -- the frame trade back (pop 4) *)
    set (Q5c := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q5a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q5a).
    assert (HQ5csp : Q5c !!! Regidx csp_rs1 = sp0).
    { rewrite /Q5c upd_eq. rewrite HspQ5a. unfold spr, sp0.
      apply kfree_sp_cancel. }
    assert (Hwv : add_vec (Q5a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HspQ5a. unfold spr, sp0. apply kfree_sp_cancel. }
    assert (Hpop : Q5a !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q5a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HspQ5a. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    (* reassemble the four frame cells (at pa_stk sp0 1..4) into stack_own sp0 4 *)
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
      iSplitL "Hr0";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hr0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x5c)) (mword_of_int 2 : mword 6) Q5a (K - 4)%nat 4 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5c Hframe4 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (Q5a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q5a) with Q5c.
    assert (Hpp5e : add_vec_int (mword_of_int (KF + 0x5c) : mword 64) 2 = mword_of_int (KF + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* +0x5e c.ret *)
    assert (HQ5cra : Q5c !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Q5c upd_ne; [| vm_compute; discriminate].
      rewrite /Q5a upd_ne; [| vm_compute; discriminate].
      rewrite /Q58 upd_ne; [| vm_compute; discriminate].
      rewrite /Q56 upd_ne; [| vm_compute; discriminate].
      rewrite /Q54 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (Q5c !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HQ5cra; exact Hretm).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (KF + 0x5e)) (mword_of_int 1 : mword 5) Q5c K
              ltac:(vm_compute; discriminate) Hretaligned
              with "Hsc Hhs Hcg Htlbinv Hpc Hi5e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hretf : update_vec_dec (add_vec (Q5c !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HQ5cra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! Q5c with "Hsc Hhs Hcg Hcnt Htlbinv Hpc [%] Havail [Hcpu2] [Hnoff2] [Hint2]").
    2:{ (* a_cpu ↦₈ zero_reg -- release cleared lk->cpu *)
        iEval (rewrite HRrela0 -Hlk) in "Hcpu2". iExact "Hcpu2". }
    2:{ (* a_noff ↦₄ noff_ret -- release's pop_off restored noff *)
        iEval (rewrite HRreltp) in "Hnoff2". iExact "Hnoff2". }
    2:{ (* a_int ↦₄ (existential scratch) *)
        iEval (rewrite HRreltp) in "Hint2". iExists _. iExact "Hint2". }
    { (* callee_saved m Q5c *)
      assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
                c <> mword_of_int 9 -> c <> mword_of_int 10 -> c <> mword_of_int 11 ->
                c <> mword_of_int 12 -> c <> mword_of_int 14 -> c <> mword_of_int 15 ->
                c <> mword_of_int 18 ->
                Q5c !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N1 N2 N8 N9 N10 N11 N12 N14 N15 N18.
        let peel := (repeat (rewrite upd_ne; [ | congruence ])) in
        rewrite /Q5c /Q5a /Q58 /Q56 /Q54; peel;
        rewrite (callee_saved_lookup Hrelpins_cs c Hcs);
        rewrite /Rrel /Rae /Rld; peel;
        rewrite (callee_saved_lookup Hacqpins_cs c Hcs);
        rewrite /Kacq /S3 /S2 /S1; peel;
        rewrite (callee_saved_lookup Hpinsf_cs c Hcs);
        rewrite /Mms /R14 /R13 /R12 /R11 /R10 /R9 /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1; peel;
        reflexivity. }
      unfold callee_saved.
      split.
      { (* sp *)
        rewrite /Q5c upd_eq.
        assert (HQ5acsp : Q5a !!! Regidx csp_rs1 = spr).
        { rewrite /Q5a /Q58 /Q56 /Q54.
          repeat (rewrite upd_ne; [| vm_compute; discriminate]).
          exact HspMrel. }
        rewrite HQ5acsp. unfold regval_into_reg, spr. apply kfree_sp_cancel. }
      split.
      { (* tp *) apply Hthread; vm_compute; first [reflexivity | discriminate]. }
      split.
      { (* s0 *)
        rewrite /Q5c upd_ne; [| vm_compute; discriminate].
        rewrite /Q5a upd_ne; [| vm_compute; discriminate].
        rewrite /Q58 upd_ne; [| vm_compute; discriminate].
        rewrite /Q56 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      split.
      { (* s1 *)
        rewrite /Q5c upd_ne; [| vm_compute; discriminate].
        rewrite /Q5a upd_ne; [| vm_compute; discriminate].
        rewrite /Q58 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      split.
      { (* s2 *)
        rewrite /Q5c upd_ne; [| vm_compute; discriminate].
        rewrite /Q5a upd_eq.
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
      repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate]. }
  Qed.

End WpSconfKfree.
