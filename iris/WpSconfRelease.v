(* WpSconfRelease.v: release over the SIE-agnostic v2 bundle (stage 8).

   release = holding-check (the lock token forces a0=1), lk->cpu := 0,
   fence, the lock-word clear (locked ∗ R re-enter the invariant), then
   pop_off -- the FIRST composition that threads push_off's payload
   disjunct end-to-end: release's caller hands the intenav-keyed input
   (built from push_off's post via WpIntenaBits), pop_off's restore may
   genuinely re-enable interrupts, and the conditional payload flows
   back out through release's post.

   Deep custody: 10 slots below the entry carve -- 4 traded for
   release's own frame, 6 riding for holding (which trades 4 + rides 2
   for mycpu), of which 4 are re-lent to pop_off.                       *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfLock.
Require Import WpLock KernelRvcDecode.
Require Import WpMycpu WpSconfHolding.
Require Import WpSconfPushOff.
Require Import WpRelease.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation RL := KernelSyms.release.

Local Lemma addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  assert (add_vec_unsigned : forall a b : mword 64,
            bv_unsigned (add_vec a b) = bv_wrap 64 (bv_unsigned a + bv_unsigned b)).
  { intros a b. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite add_vec_unsigned.
  change (bv_unsigned (zero_reg : mword 64)) with 0%Z. rewrite Z.add_0_l.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Section WpSconfRelease.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_release_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γl : gname) (lka : mword 64) (R : iProp Σ)
      (m : regfile)
      (cpuold : mword 64) (noffv intenav : mword 32) (n : nat) (av : nat) {dqi : dfrac} :
    let pcE : mword 64 := mword_of_int RL in
    let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
    let a_cpu := add_vec lk0 (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let sp0 := m !!! Regidx csp_rs1 in
    let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
    let storeval_noff := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
    eq_vec cpuold cpuv = true ->
    (neq_vec nv1 zero_reg = false <-> n = 0%nat) ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    (10 <= av)%nat ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m av -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is pcE -∗
    is_lock γl lka R -∗
    locked γl -∗
    R -∗
    a_cpu ↦₈ cpuold -∗
    a_noff ↦₄ noffv -∗
    a_int ↦₄{ dqi } intenav -∗
    intr_count γ root_ppn (S n) -∗
    ( ∀ mr,
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap_gpr γ root_ppn mr av -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mr ⌝ -∗
      a_cpu ↦₈ (zero_reg : mword 64) -∗
      a_noff ↦₄ storeval_noff -∗
      a_int ↦₄{ dqi } intenav -∗
      intr_count γ root_ppn n -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE lk0 a_cpu sp0 cpuv a_noff a_int nv1 storeval_noff ret_tgt
           Hlka Hmine Hcoup Hnoffpos Hal0 Hav.
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc #Hlock Htoken HR Hcpu Hnoff Hint Hcnt Hcont".
    iPoseProof (rli_00 with "Htext") as "Hi00".
    iPoseProof (rli_02 with "Htext") as "Hi02".
    iPoseProof (rli_04 with "Htext") as "Hi04".
    iPoseProof (rli_06 with "Htext") as "Hi06".
    iPoseProof (rli_08 with "Htext") as "Hi08".
    iPoseProof (rli_0a with "Htext") as "Hi0a".
    iPoseProof (rli_0c with "Htext") as "Hi0c".
    (* ---- 0x00: c.addi sp,-32 -- the frame trade (k := 4) ---- *)
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (R0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspR0 : R0 !!! Regidx csp_rs1 = spr)
      by (rewrite /R0 upd_eq; reflexivity).
    assert (Hspr4 : pa_stk sp0 4 = spr).
    { rewrite /spr. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE (mword_of_int 32 : mword 6) m av 4 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (RL + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spr. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x02/0x04/0x06: c.sdsp ra/s0/s1 ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R0 (av - 4)%nat vr24
              with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspR0 -Hb1). iExact "Hr24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (RL + 0x02) : mword 64) 2 = mword_of_int (RL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R0 (av - 4)%nat vr16
              with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspR0 -Hb2). iExact "Hr16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (RL + 0x04) : mword 64) 2 = mword_of_int (RL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R0 (av - 4)%nat vr8
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspR0 -Hb3). iExact "Hr8". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (RL + 0x06) : mword 64) 2 = mword_of_int (RL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R0 (av - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R0) with R1.
    assert (Hpc0a : add_vec_int (mword_of_int (RL + 0x08) : mword 64) 2 = mword_of_int (RL + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (R1 !!! Regidx (mword_of_int 10 : mword 5)))]> R1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (R1 !!! Regidx (mword_of_int 10 : mword 5)))]> R1) with R2.
    assert (Hpc0c : add_vec_int (mword_of_int (RL + 0x0a) : mword 64) 2 = mword_of_int (RL + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* ---- 0x0c: jal ra,holding ---- *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff06 : mword 21)
              R2 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RL + 0x0c) : mword 64) 4)]> R2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RL + 0x0c) : mword 64) 4)]> R2) with R3.
    assert (Hpchd : add_vec (mword_of_int (RL + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff06 : mword 21))
                    = mword_of_int KernelSyms.holding) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpchd) in "Hpc".
    (* ---- holding(): the token forces the slow path, a0 := 1 ---- *)
    assert (Ha0R3 : R3 !!! Regidx (mword_of_int 10 : mword 5) = lk0).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HtpR3 : R3 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HcspR3 : R3 !!! Regidx csp_rs1 = spr).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      exact HcspR0. }
    iApply (wp_holding_lockinv_locked_s_sconf γ root_ppn Φ γl lka R R3 (av - 4)%nat cpuold (dqc := DfracOwn 1)
              ltac:(rewrite Ha0R3; exact Hlka)
              ltac:(rewrite HtpR3; exact Hmine)
              ltac:(rewrite upd_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc Hlock Htoken [Hcpu] [-]").
    { iEval (rewrite Ha0R3). iExact "Hcpu". }
    iIntros (mh) "Hhs Hsc Hcg Htlbinv Hpc %Hmh Htoken Hcpu".
    iEval (rewrite Ha0R3) in "Hcpu".
    destruct Hmh as [Hcsh Ha0h].
    destruct Hcsh as (Hcsph & Htph & Hs0h & Hs1h & Hs2h & Hs3h & Hs4h & Hs5h & Hs6h & Hs7h & Hs8h & Hs9h & Hs10h & Hs11h).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc10 : update_vec_dec (add_vec (add_vec_int (mword_of_int (RL + 0x0c) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (RL + 0x10) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: c.beqz a0 falls (a0 = 1) ---- *)
    iPoseProof (rli_10 with "Htext") as "Hi10".
    assert (Ha0mh : eq_vec (mh !!! Regidx (mword_of_int 10 : mword 5)) zero_reg = false)
      by (rewrite Ha0h; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x10)) (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mh (av - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Ha0mh
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpc12 : add_vec_int (mword_of_int (RL + 0x10) : mword 64) 2 = mword_of_int (RL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- 0x12: sd zero,16(s1) : lk->cpu := 0 ---- *)
    assert (Hs1mh : mh !!! Regidx (mword_of_int 9 : mword 5) = lk0).
    { rewrite Hs1h /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_eq /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate].
      apply addv_zero_l. }
    iPoseProof (rli_12 with "Htext") as "Hi12".
    iApply (wp_sd_zero_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x12)) (mword_of_int 9 : mword 5)
              (mword_of_int 16 : mword 12) mh (av - 4)%nat cpuold
              with "Hsc Hhs Hcg Htlbinv Hpc Hi12 [Hcpu] [-]").
    { iEval (rewrite Hs1mh). iExact "Hcpu". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hcpu".
    iEval (rewrite Hs1mh) in "Hcpu".
    assert (Hpc16 : add_vec_int (mword_of_int (RL + 0x12) : mword 64) 4 = mword_of_int (RL + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: fence rw,w ---- *)
    iPoseProof (rli_16 with "Htext") as "Hi16".
    iApply (wp_fence_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x16)) mh (av - 4)%nat
              with "Hsc Hhs Hcg Htlbinv Hpc Hi16 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (RL + 0x16) : mword 64) 4 = mword_of_int (RL + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a: sw zero,0(s1) : the lock word clears ---- *)
    iPoseProof (rli_1a with "Htext") as "Hi1a".
    iApply (wp_sw_zero_lockinv_s_sconf γ root_ppn Φ γl lka R (mword_of_int (RL + 0x1a)) (mword_of_int 9 : mword 5)
              (mword_of_int 0 : mword 12) mh (av - 4)%nat
              ltac:(rewrite Hs1mh; exact Hlka)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1a Hlock Htoken HR [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpc1e : add_vec_int (mword_of_int (RL + 0x1a) : mword 64) 4 = mword_of_int (RL + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- 0x1e: jal ra,pop_off ---- *)
    iPoseProof (rli_1e with "Htext") as "Hi1e".
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff9a : mword 21)
              mh (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (M1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RL + 0x1e) : mword 64) 4)]> mh).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RL + 0x1e) : mword 64) 4)]> mh) with M1.
    assert (Hpcpp : add_vec (mword_of_int (RL + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff9a : mword 21))
                    = mword_of_int KernelSyms.pop_off) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcpp) in "Hpc".
    (* ---- pop_off(): the payload threads through ---- *)
    assert (HtpM1 : M1 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Htph. exact HtpR3. }
    assert (HcspM1 : M1 !!! Regidx csp_rs1 = spr).
    { rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hcsph. exact HcspR3. }
    iApply (wp_pop_off_sconf γ root_ppn Φ M1 (av - 4)%nat noffv intenav n (dqi := dqi)
              Hcoup Hnoffpos
              ltac:(rewrite upd_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc [Hnoff] [Hint] [-]").
    { iEval (rewrite HtpM1). iExact "Hnoff". }
    { iEval (rewrite HtpM1). iExact "Hint". }
    iIntros (mf) "Hhs Hsc Hcg Hcnt Htlbinv Hpc %Hmf Hnoff Hint".
    iEval (rewrite HtpM1) in "Hnoff".
    iEval (rewrite HtpM1) in "Hint".
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc22 : update_vec_dec (add_vec (add_vec_int (mword_of_int (RL + 0x1e) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (RL + 0x22) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    destruct Hmf as (Hcspf & Htpf & Hs0f & Hs1f & Hs2f & Hs3f & Hs4f & Hs5f & Hs6f & Hs7f & Hs8f & Hs9f & Hs10f & Hs11f).
    assert (Hcspmf : mf !!! Regidx csp_rs1 = spr) by (rewrite Hcspf; exact HcspM1).
    (* the frame cells hold the entry values *)
    assert (HraR0 : R0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0R0 : R0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1R0 : R0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /R0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspR0 HraR0) in "Hr24".
    iEval (rewrite HcspR0 Hs0R0) in "Hr16".
    iEval (rewrite HcspR0 Hs1R0) in "Hr8".
    (* ---- 0x22/0x24/0x26: c.ldsp ra/s0/s1 ---- *)
    iPoseProof (rli_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x22)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mf (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi22 [Hr24] [-]").
    { iEval (rewrite Hcspmf). iExact "Hr24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mf).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mf) with E1.
    assert (Hpc24 : add_vec_int (mword_of_int (RL + 0x22) : mword 64) 2 = mword_of_int (RL + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spr)
      by (rewrite /E1 upd_ne; [exact Hcspmf | vm_compute; discriminate]).
    iPoseProof (rli_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x24)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi24 [Hr16] [-]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc26 : add_vec_int (mword_of_int (RL + 0x24) : mword 64) 2 = mword_of_int (RL + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spr)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    iPoseProof (rli_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x26)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi26 [Hr8] [-]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc28 : add_vec_int (mword_of_int (RL + 0x26) : mword 64) 2 = mword_of_int (RL + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.addi16sp sp,32 -- the frame trade back ---- *)
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spr)
      by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spr (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spr /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HE4sp : E4 !!! Regidx csp_rs1 = sp0).
    { rewrite /E4 upd_eq HcspE3. exact Hsp0up. }
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HcspE3. exact Hsp0up. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HcspE3. symmetry. exact Hspr4. }
    iPoseProof (rli_28 with "Htext") as "Hi28".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -Hcspmf). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x28)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi28 Hframe4 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc2a : add_vec_int (mword_of_int (RL + 0x28) : mword 64) 2 = mword_of_int (RL + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a: c.ret ---- *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (E4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE4ra; exact Hal0).
    iPoseProof (rli_2a with "Htext") as "Hi2a".
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (RL + 0x2a)) (mword_of_int 1 : mword 5) E4 av
              ltac:(vm_compute; discriminate) Hal0'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hra_final : update_vec_dec (add_vec (E4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! E4 with "Hhs Hsc Hcg Htlbinv Hpc [%] Hcpu Hnoff Hint Hcnt").
    unfold callee_saved. repeat split.
    + rewrite HE4sp. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Htpf. exact HtpM1.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs2f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs2h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs3f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs3h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs4f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs4h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs5f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs5h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs6f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs6h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs7f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs7h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs8f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs8h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs9f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs9h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs10f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs10h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite Hs11f.
      rewrite /M1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs11h.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite /R0 upd_ne; [| vm_compute; discriminate]. reflexivity.
  Qed.

End WpSconfRelease.
