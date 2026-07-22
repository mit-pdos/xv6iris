(* WpSconfAcquire.v: acquire over the SIE-agnostic v2 bundle (stage 8).
   The amoswap spin loop is the Löb piece: the c.bnez-taken back edge
   hands the step's later out, which strips the IH.  The main lemma
   (next) composes push_off (the flip: the interrupts-off region BEGINS
   here) + the holding-not-mine check + the loop + lk->cpu := mycpu.  *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
From Stdlib Require Import FunctionalExtensionality.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfLock.
Require Import WpLock WpAmo KernelRvcDecode.
Require Import SpecMycpu SpecHolding.
Require Import SpecPushOff.
Require Import WpAcquireTop.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecAcquire.
Import Defs.


Module AcquireProof (Mycpu : MYCPU) (Holding : HOLDING) (PushOff : PUSHOFF) : ACQUIRE.

Section WpSconfAcquire.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The amoswap spin loop (AQ+0x1a..0x22) over the funnel leaves: a      *)
  (* genuine Löb loop -- the c.bnez back edge hands its step's later out. *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_acquire_lock_loop_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γl : gname) (s : string) (R : iProp Σ)
      (M0 : regfile) (n : nat) (a5v lk : mword 64) :
    let a4one : mword 64 := add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) in
    M0 !!! Regidx (mword_of_int 14 : mword 5) = a4one ->
    M0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0) n -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (AQ + 0x1a)) -∗
    is_lock γl lk s R -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (mword_of_int (AQ + 0x24)) -∗
      locked γl -∗ R -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros a4one HM0a4 HM0s1.
    assert (Ha4any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 14 : mword 5) = a4one).
    { intro w. rewrite upd_ne; [ exact HM0a4 | vm_compute; discriminate ]. }
    assert (Hs1any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { intro w. rewrite upd_ne; [ exact HM0s1 | vm_compute; discriminate ]. }
    assert (HAlk2 : add_vec (add_vec zero_reg lk) (zeros' 64) = lk).
    { rewrite aq_addv_zero_l.
      replace (zeros' 64 : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    set (v1 := add_vec zero_reg a4one).
    assert (Hst1 : amoswap_stored v1 = (mword_of_int 1 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Htgt : add_vec (mword_of_int (AQ + 0x22) : mword 64)
              (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
            = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc #Hlock Hcont".
    iPoseProof (aqi_1a with "Htext") as "#Hj1a".
    iPoseProof (aqi_1c with "Htext") as "#Hj1c".
    iPoseProof (aqi_20 with "Htext") as "#Hj20".
    iPoseProof (aqi_22 with "Htext") as "#Hj22".
    iRevert "Hsc Hhs Hcg Htlbinv Hpc Hcont".
    iLöb as "IH" forall (a5v).
    iIntros "Hsc Hhs Hcg Htlbinv Hpc Hcont".
    (* ---- +0x1a: c.mv a5,a4 ---- *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0) n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hj1a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite (Ha4any a5v) upd_upd) in "Hcg".
    assert (Hpp1c : add_vec_int (mword_of_int (AQ + 0x1a) : mword 64) 2 = mword_of_int (AQ + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- +0x1c: amoswap.w.aq a5,a5,(s1) through the invariant ---- *)
    assert (HPAlk : add_vec ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
                              !!! Regidx (mword_of_int 9 : mword 5)) (zeros' 64) = lk)
      by (rewrite (Hs1any v1); exact HAlk2).
    assert (HSTZ : neq_vec (sign_extend' 64 (amoswap_stored
                     ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
                        !!! Regidx (mword_of_int 15 : mword 5)))) zero_reg = true)
      by (rewrite upd_eq Hst1; vm_compute; reflexivity).
    iApply (wp_amoswap_lockinv_s_sconf γ root_ppn Φ γl lk s R (mword_of_int (AQ + 0x1c)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 9)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0) n
              HPAlk HSTZ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hj1c Hlock [-]").
    iIntros (w) "Hhs Hsc Hcg Htlbinv Hpc Hpay".
    iEval (rewrite upd_upd) in "Hcg".
    assert (Hpp20 : add_vec_int (mword_of_int (AQ + 0x1c) : mword 64) 4 = mword_of_int (AQ + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ---- +0x20: sext.w a5 ---- *)
    iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (amoswap_loaded w)]> M0) n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hj20 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite upd_eq upd_upd) in "Hcg".
    assert (Hroundw : sign_extend' 64 (subrange_vec_dec
        (add_vec (amoswap_loaded w) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)
        = sign_extend' 64 w) by (apply aq_sextw_round).
    iEval (rewrite Hroundw) in "Hcg".
    assert (Hpp22 : add_vec_int (mword_of_int (AQ + 0x20) : mword 64) 2 = mword_of_int (AQ + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    iDestruct "Hpay" as "[(%Hw0 & Htok & HRes) | %Hwnz]".
    - (* ---- w = 0: ACQUIRED -- c.bnez falls through ---- *)
      subst w.
      iApply (wp_cbnez_fall_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x22)) (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0) n
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite upd_eq; vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hj22 [-]").
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      assert (Hpp24 : add_vec_int (mword_of_int (AQ + 0x22) : mword 64) 2 = mword_of_int (AQ + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      iApply ("Hcont" with "Hhs Hsc Hcg Htlbinv Hpc Htok HRes").
    - (* ---- w <> 0: c.bnez TAKEN back; Löb ---- *)
      iApply (wp_cbnez_taken_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x22)) (mword_of_int 252 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 w)]> M0) n
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite upd_eq; exact Hwnz)
                ltac:(rewrite Htgt; vm_compute; reflexivity)
                with "Hsc Hhs Hcg Htlbinv Hpc Hj22 [-]").
      iNext.
      iIntros "Hhs Hsc Hcg Htlbinv Hpc".
      iEval (rewrite Htgt) in "Hpc".
      iApply ("IH" $! (sign_extend' 64 w)
                with "Hsc Hhs Hcg Htlbinv Hpc Hcont").
  Qed.

  Lemma wp_acquire_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γl : gname) (s : string) (R : iProp Σ)
      (m : regfile)
      (cpuold : mword 64) (noffv intena_old : mword 32) (n : nat) (av : nat)
    : wp_acquire_sconf_body γ root_ppn Φ γl s R m cpuold noffv intena_old n av.
  Proof.
    cbv beta delta [wp_acquire_sconf_body].
    intros pcE lk0 a_cpu cpuv a_noff a_int po_noff_a5 po_noff_store ret_tgt Hnotmine Hal0 Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hsc Hhs Hcg Hcnt Htlbinv #Htext Hpc #Hlock Hcpu Hnoff Hint Hcont".
    iPoseProof (aqi_00 with "Htext") as "Hi00".
    iPoseProof (aqi_02 with "Htext") as "Hi02".
    iPoseProof (aqi_04 with "Htext") as "Hi04".
    iPoseProof (aqi_06 with "Htext") as "Hi06".
    iPoseProof (aqi_08 with "Htext") as "Hi08".
    iPoseProof (aqi_0a with "Htext") as "Hi0a".
    iPoseProof (aqi_0c with "Htext") as "Hi0c".
    (* ---- 0x00: c.addi sp,-32 -- the frame trade (k := 4) ---- *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd)
      by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE (mword_of_int 32 : mword 6) m av 4 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (AQ + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- 0x02/0x04/0x06: c.sdsp ra/s0/s1 ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24
              with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (AQ + 0x02) : mword 64) 2 = mword_of_int (AQ + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16
              with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (AQ + 0x04) : mword 64) 2 = mword_of_int (AQ + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (AQ + 0x06) : mword 64) 2 = mword_of_int (AQ + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (AQ + 0x08) : mword 64) 2 = mword_of_int (AQ + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              A1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1) with A2.
    assert (Hpc0c : add_vec_int (mword_of_int (AQ + 0x0a) : mword 64) 2 = mword_of_int (AQ + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* ---- 0x0c: jal ra,push_off ---- *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fffba : mword 21)
              A2 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (A3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2) with A3.
    assert (Hpcpo : add_vec (mword_of_int (AQ + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 0x1fffba : mword 21))
                    = mword_of_int KernelSyms.push_off) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcpo) in "Hpc".
    (* ---- push_off(): the flip -- the interrupts-off region begins ---- *)
    assert (HtpA3 : A3 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HcspA3 : A3 !!! Regidx csp_rs1 = spd).
    { rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      exact HcspA0. }
    iApply (PushOff.wp_push_off_sconf γ root_ppn Φ A3 (av - 4)%nat noffv intena_old cpuv n
              ltac:(rewrite upd_eq; vm_compute; reflexivity)
              ltac:(rewrite HtpA3; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Hcnt Htlbinv Htext Hpc [Hnoff] [Hint] [-]").
    { iExact "Hnoff". }
    { iExact "Hint". }
    iIntros (ms mp) "%Hmsf Hhs Hsc Hcg Htlbinv Hpc %Hmp Hnoff Hint Hcnt".
    destruct Hmp as (Hcspp & Htpp & Hs0p & Hs1p & Hs2p & Hs3p & Hs4p & Hs5p & Hs6p & Hs7p & Hs8p & Hs9p & Hs10p & Hs11p).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc10 : update_vec_dec (add_vec (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (AQ + 0x10) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- 0x10: c.mv a0,s1 ---- *)
    iPoseProof (aqi_10 with "Htext") as "Hi10".
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mp (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 9 : mword 5)))]> mp).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec zero_reg (mp !!! Regidx (mword_of_int 9 : mword 5)))]> mp) with B1.
    assert (Hpc12 : add_vec_int (mword_of_int (AQ + 0x10) : mword 64) 2 = mword_of_int (AQ + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* s1 still carries the lock base through push_off *)
    assert (Hs1mp : mp !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk0).
    { rewrite Hs1p /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_eq /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HB1a0 : B1 !!! Regidx (mword_of_int 10 : mword 5) = add_vec zero_reg (add_vec zero_reg lk0)).
    { rewrite /B1 upd_eq Hs1mp. reflexivity. }
    (* ---- 0x12: jal ra,holding ---- *)
    iPoseProof (aqi_12 with "Htext") as "Hi12".
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff88 : mword 21)
              B1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi12 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (B2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4)]> B1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4)]> B1) with B2.
    assert (Hpchd : add_vec (mword_of_int (AQ + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff88 : mword 21))
                    = mword_of_int KernelSyms.holding) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpchd) in "Hpc".
    (* ---- holding(): not mine -> a0 := 0 ---- *)
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5) = add_vec zero_reg (add_vec zero_reg lk0))
      by (rewrite /B2 upd_ne; [exact HB1a0 | vm_compute; discriminate]).
    assert (HtpB2 : B2 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Htpp. exact HtpA3. }
    assert (HcspB2 : B2 !!! Regidx csp_rs1 = spd).
    { rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hcspp. exact HcspA3. }
    assert (Hlkb : add_vec (B2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk0).
    { rewrite HB2a0 !aq_addv_zero_l.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (Holding.wp_holding_lockinv_s_sconf γ root_ppn Φ γl lk0 s R B2 (av - 4)%nat cpuold (dqc := DfracOwn 1)
              Hlkb
              ltac:(rewrite HtpB2; exact Hnotmine)
              ltac:(rewrite upd_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc Hlock [Hcpu] [-]").
    { iEval (rewrite HB2a0 !aq_addv_zero_l). iExact "Hcpu". }
    iIntros (mh) "Hhs Hsc Hcg Htlbinv Hpc %Hmh Hcpu".
    iEval (rewrite HB2a0 !aq_addv_zero_l) in "Hcpu".
    destruct Hmh as [Hcsh Ha0h].
    destruct Hcsh as (Hcsph & Htph & Hs0h & Hs1h & Hs2h & Hs3h & Hs4h & Hs5h & Hs6h & Hs7h & Hs8h & Hs9h & Hs10h & Hs11h).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc16 : update_vec_dec (add_vec (add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (AQ + 0x16) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: c.li a4,1 ---- *)
    iPoseProof (aqi_16 with "Htext") as "Hi16".
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x16)) (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) mh (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi16 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (B3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mh).
    change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mh) with B3.
    assert (Hpc18 : add_vec_int (mword_of_int (AQ + 0x16) : mword 64) 2 = mword_of_int (AQ + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* ---- 0x18: c.bnez a0 falls (a0 = 0) ---- *)
    iPoseProof (aqi_18 with "Htext") as "Hi18".
    assert (Ha0B3 : neq_vec (B3 !!! Regidx (mword_of_int 10 : mword 5)) zero_reg = false).
    { rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Ha0h. vm_compute. reflexivity. }
    iApply (wp_cbnez_fall_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x18)) (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              B3 (av - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Ha0B3
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpc1a : add_vec_int (mword_of_int (AQ + 0x18) : mword 64) 2 = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- 0x1a..0x22: the test-and-set loop ---- *)
    assert (HB3a4 : B3 !!! Regidx (mword_of_int 14 : mword 5)
                    = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (rewrite /B3; apply upd_eq).
    assert (HB3s1 : B3 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk0).
    { rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs1h /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      exact Hs1mp. }
    assert (Hupd_id : forall (f : regfile) (k : regidx), <[k := regval_into_reg (f !!! k)]> f = f).
    { intros f k. apply functional_extensionality; intro j.
      unfold insert, regfile_insert, rf_upd, regval_into_reg, lookup_total, regfile_lookup_total.
      case_bool_decide as Heq; [subst; reflexivity | reflexivity]. }
    iApply (wp_acquire_lock_loop_sconf γ root_ppn Φ γl s R B3 (av - 4)%nat (B3 !!! Regidx (mword_of_int 15 : mword 5)) lk0
              HB3a4 HB3s1
              with "Hsc Hhs [Hcg] Htlbinv Htext Hpc Hlock [-]").
    { rewrite (Hupd_id B3 (Regidx (mword_of_int 15 : mword 5))). iExact "Hcg". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Htok HRes".
    set (B8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> B3).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> B3) with B8.
    (* ---- 0x24: jal ra,mycpu ---- *)
    assert (HcspB8 : B8 !!! Regidx csp_rs1 = spd).
    { rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hcsph. exact HcspB2. }
    iPoseProof (aqi_24 with "Htext") as "Hi24".
    iApply (Mycpu.wp_call_mycpu_sconf_cs γ root_ppn Φ (mword_of_int (AQ + 0x24)) (mword_of_int 0xcb8 : mword 21) B8 (av - 4)%nat
 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite upd_eq; vm_compute; reflexivity) ltac:(lia)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc Hi24 [-]").
    iIntros (mo) "Hhs Hsc Hcg Htlbinv Hpc %Hmo".
    set (C := mo).
    destruct Hmo as [Hcso Hmo_a0].
    destruct Hcso as (Hcspo & Htpo & Hs0o & Hs1o & Hs2o & Hs3o & Hs4o & Hs5o & Hs6o & Hs7o & Hs8o & Hs9o & Hs10o & Hs11o).
    assert (HtpB8 : B8 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Htph. exact HtpB2. }
    assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = cpuv)
      by (rewrite /C Hmo_a0 HtpB8; reflexivity).
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc28 : update_vec_dec (add_vec (add_vec_int (mword_of_int (AQ + 0x24) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (AQ + 0x28) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- 0x28: c.sd a0,16(s1) : lk->cpu := mycpu ---- *)
    assert (Hs1C : C !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk0).
    { rewrite /C Hs1o /B8 upd_ne; [| vm_compute; discriminate].
      exact HB3s1. }
    assert (Hpacpu : add_vec (C !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu).
    { rewrite Hs1C aq_addv_zero_l. reflexivity. }
    iPoseProof (aqi_28 with "Htext") as "Hi28".
    iApply (wp_csd_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x28)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 16 : mword 12) C (av - 4)%nat cpuold
              with "Hsc Hhs Hcg Htlbinv Hpc Hi28 [Hcpu] [-]").
    { iEval (rewrite Hpacpu). iExact "Hcpu". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hcpu".
    iEval (rewrite Hpacpu Ha0C) in "Hcpu".
    assert (Hpc2a : add_vec_int (mword_of_int (AQ + 0x28) : mword 64) 2 = mword_of_int (AQ + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- 0x2a/0x2c/0x2e: c.ldsp ra/s0/s1 ---- *)
    assert (HcspC : C !!! Regidx csp_rs1 = spd) by (rewrite /C Hcspo; exact HcspB8).
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0 HraA0) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0) in "Hr8".
    iPoseProof (aqi_2a with "Htext") as "Hi2a".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x2a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              C (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2a [Hr24] [-]").
    { iEval (rewrite HcspC). iExact "Hr24". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C) with E1.
    assert (Hpc2c : add_vec_int (mword_of_int (AQ + 0x2a) : mword 64) 2 = mword_of_int (AQ + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spd)
      by (rewrite /E1 upd_ne; [exact HcspC | vm_compute; discriminate]).
    iPoseProof (aqi_2c with "Htext") as "Hi2c".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x2c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2c [Hr16] [-]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (Hpc2e : add_vec_int (mword_of_int (AQ + 0x2c) : mword 64) 2 = mword_of_int (AQ + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    iPoseProof (aqi_2e with "Htext") as "Hi2e".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x2e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2e [Hr8] [-]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (Hpc30 : add_vec_int (mword_of_int (AQ + 0x2e) : mword 64) 2 = mword_of_int (AQ + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* ---- 0x30: c.addi16sp sp,32 -- the frame trade back ---- *)
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
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
    { rewrite Hwv HcspE3. symmetry. exact Hspd4. }
    iPoseProof (aqi_30 with "Htext") as "Hi30".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HcspC). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HcspE1). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HcspE2). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x30)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi30 Hframe4 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hpc32 : add_vec_int (mword_of_int (AQ + 0x30) : mword 64) 2 = mword_of_int (AQ + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc32) in "Hpc".
    (* ---- 0x32: c.ret ---- *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (E4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE4ra; exact Hal0).
    iPoseProof (aqi_32 with "Htext") as "Hi32".
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (AQ + 0x32)) (mword_of_int 1 : mword 5) E4 av
              ltac:(vm_compute; discriminate) Hal0'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hra_final : update_vec_dec (add_vec (E4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! ms E4 with "[%] Hhs Hsc Hcg Htlbinv Hpc [%] Htok HRes Hcpu Hnoff Hint Hcnt").
    { exact Hmsf. }
    unfold callee_saved. repeat split.
    + rewrite HE4sp. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Htpo. exact HtpB8.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs2o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs2h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs2p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs3o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs3h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs3p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs4o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs4h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs4p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs5o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs5h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs5p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs6o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs6h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs6p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs7o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs7h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs7p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs8o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs8h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs8p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs9o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs9h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs9p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs10o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs10h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs10p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
    + do 4 (rewrite upd_ne; [| vm_compute; discriminate]).
      rewrite /C Hs11o.
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite Hs11h.
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite Hs11p.
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. reflexivity.
  Qed.

End WpSconfAcquire.

End AcquireProof.
