(* ProofReleasesleep.v -- releasesleep over the SIE-agnostic sconf world.

   releasesleep(slk) @ 0x80003f12 (56 bytes, 32-byte 4-register frame
   ra/s0/s1/s2).  Straight-line, no branches:

     prologue (push frame, save ra/s0/s1/s2, s0:=sp+32)
     s1 := a0 (= slk) / s2 := a0+8 (= &slk->lk = sl_lk slk)
     a0 := s2 ; jal acquire            (take the inner spinlock)
     sw zero,0(s1)                     (slk->locked := 0)
     sw zero,40(s1)                    (slk->pid := 0)
     a0 := s1 (= slk) ; jal wakeup     (wake sleepers on the sleeplock chan)
     a0 := s2 ; jal release            (drop the inner spinlock)
     epilogue (restore, pop frame, ret)

   Mirrors ProofKfree (same frame, acquire..release skeleton), with the
   wakeup loop and two zero-stores in place of kfree's freelist push, and the
   sleeplock resource shuffle: acquire re-hands [sl_res] back, the holder's
   token refutes its free arm (sl_res_open_held), the two stores zero the
   word and pid, and release rebuilds the FREE [sl_res] (sl_res_close_free).
   The per-cpu noff/intena cells thread net-zero across the acquire/release
   pair (with wakeup's own acquire/release pairs net-zero internally); the
   counting token goes 0 ->(acquire) 1 ->(release) 0. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpMmodeLeafBase SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import WpLock WpMycpu.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import ProcGeom.
Require Import WpWakeup.
Require Import SleepLock.
Require Import WpSleeplockDecode.
Require Import SpecAcquire SpecRelease SpecWakeup.
Require Import SpecReleasesleep.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure reconciliation lemmas (closed, so vm_compute decides).           *)
(* ===================================================================== *)

Module ReleasesleepProof (Acquire : ACQUIRE) (Release : RELEASE) (Wakeup : WAKEUP) : RELEASESLEEP.

Section ProofReleasesleep.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_releasesleep_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat) (eb : bool) (C : iProp Σ)
    : wp_releasesleep_sconf_body γ Φ γs γl γsl s R m pd pme av eb C.
  Proof.
    cbv beta delta [wp_releasesleep_sconf_body].
    intros pcE slk ret_tgt Htp Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    assert (Hcpune : eq_vec (zero_reg : mword 64) (mycpu_ret cid_word) = false)
      by (apply mycpu_ret_nonzero; apply tp_ok_cid).
    iIntros "Hcg Hown #Htext Hpc #Hslp Hslk Hpid HRcaller #Hpanic #Hpinv Hcont".
    iDestruct (is_sleeplock_lock with "Hslp") as "#Hlockinv".
    iAssert (⌜length γs = NPROC⌝)%I as %Hlen.
    { iDestruct "Hpinv" as "[%Hl _]". iPureIntro. exact Hl. }
    iPoseProof (rsl_00 with "Htext") as "Hi00".
    iPoseProof (rsl_02 with "Htext") as "Hi02".
    iPoseProof (rsl_04 with "Htext") as "Hi04".
    iPoseProof (rsl_06 with "Htext") as "Hi06".
    iPoseProof (rsl_08 with "Htext") as "Hi08".
    iPoseProof (rsl_0a with "Htext") as "Hi0a".
    (* ===== PROLOGUE: 4-slot frame push + saves ra/s0/s1/s2 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE (mword_of_int 32 : mword 6) m av 4 ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 upd_eq; reflexivity).
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
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (RSL + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (RSL + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 (av - 4)%nat vr24 with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (RSL + 0x02) : mword 64) 2 = mword_of_int (RSL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (RSL + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (av - 4)%nat vr16 with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (RSL + 0x04) : mword 64) 2 = mword_of_int (RSL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (RSL + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (av - 4)%nat vr8 with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (RSL + 0x06) : mword 64) 2 = mword_of_int (RSL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (RSL + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 (av - 4)%nat vr0 with "Hcg Hpc Hi08 Hr0 [-]").
    iIntros "Hcg Hpc Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (RSL + 0x08) : mword 64) 2 = mword_of_int (RSL + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (RSL + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1) with R2.
    assert (Hpp0c : add_vec_int (mword_of_int (RSL + 0x0a) : mword 64) 2 = mword_of_int (RSL + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== s1 := a0 (slk) ; s2 := a0+8 (sl_lk slk) ; a0 := s2 ===== *)
    iPoseProof (rsl_0c with "Htext") as "Hi0c".
    iPoseProof (rsl_0e with "Htext") as "Hi0e".
    iPoseProof (rsl_12 with "Htext") as "Hi12".
    iPoseProof (rsl_14 with "Htext") as "Hi14".
    (* +0x0c c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (RSL + 0x0c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R2 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    set (A_s1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    assert (Hpp0e : add_vec_int (mword_of_int (RSL + 0x0c) : mword 64) 2 = mword_of_int (RSL + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HA_s1_a0 : A_s1 !!! Regidx (mword_of_int 10 : mword 5) = slk).
    { rewrite /A_s1 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    (* +0x0e addi s2,a0,8 *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (RSL + 0x0e)) (mword_of_int 18 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 8 : mword 12)
              A_s1 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    set (A_s2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (A_s1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> A_s1).
    assert (Hpp12 : add_vec_int (mword_of_int (RSL + 0x0e) : mword 64) 4 = mword_of_int (RSL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    assert (HA_s2_s2 : A_s2 !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /A_s2 upd_eq. rewrite HA_s1_a0. reflexivity. }
    (* +0x12 c.mv a0,s2 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (RSL + 0x12)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              A_s2 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (A_a0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (A_s2 !!! Regidx (mword_of_int 18 : mword 5)))]> A_s2).
    assert (Hpp14 : add_vec_int (mword_of_int (RSL + 0x12) : mword 64) 2 = mword_of_int (RSL + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    assert (HA_a0_a0 : A_a0 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /A_a0 upd_eq. rewrite HA_s2_s2. apply add_vec_zero_l. }
    (* +0x14 jal ra,acquire *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (RSL + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2084066 : mword 21)
              A_a0 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (Kacq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RSL + 0x14) : mword 64) 4)]> A_a0).
    assert (Htgtacq : add_vec (mword_of_int (RSL + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2084066 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HKacqa0 : Kacq !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate]. exact HA_a0_a0. }
    assert (HKacqra : Kacq !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (RSL + 0x14) : mword 64) 4)
      by (rewrite /Kacq; apply upd_eq).
    assert (HKacqtp : Kacq !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /A_a0 upd_ne; [| vm_compute; discriminate].
      rewrite /A_s2 upd_ne; [| vm_compute; discriminate].
      rewrite /A_s1 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Htp | vm_compute; discriminate]. }
    assert (HKacqs1 : Kacq !!! Regidx (mword_of_int 9 : mword 5) = slk).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /A_a0 upd_ne; [| vm_compute; discriminate].
      rewrite /A_s2 upd_ne; [| vm_compute; discriminate].
      rewrite /A_s1 upd_eq.
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      rewrite add_vec_zero_l. reflexivity. }
    assert (HKacqs2 : Kacq !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /A_a0 upd_ne; [| vm_compute; discriminate].
      exact HA_s2_s2. }
    (* ===== acquire(&slk->lk): intr_count 0 -> 1, returns sl_res + locked ===== *)
    iApply (Acquire.wp_acquire_sconf γ Φ γl "sleep lock"%string (sl_res γsl slk R) Kacq
              0%nat eb pme C (av - 4)%nat
              HKacqtp
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hown Htext Hpc [] Hpanic [-]").
    { iEval (rewrite HKacqa0). iExact "Hlockinv". }
    iIntros (ms Macq) "%Hms Hcg Hpc %Hpins HtokL HRsl Hown Hpay".
    assert (Hpc18 : ret_pc (Kacq !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (RSL + 0x18)).
    { rewrite HKacqra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc18) in "Hpc".
    (* s1 preserved by acquire (callee_saved). *)
    assert (HMacqs1 : Macq !!! Regidx (mword_of_int 9 : mword 5) = slk).
    { rewrite (callee_saved_lookup Hpins (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HKacqs1. }
    assert (HMacqs2 : Macq !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite (callee_saved_lookup Hpins (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact HKacqs2. }
    (* open sl_res as the holder: the token refutes the free arm. *)
    iDestruct (sl_res_open_held γsl slk R with "HRsl Hslk") as "[Hslk Hcell]".
    iDestruct "Hcell" as (v) "[Hslkw %Hnz]".
    (* ===== sw zero,0(s1) : slk->locked := 0 ===== *)
    iPoseProof (rsl_18 with "Htext") as "Hi18".
    iApply (wp_sw_zero_s_sconf γ Φ (mword_of_int (RSL + 0x18)) (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12) Macq (av - 4)%nat v
              with "Hcg Hpc Hi18 [Hslkw] [-]").
    { iEval (rewrite HMacqs1 wk_add_vec_0). iExact "Hslkw". }
    iIntros "Hcg Hpc Hslkw".
    iEval (rewrite HMacqs1 wk_add_vec_0) in "Hslkw".
    assert (Hpp1c : add_vec_int (mword_of_int (RSL + 0x18) : mword 64) 4 = mword_of_int (RSL + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== sw zero,40(s1) : slk->pid := 0 ===== *)
    iPoseProof (rsl_1c with "Htext") as "Hi1c".
    iApply (wp_sw_zero_s_sconf γ Φ (mword_of_int (RSL + 0x1c)) (mword_of_int 9 : mword 5) (mword_of_int 0x28 : mword 12) Macq (av - 4)%nat pd
              with "Hcg Hpc Hi1c [Hpid] [-]").
    { iEval (rewrite HMacqs1). iExact "Hpid". }
    iIntros "Hcg Hpc Hpid".
    iEval (rewrite HMacqs1) in "Hpid".
    assert (Hpp20 : add_vec_int (mword_of_int (RSL + 0x1c) : mword 64) 4 = mword_of_int (RSL + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ===== a0 := s1 (slk) ; jal wakeup ===== *)
    iPoseProof (rsl_20 with "Htext") as "Hi20".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (RSL + 0x20)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              Macq (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi20 [-]").
    iIntros "Hcg Hpc".
    set (A_wa0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Macq !!! Regidx (mword_of_int 9 : mword 5)))]> Macq).
    assert (Hpp22 : add_vec_int (mword_of_int (RSL + 0x20) : mword 64) 2 = mword_of_int (RSL + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    iPoseProof (rsl_22 with "Htext") as "Hi22".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (RSL + 0x22)) (mword_of_int 1 : mword 5) (mword_of_int 2088990 : mword 21)
              A_wa0 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi22 [-]").
    iIntros "Hcg Hpc".
    set (Cwk := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RSL + 0x22) : mword 64) 4)]> A_wa0).
    assert (Htgtwk : add_vec (mword_of_int (RSL + 0x22) : mword 64) (sign_extend' 64 (mword_of_int 2088990 : mword 21)) = mword_of_int KernelSyms.wakeup)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwk) in "Hpc".
    assert (HCwkra : Cwk !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (RSL + 0x22) : mword 64) 4)
      by (rewrite /Cwk; apply upd_eq).
    assert (HCwktp : Cwk !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /Cwk upd_ne; [| vm_compute; discriminate].
      rewrite /A_wa0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hpins (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HKacqtp. }
    (* ===== wakeup(slk): intr_count 1 (unchanged net), noff/intena threaded ===== *)
    iApply (Wakeup.wp_wakeup_sconf γ Φ Cwk γs (mycpu_ret cid_word) pme 1%nat (av - 4)%nat eb C
              ltac:(lia)
              ltac:(intro r; apply rf_to_gmap_dom)
              Hlen
              HCwktp
              ltac:(rewrite HCwktp; reflexivity)
              ltac:(rewrite HCwktp; exact Hcpune)
              ltac:(lia)
              with "Hcg Hown Htext Hpc Hpanic Hpinv [-]").
    iIntros (Mwk) "[%Hwkcs %Hwkdom] Hcg Hown Htext2 Hpc".
    assert (Hpc26 : ret_pc (Cwk !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (RSL + 0x26)).
    { rewrite HCwkra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc26) in "Hpc".
    assert (HMwks2 : Mwk !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite (callee_saved_lookup Hwkcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /Cwk upd_ne; [| vm_compute; discriminate].
      rewrite /A_wa0 upd_ne; [| vm_compute; discriminate].
      exact HMacqs2. }
    (* ===== a0 := s2 (sl_lk slk) ; jal release ===== *)
    iPoseProof (rsl_26 with "Htext") as "Hi26".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (RSL + 0x26)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              Mwk (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi26 [-]").
    iIntros "Hcg Hpc".
    set (A_ra0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Mwk !!! Regidx (mword_of_int 18 : mword 5)))]> Mwk).
    assert (Hpp28 : add_vec_int (mword_of_int (RSL + 0x26) : mword 64) 2 = mword_of_int (RSL + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    iPoseProof (rsl_28 with "Htext") as "Hi28".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (RSL + 0x28)) (mword_of_int 1 : mword 5) (mword_of_int 2084182 : mword 21)
              A_ra0 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi28 [-]").
    iIntros "Hcg Hpc".
    set (Krel := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RSL + 0x28) : mword 64) 4)]> A_ra0).
    assert (Htgtrel : add_vec (mword_of_int (RSL + 0x28) : mword 64) (sign_extend' 64 (mword_of_int 2084182 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HKrela0 : Krel !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /Krel upd_ne; [| vm_compute; discriminate].
      rewrite /A_ra0 upd_eq. rewrite HMwks2. apply add_vec_zero_l. }
    assert (HKrelra : Krel !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (RSL + 0x28) : mword 64) 4)
      by (rewrite /Krel; apply upd_eq).
    assert (HKreltp : Krel !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /Krel upd_ne; [| vm_compute; discriminate].
      rewrite /A_ra0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hwkcs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HCwktp. }
    assert (HKrelsp : Krel !!! Regidx csp_rs1 = spr).
    { rewrite /Krel upd_ne; [| vm_compute; discriminate].
      rewrite /A_ra0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hwkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Cwk upd_ne; [| vm_compute; discriminate].
      rewrite /A_wa0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hpins csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /Kacq upd_ne; [| vm_compute; discriminate].
      rewrite /A_a0 upd_ne; [| vm_compute; discriminate].
      rewrite /A_s2 upd_ne; [| vm_compute; discriminate].
      rewrite /A_s1 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_eq. reflexivity. }
    (* rebuild the FREE sl_res: zeroed word + token + zeroed pid + R. *)
    iDestruct (sl_res_close_free γsl slk R with "Hslkw Hslk Hpid HRcaller") as "HRsl".
    (* release(&slk->lk): intr_count 1 -> 0. *)
    iApply (Release.wp_release_sconf γ Φ γl (sl_lk slk) "sleep lock"%string (sl_res γsl slk R) Krel
              0%nat eb pme C (av - 4)%nat
              ltac:(rewrite HKrela0; apply wk_add_vec_0)
              HKreltp
              ltac:(lia)
              with "Hcg Htext Hpc [] HtokL HRsl Hown Hpay [-]").
    { iExact "Hlockinv". }
    iIntros (Mrel) "Hcg Hpc %Hrelcs Hown".
    assert (Hpc2c : ret_pc (Krel !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (RSL + 0x2c)).
    { rewrite HKrelra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc2c) in "Hpc".
    assert (HspMrel : Mrel !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hrelcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HKrelsp. }
    (* ===== EPILOGUE: restore ra/s0/s1/s2, pop frame, ret ===== *)
    iPoseProof (rsl_2c with "Htext") as "Hi2c".
    iPoseProof (rsl_2e with "Htext") as "Hi2e".
    iPoseProof (rsl_30 with "Htext") as "Hi30".
    iPoseProof (rsl_32 with "Htext") as "Hi32".
    iPoseProof (rsl_34 with "Htext") as "Hi34".
    iPoseProof (rsl_36 with "Htext") as "Hi36".
    (* +0x2c c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (RSL + 0x2c)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              Mrel (av - 4)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2c [Hr24] [-]").
    { iEval (rewrite HspMrel). iEval (rewrite HspR1) in "Hr24". iExact "Hr24". }
    iIntros "Hcg Hpc Hr24".
    iEval (rewrite HspMrel) in "Hr24".
    set (Q2c := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> Mrel).
    assert (HspQ2c : Q2c !!! Regidx csp_rs1 = spr) by (rewrite /Q2c upd_ne; [ exact HspMrel | vm_compute; discriminate ]).
    assert (Hpp2e : add_vec_int (mword_of_int (RSL + 0x2c) : mword 64) 2 = mword_of_int (RSL + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (RSL + 0x2e)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q2c (av - 4)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2e [Hr16] [-]").
    { iEval (rewrite HspQ2c). iEval (rewrite HspR1) in "Hr16". iExact "Hr16". }
    iIntros "Hcg Hpc Hr16".
    iEval (rewrite HspQ2c) in "Hr16".
    set (Q2e := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q2c).
    assert (HspQ2e : Q2e !!! Regidx csp_rs1 = spr) by (rewrite /Q2e upd_ne; [ exact HspQ2c | vm_compute; discriminate ]).
    assert (Hpp30 : add_vec_int (mword_of_int (RSL + 0x2e) : mword 64) 2 = mword_of_int (RSL + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (RSL + 0x30)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q2e (av - 4)%nat (R1 !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi30 [Hr8] [-]").
    { iEval (rewrite HspQ2e). iEval (rewrite HspR1) in "Hr8". iExact "Hr8". }
    iIntros "Hcg Hpc Hr8".
    iEval (rewrite HspQ2e) in "Hr8".
    set (Q30 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q2e).
    assert (HspQ30 : Q30 !!! Regidx csp_rs1 = spr) by (rewrite /Q30 upd_ne; [ exact HspQ2e | vm_compute; discriminate ]).
    assert (Hpp32 : add_vec_int (mword_of_int (RSL + 0x30) : mword 64) 2 = mword_of_int (RSL + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (RSL + 0x32)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              Q30 (av - 4)%nat (R1 !!! Regidx (mword_of_int 18 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi32 [Hr0] [-]").
    { iEval (rewrite HspQ30). iEval (rewrite HspR1) in "Hr0". iExact "Hr0". }
    iIntros "Hcg Hpc Hr0".
    iEval (rewrite HspQ30) in "Hr0".
    set (Q32 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 18 : mword 5))]> Q30).
    assert (HspQ32 : Q32 !!! Regidx csp_rs1 = spr) by (rewrite /Q32 upd_ne; [ exact HspQ30 | vm_compute; discriminate ]).
    assert (Hpp34 : add_vec_int (mword_of_int (RSL + 0x32) : mword 64) 2 = mword_of_int (RSL + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* +0x34 c.addi16sp sp,32 -- pop the frame *)
    set (Q34 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q32 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q32).
    assert (Hwv : add_vec (Q32 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HspQ32. unfold spr, sp0. apply frame_cancel_32. }
    assert (Hpop : Q32 !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q32 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HspQ32. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
      iSplitL "Hr0";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hr0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (RSL + 0x34)) (mword_of_int 2 : mword 6) Q32 (av - 4)%nat 4 Hpop
              with "Hcg Hpc Hi34 Hframe4 [-]").
    iIntros "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (Q32 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q32) with Q34.
    assert (Hpp36 : add_vec_int (mword_of_int (RSL + 0x34) : mword 64) 2 = mword_of_int (RSL + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* +0x36 c.ret *)
    assert (HQ34ra : Q34 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Q34 upd_ne; [| vm_compute; discriminate].
      rewrite /Q32 upd_ne; [| vm_compute; discriminate].
      rewrite /Q30 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2e upd_ne; [| vm_compute; discriminate].
      rewrite /Q2c upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (RSL + 0x36)) (mword_of_int 1 : mword 5) Q34 av
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi36 [-]").
    iIntros "Hcg Hpc".
    assert (Hretf : ret_pc (Q34 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HQ34ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! Q34 with "[%] Hcg Hown Hpc").
    (* callee_saved m Q34 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              c <> mword_of_int 9 -> c <> mword_of_int 10 -> c <> mword_of_int 18 ->
              Q34 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N1 N2 N8 N9 N10 N18.
      let peel := (repeat (rewrite upd_ne; [ | congruence ])) in
      rewrite /Q34 /Q32 /Q30 /Q2e /Q2c; peel;
      rewrite (callee_saved_lookup Hrelcs c Hcs);
      rewrite /Krel /A_ra0; peel;
      rewrite (callee_saved_lookup Hwkcs c Hcs);
      rewrite /Cwk /A_wa0; peel;
      rewrite (callee_saved_lookup Hpins c Hcs);
      rewrite /Kacq /A_a0 /A_s2 /A_s1 /R2 /R1; peel;
      reflexivity. }
    unfold callee_saved.
    split.
    { (* sp *)
      rewrite /Q34 upd_eq.
      assert (HQ32csp : Q32 !!! Regidx csp_rs1 = spr).
      { rewrite /Q32 /Q30 /Q2e /Q2c.
        repeat (rewrite upd_ne; [| vm_compute; discriminate]).
        exact HspMrel. }
      rewrite HQ32csp. unfold regval_into_reg, spr, sp0. apply frame_cancel_32. }
    split.
    { (* tp *) apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split.
    { (* s0 *)
      rewrite /Q34 upd_ne; [| vm_compute; discriminate].
      rewrite /Q32 upd_ne; [| vm_compute; discriminate].
      rewrite /Q30 upd_ne; [| vm_compute; discriminate].
      rewrite /Q2e upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s1 *)
      rewrite /Q34 upd_ne; [| vm_compute; discriminate].
      rewrite /Q32 upd_ne; [| vm_compute; discriminate].
      rewrite /Q30 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    split.
    { (* s2 *)
      rewrite /Q34 upd_ne; [| vm_compute; discriminate].
      rewrite /Q32 upd_eq.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofReleasesleep.

End ReleasesleepProof.
