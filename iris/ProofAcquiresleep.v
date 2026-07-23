(* ProofAcquiresleep.v -- acquiresleep() over the SIE-agnostic sconf world.

   acquiresleep(slk) @ 0x80003ecc: the 32-byte 4-register frame (ra/s0/s1/s2)
   trade, then s1:=slk, s2:=&slk->lk (= sl_lk slk), acquire(&slk->lk); then the
   condition-variable WAIT LOOP

      while (slk->locked) sleep(slk, &slk->lk);

   over the inner spinlock, then slk->locked:=1, slk->pid:=myproc()->pid,
   release(&slk->lk), epilogue.

   The retry loop is UNBOUNDED (sleep may never see the lock free), so it is
   proved by iLöb over a loop lemma whose back edge (the c.bnez after the
   post-sleep reload) closes against the later-handing taken leaf
   [wp_cbnez_taken_s_sconf].  The two [lw]/branch sites (+0x18 beqz at entry,
   +0x24 bnez in-loop) both destruct [sl_res]: the FREE arm exits (beqz taken /
   bnez falls through), the HELD arm loops (beqz falls / bnez taken).

   A functor over ACQUIRE / RELEASE / MYPROC; the sleep() call uses the
   deliberately-assumed [wp_sleep_sconf] axiom (SpecSleep.v) directly. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import IntrDefs.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpIntenaBits KernelRvcDecode.
Require Import WpSmodeIntr.
Require Import WpMycpu ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx SpecSched.
Require Import WpLock.
Require Import SleepLock.
Require Import WpSleeplockDecode.
Require Import SpecAcquire SpecRelease SpecMyproc SpecSleep.
Require Import SpecAcquiresleep.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* the loop/exit register-map invariant: s1=slk, s2=sl_lk slk, sp=frame sp,
   tp=cid_word, and s3..s11 preserved from the entry map [m]. *)
Definition asl_regs `{CID : CpuId} (m M : regfile) (slk spd : mword 64) : Prop :=
  M !!! Regidx (mword_of_int 9 : mword 5) = slk /\
  M !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk /\
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx (mword_of_int 4 : mword 5) = cid_word /\
  M !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\
  M !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
  M !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
  M !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
  M !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
  M !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
  M !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
  M !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).

Lemma asl_regs_cs `{CID : CpuId} (m M1 M2 : regfile) (slk spd : mword 64) :
  callee_saved M1 M2 -> asl_regs m M1 slk spd -> asl_regs m M2 slk spd.
Proof.
  intros Hcs Ha. unfold asl_regs in *.
  destruct Ha as (A&B&C&D&E&F&G&H&I&J&K&L&N).
  repeat split.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact B.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact C.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)). exact D.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact E.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). exact F.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). exact G.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). exact H.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). exact I.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)). exact J.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)). exact K.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)). exact L.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). exact N.
Qed.

(* the shared exit-path continuation (control at +0x28): everything the exit
   straight-line needs, phrased over the abstract register map [M]. *)
Definition asl_exit `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γs : list gname)
    (γl γsl : gname) (R : iProp Σ) (m : regfile) (pidv : mword 32) (av : nat) (dq : dfrac)
    (slk spd sp0 pj cpuv : mword 64) (eb : bool) (C : iProp Σ) : iProp Σ :=
  (∀ M : regfile,
    ⌜ asl_regs m M slk spd ⌝ -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked γl -∗ sleeplocked γsl -∗ sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗ R -∗
    slk ↦₄ (mword_of_int 0 : mword 32) -∗ sl_lkcpu slk ↦₈ cpuv -∗
    p_pid pj ↦₄{dq} pidv -∗ p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
    own_ctx (p_context pj) -∗ ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
    cpu_own γ 1 eb pj C -∗ trap_csrs_pay 0 eb -∗ sie_cap_gpr γ M (av - 4) -∗
    pc_is (mword_of_int (ASL + 0x28)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }})%I.

(* the wait-loop invariant (control at +0x1c): held-word cell + the sleep bundle,
   threading the exit continuation as its last premise. *)
Definition asl_loop `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γs : list gname) (j : nat)
    (γl γsl : gname) (R : iProp Σ) (m : regfile) (pidv : mword 32) (av : nat) (dq : dfrac)
    (slk spd sp0 pj cpuv : mword 64) (eb : bool) (C : iProp Σ) : iProp Σ :=
  (∀ M : regfile,
    ⌜ asl_regs m M slk spd ⌝ -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked γl -∗
    (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝) -∗
    sl_lkcpu slk ↦₈ cpuv -∗
    p_pid pj ↦₄{dq} pidv -∗ p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
    own_ctx (p_context pj) -∗ ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
    cpu_own γ 1 eb pj C -∗ trap_csrs_pay 0 eb -∗ sie_cap_gpr γ M (av - 4) -∗
    pc_is (mword_of_int (ASL + 0x1c)) -∗
    asl_exit γ Φ γs γl γsl R m pidv av dq slk spd sp0 pj cpuv eb C -∗
    WP (Loop : expr riscv_lang) {{ Φ }})%I.

Module AcquiresleepProof (Acquire : ACQUIRE) (Release : RELEASE) (Myproc : MYPROC) (Sleep : SLEEP) : ACQUIRESLEEP.

Section ProofAcquiresleep.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  (* register disequality guard (perf rule): unify settles convertibility
     cheaply, so [discriminate] only ever runs on a genuine miss. *)
  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Lemma wp_acquiresleep_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) {dq : dfrac}
    : wp_acquiresleep_sconf_body γ Φ γs j γl γsl s R m pidv av eb C dq.
  Proof.
    cbv beta delta [wp_acquiresleep_sconf_body].
    intros pcE slk pj ret_tgt Htp Hj Hav.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := pa_stk sp0 4).
    set (cpuv := mycpu_ret cid_word).
    iIntros "Hcg Hown #Htext Hpc #Hslk Hlkcpu Hpid Hplk #Hpinv Hctx Hsched Hcont".
    (* derive proc j's own lock gname γpl from procs_inv (persistent, peek) *)
    iAssert (⌜length γs = NPROC⌝)%I as %Hlen. { by iDestruct "Hpinv" as "[$ _]". }
    destruct (lookup_lt_is_Some_2 γs j ltac:(rewrite Hlen; exact Hj)) as [γpl Hjpl].
    iPoseProof (asl_00 with "Htext") as "Hi00".
    iPoseProof (asl_02 with "Htext") as "Hi02".
    iPoseProof (asl_04 with "Htext") as "Hi04".
    iPoseProof (asl_06 with "Htext") as "Hi06".
    iPoseProof (asl_08 with "Htext") as "Hi08".
    iPoseProof (asl_0a with "Htext") as "Hi0a".
    iPoseProof (asl_0c with "Htext") as "Hi0c".
    iPoseProof (asl_0e with "Htext") as "Hi0e".
    iPoseProof (asl_12 with "Htext") as "Hi12".
    iPoseProof (asl_14 with "Htext") as "Hi14".
    (* ===== PROLOGUE: 4-slot frame trade + saves ===== *)
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
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spd).
    { rewrite /R1 upd_eq. rewrite /spd. rewrite -Hpush. reflexivity. }
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vr0)  "Hr0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hr0".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (ASL + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (ASL + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 (av - 4)%nat vr24 with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (ASL + 0x02) : mword 64) 2 = mword_of_int (ASL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (ASL + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (av - 4)%nat vr16 with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (ASL + 0x04) : mword 64) 2 = mword_of_int (ASL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (ASL + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (av - 4)%nat vr8 with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (ASL + 0x06) : mword 64) 2 = mword_of_int (ASL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (ASL + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 (av - 4)%nat vr0 with "Hcg Hpc Hi08 Hr0 [-]").
    iIntros "Hcg Hpc Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (ASL + 0x08) : mword 64) 2 = mword_of_int (ASL + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* the four frame cells now hold m's ra/s0/s1/s2; re-anchor at pa_stk sp0 k *)
    iEval (rewrite Hb1) in "Hr24". iEval (rewrite Hb2) in "Hr16".
    iEval (rewrite Hb3) in "Hr8".  iEval (rewrite Hb4) in "Hr0".
    assert (Hr1v : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr8v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr9v : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr18v : R1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)) by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite Hr1v) in "Hr24". iEval (rewrite Hr8v) in "Hr16".
    iEval (rewrite Hr9v) in "Hr8".  iEval (rewrite Hr18v) in "Hr0".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (ASL + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1) with R2.
    assert (Hpp0c : add_vec_int (mword_of_int (ASL + 0x0a) : mword 64) 2 = mword_of_int (ASL + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = slk).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    (* +0x0c c.mv s1,a0 : s1 := slk *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (ASL + 0x0c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R2 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    set (C0 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2) with C0.
    assert (Hpp0e : add_vec_int (mword_of_int (ASL + 0x0c) : mword 64) 2 = mword_of_int (ASL + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HC0a0 : C0 !!! Regidx (mword_of_int 10 : mword 5) = slk) by (rewrite /C0 upd_ne; [ exact HR2a0 | reg_neq ]).
    (* +0x0e addi s2,a0,8 : s2 := sl_lk slk *)
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (ASL + 0x0e)) (mword_of_int 18 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 8 : mword 12)
              C0 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    set (C1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (C0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> C0).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (C0 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> C0) with C1.
    assert (Hpp12 : add_vec_int (mword_of_int (ASL + 0x0e) : mword 64) 4 = mword_of_int (ASL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    assert (HC1s2 : C1 !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /C1 upd_eq. rewrite HC0a0. reflexivity. }
    (* +0x12 c.mv a0,s2 : a0 := sl_lk slk *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (ASL + 0x12)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              C1 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (C2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (C1 !!! Regidx (mword_of_int 18 : mword 5)))]> C1).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (C1 !!! Regidx (mword_of_int 18 : mword 5)))]> C1) with C2.
    assert (Hpp14 : add_vec_int (mword_of_int (ASL + 0x12) : mword 64) 2 = mword_of_int (ASL + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 jal ra,acquire *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (ASL + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2084136 : mword 21)
              C2 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (Maq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (ASL + 0x14) : mword 64) 4)]> C2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (ASL + 0x14) : mword 64) 4)]> C2) with Maq.
    assert (Hjaq : add_vec (mword_of_int (ASL + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2084136 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    (* facts about the acquire-entry map Maq *)
    assert (HMaqa0 : Maq !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_eq. rewrite add_vec_zero_l. exact HC1s2. }
    assert (HMaqra : Maq !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (ASL + 0x14) : mword 64) 4)
      by (rewrite /Maq; apply upd_eq).
    assert (HMaqtp : Maq !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
      rewrite /C1 upd_ne; [| reg_neq]. rewrite /C0 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [| reg_neq]. exact Htp. }
    assert (HMaqcsp : Maq !!! Regidx csp_rs1 = spd).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
      rewrite /C1 upd_ne; [| reg_neq]. rewrite /C0 upd_ne; [| reg_neq].
      rewrite /R2 upd_ne; [| reg_neq]. exact HspR1. }
    assert (HMaqs1 : Maq !!! Regidx (mword_of_int 9 : mword 5) = slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
      rewrite /C1 upd_ne; [| reg_neq]. rewrite /C0 upd_eq. rewrite add_vec_zero_l. exact HR2a0. }
    assert (HMaqs2 : Maq !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq]. exact HC1s2. }
    (* the s3..s11 preservation from m through the prologue (no writes) *)
    assert (Hpro_cs : forall c : mword 5,
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 9 ->
              c <> mword_of_int 10 -> c <> mword_of_int 18 -> c <> mword_of_int 1 ->
              Maq !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N9 N10 N18 N1.
      rewrite /Maq upd_ne; [| congruence]. rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence]. rewrite /C0 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence]. rewrite /R1 upd_ne; [reflexivity | congruence]. }
    (* ===== acquire(&slk->lk): cpu_own 0 -> 1, returns locked + sl_res + pay ===== *)
    iApply (Acquire.wp_acquire_sconf γ Φ γl "sleep lock"%string (sl_res γsl slk R) Maq
              (zero_reg : mword 64) 0%nat eb pj C (av - 4)%nat
              ltac:(rewrite HMaqtp; exact (mycpu_ret_nonzero cid_word tp_ok_cid))
              HMaqtp
              ltac:(lia)
              ltac:(lia)
              with "Hcg Hown Htext Hpc [] [Hlkcpu] [-]").
    { iEval (rewrite HMaqa0). iApply (is_sleeplock_lock with "Hslk"). }
    { iEval (rewrite HMaqa0). iExact "Hlkcpu". }
    iIntros (ms_a Macq) "%Hms_a Hcg Hpc %Hpins Htok HR Hlkcpu Hown Hpay".
    (* pc = +0x18; anchor the lock cpu word to [sl_lkcpu slk] at [cpuv] *)
    assert (Hpc18 : ret_pc (Maq !!! Regidx (mword_of_int 1 : mword 5))
                    = mword_of_int (ASL + 0x18)) by (rewrite HMaqra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    iEval (rewrite HMaqa0) in "Hlkcpu".
    iEval (rewrite HMaqtp) in "Hlkcpu".
    change (add_vec (sl_lk slk) (sign_extend' 64 (mword_of_int 16 : mword 12))) with (sl_lkcpu slk) in *.
    (* asl_regs for the post-acquire map (via callee_saved from Maq) *)
    assert (Hasl_acq : asl_regs m Macq slk spd).
    { unfold asl_regs.
      pose proof Hpins as Hpins2.
      repeat split.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HMaqs1.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact HMaqs2.
      - rewrite (callee_saved_lookup Hpins csp_rs1 ltac:(vm_compute; reflexivity)). exact HMaqcsp.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)). exact HMaqtp.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq.
      - rewrite (callee_saved_lookup Hpins (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). apply Hpro_cs; reg_neq. }

    (* ================= the shared EXIT continuation (+0x28 -> ret) ================= *)
    iAssert (asl_exit γ Φ γs γl γsl R m pidv av dq slk spd sp0 pj cpuv eb C) with "[Hcont]" as "Hexit".
    { rewrite /asl_exit.
      iIntros (M) "%Hasl Hr24 Hr16 Hr8 Hr0 Htok Hstok Hspid HR Hw Hlkcpu Hpid Hplk Hctx Hsched Hown Hpay Hcg Hpc".
      destruct Hasl as (Hs1 & Hs2 & Hsp & HtpM & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
      iPoseProof (asl_28 with "Htext") as "Hi28".
      iPoseProof (asl_2a with "Htext") as "Hi2a".
      iPoseProof (asl_2c with "Htext") as "Hi2c".
      iPoseProof (asl_30 with "Htext") as "Hi30".
      iPoseProof (asl_32 with "Htext") as "Hi32".
      iPoseProof (asl_34 with "Htext") as "Hi34".
      iPoseProof (asl_36 with "Htext") as "Hi36".
      (* +0x28 c.li a5,1 *)
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (ASL + 0x28)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                M (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi28 [-]").
      iIntros "Hcg Hpc".
      set (E1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> M).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> M) with E1.
      assert (Hpp2a : add_vec_int (mword_of_int (ASL + 0x28) : mword 64) 2 = mword_of_int (ASL + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      assert (HE1s1 : E1 !!! Regidx (mword_of_int 9 : mword 5) = slk) by (rewrite /E1 upd_ne; [ exact Hs1 | reg_neq ]).
      (* +0x2a c.sw a5,0(s1) : slk->locked := 1 *)
      assert (Hlw0 : add_vec (E1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
      { rewrite HE1s1. replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
      iApply (wp_csw_s_sconf γ Φ (mword_of_int (ASL + 0x2a)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) E1 (av - 4)%nat (mword_of_int 0 : mword 32)
                with "Hcg Hpc Hi2a [Hw] [-]").
      { iEval (rewrite Hlw0). iExact "Hw". }
      iIntros "Hcg Hpc Hw".
      iEval (rewrite Hlw0) in "Hw".
      assert (Hsv1 : trunc32 (E1 !!! Regidx (mword_of_int 15 : mword 5)) = (mword_of_int 1 : mword 32)).
      { rewrite /E1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hsv1) in "Hw".
      assert (Hpp2c : add_vec_int (mword_of_int (ASL + 0x2a) : mword 64) 2 = mword_of_int (ASL + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      (* +0x2c jal ra,myproc *)
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (ASL + 0x2c)) (mword_of_int 1 : mword 5) (mword_of_int 2087436 : mword 21)
                E1 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2c [-]").
      iIntros "Hcg Hpc".
      set (E2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (ASL + 0x2c) : mword 64) 4)]> E1).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (ASL + 0x2c) : mword 64) 4)]> E1) with E2.
      assert (Hjmp : add_vec (mword_of_int (ASL + 0x2c) : mword 64) (sign_extend' 64 (mword_of_int 2087436 : mword 21)) = mword_of_int KernelSyms.myproc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjmp) in "Hpc".
      assert (HE2ra : E2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (ASL + 0x2c) : mword 64) 4) by (rewrite /E2; apply upd_eq).
      assert (HE2tp : E2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [ exact HtpM | reg_neq ]. }
      iApply (Myproc.wp_myproc_sconf γ Φ E2 (av - 4)%nat 1%nat eb pj C
                ltac:(exact HE2tp)
                ltac:(lia)
                ltac:(lia)
                with "Hcg Hown Htext Hpc").
      iIntros (ms_m mfm) "%Hms_m Hcg Hown Hpc %Hmp".
      destruct Hmp as (Hmp_cs & Hmp_a0).
      assert (Hpc30 : ret_pc (E2 !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (ASL + 0x30)) by (rewrite HE2ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc30) in "Hpc".
      (* mfm!!!a0 = pj *)
      assert (Hmfma0 : mfm !!! Regidx (mword_of_int 10 : mword 5) = pj) by exact Hmp_a0.
      (* +0x30 c.lw a5,48(a0) : a5 := myproc()->pid *)
      assert (Hppid : add_vec (mfm !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00")))) = p_pid pj).
      { rewrite Hmfma0. rewrite /p_pid.
        replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) : mword 64)
          with (sign_extend' 64 (mword_of_int 48 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        reflexivity. }
      iApply (wp_clw_s_sconf γ Φ (mword_of_int (ASL + 0x30)) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 5) ('b"00"))) mfm (av - 4)%nat pidv (dqm := dq)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi30 [Hpid] [-]").
      { iEval (rewrite Hppid). iExact "Hpid". }
      iIntros "Hcg Hpc Hpid".
      iEval (rewrite Hppid) in "Hpid".
      set (E3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> mfm).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 pidv)]> mfm) with E3.
      assert (Hpp32 : add_vec_int (mword_of_int (ASL + 0x30) : mword 64) 2 = mword_of_int (ASL + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      (* s1 = slk in E3 (through myproc callee_saved) *)
      assert (HmfmS1 : mfm !!! Regidx (mword_of_int 9 : mword 5) = slk).
      { rewrite (callee_saved_lookup Hmp_cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HE1s1. }
      assert (HE3s1 : E3 !!! Regidx (mword_of_int 9 : mword 5) = slk) by (rewrite /E3 upd_ne; [ exact HmfmS1 | reg_neq ]).
      (* +0x32 c.sw a5,40(s1) : slk->pid := pidv *)
      assert (Hspidaddr : add_vec (E3 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00")))) = sl_pid slk).
      { rewrite HE3s1. rewrite /sl_pid.
        replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))) : mword 64)
          with (sign_extend' 64 (mword_of_int 40 : mword 12) : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        reflexivity. }
      iApply (wp_csw_s_sconf γ Φ (mword_of_int (ASL + 0x32)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))) E3 (av - 4)%nat (mword_of_int 0 : mword 32)
                with "Hcg Hpc Hi32 [Hspid] [-]").
      { iEval (rewrite Hspidaddr). iExact "Hspid". }
      iIntros "Hcg Hpc Hspid".
      iEval (rewrite Hspidaddr) in "Hspid".
      assert (Hsvpid : trunc32 (E3 !!! Regidx (mword_of_int 15 : mword 5)) = pidv).
      { rewrite /E3 upd_eq. apply trunc32_sext. }
      iEval (rewrite Hsvpid) in "Hspid".
      assert (Hpp34 : add_vec_int (mword_of_int (ASL + 0x32) : mword 64) 2 = mword_of_int (ASL + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      (* +0x34 c.mv a0,s2 : a0 := sl_lk slk *)
      assert (HmfmS2 : mfm !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk).
      { rewrite (callee_saved_lookup Hmp_cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
        rewrite /E1 upd_ne; [ exact Hs2 | reg_neq ]. }
      assert (HE3s2 : E3 !!! Regidx (mword_of_int 18 : mword 5) = sl_lk slk) by (rewrite /E3 upd_ne; [ exact HmfmS2 | reg_neq ]).
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (ASL + 0x34)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
                E3 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi34 [-]").
      iIntros "Hcg Hpc".
      set (E4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (E3 !!! Regidx (mword_of_int 18 : mword 5)))]> E3).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (E3 !!! Regidx (mword_of_int 18 : mword 5)))]> E3) with E4.
      assert (Hpp36 : add_vec_int (mword_of_int (ASL + 0x34) : mword 64) 2 = mword_of_int (ASL + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 jal ra,release *)
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (ASL + 0x36)) (mword_of_int 1 : mword 5) (mword_of_int 2084238 : mword 21)
                E4 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi36 [-]").
      iIntros "Hcg Hpc".
      set (E5 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (ASL + 0x36) : mword 64) 4)]> E4).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (ASL + 0x36) : mword 64) 4)]> E4) with E5.
      assert (Hjrel : add_vec (mword_of_int (ASL + 0x36) : mword 64) (sign_extend' 64 (mword_of_int 2084238 : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjrel) in "Hpc".
      assert (HE5ra : E5 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (ASL + 0x36) : mword 64) 4) by (rewrite /E5; apply upd_eq).
      assert (HE5a0 : E5 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
      { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_eq. rewrite add_vec_zero_l. exact HE3s2. }
      assert (HE5tp : E5 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
        rewrite (callee_saved_lookup Hmp_cs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)). exact HE2tp. }
      (* re-close sl_res in the HELD state (word = 1) *)
      iDestruct (sl_res_close_held γsl slk R (mword_of_int 1 : mword 32) ltac:(vm_compute; reflexivity) with "Hw") as "HRc".
      (* release premises pre-established *)
      assert (Hrel_lka : add_vec (E5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = sl_lk slk).
      { rewrite HE5a0. replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
      assert (Hrel_cpu : eq_vec cpuv (mycpu_ret (E5 !!! Regidx (mword_of_int 4 : mword 5))) = true).
      { rewrite HE5tp. rewrite /cpuv. apply eq_vec_true_iff. reflexivity. }
      iApply (Release.wp_release_sconf γ Φ γl (sl_lk slk) "sleep lock"%string (sl_res γsl slk R) E5
                cpuv 0%nat eb pj C (av - 4)%nat
                Hrel_lka Hrel_cpu HE5tp ltac:(lia)
                with "Hcg Htext Hpc [] Htok HRc [Hlkcpu] Hown Hpay [-]").
      { iApply (is_sleeplock_lock with "Hslk"). }
      { iEval (rewrite HE5a0). change (add_vec (sl_lk slk) (sign_extend' 64 (mword_of_int 16 : mword 12))) with (sl_lkcpu slk). iExact "Hlkcpu". }
      iIntros (mrel) "Hcg Hpc %Hrelcs Hlkcpu Hown".
      assert (Hpc3a : ret_pc (E5 !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (ASL + 0x3a)) by (rewrite HE5ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc3a) in "Hpc".
      iEval (rewrite HE5a0) in "Hlkcpu".
      change (add_vec (sl_lk slk) (sign_extend' 64 (mword_of_int 16 : mword 12))) with (sl_lkcpu slk) in *.
      (* ===== EPILOGUE (0x3a..0x44): restore ra/s0/s1/s2, frame pop, ret ===== *)
      pose proof Hrelcs as Hrelcs2.
      iPoseProof (asl_3a with "Htext") as "Hi3a".
      iPoseProof (asl_3c with "Htext") as "Hi3c".
      iPoseProof (asl_3e with "Htext") as "Hi3e".
      iPoseProof (asl_40 with "Htext") as "Hi40".
      iPoseProof (asl_42 with "Htext") as "Hi42".
      iPoseProof (asl_44 with "Htext") as "Hi44".
      (* sp preserved through release, myproc, exit chain: mrel!!!sp = spd *)
      assert (HmfmSp : mfm !!! Regidx csp_rs1 = spd).
      { rewrite (callee_saved_lookup Hmp_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /E1 upd_ne; [ exact Hsp | reg_neq ]. }
      assert (HE5csp : E5 !!! Regidx csp_rs1 = spd).
      { rewrite /E5 upd_ne; [| reg_neq]. rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq]. exact HmfmSp. }
      assert (HmrelSp : mrel !!! Regidx csp_rs1 = spd).
      { rewrite (callee_saved_lookup Hrelcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HE5csp. }
      (* +0x3a c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (ASL + 0x3a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                mrel (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi3a [Hr24] [-]").
      { iEval (rewrite HmrelSp). iEval (rewrite -Hb1 HspR1) in "Hr24". iExact "Hr24". }
      iIntros "Hcg Hpc Hr24".
      iEval (rewrite HmrelSp) in "Hr24".
      set (Q3a := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with Q3a.
      assert (HQ3asp : Q3a !!! Regidx csp_rs1 = spd) by (rewrite /Q3a upd_ne; [ exact HmrelSp | reg_neq ]).
      assert (Hpp3c : add_vec_int (mword_of_int (ASL + 0x3a) : mword 64) 2 = mword_of_int (ASL + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      (* +0x3c c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (ASL + 0x3c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                Q3a (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi3c [Hr16] [-]").
      { iEval (rewrite HQ3asp). iEval (rewrite -Hb2 HspR1) in "Hr16". iExact "Hr16". }
      iIntros "Hcg Hpc Hr16".
      iEval (rewrite HQ3asp) in "Hr16".
      set (Q3c := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q3a).
      change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q3a) with Q3c.
      assert (HQ3csp : Q3c !!! Regidx csp_rs1 = spd) by (rewrite /Q3c upd_ne; [ exact HQ3asp | reg_neq ]).
      assert (Hpp3e : add_vec_int (mword_of_int (ASL + 0x3c) : mword 64) 2 = mword_of_int (ASL + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      (* +0x3e c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (ASL + 0x3e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                Q3c (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi3e [Hr8] [-]").
      { iEval (rewrite HQ3csp). iEval (rewrite -Hb3 HspR1) in "Hr8". iExact "Hr8". }
      iIntros "Hcg Hpc Hr8".
      iEval (rewrite HQ3csp) in "Hr8".
      set (Q3e := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q3c).
      change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q3c) with Q3e.
      assert (HQ3esp : Q3e !!! Regidx csp_rs1 = spd) by (rewrite /Q3e upd_ne; [ exact HQ3csp | reg_neq ]).
      assert (Hpp40 : add_vec_int (mword_of_int (ASL + 0x3e) : mword 64) 2 = mword_of_int (ASL + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* +0x40 c.ldsp s2,0(sp) *)
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (ASL + 0x40)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
                Q3e (av - 4)%nat (m !!! Regidx (mword_of_int 18 : mword 5))
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi40 [Hr0] [-]").
      { iEval (rewrite HQ3esp). iEval (rewrite -Hb4 HspR1) in "Hr0". iExact "Hr0". }
      iIntros "Hcg Hpc Hr0".
      iEval (rewrite HQ3esp) in "Hr0".
      set (Q40 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q3e).
      change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q3e) with Q40.
      assert (HQ40sp : Q40 !!! Regidx csp_rs1 = spd) by (rewrite /Q40 upd_ne; [ exact HQ3esp | reg_neq ]).
      assert (Hpp42 : add_vec_int (mword_of_int (ASL + 0x40) : mword 64) 2 = mword_of_int (ASL + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* +0x42 c.addi16sp sp,32 -- the frame trade back (pop 4) *)
      set (Q42 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q40).
      assert (Hwv : add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite HQ40sp. rewrite /spd /sp0. rewrite -Hpush. rewrite po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply kv_addv_zero. }
      assert (Hpop : Q40 !!! Regidx csp_rs1
                     = pa_stk (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HQ40sp. reflexivity. }
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hr24"|].
        iSplitL "Hr16"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hr16"|].
        iSplitL "Hr8";  [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hr8"|].
        iSplitL "Hr0";  [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hr0"|].
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (ASL + 0x42)) (mword_of_int 2 : mword 6) Q40 (av - 4)%nat 4 Hpop
                with "Hcg Hpc Hi42 Hframe4 [-]").
      iIntros "Hcg Hpc".
      assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (Q40 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q40) with Q42.
      assert (Hpp44 : add_vec_int (mword_of_int (ASL + 0x42) : mword 64) 2 = mword_of_int (ASL + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* +0x44 c.ret *)
      assert (HQ42ra : Q42 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_ne; [| reg_neq].
        rewrite /Q3c upd_ne; [| reg_neq]. rewrite /Q3a upd_eq. reflexivity. }
      iApply (wp_cret_s_sconf γ Φ (mword_of_int (ASL + 0x44)) (mword_of_int 1 : mword 5) Q42 av
                ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi44 [-]").
      iIntros "Hcg Hpc".
      assert (Hretf : ret_pc (Q42 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
        by (rewrite HQ42ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      (* callee_saved m Q42.  s3..s11/tp thread through release+myproc back to M
         (asl_regs), then M relates to m; sp cancels; ra/s0/s1/s2 restored from
         the frame (= m's saved values). *)
      assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
                c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
                c <> mword_of_int 9 -> c <> mword_of_int 10 -> c <> mword_of_int 15 ->
                c <> mword_of_int 18 ->
                Q42 !!! Regidx c = M !!! Regidx c).
      { intros c Hcs N1 N2 N8 N9 N10 N15 N18.
        rewrite /Q42 /Q40 /Q3e /Q3c /Q3a. repeat (rewrite upd_ne; [| congruence]).
        rewrite (callee_saved_lookup Hrelcs2 c Hcs).
        rewrite /E5 /E4 /E3. repeat (rewrite upd_ne; [| congruence]).
        rewrite (callee_saved_lookup Hmp_cs c Hcs).
        rewrite /E2 /E1. repeat (rewrite upd_ne; [| congruence]). reflexivity. }
      iApply ("Hcont" $! Q42 with "[%] Hcg Hown Hpc Hstok Hspid HR [Hlkcpu] Hpid Hplk Hctx Hsched").
      { unfold callee_saved.
        split. { (* sp *) rewrite /Q42 upd_eq. rewrite Hwv. reflexivity. }
        split. { (* tp *) rewrite (Hthr (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
                 rewrite HtpM. symmetry. exact Htp. }
        split. { (* s0 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_ne; [| reg_neq]. rewrite /Q3c upd_eq. reflexivity. }
        split. { (* s1 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_ne; [| reg_neq]. rewrite /Q3e upd_eq. reflexivity. }
        split. { (* s2 *) rewrite /Q42 upd_ne; [| reg_neq]. rewrite /Q40 upd_eq. reflexivity. }
        split. { rewrite (Hthr (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H19. }
        split. { rewrite (Hthr (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20. }
        split. { rewrite (Hthr (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21. }
        split. { rewrite (Hthr (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22. }
        split. { rewrite (Hthr (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23. }
        split. { rewrite (Hthr (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24. }
        split. { rewrite (Hthr (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25. }
        split. { rewrite (Hthr (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26. }
        { rewrite (Hthr (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. } }
      { iExact "Hlkcpu". } }

    (* ================= the WAIT LOOP (iLöb), from +0x1c ================= *)
    iAssert (asl_loop γ Φ γs j γl γsl R m pidv av dq slk spd sp0 pj cpuv eb C) with "[]" as "Hloop".
    { iLöb as "IH". rewrite /asl_loop.
      iIntros (M) "%HaslM0 Hr24 Hr16 Hr8 Hr0 Htok Hheld Hlkcpu Hpid Hplk Hctx Hsched Hown Hpay Hcg Hpc Hexit".
      assert (HaslM : asl_regs m M slk spd) by exact HaslM0.
      destruct HaslM0 as (Hs1 & Hs2 & Hsp & HtpM & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
      iDestruct "Hheld" as (vh) "[Hw %Hvh]".
      iPoseProof (asl_1c with "Htext") as "Hi1c".
      iPoseProof (asl_1e with "Htext") as "Hi1e".
      iPoseProof (asl_20 with "Htext") as "Hi20".
      iPoseProof (asl_24 with "Htext") as "Hi24".
      iPoseProof (asl_26 with "Htext") as "Hi26".
      (* +0x1c c.mv a1,s2 : a1 := sl_lk slk *)
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (ASL + 0x1c)) (mword_of_int 11 : mword 5) (mword_of_int 18 : mword 5)
                M (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi1c [-]").
      iIntros "Hcg Hpc".
      set (L0 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 18 : mword 5)))]> M).
      change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 18 : mword 5)))]> M) with L0.
      assert (Hpp1e : add_vec_int (mword_of_int (ASL + 0x1c) : mword 64) 2 = mword_of_int (ASL + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* +0x1e c.mv a0,s1 : a0 := slk *)
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (ASL + 0x1e)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                L0 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi1e [-]").
      iIntros "Hcg Hpc".
      set (L1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (L0 !!! Regidx (mword_of_int 9 : mword 5)))]> L0).
      change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (L0 !!! Regidx (mword_of_int 9 : mword 5)))]> L0) with L1.
      assert (Hpp20 : add_vec_int (mword_of_int (ASL + 0x1e) : mword 64) 2 = mword_of_int (ASL + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 jal ra,sleep *)
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (ASL + 0x20)) (mword_of_int 1 : mword 5) (mword_of_int 2088986 : mword 21)
                L1 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi20 [-]").
      iIntros "Hcg Hpc".
      set (L2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (ASL + 0x20) : mword 64) 4)]> L1).
      change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (ASL + 0x20) : mword 64) 4)]> L1) with L2.
      assert (Hjsl : add_vec (mword_of_int (ASL + 0x20) : mword 64) (sign_extend' 64 (mword_of_int 2088986 : mword 21)) = mword_of_int KernelSyms.sleep)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjsl) in "Hpc".
      (* L2 register facts *)
      assert (HL2a1 : L2 !!! Regidx (mword_of_int 11 : mword 5) = sl_lk slk).
      { rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_ne; [| reg_neq]. rewrite /L0 upd_eq.
        rewrite Hs2. apply add_vec_zero_l. }
      assert (HL2ra : L2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (ASL + 0x20) : mword 64) 4)
        by (rewrite /L2; apply upd_eq).
      assert (HL2tp : L2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
      { rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_ne; [| reg_neq]. rewrite /L0 upd_ne; [| reg_neq]. exact HtpM. }
      (* callee_saved M L2 (only a1/a0/ra written) *)
      assert (HcsML2 : callee_saved M L2).
      { rewrite /L2 /L1 /L0.
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_insert_r; [vm_compute; reflexivity|].
        apply callee_saved_refl. }
      assert (HaslL2 : asl_regs m L2 slk spd) by (apply (asl_regs_cs m M L2 slk spd HcsML2 HaslM)).
      (* re-close sl_res in the HELD state (word = vh) and call sleep *)
      iDestruct (sl_res_close_held γsl slk R vh Hvh with "Hw") as "HRc".
      assert (Hsl_lka : add_vec (L2 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = sl_lk slk).
      { rewrite HL2a1. replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
      iApply (Sleep.wp_sleep_sconf γ Φ γs j γpl γl (sl_lk slk) "sleep lock"%string (sl_res γsl slk R) L2 (av - 4)%nat eb C
                HL2tp Hj Hjpl Hsl_lka
                ltac:(lia)
                with "Hcg Hown Hpay Htext Hpc Hpinv [] Htok HRc [Hlkcpu] Hplk Hctx Hsched [-]").
      { iApply (is_sleeplock_lock with "Hslk"). }
      { iEval (rewrite HL2a1). change (add_vec (sl_lk slk) (sign_extend' 64 (mword_of_int 16 : mword 12))) with (sl_lkcpu slk). iExact "Hlkcpu". }
      iIntros (mfs) "%Hs_cs Hcg Hown Hpay Hpc Htok HRc Hlkcpu Hplk Hctx Hsched".
      (* pc = +0x24; anchor cells *)
      assert (Hpc24 : ret_pc (L2 !!! Regidx (mword_of_int 1 : mword 5))
                      = mword_of_int (ASL + 0x24)) by (rewrite HL2ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc24) in "Hpc".
      iEval (rewrite HL2a1) in "Hlkcpu".
      iEval (change (add_vec (sl_lk slk) (sign_extend' 64 (mword_of_int 16 : mword 12))) with (sl_lkcpu slk)) in "Hlkcpu".
      assert (HaslMfs : asl_regs m mfs slk spd) by (apply (asl_regs_cs m L2 mfs slk spd Hs_cs HaslL2)).
      assert (Hmfss1 : mfs !!! Regidx (mword_of_int 9 : mword 5) = slk) by (destruct HaslMfs as (X&_); exact X).
      (* open the fresh sl_res, do the +0x24 reload *)
      iDestruct "HRc" as (vp) "[Hwp Harm]".
      assert (Hlw24 : add_vec (mfs !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
      { rewrite Hmfss1. replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
      iApply (wp_clw_s_sconf γ Φ (mword_of_int (ASL + 0x24)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) mfs (av - 4)%nat vp (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi24 [Hwp] [-]").
      { iEval (rewrite Hlw24). iExact "Hwp". }
      iIntros "Hcg Hpc Hwp".
      iEval (rewrite Hlw24) in "Hwp".
      set (La5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 vp)]> mfs).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 vp)]> mfs) with La5.
      assert (Hpp26 : add_vec_int (mword_of_int (ASL + 0x24) : mword 64) 2 = mword_of_int (ASL + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      assert (HLa5_15 : La5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 vp) by (rewrite /La5; apply upd_eq).
      assert (HcsMfsLa5 : callee_saved mfs La5).
      { rewrite /La5. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
      assert (HaslLa5 : asl_regs m La5 slk spd) by (apply (asl_regs_cs m mfs La5 slk spd HcsMfsLa5 HaslMfs)).
      (* +0x26 c.bnez a5 : free -> fall to +0x28 (exit); held -> back edge to +0x1c *)
      iDestruct "Harm" as "[(%Hvp0 & Hstok & Hspid & HRu) | %Hvph]".
      - (* FREE: vp = 0 -> bnez falls through to +0x28 -> exit *)
        iApply (wp_cbnez_fall_s_sconf γ Φ (mword_of_int (ASL + 0x26)) (mword_of_int 251 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  La5 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HLa5_15 Hvp0; vm_compute; reflexivity)
                  with "Hcg Hpc Hi26 [-]").
        iIntros "Hcg Hpc".
        assert (Hpp28 : add_vec_int (mword_of_int (ASL + 0x26) : mword 64) 2 = mword_of_int (ASL + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp28) in "Hpc".
        iEval (rewrite Hvp0) in "Hwp".
        iApply ("Hexit" $! La5 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hstok Hspid HRu Hwp Hlkcpu Hpid Hplk Hctx Hsched Hown Hpay Hcg Hpc").
        exact HaslLa5.
      - (* HELD: vp <> 0 -> bnez TAKEN, back edge to +0x1c (Löb IH).  Give the
           loop resources ([Hbig], [Hheldw]) to the taken leaf's ▷-continuation
           bracket, so the [iNext] inside sees ONLY those (it cannot reshuffle
           the names of the surrounding context that way). *)
        iAssert (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝)%I with "[Hwp]" as "Hheldw".
        { iExists vp. iFrame "Hwp". iPureIntro. exact Hvph. }
        (* hand the loop resources to the taken leaf's ▷-continuation bracket,
           listed INDIVIDUALLY so the inner [iNext] sees exactly this controlled
           context (no bundling: intr_count / sconf share a ghost_var, which
           [iCombine] mishandles). *)
        iApply (wp_cbnez_taken_s_sconf γ Φ (mword_of_int (ASL + 0x26)) (mword_of_int 251 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                  La5 (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HLa5_15; exact Hvph)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi26 [Hr24 Hr16 Hr8 Hr0 Htok Hlkcpu Hpid Hplk Hctx Hsched Hown Hpay Hexit Hheldw]").
        iNext. iIntros "Hcg Hpc".
        (* iNext strips the [▷] of [▷ sched_vc]; [cpu_own]/[trap_csrs_pay] are
           opaque Definitions so their contents are untouched -- re-wrap only the
           scheduler valid-context. *)
        iAssert (▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj)%I with "[Hsched]" as "Hsched".
        { iNext. iExact "Hsched". }
        assert (Hbk : add_vec (mword_of_int (ASL + 0x26) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")))) = mword_of_int (ASL + 0x1c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hbk) in "Hpc".
        iApply ("IH" $! La5 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hheldw Hlkcpu Hpid Hplk Hctx Hsched Hown Hpay Hcg Hpc Hexit").
        exact HaslLa5. }

    (* ================= entry dispatch at +0x18 (lw then c.beqz) ================= *)
    pose proof Hasl_acq as HaslAcqW.
    destruct Hasl_acq as (Hacq_s1 & Hacq_s2 & Hacq_sp & Hacq_tp & Ha19 & Ha20 & Ha21 & Ha22 & Ha23 & Ha24 & Ha25 & Ha26 & Ha27).
    iPoseProof (asl_18 with "Htext") as "Hi18".
    iPoseProof (asl_1a with "Htext") as "Hi1a".
    iDestruct "HR" as (v0) "[Hw0 Harm0]".
    assert (Hlw18 : add_vec (Macq !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))) = slk).
    { rewrite Hacq_s1. replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    (* +0x18 lw a5,0(s1) *)
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (ASL + 0x18)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) Macq (av - 4)%nat v0 (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi18 [Hw0] [-]").
    { iEval (rewrite Hlw18). iExact "Hw0". }
    iIntros "Hcg Hpc Hw0".
    iEval (rewrite Hlw18) in "Hw0".
    set (Me := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 v0)]> Macq).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 v0)]> Macq) with Me.
    assert (Hpp1a : add_vec_int (mword_of_int (ASL + 0x18) : mword 64) 2 = mword_of_int (ASL + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HMe15 : Me !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 v0) by (rewrite /Me; apply upd_eq).
    assert (HcsAcqMe : callee_saved Macq Me).
    { rewrite /Me. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HaslMe : asl_regs m Me slk spd) by (apply (asl_regs_cs m Macq Me slk spd HcsAcqMe HaslAcqW)).
    iDestruct "Harm0" as "[(%Hv00 & Hstok & Hspid & HRu) | %Hv0h]".
    - (* FREE at entry: v0 = 0 -> c.beqz TAKEN -> +0x28 (exit) *)
      iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (ASL + 0x1a)) (mword_of_int 7 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                Me (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HMe15 Hv00; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1a").
      iNext. iIntros "Hcg Hpc".
      assert (Htgt28 : add_vec (mword_of_int (ASL + 0x1a) : mword 64) (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 7 : mword 8) ('b"0")))) = mword_of_int (ASL + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt28) in "Hpc".
      iEval (rewrite Hv00) in "Hw0".
      (* iNext (from beqz-taken) strips [▷ sched_vc]; cpu_own/pay are opaque *)
      iAssert (▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj)%I with "[Hsched]" as "Hsched".
      { iNext. iExact "Hsched". }
      iApply ("Hexit" $! Me with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hstok Hspid HRu Hw0 Hlkcpu Hpid Hplk Hctx Hsched Hown Hpay Hcg Hpc").
      exact HaslMe.
    - (* HELD at entry: v0 <> 0 -> c.beqz falls through -> +0x1c (loop) *)
      iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (ASL + 0x1a)) (mword_of_int 7 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
                Me (av - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HMe15; assert (Hx : neq_vec (sign_extend' 64 v0) zero_reg = true) by exact Hv0h; unfold neq_vec in Hx; apply negb_true_iff in Hx; exact Hx)
                with "Hcg Hpc Hi1a [-]").
      iIntros "Hcg Hpc".
      assert (Hpp1c : add_vec_int (mword_of_int (ASL + 0x1a) : mword 64) 2 = mword_of_int (ASL + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      iAssert (∃ v : mword 32, slk ↦₄ v ∗ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝)%I with "[Hw0]" as "Hheldw".
      { iExists v0. iFrame "Hw0". iPureIntro. exact Hv0h. }
      iApply ("Hloop" $! Me with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hheldw Hlkcpu Hpid Hplk Hctx Hsched Hown Hpay Hcg Hpc Hexit").
      exact HaslMe.
  Qed.

End ProofAcquiresleep.

End AcquiresleepProof.
