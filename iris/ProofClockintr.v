(* ProofClockintr.v -- clockintr() over the SIE-agnostic sconf world.

   clockintr() @ 0x800024e4 is xv6's timer-interrupt handler body:

     if (cpuid() == 0) { acquire(&tickslock); ticks++; wakeup(&ticks); release(&tickslock); }
     w_stimecmp(r_time() + 1000000);

   On the standard 16-byte frame (ra/s0), the compiler puts the TIMER TAIL
   (rdtime / lui+addi 1000000 / c.add / csrw stimecmp / epilogue) in the
   fall-through path at +0x0e and the TICK BLOCK at +0x28, which the c.beqz
   at +0x0c jumps to when cpuid() returns 0 and which ends with a c.j back to
   the tail.  Both paths therefore converge on the tail: it is proved ONCE, as
   [wp_ci_tail], and applied in both arms of the [cpuid() == 0] case split
   (the arms differ only in the register map they arrive with and in whether
   they consumed the tick machinery).

   The case split itself is on the AMBIENT hart: a0 = cpuid_ret tp = cid_word
   ([cpuid_ret_cid]), so [eq_vec cid_word zero_reg] decides the branch at
   proof time, and [tick_keeper]'s disjunction (SpecClockintr.v) supplies the
   tickslock/proc-array resources in exactly the arm that steps into the tick
   block -- the other arm's left disjunct contradicts the branch condition.

   THE SIE INDEX IS THE LITERAL [false] THROUGHOUT.  SpecClockintr.v states
   the contract at [b = false] for two independent reasons (its header spells
   them out): clockintr calls cpuid() at KernelSyms.clockintr+0x08 without bracketing it in its
   own push_off/pop_off -- and cpuid, which reads tp mid-body, is itself
   [false]-only -- and [tick_keeper] is HART-INDEXED through [tick_hart]'s
   [cid_word], so it could not ride a generic-[b] [wp_next] at all.  So there
   is no [wp_next] wrapper on this contract, every leaf is applied at [false]
   and collapsed with one [rewrite wp_next_off], and the hart never moves:
   no hart binders, no [cpu_own_transport], no [wp_next_chain].  release's
   exit index [match n with O => eb | S _ => false end] is derived to be
   [false] by [ci_outb_false] from the entry resources (porting guide,
   "derive the SIE index rather than stating it").

   A functor over KernelSyms.cpuid / ACQUIRE / RELEASE / WAKEUP. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import FdSlots.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import IntrDefs.
Require Import HartTp WpNext CpuOwn.
Require Import KernelRvcDecode.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import TimerCap WpSconfTimer.
Require Import TicksInv.
Require Import CodeClockintr.
Require Import SpecCpuid SpecAcquire SpecRelease SpecWakeup.
Require Import SpecClockintr.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.



Lemma ci_eq_vec_refl {k} (x : mword k) : eq_vec x x = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.

Module ClockintrProof (Cpuid : CPUID) (Acquire : ACQUIRE) (Release : RELEASE)
                      (Wakeup : WAKEUP) : CLOCKINTR.

Section ProofClockintr.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).
  Notation a4_idx := (mword_of_int 14 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ================================================================== *)
  (* release's EXIT INDEX, derived rather than stated.  release leaves at *)
  (* [outb = match n with O => eb | S _ => false end]; clockintr's own     *)
  (* contract is at the literal [false], and the two agree because at      *)
  (* [n = 0] the entry resources force [eb = false]: [sie_arm false]'s      *)
  (* eighth (at '0') and [intr_count 0 eb]'s complementary eighth (at       *)
  (* [sie_bit eb]) are the SAME ghost, so [ghost_var_agree] refutes         *)
  (* [eb = true].  At any [S _] level the match is [false] outright.        *)
  (* ================================================================== *)
  Local Lemma ci_outb_false (M : regfile) (av n : nat) (eb : bool)
      (p : mword 64) (lks : gset string) :
    sie_cap_gpr KT1 M av false p -∗ cpu_own n eb p false lks -∗
    ⌜ (match n with O => eb | S _ => false end) = false ⌝.
  Proof.
    iIntros "Hcg Hcnt".
    iDestruct "Hcnt" as "[_ Hic]".
    destruct n as [|n'].
    - iDestruct (sie_cap_gpr_split with "Hcg") as "(_ & _ & Hsie & _)".
      iDestruct "Hsie" as "(_ & _ & Hbit & _)".
      destruct eb.
      + iDestruct (ghost_var_agree with "Hbit Hic") as %Hbad.
        exfalso. apply (f_equal (@bv_unsigned _)) in Hbad. vm_compute in Hbad. discriminate.
      + iPureIntro. reflexivity.
    - iPureIntro. reflexivity.
  Qed.

  (* ================================================================== *)
  (* THE TIMER TAIL (KernelSyms.clockintr+0x0e .. KernelSyms.clockintr+0x26): ask for the next timer         *)
  (* interrupt, then pop the frame and return.  Both paths through       *)
  (* clockintr end here, so it is proved once, over an ARBITRARY arrival  *)
  (* map [M] (only its sp matters) and an arbitrary saved ra/s0.          *)
  (* ================================================================== *)
  Lemma wp_ci_tail
      (M : regfile) (sp0 ra0 s00 : mword 64) (k : nat) (p : mword 64) :
    M !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    timer_cap -∗
    sie_cap_gpr KT1 M k false p -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.clockintr + 0x0e) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    ( ∀ Mf : regfile,
        ⌜ Mf !!! Regidx csp_rs1 = sp0 /\
          Mf !!! Regidx s0_idx = s00 /\
          (forall r : mword 5, is_cs_idx r = true ->
             r <> csp_rs1 -> r <> s0_idx -> Mf !!! Regidx r = M !!! Regidx r) ⌝ -∗
        sie_cap_gpr KT1 Mf (k + 2) false p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro HMsp.
    iIntros "#Htcap Hcg #Htext Hpc Hbra Hbs0 Hcont".
    (* ---- +0x0e: rdtime a5 ---- *)
    iPoseProof (cii_0e with "Htext") as "Hi0e".
    iApply (wp_csrr_time_s_sconf (mword_of_int (KernelSyms.clockintr + 0x0e)) a5_idx M k
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Htcap Hcg Hpc Hi0e").
    iIntros (tv). iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T0 := <[Regidx a5_idx := regval_into_reg tv]> M).
    change (<[Regidx a5_idx := regval_into_reg tv]> M) with T0.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ---- +0x12: lui a4,0xf4 ---- *)
    iPoseProof (cii_12 with "Htext") as "Hi12".
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.clockintr + 0x12)) a4_idx (mword_of_int 0xf4 : mword 20)
              (luival (mword_of_int 0xf4 : mword 20)) T0 k false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi12").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T1 := <[Regidx a4_idx := regval_into_reg (luival (mword_of_int 0xf4 : mword 20))]> T0).
    change (<[Regidx a4_idx := regval_into_reg (luival (mword_of_int 0xf4 : mword 20))]> T0) with T1.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- +0x16: addi a4,a4,576 ---- *)
    iPoseProof (cii_16 with "Htext") as "Hi16".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.clockintr + 0x16)) a4_idx a4_idx (mword_of_int 0x240 : mword 12)
              T1 k false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T2 := <[Regidx a4_idx := regval_into_reg
        (add_vec (rget T1 a4_idx) (sign_extend' 64 (mword_of_int 0x240 : mword 12)))]> T1).
    change (<[Regidx a4_idx := regval_into_reg
        (add_vec (rget T1 a4_idx) (sign_extend' 64 (mword_of_int 0x240 : mword 12)))]> T1) with T2.
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* ---- +0x1a: c.add a5,a5,a4 ---- *)
    iPoseProof (cii_1a with "Htext") as "Hi1a".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.clockintr + 0x1a)) a5_idx a4_idx T2 k false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T3 := <[Regidx a5_idx := regval_into_reg
        (add_vec (rget T2 a5_idx) (rget T2 a4_idx))]> T2).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (rget T2 a5_idx) (rget T2 a4_idx))]> T2) with T3.
    assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* ---- +0x1c: csrw stimecmp,a5 -- the new deadline ---- *)
    iPoseProof (cii_1c with "Htext") as "Hi1c".
    iApply (wp_csrw_stimecmp_s_sconf (mword_of_int (KernelSyms.clockintr + 0x1c)) a5_idx T3 k
              ltac:(vm_compute; discriminate)
              with "Htcap Hcg Hpc Hi1c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpc20 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    (* ---- the frame cells, in c.ldsp's own address spelling ---- *)
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [| vm_compute; discriminate].
      rewrite /T0 upd_ne; [| vm_compute; discriminate]. exact HMsp. }
    assert (Hpa1 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HT3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    (* ---- +0x20: c.ldsp ra,8(sp) ---- *)
    iPoseProof (cii_20 with "Htext") as "Hi20".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.clockintr + 0x20)) (mword_of_int 1 : mword 6) ra_idx
              T3 k ra0 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 Hbra").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbra".
    set (T4 := <[Regidx ra_idx := regval_into_reg ra0]> T3).
    change (<[Regidx ra_idx := regval_into_reg ra0]> T3) with T4.
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = T3 !!! Regidx csp_rs1)
      by (rewrite /T4 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -Hpa2 -HT4sp) in "Hbs0".
    (* ---- +0x22: c.ldsp s0,0(sp) ---- *)
    iPoseProof (cii_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.clockintr + 0x22)) (mword_of_int 0 : mword 6) s0_idx
              T4 k s00 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 Hbs0").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs0".
    set (T5 := <[Regidx s0_idx := regval_into_reg s00]> T4).
    change (<[Regidx s0_idx := regval_into_reg s00]> T4) with T5.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- +0x24: c.addi sp,16 -- the frame pop ---- *)
    assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate]. exact HT3sp. }
    assert (Hwv : add_vec (T5 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite HT5sp.
      assert (Hps : pa_stk sp0 2
                    = add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
      { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hps. apply frame_cancel_16. }
    assert (Hpop : T5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T5 !!! Regidx csp_rs1)
                               (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. exact HT5sp. }
    iEval (rewrite Hpa1) in "Hbra".
    iEval (rewrite HT4sp Hpa2) in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iPoseProof (cii_24 with "Htext") as "Hi24".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.clockintr + 0x24)) (mword_of_int 16 : mword 6)
              T5 k 2 false Hpop
              with "Hcg Hpc Hi24 Hframe").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T6 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (T5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T5).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T5 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T5) with T6.
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* ---- +0x26: c.ret ---- *)
    assert (HT6ra : T6 !!! Regidx ra_idx = ra0).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4. apply upd_eq. }
    assert (HT6rg : rget T6 ra_idx = ra0) by (rgne; exact HT6ra).
    iPoseProof (cii_26 with "Htext") as "Hi26".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.clockintr + 0x26)) ra_idx T6 (k + 2)%nat false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi26").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HT6rg) in "Hpc".
    (* ---- the register facts the callers need ---- *)
    assert (HT6sp : T6 !!! Regidx csp_rs1 = sp0) by (rewrite /T6 upd_eq; exact Hwv).
    assert (HT6s0 : T6 !!! Regidx s0_idx = s00).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate]. rewrite /T5. apply upd_eq. }
    assert (HT6thr : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> s0_idx -> T6 !!! Regidx r = M !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> mword_of_int 14) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T6 upd_ne; [| congruence].
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      rewrite /T0 upd_ne; [| congruence]. reflexivity. }
    iApply ("Hcont" $! T6 with "[%] Hcg Hpc").
    split; [exact HT6sp|]. split; [exact HT6s0|]. exact HT6thr.
  Qed.

  (* ================================================================== *)
  (* THE WHOLE FUNCTION.                                                 *)
  (* ================================================================== *)
  Lemma wp_clockintr_sconf  (γl : gname) (γs : list gname)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (lks : gset string)
    : wp_clockintr_sconf_body γl γs m n eb p av lks.
  Proof.
    cbv beta delta [wp_clockintr_sconf_body].
    intros pcE ret_tgt Hn Hav Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (ra0 := (m !!! Regidx ra_idx : mword 64)).
    set (s00 := (m !!! Regidx s0_idx : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Htcap Htk Hcont".
    (* release's exit index, fixed once here (it is used only at the very end) *)
    iDestruct (ci_outb_false m av n eb p lks with "Hcg Hcnt") as %Hout.
    (* ===================== PROLOGUE (16-byte frame) ===================== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (cii_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m av 2 false
              ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iApply wp_next_off_intro. iIntros "Hcg Hframe Hpc".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /A0 upd_eq; exact Hpush).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vra vs0) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (A0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (A0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- +0x02: c.sdsp ra,8(sp) ---- *)
    iPoseProof (cii_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.clockintr + 0x02)) (mword_of_int 1 : mword 6) ra_idx
              A0 (av - 2)%nat vra false
              with "Hcg Hpc Hi02 Hbra").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbra".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,0(sp) ---- *)
    iPoseProof (cii_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.clockintr + 0x04)) (mword_of_int 0 : mword 6) s0_idx
              A0 (av - 2)%nat vs0 false
              with "Hcg Hpc Hi04 Hbs0").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hbs0".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* the saved values are the entry ra/s0.  [c.sdsp] stores [rget A0 rs2],
       so the value side needs the [rgne] respelling as well as the address. *)
    assert (HA0ra : A0 !!! Regidx ra_idx = ra0)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s0 : A0 !!! Regidx s0_idx = s00)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0rag : rget A0 ra_idx = ra0) by (rgne; exact HA0ra).
    assert (HA0s0g : rget A0 s0_idx = s00) by (rgne; exact HA0s0).
    iEval (rewrite Hpa1 HA0rag) in "Hbra".
    iEval (rewrite Hpa2 HA0s0g) in "Hbs0".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iPoseProof (cii_06 with "Htext") as "Hi06".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.clockintr + 0x06)) (Cregidx (mword_of_int 0))
              (mword_of_int 4 : mword 8) s0_idx A0 (av - 2)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A1 := <[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> A0).
    change (<[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> A0) with A1.
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /A1 upd_ne; [exact HA0sp | vm_compute; discriminate]).
    (* NO tp fact: [tp_pin] makes the map's tp slot unobservable, and the true
       tp is [cid_word_of cpu_id] by construction ([rget_tp]). *)
    (* ===================== +0x08: cpuid() ===================== *)
    iPoseProof (cii_08 with "Htext") as "Hi08".
    iApply (Cpuid.wp_call_cpuid_sconf_cs KT1 (mword_of_int (KernelSyms.clockintr + 0x08))
              (mword_of_int 2094036 : mword 21) A1 (av - 2)%nat p
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi08").
    iIntros (mo) "Hcg Hpc %Hcs0".
    destruct Hcs0 as [HcsA1 Ha0].
    assert (Hpc0c : ret_pc (<[Regidx ra_idx := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.clockintr + 0x08) : mword 64) 4)]> A1 !!! Regidx ra_idx)
                    = mword_of_int (KernelSyms.clockintr + 0x0c)).
    { rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc0c) in "Hpc".
    (* a0 is this hart's id *)
    assert (Hmoa0 : mo !!! Regidx a0_idx = cid_word).
    { rewrite Ha0. exact (eq_trans (f_equal cpuid_ret (rget_tp A1)) cpuid_ret_cid). }
    assert (Hmosp : mo !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite (callee_saved_lookup HcsA1 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HA1sp. }
    (* the callee-saved registers clockintr itself never touches, at [mo] *)
    assert (Hmothr : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> s0_idx -> mo !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      rewrite (callee_saved_lookup HcsA1 r Hr).
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    iPoseProof (cii_0c with "Htext") as "Hi0c".
    (* ===================== the cpuid() == 0 case split ===================== *)
    destruct (tick_hart) as [|] eqn:Hth.
    - (* ---------------- THIS HART KEEPS TIME: the tick block ------------- *)
      iDestruct "Htk" as "[%Hno | (#Hlk & #Hpi)]".
      { rewrite Hth in Hno. discriminate. }
      iPoseProof "Hpi" as "Hpi2".
      iDestruct "Hpi2" as "[%Hlen _]".
      iDestruct (is_tickslock_lock with "Hlk") as "#Hlkl".
      assert (Hzero : eq_vec (rget mo a0_idx) (zero_reg : mword 64) = true)
        by (rgne; rewrite Hmoa0; exact Hth).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.clockintr + 0x0c)) (mword_of_int 14 : mword 8)
                (Cregidx (mword_of_int 2)) a0_idx mo (av - 2)%nat false
                creg_c2 ltac:(vm_compute; discriminate) Hzero
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0c").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpc28 : add_vec (mword_of_int (KernelSyms.clockintr + 0x0c) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.clockintr + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      (* ---- +0x28/+0x2c: a0 := &tickslock ---- *)
      iPoseProof (cii_28 with "Htext") as "Hi28".
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.clockintr + 0x28)) a0_idx (mword_of_int 0x16 : mword 20)
                mo (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi28").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B0 := <[Regidx a0_idx := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.clockintr + 0x28) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> mo).
      change (<[Regidx a0_idx := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.clockintr + 0x28) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> mo) with B0.
      assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2c) in "Hpc".
      iPoseProof (cii_2c with "Htext") as "Hi2c".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.clockintr + 0x2c)) a0_idx a0_idx (mword_of_int 0xd06 : mword 12)
                B0 (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2c").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B1 := <[Regidx a0_idx := regval_into_reg
          (add_vec (rget B0 a0_idx) (sign_extend' 64 (mword_of_int 3334 : mword 12)))]> B0).
      change (<[Regidx a0_idx := regval_into_reg
          (add_vec (rget B0 a0_idx) (sign_extend' 64 (mword_of_int 3334 : mword 12)))]> B0) with B1.
      assert (Hpc30 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc30) in "Hpc".
      (* ---- +0x30: jal ra,acquire ---- *)
      iPoseProof (cii_30 with "Htext") as "Hi30".
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.clockintr + 0x30)) ra_idx (mword_of_int 2090688 : mword 21)
                B1 (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi30").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B2 := <[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.clockintr + 0x30) : mword 64) 4)]> B1).
      change (<[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.clockintr + 0x30) : mword 64) 4)]> B1) with B2.
      assert (Hjacq : add_vec (mword_of_int (KernelSyms.clockintr + 0x30) : mword 64)
                        (sign_extend' 64 (mword_of_int 2090688 : mword 21))
                      = mword_of_int KernelSyms.acquire)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjacq) in "Hpc".
      assert (HB2ra : B2 !!! Regidx ra_idx
                      = add_vec_int (mword_of_int (KernelSyms.clockintr + 0x30) : mword 64) 4)
        by (rewrite /B2 upd_eq; reflexivity).
      assert (HB2a0 : B2 !!! Regidx a0_idx = a_tickslock).
      { rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_eq. rgne. rewrite /B0 upd_eq.
        rewrite /a_tickslock. apply bv_eq; vm_compute; reflexivity. }
      assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [| vm_compute; discriminate].
        rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact Hmosp. }
      (* ===================== acquire(&tickslock) ===================== *)
      iApply (Acquire.wp_acquire_sconf KT1 γl "time"%string ticks_res B2
                n eb p (av - 2)%nat false lks
                ltac:(lia)
                ltac:(lia)
                Hbelow
                with "Hcg Hcnt Htext Hpc [Hlkl]").
      all: try lkbelow.
      { iEval (rewrite HB2a0). iExact "Hlkl". }
      iApply wp_next_off_intro.
      iIntros (ms MA) "%Hms Hcg Hpc %HcsA Htok HR Hcnt Hpay".
      assert (Hpc34 : ret_pc (B2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.clockintr + 0x34))
        by (rewrite HB2ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc34) in "Hpc".
      iDestruct "HR" as (t) "Hticks".
      (* ---- +0x34/+0x38: a4 := &ticks ---- *)
      iPoseProof (cii_34 with "Htext") as "Hi34".
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.clockintr + 0x34)) a4_idx (mword_of_int 0x8 : mword 20)
                MA (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi34").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D0 := <[Regidx a4_idx := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.clockintr + 0x34) : mword 64) (auipc_off (mword_of_int 0x8 : mword 20)))]> MA).
      change (<[Regidx a4_idx := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.clockintr + 0x34) : mword 64) (auipc_off (mword_of_int 0x8 : mword 20)))]> MA) with D0.
      assert (Hpc38 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc38) in "Hpc".
      iPoseProof (cii_38 with "Htext") as "Hi38".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.clockintr + 0x38)) a4_idx a4_idx (mword_of_int 0xdca : mword 12)
                D0 (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi38").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D1 := <[Regidx a4_idx := regval_into_reg
          (add_vec (rget D0 a4_idx) (sign_extend' 64 (mword_of_int 3530 : mword 12)))]> D0).
      change (<[Regidx a4_idx := regval_into_reg
          (add_vec (rget D0 a4_idx) (sign_extend' 64 (mword_of_int 3530 : mword 12)))]> D0) with D1.
      assert (Hpc3c : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc3c) in "Hpc".
      assert (HD1a4 : D1 !!! Regidx a4_idx = a_ticks).
      { rewrite /D1 upd_eq. rgne. rewrite /D0 upd_eq.
        rewrite /a_ticks. apply bv_eq; vm_compute; reflexivity. }
      assert (Haddrt : add_vec (rget D1 a4_idx) (sign_extend' 64 (mword_of_int 0 : mword 12))
                       = a_ticks)
        by (rgne; rewrite HD1a4; apply addv_sext0).
      (* ---- +0x3c: c.lw a5,0(a4) -- read ticks, under the lock ---- *)
      iPoseProof (cii_3c with "Htext") as "Hi3c".
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.clockintr + 0x3c)) a5_idx a4_idx
                (mword_of_int 0 : mword 12) D1 (av - 2)%nat t false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3c [Hticks]").
      { iEval (rewrite Haddrt). iExact "Hticks". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hticks".
      iEval (rewrite Haddrt) in "Hticks".
      set (D2 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 (t : mword 32))]> D1).
      change (<[Regidx a5_idx := regval_into_reg (sign_extend' 64 (t : mword 32))]> D1) with D2.
      assert (Hpc3e : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc3e) in "Hpc".
      (* ---- +0x3e: c.addiw a5,1 -- ticks + 1 as an int ---- *)
      iPoseProof (cii_3e with "Htext") as "Hi3e".
      iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.clockintr + 0x3e)) a5_idx (mword_of_int 1 : mword 6)
                D2 (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D3 := <[Regidx a5_idx := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (rget D2 a5_idx)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D2).
      change (<[Regidx a5_idx := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (rget D2 a5_idx)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> D2) with D3.
      assert (Hpc40 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc40) in "Hpc".
      (* ---- +0x40: c.sw a5,0(a4) -- the incremented counter ---- *)
      assert (HD3a4 : D3 !!! Regidx a4_idx = a_ticks).
      { rewrite /D3 upd_ne; [| vm_compute; discriminate].
        rewrite /D2 upd_ne; [| vm_compute; discriminate]. exact HD1a4. }
      assert (Haddrt3 : add_vec (rget D3 a4_idx) (sign_extend' 64 (mword_of_int 0 : mword 12))
                        = a_ticks)
        by (rgne; rewrite HD3a4; apply addv_sext0).
      iPoseProof (cii_40 with "Htext") as "Hi40".
      iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.clockintr + 0x40)) a5_idx a4_idx
                (mword_of_int 0 : mword 12) D3 (av - 2)%nat t false
                with "Hcg Hpc Hi40 [Hticks]").
      { iEval (rewrite Haddrt3). iExact "Hticks". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hticks".
      iEval (rewrite Haddrt3) in "Hticks".
      assert (Hpc42 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc42) in "Hpc".
      (* ---- +0x42: c.mv a0,a4 -- the wakeup channel ---- *)
      iPoseProof (cii_42 with "Htext") as "Hi42".
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.clockintr + 0x42)) a0_idx a4_idx D3 (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi42").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D4 := <[Regidx a0_idx := regval_into_reg
          (add_vec zero_reg (rget D3 a4_idx))]> D3).
      change (<[Regidx a0_idx := regval_into_reg
          (add_vec zero_reg (rget D3 a4_idx))]> D3) with D4.
      assert (Hpc44 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc44) in "Hpc".
      (* ---- +0x44: jal ra,wakeup ---- *)
      iPoseProof (cii_44 with "Htext") as "Hi44".
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.clockintr + 0x44)) ra_idx (mword_of_int 2095682 : mword 21)
                D4 (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi44").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (D5 := <[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.clockintr + 0x44) : mword 64) 4)]> D4).
      change (<[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.clockintr + 0x44) : mword 64) 4)]> D4) with D5.
      assert (Hjwk : add_vec (mword_of_int (KernelSyms.clockintr + 0x44) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095682 : mword 21))
                     = mword_of_int KernelSyms.wakeup)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjwk) in "Hpc".
      assert (HD5ra : D5 !!! Regidx ra_idx
                      = add_vec_int (mword_of_int (KernelSyms.clockintr + 0x44) : mword 64) 4)
        by (rewrite /D5 upd_eq; reflexivity).
      assert (HD5sp : D5 !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite /D5 upd_ne; [| vm_compute; discriminate].
        rewrite /D4 upd_ne; [| vm_compute; discriminate].
        rewrite /D3 upd_ne; [| vm_compute; discriminate].
        rewrite /D2 upd_ne; [| vm_compute; discriminate].
        rewrite /D1 upd_ne; [| vm_compute; discriminate].
        rewrite /D0 upd_ne; [| vm_compute; discriminate].
        rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HB2sp. }
      (* ===================== wakeup(&ticks) ===================== *)
      iApply (Wakeup.wp_wakeup_sconf D5 γs p
                (S n) (av - 2)%nat eb false ({["time"]} ∪ lks)
                ltac:(lia)
                ltac:(intro r; apply rf_to_gmap_dom)
                Hlen
                ltac:(lia)
                (locks_below_union_singleton lks "time" "proc"
                   ltac:(vm_compute; lia)
                   ltac:(lkbelow))
                with "Hcg Hcnt Htext Hpc Hpi").
      all: try lkbelow.
      iApply wp_next_off_intro.
      iIntros (MW) "%HcsW Hcg Hcnt #Htext2 Hpc".
      destruct HcsW as [HcsW _].
      assert (Hpc48 : ret_pc (D5 !!! Regidx ra_idx) = mword_of_int (KernelSyms.clockintr + 0x48))
        by (rewrite HD5ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc48) in "Hpc".
      (* ---- +0x48/+0x4c: a0 := &tickslock (again) ---- *)
      iPoseProof (cii_48 with "Htext") as "Hi48".
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.clockintr + 0x48)) a0_idx (mword_of_int 0x16 : mword 20)
                MW (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi48").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (E0 := <[Regidx a0_idx := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.clockintr + 0x48) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> MW).
      change (<[Regidx a0_idx := regval_into_reg
          (add_vec (mword_of_int (KernelSyms.clockintr + 0x48) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> MW) with E0.
      assert (Hpc4c : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x4c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc4c) in "Hpc".
      iPoseProof (cii_4c with "Htext") as "Hi4c".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.clockintr + 0x4c)) a0_idx a0_idx (mword_of_int 0xce6 : mword 12)
                E0 (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4c").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (E1 := <[Regidx a0_idx := regval_into_reg
          (add_vec (rget E0 a0_idx) (sign_extend' 64 (mword_of_int 3302 : mword 12)))]> E0).
      change (<[Regidx a0_idx := regval_into_reg
          (add_vec (rget E0 a0_idx) (sign_extend' 64 (mword_of_int 3302 : mword 12)))]> E0) with E1.
      assert (Hpc50 : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.clockintr + 0x50))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc50) in "Hpc".
      (* ---- +0x50: jal ra,release ---- *)
      iPoseProof (cii_50 with "Htext") as "Hi50".
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.clockintr + 0x50)) ra_idx (mword_of_int 2090792 : mword 21)
                E1 (av - 2)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi50").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (E2 := <[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.clockintr + 0x50) : mword 64) 4)]> E1).
      change (<[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.clockintr + 0x50) : mword 64) 4)]> E1) with E2.
      assert (Hjrel : add_vec (mword_of_int (KernelSyms.clockintr + 0x50) : mword 64)
                        (sign_extend' 64 (mword_of_int 2090792 : mword 21))
                      = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjrel) in "Hpc".
      assert (HE2ra : E2 !!! Regidx ra_idx
                      = add_vec_int (mword_of_int (KernelSyms.clockintr + 0x50) : mword 64) 4)
        by (rewrite /E2 upd_eq; reflexivity).
      assert (HE2a0 : E2 !!! Regidx a0_idx = a_tickslock).
      { rewrite /E2 upd_ne; [| vm_compute; discriminate].
        rewrite /E1 upd_eq. rgne. rewrite /E0 upd_eq.
        rewrite /a_tickslock. apply bv_eq; vm_compute; reflexivity. }
      assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite /E2 upd_ne; [| vm_compute; discriminate].
        rewrite /E1 upd_ne; [| vm_compute; discriminate].
        rewrite /E0 upd_ne; [| vm_compute; discriminate].
        rewrite (callee_saved_lookup HcsW csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HD5sp. }
      (* ===================== release(&tickslock) ===================== *)
      iDestruct (ticks_res_intro _ with "Hticks") as "HR".
      (* clockintr is entered interrupts-OFF at a level that provably does not
         unwind to 0 with an enabled base ([Hout]), so its exit arm is [false]
         and the reserve release owes is ZERO -- [trap_res false + N] IS [N].
         The rewrite only makes that spelling explicit for the seam. *)
      assert (Hridx : (av - 2)%nat
                      = (trap_res (match n with O => eb | S _ => false end)
                         + (av - 2))%nat) by (rewrite Hout; reflexivity).
      iEval (rewrite Hridx) in "Hcg".
      iApply (Release.wp_release_sconf KT1 γl a_tickslock "time"%string ticks_res E2
                n eb p (av - 2)%nat
                ({["time"]} ∪ lks)
                ltac:(rewrite HE2a0; apply addv_sext0)
                ltac:(lia)
                with "Hcg Htext Hpc [Hlkl] [Htok] [HR] Hcnt Hpay").
      { iExact "Hlkl". }
      { iExact "Htok". }
      { iExact "HR". }
      rewrite Hout. iApply wp_next_off_intro.
      iIntros (MR) "Hcg Hpc %HcsR Hcnt".
      (* clockintr is BALANCED: the set release hands back collapses to the
         entry [lks] -- [Hfresh] is what makes the singleton insert/delete
         cancel. *)
      assert (Hsetback : ({["time"]} ∪ lks) ∖ {["time"]} = lks)
      by (apply locks_add_del_below; lkbelow).
      iEval (rewrite Hsetback) in "Hcnt".
      assert (Hpc54 : ret_pc (E2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.clockintr + 0x54))
        by (rewrite HE2ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc54) in "Hpc".
      (* ---- +0x54: c.j back to the timer tail ---- *)
      assert (HMRsp : MR !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite (callee_saved_lookup HcsR csp_rs1 ltac:(vm_compute; reflexivity)). exact HE2sp. }
      iPoseProof (cii_54 with "Htext") as "Hi54".
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.clockintr + 0x54))
                (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0")))
                MR (av - 2)%nat false
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi54").
      iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
      assert (Hpcback : add_vec (mword_of_int (KernelSyms.clockintr + 0x54) : mword 64)
                          (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2013 : mword 11) ('b"0"))))
                        = mword_of_int (KernelSyms.clockintr + 0x0e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpcback) in "Hpc".
      (* ===================== the shared timer tail ===================== *)
      iApply (wp_ci_tail MR sp0 ra0 s00 (av - 2)%nat p HMRsp
                with "Htcap Hcg Htext Hpc Hbra Hbs0").
      iIntros (Mf) "[%Hfsp [%Hfs0 %Hfthr]] Hcg Hpc".
      assert (Hnk : ((av - 2) + 2)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      iApply ("Hcont" $! Mf with "[%] Hcg Hcnt [Hpc]").
      { unfold callee_saved.
        assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                  r <> csp_rs1 -> r <> s0_idx -> Mf !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8.
          rewrite (Hfthr r Hr Ncsp N8).
          rewrite (callee_saved_lookup HcsR r Hr).
          assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N14 : r <> mword_of_int 14) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /E2 upd_ne; [| congruence].
          rewrite /E1 upd_ne; [| congruence].
          rewrite /E0 upd_ne; [| congruence].
          rewrite (callee_saved_lookup HcsW r Hr).
          rewrite /D5 upd_ne; [| congruence].
          rewrite /D4 upd_ne; [| congruence].
          rewrite /D3 upd_ne; [| congruence].
          rewrite /D2 upd_ne; [| congruence].
          rewrite /D1 upd_ne; [| congruence].
          rewrite /D0 upd_ne; [| congruence].
          rewrite (callee_saved_lookup HcsA r Hr).
          rewrite /B2 upd_ne; [| congruence].
          rewrite /B1 upd_ne; [| congruence].
          rewrite /B0 upd_ne; [| congruence].
          exact (Hmothr r Hr Ncsp N8). }
        split; [exact Hfsp|].
        split; [exact Hfs0|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        apply Hthr; vm_compute; first [reflexivity | discriminate]. }
      { iExact "Hpc". }
      iRight. iFrame "Hlk Hpi".
    - (* ---------------- ANOTHER HART: straight to the timer tail -------- *)
      assert (Hnzero : eq_vec (rget mo a0_idx) (zero_reg : mword 64) = false)
        by (rgne; rewrite Hmoa0; exact Hth).
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.clockintr + 0x0c)) (mword_of_int 14 : mword 8)
                (Cregidx (mword_of_int 2)) a0_idx mo (av - 2)%nat false
                creg_c2 ltac:(vm_compute; discriminate) Hnzero
                with "Hcg Hpc Hi0c").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.clockintr + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.clockintr + 0x0e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc0e) in "Hpc".
      iApply (wp_ci_tail mo sp0 ra0 s00 (av - 2)%nat p Hmosp
                with "Htcap Hcg Htext Hpc Hbra Hbs0").
      iIntros (Mf) "[%Hfsp [%Hfs0 %Hfthr]] Hcg Hpc".
      assert (Hnk : ((av - 2) + 2)%nat = av) by lia.
      iEval (rewrite Hnk) in "Hcg".
      iApply ("Hcont" $! Mf with "[%] Hcg Hcnt Hpc Htk").
      unfold callee_saved.
      assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                r <> csp_rs1 -> r <> s0_idx -> Mf !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8.
        rewrite (Hfthr r Hr Ncsp N8). exact (Hmothr r Hr Ncsp N8). }
      split; [exact Hfsp|].
      split; [exact Hfs0|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
      apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofClockintr.

End ClockintrProof.
