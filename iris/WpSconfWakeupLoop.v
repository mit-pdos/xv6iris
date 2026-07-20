(* WpSconfWakeupLoop.v -- the wakeup proc[]-table loop over the SIE-agnostic
   sconf world (kalloc cone, stage 8).  The sconf mirror of [wp_wakeup_loop]
   (WpWakeup.v): a bounded fuel induction over the 64-entry proc[] table that,
   per proc, acquires the proc lock, wakes it if SLEEPING on the given chan,
   and releases -- threading the counting token [intr_count] NET-ZERO across
   each acquire/release pair (acquire lvl->S lvl, release S lvl->lvl).

   The one design subtlety absent from the smode proof (where intena=0 under
   SIE=0): the intena cell is held EXISTENTIALLY in the loop invariant --
   [exists iv, wk_intena_addr a0f |->4 iv].  release passes a_int through
   unchanged and acquire accepts any incoming intena, so whether the noff
   counter is 0 (acquire rewrites to po_intena_val ms) or nonzero (passthrough)
   the existential absorbs it and the invariant closes with no ms dependence.
   See CLAUDE.md's wakeup note for the full design. *)
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
Require Import WpMycpu.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved StackOwn.
Require Import RiscvExtras.
Require Import KptTree.
Require Import IntrDefs WpIntenaBits.
Require Import IntrDefs.
Require Import VcGenS.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSconfAcquire WpSconfRelease.
Require Import WpWakeup WpSconfWakeup WpSconfKfree.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* release's nv1, when its noff argument is the acquire-incremented
   [wk_noff_acq noffv], cancels back to [sign_extend' 64 noffv] -- so release's
   coupling premise ([neq_vec nv1 zero <-> lvl=0]) reduces to the clean loop
   entry coupling on [noffv].  Same identity as [kfree_nv1_cancel_pure], stated
   with [wk_noff_acq] folded so it matches the loop goal. *)
Lemma wk_release_nv1_cancel (noffv : mword 32) :
  sign_extend' 64 (subrange_vec_dec (add_vec
     (sign_extend' 64 (wk_noff_acq noffv))
     (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
  = sign_extend' 64 noffv.
Proof. unfold wk_noff_acq. exact (kfree_nv1_cancel_pure noffv). Qed.

Section WpSconfWakeupLoop.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* the mutable wakeup resources the loop threads, sconf flavour.  Mirrors the
     smode [wk_res] but (a) the scratch stack is NO LONGER a conjunct here: the
     [sie_cap … av] the loop threads (av >= 10) owns the deep slots directly, and
     sconf acquire/release/myproc borrow them from the cap internally, and (b) the
     intena word is EXISTENTIAL (see header).  [noffv] is the fixed entry noff,
     restored by each acquire/release pair; the counting token [intr_count] is
     threaded ALONGSIDE (not in this bundle, since it changes shape acquire->S /
     release->pred). *)
  Definition wk_res_sconf (γs : list gname) (spF a0f : mword 64) (noffv : mword 32) : iProp Σ :=
    (wk_noff_addr a0f ↦₄ noffv ∗
     (∃ iv : mword 32, wk_intena_addr a0f ↦₄ iv) ∗
     wk_lockcells γs)%I.

  (* wakeup only RELAYS parked contexts (SLEEPING->RUNNABLE, untouched), never
     resumes them, so the smode-flavoured [proc_lock_res] (whose [proc_ctx]
     embeds a [valid_context] over the smode [sconf R gc bsie dq]) is threaded
     OPAQUELY here: the wakeup CODE runs over the sie-agnostic sconf world while
     the proc-lock RESOURCE stays the existing one (it ports later, with the
     scheduler).  Hence the smode [R/gc/bsie/dq] parameters -- carried, never
     inspected. *)
  Lemma wp_wakeup_loop_sconf
      (γ : gname) (root_ppn : mword 44)
      (Rreg : s_regime) (γc : gname) (bsie : mword 1) (dq : dfrac)
      (Φ : mval -> iProp Σ)
      (γs : list gname) (spF a0f rtp chan : mword 64) (noffv : mword 32)
      (vra vs0 vs1 vs2 vs3 vs4 vs5 : mword 64)
      (vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) (lvl : nat) (av : nat) :
    length γs = NPROC ->
    mycpu_ret rtp = a0f ->
    eq_vec (zero_reg : mword 64) (mycpu_ret rtp) = false ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 (wk_noff_acq noffv)) = false ->
    wk_noff_rel (wk_noff_acq noffv) = noffv ->
    (neq_vec (sign_extend' 64 noffv) zero_reg = false <-> lvl = 0%nat) ->
    (10 <= av)%nat ->
    procs_inv Rreg Φ γc bsie dq γs -∗
    (* the loop's exit continuation: control at the epilogue entry [wakeup+0x58]. *)
    ( ∀ Mexit : gmap regidx (mword 64),
        ⌜ Mexit !!! Regidx csp_rs1 = spF
          /\ Mexit !!! Regidx (mword_of_int 4)  = rtp
          /\ Mexit !!! Regidx (mword_of_int 22) = vs6
          /\ Mexit !!! Regidx (mword_of_int 23) = vs7
          /\ Mexit !!! Regidx (mword_of_int 24) = vs8
          /\ Mexit !!! Regidx (mword_of_int 25) = vs9
          /\ Mexit !!! Regidx (mword_of_int 26) = vs10
          /\ Mexit !!! Regidx (mword_of_int 27) = vs11
          /\ (forall r : regidx, r ∈ dom Mexit) ⌝ -∗
        sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn Mexit av -∗
        intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
        kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x58)) -∗ gpr_file Mexit -∗
        wk_res_sconf γs spF a0f noffv -∗
        wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    ∀ (k : nat) (M : gmap regidx (mword 64)),
      ⌜(k < NPROC)%nat⌝ -∗ ⌜wk_loop_regs M spF rtp chan vs6 vs7 vs8 vs9 vs10 vs11 k⌝ -∗
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn M av -∗
      intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
      kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗ gpr_file M -∗
      wk_res_sconf γs spF a0f noffv -∗ wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hlen Ha0f Hmycpu_nz Hnf_pos Hnf_rt Hcoupling Hav.
    iIntros "#Hpinv Hqexit".
    (* BOUNDED loop: ordinary Coq induction on a [fuel] bounding the remaining
       iterations [NPROC - k] -- no Löb needed. *)
    iAssert (∀ (fuel k : nat) (M : gmap regidx (mword 64)),
               ⌜(NPROC - k <= fuel)%nat⌝ -∗ ⌜(k < NPROC)%nat⌝ -∗
               ⌜wk_loop_regs M spF rtp chan vs6 vs7 vs8 vs9 vs10 vs11 k⌝ -∗
               ( ∀ Mexit : gmap regidx (mword 64),
                   ⌜ Mexit !!! Regidx csp_rs1 = spF
          /\ Mexit !!! Regidx (mword_of_int 4)  = rtp
          /\ Mexit !!! Regidx (mword_of_int 22) = vs6
          /\ Mexit !!! Regidx (mword_of_int 23) = vs7
          /\ Mexit !!! Regidx (mword_of_int 24) = vs8
          /\ Mexit !!! Regidx (mword_of_int 25) = vs9
          /\ Mexit !!! Regidx (mword_of_int 26) = vs10
          /\ Mexit !!! Regidx (mword_of_int 27) = vs11
          /\ (forall r : regidx, r ∈ dom Mexit) ⌝ -∗
                   sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn Mexit av -∗
                   intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
                   kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x58)) -∗ gpr_file Mexit -∗
                   wk_res_sconf γs spF a0f noffv -∗
                   wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
                   WP (Loop : expr riscv_lang) {{ Φ }}) -∗
               sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn M av -∗
               intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
               kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗ gpr_file M -∗
               wk_res_sconf γs spF a0f noffv -∗ wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
               WP (Loop : expr riscv_lang) {{ Φ }})%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (k M) "%Hfuel %Hk %Hregs Hqexit Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile Hres Hframe".
        exfalso. lia. }
      iIntros (k M) "%Hfuel %Hk %Hregs Hqexit Hsc Hhs Hcap Hcnt Htlb #Htext Hpc Hfile Hres Hframe".
      destruct Hregs as (Hs1 & Hsp & Htp & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11 & Hdom).
      (* ---- shared tail [pc = wakeup+0x30]: p++ (0x30 addi s1,s1,360), then the
         termination test (0x34 beq s1,s2): exit to the epilogue at wakeup+0x58,
         else recurse into iteration k+1.  Captured once, reached from both the
         skip-self path (0x3c taken) and the release-return path (0x2c). ---- *)
      iAssert (∀ Mt : gmap regidx (mword 64),
                 ⌜ wk_loop_regs Mt spF rtp chan vs6 vs7 vs8 vs9 vs10 vs11 k ⌝ -∗
                 sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn Mt av -∗
                 intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
                 pc_is (mword_of_int (KernelSyms.wakeup + 0x30)) -∗ gpr_file Mt -∗
                 wk_res_sconf γs spF a0f noffv -∗ wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
                 WP (Loop : expr riscv_lang) {{ Φ }})%I
        with "[Hqexit]" as "Htail".
      { iIntros (Mt) "%Hmt Hsc Hhs Hcap Hcnt Htlb Hpc Hfile Hres Hframe".
        destruct Hmt as (Ht1 & Htsp & Http & Ht18 & Ht19 & Ht20 & Ht21 & Ht22 & Ht23 & Ht24 & Ht25 & Ht26 & Ht27 & Htdom).
        iPoseProof (wki_30 with "Htext") as "Hi30".
        iPoseProof (wki_34 with "Htext") as "Hi34".
        (* 0x30 addi s1,s1,360 : s1 := &proc[k+1] *)
        iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x30))
                  (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 360 : mword 12)
                  Mt av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hsc Hhs Hcap Htlb Hpc Hfile Hi30 [-]").
        iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
        set (Mt30 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
             (add_vec (Mt !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> Mt).
        assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x34))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp34) in "Hpc".
        assert (HMt30_9 : Mt30 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr (S k)).
        { rewrite /Mt30 lookup_total_insert. rewrite Ht1. apply (proc_addr_succ k). }
        assert (HMt30_18 : Mt30 !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC).
        { rewrite /Mt30 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ht18. }
        (* 0x34 beq s1,s2 : exit iff &proc[k+1] = &proc[NPROC]. *)
        destruct (eq_vec (Mt30 !!! Regidx (mword_of_int 9 : mword 5))
                         (Mt30 !!! Regidx (mword_of_int 18 : mword 5))) eqn:Hcmp.
        + (* TAKEN: p reached &proc[NPROC]; exit to epilogue at wakeup+0x58 *)
          iApply (wp_beq_taken_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x34))
                    (mword_of_int 36 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                    Mt30 av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp ltac:(vm_compute; reflexivity)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi34 [-]").
          iNext. iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
          assert (Htgt58 : add_vec (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64)
                             (sign_extend' 64 (mword_of_int 36 : mword 13)) = mword_of_int (KernelSyms.wakeup + 0x58))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt58) in "Hpc".
          iApply ("Hqexit" $! Mt30 with "[] Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile Hres Hframe").
          iPureIntro.
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Htsp | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Http | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht22 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht23 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht24 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht25 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht26 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht27 | vm_compute; discriminate]|].
          intro r. rewrite /Mt30 dom_insert_L. apply elem_of_union_r. apply Htdom.
        + (* FALL: p < &proc[NPROC]; recurse into iteration k+1 *)
          iApply (wp_beq_fall_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x34))
                    (mword_of_int 36 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                    Mt30 av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp with "Hsc Hhs Hcap Htlb Hpc Hfile Hi34 [-]").
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
          assert (HkS : (S k < NPROC)%nat).
          { destruct (Nat.lt_ge_cases (S k) NPROC) as [Hlt | Hge]; [exact Hlt|].
            assert (HeqN : S k = NPROC) by lia.
            exfalso.
            assert (Hbad : eq_vec (Mt30 !!! Regidx (mword_of_int 9 : mword 5))
                             (Mt30 !!! Regidx (mword_of_int 18 : mword 5)) = true).
            { rewrite HMt30_9 HMt30_18 HeqN. apply wk_eq_vec_refl. }
            rewrite Hcmp in Hbad. discriminate. }
          assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x38))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp38) in "Hpc".
          iApply ("IHf" $! (S k) Mt30 with "[%] [%] [%] Hqexit Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile Hres Hframe").
          * lia.
          * exact HkS.
          * unfold wk_loop_regs.
            split; [exact HMt30_9|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Htsp | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Http | vm_compute; discriminate]|].
            split; [exact HMt30_18|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht19 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht20 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht21 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht22 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht23 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht24 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht25 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht26 | vm_compute; discriminate]|].
            split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht27 | vm_compute; discriminate]|].
            intro r. rewrite /Mt30 dom_insert_L. apply elem_of_union_r. apply Htdom. }
      (* ==================== loop body [0x38 .. 0x30] ==================== *)
      iPoseProof (wki_38 with "Htext") as "Hi38".
      (* ---- 0x38: jal ra, myproc (base JAL, 2-aligned target) ---- *)
      iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x38))
                (mword_of_int 1 : mword 5) (mword_of_int 2095482 : mword 21) M av
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                with "Hsc Hhs Hcap Htlb Hpc Hfile Hi38 [-]").
      iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
      set (Mj := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64) 4)]> M).
      assert (Hjtgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64)
                        (sign_extend' 64 (mword_of_int 2095482 : mword 21)) = mword_of_int KernelSyms.myproc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjtgt) in "Hpc".
      assert (HMjra : Mj !!! Regidx (mword_of_int 1 : mword 5)
                      = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64) 4)
        by (rewrite /Mj; apply lookup_total_insert).
      assert (HMjcsp : Mj !!! Regidx csp_rs1 = spF).
      { rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hsp. }
      (* ---- myproc(): a0 = proc_addr j (j<NPROC), callee-saved preserved.  Lend
         the deep custody (K := 10); intr_count [lvl] unchanged. ---- *)
      iDestruct "Hres" as "(Hnoffc & Hintc & Hlockcells)".
      iApply (wp_myproc_sconf γ root_ppn Φ Mj lvl av ltac:(lia)
                ltac:(rewrite HMjra; vm_compute; reflexivity)
                with "Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile [-]").
      iIntros (j mret) "%Hj %Hreta0 %Hpres Hsc Hhs Hcap Hcnt Htlb Hpc Hfile".
      (* pc is now wakeup+0x3c (myproc's bit-0-cleared return target) *)
      assert (Hret3c : update_vec_dec (add_vec (Mj !!! Regidx (mword_of_int 1 : mword 5))
                         (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                       = mword_of_int (KernelSyms.wakeup + 0x3c)).
      { rewrite HMjra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret3c) in "Hpc".
      (* s1 preserved by myproc: mret!!!s1 = proc_addr k *)
      assert (Hmrets1 : mret !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k).
      { rewrite (callee_saved_lookup Hpres (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
        rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hs1. }
      (* ---- 0x3c: beq a0,s1 : skip-self test ---- *)
      iPoseProof (wki_3c with "Htext") as "Hi3c".
      destruct (eq_vec (mret !!! Regidx (mword_of_int 10 : mword 5))
                       (mret !!! Regidx (mword_of_int 9 : mword 5))) eqn:Hcmp3.
      - (* TAKEN: a0 = s1 (current proc is myproc): skip to 0x30 (p++) *)
        iApply (wp_beq_taken_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x3c))
                  (mword_of_int 8180 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
                  mret av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp3 ltac:(vm_compute; reflexivity)
                  with "Hsc Hhs Hcap Htlb Hpc Hfile Hi3c [-]").
        iNext. iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
        assert (Htgt30 : add_vec (mword_of_int (KernelSyms.wakeup + 0x3c) : mword 64)
                           (sign_extend' 64 (mword_of_int 8180 : mword 13)) = mword_of_int (KernelSyms.wakeup + 0x30))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt30) in "Hpc".
        iDestruct (gpr_file_dom with "Hfile") as "[%Hdommret Hfile]".
        iApply ("Htail" $! mret with "[%] Hsc Hhs Hcap Hcnt Htlb Hpc Hfile [Hnoffc Hintc Hlockcells] Hframe").
        + unfold wk_loop_regs.
          split; [exact Hmrets1|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)); exact HMjcsp|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Htp | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs2 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs3 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs4 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs5 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs6 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs7 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs8 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs9 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs10 | vm_compute; discriminate]|].
          split; [rewrite (callee_saved_lookup Hpres (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity));
                  rewrite /Mj lookup_total_insert_ne; [exact Hs11 | vm_compute; discriminate]|].
          exact Hdommret.
        + rewrite /wk_res_sconf. iFrame "Hnoffc Hintc Hlockcells".
      - (* FALL: a0 <> s1: acquire proc[k], check state/chan, maybe wake, release *)
        iApply (wp_beq_fall_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x3c))
                  (mword_of_int 8180 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
                  mret av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp3 with "Hsc Hhs Hcap Htlb Hpc Hfile Hi3c [-]").
        iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
        assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x40))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp40) in "Hpc".
        (* the per-proc lock for proc[k] and its protected resource. *)
        destruct (lookup_lt_is_Some_2 γs k ltac:(rewrite Hlen; exact Hk)) as [γk Hγk].
        iDestruct (procs_inv_lookup Rreg Φ γc bsie dq γs k γk Hγk with "Hpinv") as "#Hlockk".
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hγk with "Hlockcells") as "[Hcpuk Hlockback]".
        iDestruct "Hintc" as (iv) "Hintc".
        (* sp/tp preserved through myproc. *)
        assert (Hmret2 : mret !!! Regidx (mword_of_int 2 : mword 5) = spF).
        { rewrite (callee_saved_lookup Hpres (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)). exact HMjcsp. }
        assert (Hmret4 : mret !!! Regidx (mword_of_int 4 : mword 5) = rtp).
        { rewrite (callee_saved_lookup Hpres (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Htp. }
        iPoseProof (wki_40 with "Htext") as "Hi40".
        (* 0x40 c.mv a0,s1 : a0 := &proc[k] *)
        iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x40))
                  (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                  mret av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hsc Hhs Hcap Htlb Hpc Hfile Hi40 [-]").
        iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
        set (M40 := <[Regidx (mword_of_int 10 : mword 5) :=
                      regval_into_reg (add_vec zero_reg (mret !!! Regidx (mword_of_int 9 : mword 5)))]> mret).
        assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.wakeup + 0x42))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp42) in "Hpc".
        iPoseProof (wki_42 with "Htext") as "Hi42".
        (* 0x42 jal ra,acquire *)
        iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x42))
                  (mword_of_int 1 : mword 5) (mword_of_int 2092148 : mword 21) M40 av
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity)
                  with "Hsc Hhs Hcap Htlb Hpc Hfile Hi42 [-]").
        iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
        set (M42 := <[Regidx (mword_of_int 1 : mword 5) :=
                      regval_into_reg (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64) 4)]> M40).
        assert (Hjtgt_aq : add_vec (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64)
                            (sign_extend' 64 (mword_of_int 2092148 : mword 21)) = mword_of_int KernelSyms.acquire)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjtgt_aq) in "Hpc".
        assert (HM42ra : M42 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64) 4)
          by (rewrite /M42; apply lookup_total_insert).
        assert (HM42a0 : M42 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr k).
        { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M40 lookup_total_insert. rewrite add_vec_zero_l. exact Hmrets1. }
        assert (HM42csp : M42 !!! Regidx csp_rs1 = spF).
        { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmret2. }
        assert (HM42tp : M42 !!! Regidx (mword_of_int 4 : mword 5) = rtp).
        { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmret4. }
        (* acquire(&proc[k]->lock): intr_count lvl -> S lvl; returns locked + proc_lock_res. *)
        iApply (wp_acquire_sconf γ root_ppn Φ γk (proc_lock_res Rreg Φ γc bsie dq γk (proc_addr k)) M42
                  (zero_reg : mword 64) noffv iv lvl av
                  ltac:(rewrite HM42tp; exact Hmycpu_nz)
                  ltac:(rewrite HM42ra; vm_compute; reflexivity)
                  ltac:(lia)
                  with "Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile [Hlockk] [Hcpuk] [Hnoffc] [Hintc] [-]").
        { iEval (rewrite HM42a0). iExact "Hlockk". }
        { iEval (rewrite HM42a0). iExact "Hcpuk". }
        { iEval (rewrite HM42tp). iEval (rewrite Ha0f). iExact "Hnoffc". }
        { iEval (rewrite HM42tp). iEval (rewrite Ha0f). iExact "Hintc". }
        iIntros (ms Macq) "%Hms Hhs Hsc Hcap Htlb Hpc Hfile %Hpins Htok HR Hcpu2 Hnoff2 Hint2 Hcnt".
        (* acquire returned: pc = wakeup+0x46, intr_count (S lvl). *)
        assert (Hpc46 : update_vec_dec (add_vec (M42 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                        = mword_of_int (KernelSyms.wakeup + 0x46)).
        { rewrite HM42ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hpc46) in "Hpc".
        iDestruct (proc_lock_res_elim Rreg Φ γc bsie dq γk (proc_addr k) with "HR") as (st ch) "(Hpst & Hpch & Hctx)".
        (* the acquire-returned cpu/noff/int cells: rewrite their addresses into
           the [wk_cpu_addr (proc_addr k)] / [wk_noff_addr a0f] forms release wants. *)
        iEval (rewrite HM42a0) in "Hcpu2".
        iEval (rewrite HM42tp) in "Hcpu2".
        iEval (rewrite HM42tp) in "Hnoff2". iEval (rewrite Ha0f) in "Hnoff2".
        iEval (rewrite HM42tp) in "Hint2". iEval (rewrite Ha0f) in "Hint2".
        (* register-preservation through acquire (callee_saved M42 Macq). *)
        assert (HMacq9 : Macq !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k).
        { rewrite (callee_saved_lookup Hpins (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmrets1. }
        (* =============================================================== *)
        (* shared release tail [Hrel], reached from all 3 exits (state !=   *)
        (* SLEEPING, chan mismatch, or after waking): 0x2a mv a0,s1;        *)
        (* 0x2c jal release (intr_count S lvl -> lvl); then p++ tail at 0x30.*)
        (* =============================================================== *)
        iAssert (∀ (Mr : gmap regidx (mword 64)),
                   ⌜ Mr !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k /\
                     Mr !!! Regidx (mword_of_int 2 : mword 5) = spF /\
                     Mr !!! Regidx (mword_of_int 4 : mword 5) = rtp /\
                     Mr !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC /\
                     Mr !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64) /\
                     Mr !!! Regidx (mword_of_int 20 : mword 5) = chan /\
                     Mr !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64) /\
                     Mr !!! Regidx (mword_of_int 22 : mword 5) = vs6 /\
                     Mr !!! Regidx (mword_of_int 23 : mword 5) = vs7 /\
                     Mr !!! Regidx (mword_of_int 24 : mword 5) = vs8 /\
                     Mr !!! Regidx (mword_of_int 25 : mword 5) = vs9 /\
                     Mr !!! Regidx (mword_of_int 26 : mword 5) = vs10 /\
                     Mr !!! Regidx (mword_of_int 27 : mword 5) = vs11 /\
                     (forall r : regidx, r ∈ dom Mr) ⌝ -∗
                   sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn Mr av -∗ tlb_inv_pt root_ppn -∗
                   pc_is (mword_of_int (KernelSyms.wakeup + 0x2a)) -∗ gpr_file Mr -∗
                   locked γk -∗ proc_lock_res Rreg Φ γc bsie dq γk (proc_addr k) -∗
                   WP (Loop : expr riscv_lang) {{ Φ }})%I
          with "[Hcnt Hnoff2 Hint2 Hcpu2 Hlockback Hframe Htail]"
          as "Hrel".
        { iIntros (Mr) "%Hmr Hsc Hhs Hcap Htlb Hpc Hfile Htok HR".
          destruct Hmr as (Hr9 & Hr2 & Hr4 & Hr18 & Hr19 & Hr20 & Hr21 & Hr22 & Hr23 & Hr24 & Hr25 & Hr26 & Hr27 & Hrdom).
          iPoseProof (wki_2a with "Htext") as "Hi2a".
          iPoseProof (wki_2c with "Htext") as "Hi2c".
          (* 0x2a c.mv a0,s1 : a0 := &proc[k] *)
          iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x2a))
                    (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                    Mr av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi2a [-]").
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
          set (Mr2a := <[Regidx (mword_of_int 10 : mword 5) :=
                         regval_into_reg (add_vec zero_reg (Mr !!! Regidx (mword_of_int 9 : mword 5)))]> Mr).
          assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.wakeup + 0x2c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp2c) in "Hpc".
          (* 0x2c jal ra,release *)
          iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x2c))
                    (mword_of_int 1 : mword 5) (mword_of_int 2092306 : mword 21) Mr2a av
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(vm_compute; reflexivity)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi2c [-]").
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
          set (Mr2c := <[Regidx (mword_of_int 1 : mword 5) :=
                         regval_into_reg (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64) 4)]> Mr2a).
          assert (Hjtgt_rl : add_vec (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64)
                              (sign_extend' 64 (mword_of_int 2092306 : mword 21)) = mword_of_int KernelSyms.release)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjtgt_rl) in "Hpc".
          assert (HMr2c_ra : Mr2c !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64) 4)
            by (rewrite /Mr2c; apply lookup_total_insert).
          assert (HMr2c_a0 : Mr2c !!! Regidx (mword_of_int 10 : mword 5) = proc_addr k).
          { rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
            rewrite /Mr2a lookup_total_insert. rewrite add_vec_zero_l. exact Hr9. }
          assert (HMr2c_csp : Mr2c !!! Regidx csp_rs1 = spF).
          { rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
            rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr2. }
          assert (HMr2c_tp : Mr2c !!! Regidx (mword_of_int 4 : mword 5) = rtp).
          { rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
            rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr4. }
          (* bind the noff/intena arguments to LOCAL names: passing the big
             unfolded terms straight into the [iApply] blows up unification
             (they get substituted into every derived [let] of the release spec),
             exactly as kfree passes its [po_noff_store]/[intena_old] locals. *)
          set (nacq := wk_noff_acq noffv).
          set (ivc := if eq_vec (sign_extend' 64 noffv) zero_reg then po_intena_val ms else iv).
          (* the acquire (+1) / release (-1) noff cancellation makes release's
             nv1 equal to [sign_extend' 64 noffv], so its coupling premise IS the
             loop entry coupling.  Pre-established (NOT inline in the iApply). *)
          assert (Hrel_coup : neq_vec (sign_extend' 64 (subrange_vec_dec (add_vec
                    (sign_extend' 64 nacq)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)) zero_reg = false <-> lvl = 0%nat).
          { unfold nacq. rewrite wk_release_nv1_cancel. exact Hcoupling. }
          (* PRE-ESTABLISH every release premise as a hypothesis: an inline
             [ltac:(rewrite ...)] over the opaque loop map [Mr2c] elaborates
             against the iApply's unresolved evars and blows up (kfree's inline
             ltacs are fine only because its map is concrete). *)
          assert (Hlka2 : add_vec (Mr2c !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k)
            by (rewrite HMr2c_a0; apply wk_add_vec_0).
          assert (Hmine2 : eq_vec (mycpu_ret rtp) (mycpu_ret (Mr2c !!! Regidx (mword_of_int 4 : mword 5))) = true)
            by (rewrite HMr2c_tp; apply wk_eq_vec_refl).
          assert (Hal5 : eq_vec (access_vec_dec (update_vec_dec (add_vec (Mr2c !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
            by (rewrite HMr2c_ra; vm_compute; reflexivity).
          (* release(&proc[k]->lock): intr_count S lvl -> lvl. *)
          iApply (wp_release_sconf γ root_ppn Φ γk (proc_addr k) (proc_lock_res Rreg Φ γc bsie dq γk (proc_addr k)) Mr2c
                    (mycpu_ret rtp) nacq ivc
                    lvl av (dqi:=DfracOwn 1)
                    Hlka2 Hmine2 Hrel_coup Hnf_pos Hal5 ltac:(lia)
                    with "Hsc Hhs Hcap Htlb Htext Hpc Hfile Hlockk Htok HR [Hcpu2] [Hnoff2] [Hint2] Hcnt [-]").
          { iEval (rewrite HMr2c_a0). iExact "Hcpu2". }
          { iEval (rewrite HMr2c_tp). iEval (rewrite Ha0f). iExact "Hnoff2". }
          { iEval (rewrite HMr2c_tp). iEval (rewrite Ha0f). iExact "Hint2". }
          iIntros (mr) "Hhs Hsc Hcap Htlb Hpc Hfile %Hpinsr Hcpu3 Hnoff3 Hint3 Hcnt".
          (* pc = wakeup+0x30 (release's return target). *)
          assert (Hpc30 : update_vec_dec (add_vec (Mr2c !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                          = mword_of_int (KernelSyms.wakeup + 0x30)).
          { rewrite HMr2c_ra. apply bv_eq; vm_compute; reflexivity. }
          iEval (rewrite Hpc30) in "Hpc".
          iDestruct (gpr_file_dom with "Hfile") as "[%Hdommr Hfile]".
          iEval (rewrite HMr2c_a0) in "Hcpu3".
          iEval (rewrite HMr2c_tp) in "Hnoff3". iEval (rewrite Ha0f) in "Hnoff3".
          iEval (rewrite HMr2c_tp) in "Hint3". iEval (rewrite Ha0f) in "Hint3".
          iApply ("Htail" $! mr with "[%] Hsc Hhs Hcap Hcnt Htlb Hpc Hfile [Hnoff3 Hint3 Hcpu3 Hlockback] Hframe").
          - (* wk_loop_regs mr spF rtp chan k *)
            unfold wk_loop_regs.
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr9. }
            split; [rewrite (callee_saved_lookup Hpinsr (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)); exact HMr2c_csp|].
            split; [rewrite (callee_saved_lookup Hpinsr (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)); exact HMr2c_tp|].
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr18. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr19. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr20. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr21. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr22. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr23. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr24. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr25. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr26. }
            split.
            { rewrite (callee_saved_lookup Hpinsr (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)).
              rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
              rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr27. }
            exact Hdommr.
          - (* wk_res_sconf: noff ∗ ∃intena ∗ lockcells *)
            rewrite /wk_res_sconf. iSplitL "Hnoff3".
            { iEval (rewrite <- Hnf_rt). iExact "Hnoff3". }
            iSplitR "Hcpu3 Hlockback".
            { iExists (if eq_vec (sign_extend' 64 noffv) zero_reg then po_intena_val ms else iv). iExact "Hint3". }
            iApply "Hlockback". iExact "Hcpu3". }
        (* ===== 0x46..0x56: state/chan test + conditional wake, then Hrel ===== *)
        (* Macq's callee-saved registers all equal the loop-entry values: compose
           [callee_saved] across myproc (Hpres) + the a0/ra writes + acquire
           (Hpins), then project. *)
        assert (HcsMj : callee_saved M Mj).
        { rewrite /Mj. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
        assert (HcsMret : callee_saved M mret) by (eapply callee_saved_trans; [exact HcsMj | exact Hpres]).
        assert (HcsM40 : callee_saved M M40).
        { rewrite /M40. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsMret]. }
        assert (HcsM42 : callee_saved M M42).
        { rewrite /M42. apply callee_saved_insert_r; [vm_compute; reflexivity | exact HcsM40]. }
        assert (HcsMacq : callee_saved M Macq) by (eapply callee_saved_trans; [exact HcsM42 | exact Hpins]).
        assert (HMacq2 : Macq !!! Regidx (mword_of_int 2 : mword 5) = spF)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)); exact Hsp).
        assert (HMacq4 : Macq !!! Regidx (mword_of_int 4 : mword 5) = rtp)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)); exact Htp).
        assert (HMacq18 : Macq !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs2).
        assert (HMacq19 : Macq !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64))
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs3).
        assert (HMacq20 : Macq !!! Regidx (mword_of_int 20 : mword 5) = chan)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs4).
        assert (HMacq21 : Macq !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs5).
        assert (HMacq22 : Macq !!! Regidx (mword_of_int 22 : mword 5) = vs6)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs6).
        assert (HMacq23 : Macq !!! Regidx (mword_of_int 23 : mword 5) = vs7)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs7).
        assert (HMacq24 : Macq !!! Regidx (mword_of_int 24 : mword 5) = vs8)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs8).
        assert (HMacq25 : Macq !!! Regidx (mword_of_int 25 : mword 5) = vs9)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs9).
        assert (HMacq26 : Macq !!! Regidx (mword_of_int 26 : mword 5) = vs10)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs10).
        assert (HMacq27 : Macq !!! Regidx (mword_of_int 27 : mword 5) = vs11)
          by (rewrite (callee_saved_lookup HcsMacq (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)); exact Hs11).
        iDestruct (gpr_file_dom with "Hfile") as "[%Hdomacq Hfile]".
        (* ---- 0x46 c.lw a5,24(s1) : a5 := sext(state) ---- *)
        iPoseProof (wki_46 with "Htext") as "Hi46".
        iEval (rewrite wk_cr1; rewrite wk_cr7) in "Hi46".
        assert (Hea46 : add_vec (Macq !!! Regidx (mword_of_int 9 : mword 5))
                          (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00"))))
                        = p_state (proc_addr k)).
        { rewrite HMacq9. rewrite /p_state /state_off.
          replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00"))))
             with (mword_of_int 24 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          reflexivity. }
        iApply (wp_clw_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x46))
                  (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                  (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")))
                  Macq av st ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hsc Hhs Hcap Htlb Hpc Hfile Hi46 [Hpst] [-]").
        { iEval (rewrite Hea46). iExact "Hpst". }
        iIntros "Hhs Hsc Hcap Htlb Hpc Hfile Hpst".
        iEval (rewrite Hea46) in "Hpst".
        set (M48 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 st)]> Macq).
        assert (Hpc48 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x46) : mword 64) 2
                        = mword_of_int (KernelSyms.wakeup + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc48) in "Hpc".
        assert (HM48a5 : M48 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 st)
          by (rewrite /M48 lookup_total_insert; reflexivity).
        assert (HM48_9 : M48 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq9 | vm_compute; discriminate]).
        assert (HM48_2 : M48 !!! Regidx (mword_of_int 2 : mword 5) = spF)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq2 | vm_compute; discriminate]).
        assert (HM48_4 : M48 !!! Regidx (mword_of_int 4 : mword 5) = rtp)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq4 | vm_compute; discriminate]).
        assert (HM48_18 : M48 !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq18 | vm_compute; discriminate]).
        assert (HM48_19 : M48 !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64))
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq19 | vm_compute; discriminate]).
        assert (HM48_20 : M48 !!! Regidx (mword_of_int 20 : mword 5) = chan)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq20 | vm_compute; discriminate]).
        assert (HM48_21 : M48 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq21 | vm_compute; discriminate]).
        assert (HM48_22 : M48 !!! Regidx (mword_of_int 22 : mword 5) = vs6)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq22 | vm_compute; discriminate]).
        assert (HM48_23 : M48 !!! Regidx (mword_of_int 23 : mword 5) = vs7)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq23 | vm_compute; discriminate]).
        assert (HM48_24 : M48 !!! Regidx (mword_of_int 24 : mword 5) = vs8)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq24 | vm_compute; discriminate]).
        assert (HM48_25 : M48 !!! Regidx (mword_of_int 25 : mword 5) = vs9)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq25 | vm_compute; discriminate]).
        assert (HM48_26 : M48 !!! Regidx (mword_of_int 26 : mword 5) = vs10)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq26 | vm_compute; discriminate]).
        assert (HM48_27 : M48 !!! Regidx (mword_of_int 27 : mword 5) = vs11)
          by (rewrite /M48 lookup_total_insert_ne; [exact HMacq27 | vm_compute; discriminate]).
        assert (HdomM48 : forall r : regidx, r ∈ dom M48).
        { intro r. rewrite /M48 dom_insert_L. apply elem_of_union_r. apply Hdomacq. }
        (* ---- 0x48 bne a5,s3 : if state != SLEEPING -> release ---- *)
        iPoseProof (wki_48 with "Htext") as "Hi48".
        destruct (neq_vec (M48 !!! Regidx (mword_of_int 15 : mword 5))
                          (M48 !!! Regidx (mword_of_int 19 : mword 5))) eqn:Hcmp48.
        + (* TAKEN: state != SLEEPING -> reassemble proc_lock_res, release *)
          iApply (wp_bne_taken_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x48))
                    (mword_of_int 8162 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
                    M48 av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp48 ltac:(vm_compute; reflexivity)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi48 [-]").
          iNext. iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
          assert (H48tgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64)
                            (sign_extend' 64 (mword_of_int 8162 : mword 13))
                          = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite H48tgt) in "Hpc".
          iDestruct (proc_lock_res_intro Rreg Φ γc bsie dq γk (proc_addr k) st ch with "Hpst Hpch Hctx") as "HR".
          iApply ("Hrel" $! M48 with "[%] Hsc Hhs Hcap Htlb Hpc Hfile Htok HR").
          repeat split; [exact HM48_9 | exact HM48_2 | exact HM48_4 | exact HM48_18
                        | exact HM48_19 | exact HM48_20 | exact HM48_21
                        | exact HM48_22 | exact HM48_23 | exact HM48_24
                        | exact HM48_25 | exact HM48_26 | exact HM48_27 | exact HdomM48].
        + (* FALL: state == SLEEPING -> load chan *)
          iApply (wp_bne_fall_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x48))
                    (mword_of_int 8162 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
                    M48 av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp48 with "Hsc Hhs Hcap Htlb Hpc Hfile Hi48 [-]").
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
          assert (Heq2 : sign_extend' 64 st = (mword_of_int 2 : mword 64)).
          { rewrite HM48a5 HM48_19 in Hcmp48. unfold neq_vec in Hcmp48.
            rewrite negb_false_iff in Hcmp48. apply eq_vec_true_iff in Hcmp48. exact Hcmp48. }
          pose proof (wk_sext_sleeping st Heq2) as Hst_sl.
          assert (Hpc4c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64) 4
                          = mword_of_int (KernelSyms.wakeup + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc4c) in "Hpc".
          (* ---- 0x4c c.ld a5,32(s1) : a5 := p->chan ---- *)
          iPoseProof (wki_4c with "Htext") as "Hi4c".
          iEval (rewrite wk_cr1; rewrite wk_cr7) in "Hi4c".
          assert (Hea4c : add_vec (M48 !!! Regidx (mword_of_int 9 : mword 5))
                            (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))) = p_chan (proc_addr k)).
          { rewrite HM48_9. rewrite /p_chan /chan_off.
            replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))) with (mword_of_int 32 : mword 64)
              by (apply bv_eq; vm_compute; reflexivity).
            reflexivity. }
          iApply (wp_cld_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x4c))
                    (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))
                    M48 av ch ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    with "Hsc Hhs Hcap Htlb Hpc Hfile Hi4c [Hpch] [-]").
          { iEval (rewrite Hea4c). iExact "Hpch". }
          iIntros "Hhs Hsc Hcap Htlb Hpc Hfile Hpch".
          iEval (rewrite Hea4c) in "Hpch".
          set (M4e := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ch]> M48).
          assert (Hpc4e : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x4c) : mword 64) 2
                          = mword_of_int (KernelSyms.wakeup + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc4e) in "Hpc".
          assert (HM4e_a5 : M4e !!! Regidx (mword_of_int 15 : mword 5) = ch)
            by (rewrite /M4e lookup_total_insert; reflexivity).
          assert (HM4e_9 : M4e !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_9 | vm_compute; discriminate]).
          assert (HM4e_2 : M4e !!! Regidx (mword_of_int 2 : mword 5) = spF)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_2 | vm_compute; discriminate]).
          assert (HM4e_4 : M4e !!! Regidx (mword_of_int 4 : mword 5) = rtp)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_4 | vm_compute; discriminate]).
          assert (HM4e_18 : M4e !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_18 | vm_compute; discriminate]).
          assert (HM4e_19 : M4e !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64))
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_19 | vm_compute; discriminate]).
          assert (HM4e_20 : M4e !!! Regidx (mword_of_int 20 : mword 5) = chan)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_20 | vm_compute; discriminate]).
          assert (HM4e_21 : M4e !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_21 | vm_compute; discriminate]).
          assert (HM4e_22 : M4e !!! Regidx (mword_of_int 22 : mword 5) = vs6)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_22 | vm_compute; discriminate]).
          assert (HM4e_23 : M4e !!! Regidx (mword_of_int 23 : mword 5) = vs7)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_23 | vm_compute; discriminate]).
          assert (HM4e_24 : M4e !!! Regidx (mword_of_int 24 : mword 5) = vs8)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_24 | vm_compute; discriminate]).
          assert (HM4e_25 : M4e !!! Regidx (mword_of_int 25 : mword 5) = vs9)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_25 | vm_compute; discriminate]).
          assert (HM4e_26 : M4e !!! Regidx (mword_of_int 26 : mword 5) = vs10)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_26 | vm_compute; discriminate]).
          assert (HM4e_27 : M4e !!! Regidx (mword_of_int 27 : mword 5) = vs11)
            by (rewrite /M4e lookup_total_insert_ne; [exact HM48_27 | vm_compute; discriminate]).
          assert (HdomM4e : forall r : regidx, r ∈ dom M4e).
          { intro r. rewrite /M4e dom_insert_L. apply elem_of_union_r. apply HdomM48. }
          (* ---- 0x4e bne a5,s4 : if chan != arg -> release ---- *)
          iPoseProof (wki_4e with "Htext") as "Hi4e".
          destruct (neq_vec (M4e !!! Regidx (mword_of_int 15 : mword 5))
                            (M4e !!! Regidx (mword_of_int 20 : mword 5))) eqn:Hcmp4e.
          * (* TAKEN: chan mismatch -> release *)
            iApply (wp_bne_taken_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x4e))
                      (mword_of_int 8156 : mword 13) (mword_of_int 20 : mword 5) (mword_of_int 15 : mword 5)
                      M4e av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                      Hcmp4e ltac:(vm_compute; reflexivity)
                      with "Hsc Hhs Hcap Htlb Hpc Hfile Hi4e [-]").
            iNext. iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
            assert (H4etgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64)
                              (sign_extend' 64 (mword_of_int 8156 : mword 13))
                            = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite H4etgt) in "Hpc".
            iDestruct (proc_lock_res_intro Rreg Φ γc bsie dq γk (proc_addr k) st ch with "Hpst Hpch Hctx") as "HR".
            iApply ("Hrel" $! M4e with "[%] Hsc Hhs Hcap Htlb Hpc Hfile Htok HR").
            repeat split; [exact HM4e_9 | exact HM4e_2 | exact HM4e_4 | exact HM4e_18
                          | exact HM4e_19 | exact HM4e_20 | exact HM4e_21
                          | exact HM4e_22 | exact HM4e_23 | exact HM4e_24
                          | exact HM4e_25 | exact HM4e_26 | exact HM4e_27 | exact HdomM4e].
          * (* FALL: chan matches -> wake (state := RUNNABLE) *)
            iApply (wp_bne_fall_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x4e))
                      (mword_of_int 8156 : mword 13) (mword_of_int 20 : mword 5) (mword_of_int 15 : mword 5)
                      M4e av ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                      Hcmp4e with "Hsc Hhs Hcap Htlb Hpc Hfile Hi4e [-]").
            iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
            assert (Hpc52 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64) 4
                            = mword_of_int (KernelSyms.wakeup + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpc52) in "Hpc".
            (* ---- 0x52 sw s5,24(s1) : p->state := RUNNABLE ---- *)
            iPoseProof (wki_52 with "Htext") as "Hi52".
            assert (Hea52 : add_vec (M4e !!! Regidx (mword_of_int 9 : mword 5))
                              (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state (proc_addr k)).
            { rewrite HM4e_9. rewrite /p_state /state_off.
              replace (sign_extend' 64 (mword_of_int 24 : mword 12)) with (mword_of_int 24 : mword 64)
                by (apply bv_eq; vm_compute; reflexivity).
              reflexivity. }
            iApply (wp_sw_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x52))
                      (mword_of_int 21 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 24 : mword 12)
                      M4e av st with "Hsc Hhs Hcap Htlb Hpc Hfile Hi52 [Hpst] [-]").
            { iEval (rewrite Hea52). iExact "Hpst". }
            iIntros "Hhs Hsc Hcap Htlb Hpc Hfile Hpst".
            assert (Hstored : trunc32 (M4e !!! Regidx (mword_of_int 21 : mword 5)) = RUNNABLE).
            { rewrite HM4e_21. rewrite /RUNNABLE. apply bv_eq; vm_compute; reflexivity. }
            iEval (rewrite Hstored) in "Hpst". iEval (rewrite Hea52) in "Hpst".
            assert (Hpc56 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x52) : mword 64) 4
                            = mword_of_int (KernelSyms.wakeup + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
            iEval (rewrite Hpc56) in "Hpc".
            (* reassemble proc_lock_res via the wakeup transition. *)
            assert (Hnc : (if needs_ctx st then proc_ctx Rreg Φ γc bsie dq γk (proc_addr k) else emp)%I
                          = proc_ctx Rreg Φ γc bsie dq γk (proc_addr k))
              by (rewrite Hst_sl needs_ctx_SLEEPING; reflexivity).
            iEval (rewrite Hnc) in "Hctx".
            iDestruct (proc_lock_res_wakeup Rreg Φ γc bsie dq γk (proc_addr k) ch with "Hpst Hpch Hctx") as "HR".
            (* ---- 0x56 c.j release ---- *)
            iPoseProof (wki_56 with "Htext") as "Hi56".
            assert (H56tgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x56) : mword 64)
                              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0"))))
                            = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
            iApply (wp_cj_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.wakeup + 0x56))
                      (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")))
                      M4e av ltac:(rewrite H56tgt; vm_compute; reflexivity)
                      with "Hsc Hhs Hcap Htlb Hpc Hfile Hi56 [-]").
            iNext. iIntros "Hhs Hsc Hcap Htlb Hpc Hfile".
            iEval (rewrite H56tgt) in "Hpc".
            iApply ("Hrel" $! M4e with "[%] Hsc Hhs Hcap Htlb Hpc Hfile Htok HR").
            repeat split; [exact HM4e_9 | exact HM4e_2 | exact HM4e_4 | exact HM4e_18
                          | exact HM4e_19 | exact HM4e_20 | exact HM4e_21
                          | exact HM4e_22 | exact HM4e_23 | exact HM4e_24
                          | exact HM4e_25 | exact HM4e_26 | exact HM4e_27 | exact HdomM4e].
    }
    iIntros (k M) "%Hk %Hregs Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile Hres Hframe".
    iApply ("Hloop" $! (NPROC - k)%nat k M with "[%] [%] [%] Hqexit Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile Hres Hframe");
      [lia | exact Hk | exact Hregs].
  Qed.

  (* ===================================================================== *)
  (* Whole-function WP for wakeup(chan) over sconf: prologue -> loop        *)
  (* (k=0, exiting to the epilogue) -> return.  Mirrors the smode wp_wakeup  *)
  (* (WpWakeup.v).  The caller supplies deep-K custody (K>=18, so deep-10    *)
  (* remains for the loop after the prologue's 8-slot frame carve), the      *)
  (* per-cpu push_off scratch (noff + EXISTENTIAL intena + lock words), and  *)
  (* procs_inv; the arithmetic side conditions (mycpu non-null, noff round-  *)
  (* trip, and the noff<->intr_count coupling) are the caller's obligations. *)
  (* proc_lock_res is threaded opaquely (Rreg/gc/bsie/dq), as in the loop.   *)
  (* ===================================================================== *)
  Lemma wp_wakeup_sconf
      (γ : gname) (root_ppn : mword 44)
      (Rreg : s_regime) (γc : gname) (bsie : mword 1) (dq : dfrac)
      (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (γs : list gname) (a0f : mword 64)
      (noffv : mword 32) (lvl K : nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spF := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    let rettgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (18 <= K)%nat ->
    (forall r : regidx, r ∈ dom m) ->
    length γs = NPROC ->
    mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0f ->
    eq_vec (zero_reg : mword 64) (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 (wk_noff_acq noffv)) = false ->
    wk_noff_rel (wk_noff_acq noffv) = noffv ->
    (neq_vec (sign_extend' 64 noffv) zero_reg = false <-> lvl = 0%nat) ->
    eq_vec (access_vec_dec rettgt 0) ('b"0") = true ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn m K -∗
    intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.wakeup) -∗ gpr_file m -∗
    wk_noff_addr a0f ↦₄ noffv -∗ (∃ iv : mword 32, wk_intena_addr a0f ↦₄ iv) -∗
    wk_lockcells γs -∗ procs_inv Rreg Φ γc bsie dq γs -∗
    ( ∀ Mf : gmap regidx (mword 64),
        ⌜ callee_saved m Mf /\ (forall r : regidx, r ∈ dom Mf) ⌝ -∗
        sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap γ root_ppn Mf K -∗
        intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
        kernel_text -∗ pc_is rettgt -∗ gpr_file Mf -∗
        wk_noff_addr a0f ↦₄ noffv -∗ (∃ iv : mword 32, wk_intena_addr a0f ↦₄ iv) -∗
        wk_lockcells γs -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spF rettgt HK Hdom Hlen Hmycpu Hmycpu_nz Hnf_pos Hnf_rt Hcoupling Halign.
    iIntros "Hsc Hhs Hcap Hcnt Htlb #Htext Hpc Hfile Hnoffc Hintc Hlockcells #Hpinv Hcont".
    (* ---- prologue: save frame (carve 8 from the cap's avail), set up loop regs ---- *)
    iApply (wp_wakeup_prologue_sconf γ root_ppn Φ m K ltac:(lia) Hdom
              with "Hsc Hhs Hcap Htlb Htext Hpc Hfile [-]").
    iIntros (M vpad) "%Hpro Hsc Hhs Hcap Htlb Hpc Hfile Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1 Hf0".
    destruct Hpro as (HM9 & HM18 & HM19 & HM21 & HM20 & HMcsp & HM1 & HM4 & HM22 & HM23 & HM24 & HM25 & HM26 & HM27 & HMdom).
    (* ---- the loop, with the epilogue as its exit continuation ---- *)
    iPoseProof (wp_wakeup_loop_sconf γ root_ppn Rreg γc bsie dq Φ γs spF a0f
                  (m !!! Regidx (mword_of_int 4 : mword 5)) (m !!! Regidx (mword_of_int 10 : mword 5)) noffv
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                  (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                  (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                  (m !!! Regidx (mword_of_int 21 : mword 5))
                  (m !!! Regidx (mword_of_int 22 : mword 5)) (m !!! Regidx (mword_of_int 23 : mword 5))
                  (m !!! Regidx (mword_of_int 24 : mword 5)) (m !!! Regidx (mword_of_int 25 : mword 5))
                  (m !!! Regidx (mword_of_int 26 : mword 5)) (m !!! Regidx (mword_of_int 27 : mword 5)) lvl
                  (K - 8)%nat
                  Hlen Hmycpu Hmycpu_nz Hnf_pos Hnf_rt Hcoupling ltac:(lia)
                  with "Hpinv") as "Hloop".
    iSpecialize ("Hloop" with "[Hf0 Hcont]").
    { (* exit continuation = epilogue at wakeup+0x58 *)
      iIntros (Mexit) "(%Hecsp & %He4 & %He22 & %He23 & %He24 & %He25 & %He26 & %He27 & %Hedom)
                       Hsc Hhs Hcap Hcnt Htlb Htextx Hpc Hfile Hres Hframe".
      iDestruct "Hres" as "(Hnoffc & Hintc & Hlockcells)".
      iDestruct "Hframe" as "(Hf7 & Hf6 & Hf5 & Hf4 & Hf3 & Hf2 & Hf1)".
      iApply (wp_wakeup_epilogue_sconf γ root_ppn Φ Mexit K
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                (m !!! Regidx (mword_of_int 21 : mword 5)) vpad
                ltac:(lia) Hedom Halign
                with "Hsc Hhs Hcap Htlb Htextx Hpc Hfile [Hf7] [Hf6] [Hf5] [Hf4] [Hf3] [Hf2] [Hf1] [Hf0] [-]").
      { iEval (rewrite Hecsp). iExact "Hf7". }
      { iEval (rewrite Hecsp). iExact "Hf6". }
      { iEval (rewrite Hecsp). iExact "Hf5". }
      { iEval (rewrite Hecsp). iExact "Hf4". }
      { iEval (rewrite Hecsp). iExact "Hf3". }
      { iEval (rewrite Hecsp). iExact "Hf2". }
      { iEval (rewrite Hecsp). iExact "Hf1". }
      { iEval (rewrite Hecsp). iExact "Hf0". }
      iIntros (Mf) "%Hepi Hsc Hhs Hcap Htlb Hpc Hfile".
      destruct Hepi as (Hf1v & Hf0v & Hf9v & Hf18v & Hf19v & Hf20v & Hf21v & Hfcsp & Hf4v & Hf22v & Hf23v & Hf24v & Hf25v & Hf26v & Hf27v & Hfdom).
      (* the epilogue's restored sp equals the caller's sp0 (the -64/+60+4 cancel) *)
      assert (Hspcancel : add_vec (Mexit !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0)
        by (rewrite Hecsp; subst spF sp0; apply wakeup_sp_cancel).
      iApply ("Hcont" $! Mf with "[%] Hsc Hhs Hcap Hcnt Htlb Htext [Hpc] Hfile Hnoffc Hintc Hlockcells").
      - (* callee_saved m Mf /\ dom Mf *)
        split; [| exact Hfdom].
        unfold callee_saved.
        rewrite Hfcsp Hf4v Hf0v Hf9v Hf18v Hf19v Hf20v Hf21v Hf22v Hf23v Hf24v Hf25v Hf26v Hf27v.
        rewrite He4 He22 He23 He24 He25 He26 He27.
        repeat split; try reflexivity. exact Hspcancel.
      - (* pc_is rettgt : the epilogue's rettgt matches the caller's *)
        iExact "Hpc". }
    (* discharge the loop at k=0 with the prologue's loop-head map M *)
    iApply ("Hloop" $! 0%nat M with "[%] [%] Hsc Hhs Hcap Hcnt Htlb Htext Hpc Hfile [Hnoffc Hintc Hlockcells] [Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1]").
    - unfold NPROC. lia.
    - unfold wk_loop_regs.
      split; [exact HM9|]. split; [exact HMcsp|]. split; [exact HM4|].
      split; [exact HM18|]. split; [exact HM19|]. split; [exact HM20|].
      split; [exact HM21|]. split; [exact HM22|]. split; [exact HM23|].
      split; [exact HM24|]. split; [exact HM25|]. split; [exact HM26|].
      split; [exact HM27|]. exact HMdom.
    - rewrite /wk_res_sconf. iFrame "Hnoffc Hintc Hlockcells".
    - rewrite /wk_frame. iFrame "Hf7 Hf6 Hf5 Hf4 Hf3 Hf2 Hf1".
  Qed.

End WpSconfWakeupLoop.
