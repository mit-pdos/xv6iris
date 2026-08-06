(** * WeakBranch.v — the branch leaves and the REAL-SHAPE acquire loop
      (M4-prep item (iii))

    WHAT WAS MISSING.  [WeakAcquire]'s spin loop ([wwp_spin_loop] /
    [wwp_acquire_loop]) abstracts its RETRY EDGE: xv6's acquire is

        1:  amoswap.w.aq  a5, a4, (s1)
            bnez          a5, 1b

    and only the first of those two instructions had a weak leaf, so the
    branch back was a premise of the loop lemma rather than a proof.  This
    file supplies the missing leaf and closes the loop over the real shape.

    WHY A BRANCH IS NOT [wQ_none].  A branch performs no memory access of its
    own, but its certificate cannot be [WeakInstr.wQ_none]: a leaf has to give
    the state interpretation back at the successor, and [wmstate_interp σ']'s
    [wlat_interp] conjunct says every latest-write ELEMENT is still the latest
    write — which is unprovable if the step might have appended a message.
    [wstep_post]'s [∃ l, log' = log ++ l] is not enough.  So the branch's [Q]
    is [WeakEff.wQ_pure]: the image and the LOG are unchanged and the views
    only grew.  That is the cheapest [Q] that is actually usable, and it is
    still free — [WeakEff.wcert_nowrite] proves it for any WRITE-FREE effect
    trace, and a branch's trace is the fetch read and nothing else.

    §1 the leaf ([wwp_branch_step]) and its certificate-discharged form;
    §2 the composed real-shape acquire loop ([wwp_acquire_loop_real]) — one
       [amoswap.w.aq] at [pca] and one branch at [pcb], with the loop's
       retry edge a PROOF rather than a premise.
*)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var invariants.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode monpred.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakExec.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakFence.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import WeakStore.
Require Import WeakCert.
Require Import WeakEff.
Require Import WeakLock.
Require Import WeakAcquire.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WpLock.

Local Open Scope Z_scope.

(** A branch's whole effect trace is the fetch read. *)
Lemma nowrite_trace_read (ak : akinfo) (pa : Arch.pa) (n : N) :
  nowrite_trace [WEread ak pa n].
Proof. constructor; [exact I|constructor]. Qed.

Section branch.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types R : vProp Σ.
  Implicit Types Φ : mval → iProp Σ.

(* ====================================================================== *)
(** ** 1. THE LEAF

    Identical to [WeakAcquire.wwp_fence_step] except for the [Q]: a branch,
    a jump, or an ALU instruction has no weak-memory effect of its own, so
    what its certificate carries is only "nothing moved that the state
    interpretation depends on". *)

  (** Generic in [Q]: this is [WeakAcquire.wwp_fence_step] with the effect
      predicate abstracted, so ONE rule serves the branch ([wQ_pure] — or
      [wQ_quiet], when the trace's write-freedom is only known up to
      [WeakEff]'s zero-width residue), the jump, and any ALU instruction. *)
  Definition wbr_cb Φ (pc : SailStdpp.Values.mword 64)
      (P : wmstate → Prop) (Q : wmstate → wmstate → Prop) : iProp Σ :=
    (∀ σ : wmstate, wmstate_interp σ ={⊤,∅}=∗
       ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
       ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
       ⌜P σ⌝ ∗
       ∃ t0 t1 : mstate,
         ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
         ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
         ▷ (∀ (tick : bool) (σ' : wmstate),
              ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
              ⌜Q σ σ'⌝
              ={∅,⊤}=∗ wmstate_interp σ' ∗
                       WP (Loop : expr weak_riscv_lang) {{ Φ }}))%I.

  Lemma wwp_branch_step Φ (pc : SailStdpp.Values.mword 64)
      (P : wmstate → Prop) (Q : wmstate → wmstate → Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    wstep_cert (fin_to_nat cpu_id) pc P Q →
    wbr_cb Φ pc P Q -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hgid Haccpc Hcert) "Hk". rewrite /wbr_cb.
    iApply (wp_winstr Φ pc P Q Hgid Haccpc Hcert).
    iIntros (σ) "Hσ". iMod ("Hk" $! σ with "Hσ") as "(%Hpc & %Ht & %HP & Hc)".
    iDestruct "Hc" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iExists t0, t1.
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQ".
    iApply ("Hcont" $! tick σ' with "[%] [%]"); [exact Hpost|exact HQ].
  Qed.

  (** The latest-write authority crosses a [wQ_pure] step untouched — the
      whole reason [wQ_pure] is stated the way it is.  A branch leaf's "give
      the interpretation back" obligation is this lemma plus the caller's own
      register tower. *)
  Lemma wlat_interp_wQ_pure (σ σ' : wmstate) :
    wQ_pure σ σ' →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_interp (wm_img σ') (wm_log σ').
  Proof.
    iIntros ((Hi & Hl & _)) "H". by rewrite Hi Hl.
  Qed.

  (** ... and the certificate, DISCHARGED.  A branch's effect trace is the
      FETCH READ and nothing else, and [WeakEff.wcert_nowrite] asks only that
      the trace contain no write — so the caller is left with the [exec_eff]
      fact inside its own σ-callback and nothing more, exactly as for the
      three sync instructions of [WeakAcquire] §9. *)
  Corollary wwp_branch_step_cert Φ (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    wbr_cb Φ pc (wP_eff (Some (fin_to_nat cpu_id)) [WEread akf pf nf]) wQ_pure -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Haccpc. iIntros "Hk".
    iApply (wwp_branch_step Φ pc _ _ Hgid Haccpc
              (wcert_nowrite (fin_to_nat cpu_id) pc [WEread akf pf nf]
                 (nowrite_trace_read akf pf nf)) with "Hk").
  Qed.

  (** The same at the QUIET altitude: when the trace's write-freedom is only
      known up to [WeakEff]'s zero-width residue (which is what the
      empty-memory detector gives for an opaque memory-free sub-run), the
      effect predicate is [WeakEff.wQ_quiet] and the state interpretation is
      re-established through [WeakEff.wlat_interp_wQ_quiet] instead. *)
  Corollary wwp_branch_step_quiet Φ (pc : SailStdpp.Values.mword 64)
      (es : list weff) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    quiet_trace es →
    wbr_cb Φ pc (wP_eff (Some (fin_to_nat cpu_id)) es) wQ_quiet -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Haccpc Hq. iIntros "Hk".
    iApply (wwp_branch_step Φ pc _ _ Hgid Haccpc
              (wcert_quiet (fin_to_nat cpu_id) pc es Hq) with "Hk").
  Qed.

(* ====================================================================== *)
(** ** 2. THE REAL-SHAPE ACQUIRE LOOP

        1:  amoswap.w.aq  a5, a4, (s1)     -- at [pca]
            bnez          a5, 1b           -- at [pcb]

    Two premises, both persistent, both exactly one instruction:

      - THE ATTEMPT: from the loop head's resources [K], one
        [WeakAcquire.wacq_cb] at [pca].  Its SUCCESS arm receives the payload
        and the holder token (and is the caller's to finish); its FAILURE arm
        must hand back [Kb] — the loop head's resources one instruction later,
        i.e. with [pc_is pcb] and [a5 ≠ 0].
      - THE RETRY EDGE: from [Kb], one branch step at [pcb], which returns to
        the loop head's [K].  THIS is the premise that used to be an
        abstraction.

    The Löb induction is [WeakAcquire.wwp_spin_loop]'s, unchanged: the [▷] it
    hands the body is the one the AMO's own [wp_winstr] provides, and it is
    stripped inside the AMO's continuation — which is where the branch runs,
    so the branch's own [▷] is never needed for the induction.  That is why
    adding the second instruction does not change the loop's shape. *)

  Lemma wwp_acquire_loop_real Φ (γ : gname) (lk : Arch.pa) R
      (pca pcb : SailStdpp.Values.mword 64)
      (Pa Pb : wmstate → Prop) (Qb : wmstate → wmstate → Prop)
      (K Kb : iProp Σ) :
    gen_id = 0%nat →
    acc_wf pca 4 →
    acc_wf pcb 4 →
    acc_wf lk 4 →
    wstep_cert (fin_to_nat cpu_id) pca Pa
      (wQ_amo_aq (Some (fin_to_nat cpu_id)) lk lock_one) →
    wstep_cert (fin_to_nat cpu_id) pcb Pb Qb →
    inv wlockN (wlock_inv γ lk R) -∗
    □ (K -∗ ▷ (Kb -∗ WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
         wacq_cb Φ γ lk R pca Pa) -∗
    □ (Kb -∗ (K -∗ WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
         wbr_cb Φ pcb Pb Qb) -∗
    K -∗ WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hgid Hacca Haccb Hacclk Hcerta Hcertb) "#Hinv #Hatt #Hbr HK".
    iApply (wwp_spin_loop Φ K with "[] HK").
    iModIntro. iIntros "HK Hrec".
    iApply (wwp_acquire_swap Φ γ lk R pca Pa Hgid Hacca Hacclk Hcerta
              with "Hinv").
    iApply ("Hatt" with "HK [Hrec]").
    (* the retry edge, under the AMO's own later: from [Kb], the branch step
       returns to the loop head, where the (now stripped) induction
       hypothesis closes it *)
    iNext. iIntros "HKb".
    iApply (wwp_branch_step Φ pcb Pb Qb Hgid Haccb Hcertb).
    iApply ("Hbr" with "HKb Hrec").
  Qed.

  (** ... and the same with BOTH certificates discharged: what remains, per
      instruction, is the [exec_eff] fact in the caller's own σ-callback. *)
  Corollary wwp_acquire_loop_real_cert Φ (γ : gname) (lk : Arch.pa) R
      (pca pcb : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (aka akw : akinfo)
      (akf2 : akinfo) (pf2 : Arch.pa) (nf2 : N)
      (K Kb : iProp Σ) :
    gen_id = 0%nat →
    acc_wf pca 4 →
    acc_wf pcb 4 →
    acc_wf lk 4 →
    ak_coh aka = false →
    ak_sync aka = true →
    inv wlockN (wlock_inv γ lk R) -∗
    □ (K -∗ ▷ (Kb -∗ WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
         wacq_cb Φ γ lk R pca
           (wP_eff (Some (fin_to_nat cpu_id))
              [WEread akf pf nf; WEread aka lk 4; WEwrite akw lk 4 lock_one])) -∗
    □ (Kb -∗ (K -∗ WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
         wbr_cb Φ pcb
           (wP_eff (Some (fin_to_nat cpu_id)) [WEread akf2 pf2 nf2]) wQ_pure) -∗
    K -∗ WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hacca Haccb Hacclk Hcoh Hsync. iIntros "#Hinv #Hatt #Hbr HK".
    iApply (wwp_acquire_loop_real Φ γ lk R pca pcb _ _ _ K Kb
              Hgid Hacca Haccb Hacclk
              (wcert_amo_aq (fin_to_nat cpu_id) pca akf pf nf aka akw lk lock_one
                 Hcoh Hsync)
              (wcert_nowrite (fin_to_nat cpu_id) pcb [WEread akf2 pf2 nf2]
                 (nowrite_trace_read akf2 pf2 nf2))
              with "Hinv Hatt Hbr HK").
  Qed.

End branch.
