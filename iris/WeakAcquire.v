(** * WeakAcquire.v — the lock and the escrow AT THE WP ALTITUDE (M3c item 3)

    M3b landed the two lock cores ([WeakLock.wacquire_core] / [wrelease_core])
    and the escrow's writer ([WeakStarted.wstarted_set]) at the σ/σ' altitude —
    "given that the step appended THIS message and gained THAT view, the
    invariant moves like this".  This file composes them THROUGH
    [WeakInstr.wp_winstr], i.e. over a real instruction certificate, so that
    what comes out is a weakest-precondition rule: one [amoswap.w.aq] = one
    acquire attempt, one [sw] = one release, and a spin loop over the former.

    ================== THE THREE THINGS THAT MADE THIS WORK ==================

    (1) THE LATEST-WRITE AUTHORITY IS WHAT A RACY LEAF BORROWS.
        [WeakGhost.wmstate_interp σ] is seven conjuncts, and exactly ONE of
        them — [wlat_interp (wm_img σ) (wm_log σ)] — is what a step that
        writes a shared byte has to update.  §1 splits it off as
        [wmstate_rest]: the leaf's own caller keeps registers, devices, the
        log auth and this hart's [wstate] cell (all of which it updates with
        the SC tower it already has), while the LOCK keeps the latest-write
        authority across the step and hands it back retargeted.  Every racy
        leaf in the M4 sweep has this shape.

    (2) THE INVARIANT IS OPEN ACROSS THE STEP, AND THE MASKS ARE THE LEAF'S
        OWN.  [wp_winstr]'s callback is [⊤ ={⊤,∅}=∗ … ▷ (… ={∅,⊤}=∗ …)], so
        the lock invariant is opened at ⊤ (leaving ⊤∖↑wlockN for the caller's
        own fupd), held across the [▷], and closed on the way back — the
        ordinary atomic-step discipline.  What the CALLER sees is therefore
        the same callback with ⊤ replaced by ⊤∖↑wlockN, and nothing else.

    (3) THE VALUE THE SWAP RETURNS IS READ OUT BEFORE THE STEP, FROM THE
        ELEMENTS.  [WeakLock.wlat4_flat_gen] turns the invariant's element
        bundle into the flat lock word with no view hypothesis (the AMO's read
        half is [ak_latest]), so the caller's [exec] fact — which is a
        statement about [WeakBridge.wflat_st σ] — can be supplied at a KNOWN
        lock word, and the post-step branch on "did I get it" is the same [v].

    §3–§8 take the instruction certificate as a PREMISE (the way an SC leaf
    takes an [instr] fact); §9 discharges it with [WeakCert]'s trace-indexed
    certificates, so the composed acquire / release / setter rest on nothing
    per-instruction but ONE [exec_eff] fact inside the caller's own callback.

    ==================== WHAT IS ABSTRACT, AND WHY ====================

    The BRANCH instructions of the spin loop have no weak leaf yet (the M4
    sweep's job), so the loop is stated over an abstract RETRY EDGE: §4's
    [wwp_spin_loop] is the generic Löb rule "a body that either finishes or
    comes back under a [▷] runs forever", and the acquire loop is that rule
    with the body = one [wwp_acquire_swap] followed by the caller's retry
    edge.  Nothing about the lock is abstracted; the loop's shape is. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac excl.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
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
Require Import WeakLock.
Require Import WeakStarted.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WpLock.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The state interpretation, minus the latest-write authority

    What a racy leaf borrows for the duration of one step.  The split is
    definitional (a reassociation of [wmstate_interp]'s seven conjuncts), so
    both directions are [iFrame]. *)

Section rest.
  Context `{!riscvGS Σ, !weakGS Σ} `{CID : CpuId}.

  Definition wmstate_rest (σ : wmstate) : iProp Σ :=
    (⌜ws_bounded σ.(wm_ws) (length σ.(wm_log))⌝ ∗
     ⌜wlog_wf σ.(wm_log)⌝ ∗
     reg_interp σ.(wm_regs) ∗
     dev_interp σ.(wm_dev) ∗
     wlog_auth σ.(wm_log) ∗
     wws_auth cpu_id σ.(wm_ws))%I.

  Lemma wmstate_interp_split σ :
    wmstate_interp σ ⊣⊢ wlat_interp (wm_img σ) (wm_log σ) ∗ wmstate_rest σ.
  Proof.
    rewrite /wmstate_interp /wmstate_rest. iSplit.
    - iIntros "(%Hb & %Hw & Hr & Hd & Hl & Hlat & Hws)". iFrame "Hlat".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
    - iIntros "(Hlat & %Hb & %Hw & Hr & Hd & Hl & Hws)".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  Lemma wmstate_rest_facts σ :
    wmstate_rest σ -∗
    ⌜ws_bounded σ.(wm_ws) (length σ.(wm_log)) ∧ wlog_wf σ.(wm_log)⌝.
  Proof. iIntros "(% & % & _)". by iPureIntro. Qed.

End rest.

(* ====================================================================== *)
(** ** 2. Byte-wise identification of two readings of the same word

    Both the pre-step read of the lock word (out of the invariant's elements)
    and [WeakLock.wacquire_core]'s own read produce "the flat memory holds
    THIS word here"; the two words are therefore equal.  Stated once, because
    the release and the escrow need it too. *)

Lemma wflat_word_agree (σ : wmstate) (a : Arch.pa) (v v' : bv 32) :
  (∀ j : nat, (j < 4)%nat →
     wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte v j)) →
  (∀ j : nat, (j < 4)%nat →
     wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte v' j)) →
  v = v'.
Proof.
  intros H1 H2. apply (bv_eq_of_bytes (n := 4%N)). intros j Hj.
  assert (Hj4 : (j < 4)%nat) by lia.
  pose proof (eq_trans (eq_sym (H1 j Hj4)) (H2 j Hj4)) as E1.
  exact (Some_inj _ _ E1).
Qed.

Section wp_lock.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types R : vProp Σ.

(* ====================================================================== *)
(** ** 3. THE ACQUIRE ATTEMPT — one [amoswap.w.aq] through the invariant

    Read the statement as [wp_winstr] with three changes, and nothing else:

      - the caller's callback runs at ⊤∖↑wlockN (the lock invariant is open);
      - it is handed the LOCK WORD [v] the swap will return, together with the
        flat-memory fact its own [exec] lemma needs about that word, and the
        latest-write authority to derive the rest of its flat facts from (it
        hands the authority straight back — it only ever reads it);
      - its post-step continuation receives, besides [wstep_post], the ACQUIRE
        OUTCOME: either the word was 0 and the payload [R] has been thawed at
        this hart's own index together with the holder token, or it was not
        and nothing was gained.

    The certificate is the caller's, and its [Q] is exactly the instruction's
    ISA content: [wQ_amo_aq tid lk lock_one] — "the step appended the message
    writing 1 to the lock word, and the [.aq] raised the scalar floor to the
    timestamp the read half took". *)

  Definition wacq_cb (γ : gname) (lk : Arch.pa) R
      (pc : SailStdpp.Values.mword 64) (P : wmstate → Prop) : iProp Σ :=
    (∀ (σ : wmstate) (v : bv 32),
       ⌜∀ j : nat, (j < 4)%nat →
          wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte v j)⌝ -∗
       wlat_interp (wm_img σ) (wm_log σ) -∗
       wmstate_rest σ ={⊤ ∖ ↑wlockN, ∅}=∗
         ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
         ⌜P σ⌝ ∗
         wlat_interp (wm_img σ) (wm_log σ) ∗
         ∃ t0 t1 : mstate,
           ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
           ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
           ▷ (∀ (tick : bool) (σ' : wmstate),
                ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
                ((⌜v = lock_zero⌝ ∗ vwp_hold R (wm_ws σ') ∗ locked γ cpu_id)
                 ∨ ⌜v ≠ lock_zero⌝) -∗
                |={∅, ⊤ ∖ ↑wlockN}=> wmstate_rest σ' ∗
                  WWP Loop))%I.

  Lemma wwp_acquire_swap (γ : gname) (lk : Arch.pa) R
      (pc : SailStdpp.Values.mword 64) (P : wmstate → Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf lk 4 →
    wstep_cert (fin_to_nat cpu_id) pc P
      (wQ_amo_aq (Some (fin_to_nat cpu_id)) lk lock_one) →
    inv wlockN (wlock_inv γ lk R) -∗
    wacq_cb γ lk R pc P -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hacclk Hcert) "#Hinv Hk". rewrite /wacq_cb.
    iApply (wp_winstr pc P (wQ_amo_aq (Some (fin_to_nat cpu_id)) lk lock_one)
              Hgid Haccpc Hcert).
    iIntros (σ) "Hσ".
    iDestruct (wmstate_interp_split σ with "Hσ") as "[Hlat Hrest]".
    iDestruct (wmstate_rest_facts with "Hrest") as %[Hbnd Hwf].
    (* open the lock: ⊤ -> ⊤ ∖ ↑wlockN, held across the step *)
    iInv wlockN as (st t v) "(>Hw & Hlk)" "Hclose".
    (* the swap's return value, off the elements alone *)
    iDestruct (wlat4_flat_gen σ lk (DfracOwn 1) t v Hwf Hacclk with "Hlat Hw")
      as %[Hflat _].
    iMod ("Hk" $! σ v with "[%] Hlat Hrest")
      as "(%Hpc & %Htext & %HP & Hlat & Hcont)"; [exact Hflat|].
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    iDestruct "Hcont" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iExists t0, t1. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQ".
    (* past the step: reassemble the invariant body and fire the core *)
    iDestruct (wacquire_core γ lk R cpu_id (Some (fin_to_nat cpu_id)) σ σ'
                 Hwf Hacclk HQ with "Hlat [Hw Hlk]") as (v') "[%Hflat' Hupd]".
    { iExists st, t, v. iFrame "Hw". iExact "Hlk". }
    assert (Hvv : v = v') by exact (wflat_word_agree σ lk v v' Hflat Hflat').
    subst v'.
    iMod "Hupd" as "(Hlat & Hbody & Harm)".
    iMod ("Hcont" $! tick σ' with "[%] [Harm]") as "[Hrest $]"; [exact Hpost| |].
    { iDestruct "Harm" as "[(-> & HR & Htok)|%Hne]".
      - iLeft. iFrame "HR Htok". by iPureIntro.
      - iRight. by iPureIntro. }
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
    iModIntro. iApply (wmstate_interp_split σ'). iFrame.
  Qed.

(* ====================================================================== *)
(** ** 4. THE SPIN LOOP

    A weak-memory spinlock's loop carries no weak-memory content at all: the
    acquire's whole content is in the ONE attempt that succeeds (§3), and the
    failed attempts leave nothing behind (the contended arm of the core hands
    back [⌜v ≠ 0⌝] and no resource).  What the loop needs is therefore only
    the Löb rule, and the [▷] it consumes is the one [wp_winstr] already
    provides at every instruction — so the loop is generic:

      a body that, from the loop head's resources, either finishes or comes
      back to the loop head under a [▷], runs forever.

    THE BRANCH BACK IS THE CALLER'S.  [bnez]/[j] have no weak leaf yet (M4),
    so the body below is "one [wwp_acquire_swap] ; the caller's retry edge",
    with the retry edge an abstract premise of exactly the shape a branch
    leaf has.  Nothing about the LOCK is abstracted. *)

  Lemma wwp_spin_loop (K : iProp Σ) :
    □ (K -∗ ▷ (K -∗ WWP Loop) -∗
         WWP Loop) -∗
    K -∗ WWP Loop.
  Proof.
    iIntros "#Hbody HK". iLöb as "IH" forall (K) "Hbody HK".
    iApply ("Hbody" with "HK"). iNext. iIntros "HK".
    iApply ("IH" with "Hbody HK").
  Qed.

  (** THE ACQUIRE LOOP.  [K] is whatever the loop head owns (the register
      tower, the pc resource, the caller's frame); one iteration is one
      [wwp_acquire_swap] whose FAILURE branch consumes the recursive call —
      i.e. the [▷] the instruction's own step provides, spent on the branch
      back.  The success branch is inside the caller's callback, where the
      payload and the holder token arrive. *)
  Lemma wwp_acquire_loop (γ : gname) (lk : Arch.pa) R
      (pc : SailStdpp.Values.mword 64) (P : wmstate → Prop) (K : iProp Σ) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf lk 4 →
    wstep_cert (fin_to_nat cpu_id) pc P
      (wQ_amo_aq (Some (fin_to_nat cpu_id)) lk lock_one) →
    inv wlockN (wlock_inv γ lk R) -∗
    □ (K -∗ ▷ (K -∗ WWP Loop) -∗
         wacq_cb γ lk R pc P) -∗
    K -∗ WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hacclk Hcert) "#Hinv #Hatt HK".
    iApply (wwp_spin_loop K with "[] HK").
    iModIntro. iIntros "HK Hrec".
    iApply (wwp_acquire_swap γ lk R pc P Hgid Haccpc Hacclk Hcert with "Hinv").
    iApply ("Hatt" with "HK Hrec").
  Qed.

(* ====================================================================== *)
(** ** 5. THE RELEASING STORE — one [sw] through an invariant

    The releaser's callback is the acquire's minus the branch: it hands over
    the payload [R] AT ITS OWN INDEX ([vwp_hold R (wm_ws σ)] — the hart's
    [wstate] is σ's, which is what the caller's [hart_ws] fragment says), and
    gets back nothing.  What happens in between is the deposit: by
    [WeakMem.ws_bounded] the releaser's whole index is below the timestamp its
    own store takes, so [R] is frozen at [view_scl (S (length (wm_log σ)))] —
    the very timestamp the invariant's elements move to — and handed in.

    ONE CALLBACK SHAPE serves the lock's release and the escrow's setter
    (§6); the namespace is a parameter because they are different
    invariants. *)

  Definition wrel_cb R (pc : SailStdpp.Values.mword 64)
      (P : wmstate → Prop) (N : namespace) : iProp Σ :=
    (∀ σ : wmstate,
       wlat_interp (wm_img σ) (wm_log σ) -∗
       wmstate_rest σ ={⊤ ∖ ↑N, ∅}=∗
         ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
         ⌜P σ⌝ ∗
         wlat_interp (wm_img σ) (wm_log σ) ∗
         vwp_hold R (wm_ws σ) ∗
         ∃ t0 t1 : mstate,
           ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
           ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
           ▷ (∀ (tick : bool) (σ' : wmstate),
                ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
                |={∅, ⊤ ∖ ↑N}=> wmstate_rest σ' ∗
                  WWP Loop))%I.

  Lemma wwp_release_store (γ : gname) (lk : Arch.pa) R
      (pc : SailStdpp.Values.mword 64) (P : wmstate → Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    wstep_cert (fin_to_nat cpu_id) pc P
      (wQ_store (Some (fin_to_nat cpu_id)) lk lock_zero) →
    inv wlockN (wlock_inv γ lk R) -∗
    locked γ cpu_id -∗
    wrel_cb R pc P wlockN -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hcert) "#Hinv Htok Hk". rewrite /wrel_cb.
    iApply (wp_winstr pc P (wQ_store (Some (fin_to_nat cpu_id)) lk lock_zero)
              Hgid Haccpc Hcert).
    iIntros (σ) "Hσ".
    iDestruct (wmstate_interp_split σ with "Hσ") as "[Hlat Hrest]".
    iDestruct (wmstate_rest_facts with "Hrest") as %[Hbnd Hwf].
    iInv wlockN as "Hbody" "Hclose".
    iMod ("Hk" $! σ with "Hlat Hrest")
      as "(%Hpc & %Htext & %HP & Hlat & HR & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    iDestruct "Hcont" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iExists t0, t1. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQ".
    iMod (wrelease_core γ lk R cpu_id (Some (fin_to_nat cpu_id)) σ σ' HQ Hbnd
            with "Hlat Hbody Htok HR") as "[Hlat Hbody]".
    iMod ("Hcont" $! tick σ' with "[%]") as "[Hrest $]"; [exact Hpost|].
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
    iModIntro. iApply (wmstate_interp_split σ'). iFrame.
  Qed.

(* ====================================================================== *)
(** ** 6. THE [started] ESCROW

    THE SETTER is the release, verbatim in structure: deposit at the store's
    own timestamp, retarget the escrow's elements at the message the step
    appended ([WeakStarted.wstarted_set]).  The only difference is which
    invariant is opened and that the value stored is 1, not 0.

    THE WAITER'S LOAD IS NOT HERE, AND THAT IS A FINDING — see the note at the
    end of the file.  Its FENCE is (§7): a fence touches no memory, so it is
    certifiable for any hart, and it is the whole reader-side content of the
    handoff ([WeakStarted.wstarted_deliver] over [WeakInstr.wwp_fence_scl]). *)

  Lemma wwp_started_set (a : Arch.pa) (Pl : vProp Σ)
      (pc : SailStdpp.Values.mword 64) (P : wmstate → Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    wstep_cert (fin_to_nat cpu_id) pc P
      (wQ_store (Some (fin_to_nat cpu_id)) a lock_one) →
    inv wstartedN (wstarted_body a Pl) -∗
    wrel_cb Pl pc P wstartedN -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hcert) "#Hinv Hk". rewrite /wrel_cb.
    iApply (wp_winstr pc P (wQ_store (Some (fin_to_nat cpu_id)) a lock_one)
              Hgid Haccpc Hcert).
    iIntros (σ) "Hσ".
    iDestruct (wmstate_interp_split σ with "Hσ") as "[Hlat Hrest]".
    iDestruct (wmstate_rest_facts with "Hrest") as %[Hbnd Hwf].
    iInv wstartedN as "Hbody" "Hclose".
    iMod ("Hk" $! σ with "Hlat Hrest")
      as "(%Hpc & %Htext & %HP & Hlat & HP0 & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    iDestruct "Hcont" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iExists t0, t1. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQ".
    iMod (wstarted_set a Pl (Some (fin_to_nat cpu_id)) σ σ' HQ Hbnd
            with "Hlat Hbody HP0") as "[Hlat Hat]".
    iMod ("Hcont" $! tick σ' with "[%]") as "[Hrest $]"; [exact Hpost|].
    iMod ("Hclose" with "[Hat]") as "_".
    { iNext. iExists (S (length (wm_log σ))), lock_one. iExact "Hat". }
    iModIntro. iApply (wmstate_interp_split σ'). iFrame.
  Qed.

(* ====================================================================== *)
(** ** 7. THE FENCE STEP

    A fence touches no memory at all, so nothing has to be borrowed from the
    state interpretation and the caller's callback is [wp_winstr]'s verbatim,
    at the full mask ⊤.  What it gets back is the instruction's ISA content in
    VIEW form ([WeakInstr.wV_fence]), which is what the two consumers take:
    [wwp_fence_deliver] / [wwp_fence_scl] (the reader half of a handoff) and
    [wwp_fence_rw_w] (the release fence, which in a promise-free machine
    carries no view content — the STORE publishes). *)

  Lemma wwp_fence_step (pc : SailStdpp.Values.mword 64) (b : barrier_kind)
      (P : wmstate → Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    wstep_cert (fin_to_nat cpu_id) pc P (wQ_fence b) →
    (∀ σ : wmstate, wmstate_interp σ ={⊤,∅}=∗
       ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
       ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
       ⌜P σ⌝ ∗
       ∃ t0 t1 : mstate,
         ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
         ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
         ▷ (∀ (tick : bool) (σ' : wmstate),
              ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
              ⌜wV_fence b σ (wm_ws σ')⌝
              ={∅,⊤}=∗ wmstate_interp σ' ∗
                       WWP Loop)) -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hcert) "Hk".
    iApply (wp_winstr pc P (wQ_fence b) Hgid Haccpc Hcert).
    iIntros (σ) "Hσ". iMod ("Hk" $! σ with "Hσ") as "(%Hpc & %Ht & %HP & Hc)".
    iDestruct "Hc" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iExists t0, t1.
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQ".
    iApply ("Hcont" $! tick σ' with "[%] [%]"); [exact Hpost|exact HQ].
  Qed.

  (** ... and the escrow's READER-SIDE payoff at that step: whatever the
      setter deposited at a timestamp this hart has already READ
      ([WeakMem.load_post_vrOld_nofwd] leaves that after the load) is
      delivered to the hart's own index by the [fence rw,rw].  This is
      [WeakStarted.wstarted_deliver] at the WP altitude's successor. *)
  Lemma wwp_started_fence_deliver (Pl : vProp Σ) (σ σ' : wmstate) (t : nat) :
    (t ≤ w_vrOld (wm_ws σ))%nat →
    wQ_fence Barrier_RISCV_rw_rw σ σ' →
    monPred_at Pl (view_scl t) ⊢ vwp_hold Pl (wm_ws σ').
  Proof. intros Ht HQ. exact (wstarted_deliver Pl σ (wm_ws σ') t Ht HQ). Qed.

(* ====================================================================== *)
(** ** 8. SMOKE TEST: two instructions in a row, each its own [wp_winstr]

    xv6's [release] is [fence rw,w ; sw zero,0(s1)], and this is that
    sequence composed at the WP altitude: the fence's continuation hands back
    the state interpretation together with the STORE's callback, and the store
    runs through the lock invariant.  Nothing glues the two steps but
    [wstep_post] — the successor of the first is the pre-state of the second,
    and the caller never sees a view.

    (It is an [Example], not a theorem of record: what it checks is that the
    two rules' interfaces meet with no adapter.) *)

  Example wwp_release_seq (γ : gname) (lk : Arch.pa) R
      (pcf pcs : SailStdpp.Values.mword 64) (Pf Ps : wmstate → Prop) :
    gen_id = 0%nat →
    acc_wf pcf 4 →
    acc_wf pcs 4 →
    wstep_cert (fin_to_nat cpu_id) pcf Pf (wQ_fence Barrier_RISCV_rw_w) →
    wstep_cert (fin_to_nat cpu_id) pcs Ps
      (wQ_store (Some (fin_to_nat cpu_id)) lk lock_zero) →
    inv wlockN (wlock_inv γ lk R) -∗
    locked γ cpu_id -∗
    (∀ σ : wmstate, wmstate_interp σ ={⊤,∅}=∗
       ⌜register_lookup PC (wm_regs σ) = pcf⌝ ∗
       ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pcf j)⌝ ∗
       ⌜Pf σ⌝ ∗
       ∃ t0 t1 : mstate,
         ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
         ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
         ▷ (∀ (tick : bool) (σ' : wmstate),
              ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
              ⌜wV_fence Barrier_RISCV_rw_w σ (wm_ws σ')⌝
              ={∅,⊤}=∗ wmstate_interp σ' ∗ wrel_cb R pcs Ps wlockN)) -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccf Haccs Hcertf Hcerts) "#Hinv Htok Hk".
    iApply (wwp_fence_step pcf Barrier_RISCV_rw_w Pf Hgid Haccf Hcertf).
    iIntros (σ) "Hσ".
    iMod ("Hk" $! σ with "Hσ") as "(%Hpc & %Htext & %HP & Hc)".
    iDestruct "Hc" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iExists t0, t1.
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQ".
    iMod ("Hcont" $! tick σ' with "[%] [%]") as "[$ Hrel]";
      [exact Hpost|exact HQ|].
    iModIntro.
    iApply (wwp_release_store γ lk R pcs Ps Hgid Haccs Hcerts
              with "Hinv Htok Hrel").
  Qed.

(* ====================================================================== *)
(** ** 9. THE SAME THREE RULES, OVER A DISCHARGED CERTIFICATE

    §3–§6 take the instruction certificate as a premise, the way the SC leaves
    take an [instr] fact.  [WeakCert] discharges it: [wcert_amo_aq] /
    [wcert_store] / [wcert_fence] prove [wstep_cert] outright for a step whose
    EFFECT TRACE is the given one, under the single obligation [wP_conf]
    strengthened to [WeakCert.wP_eff] — "the confined SC run succeeds and its
    trace is exactly these effects".  So the corollaries below have NO
    certificate premise at all: what is left for the caller is one
    [exec_eff]-level fact per instruction, inside the σ-callback, exactly
    where its own SC library lemma already lives.

    The trace of each instruction is: the FETCH read, then the instruction's
    own access(es).  The fetch is left generic in kind/address/width, so a
    compressed 2-byte fetch instantiates these too. *)

  Corollary wwp_acquire_swap_cert (γ : gname) (lk : Arch.pa) R
      (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (aka akw : akinfo) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf lk 4 →
    ak_coh aka = false →
    ak_sync aka = true →
    inv wlockN (wlock_inv γ lk R) -∗
    wacq_cb γ lk R pc
      (wP_eff (Some (fin_to_nat cpu_id))
         [WEread akf pf nf; WEread aka lk 4; WEwrite akw lk 4 lock_one]) -∗
    WWP Loop.
  Proof.
    intros Hgid Haccpc Hacclk Hcoh Hsync. iIntros "#Hinv Hk".
    iApply (wwp_acquire_swap γ lk R pc _ Hgid Haccpc Hacclk
              (wcert_amo_aq (fin_to_nat cpu_id) pc akf pf nf aka akw lk lock_one
                 Hcoh Hsync) with "Hinv Hk").
  Qed.

  Corollary wwp_release_store_cert (γ : gname) (lk : Arch.pa) R
      (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (akw : akinfo) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    inv wlockN (wlock_inv γ lk R) -∗
    locked γ cpu_id -∗
    wrel_cb R pc
      (wP_eff (Some (fin_to_nat cpu_id))
         [WEread akf pf nf; WEwrite akw lk 4 lock_zero]) wlockN -∗
    WWP Loop.
  Proof.
    intros Hgid Haccpc. iIntros "#Hinv Htok Hk".
    iApply (wwp_release_store γ lk R pc _ Hgid Haccpc
              (wcert_store (fin_to_nat cpu_id) pc akf pf nf akw lk lock_zero)
              with "Hinv Htok Hk").
  Qed.

  Corollary wwp_started_set_cert (a : Arch.pa) (Pl : vProp Σ)
      (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (akw : akinfo) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    inv wstartedN (wstarted_body a Pl) -∗
    wrel_cb Pl pc
      (wP_eff (Some (fin_to_nat cpu_id))
         [WEread akf pf nf; WEwrite akw a 4 lock_one]) wstartedN -∗
    WWP Loop.
  Proof.
    intros Hgid Haccpc. iIntros "#Hinv Hk".
    iApply (wwp_started_set a Pl pc _ Hgid Haccpc
              (wcert_store (fin_to_nat cpu_id) pc akf pf nf akw a lock_one)
              with "Hinv Hk").
  Qed.

  (** ... and the loop, whose only premise is now the caller's retry edge. *)
  Corollary wwp_acquire_loop_cert (γ : gname) (lk : Arch.pa) R
      (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (aka akw : akinfo) (K : iProp Σ) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf lk 4 →
    ak_coh aka = false →
    ak_sync aka = true →
    inv wlockN (wlock_inv γ lk R) -∗
    □ (K -∗ ▷ (K -∗ WWP Loop) -∗
         wacq_cb γ lk R pc
           (wP_eff (Some (fin_to_nat cpu_id))
              [WEread akf pf nf; WEread aka lk 4; WEwrite akw lk 4 lock_one])) -∗
    K -∗ WWP Loop.
  Proof.
    intros Hgid Haccpc Hacclk Hcoh Hsync. iIntros "#Hinv #Hatt HK".
    iApply (wwp_acquire_loop γ lk R pc _ K Hgid Haccpc Hacclk
              (wcert_amo_aq (fin_to_nat cpu_id) pc akf pf nf aka akw lk lock_one
                 Hcoh Hsync) with "Hinv Hatt HK").
  Qed.

End wp_lock.

(* ======================================================================
   THE ONE THING THAT DID NOT COMPOSE, AND WHY IT IS A DESIGN ITEM

   THE [started] WAITER'S PLAIN LOAD CANNOT GO THROUGH [wp_winstr] AT ALL,
   and the obstacle is structural rather than incidental.

     [wp_winstr] rests on [WeakBridge]'s PINNED-fragment transfer: the caller
     supplies [exec] facts about [wflat_st σ] — the COHERENT flat projection —
     and the bridge says the weak run agrees with them.  That is sound exactly
     when every read of the step is pinned ([WeakBridge.wstep_ok]'s read arm),
     i.e. when the hart's own index already covers the latest write to the
     bytes it reads.  A racy PLAIN load is the one case where it is not: the
     waiting hart may legally read the era image (flag still 0) while the flat
     projection already holds the setter's 1, so no [exec]-level fact about
     [wflat_st σ] describes the step.

   The AMO is unaffected — its read half is [ak_latest], whose admissibility
   condition IS "read the latest" ([WeakBridge.ak_pins]), which is why the
   whole SPINLOCK composes here and the escrow's reader does not.

   WHAT IT NEEDS (M4, and it is a rule, not a proof): a load rule that
   quantifies over the ADMISSIBLE READ RESULTS instead of the flat value —
   the caller supplies one [exec] fact per admissible value (for a one-shot
   flag, two: the era image's 0 and the setter's 1) and receives the
   corresponding disjunction, with [WeakStarted.wstarted_oneshot] collapsing
   it.  The pieces below the rule already exist: [WeakExec.wp_wrun_step] (the
   PRIMITIVE lifting rule, which has no bridge premise at all) is the right
   floor, and [WeakStarted.wstarted_read_ts] / [wstarted_read_vrOld] are the
   two facts such a rule would hand its caller. *)
