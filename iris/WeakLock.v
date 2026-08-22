(** * WeakLock.v — the weak-memory spinlock (M3b item 3)

    THE DESIGN'S CENTRAL CLAIM, ON REAL MACHINERY: a spinlock whose
    CLIENT-FACING interface is today's — [wis_lock γ lk R] persistent,
    [wlocked γ i] the exclusive holder token, [R] an arbitrary [vProp] — over
    a machine where a store is a message in a log and a load may read a stale
    one.  What changes is only the two sync instructions' proofs.

    ================= WHY THE INVARIANT IS AN [iProp] =================

    Iris invariants may hold only OBJECTIVE assertions (design doc, Decision
    5), and the cleanest way to be objective is to be an [iProp]: the whole
    invariant lives at the BASE altitude (the Cosmo pattern), and the [vProp]
    surface appears only in the payload, frozen at a view:

      wlock_inv γ lk R := ∃ st t v, wlat4 lk (DfracOwn 1) t v ∗ lock_auth γ st ∗
                            ( free: ⌜v = 0⌝ ∗ frag ∗ monPred_at R (view_scl t)
                            | held: ⌜v ≠ 0⌝ )

    Three things make that work, and each is a landed fact rather than a new
    assumption:
      - [WeakInstr.wlat4] — the four latest-write ELEMENTS of the lock word —
        is an [iProp], so it is objective and needs no receipt (M3a);
      - [monPred_at R V] is the [WeakVProp] view-at, objective by
        construction for any [vProp] [R] whatsoever;
      - the timestamp [t] the elements carry IS the timestamp the payload is
        frozen at.  That single identification is the whole handoff: the
        releaser deposits at the timestamp its own store takes
        ([WeakInstr.wwp_release_deposit], resting on [ws_bounded]), and the
        acquirer's [amoswap.w.aq] reads THAT timestamp and gains
        [view_scl t ⊑ ws_view] ([WeakFence.amo_acq_gain]) — so the payload
        thaws into the acquirer's own index by [monPred_mono], and no view
        ever crosses the invariant boundary.

    ================= WHAT IS KEPT AND WHAT IS DEFERRED =================

    KEPT: the lock WORD, the [excl_auth] ghost state and the holder token —
    literally [WpLock]'s ([wlocked γ i] IS [WpLock.locked γ i], so a client's
    token is unchanged in statement), and the transfer of [R].
    DEFERRED (M4 bookkeeping, no design content): the [lk->cpu] field and the
    [lock_name] field, both of which are 8-byte cells and so need the [↦w₈]
    tower that M2b cut; the lock's [lock_state] therefore only ever takes the
    values [None] and [Some (i, true)] here, and the intermediate
    "word taken, cpu not yet written" state is passed through by composing
    [WpLock]'s own two transitions.

    ================= THE ALTITUDE OF THE TWO CORES =================

    [wacquire_core] and [wrelease_core] are stated over the step's PRE- and
    POST-state ([σ], [σ']) with the instruction's weak-memory effect
    ([wQ_amo_aq] / [wQ_store]) as a premise, i.e. at exactly the altitude
    [WeakInstr.wp_winstr] hands a leaf.  See the note at the end of the file:
    that premise is strictly MORE than [WeakInstr.wstep_cert]'s [Q] can
    currently say, and the gap is a real finding about [wstep_cert]'s shape,
    not a shortcut taken here. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac excl.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import iprop invariants ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakFence.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import WeakStore.
Require Import RiscvLang RiscvPtsto.
Require Import WpLock.

Local Open Scope Z_scope.

(** The two values the lock word takes.  (xv6's [locked] field is an [int];
    [acquire] swaps in 1 and [release] stores 0.) *)
Definition lock_zero : bv 32 := (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 32).
Definition lock_one  : bv 32 := (SailStdpp.Values.mword_of_int 1 : SailStdpp.Values.mword 32).

Lemma lock_one_ne_zero : lock_one ≠ lock_zero.
Proof. rewrite /lock_one /lock_zero. intros H. apply bv_eq in H. done. Qed.

(* ---------------------------------------------------------------------- *)
(** T2-0: THE TWO MESSAGE SHAPES the lock word's value protocol admits
    ([WeakGhost.wlock_shaped]), as facts about the messages the two leaves
    actually append.  The acquire's is [WCexcl] (pinned by
    [WeakInstr.wQ_amo_aq_w]); the release's is whatever [wm_class_of]
    computed, of which the leaf knows only [≠ WCplain] — hence the
    protocol's release arm is keyed on the VALUE (a zero word), which the
    leaf does pin. *)

Lemma wwrite_msg_data4 tid k (a : Arch.pa) {w : N} (v : bv w) :
  wm_data (wwrite_msg tid k a 4 v)
  = [nth_byte v 0; nth_byte v 1; nth_byte v 2; nth_byte v 3].
Proof. reflexivity. Qed.

Lemma lock_zero_data4 tid k (a : Arch.pa) :
  wm_data (wwrite_msg tid k a 4 lock_zero) = wlock_zero4.
Proof.
  rewrite wwrite_msg_data4 wlock_zero4_eq. f_equal.
Qed.

Lemma wlock_shaped_acq tid (a : Arch.pa) (v : bv 32) :
  wlock_shaped (wwrite_msg tid WCexcl a 4 v).
Proof.
  rewrite /wlock_shaped wwrite_msg_length.
  split_and!; [reflexivity|discriminate|by left].
Qed.

Lemma wlock_shaped_rel tid k (a : Arch.pa) :
  k ≠ WCplain -> wlock_shaped (wwrite_msg tid k a 4 lock_zero).
Proof.
  intros Hk. rewrite /wlock_shaped wwrite_msg_length.
  split_and!; [reflexivity|exact Hk|right; apply lock_zero_data4].
Qed.

(** T2-0′ (F3′): the ALTERNATION side of the same two messages.  The acquire
    swaps in ONE, which is not the zero word — that, plus the [WCexcl] class
    and the message's author, is the whole content of the acquire step of
    [WeakGhost.alt_step]; the release's is [lock_zero_data4] above. *)
Lemma nth_byte_lock_one_0_ne : nth_byte lock_one 0 <> Z_to_bv 8 0.
Proof. intros H. apply (f_equal bv_unsigned) in H. by vm_compute in H. Qed.

Lemma lock_one_data4_ne tid k (a : Arch.pa) :
  wm_data (wwrite_msg tid k a 4 lock_one) <> wlock_zero4.
Proof.
  rewrite wwrite_msg_data4 wlock_zero4_eq.
  intros H. apply nth_byte_lock_one_0_ne. by injection H.
Qed.

(** The acquire's step: a successful swap on a FREE word installs its
    author. *)
Lemma alt_step_acq_msg (i : CPU) (a : Arch.pa) :
  alt_step None (wwrite_msg (Some (fin_to_nat i)) WCexcl a 4 lock_one)
  = Some (Some (fin_to_nat i)).
Proof.
  apply alt_step_acq; [apply lock_one_data4_ne|reflexivity|reflexivity].
Qed.

(** ... the FAILED swap's: the same message on a HELD word changes nothing. *)
Lemma alt_step_fail_msg (tid : option nat) (a : Arch.pa) (t : nat) :
  alt_step (Some t) (wwrite_msg tid WCexcl a 4 lock_one) = Some (Some t).
Proof. apply alt_step_fail; [apply lock_one_data4_ne|reflexivity]. Qed.

(** ... and the release's: the HOLDER's zero store frees it. *)
Lemma alt_step_rel_msg (i : CPU) k (a : Arch.pa) :
  alt_step (Some (fin_to_nat i))
    (wwrite_msg (Some (fin_to_nat i)) k a 4 lock_zero) = Some None.
Proof. apply alt_step_rel; [apply lock_zero_data4|reflexivity]. Qed.

(* ====================================================================== *)
(** ** 1. The instruction effects the two cores consume

    Both are statements about ONE step of the hart: which message it appended
    and what it did to the hart's index.  They are the weak-memory content of
    [sw] and of [amoswap.w.aq]; everything else about the step (registers,
    devices, the flat memory) is [WeakInstr.wstep_post]'s business and does
    not appear here.  They are [WeakInstr]'s [wQ_store] / [wQ_amo_aq] — the
    certificate-level effects, i.e. exactly what [wstep_cert]'s [Q] carries. *)

(* ====================================================================== *)
(** ** 2. The lock *)

Section weak_lock.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Implicit Types R : vProp Σ.

  Definition wlockN : namespace := nroot .@ "xv6weakspinlock".

  (** THE INVARIANT — an [iProp], hence objective, hence admissible.  [t] is
      the timestamp of the lock word's latest write AND the view the payload
      is frozen at; they are the same number, and that is the handoff. *)
  (** T2-0 (S6 §4/§6b): THE BUNDLE IS [wlat4L], NOT [wlat4] — the lock word's
      four bytes ride the fourth C/D/S state [WeakGhost.WLock] rather than
      [WClean], which is what makes the VALUE PROTOCOL (acquire-RMW writes
      nonzero exclusively / release writes zero) an invariant of the state
      interpretation and hence EXPORTABLE at every reachable configuration
      ([WeakStore.wlp_at_wlat4L], [WeakEvAdequacy.weak_ev_adequacy_lockproto]).

      The registration point [n0] is EXISTENTIAL inside [wlat4L], not a
      parameter of [wlock_inv]: threading it through the ~40 downstream
      statements that mention [wlock_inv] (WeakAcquire, WkOwnPingPong,
      WkYieldFrame, WkCtxSurface, WeakCtxLock, WeakBranch, WeakLeafAmo4Leaf)
      would buy nothing — no client names the registration point, and the
      export recovers it existentially. *)
  (** T2-0′ (F3′): THE TIE.  The lock's ghost state names the holder; so does
      the alternation fold.  [wlock_inv] IDENTIFIES the two, which is what
      makes the fold's step rules discharge locally at the two leaves: the
      acquire's success arm has [st = None] hence [h = None] (the acquire
      rule), its contended arm has [st ≠ None] hence [h ≠ None] (the failed
      swap), and the release holds [locked γ i] hence [h = Some i] (the
      release rule, whose author side condition is the core's new
      [tid = Some (fin_to_nat i)] hypothesis). *)
  Definition tid_of (st : lock_state) : option nat :=
    match st with Some (i, _) => Some (fin_to_nat i) | None => None end.

  Definition wlock_inv (γ : gname) (lk : Arch.pa) (R : vProp Σ) : iProp Σ :=
    (∃ (st : lock_state) (t : nat) (v : bv 32),
       wlat4L lk t v (tid_of st) ∗ lock_auth γ st ∗
       (⌜st = None⌝ ∗ ⌜v = lock_zero⌝ ∗ lock_frag γ None ∗ monPred_at R (view_scl t)
        ∨ ⌜st ≠ None⌝ ∗ ⌜v ≠ lock_zero⌝))%I.

  (** ... so the lock predicate is the embedded invariant: PERSISTENT (as
      today) and OBJECTIVE (new, and what lets two harts share it). *)
  Definition wis_lock (γ : gname) (lk : Arch.pa) (R : vProp Σ) : vProp Σ :=
    (⎡inv wlockN (wlock_inv γ lk R)⎤)%I.

  Global Instance wis_lock_persistent γ lk R : Persistent (wis_lock γ lk R).
  Proof. apply _. Qed.
  Global Instance wis_lock_objective γ lk R : Objective (wis_lock γ lk R).
  Proof. apply _. Qed.

  (** THE HOLDER TOKEN IS TODAY'S, unchanged in statement and in algebra. *)
  Definition wlocked (γ : gname) (i : CPU) : vProp Σ := (⎡locked γ i⎤)%I.

  Global Instance wlocked_objective γ i : Objective (wlocked γ i).
  Proof. apply _. Qed.

  Lemma wlocked_exclusive γ i j : wlocked γ i -∗ wlocked γ j -∗ False.
  Proof.
    rewrite /wlocked. iIntros "H1 H2".
    iAssert (⌜False⌝)%I with "[H1 H2]" as %[].
    iCombine "H1 H2" as "H". iStopProof.
    rewrite -(embed_pure (PROP1 := iProp Σ) False). apply embed_mono.
    iIntros "[H1 H2]". by iDestruct (locked_exclusive with "H1 H2") as "%".
  Qed.

  (** ALLOCATION — AND REGISTRATION (T2-0).  A free lock word (owned
      outright, at the timestamp its elements carry) plus the payload frozen
      at that timestamp — which is what [initlock]'s own store leaves —
      becomes a lock, and the C→[WLock] ghost flip happens HERE, at the
      current log length.  That is exactly why the protocol is stated on the
      post-registration SUFFIX: [initlock]'s own store is a [WCplain] message
      on the very bytes being registered, and it sits below [length log]. *)
  Lemma wlock_alloc (lk : Arch.pa) (R : vProp Σ) (t : nat) img log E :
    wlat_interp img log -∗
    wlat4 lk (DfracOwn 1) t lock_zero -∗
    monPred_at R (view_scl t) ={E}=∗
    wlat_interp img log ∗ ∃ γ : gname, inv wlockN (wlock_inv γ lk R).
  Proof.
    iIntros "Hi Hw HR".
    iMod (wlat4L_mint img log lk t lock_zero with "Hi Hw") as "[Hi Hw]".
    iMod (own_alloc ((●E (None : leibnizO lock_state)
                      ⋅ ◯E (None : leibnizO lock_state)) : lockUR)) as (γ) "[Ha Hf]".
    { apply excl_auth_valid. }
    iMod (inv_alloc wlockN _ (wlock_inv γ lk R) with "[Hw Ha Hf HR]") as "#Hinv".
    { iNext. iExists None, t, lock_zero. rewrite /tid_of. iFrame "Hw Ha".
      iLeft. iSplitR; [done|]. iSplitR; [done|]. iFrame "Hf HR". }
    iModIntro. iFrame "Hi". iExists γ. iExact "Hinv".
  Qed.

  (** T2-0's REGISTRATION SEAM, instantiated.  [WeakGhost.wlock_regd] is
      what travels to the adequacy export: the persistent [inv] assertion
      plus the accessor "the body holds byte [acc_addr lk j]'s [WLock]
      fragment at some registration point, and takes it back".  The lock
      invariant satisfies it for each of the word's four bytes, and this is
      the ONLY thing the export needs to know about the lock library — which
      is why [WeakGhost] and [WeakEvAdequacy] stay independent of it. *)
  Lemma wlock_inv_regd (γ : gname) (lk : Arch.pa) R (j : nat) :
    (j < 4)%nat ->
    inv wlockN (wlock_inv γ lk R) -∗ wlock_regd wlockN (acc_addr lk j) (pa_z lk).
  Proof.
    intros Hj. iIntros "#Hinv". rewrite /wlock_regd.
    iExists (wlock_inv γ lk R). iFrame "Hinv". iModIntro.
    iIntros "Hbody". iDestruct "Hbody" as (st t v) "(Hw & Ha & Harm)".
    iDestruct "Hw" as (n0) "[Hel (L0 & L1 & L2 & L3)]".
    iExists n0, (tid_of st).
    destruct j as [|[|[|[|j]]]]; [| | | |lia].
    - iFrame "L0". iIntros "L0". iExists st, t, v. iFrame "Ha Harm".
      iExists n0. rewrite /wlock_win. iFrame.
    - iFrame "L1". iIntros "L1". iExists st, t, v. iFrame "Ha Harm".
      iExists n0. rewrite /wlock_win. iFrame.
    - iFrame "L2". iIntros "L2". iExists st, t, v. iFrame "Ha Harm".
      iExists n0. rewrite /wlock_win. iFrame.
    - iFrame "L3". iIntros "L3". iExists st, t, v. iFrame "Ha Harm".
      iExists n0. rewrite /wlock_win. iFrame.
  Qed.

(* ====================================================================== *)
(** ** 3. Reading the lock word out of the invariant

    The AMO's read half is [ak_latest] ([WeakBridge.ak_pins]), so the ELEMENT
    bundle alone determines both the value the swap returns and the timestamp
    it reads — with no ownership and no hypothesis about the acquirer's views
    (M3a).  Unlike [WeakInstr.wwp_amoswap_w_aq_inv] this hands the bundle
    BACK, because the acquire has to update it afterwards (its own write). *)

  Lemma wlat4_flat_gen (σ : wmstate) (a : Arch.pa) (dq : dfrac) (t : nat)
      (w : bv 32) :
    wlog_wf (wm_log σ) → acc_wf a 4 →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat4 a dq t w -∗
    ⌜(∀ j : nat, (j < 4)%nat →
        wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)) ∧
     (∀ j : nat, (j < 4)%nat → latest_ts (wm_log σ) (acc_addr a j) = t)⌝.
  Proof.
    intros Hwf Hacc. iIntros "Hi (H0 & H1 & H2 & H3)".
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a 0 = Some (nth_byte w 0)
               ∧ latest_ts (wm_log σ) (acc_addr a 0) = t⌝)%I as %E0.
    { rewrite -(acc_wf_byte a 4 0 Hacc ltac:(lia)).
      iApply (wpt_img_flat_lookup_gen σ (pa_add a 0) dq t (nth_byte w 0) Hwf
                with "Hi [H0]").
      rewrite (acc_wf_byte a 4 0 Hacc ltac:(lia)). iExact "H0". }
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a 1 = Some (nth_byte w 1)
               ∧ latest_ts (wm_log σ) (acc_addr a 1) = t⌝)%I as %E1.
    { rewrite -(acc_wf_byte a 4 1 Hacc ltac:(lia)).
      iApply (wpt_img_flat_lookup_gen σ (pa_add a 1) dq t (nth_byte w 1) Hwf
                with "Hi [H1]").
      rewrite (acc_wf_byte a 4 1 Hacc ltac:(lia)). iExact "H1". }
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a 2 = Some (nth_byte w 2)
               ∧ latest_ts (wm_log σ) (acc_addr a 2) = t⌝)%I as %E2.
    { rewrite -(acc_wf_byte a 4 2 Hacc ltac:(lia)).
      iApply (wpt_img_flat_lookup_gen σ (pa_add a 2) dq t (nth_byte w 2) Hwf
                with "Hi [H2]").
      rewrite (acc_wf_byte a 4 2 Hacc ltac:(lia)). iExact "H2". }
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a 3 = Some (nth_byte w 3)
               ∧ latest_ts (wm_log σ) (acc_addr a 3) = t⌝)%I as %E3.
    { rewrite -(acc_wf_byte a 4 3 Hacc ltac:(lia)).
      iApply (wpt_img_flat_lookup_gen σ (pa_add a 3) dq t (nth_byte w 3) Hwf
                with "Hi [H3]").
      rewrite (acc_wf_byte a 4 3 Hacc ltac:(lia)). iExact "H3". }
    iPureIntro. split; intros j Hj;
      destruct j as [|[|[|[|j]]]];
      first [exact (proj1 E0)|exact (proj1 E1)|exact (proj1 E2)|exact (proj1 E3)
            |exact (proj2 E0)|exact (proj2 E1)|exact (proj2 E2)|exact (proj2 E3)
            |lia].
  Qed.

(* ====================================================================== *)
(** ** 4. THE ACQUIRE CORE — one [amoswap.w.aq]

    Open the invariant, hand the machinery the element bundle, and get back:
    the flat lock word (which is what the SC [amoswap] execute-lemma consumes,
    and what the spin test branches on), and — after the step — the invariant
    restored at the new timestamp plus, IF the word read was 0, the payload
    [R] thawed at the acquirer's OWN index together with the holder token.

    The contended arm is not a no-op on the weak state: the AMO writes 1 back
    even when it read 1, so the invariant's elements are retargeted at the new
    message in BOTH arms.  That is why the bundle is held at full fraction. *)

  Lemma wacquire_core (γ : gname) (lk : Arch.pa) R (i : CPU) (tid : option nat)
      (σ σ' : wmstate) :
    wlog_wf (wm_log σ) → acc_wf lk 4 → wQ_amo_aq tid lk lock_one σ σ' →
    (* T2-0′ (F3′): THE AUTHOR TIE.  The message the step appends is THIS
       hart's — true at every xv6 site ([holding()]) — and it is the only way
       the alternation fold's author bookkeeping is sound. *)
    tid = Some (fin_to_nat i) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk R -∗
    ∃ v : bv 32,
      ⌜∀ j : nat, (j < 4)%nat →
         wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte v j)⌝ ∗
      (|==> wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ lk R ∗
            ((⌜v = lock_zero⌝ ∗ vwp_hold R (wm_ws σ') ∗ locked γ i)
             ∨ ⌜v ≠ lock_zero⌝)).
  Proof.
    intros Hwf Hacc Heff Htid.
    destruct Heff as ((Himg & (kc & Hlog & _) & Hle & Hflr) & Hgain & Hexcl).
    iIntros "Hi Hinv".
    iDestruct "Hinv" as (st t v) "(Hw & Ha & Harm)".
    iDestruct (wlat4L_flat_gen σ lk t v (tid_of st) Hwf Hacc with "Hi Hw")
      as %[Hflat Hts].
    iExists v. iSplitR; [by iPureIntro|].
    iDestruct "Harm" as "[(-> & -> & Hfrag & HR)|(%Hst & %Hv)]".
    - (* the lock was FREE: the swap is a SUCCESSFUL ACQUIRE, so the fold
         moves from [None] to this hart — take the lock and thaw the payload *)
      iMod (wlat4L_store_gen tid WCexcl σ σ' lk t lock_zero lock_one None
              (Some (fin_to_nat i))
              (wlock_shaped_acq tid lk lock_one)
              ltac:(rewrite Htid; apply alt_step_acq_msg) Himg Hexcl
              with "Hi Hw") as "[Hi Hw]".
      iMod (lock_take γ i with "Ha Hfrag") as "[Ha Hpre]".
      iMod (lock_setcpu γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Htok)".
      iModIntro. iFrame "Hi". iSplitR "HR Htok".
      + iExists (Some (i, true)), (S (length (wm_log σ))), lock_one.
        iFrame "Hw Ha". iRight. iSplitR; [done|].
        iPureIntro. apply lock_one_ne_zero.
      + iLeft. iSplitR; [done|]. iFrame "Htok".
        (* THE THAW: the payload was frozen at [t], the acquire's scalar floor
           now covers [t] ([wQ_amo_aq] at byte 0, where [t] IS [latest_ts]) *)
        rewrite /vwp_hold. iApply (monPred_mono R (view_scl t) (ws_view (wm_ws σ'))).
        { rewrite -(Hts 0%nat ltac:(lia)). apply Hgain. lia. }
        iExact "HR".
    - (* the lock was HELD: the swap is a FAILED one; the fold keeps the
         holder, and nothing moves but the timestamp *)
      destruct st as [[j b]|]; [|by destruct Hst].
      iMod (wlat4L_store_gen tid WCexcl σ σ' lk t v lock_one
              (Some (fin_to_nat j)) (Some (fin_to_nat j))
              (wlock_shaped_acq tid lk lock_one)
              (alt_step_fail_msg tid lk (fin_to_nat j)) Himg Hexcl
              with "Hi Hw") as "[Hi Hw]".
      iModIntro. iFrame "Hi". iSplitR "".
      + iExists (Some (j, b)), (S (length (wm_log σ))), lock_one.
        iFrame "Hw Ha". iRight. iSplitR; [done|].
        iPureIntro. apply lock_one_ne_zero.
      + iRight. by iPureIntro.
  Qed.

(* ====================================================================== *)
(** ** 5. THE RELEASE CORE — [fence rw,w] then [sw zero,0(s1)]

    The holder deposits [R] at the timestamp its OWN store takes.  That is
    sound at the [sw] step ALONE — [WeakInstr.wwp_release_deposit] rests only
    on [ws_bounded] (every view the releaser holds is a real timestamp of the
    current log, hence below the fresh top), not on any fence — so the fence
    contributes NO view content in this machine.  The [fence rw,w] is still
    executed and still certified for fidelity, and its obligation reappears in
    the M6 robustness theorem, where a predecessor-W fence is what stops the
    store from being promised early (design doc, Decision 1). *)

  Lemma wrelease_core (γ : gname) (lk : Arch.pa) R (i : CPU) (tid : option nat)
      (σ σ' : wmstate) :
    wQ_store tid lk lock_zero σ σ' →
    (* T2-0′ (F3′): THE AUTHOR TIE — the releasing message is the holder's
       own (see [wacquire_core]).  It is what the fold's release step needs:
       only the holder may free the word. *)
    tid = Some (fin_to_nat i) →
    (* φ-upgrade §1: the RELEASE-PENDING flag is what makes this store's
       message release-class ([WeakInstr.wm_class_of_relp]), hence what lets
       the lock word's invariant-held bundle be retargeted CLEAN.  It is set
       by the [fence rw,w] that precedes every xv6 release, and it is the one
       fact the fence contributes to this machine. *)
    w_relp (wm_ws σ) = true →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk R -∗
    locked γ i -∗
    vwp_hold R (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ lk R.
  Proof.
    intros (Himg & (kc & Hlog & Hnp) & Hle & Hflr) Htid Hrelp Hbnd.
    specialize (Hnp Hrelp).
    iIntros "Hi Hinv Htok HR".
    iDestruct "Hinv" as (st t v) "(Hw & Ha & _)".
    (* the holder's token says the lock is held by [i] — hence, by the tie,
       so does the alternation fold *)
    iDestruct (locked_state with "Ha Htok") as %->.
    (* THE DEPOSIT: everything the releaser holds is below the store's own
       timestamp, so it may be frozen there and handed to the invariant *)
    iAssert (monPred_at R (view_scl (S (length (wm_log σ)))))%I with "[HR]" as "HR".
    { by iApply (wwp_release_deposit R σ Hbnd with "HR"). }
    (* T2-0: the release arm of [WeakGhost.wlock_shaped] — the message writes
       the ZERO word and is at least release-class (the [w_relp] flag the
       preceding [fence rw,w] set is what rules out [WCplain]). *)
    iMod (wlat4L_store_gen tid kc σ σ' lk t v lock_zero
            (Some (fin_to_nat i)) None
            (wlock_shaped_rel tid kc lk Hnp)
            ltac:(rewrite Htid; apply alt_step_rel_msg) Himg Hlog
            with "Hi Hw") as "[Hi Hw]".
    iMod (lock_clrcpu γ (Some (i, true)) i with "Ha Htok") as "(_ & Ha & Hpre)".
    iMod (lock_give γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Hfrag)".
    iModIntro. iFrame "Hi".
    iExists None, (S (length (wm_log σ))), lock_zero.
    iFrame "Hw Ha". iLeft. iSplitR; [done|].
    iSplitR; [done|]. iFrame "Hfrag HR".
  Qed.

(* ====================================================================== *)
(** ** 6. THE PROTECTED LOCK — the payload's FOOTPRINT (T2-0′ / F3″,
    route-b §4d.3′)

    [wlock_inv] protects a payload [R] by an Iris invariant; NOTHING in it
    says what the payload's BYTES are, and that is exactly what route B's
    cycle kill needs to know (`(P)` of §4d.1 F6: the message a critical
    section read was written inside its writer's critical section of the SAME
    lock).  [wplock_body] is [wlock_inv] with the payload's FOOTPRINT
    declared: a list [F] of byte addresses whose C/D/S state is
    [WeakGhost.WProt], registered at the same point [n0] as the word itself.

    WHY THE FRAGMENTS LIVE IN THE INVARIANT, AND WHY [n0] IS A PARAMETER.
    [wprot_at]'s content is a statement about the fold [wlp_holder_at log
    base n0 ·]: it is only as good as the registration point it is stated at,
    and nothing relates two independently-quantified ones.  So the
    footprint's [n0] and the word's must be THE SAME NUMBER — a resource
    fact, which can only be made persistent by living in one invariant.
    Hence [n0] is a parameter here where [wlock_inv] hides it, and the
    footprint's [WProt] fragments sit next to the word's [WLock] ones.
    (Everything else about the lock is unchanged: [wplock_body_inv] forgets
    the footprint and is an ordinary [wlock_inv].) *)

  Context `{!wprotG Σ}.

  Lemma acc_addr_0 (a : Arch.pa) : acc_addr a 0 = pa_z a.
  Proof. rewrite /acc_addr. lia. Qed.

  (** The dirty author a footprint byte may carry, tied to the lock's state:
      only the CURRENT holder may have an outstanding owned store on the
      payload.  φ's D-state, with the lock protocol saying whose it is; the
      release's flip ([wprot_win_flip]) is what re-establishes it. *)
  Definition prot_dok (d : option CPU) (st : lock_state) : Prop :=
    match d with
    | None => True
    | Some c => exists b : bool, st = Some (c, b)
    end.

  Definition wprot_win (γ : gname) (base : Z) (n0 : nat) (F : list Z)
      (st : lock_state) : iProp Σ :=
    ([∗ list] a ∈ F, ∃ d : option CPU,
       wprot_st a γ base n0 n0 d ∗ ⌜prot_dok d st⌝)%I.

  Global Instance wprot_win_timeless γ base n0 F st :
    Timeless (wprot_win γ base n0 F st).
  Proof. rewrite /wprot_win. apply _. Qed.

  (** A state change that only ever WIDENS what [prot_dok] allows — the
      acquire's [None → Some (i, b)] — leaves the window alone. *)
  Lemma wprot_win_free γ base n0 F st :
    wprot_win γ base n0 F None -∗ wprot_win γ base n0 F st.
  Proof.
    rewrite /wprot_win. iIntros "H".
    iApply (big_sepL_mono with "H"). intros k a Hk.
    iIntros "H". iDestruct "H" as (d) "[Hpr %Hd]".
    destruct d as [c|]; [by destruct Hd as (b & [=])|].
    iExists None. iFrame "Hpr".
  Qed.

  Definition wplock_body (γ γr : gname) (lk : Arch.pa) (R : vProp Σ)
      (n0 : nat) (F : list Z) : iProp Σ :=
    (∃ (st : lock_state) (t : nat) (v : bv 32) (L : list (Z * nat)),
       wlat4_lock lk n0 t v (tid_of st) ∗ lock_auth γ st ∗
       wprot_win γ (pa_z lk) n0 F st ∗
       prot_recs γr L ∗ ⌜prot_recs_ok n0 L⌝ ∗
       (⌜st = None⌝ ∗ ⌜v = lock_zero⌝ ∗ lock_frag γ None ∗
          monPred_at R (view_scl t)
        ∨ ⌜st ≠ None⌝ ∗ ⌜v ≠ lock_zero⌝))%I.

  (** It IS a lock invariant — the footprint and the records are extra. *)
  Lemma wplock_body_inv γ γr lk R n0 F :
    wplock_body γ γr lk R n0 F ⊢ wlock_inv γ lk R.
  Proof.
    iIntros "H". iDestruct "H" as (st t v L) "(Hw & Ha & _ & _ & _ & Harm)".
    iExists st, t, v. iSplitL "Hw"; [by iExists n0|]. iFrame "Ha Harm".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 6a. REGISTRATION *)

  (** The whole footprint at once: full-fraction CLEAN fragments in, [WProt]
      fragments out, all at the current log length — where the protection
      clause is vacuous, so nothing about the payload's history is required
      (which is what makes registration legal after the allocator's zeroing
      and after [initlock]). *)
  Lemma wprot_register_list (img : _) (log : list wmsg) (F : list Z)
      (γ : gname) (base : Z) :
    wlat_interp img log -∗ ([∗ list] a ∈ F, wclean a (DfracOwn 1)) ==∗
    wlat_interp img log ∗ wprot_win γ base (length log) F None.
  Proof.
    induction F as [|a F IH]; iIntros "Hi HF".
    - iModIntro. rewrite /wprot_win /=. by iFrame.
    - rewrite /wprot_win /=. iDestruct "HF" as "[Ha HF]".
      iMod (wprot_register img log a γ base (length log) (Nat.le_refl _)
              with "Hi Ha") as "[Hi Hpr]".
      iMod (IH with "Hi HF") as "[Hi Htl]".
      iModIntro. iFrame "Hi Htl". iExists None. iFrame "Hpr".
  Qed.

  (** DEREGISTRATION, purely at the ghost level: with the lock free every
      byte's dirty author is [None], so the whole footprint comes back as
      ordinary clean fragments.  (The Iris-level side conditions — the full
      fractions, and that the lock is free — are the caller's; this is the
      ghost half, and it is what a [pipefree]-shaped client spends.) *)
  Lemma wprot_deregister_list (img : _) (log : list wmsg) (F : list Z)
      (γ : gname) (base : Z) (n0 : nat) :
    wlat_interp img log -∗ wprot_win γ base n0 F None ==∗
    wlat_interp img log ∗ ([∗ list] a ∈ F, wclean a (DfracOwn 1)).
  Proof.
    induction F as [|a F IH]; iIntros "Hi HF".
    - iModIntro. by iFrame.
    - rewrite /wprot_win /=. iDestruct "HF" as "[Ha HF]".
      iDestruct "Ha" as (d) "[Hpr %Hd]".
      destruct d as [c|]; [by destruct Hd as (b & [=])|].
      iMod (wprot_deregister img log a γ base n0 n0 with "Hi Hpr")
        as "[Hi Hcl]".
      iMod (IH with "Hi HF") as "[Hi Htl]".
      iModIntro. by iFrame.
  Qed.

  (** THE ALLOCATION.  [wlock_alloc]'s protected twin: the lock word AND the
      declared footprint are registered in the same instant, so they share
      the registration point — which is the whole reason the invariant names
      it. *)
  Lemma wplock_alloc (lk : Arch.pa) (R : vProp Σ) (F : list Z) (t : nat)
      img log E :
    wlat_interp img log -∗
    wlat4 lk (DfracOwn 1) t lock_zero -∗
    ([∗ list] a ∈ F, wclean a (DfracOwn 1)) -∗
    monPred_at R (view_scl t) ={E}=∗
    wlat_interp img log ∗
    ∃ γ γr : gname, inv wlockN (wplock_body γ γr lk R (length log) F).
  Proof.
    iIntros "Hi Hw HF HR".
    iMod (own_alloc ((●E (None : leibnizO lock_state)
                      ⋅ ◯E (None : leibnizO lock_state)) : lockUR))
      as (γ) "[Ha Hf]".
    { apply excl_auth_valid. }
    iMod prot_recs_alloc as (γr) "Hrecs".
    iMod (wlat4_lock_mint img log lk t lock_zero with "Hi Hw") as "[Hi Hw]".
    iMod (wprot_register_list img log F γ (pa_z lk) with "Hi HF")
      as "[Hi Hwin]".
    iMod (inv_alloc wlockN _ (wplock_body γ γr lk R (length log) F)
            with "[Hw Ha Hf HR Hwin Hrecs]") as "#Hinv".
    { iNext. iExists None, t, lock_zero, []. rewrite /tid_of.
      iFrame "Hw Ha Hwin Hrecs". iSplitR.
      { iPureIntro. intros ap Hap. by apply elem_of_nil in Hap. }
      iLeft. iSplitR; [done|]. iSplitR; [done|]. iFrame "Hf HR". }
    iModIntro. iFrame "Hi". iExists γ, γr. iExact "Hinv".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 6b. THE ADEQUACY SEAMS

      [WeakLock.wlock_inv_regd]'s twins.  Both hand out the byte's [WProt]
      fragment TOGETHER WITH the lock word's byte-0 [WLock] fragment at the
      same [n0], which is what makes the exported protection clause and the
      exported alternation speak of one and the same fold. *)
  Lemma wplock_inv_regd (γ γr : gname) (lk : Arch.pa) R (n0 : nat)
      (F : list Z) (a : Z) :
    a ∈ F ->
    inv wlockN (wplock_body γ γr lk R n0 F) -∗ wprot_regd wlockN a (pa_z lk).
  Proof.
    intros Hin. apply elem_of_list_lookup in Hin as [k Hk].
    iIntros "#Hinv". rewrite /wprot_regd.
    iExists (wplock_body γ γr lk R n0 F). iFrame "Hinv". iModIntro.
    iIntros "Hbody".
    iDestruct "Hbody" as (st t v L) "(Hw & Ha & Hwin & Hrec & %Hok & Harm)".
    iDestruct "Hw" as "[Hel (L0 & L1 & L2 & L3)]".
    iDestruct (big_sepL_lookup_acc _ _ k a Hk with "Hwin") as "[Hb Hwin]".
    iDestruct "Hb" as (d) "[Hpr %Hd]".
    replace (acc_addr lk 0) with (pa_z lk) by (rewrite /acc_addr; lia).
    iExists γ, n0, n0, d, (tid_of st). iFrame "Hpr L0".
    iIntros "Hpr L0". iExists st, t, v, L. iFrame "Ha Hrec Harm".
    iSplitL "Hel L0 L1 L2 L3".
    { rewrite /wlat4_lock /wlock_win.
      replace (acc_addr lk 0) with (pa_z lk) by (rewrite /acc_addr; lia).
      iFrame "Hel L0 L1 L2 L3". }
    iSplitL; [|by iPureIntro].
    iApply "Hwin". iExists d. iFrame "Hpr". by iPureIntro.
  Qed.

  Lemma wplock_inv_rd_regd (γ γr : gname) (lk : Arch.pa) R (n0 : nat)
      (F : list Z) (a : Z) :
    a ∈ F ->
    inv wlockN (wplock_body γ γr lk R n0 F) -∗
    wprot_rd_regd wlockN γr a (pa_z lk).
  Proof.
    intros Hin. apply elem_of_list_lookup in Hin as [k Hk].
    iIntros "#Hinv". rewrite /wprot_rd_regd.
    iExists (wplock_body γ γr lk R n0 F). iFrame "Hinv". iModIntro.
    iIntros "Hbody".
    iDestruct "Hbody" as (st t v L) "(Hw & Ha & Hwin & Hrec & %Hok & Harm)".
    iDestruct "Hw" as "[Hel (L0 & L1 & L2 & L3)]".
    iDestruct (big_sepL_lookup_acc _ _ k a Hk with "Hwin") as "[Hb Hwin]".
    iDestruct "Hb" as (d) "[Hpr %Hd]".
    replace (acc_addr lk 0) with (pa_z lk) by (rewrite /acc_addr; lia).
    iExists γ, n0, n0, d, (tid_of st), L. iFrame "Hpr L0 Hrec".
    iSplitR; [by iPureIntro|].
    iIntros "Hpr L0 Hrec". iExists st, t, v, L. iFrame "Ha Hrec Harm".
    iSplitL "Hel L0 L1 L2 L3".
    { rewrite /wlat4_lock /wlock_win.
      replace (acc_addr lk 0) with (pa_z lk) by (rewrite /acc_addr; lia).
      iFrame "Hel L0 L1 L2 L3". }
    iSplitL; [|by iPureIntro].
    iApply "Hwin". iExists d. iFrame "Hpr". by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 6c. THE PROTECTED STORE AND THE READ RECORD *)

  (** The holder fact, off the invariant and the token: the lock word's fold
      names THIS hart at the log's top.  This is the premise the pure
      protected-store rule ([WeakGhost.wcds_ok_store_prot]) takes, and the
      only thing a protected store site needs the lock for. *)
  Lemma wplock_holder (γ γr : gname) (lk : Arch.pa) R (n0 : nat) (F : list Z)
      (i : CPU) (img : _) (log : list wmsg) :
    wlat_interp img log -∗ wplock_body γ γr lk R n0 F -∗ locked γ i -∗
    ⌜wlp_holder_at log (pa_z lk) n0 (length log)
       = Some (Some (fin_to_nat i))⌝.
  Proof.
    iIntros "Hi Hbody Htok".
    iDestruct "Hbody" as (st t v L) "(Hw & Ha & _ & _ & _ & _)".
    iDestruct (locked_state with "Ha Htok") as %->.
    iDestruct "Hw" as "[_ (L0 & _ & _ & _)]".
    iDestruct (wlp_alt_of_lock with "Hi L0") as %[_ Hf].
    iPureIntro. rewrite -Hf /acc_addr. f_equal. lia.
  Qed.

  (** THE PROTECTED STORE, at the altitude the two lock cores are stated at:
      the message the step appended is an OWNED store of this hart to a
      footprint byte, and it is legal because the token says this hart holds
      the lock.  The byte's value element is retargeted and its state becomes
      "dirty by [i]"; the lock's own bundle is untouched. *)
  Lemma wprot_store_core (γ γr : gname) (lk : Arch.pa) R (n0 : nat)
      (F : list Z) (i : CPU) (a : Z) (m : wmsg) (σ σ' : wmstate)
      (t : nat) (w b : bv 8) :
    a ∈ F ->
    msg_byte m a = Some b -> (forall a', a' <> a -> msg_byte m a' = None) ->
    wm_ak m = WCplain -> wm_tid m = Some (fin_to_nat i) ->
    wm_img σ' = wm_img σ -> wm_log σ' = (wm_log σ ++ [m])%list ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wplock_body γ γr lk R n0 F -∗ locked γ i -∗
    wlat_elem a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wplock_body γ γr lk R n0 F ∗
    locked γ i ∗ wlat_elem a (DfracOwn 1) (S (length (wm_log σ))) b.
  Proof.
    intros Hin Hma Hother Hk Htid Himg Hlog.
    apply elem_of_list_lookup in Hin as [j Hj].
    iIntros "Hi Hbody Htok Hel".
    iDestruct (wplock_holder γ γr lk R n0 F i (wm_img σ) (wm_log σ)
                 with "Hi Hbody Htok") as %Hhold.
    iDestruct "Hbody" as (st t0 v L) "(Hw & Ha & Hwin & Hrec & %Hok & Harm)".
    iDestruct (locked_state with "Ha Htok") as %->.
    iDestruct (big_sepL_lookup_acc _ _ j a Hj with "Hwin") as "[Hb Hwin]".
    iDestruct "Hb" as (d) "[Hpr %Hd]".
    assert (Hdd : d = None \/ d = Some i).
    { destruct d as [c|]; [|by left]. right.
      destruct Hd as (bb & [= <- _]). done. }
    iMod (wprot_store (wm_img σ) (wm_log σ) m a γ (pa_z lk) n0 n0 d i t w b
            Hk Htid Hdd Hhold Hma Hother with "Hi Hel Hpr")
      as "(Hi & Hel & Hpr)".
    iModIntro. rewrite Himg Hlog. iFrame "Hi Hel Htok".
    iExists (Some (i, true)), t0, v, L. iFrame "Ha Hw Hrec Harm".
    iSplitL "Hwin Hpr"; [|by iPureIntro].
    iApply "Hwin". iExists (Some i). iFrame "Hpr". iPureIntro. by exists true.
  Qed.

  (** THE READ RECORD.  The protected LOAD rule is the ordinary load PLUS
      this: a persistent receipt that byte [a] of this lock's payload was
      read at log position [p].  Its only content is the position bound the
      export re-states ([r0 ≤ p], with [r0 = n0] here), which is what tells
      the kill that the read it is chasing happened inside the protected
      window. *)
  Lemma wprot_read_record (γ γr : gname) (lk : Arch.pa) R (n0 : nat)
      (F : list Z) (a : Z) (p : nat) :
    (n0 <= p)%nat ->
    wplock_body γ γr lk R n0 F ==∗
    wplock_body γ γr lk R n0 F ∗ prot_read γr a p.
  Proof.
    intros Hp. iIntros "Hbody".
    iDestruct "Hbody" as (st t v L) "(Hw & Ha & Hwin & Hrec & %Hok & Harm)".
    iMod (prot_recs_append γr L a p with "Hrec") as "[Hrec #Hrd]".
    iModIntro. iFrame "Hrd".
    iExists st, t, v, (L ++ [(a, p)])%list. iFrame "Hw Ha Hwin Hrec Harm".
    iPureIntro. intros ap Hap. apply elem_of_app in Hap as [Hap|Hap].
    - exact (Hok ap Hap).
    - apply elem_of_list_singleton in Hap as ->. exact Hp.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 6d. THE TWO CORES, AT A FIXED REGISTRATION POINT

      [wacquire_core] / [wrelease_core] verbatim, over [wplock_body] instead
      of [wlock_inv] — the [n0] the footprint names has to survive the two
      protocol steps, and [wlock_inv] hides it.  The only NEW content is what
      happens to the footprint window:

        - the ACQUIRE takes the lock from FREE, where every payload byte's
          dirty author is [None] (the previous holder published its backlog
          when it released), so the window survives by [wprot_win_free];
        - the RELEASE hands it back, and its [WCrel] message publishes the
          holder's whole owned backlog — so every payload byte flips D→C
          ([wprot_win_flip]).  That is why this core needs the release
          message's class PINNED at [WCrel] where [wrelease_core] makes do
          with [≠ WCplain]: the weaker fact keeps the lock WORD clean but
          does not publish anything, and the footprint's φ obligation is
          about publication.  Every xv6 release site has it (the store is a
          plain [sw] — [ak_latest] false — under the [fence rw,w]'s
          [w_relp], so [WeakInterp.wm_class_of] computes [WCrel]). *)

  Lemma wprot_win_flip (img : _) (log : list wmsg) (mrel : wmsg)
      (γ : gname) (base : Z) (n0 : nat) (F : list Z) (i : CPU) (bb : bool) :
    wm_tid mrel = Some (fin_to_nat i) -> wm_ak mrel = WCrel ->
    wlat_interp img (log ++ [mrel]) -∗
    wprot_win γ base n0 F (Some (i, bb)) ==∗
    wlat_interp img (log ++ [mrel]) ∗ wprot_win γ base n0 F None.
  Proof.
    intros Htid Hk. induction F as [|a F IH]; iIntros "Hi HF".
    - iModIntro. by iFrame.
    - rewrite /wprot_win /=. iDestruct "HF" as "[Ha HF]".
      iDestruct "Ha" as (d) "[Hpr %Hd]".
      iMod (IH with "Hi HF") as "[Hi Htl]".
      iAssert (|==> wlat_interp img (log ++ [mrel]) ∗
                    wprot_st a γ base n0 n0 None)%I with "[Hi Hpr]" as ">[Hi Hpr]".
      { destruct d as [c|]; last first.
        { iModIntro. iFrame "Hi Hpr". }
        destruct Hd as (b0 & [= <- _]).
        iMod (wprot_flip img log mrel i a γ base n0 n0 Htid Hk with "Hi Hpr")
          as "[Hi Hpr]". iModIntro. iFrame "Hi Hpr". }
      iModIntro. iFrame "Hi Htl". iExists None. iFrame "Hpr".
  Qed.

  Lemma wpacquire_core (γ γr : gname) (lk : Arch.pa) R (n0 : nat)
      (F : list Z) (i : CPU) (tid : option nat) (σ σ' : wmstate) :
    wlog_wf (wm_log σ) -> acc_wf lk 4 -> wQ_amo_aq tid lk lock_one σ σ' ->
    tid = Some (fin_to_nat i) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wplock_body γ γr lk R n0 F -∗
    ∃ v : bv 32,
      ⌜forall j : nat, (j < 4)%nat ->
         wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte v j)⌝ ∗
      (|==> wlat_interp (wm_img σ') (wm_log σ') ∗
            wplock_body γ γr lk R n0 F ∗
            ((⌜v = lock_zero⌝ ∗ vwp_hold R (wm_ws σ') ∗ locked γ i)
             ∨ ⌜v ≠ lock_zero⌝)).
  Proof.
    intros Hwf Hacc Heff Htid.
    destruct Heff as ((Himg & (kc & Hlog & _) & Hle & Hflr) & Hgain & Hexcl).
    iIntros "Hi Hbody".
    iDestruct "Hbody" as (st t v L) "(Hw & Ha & Hwin & Hrec & %Hok & Harm)".
    iDestruct (wlat4_lock_flat_gen σ lk n0 t v (tid_of st) Hwf Hacc
                 with "Hi Hw") as %[Hflat Hts].
    iExists v. iSplitR; [by iPureIntro|].
    iDestruct "Harm" as "[(-> & -> & Hfrag & HR)|(%Hst & %Hv)]".
    - (* FREE: a successful acquire, and the window widens for free *)
      iMod (wlat4_lock_store_gen tid WCexcl σ σ' lk n0 t lock_zero lock_one
              None (Some (fin_to_nat i))
              (wlock_shaped_acq tid lk lock_one)
              ltac:(rewrite Htid; apply alt_step_acq_msg) Himg Hexcl
              with "Hi Hw") as "[Hi Hw]".
      iMod (lock_take γ i with "Ha Hfrag") as "[Ha Hpre]".
      iMod (lock_setcpu γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Htok)".
      iDestruct (wprot_win_free γ (pa_z lk) n0 F (Some (i, true))
                   with "Hwin") as "Hwin".
      iModIntro. iFrame "Hi". iSplitR "HR Htok".
      + iExists (Some (i, true)), (S (length (wm_log σ))), lock_one, L.
        iFrame "Hw Ha Hwin Hrec". iSplitR; [by iPureIntro|].
        iRight. iSplitR; [done|]. iPureIntro. apply lock_one_ne_zero.
      + iLeft. iSplitR; [done|]. iFrame "Htok".
        rewrite /vwp_hold.
        iApply (monPred_mono R (view_scl t) (ws_view (wm_ws σ'))).
        { rewrite -(Hts 0%nat ltac:(lia)). apply Hgain. lia. }
        iExact "HR".
    - (* HELD: a failed swap; nothing about the footprint moves *)
      destruct st as [[j b]|]; [|by destruct Hst].
      iMod (wlat4_lock_store_gen tid WCexcl σ σ' lk n0 t v lock_one
              (Some (fin_to_nat j)) (Some (fin_to_nat j))
              (wlock_shaped_acq tid lk lock_one)
              (alt_step_fail_msg tid lk (fin_to_nat j)) Himg Hexcl
              with "Hi Hw") as "[Hi Hw]".
      iModIntro. iFrame "Hi". iSplitR "".
      + iExists (Some (j, b)), (S (length (wm_log σ))), lock_one, L.
        iFrame "Hw Ha Hwin Hrec". iSplitR; [by iPureIntro|].
        iRight. iSplitR; [done|]. iPureIntro. apply lock_one_ne_zero.
      + iRight. by iPureIntro.
  Qed.

  Lemma wprelease_core (γ γr : gname) (lk : Arch.pa) R (n0 : nat)
      (F : list Z) (i : CPU) (tid : option nat) (σ σ' : wmstate) :
    wQ_store tid lk lock_zero σ σ' ->
    tid = Some (fin_to_nat i) ->
    (* the release's message is RELEASE-CLASS, not merely non-plain: it is
       what publishes the footprint's owned backlog.  Pinned exactly as
       [wQ_amo_aq_w] pins [WCexcl] for the acquire's write half; every xv6
       release site has it (a plain [sw] — [ak_latest] false — under the
       [fence rw,w]'s [w_relp], so [WeakInterp.wm_class_of] computes
       [WCrel]). *)
    wm_log σ' = (wm_log σ ++ [wwrite_msg tid WCrel lk 4 lock_zero])%list ->
    ws_bounded (wm_ws σ) (length (wm_log σ)) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wplock_body γ γr lk R n0 F -∗
    locked γ i -∗
    vwp_hold R (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wplock_body γ γr lk R n0 F.
  Proof.
    intros (Himg & _ & Hle & Hflr) Htid Hrel Hbnd.
    iIntros "Hi Hbody Htok HR".
    iDestruct "Hbody" as (st t v L) "(Hw & Ha & Hwin & Hrec & %Hok & _)".
    iDestruct (locked_state with "Ha Htok") as %->.
    iAssert (monPred_at R (view_scl (S (length (wm_log σ)))))%I
      with "[HR]" as "HR".
    { by iApply (wwp_release_deposit R σ Hbnd with "HR"). }
    iMod (wlat4_lock_store_gen tid WCrel σ σ' lk n0 t v lock_zero
            (Some (fin_to_nat i)) None
            (wlock_shaped_rel tid WCrel lk ltac:(discriminate))
            ltac:(rewrite Htid; apply alt_step_rel_msg) Himg Hrel
            with "Hi Hw") as "[Hi Hw]".
    iMod (lock_clrcpu γ (Some (i, true)) i with "Ha Htok") as "(_ & Ha & Hpre)".
    iMod (lock_give γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Hfrag)".
    (* THE FOOTPRINT FLIP: the release message is the log's last and is
       [WCrel], so every payload byte's owned backlog is published *)
    rewrite Himg Hrel.
    iMod (wprot_win_flip (wm_img σ) (wm_log σ)
            (wwrite_msg tid WCrel lk 4 lock_zero) γ (pa_z lk) n0 F i true
            ltac:(by rewrite Htid) ltac:(reflexivity) with "Hi Hwin")
      as "[Hi Hwin]".
    iModIntro. iFrame "Hi".
    iExists None, (S (length (wm_log σ))), lock_zero, L.
    iFrame "Hw Ha Hwin Hrec". iSplitR; [by iPureIntro|].
    iLeft. iSplitR; [done|]. iSplitR; [done|]. iFrame "Hfrag HR".
  Qed.

End weak_lock.

(* ======================================================================
   WHY [wstep_cert]'s [Q] IS OVER THE SUCCESSOR *STATE* (M3b's finding, fixed
   at M3c).

     THE INVARIANT OWNS THE LOCK WORD'S LATEST-WRITE ELEMENTS, AND ANY STEP
     THAT WRITES THOSE BYTES INVALIDATES THEM.  Re-establishing
     [wmstate_interp σ'] after a store therefore requires RETARGETING the
     elements at the message the step appended — so the certificate must say
     WHICH message that was ([wQ_store]'s second conjunct,
     [wm_log σ' = wm_log σ ++ [wwrite_msg tid ea 4 v]]), and that is a
     statement about [wm_log σ'], which a [wstate] cannot express.

   [WeakInstr.wstep_post] does not close the gap either: it says only
   [∃ l, wm_log σ' = wm_log σ ++ l].  A store leaf built on a [Q] over views
   alone is therefore unprovable — not because of any weak-memory subtlety,
   but because the ghost map of latest writes cannot be updated blind.  Hence
   [Q : wmstate -> wmstate -> Prop], with the view-level content factored out
   as [WeakInstr.wV_store] / [wV_amo_aq] / [wV_fence] / [wV_load]. *)
