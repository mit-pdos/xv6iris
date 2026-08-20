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
  Definition wlock_inv (γ : gname) (lk : Arch.pa) (R : vProp Σ) : iProp Σ :=
    (∃ (st : lock_state) (t : nat) (v : bv 32),
       wlat4L lk t v ∗ lock_auth γ st ∗
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
    { iNext. iExists None, t, lock_zero. iFrame "Hw Ha".
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
    iExists n0.
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
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk R -∗
    ∃ v : bv 32,
      ⌜∀ j : nat, (j < 4)%nat →
         wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte v j)⌝ ∗
      (|==> wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ lk R ∗
            ((⌜v = lock_zero⌝ ∗ vwp_hold R (wm_ws σ') ∗ locked γ i)
             ∨ ⌜v ≠ lock_zero⌝)).
  Proof.
    intros Hwf Hacc Heff.
    destruct Heff as ((Himg & (kc & Hlog & _) & Hle & Hflr) & Hgain & Hexcl).
    iIntros "Hi Hinv".
    iDestruct "Hinv" as (st t v) "(Hw & Ha & Harm)".
    iDestruct (wlat4L_flat_gen σ lk t v Hwf Hacc with "Hi Hw")
      as %[Hflat Hts].
    iExists v. iSplitR; [by iPureIntro|].
    (* the machine's own write: the elements move to the fresh top, value 1.
       T2-0: it goes through the PROTOCOL store — the message is [WCexcl]
       (pinned by [wQ_amo_aq]), which is the acquire arm of
       [WeakGhost.wlock_shaped]. *)
    iMod (wlat4L_store_gen tid WCexcl σ σ' lk t v lock_one
            (wlock_shaped_acq tid lk lock_one) Himg Hexcl with "Hi Hw")
      as "[Hi Hw]".
    iDestruct "Harm" as "[(-> & -> & Hfrag & HR)|(%Hst & %Hv)]".
    - (* the lock was FREE: take it, and thaw the payload *)
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
    - (* the lock was HELD: the swap returns a nonzero word; nothing moves but
         the timestamp *)
      iModIntro. iFrame "Hi". iSplitR "".
      + iExists st, (S (length (wm_log σ))), lock_one.
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
    intros (Himg & (kc & Hlog & Hnp) & Hle & Hflr) Hrelp Hbnd.
    specialize (Hnp Hrelp).
    iIntros "Hi Hinv Htok HR".
    iDestruct "Hinv" as (st t v) "(Hw & Ha & _)".
    (* the holder's token says the lock is held by [i] *)
    iDestruct (locked_state with "Ha Htok") as %->.
    (* THE DEPOSIT: everything the releaser holds is below the store's own
       timestamp, so it may be frozen there and handed to the invariant *)
    iAssert (monPred_at R (view_scl (S (length (wm_log σ)))))%I with "[HR]" as "HR".
    { by iApply (wwp_release_deposit R σ Hbnd with "HR"). }
    (* T2-0: the release arm of [WeakGhost.wlock_shaped] — the message writes
       the ZERO word and is at least release-class (the [w_relp] flag the
       preceding [fence rw,w] set is what rules out [WCplain]). *)
    iMod (wlat4L_store_gen tid kc σ σ' lk t v lock_zero
            (wlock_shaped_rel tid kc lk Hnp) Himg Hlog
            with "Hi Hw") as "[Hi Hw]".
    iMod (lock_clrcpu γ (Some (i, true)) i with "Ha Htok") as "(_ & Ha & Hpre)".
    iMod (lock_give γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Hfrag)".
    iModIntro. iFrame "Hi".
    iExists None, (S (length (wm_log σ))), lock_zero.
    iFrame "Hw Ha". iLeft. iSplitR; [done|]. iSplitR; [done|]. iFrame "Hfrag HR".
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
