(** * WeakRvwmoKillArms.v — B2e-3c, THE SEGMENT-COMPOSITION KILL

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.2(3) (the three
    arms and the NOTE on when the window order is row data) and §4d.3′ (what
    F3′/F3″ export).

    THE SETTING.  A graph [G] ([rvwmo_minus_consistent]) together with a LOG
    [log] that is the gmo-ordered message list of a PREFIX of [G]'s writes —
    what a certified configuration's log is in the device-quiet milestone.
    §1 is the DICTIONARY between the two vocabularies: log position [p] is
    graph write index [S p] ([log_of]; the same convention as
    [WeakRvwmoFloor]'s [gtp_log] / [gtp_log_writes], which state it as
    "[cd_log c … !! (s - 1)] is the message of [gwrite_at G s]").

    THE KILL.  An [R]-cycle is presented as a list of SEGMENTS (hart, entry
    event, exit write) with a cross-hart edge (rf / co / fr — [Racy]'s
    cross-hart arms) from each segment's predecessor's exit to its entry, and
    a per-segment CERTIFICATE of one of three kinds (§2):

      - [Pinned]     — [gmo_lt G entry exit] outright (ppo rule 5, rule 4, or
                       [gd_deps]); composed with the cross edge it gives
                       [gmo_lt G prev_exit exit];
      - [CSchained]  — [gmo_lt G prev_exit exit] derived THROUGH the lock
                       window (§4: [cs_chained]);
      - [Bad]        — the entry reads an owned-unpublished message; φ refutes
                       the certifying configuration, so the arm is the
                       hypothesis [False] (out of this file's scope).

    [cycle_kill_arms] chains the resulting [gmo_lt] steps around the cycle and
    closes on [gmo_lt_irrefl].

    §4 IS THE ARITHMETIC THE DESIGN NOTE CALLS FOR, and BOTH window orders
    close:

      - WRITER-FIRST (the handoff).  The writer's acquire [ACQ_w] sits at log
        position [q]; the reader's acquire [ACQ] at [pA].  With [q < pA],
        [wlp_alt_two_acq] puts a release BY THE WRITER between them, and
        [wprot_at]'s own "no release between [q] and the write" clause forces
        that release ABOVE the write — so [gwix w < gwix ACQ], and ppo rule 5
        carries [ACQ] to the exit.
      - READER-FIRST is REFUTED, not handled: with [pA < q], the same lemma
        puts a release BY THE READER between [pA] and [q], and [lock_cs]'s
        no-write-in-between clause identifies it at or above the reader's own
        release [REL].  Then [REL <co ACQ_w <co w], while [w <gmo entry]
        (the cross edge) and [entry <gmo REL] (ppo rule 4, the release
        fence) — a three-step gmo cycle.

    So [cs_chained] needs [wlp_alt_two_acq] only; [wlp_alt_open] is not
    required, because the reader-first case is killed through the ROW's own
    release rather than through the fold's open-section shape.

    THE ONE BRIDGE THAT IS A HYPOTHESIS, AND WHY.  F3′'s fold tests the WORD
    ([wm_data m = wlock_zero4], four zero bytes) while the graph-side kit
    ([WeakRvwmoLock]) tests ONE BYTE ([lock_free]).  Byte-zero does not
    follow from word-zero's negation, so [lock_word_byte] — "a message whose
    byte [b] is zero has the whole word zero" — is carried explicitly.  It is
    true at [b = base] for xv6's lock word (the release stores the zero word;
    the acquire swaps in 1, whose low byte is 1) and it is DISCHARGED on the
    witness of §5.  The reverse direction is free ([zero4_byte]).

    §5 — NON-VACUITY.  Two witnesses.
    (a) [lkw], a two-hart acquire/release graph with a 4-BYTE lock word, on
        which every hypothesis of [cs_chained] is discharged and the
        conclusion [gmo_lt lkw w exit] is derived by it.  A FINDING recorded
        by this instantiation: [WeakRvwmoLockWit.lkg] CANNOT serve here —
        its lock stores are ONE byte wide, and F3′'s [alt_step] rejects
        every non-[WCexcl] message whose data is not literally the four-byte
        zero word, so [lkg]'s [WCrel] release makes the fold [None] and
        [wlp_alt] is unsatisfiable on its log.  [lkw] is [lkg] widened to
        4 bytes with the CS bodies swapped (hart 0 writes the payload, hart 1
        reads it), which is the orientation the CS arm needs.
    (b) [lbg] (the LB witness): its [Racy] cycle IS a two-segment cycle in
        this file's shape, and [cycle_kill_arms] fires on it AS SOON AS both
        [Pinned] certificates are supplied — while both are in fact FALSE in
        [lbg] ([lbg_pinned_absent]), which is exactly why LB survives.  The
        pair shows the conclusion shape is not vacuous and that the kill is
        certificate-driven.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic WeakGhost
     WeakRvwmoGraph WeakRvwmoXchg WeakRvwmoAcyc WeakRvwmoLock.

(* ====================================================================== *)
(** * 1. THE LOG DICTIONARY

    [gmsg] is [WeakRvwmoFloor.gwmsg] restated here (this file does not import
    the floor); [log_of] is the index convention of [gtp_log], read as an
    equivalence: LOG POSITION [p] IS GRAPH WRITE INDEX [S p]. *)

Definition gmsg (G : gexec) (w : geid) : option wmsg :=
  match gx_lbl G w with
  | Some l =>
      match lb_wr l with
      | Some (base, vs) => Some (WMsg base vs (Some w.1) (lb_cls l))
      | None => None
      end
  | None => None
  end.

(** The log is the message list of a gmo-PREFIX of [G]'s writes. *)
Definition log_of (G : gexec) (log : list wmsg) : Prop :=
  ∀ p m, log !! p = Some m ↔
         (∃ w, gwrite_at G (S p) = Some w ∧ gmsg G w = Some m).

(** The class a graph event's write half publishes. *)
Definition gcls (G : gexec) (w : geid) (k : wm_class) : Prop :=
  ∃ l, gx_lbl G w = Some l ∧ lb_cls l = k.

Lemma gmsg_is_Some G w : gis_w G w = true → is_Some (gmsg G w).
Proof.
  rewrite /gis_w /gmsg. destruct (gx_lbl G w) as [l|]; [|done].
  intros Hw. destruct (lb_is_w_wr l Hw) as (base & vs & ->). by eexists.
Qed.

Lemma gmsg_tid G w m : gmsg G w = Some m → wm_tid m = Some w.1.
Proof.
  rewrite /gmsg. destruct (gx_lbl G w) as [l|]; [|done].
  destruct (lb_wr l) as [[base vs]|]; [|done]. by intros [= <-].
Qed.

Lemma gmsg_cls G w m k : gcls G w k → gmsg G w = Some m → wm_ak m = k.
Proof.
  intros (l & Hl & <-). rewrite /gmsg Hl.
  destruct (lb_wr l) as [[base vs]|]; [|done]. by intros [= <-].
Qed.

(** THE BYTE DICTIONARY: [msg_byte] of the message IS [gwrites_byte] of the
    event.  ([acc_addr base j = base + j] and [msg_byte]'s offset are the
    same arithmetic, read in the two directions.) *)
Lemma gmsg_byte G w m a v :
  gmsg G w = Some m → (msg_byte m a = Some v ↔ gwrites_byte G w a v).
Proof.
  rewrite /gmsg. destruct (gx_lbl G w) as [l|] eqn:Hl; [|done].
  destruct (lb_wr l) as [[base vs]|] eqn:Hwr; [|done]. intros [= <-]. split.
  - rewrite /msg_byte /=. case_bool_decide as Hle; [|done]. intros Hv.
    exists l, base, vs, (Z.to_nat (a - base)). split_and!;
      [done|done|done|]. rewrite /acc_addr Z2Nat.id; lia.
  - intros (l' & base' & vs' & j & Hl' & Hwr' & Hv & Ha).
    rewrite Hl in Hl'. injection Hl' as <-. rewrite Hwr in Hwr'.
    injection Hwr' as <- <-. rewrite /acc_addr in Ha.
    assert (Hle : (base <= a)%Z) by lia.
    assert (Hj : Z.to_nat (a - base) = j) by lia.
    rewrite /msg_byte /= (bool_decide_eq_true_2 _ Hle) Hj. exact Hv.
Qed.

(** … and its negative half, the shape the "this write does not touch the
    lock word" side condition is stated in. *)
Lemma gmsg_byte_None G w m a :
  gmsg G w = Some m → (∀ v, ¬ gwrites_byte G w a v) → msg_byte m a = None.
Proof.
  intros Hm Hno. destruct (msg_byte m a) as [v|] eqn:Hb; [|done].
  exfalso. apply (Hno v). by apply (gmsg_byte G w m a v Hm).
Qed.

(** LOG → GRAPH. *)
Lemma log_of_lookup G log p m :
  gwf G → log_of G log → log !! p = Some m →
  ∃ w, gwrite_at G (S p) = Some w ∧ gmsg G w = Some m ∧ gwix G w = S p ∧
       w ∈ gwrites G.
Proof.
  intros Hwf Hlog Hp. pose proof Hwf as (Hnd & _ & _).
  destruct (proj1 (Hlog p m) Hp) as (w & Hw & Hm).
  rewrite /gwrite_at in Hw.
  exists w. split_and!; [exact Hw|exact Hm| |].
  - by apply gwix_of_lookup.
  - by eapply gwrites_lookup_elem.
Qed.

(** GRAPH → LOG. *)
Lemma log_of_write G log w :
  gwf G → log_of G log → w ∈ gwrites G → (gwix G w ≤ length log)%nat →
  ∃ m, log !! (gwix G w - 1)%nat = Some m ∧ gmsg G w = Some m.
Proof.
  intros Hwf Hlog Hw Hle. pose proof Hwf as (Hnd & _ & _).
  destruct (gwix_lookup G w Hw) as (i & Hi & Hix).
  rewrite Hix. replace (S i - 1)%nat with i by lia.
  assert (Hlt : (i < length log)%nat) by lia.
  destruct (lookup_lt_is_Some_2 log i Hlt) as [m Hm].
  destruct (proj1 (Hlog i m) Hm) as (w' & Hw' & Hm').
  rewrite /gwrite_at Hi in Hw'. injection Hw' as <-. by exists m.
Qed.

(* ====================================================================== *)
(** * 2. SEGMENTS, CERTIFICATES, AND THE COMPOSITION KILL

    [Racy]'s CROSS-HART arms — rf, co, fr — are the edges that join one
    segment's exit write to the next segment's entry.  All three are
    gmo-forward from [rvwmo_minus_consistent] ALONE (unlike [gpow], which
    needs rule 14), and that matters: the graph this kill runs on is
    precisely one that need NOT satisfy rule 14. *)

Definition gcross (G : gexec) (x y : geid) : Prop :=
  grf G x y ∨ gco G x y ∨ gfr G x y.

Lemma gcross_gmo G x y :
  rvwmo_minus_consistent G → gcross G x y → gmo_lt G x y.
Proof.
  intros Hcons [H|[H|H]].
  - by eapply grf_gmo.
  - by eapply gco_gmo; [apply Hcons|].
  - by eapply gfr_gmo.
Qed.

Lemma gcross_Racy G x y : gcross G x y → Racy G x y.
Proof.
  intros [H|[H|H]];
    [by right;left|by right;right;left|by right;right;right;left].
Qed.

(** ONE SEGMENT of the cycle: a hart, the event the cross edge lands on, and
    the write the next cross edge leaves from.  ([sg_hart] is carried because
    the design states the segment that way — every event of a segment belongs
    to it — but the arithmetic below never reads it: the certificates already
    pin the only order facts the composition needs.) *)
Record seg := Seg { sg_hart : agent; sg_entry : geid; sg_exit : geid }.

(** THE THREE ARMS, as one certificate relating the PREDECESSOR's exit to
    this segment's exit. *)
Inductive cert (G : gexec) (prev : geid) (s : seg) : Prop :=
| Pinned      : gcross G prev (sg_entry s) →
                gmo_lt G (sg_entry s) (sg_exit s) → cert G prev s
| CSchained   : gmo_lt G prev (sg_exit s) → cert G prev s
| Bad         : False → cert G prev s.

Lemma cert_gmo G prev s :
  rvwmo_minus_consistent G → cert G prev s → gmo_lt G prev (sg_exit s).
Proof.
  intros Hcons [Hx Hp|Hcs|[]].
  - eapply gmo_lt_trans; [by eapply gcross_gmo|exact Hp].
  - exact Hcs.
Qed.

(** A CHAIN of certified segments, from [x] to [y]. *)
Fixpoint chain (G : gexec) (x y : geid) (ss : list seg) : Prop :=
  match ss with
  | [] => x = y
  | s :: ss' => cert G x s ∧ chain G (sg_exit s) y ss'
  end.

Lemma chain_gmo G x y ss :
  rvwmo_minus_consistent G → ss ≠ [] → chain G x y ss → gmo_lt G x y.
Proof.
  intros Hcons. revert x. induction ss as [|s ss IH]; intros x Hne; [done|].
  intros [Hc Hch]. destruct ss as [|s' ss].
  - simpl in Hch. subst y. by eapply cert_gmo.
  - eapply gmo_lt_trans; [by eapply cert_gmo|].
    apply (IH (sg_exit s) ltac:(done) Hch).
Qed.

(** THE THEOREM: a CYCLE of certified segments is inconsistent. *)
Theorem cycle_kill_arms G x ss :
  rvwmo_minus_consistent G → ss ≠ [] → chain G x x ss → False.
Proof. intros Hcons Hne Hch. by eapply gmo_lt_irrefl, chain_gmo. Qed.

(* ====================================================================== *)
(** * 3. THE TRANSLATION LEMMAS

    F3′'s fold and F3″'s protection clause speak of MESSAGES and LOG
    POSITIONS; [WeakRvwmoLock]'s kit speaks of EVENTS and WRITE INDICES.
    §1's dictionary moves between them; what is left is the one genuine
    mismatch — the fold tests the WORD, the kit tests the BYTE. *)

(** THE BRIDGE, as a hypothesis: byte [b] WITNESSES the lock word — a
    message whose [b] byte is [lock_free] has the whole word zero.  True at
    [b = base] for xv6's lock word (release stores the zero word, acquire
    swaps in 1); discharged on §5's witness. *)
Definition lock_word_byte (log : list wmsg) (b : Z) : Prop :=
  ∀ p m v, log !! p = Some m → msg_byte m b = Some v → v = lock_free →
    wm_data m = wlock_zero4.

(** The converse direction is FREE. *)
Lemma zero4_byte m b v :
  wm_data m = wlock_zero4 → msg_byte m b = Some v → v = lock_free.
Proof.
  intros Hd Hb. rewrite /msg_byte Hd in Hb.
  case_bool_decide as Hle; [|done].
  rewrite /wlock_zero4 in Hb.
  by destruct (proj1 (lookup_replicate _ _ _ _) Hb) as [-> _].
Qed.

(** A zero-word message on the lock byte IS a graph RELEASE. *)
Lemma log_rel_graph G log b p m :
  gwf G → log_of G log → log !! p = Some m →
  is_Some (msg_byte m b) → wm_data m = wlock_zero4 →
  ∃ R, gwrite_at G (S p) = Some R ∧ lock_rel G b R ∧ gwix G R = S p ∧
       R ∈ gwrites G ∧ wm_tid m = Some R.1.
Proof.
  intros Hwf Hlog Hp [v Hb] Hz.
  destruct (log_of_lookup G log p m Hwf Hlog Hp) as (R & Hat & Hm & Hix & Hw).
  exists R. split_and!; [done| |done|done|by eapply gmsg_tid].
  rewrite /lock_rel -(zero4_byte m b v Hz Hb).
  by apply (gmsg_byte G R m b v).
Qed.

(** A nonzero message on the lock byte IS a graph ACQUIRE (the value pattern
    is what turns "not the zero word" into "not the free byte"). *)
Lemma log_acq_graph G log b p m :
  gwf G → log_of G log → lock_word_byte log b →
  log !! p = Some m → is_Some (msg_byte m b) → wm_data m ≠ wlock_zero4 →
  ∃ A, gwrite_at G (S p) = Some A ∧ lock_acq G b A ∧ gwix G A = S p ∧
       A ∈ gwrites G ∧ wm_tid m = Some A.1.
Proof.
  intros Hwf Hlog Hlwb Hp [v Hb] Hnz.
  destruct (log_of_lookup G log p m Hwf Hlog Hp) as (A & Hat & Hm & Hix & Hw).
  exists A. split_and!; [done| |done|done|by eapply gmsg_tid].
  exists v. split; [by apply (gmsg_byte G A m b v)|].
  intros ->. apply Hnz. by eapply (Hlwb p m lock_free).
Qed.

(** [holder_acq_graph] — F3″'s export, translated.  A plain write of a
    protected byte sits inside its author's critical section; the fold names
    that section's ACQUIRE, and this lemma hands it back BOTH as a log
    position (which is all the arithmetic of §4 uses) AND as a graph
    [lock_acq] event at write index [S q]. *)
Lemma holder_acq_graph G log b a n0 r0 (w : geid) :
  gwf G → log_of G log → lock_word_byte log b →
  wprot_at log a b n0 r0 →
  w ∈ gwrites G → (r0 < gwix G w)%nat → (gwix G w ≤ length log)%nat →
  (∃ v, gwrites_byte G w a v) → gcls G w WCplain →
  ∃ q mq, (n0 ≤ q < gwix G w - 1)%nat ∧ log !! q = Some mq ∧
    is_Some (msg_byte mq b) ∧ wm_data mq ≠ wlock_zero4 ∧
    wm_tid mq = Some w.1 ∧ wlp_holder_at log b n0 q = Some None ∧
    (∀ r mr, (q < r < gwix G w - 1)%nat → log !! r = Some mr →
       is_Some (msg_byte mr b) → wm_data mr ≠ wlock_zero4) ∧
    (∃ ACQw, gwrite_at G (S q) = Some ACQw ∧ lock_acq G b ACQw ∧
             gwix G ACQw = S q ∧ ACQw.1 = w.1).
Proof.
  intros Hwf Hlog Hlwb Hpr Hw Hr0 Hle (v & Hwb) Hcl.
  destruct (log_of_write G log w Hwf Hlog Hw Hle) as (mw & Hmw & Hgw).
  assert (Hbyte : is_Some (msg_byte mw a))
    by (exists v; by apply (gmsg_byte G w mw a v)).
  assert (Hak : wm_ak mw = WCplain) by (by eapply gmsg_cls).
  assert (Htid : wm_tid mw = Some w.1) by (by eapply gmsg_tid).
  destruct (wprot_writer_cs log a b n0 r0 (gwix G w - 1)%nat mw w.1
              Hpr Hmw ltac:(lia) Hbyte Hak Htid)
    as (q & mq & Hq & Hlk & Hs & Hnz & Ht & Hfree & Hno).
  destruct (log_acq_graph G log b q mq Hwf Hlog Hlwb Hlk Hs Hnz)
    as (ACQw & Hat & Hacq & Hix & _ & Htq).
  exists q, mq. split_and!; [lia|lia|done|done|done|done|done|done|].
  exists ACQw. split_and!; [done|done|done|].
  rewrite Ht in Htq. by injection Htq as <-.
Qed.

(** [release_between_graph] — F3′'s [wlp_alt_two_acq], translated: between a
    successful acquire and a later FREE point sits its own author's RELEASE,
    named as a graph event with its write index. *)
Lemma release_between_graph G log b n0 p q mp (i : agent) :
  gwf G → log_of G log →
  (n0 ≤ p)%nat → (p < q)%nat → log !! p = Some mp →
  is_Some (msg_byte mp b) → wm_data mp ≠ wlock_zero4 → wm_tid mp = Some i →
  wlp_holder_at log b n0 p = Some None →
  wlp_holder_at log b n0 q = Some None →
  ∃ r R mr, (p < r < q)%nat ∧ log !! r = Some mr ∧
            is_Some (msg_byte mr b) ∧ wm_data mr = wlock_zero4 ∧
            gwrite_at G (S r) = Some R ∧ lock_rel G b R ∧
            gwix G R = S r ∧ R ∈ gwrites G ∧ R.1 = i.
Proof.
  intros Hwf Hlog Hn0 Hpq Hp Hs Hnz Hti Hfp Hfq.
  destruct (wlp_alt_two_acq log b n0 p q mp i Hn0 Hpq Hp Hs Hnz Hti Hfp Hfq)
    as (r & mr & Hr & Hlk & Hsr & Hzr & Htr).
  destruct (log_rel_graph G log b r mr Hwf Hlog Hlk Hsr Hzr)
    as (R & Hat & Hrel & Hix & Hw & Htid).
  exists r, R, mr. split_and!;
    [lia|lia|done|done|done|done|done|done|done|].
  rewrite Htr in Htid. by injection Htid as <-.
Qed.

(** THE FOLD IS FREE AT AN ACQUIRE.  F3′'s locality fact (i), read off the
    ROW: the acquire's read entry at [b] names a zero value, so its co-
    predecessor (atomicity + load-value, [WeakRvwmoLock] §2) is a release
    sitting immediately below it — and the fold, which sees exactly the
    [b]-writing messages, is therefore FREE just before it. *)
Lemma acq_fold_free G log b n0 h ACQ :
  rvwmo_minus_consistent G → log_of G log → lock_word_byte log b →
  wlp_alt log b n0 h → lock_pattern G b → lock_acq G b ACQ →
  (gwix G ACQ ≤ length log)%nat →
  wlp_holder_at log b n0 (gwix G ACQ - 1)%nat = Some None.
Proof.
  intros Hcons Hlog Hlwb Halt Hpat Hacq Hle.
  pose proof Hcons as (Hwf & _ & _ & _).
  pose proof (lock_acq_gwrites G b ACQ Hwf Hacq) as HAw.
  pose proof (gwix_pos G ACQ HAw) as Hpos.
  destruct (lock_acq_read G b ACQ Hpat Hacq) as [_ (t & Hrd)].
  pose proof (acq_ts_lt G b ACQ t Hcons Hacq Hrd) as Htlt.
  assert (Hquiet : ∀ r mr, (t ≤ r < gwix G ACQ - 1)%nat → log !! r = Some mr →
                    msg_byte mr b = None).
  { intros r mr Hr Hmr. destruct (msg_byte mr b) as [v|] eqn:Hb; [|done].
    exfalso.
    destruct (log_of_lookup G log r mr Hwf Hlog Hmr)
      as (w' & _ & Hm' & Hix' & _).
    assert (Hwb : gwrites_byte G w' b v) by (by apply (gmsg_byte G w' mr b v)).
    destruct (acq_src G b ACQ t Hcons Hacq Hrd w' v Hwb) as [Hlo|Hhi].
    - rewrite Hix' in Hlo. lia.
    - rewrite Hix' in Hhi. lia. }
  rewrite (wlp_holder_quiet log b n0 t (gwix G ACQ - 1)%nat
             ltac:(lia) Hquiet).
  destruct (decide (t ≤ n0)%nat) as [Hn0|Hn0]; [by apply wlp_holder_small|].
  destruct (acq_src_rel G b ACQ t Hcons Hrd ltac:(lia)) as (R & HR & HRw & HRix).
  destruct (log_of_write G log R Hwf Hlog HRw ltac:(lia)) as (m & Hm & Hgm).
  rewrite HRix in Hm.
  assert (Hbz : msg_byte m b = Some lock_free)
    by (by apply (gmsg_byte G R m b lock_free)).
  assert (Hzero : wm_data m = wlock_zero4)
    by (by eapply (Hlwb (t - 1)%nat m lock_free)).
  destruct Halt as [Hlen Hf].
  destruct (wlp_holder_is_Some log b n0 t (length log) h ltac:(lia) Hf)
    as [h2 Ht2].
  destruct (wlp_holder_is_Some log b n0 (t - 1)%nat (length log) h
              ltac:(lia) Hf) as [h1 Ht1].
  rewrite Ht2. f_equal.
  assert (Hstep : wlp_holder_at log b n0 (S (t - 1)) =
            (if mwrites b m then alt_step h1 m else Some h1)).
  { by rewrite (wlp_holder_step log b n0 (t-1)%nat m ltac:(lia) Hm) Ht1. }
  replace (S (t - 1))%nat with t in Hstep by lia.
  rewrite Ht2 (proj2 (mwrites_true b m) ltac:(by exists lock_free)) in Hstep.
  by destruct (alt_step_zero h1 m h2 Hzero (eq_sym Hstep)) as (-> & _ & _).
Qed.

(* ====================================================================== *)
(** * 4. THE CS-CHAINED ARM

    The segment's entry is a read inside its hart's critical section of the
    lock byte [b]; the PREVIOUS segment's exit [w] is a plain write of a byte
    [a] that [b] protects.  §4d.2(3)'s NOTE: the window order is ROW DATA
    when both sections are under the same lock — and here it is LOG data, of
    exactly the same kind, read off F3′'s fold.

    Both window orders are handled, and only one of them is a derivation:

      WRITER-FIRST  ([ACQ_w] below [ACQ] in the log): [wlp_alt_two_acq] puts
                    the writer's own release between them, [wprot_at]'s
                    no-release clause puts that release ABOVE [w], hence
                    [w <co ACQ], and ppo rule 5 gives [ACQ <gmo exit].
      READER-FIRST  ([ACQ] below [ACQ_w]): [wlp_alt_two_acq] puts the
                    READER's release between them; [lock_cs]'s
                    no-[b]-write-in-between clause identifies it at or above
                    [REL]; so [REL <co ACQ_w <co w], while the cross edge
                    gives [w <gmo entry] and ppo rule 4 (the release fence)
                    gives [entry <gmo REL] — a gmo cycle.  REFUTED.

    The two acquires cannot be the SAME event: their authors differ
    ([ACQ.1 ≠ w.1], the cross-hart premise [WeakRvwmoLock.cs_kill] also
    carries). *)

Theorem cs_chained (G : gexec) (log : list wmsg) (b a : Z) (n0 r0 : nat)
    (h : option nat) (w entry exit ACQ REL : geid) :
  rvwmo_minus_consistent G →
  (* the log, the fold, and the byte/word bridge *)
  log_of G log → lock_word_byte log b → wlp_alt log b n0 h →
  (* the graph-side value protocol on the lock byte *)
  lock_pattern G b →
  (* F3″ at the protected byte *)
  wprot_at log a b n0 r0 →
  (* the PREVIOUS EXIT [w]: an owned plain write of the protected byte,
     inside the log, not touching the lock word *)
  (∃ v, gwrites_byte G w a v) → gcls G w WCplain →
  (r0 < gwix G w)%nat → (gwix G w ≤ length log)%nat →
  (∀ v, ¬ gwrites_byte G w b v) →
  (* the READER's row: its acquire, its section, and the release fence *)
  lock_acq G b ACQ → glbl_is G ACQ lb_aq →
  (n0 < gwix G ACQ)%nat → (gwix G ACQ ≤ length log)%nat →
  lock_cs G b ACQ REL → gpo G ACQ entry → gfence_covers G entry REL →
  (* the cross-hart edge into the entry, and the segment's exit *)
  gcross G w entry → gpo G ACQ exit → gmem G exit →
  ACQ.1 ≠ w.1 →
  gmo_lt G w exit.
Proof.
  intros Hcons Hlog Hlwb Halt Hpat Hpr Hwa Hcl Hr0 Hlew Hnob
         Hacq Haq Hn0A HleA Hcs Hpoe Hfen Hcross Hpox Hmx Hhart.
  pose proof Hcons as (Hwf & Hppo & _ & _). pose proof Hwf as (Hnd & _ & _).
  pose proof (lock_acq_gwrites G b ACQ Hwf Hacq) as HAw.
  pose proof (gwix_pos G ACQ HAw) as HposA.
  assert (Hw : w ∈ gwrites G).
  { destruct Hwa as (v & Hv). by eapply gwrites_byte_gwrites. }
  pose proof (gwix_pos G w Hw) as Hposw.
  (* F3″: the writer's own acquire, at log position [q] *)
  destruct (holder_acq_graph G log b a n0 r0 w Hwf Hlog Hlwb Hpr Hw Hr0 Hlew
              Hwa Hcl)
    as (q & mq & Hq & Hlk & Hs & Hnz & Ht & Hfree & Hno & _).
  (* F3′ locality: the fold is FREE just before the reader's acquire *)
  pose proof (acq_fold_free G log b n0 h ACQ Hcons Hlog Hlwb Halt Hpat Hacq
                HleA) as HfreeA.
  (* ppo rule 5: the reader's acquire is gmo-before its segment's exit *)
  destruct (lock_acq_read G b ACQ Hpat Hacq) as [HrA _].
  assert (HmoAx : gmo_lt G ACQ exit) by (by eapply acq_gmo_after).
  destruct (log_of_write G log w Hwf Hlog Hw Hlew) as (mw & Hmw & Hgw).
  (* the two acquires are distinct events *)
  destruct (decide (q = (gwix G ACQ - 1)%nat)) as [Heq|Hne].
  { exfalso. subst q.
    destruct (log_of_lookup G log (gwix G ACQ - 1)%nat mq Hwf Hlog Hlk)
      as (A' & Hat' & Hm' & Hix' & Hw').
    assert (A' = ACQ) as ->.
    { eapply gwix_inj; [exact Hnd|exact Hw'|exact HAw|rewrite Hix'; lia]. }
    apply Hhart. pose proof (gmsg_tid G ACQ mq Hm') as HtA.
    rewrite Ht in HtA. by injection HtA as <-. }
  destruct (decide (q < gwix G ACQ - 1)%nat) as [Hlt|Hge].
  - (* ---- WRITER-FIRST: the handoff ---- *)
    destruct (release_between_graph G log b n0 q (gwix G ACQ - 1)%nat mq w.1
                Hwf Hlog ltac:(lia) Hlt Hlk Hs Hnz Ht Hfree HfreeA)
      as (r & R & mr & Hr & Hlkr & Hsr & Hzr & Hatr & Hrelr & Hixr & Hwr & Hhr).
    (* the writer's release cannot sit BELOW its own protected write *)
    assert (Hrp : (gwix G w - 1 ≤ r)%nat).
    { destruct (decide (r < gwix G w - 1)%nat) as [Hc|Hc]; [|lia].
      exfalso. exact (Hno r mr ltac:(lia) Hlkr Hsr Hzr). }
    (* … nor AT it: [w] does not touch the lock word *)
    assert (Hrne : r ≠ (gwix G w - 1)%nat).
    { intros ->. rewrite Hmw in Hlkr. injection Hlkr as <-.
      rewrite (gmsg_byte_None G w mw b Hgw Hnob) in Hsr. by destruct Hsr. }
    eapply gmo_lt_trans; [|exact HmoAx].
    eapply gwix_lt_gmo; [exact Hwf|exact Hw|exact HAw|lia].
  - (* ---- READER-FIRST: refuted ---- *)
    assert (HltA : (gwix G ACQ - 1 < q)%nat) by lia.
    destruct (log_of_write G log ACQ Hwf Hlog HAw HleA) as (mA & HmA & HgA).
    pose proof Hacq as (va & Hva & Hvane).
    assert (HbA : msg_byte mA b = Some va)
      by (by apply (gmsg_byte G ACQ mA b va)).
    assert (HnzA : wm_data mA ≠ wlock_zero4).
    { intros Hz. apply Hvane. by eapply zero4_byte. }
    assert (HtA : wm_tid mA = Some ACQ.1) by (by eapply gmsg_tid).
    destruct (release_between_graph G log b n0 (gwix G ACQ - 1)%nat q mA ACQ.1
                Hwf Hlog ltac:(lia) HltA HmA ltac:(by exists va) HnzA HtA
                HfreeA Hfree)
      as (r' & R' & mr' & Hr' & Hlkr' & Hsr' & Hzr' & Hatr' & Hrelr' & Hixr'
          & Hwr' & Hhr').
    pose proof Hcs as (_ & HRel & Hag & HltR & Hnoin).
    assert (HRle : (gwix G REL ≤ gwix G R')%nat).
    { destruct (decide (gwix G R' < gwix G REL)%nat) as [Hc|Hc]; [|lia].
      exfalso. apply (Hnoin R' lock_free Hrelr' Hhr'). lia. }
    assert (HmoRw : gmo_lt G REL w).
    { eapply gwix_lt_gmo;
        [exact Hwf|by eapply lock_rel_gwrites|exact Hw|lia]. }
    assert (HmoWe : gmo_lt G w entry) by (by eapply gcross_gmo).
    assert (HmoeR : gmo_lt G entry REL) by (by eapply fence_gmo_after).
    exfalso. eapply (gmo_lt_irrefl G w).
    eapply gmo_lt_trans; [exact HmoWe|].
    eapply gmo_lt_trans; [exact HmoeR|exact HmoRw].
Qed.

(* ====================================================================== *)
(** * 5. NON-VACUITY (a): the LB cycle IS a two-segment cycle

    [WeakRvwmoLinInd.lbgd_cycle]'s [RacyD] cycle, re-presented in this file's
    segment vocabulary: two segments, two rf cross edges, and the two
    [Pinned] certificates that would close it.  Both certificates are FALSE
    in [lbg] — which is exactly why the load-buffering execution survives —
    so the pair shows the kill is CERTIFICATE-DRIVEN and its conclusion
    shape is inhabited. *)

Lemma lbg_grf_01 : grf lbg (0%nat, 1%nat) (1%nat, 0%nat).
Proof.
  exists 8%Z, 1%nat, WeakLitmus.b1. split.
  - exists (LLoad false 8 [1%nat] [WeakLitmus.b1]),
           8%Z, [1%nat], [WeakLitmus.b1], 0%nat.
    split_and!; reflexivity.
  - by vm_compute.
Qed.

Lemma lbg_grf_10 : grf lbg (1%nat, 1%nat) (0%nat, 0%nat).
Proof.
  exists 0%Z, 2%nat, WeakLitmus.b1. split.
  - exists (LLoad false 0 [2%nat] [WeakLitmus.b1]),
           0%Z, [2%nat], [WeakLitmus.b1], 0%nat.
    split_and!; reflexivity.
  - by vm_compute.
Qed.

Definition lb_segs : list seg :=
  [Seg 1%nat (1%nat, 0%nat) (1%nat, 1%nat);
   Seg 0%nat (0%nat, 0%nat) (0%nat, 1%nat)].

Theorem lbg_pinned_would_kill :
  gmo_lt lbg (1%nat, 0%nat) (1%nat, 1%nat) →
  gmo_lt lbg (0%nat, 0%nat) (0%nat, 1%nat) → False.
Proof.
  intros H1 H0.
  eapply (cycle_kill_arms lbg (0%nat, 1%nat) lb_segs lb_graph_consistent
            ltac:(done)).
  simpl. split_and!; [| |reflexivity].
  - apply Pinned; [left; exact lbg_grf_01|exact H1].
  - apply Pinned; [left; exact lbg_grf_10|exact H0].
Qed.

Theorem lbg_pinned_absent :
  ¬ gmo_lt lbg (0%nat, 0%nat) (0%nat, 1%nat) ∧
  ¬ gmo_lt lbg (1%nat, 0%nat) (1%nat, 1%nat).
Proof.
  split; intros (_ & _ & Hlt); vm_compute in Hlt; lia.
Qed.

(* ====================================================================== *)
(** * 6. NON-VACUITY (b): the CS arm, instantiated

    [WeakRvwmoLockWit.lkg] CANNOT serve as this witness, and the reason is
    worth recording: its lock stores are ONE byte wide, while F3′'s
    [alt_step] classifies a message as a RELEASE only if its data is
    literally [wlock_zero4] — the FOUR-byte zero word — and otherwise demands
    [WCexcl].  [lkg]'s release is a one-byte [WCrel] store, so [alt_step]
    returns [None] on it and [wlp_alt] is unsatisfiable on [lkg]'s log,
    whatever the log is.  [lkw] below is [lkg] widened to a 4-byte lock word,
    with the two harts' CS BODIES SWAPPED (hart 0 writes the payload byte,
    hart 1 reads it) — the orientation the CS arm needs, and the WRITER-FIRST
    window order.

      hart 0 (the writer)                 hart 1 (the reader)
      (0,0) ACQ amoswap.aq 0:0->1 (img)   (1,0) ACQ amoswap.aq, reads (0,3)
      (0,1) STORE d := 1 (WCplain)        (1,1) LOAD  d, reads (0,1)
      (0,2) FENCE rw,rw                   (1,2) FENCE rw,rw
      (0,3) REL store 0 := 0              (1,3) REL store 0 := 0            *)

Definition imgw : image :=
  λ a, if bool_decide ((0 ≤ a < 4)%Z ∨ a = 8%Z) then Some WeakLitmus.b0 else None.

Definition z4 : list (bv 8) :=
  [WeakLitmus.b0; WeakLitmus.b0; WeakLitmus.b0; WeakLitmus.b0].
Definition o4 : list (bv 8) :=
  [WeakLitmus.b1; WeakLitmus.b1; WeakLitmus.b1; WeakLitmus.b1].

Definition lkw : gexec :=
  GExec imgw
    [[LRmw true false 0 [0%nat; 0%nat; 0%nat; 0%nat] z4 o4 WCexcl;
      LStore false 8 [WeakLitmus.b1] WCplain;
      LFence true true true true;
      LStore true 0 z4 WCrel];
     [LRmw true false 0 [3%nat; 3%nat; 3%nat; 3%nat] z4 o4 WCexcl;
      LLoad false 8 [2%nat] [WeakLitmus.b1];
      LFence true true true true;
      LStore true 0 z4 WCrel]]
    [(0%nat, 0%nat); (0%nat, 1%nat); (0%nat, 3%nat);
     (1%nat, 0%nat); (1%nat, 1%nat); (1%nat, 3%nat)].

Local Notation ACQw := (0%nat, 0%nat).
Local Notation Wp   := (0%nat, 1%nat).
Local Notation RELw := (0%nat, 3%nat).
Local Notation ACQr := (1%nat, 0%nat).
Local Notation ENT  := (1%nat, 1%nat).
Local Notation RELr := (1%nat, 3%nat).

(** A byte of a uniform word. *)
Lemma z4_lookup (a : Z) : (0 ≤ a < 4)%Z → z4 !! Z.to_nat a = Some WeakLitmus.b0.
Proof.
  intros Ha. assert (Hk : (Z.to_nat a < 4)%nat) by lia.
  by destruct (Z.to_nat a) as [|[|[|[|k]]]]; [| | | |lia].
Qed.

Lemma gwrites_byte_of (G : gexec) (e : geid) (l : lbl) (base : Z)
    (vs : list (bv 8)) (a : Z) (v : bv 8) :
  gx_lbl G e = Some l → lb_wr l = Some (base, vs) → (base ≤ a)%Z →
  vs !! Z.to_nat (a - base) = Some v → gwrites_byte G e a v.
Proof.
  intros Hl Hwr Hle Hv. exists l, base, vs, (Z.to_nat (a - base)).
  split_and!; [done|done|done|]. rewrite /acc_addr Z2Nat.id; lia.
Qed.

Lemma imgw_in (a : Z) : (0 ≤ a < 4)%Z → gx_img lkw a = Some WeakLitmus.b0.
Proof.
  intros Ha. assert (Hd : ((0 ≤ a < 4)%Z ∨ a = 8%Z)) by (by left).
  change (gx_img lkw a) with (imgw a). rewrite /imgw.
  by rewrite (bool_decide_eq_true_2 _ Hd).
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 6.1 Inversions and the position / index arithmetic *)

Lemma lkw_nodup : NoDup (gx_gmo lkw).
Proof.
  repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
Qed.

Lemma lkw_gpos_of (n : nat) (e : geid) : gx_gmo lkw !! n = Some e → gpos lkw e = n.
Proof. apply gpos_of_lookup, lkw_nodup. Qed.

Lemma lkw_gwix_of (n : nat) (w : geid) :
  gwrites lkw !! n = Some w → gwix lkw w = S n.
Proof. apply gwix_of_lookup, lkw_nodup. Qed.

Lemma lkw_p0 : gpos lkw ACQw = 0%nat. Proof. by apply lkw_gpos_of. Qed.
Lemma lkw_p1 : gpos lkw Wp   = 1%nat. Proof. by apply lkw_gpos_of. Qed.
Lemma lkw_p2 : gpos lkw RELw = 2%nat. Proof. by apply lkw_gpos_of. Qed.
Lemma lkw_p3 : gpos lkw ACQr = 3%nat. Proof. by apply lkw_gpos_of. Qed.
Lemma lkw_p4 : gpos lkw ENT  = 4%nat. Proof. by apply lkw_gpos_of. Qed.
Lemma lkw_p5 : gpos lkw RELr = 5%nat. Proof. by apply lkw_gpos_of. Qed.

Lemma lkw_gwrites : gwrites lkw = [ACQw; Wp; RELw; ACQr; RELr].
Proof. by vm_compute. Qed.

Lemma lkw_x1 : gwix lkw ACQw = 1%nat. Proof. by apply lkw_gwix_of; vm_compute. Qed.
Lemma lkw_x2 : gwix lkw Wp   = 2%nat. Proof. by apply lkw_gwix_of; vm_compute. Qed.
Lemma lkw_x3 : gwix lkw RELw = 3%nat. Proof. by apply lkw_gwix_of; vm_compute. Qed.
Lemma lkw_x4 : gwix lkw ACQr = 4%nat. Proof. by apply lkw_gwix_of; vm_compute. Qed.
Lemma lkw_x5 : gwix lkw RELr = 5%nat. Proof. by apply lkw_gwix_of; vm_compute. Qed.

Lemma lkw_mem_inv (e : geid) :
  gmem lkw e →
  e = ACQw ∨ e = Wp ∨ e = RELw ∨ e = ACQr ∨ e = ENT ∨ e = RELr.
Proof.
  intros (l & Hl & Hm). destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|k]]]]; simplify_eq/=; naive_solver.
Qed.

Lemma lkw_gmo_mem (e : geid) : gmem lkw e → e ∈ gx_gmo lkw.
Proof.
  intros [->|[->|[->|[->|[->| ->]]]]]%lkw_mem_inv;
    rewrite /gx_gmo /= !elem_of_cons; naive_solver.
Qed.

Lemma lkw_mo (e1 e2 : geid) :
  gmem lkw e1 → gmem lkw e2 → (gpos lkw e1 < gpos lkw e2)%nat → gmo_lt lkw e1 e2.
Proof.
  intros H1 H2 Hlt.
  split_and!; [by apply lkw_gmo_mem|by apply lkw_gmo_mem|exact Hlt].
Qed.

(** gmo IS per-hart program order, hart 0's section first. *)
Lemma lkw_gmo_po (e1 e2 : geid) :
  gmem lkw e1 → gmem lkw e2 → e1.1 = e2.1 → (e1.2 < e2.2)%nat →
  gmo_lt lkw e1 e2.
Proof.
  intros Hm1 Hm2 Hag Hlt.
  split_and!; [by apply lkw_gmo_mem|by apply lkw_gmo_mem|].
  apply lkw_mem_inv in Hm1. apply lkw_mem_inv in Hm2.
  destruct Hm1 as [->|[->|[->|[->|[->| ->]]]]];
    destruct Hm2 as [->|[->|[->|[->|[->| ->]]]]];
    simpl in Hag, Hlt; try lia;
    rewrite ?lkw_p0 ?lkw_p1 ?lkw_p2 ?lkw_p3 ?lkw_p4 ?lkw_p5; lia.
Qed.

(** The write footprints. *)
Lemma lkw_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte lkw e a v →
  (e = ACQw ∧ (0 ≤ a < 4)%Z ∧ v = WeakLitmus.b1) ∨
  (e = Wp   ∧ a = 8%Z ∧ v = WeakLitmus.b1) ∨
  (e = RELw ∧ (0 ≤ a < 4)%Z ∧ v = WeakLitmus.b0) ∨
  (e = ACQr ∧ (0 ≤ a < 4)%Z ∧ v = WeakLitmus.b1) ∨
  (e = RELr ∧ (0 ≤ a < 4)%Z ∧ v = WeakLitmus.b0).
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|k]]]]; simplify_eq/=;
    destruct j as [|[|[|[|j]]]]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver lia.
Qed.

(** The read footprints. *)
Lemma lkw_rd (e : geid) (a : Z) (t : nat) (v : bv 8) :
  greads_byte lkw e a t v →
  (e = ACQw ∧ (0 ≤ a < 4)%Z ∧ t = 0%nat ∧ v = WeakLitmus.b0) ∨
  (e = ACQr ∧ (0 ≤ a < 4)%Z ∧ t = 3%nat ∧ v = WeakLitmus.b0) ∨
  (e = ENT  ∧ a = 8%Z ∧ t = 2%nat ∧ v = WeakLitmus.b1).
Proof.
  intros (l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|[|[|k]]]]; simplify_eq/=;
    destruct j as [|[|[|[|j]]]]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver lia.
Qed.

Lemma lkw_wr_lock (w : geid) (a : Z) (v : bv 8) :
  gwrites_byte lkw w a v → (0 ≤ a < 4)%Z →
  (w = ACQw ∧ v = WeakLitmus.b1) ∨ (w = RELw ∧ v = WeakLitmus.b0) ∨
  (w = ACQr ∧ v = WeakLitmus.b1) ∨ (w = RELr ∧ v = WeakLitmus.b0).
Proof.
  intros [(->&_&->)|[(_&Hab&_)|[(->&_&->)|[(->&_&->)|(->&_&->)]]]]%lkw_wr Ha;
    auto. lia.
Qed.

Lemma lkw_wr_data (w : geid) (v : bv 8) :
  gwrites_byte lkw w 8%Z v → w = Wp ∧ v = WeakLitmus.b1.
Proof.
  intros [(_&Hab&_)|[(->&_&->)|[(_&Hab&_)|[(_&Hab&_)|(_&Hab&_)]]]]%lkw_wr;
    by [lia| |lia|lia|lia].
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 6.2 [lkw] is RVWMO⁻-consistent *)

Theorem lkw_consistent : rvwmo_minus_consistent lkw.
Proof.
  split_and!.
  - (* gwf *) split_and!.
    + exact lkw_nodup.
    + intros e. split.
      * intros He. rewrite /gx_gmo /= !elem_of_cons elem_of_nil in He.
        destruct He as [->|[->|[->|[->|[->|[->|[]]]]]]];
          eexists; split; reflexivity.
      * apply lkw_gmo_mem.
    + intros i p k l Hp Hk.
      destruct i as [|[|i]]; simplify_eq/=;
        destruct k as [|[|[|[|k]]]]; simplify_eq/=; done.
  - (* ppo⁻ ⊆ gmo *)
    intros e1 e2 Hppo.
    destruct (gppo_gmem lkw e1 e2 Hppo) as [Hm1 Hm2].
    destruct (gppo_po_lt lkw e1 e2 Hppo) as [Hag Hlt].
    by apply lkw_gmo_po.
  - (* load value *)
    intros e a t v Hrd.
    destruct (lkw_rd e a t v Hrd)
      as [(->&Ha&->&->)|[(->&Ha&->&->)|(->&->&->&->)]].
    + split; [by apply imgw_in|].
      intros w' v' Hw' Hvis. exfalso.
      destruct Hvis as [(_ & _ & Hp)|(_ & Hoff & _)].
      * rewrite lkw_p0 in Hp. lia.
      * simpl in Hoff. lia.
    + split.
      * exists RELw. split_and!.
        { by vm_compute. }
        { eapply (gwrites_byte_of lkw RELw (LStore true 0 z4 WCrel) 0%Z z4);
            [done|done|lia|].
          replace (a - 0)%Z with a by lia. by apply z4_lookup. }
        { left. apply lkw_mo; [by eexists|by eexists|].
          rewrite lkw_p2 lkw_p3. lia. }
      * intros w' v' Hw' Hvis.
        destruct (lkw_wr_lock w' a v' Hw' Ha)
          as [[-> _]|[[-> _]|[[-> _]|[-> _]]]].
        { rewrite lkw_x1. lia. }
        { rewrite lkw_x3. lia. }
        { exfalso. destruct Hvis as [Hmo|(_ & Hoff & _)];
            [by eapply gmo_lt_irrefl|simpl in Hoff; lia]. }
        { exfalso. destruct Hvis as [(_ & _ & Hp)|(_ & Hoff & _)];
            [rewrite lkw_p5 lkw_p3 in Hp; lia|simpl in Hoff; lia]. }
    + split.
      * exists Wp. split_and!.
        { by vm_compute. }
        { by exists (LStore false 8 [WeakLitmus.b1] WCplain), 8%Z,
                    [WeakLitmus.b1], 0%nat. }
        { left. apply lkw_mo; [by eexists|by eexists|].
          rewrite lkw_p1 lkw_p4. lia. }
      * intros w' v' Hw' Hvis.
        destruct (lkw_wr_data w' v' Hw') as [-> _]. rewrite lkw_x2. lia.
  - (* atomicity *)
    intros e a t v Hrd Hw w' v' Hw' [Hlo Hhi].
    destruct (lkw_rd e a t v Hrd)
      as [(->&Ha&->&->)|[(->&Ha&->&->)|(->&->&->&->)]].
    + rewrite lkw_x1 in Hhi. lia.
    + rewrite lkw_x4 in Hhi. lia.
    + destruct Hw as (l & Hl & Hlw). rewrite /gx_lbl /= in Hl. by simplify_eq.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 6.3 The lock protocol and the reader's row *)

Theorem lkw_pattern : lock_pattern lkw 0%Z.
Proof.
  split.
  - intros v0 Hv. rewrite (imgw_in 0%Z ltac:(lia)) in Hv. by simplify_eq.
  - intros w v Hw.
    destruct (lkw_wr_lock w 0%Z v Hw ltac:(lia))
      as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    + left. split_and!.
      * by exists (LRmw true false 0 [0%nat;0%nat;0%nat;0%nat] z4 o4 WCexcl).
      * intros Heq. by apply WeakLitmus.b0_ne_b1.
      * exists 0%nat.
        by exists (LRmw true false 0 [0%nat;0%nat;0%nat;0%nat] z4 o4 WCexcl),
                  0%Z, [0%nat;0%nat;0%nat;0%nat], z4, 0%nat.
    + by right.
    + left. split_and!.
      * by exists (LRmw true false 0 [3%nat;3%nat;3%nat;3%nat] z4 o4 WCexcl).
      * intros Heq. by apply WeakLitmus.b0_ne_b1.
      * exists 3%nat.
        by exists (LRmw true false 0 [3%nat;3%nat;3%nat;3%nat] z4 o4 WCexcl),
                  0%Z, [3%nat;3%nat;3%nat;3%nat], z4, 0%nat.
    + by right.
Qed.

Lemma lkw_acq_r : lock_acq lkw 0%Z ACQr.
Proof.
  exists WeakLitmus.b1. split.
  - by exists (LRmw true false 0 [3%nat;3%nat;3%nat;3%nat] z4 o4 WCexcl),
              0%Z, o4, 0%nat.
  - intros Heq. by apply WeakLitmus.b0_ne_b1.
Qed.

Lemma lkw_rel_r : lock_rel lkw 0%Z RELr.
Proof. by exists (LStore true 0 z4 WCrel), 0%Z, z4, 0%nat. Qed.

Lemma lkw_aq_r : glbl_is lkw ACQr lb_aq.
Proof.
  by exists (LRmw true false 0 [3%nat;3%nat;3%nat;3%nat] z4 o4 WCexcl).
Qed.

Theorem lkw_cs_r : lock_cs lkw 0%Z ACQr RELr.
Proof.
  apply lock_cs_intro; [exact lkw_consistent| | | |].
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - exact lkw_acq_r.
  - exact lkw_rel_r.
  - intros x v Hx Hag Hlo Hhi.
    destruct (lkw_wr_lock x 0%Z v Hx ltac:(lia))
      as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; simpl in *; lia.
Qed.

Lemma lkw_fence_r : gfence_covers lkw ENT RELr.
Proof.
  exists true, true, true, true. split_and!.
  - split_and!; [done|simpl; lia|].
    exists 2%nat. split_and!; [simpl; lia|simpl; lia|done].
  - left. split; [by exists (LLoad false 8 [2%nat] [WeakLitmus.b1])|done].
  - right. split; [by exists (LStore true 0 z4 WCrel)|done].
Qed.

Lemma lkw_grf : grf lkw Wp ENT.
Proof.
  exists 8%Z, 2%nat, WeakLitmus.b1. split.
  - by exists (LLoad false 8 [2%nat] [WeakLitmus.b1]), 8%Z, [2%nat],
              [WeakLitmus.b1], 0%nat.
  - by vm_compute.
Qed.

Lemma lkw_wp_plain : gcls lkw Wp WCplain.
Proof. by exists (LStore false 8 [WeakLitmus.b1] WCplain). Qed.

Lemma lkw_wp_data : ∃ v, gwrites_byte lkw Wp 8%Z v.
Proof.
  exists WeakLitmus.b1.
  by exists (LStore false 8 [WeakLitmus.b1] WCplain), 8%Z, [WeakLitmus.b1], 0%nat.
Qed.

Lemma lkw_wp_no_lock : ∀ v, ¬ gwrites_byte lkw Wp 0%Z v.
Proof.
  intros v Hv.
  by destruct (lkw_wr_lock Wp 0%Z v Hv ltac:(lia))
    as [[Hc _]|[[Hc _]|[[Hc _]|[Hc _]]]].
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 6.4 The log, and the three log-vocabulary exports *)

Definition lkw_log : list wmsg :=
  [ WMsg 0%Z o4 (Some 0%nat) WCexcl;
    WMsg 8%Z [WeakLitmus.b1] (Some 0%nat) WCplain;
    WMsg 0%Z z4 (Some 0%nat) WCrel;
    WMsg 0%Z o4 (Some 1%nat) WCexcl;
    WMsg 0%Z z4 (Some 1%nat) WCrel ].

Lemma msg_byte_o4_0 (t : option agent) (k : wm_class) :
  msg_byte (WMsg 0%Z o4 t k) 0%Z = Some WeakLitmus.b1.
Proof. reflexivity. Qed.

Lemma msg_byte_z4_0 (t : option agent) (k : wm_class) :
  msg_byte (WMsg 0%Z z4 t k) 0%Z = Some WeakLitmus.b0.
Proof. reflexivity. Qed.

Lemma msg_byte_o4_8 (t : option agent) (k : wm_class) :
  msg_byte (WMsg 0%Z o4 t k) 8%Z = None.
Proof. reflexivity. Qed.

Lemma msg_byte_z4_8 (t : option agent) (k : wm_class) :
  msg_byte (WMsg 0%Z z4 t k) 8%Z = None.
Proof. reflexivity. Qed.

Lemma msg_byte_d_0 (t : option agent) (k : wm_class) :
  msg_byte (WMsg 8%Z [WeakLitmus.b1] t k) 0%Z = None.
Proof. reflexivity. Qed.

Lemma lkw_log_of : log_of lkw lkw_log.
Proof.
  intros p m. rewrite /gwrite_at lkw_gwrites /lkw_log.
  destruct p as [|[|[|[|[|p]]]]]; simpl.
  1-5: split;
    [ intros [= <-]; eexists; split; [reflexivity|by vm_compute]
    | intros (w & Hw & Hm); injection Hw as <-; vm_compute in Hm;
      by simplify_eq ].
  split; [by intros [=]|by intros (w & [=] & _)].
Qed.

Lemma lkw_log_0 : lkw_log !! 0%nat = Some (WMsg 0%Z o4 (Some 0%nat) WCexcl).
Proof. reflexivity. Qed.
Lemma lkw_log_1 :
  lkw_log !! 1%nat = Some (WMsg 8%Z [WeakLitmus.b1] (Some 0%nat) WCplain).
Proof. reflexivity. Qed.
Lemma lkw_log_2 : lkw_log !! 2%nat = Some (WMsg 0%Z z4 (Some 0%nat) WCrel).
Proof. reflexivity. Qed.
Lemma lkw_log_3 : lkw_log !! 3%nat = Some (WMsg 0%Z o4 (Some 1%nat) WCexcl).
Proof. reflexivity. Qed.
Lemma lkw_log_4 : lkw_log !! 4%nat = Some (WMsg 0%Z z4 (Some 1%nat) WCrel).
Proof. reflexivity. Qed.
Lemma lkw_log_hi (p : nat) : lkw_log !! (S (S (S (S (S p))))) = None.
Proof. reflexivity. Qed.

Lemma lkw_lwb : lock_word_byte lkw_log 0%Z.
Proof.
  intros p m v Hp Hb Hv. destruct p as [|[|[|[|[|p]]]]].
  - rewrite lkw_log_0 in Hp. injection Hp as Hm. subst m.
    rewrite msg_byte_o4_0 in Hb. injection Hb as Heq.
    exfalso. exact (WeakLitmus.b0_ne_b1 (eq_sym (eq_trans Heq Hv))).
  - rewrite lkw_log_1 in Hp. injection Hp as Hm. subst m.
    rewrite msg_byte_d_0 in Hb. discriminate.
  - rewrite lkw_log_2 in Hp. injection Hp as Hm. subst m. reflexivity.
  - rewrite lkw_log_3 in Hp. injection Hp as Hm. subst m.
    rewrite msg_byte_o4_0 in Hb. injection Hb as Heq.
    exfalso. exact (WeakLitmus.b0_ne_b1 (eq_sym (eq_trans Heq Hv))).
  - rewrite lkw_log_4 in Hp. injection Hp as Hm. subst m. reflexivity.
  - rewrite lkw_log_hi in Hp. discriminate.
Qed.

Lemma lkw_alt : wlp_alt lkw_log 0%Z 0 None.
Proof. split; [simpl; lia|by vm_compute]. Qed.

Lemma lkw_wprot : wprot_at lkw_log 8%Z 0%Z 0 0.
Proof.
  split; [lia|]. intros p m Hp _ Hs Hk. destruct p as [|[|[|[|[|p]]]]].
  - rewrite lkw_log_0 in Hp. injection Hp as Hm. subst m.
    rewrite msg_byte_o4_8 in Hs. by destruct Hs.
  - rewrite lkw_log_1 in Hp. injection Hp as Hm. subst m. by vm_compute.
  - rewrite lkw_log_2 in Hp. injection Hp as Hm. subst m.
    rewrite msg_byte_z4_8 in Hs. by destruct Hs.
  - rewrite lkw_log_3 in Hp. injection Hp as Hm. subst m.
    rewrite msg_byte_o4_8 in Hs. by destruct Hs.
  - rewrite lkw_log_4 in Hp. injection Hp as Hm. subst m.
    rewrite msg_byte_z4_8 in Hs. by destruct Hs.
  - rewrite lkw_log_hi in Hp. discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 6.5 THE INSTANTIATION

    Every hypothesis of [cs_chained] is discharged on [lkw]/[lkw_log], and
    its conclusion is DERIVED — the strongest form of non-vacuity available
    (stronger than [WeakRvwmoLockWit.cs_kill_hyps_sat]'s existential, which
    had to drop the configuration because the kill's conclusion is [False];
    here the conclusion is an ordinary gmo fact and nothing has to be
    dropped).  This is the WRITER-FIRST window order — hart 0's section
    closes ([RELw], write index 3) before hart 1's opens ([ACQr], index 4). *)

Lemma lkw_log_len : length lkw_log = 5%nat.
Proof. reflexivity. Qed.

Theorem lkw_cs_chained : gmo_lt lkw Wp RELr.
Proof.
  eapply (cs_chained lkw lkw_log 0%Z 8%Z 0 0 None Wp ENT RELr ACQr RELr).
  - exact lkw_consistent.
  - exact lkw_log_of.
  - exact lkw_lwb.
  - exact lkw_alt.
  - exact lkw_pattern.
  - exact lkw_wprot.
  - exact lkw_wp_data.
  - exact lkw_wp_plain.
  - rewrite lkw_x2. lia.
  - rewrite lkw_x2 lkw_log_len. lia.
  - exact lkw_wp_no_lock.
  - exact lkw_acq_r.
  - exact lkw_aq_r.
  - rewrite lkw_x4. lia.
  - rewrite lkw_x4 lkw_log_len. lia.
  - exact lkw_cs_r.
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - exact lkw_fence_r.
  - left. exact lkw_grf.
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - by eexists.
  - simpl. lia.
Qed.

(** … and the certificate the composition consumes. *)
Corollary lkw_cert : cert lkw Wp (Seg 1%nat ENT RELr).
Proof. apply CSchained. exact lkw_cs_chained. Qed.

(* ====================================================================== *)
(** * 7. AUDIT *)

Print Assumptions cycle_kill_arms.
Print Assumptions cs_chained.
Print Assumptions holder_acq_graph.
Print Assumptions release_between_graph.
Print Assumptions acq_fold_free.
Print Assumptions lkw_consistent.
Print Assumptions lkw_cs_chained.
Print Assumptions lbg_pinned_would_kill.
Print Assumptions lbg_pinned_absent.
