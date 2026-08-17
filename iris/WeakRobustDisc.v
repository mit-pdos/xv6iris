(** * WeakRobustDisc.v — COVERAGE FROM RELEASE/ACQUIRE SITE FACTS
      (premise discharge, Track A, items A1–A3)

    [claude-notes/design/weak-memory-premise-discharge.md] splits the
    discharge of [WeakRobustMain.main_premises] into three tracks.  This
    file is TRACK A: the machine-side view arithmetic, stated over an
    arbitrary traced bundle, with no xv6, no Iris and no Sail — the
    generic half that turns SITE FACTS about a release/acquire pair into
    the per-edge obligations [WeakRobustAcyc.edge_ok] and
    [WeakRobustAcyc2.ee_ok].

    WHAT A "SITE FACT" IS.  Every hypothesis below is a projection of the
    RECORDED TRACE — the label of one event ("the read at [kr] carries
    [aq]", "the event at [kf] is a [fence rw,w]"), the fulfilled
    timestamp of one event ([gev_ts]), the byte/timestamp pairs one event
    reads ([gev_reads]), or a [wstate] the bundle already records in a
    pre-state ([covered], which is literally "[w_vwNew] at this event's
    pre-record is at least [ts]").  Nothing here quantifies over cycles,
    over runs, or over program states; Track B's job is to EXHIBIT these
    facts for xv6, Track A's is to make them sufficient.

    THE THREE DELIVERABLES.

    A1 [covered_of_release_acquire].  The lock/flag-mediated edge, in
    full.  Writer [i] fulfils [ts] at [k1]; a [pw ∧ sw] fence
    ([fence rw,w]) sits at [kf > k1]; [i] fulfils [ts_s] at [ks > kf]
    (the RELEASE store).  Reader [j ≠ i] reads [ts_s] at [kr] and is
    DISCIPLINED there ([aq] read, or a [pr ∧ sw] fence before the bound)
    — the ACQUIRE.  Then the reader's [w_vwNew] is ≥ [ts] at every
    position from the acquire on: [covered Tj k2 ts].  The consequence
    [edge_ok_of_release_acquire] puts the acquire BEFORE a later plain
    read and concludes [edge_ok Tj kr k' ts] for every [k'], which is the
    shape [WeakRobustMain.edges_split] wants.

    A2 [covered_of_release_chain].  The same, through any number of
    intermediate agents (context switch through the scheduler lock, then
    the process lock, …).  The hop lemma is [acquire_release_lt]: an
    agent that ACQUIRED [tin] and later fulfils [tout] has [tin < tout] —
    and, unlike the origin hop, it needs NO fence, because an acquire
    lands in [w_vwNew] (not merely [w_vwOld]) and EXT reads [w_vwNew]
    directly.  [chain_ok] / [chain_end] fold the hops; [chain_lt]
    iterates; [covered_of_release_two_hops] is the fence-free two-hop
    spelling, with no [hop] records in sight.

    A3 [ee_ok_fence_cover] / [ee_ok_waw_cover] / [ee_ok_zero_floor].  The
    three arms of [WeakRobustAcyc2.ee_ok]'s comment, each proved from
    trace facts alone, plus [ee_ok_of_arms], which assembles them into
    [ee_ok TS].  Both substantive arms are instances of the two
    workhorses above: fence-cover IS the release site ([release_lt]) run
    at the E edge's own [F < t̂]; WAW-cover IS the hop lemma
    ([covered_fulfil_lt]).

    REUSE.  Everything rests on [WeakRobustAcyc]'s segment-lemma
    ingredients, used verbatim: [astep_ok_read_vwNew_aq] (the aq arm),
    [astep_ok_read_vrOld] + [astep_ok_fence_vwNew] (the fence arm),
    [astep_ok_fulfil_ext] (EXT), [fwd_own] / [read_unforwarded] /
    [fwd_own_read_unforwarded] (the non-forwarding side condition) and
    [WeakRobustGraph.asteps_ws_le] (view monotonicity).  The two new
    [astep_ok] facts are [astep_ok_fulfil_vwOld] (a fulfil raises
    [w_vwOld] to its own timestamp) and [astep_ok_fence_vwNew_w] (the
    [pw ∧ sw] mirror of [astep_ok_fence_vwNew]) — neither was needed by
    S1, whose measure only ever travelled through [w_vwNew].

    HYPOTHESES BEYOND THE BUNDLE.  Exactly the two [WeakRobustAcyc]'s S1
    takes: [ptraces_wf] and [ptraces_fwd_own] (both DERIVED for a real
    behavior — see [WeakRobustAcyc.ptraces_of_fwd_own]).  [fwd_own] is
    needed only by the FENCE flavour of an acquire (a plain load's gain
    is the forwarded view, not the raw timestamp); the [aq] flavour never
    touches it.  No [ptraces_ws_init], no [writes_fulfilled].

    ONE HYPOTHESIS THAT IS NOT A PURE SITE FACT, and why it is harmless:
    [release_lt] asks that the fulfilled message WRITE A BYTE
    ([msg_byte m a] is [Some]).  [store_post] raises [w_vwOld] per byte,
    so a zero-width store would fulfil a timestamp without raising
    anything.  The fact is read straight off the frozen log and every
    call site has it for free — the reader read that very message (A1) or
    the E edge carries [msg_writes] as a conjunct (A3).

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported FIRST so that [WeakPromise]'s [wlabel]
    constructors shadow its [lbl] ones. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobustGraph WeakRobust WeakRobustProv
                            WeakRobustAcyc WeakRobustLin WeakRobustOrd
                            WeakRobustAcyc2.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** THE RELEASE FENCE

    [WeakRobustAcyc.lb_fence_prsw] is the ACQUIRE-side shape
    ([fence r,rw]: past reads are pred, future writes are succ).  The
    release site needs its mirror image, [fence rw,w] — past WRITES are
    pred ([pw]) and future writes are succ ([sw]) — which is exactly the
    pair [WeakMem.fence_post_vwNew_w] routes [w_vwOld] into [w_vwNew]
    on. *)
Definition lb_fence_pwsw (l : wlabel) : Prop :=
  match l with LFence _ pw _ sw => pw = true ∧ sw = true | _ => False end.

(* ------------------------------------------------------------------ *)
(** ** THE TWO NEW [astep_ok] FACTS *)

(** A message that writes byte [a] has nonempty data — the side
    condition [store_post_run_vwOld] asks for, read off the log. *)
Lemma msg_byte_len m a : is_Some (msg_byte m a) → (0 < length (wm_data m))%nat.
Proof.
  rewrite /msg_byte. case_bool_decide as Hle; [|by intros []].
  intros [b Hb]. apply lookup_lt_Some in Hb. lia.
Qed.

Section astep.
  Context {P : Type}.
  Implicit Types ag : wpagent P.

  (** A FULFIL raises [w_vwOld] to the timestamp it fulfils.  (S1 never
      needed this: its measure entered through [w_vwNew] on the reader's
      side.  A RELEASE site is where the writer's own earlier store must
      be picked up, and that store's gain is [w_vwOld].) *)
  Lemma astep_ok_fulfil_vwOld img log i ag l f ts a m :
    astep_ok img log i ag l f (Some ts) →
    log !! (ts - 1)%nat = Some m → is_Some (msg_byte m a) →
    (ts ≤ w_vwOld (f (pa_ws ag)))%nat.
  Proof.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros (ts' & kc & _ & Hlog & _ & -> & Heq) Hm Hb.
      injection Heq as <-. rewrite Hlog in Hm. simplify_eq.
      apply store_post_run_vwOld. by apply (msg_byte_len _ a Hb).
    - intros (ts' & kc & _ & _ & Hlog & _ & _ & _ & -> & Heq) Hm Hb.
      injection Heq as <-. rewrite Hlog in Hm. simplify_eq.
      apply store_post_run_vwOld. by apply (msg_byte_len _ a Hb).
    - by intros [_ ?].
    - by intros [_ ?].
  Qed.

  (** The [pw ∧ sw] mirror of [WeakRobustAcyc.astep_ok_fence_vwNew]: a
      [fence rw,w] ships [w_vwOld] into [w_vwNew]. *)
  Lemma astep_ok_fence_vwNew_w img log i ag l f D :
    astep_ok img log i ag l f D → lb_fence_pwsw l →
    (w_vwOld (pa_ws ag) ≤ w_vwNew (f (pa_ws ag)))%nat.
  Proof.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|];
      simpl; try (by intros _ []).
    intros [-> _] [-> ->]. apply fence_post_vwNew_w.
  Qed.

End astep.

(* ------------------------------------------------------------------ *)
(** ** [covered] weakens in the timestamp *)

Lemma covered_mono_ts {P D : Type} (T : atrace P D) k ts ts' :
  covered T k ts → (ts' ≤ ts)%nat → covered T k ts'.
Proof. intros (ag & Hag & Hge) Hle. exists ag. split; [done|lia]. Qed.

(* ------------------------------------------------------------------ *)
(** ** A HOP of a synchronization chain (A2)

    One intermediate agent of the chain: it ACQUIRES the incoming
    timestamp at [hp_kr] (its discipline window closing at [hp_kd]) and
    RELEASES at [hp_ks], fulfilling [hp_ts].  All six fields are trace
    coordinates — nothing semantic lives in the record. *)
Record hop := Hop {
  hp_ag : agent;   (** the agent performing this hop *)
  hp_kr : nat;     (** its acquiring read's trace position *)
  hp_kd : nat;     (** the position by which the acquire is complete *)
  hp_ks : nat;     (** its releasing fulfil's trace position *)
  hp_ts : nat;     (** the timestamp that fulfil consumes *)
  hp_a  : Z;       (** the byte its acquiring read reads *)
}.
Add Printing Constructor hop.

(* ------------------------------------------------------------------ *)
Section disc.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (TS : ptraces P D).

  (** The two hypotheses [WeakRobustAcyc]'s S1 takes, and no others. *)
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hfo : ptraces_fwd_own TS).

  Implicit Types T : atrace P D.
  Implicit Types e : gev.

  Local Notation Img := (pt_img TS).
  Local Notation Log := (pt_log TS).

  (* ---------------------------------------------------------------- *)
  (** ** Bookkeeping *)

  Lemma trace_wf i T : pt_trs TS !! i = Some T → atrace_wf pstep Img Log i T.
  Proof. by apply Hwf. Qed.

  Lemma ag_at i T k ev :
    pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
    ∃ ag, at_ags T !! k = Some ag.
  Proof.
    intros HT Hev. destruct (trace_wf i T HT) as [Hlen _].
    apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hev. lia.
  Qed.

  Lemma ws_mono i T k k' ag ag' :
    pt_trs TS !! i = Some T → (k ≤ k')%nat →
    at_ags T !! k = Some ag → at_ags T !! k' = Some ag' →
    ws_le (pa_ws ag) (pa_ws ag').
  Proof.
    intros HT Hle Hk Hk'.
    eapply (asteps_ws_le pstep Img Log i (at_ags T) (at_evs T) k k');
      [by apply trace_wf|exact Hle|exact Hk|exact Hk'].
  Qed.

  (** [covered] propagates FORWARD along the trace (views only grow).
      The target agent record is asked for because [covered] names it:
      past the end of the trace there is nothing to be covered at. *)
  Lemma covered_pos_mono i T k k' ts ag' :
    pt_trs TS !! i = Some T → covered T k ts → (k ≤ k')%nat →
    at_ags T !! k' = Some ag' → covered T k' ts.
  Proof.
    intros HT (ag & Hag & Hge) Hle Hag'.
    exists ag'. split; [done|].
    have Hmono := ws_mono i T k k' ag ag' HT Hle Hag Hag'.
    have := ws_le_vwNew _ _ Hmono. lia.
  Qed.

  (** The two bundle-level trace facts, unpacked at a NAMED trace. *)
  Lemma gev_ts_at i T k ts :
    pt_trs TS !! i = Some T → gev_ts TS (i, k) = Some ts →
    ∃ ev, at_evs T !! k = Some ev ∧ ae_ts ev = Some ts.
  Proof.
    intros HT Hts. rewrite /gev_ts /gev_ev /= HT /= in Hts.
    destruct (at_evs T !! k) as [ev|]; simpl in Hts; [|done]. by exists ev.
  Qed.

  Lemma gev_reads_at i T k a ts :
    pt_trs TS !! i = Some T → gev_reads TS (i, k) a ts →
    ∃ ev, at_evs T !! k = Some ev ∧ (a, ts) ∈ lb_reads (ae_lb ev).
  Proof.
    intros HT (l & Hl & Hin). rewrite /gev_lb /gev_ev /= HT /= in Hl.
    destruct (at_evs T !! k) as [ev|]; simpl in Hl; [|done].
    simplify_eq. by exists ev.
  Qed.

  (** The step at a position, with both agent records. *)
  Lemma step_at i T k ev :
    pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
    ∃ ag ag' f,
      at_ags T !! k = Some ag ∧ at_ags T !! S k = Some ag' ∧
      astep_ok Img Log i ag (ae_lb ev) f (ae_ts ev) ∧
      pa_ws ag' = f (pa_ws ag).
  Proof.
    intros HT Hev.
    destruct (asteps_wf_step pstep Img Log i (at_ags T) (at_evs T) k ev
                (trace_wf i T HT) Hev)
      as (ag & ag' & st' & f & Hag & Hag' & _ & Hok & Heq).
    exists ag, ag', f.
    split_and!; [exact Hag|exact Hag'|exact Hok|by rewrite Heq].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE NON-FORWARDING SIDE CONDITION, as a site fact

      A read of a FOREIGN message is never a forward-bank hit
      ([WeakRobustAcyc.fwd_own_read_unforwarded]); and "foreign" is read
      off the log — or, the shape every call site here has, off the fact
      that the timestamp was fulfilled by a DIFFERENT agent. *)

  Definition foreign_ts (i : agent) (ts : nat) : Prop :=
    ∃ m j, Log !! (ts - 1)%nat = Some m ∧ wm_tid m = Some j ∧ j ≠ i.

  Lemma foreign_ts_unforwarded i l ts :
    foreign_ts i ts → read_unforwarded Log i l ts.
  Proof. intros H. by right. Qed.

  Lemma foreign_ts_of_fulfil i e ts :
    gev_ts TS e = Some ts → e.1 ≠ i → foreign_ts i ts.
  Proof.
    intros Hts Hne.
    destruct (gev_ts_msg pstep TS e ts Hwf Hts) as (base & data & kc & Hm).
    by exists (WMsg base data (Some e.1) kc), e.1.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE A1a: THE ACQUIRE SITE

      A DISCIPLINED read of [ts] is COVERED at every position from the
      discipline point on.  This is [WeakRobustAcyc.atrace_S1]'s first
      two arms, factored out and stated as a [covered] fact instead of
      being consumed against a fulfil — which is what makes it
      composable (A2's hops) and reusable at a LATER plain read (A1's
      [edge_ok] corollary). *)
  Theorem disciplined_covered i T kr k2 evr a ts ag2 :
    pt_trs TS !! i = Some T →
    at_evs T !! kr = Some evr →
    (a, ts) ∈ lb_reads (ae_lb evr) →
    read_unforwarded Log i (ae_lb evr) ts →
    disciplined T kr k2 →
    (kr < k2)%nat →
    at_ags T !! k2 = Some ag2 →
    covered T k2 ts.
  Proof.
    intros HT Hev Hin Hunf Hdisc Hlt Hag2.
    destruct (step_at i T kr evr HT Hev)
      as (ag & agn & f & Hag & Hagn & Hok & Hws).
    have Hfv : fwd_view (pa_ws ag) (lb_aq (ae_lb evr)) a ts = ts.
    { eapply fwd_own_read_unforwarded; [|exact Hunf].
      by eapply (Hfo i T kr ag HT Hag). }
    (* IT SUFFICES to push [ts] into [w_vwNew] at some position ≤ [k2]. *)
    cut (∃ n agm, (n ≤ k2)%nat ∧ at_ags T !! n = Some agm ∧
                  (ts ≤ w_vwNew (pa_ws agm))%nat).
    { intros (n & agm & Hn & Hagm & Hge).
      eapply (covered_pos_mono i T n k2 ts ag2 HT); [|exact Hn|exact Hag2].
      by exists agm. }
    destruct Hdisc as [(ev0 & Hev0 & Haq)
                      |(k0 & ev0 & Hk0 & Hk0' & Hev0 & Hfen)].
    - (* THE AQ ARM: the read itself lands in [w_vwNew]. *)
      assert (ev0 = evr) as -> by congruence.
      exists (S kr), agn. split_and!; [lia|exact Hagn|].
      rewrite Hws.
      eapply (astep_ok_read_vwNew_aq Img Log i ag (ae_lb evr) f (ae_ts evr)
                a ts); [exact Hok|exact Haq|exact Hin].
    - (* THE FENCE ARM: the read lands in [w_vrOld]; the fence ships it. *)
      have Hro : (ts ≤ w_vrOld (pa_ws agn))%nat.
      { rewrite Hws.
        eapply (astep_ok_read_vrOld Img Log i ag (ae_lb evr) f (ae_ts evr)
                  a ts); [exact Hok|exact Hfv|exact Hin]. }
      destruct (ag_at i T k0 ev0 HT Hev0) as (ag0 & Hag0).
      have Hro0 : (ts ≤ w_vrOld (pa_ws ag0))%nat.
      { have Hmono := ws_mono i T (S kr) k0 agn ag0 HT ltac:(lia) Hagn Hag0.
        have := ws_le_vrOld _ _ Hmono. lia. }
      destruct (step_at i T k0 ev0 HT Hev0)
        as (b0 & b1 & f0 & Hb0 & Hb1 & Hok0 & Hws0).
      assert (b0 = ag0) as -> by congruence.
      exists (S k0), b1. split_and!; [lia|exact Hb1|].
      rewrite Hws0. etrans; [exact Hro0|].
      eapply (astep_ok_fence_vwNew Img Log i ag0 (ae_lb ev0) f0 (ae_ts ev0));
        [exact Hok0|exact Hfen].
  Qed.

  (** The bundle-level spelling, with the non-forwarding side condition
      discharged from "the timestamp was fulfilled by somebody else". *)
  Corollary acquire_covered i esrc T kr k2 a ts ag2 :
    esrc.1 ≠ i →
    pt_trs TS !! i = Some T →
    gev_reads TS (i, kr) a ts →
    gev_ts TS esrc = Some ts →
    disciplined T kr k2 →
    (kr < k2)%nat →
    at_ags T !! k2 = Some ag2 →
    covered T k2 ts.
  Proof.
    intros Hne HT Hrd Hts Hdisc Hlt Hag2.
    destruct (gev_reads_at i T kr a ts HT Hrd) as (evr & Hev & Hin).
    eapply (disciplined_covered i T kr k2 evr a ts ag2);
      [exact HT|exact Hev|exact Hin| |exact Hdisc|exact Hlt|exact Hag2].
    apply foreign_ts_unforwarded. by eapply foreign_ts_of_fulfil.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE A1b: THE RELEASE SITE

      [ts] fulfilled at [k1], a [pw ∧ sw] fence at [kf > k1], [ts_s]
      fulfilled at [ks > kf] ⟹ [ts < ts_s].

      The fence is LOAD-BEARING here and only here: a fulfil raises
      [w_vwOld], EXT reads [w_vwNew], and [fence rw,w] is the only thing
      that connects them.  (Contrast [covered_fulfil_lt] below, where the
      incoming order already sits in [w_vwNew] and no fence is needed.) *)
  Theorem release_lt i T k1 kf ks ts ts_s a m :
    pt_trs TS !! i = Some T →
    gev_ts TS (i, k1) = Some ts →
    Log !! (ts - 1)%nat = Some m → is_Some (msg_byte m a) →
    (k1 < kf)%nat →
    (∃ ev, at_evs T !! kf = Some ev ∧ lb_fence_pwsw (ae_lb ev)) →
    (kf < ks)%nat →
    gev_ts TS (i, ks) = Some ts_s →
    (ts < ts_s)%nat.
  Proof.
    intros HT Hts1 Hm Hb Hlt1 (evf & Hevf & Hfen) Hlt2 Htss.
    destruct (gev_ts_at i T k1 ts HT Hts1) as (ev1 & Hev1 & Hts1').
    destruct (gev_ts_at i T ks ts_s HT Htss) as (evs & Hevs & Htss').
    (* the fulfil at [k1] raises [w_vwOld] to [ts] *)
    destruct (step_at i T k1 ev1 HT Hev1)
      as (ag1 & agn1 & f1 & Hag1 & Hagn1 & Hok1 & Hws1).
    rewrite Hts1' in Hok1.
    have Hwo : (ts ≤ w_vwOld (pa_ws agn1))%nat.
    { rewrite Hws1.
      eapply (astep_ok_fulfil_vwOld Img Log i ag1 (ae_lb ev1) f1 ts a m);
        [exact Hok1|exact Hm|exact Hb]. }
    (* … carried to the fence's pre-state … *)
    destruct (step_at i T kf evf HT Hevf)
      as (agf & agnf & ff & Hagf & Hagnf & Hokf & Hwsf).
    have Hwof : (ts ≤ w_vwOld (pa_ws agf))%nat.
    { have Hmono := ws_mono i T (S k1) kf agn1 agf HT ltac:(lia) Hagn1 Hagf.
      have := ws_le_vwOld _ _ Hmono. lia. }
    (* … and shipped into [w_vwNew] by the [pw ∧ sw] fence. *)
    have Hwn : (ts ≤ w_vwNew (pa_ws agnf))%nat.
    { rewrite Hwsf. etrans; [exact Hwof|].
      eapply (astep_ok_fence_vwNew_w Img Log i agf (ae_lb evf) ff
                (ae_ts evf)); [exact Hokf|exact Hfen]. }
    (* EXT at the release store. *)
    destruct (step_at i T ks evs HT Hevs)
      as (ags & agns & fs & Hags & Hagns & Hoks & Hwss).
    rewrite Htss' in Hoks.
    have Hext : (w_vwNew (pa_ws ags) < ts_s)%nat by eapply astep_ok_fulfil_ext.
    have Hmono := ws_mono i T (S kf) ks agnf ags HT ltac:(lia) Hagnf Hags.
    have := ws_le_vwNew _ _ Hmono. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE A2a: THE HOP LEMMA

      Whatever an agent has already got into [w_vwNew] is strictly below
      every timestamp it fulfils afterwards.  EXT plus monotonicity —
      the whole of A2's iteration, and A3's WAW arm. *)
  Theorem covered_fulfil_lt i T k ks ts ts' :
    pt_trs TS !! i = Some T →
    covered T k ts →
    (k ≤ ks)%nat →
    gev_ts TS (i, ks) = Some ts' →
    (ts < ts')%nat.
  Proof.
    intros HT (ag & Hag & Hge) Hle Hts'.
    destruct (gev_ts_at i T ks ts' HT Hts') as (evs & Hevs & Hts'').
    destruct (step_at i T ks evs HT Hevs)
      as (ags & agns & fs & Hags & _ & Hoks & _).
    rewrite Hts'' in Hoks.
    have Hext : (w_vwNew (pa_ws ags) < ts')%nat by eapply astep_ok_fulfil_ext.
    have Hmono := ws_mono i T k ks ag ags HT Hle Hag Hags.
    have := ws_le_vwNew _ _ Hmono. lia.
  Qed.

  (** ONE HOP: an intermediate agent ACQUIRES [tin] and later fulfils
      [tout].  NO release fence is needed — the acquire already landed in
      [w_vwNew].  (A release fence is of course still present in the real
      code; it is what makes the agent's OWN earlier writes visible, and
      that is [release_lt]'s business, not this one's.) *)
  Theorem acquire_release_lt i esrc T kr kd ks tin tout a ag2 :
    esrc.1 ≠ i →
    pt_trs TS !! i = Some T →
    gev_reads TS (i, kr) a tin →
    gev_ts TS esrc = Some tin →
    disciplined T kr kd →
    (kr < kd)%nat → (kd ≤ ks)%nat →
    at_ags T !! kd = Some ag2 →
    gev_ts TS (i, ks) = Some tout →
    (tin < tout)%nat.
  Proof.
    intros Hne HT Hrd Hsrc Hdisc H1 H2 Hag2 Hout.
    eapply (covered_fulfil_lt i T kd ks tin tout HT); [|exact H2|exact Hout].
    by eapply (acquire_covered i esrc T kr kd a tin ag2).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE A2b: CHAINS OF HOPS

      [chain_ok esrc tin hs]: the event [esrc] fulfils [tin], and the
      hops [hs] pass the order on, each acquiring its predecessor's
      timestamp and releasing its own.  [chain_end] names the event and
      timestamp the chain ends at. *)

  Definition hop_ok (esrc : gev) (tin : nat) (h : hop) : Prop :=
    ∃ T ag,
      pt_trs TS !! hp_ag h = Some T ∧
      esrc.1 ≠ hp_ag h ∧
      gev_ts TS esrc = Some tin ∧
      gev_reads TS (hp_ag h, hp_kr h) (hp_a h) tin ∧
      disciplined T (hp_kr h) (hp_kd h) ∧
      (hp_kr h < hp_kd h)%nat ∧ (hp_kd h ≤ hp_ks h)%nat ∧
      at_ags T !! hp_kd h = Some ag ∧
      gev_ts TS (hp_ag h, hp_ks h) = Some (hp_ts h).

  Fixpoint chain_ok (esrc : gev) (tin : nat) (hs : list hop) : Prop :=
    match hs with
    | [] => gev_ts TS esrc = Some tin
    | h :: hs' => hop_ok esrc tin h ∧ chain_ok (hp_ag h, hp_ks h) (hp_ts h) hs'
    end.

  Fixpoint chain_end (esrc : gev) (tin : nat) (hs : list hop) : gev * nat :=
    match hs with
    | [] => (esrc, tin)
    | h :: hs' => chain_end (hp_ag h, hp_ks h) (hp_ts h) hs'
    end.

  Lemma hop_lt esrc tin h : hop_ok esrc tin h → (tin < hp_ts h)%nat.
  Proof.
    intros (T & ag & HT & Hne & Hsrc & Hrd & Hd & H1 & H2 & Hag & Hout).
    by eapply (acquire_release_lt (hp_ag h) esrc T (hp_kr h) (hp_kd h)
                 (hp_ks h) tin (hp_ts h) (hp_a h) ag).
  Qed.

  (** THE ITERATION: the chain's end timestamp is at least the start's
      (strictly above it as soon as there is one hop), and it really is
      the timestamp its end event fulfils. *)
  Lemma chain_lt esrc tin hs :
    chain_ok esrc tin hs →
    (tin ≤ (chain_end esrc tin hs).2)%nat ∧
    gev_ts TS (chain_end esrc tin hs).1 = Some (chain_end esrc tin hs).2.
  Proof.
    revert esrc tin. induction hs as [|h hs IH]; intros esrc tin Hc; simpl.
    - split; [lia|exact Hc].
    - destruct Hc as (Hh & Hrest).
      destruct (IH (hp_ag h, hp_ks h) (hp_ts h) Hrest) as [Hle Hts].
      split; [|exact Hts].
      have := hop_lt esrc tin h Hh. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE A1: COVERAGE FROM ONE RELEASE/ACQUIRE PAIR *)

  Theorem covered_of_release_acquire i j Ti Tj k1 kf ks kr k2
      ts ts_s a1 m a ag2 :
    i ≠ j →
    pt_trs TS !! i = Some Ti →
    pt_trs TS !! j = Some Tj →
    (* the RELEASE site of [i] *)
    gev_ts TS (i, k1) = Some ts →
    Log !! (ts - 1)%nat = Some m → is_Some (msg_byte m a1) →
    (k1 < kf)%nat →
    (∃ ev, at_evs Ti !! kf = Some ev ∧ lb_fence_pwsw (ae_lb ev)) →
    (kf < ks)%nat →
    gev_ts TS (i, ks) = Some ts_s →
    (* the ACQUIRE site of [j] *)
    gev_reads TS (j, kr) a ts_s →
    disciplined Tj kr k2 →
    (kr < k2)%nat →
    at_ags Tj !! k2 = Some ag2 →
    covered Tj k2 ts.
  Proof.
    intros Hne HTi HTj Hts1 Hm Hb Hlt1 Hfen Hlt2 Htss Hrd Hdisc Hlt Hag2.
    have Hlts : (ts < ts_s)%nat
      by eapply (release_lt i Ti k1 kf ks ts ts_s a1 m).
    eapply covered_mono_ts; [|apply (Nat.lt_le_incl _ _ Hlts)].
    eapply (acquire_covered j (i, ks) Tj kr k2 a ts_s ag2);
      [exact Hne|exact HTj|exact Hrd|exact Htss|exact Hdisc|exact Hlt
      |exact Hag2].
  Qed.

  (** THE CONSEQUENCE IN [edge_ok] FORM.  The acquire sits BEFORE the
      reading event [kr] — the shape of a critical-section read, and the
      shape [WeakRobustMain.edges_split] quantifies over: once the
      message is covered AT the read, EVERY later fulfil is fine, with
      no discipline demanded of the read itself. *)
  Corollary edge_ok_of_release_acquire i j Ti Tj k1 kf ks ka kr
      ts ts_s a1 m a agr :
    i ≠ j →
    pt_trs TS !! i = Some Ti →
    pt_trs TS !! j = Some Tj →
    gev_ts TS (i, k1) = Some ts →
    Log !! (ts - 1)%nat = Some m → is_Some (msg_byte m a1) →
    (k1 < kf)%nat →
    (∃ ev, at_evs Ti !! kf = Some ev ∧ lb_fence_pwsw (ae_lb ev)) →
    (kf < ks)%nat →
    gev_ts TS (i, ks) = Some ts_s →
    (* [j]'s ACQUIRE of the release message, po-BEFORE [kr] *)
    gev_reads TS (j, ka) a ts_s →
    disciplined Tj ka kr →
    (ka < kr)%nat →
    at_ags Tj !! kr = Some agr →
    ∀ k', edge_ok Tj kr k' ts.
  Proof.
    intros Hne HTi HTj Hts1 Hm Hb Hlt1 Hfen Hlt2 Htss Hrd Hdisc Hlt Hagr k'.
    apply edge_ok_covered.
    by eapply (covered_of_release_acquire i j Ti Tj k1 kf ks ka kr
                 ts ts_s a1 m a agr).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE A2: COVERAGE THROUGH A CHAIN *)

  (** THE TWO-HOP SPELLING, with no [hop] records: [i] releases, [j]
      acquires and re-releases, [l] acquires. *)
  Corollary covered_of_release_two_hops i j l Ti Tj Tl
      k1 kf ks kr kd kjs kr2 k2 ts ts_s ts_j a1 m a aj agd ag2 :
    i ≠ j → j ≠ l →
    pt_trs TS !! i = Some Ti →
    pt_trs TS !! j = Some Tj →
    pt_trs TS !! l = Some Tl →
    (* [i]'s release site *)
    gev_ts TS (i, k1) = Some ts →
    Log !! (ts - 1)%nat = Some m → is_Some (msg_byte m a1) →
    (k1 < kf)%nat →
    (∃ ev, at_evs Ti !! kf = Some ev ∧ lb_fence_pwsw (ae_lb ev)) →
    (kf < ks)%nat →
    gev_ts TS (i, ks) = Some ts_s →
    (* [j] acquires [ts_s] and later fulfils [ts_j] *)
    gev_reads TS (j, kr) a ts_s →
    disciplined Tj kr kd →
    (kr < kd)%nat → (kd ≤ kjs)%nat →
    at_ags Tj !! kd = Some agd →
    gev_ts TS (j, kjs) = Some ts_j →
    (* [l] acquires [ts_j] *)
    gev_reads TS (l, kr2) aj ts_j →
    disciplined Tl kr2 k2 →
    (kr2 < k2)%nat →
    at_ags Tl !! k2 = Some ag2 →
    covered Tl k2 ts.
  Proof.
    intros Hij Hjl HTi HTj HTl Hts1 Hm Hb Hlt1 Hfen Hlt2 Htss
           Hrd Hdisc H1 H2 Hagd Htsj Hrd2 Hdisc2 H3 Hag2.
    have Hlts : (ts < ts_s)%nat
      by eapply (release_lt i Ti k1 kf ks ts ts_s a1 m).
    have Hltj : (ts_s < ts_j)%nat.
    { eapply (acquire_release_lt j (i, ks) Tj kr kd kjs ts_s ts_j a agd);
        [exact Hij|exact HTj|exact Hrd|exact Htss|exact Hdisc|exact H1
        |exact H2|exact Hagd|exact Htsj]. }
    eapply covered_mono_ts; [|apply (Nat.lt_le_incl _ ts_j); lia].
    eapply (acquire_covered l (j, kjs) Tl kr2 k2 aj ts_j ag2);
      [exact Hjl|exact HTl|exact Hrd2|exact Htsj|exact Hdisc2|exact H3
      |exact Hag2].
  Qed.

  (** THE n-HOP VERSION.  [i] releases [ts_s]; the chain [hs] passes the
      order through arbitrarily many intermediate agents; the final
      agent [j] acquires the chain's end timestamp. *)
  Theorem covered_of_release_chain i j Ti Tj k1 kf ks kr k2
      ts ts_s a1 m a ag2 hs elast tlast :
    i ≠ j →
    pt_trs TS !! i = Some Ti →
    pt_trs TS !! j = Some Tj →
    (* [i]'s release site *)
    gev_ts TS (i, k1) = Some ts →
    Log !! (ts - 1)%nat = Some m → is_Some (msg_byte m a1) →
    (k1 < kf)%nat →
    (∃ ev, at_evs Ti !! kf = Some ev ∧ lb_fence_pwsw (ae_lb ev)) →
    (kf < ks)%nat →
    gev_ts TS (i, ks) = Some ts_s →
    (* the chain of intermediate release/acquire hops *)
    chain_ok (i, ks) ts_s hs →
    chain_end (i, ks) ts_s hs = (elast, tlast) →
    (* [j]'s final acquire *)
    elast.1 ≠ j →
    gev_reads TS (j, kr) a tlast →
    disciplined Tj kr k2 →
    (kr < k2)%nat →
    at_ags Tj !! k2 = Some ag2 →
    covered Tj k2 ts.
  Proof.
    intros Hne HTi HTj Hts1 Hm Hb Hlt1 Hfen Hlt2 Htss Hch Hend Hne'
           Hrd Hdisc Hlt Hag2.
    have Hlts : (ts < ts_s)%nat
      by eapply (release_lt i Ti k1 kf ks ts ts_s a1 m).
    destruct (chain_lt (i, ks) ts_s hs Hch) as [Hle Htsl].
    rewrite Hend /= in Hle. rewrite Hend /= in Htsl.
    eapply covered_mono_ts; [|apply (Nat.lt_le_incl ts tlast); lia].
    eapply (acquire_covered j elast Tj kr k2 a tlast ag2);
      [exact Hne'|exact HTj|exact Hrd|exact Htsl|exact Hdisc|exact Hlt
      |exact Hag2].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE A3: THE THREE ARMS OF [ee_ok]

      Recall the obligation: for an E edge (witnessing read [r], byte
      [a], floor [F = rd_floor TS r a], target [et]) and every fulfil
      [ey] of [et]'s own agent strictly po-after [et], [F < ts(ey)].
      The edge carries [F < t̂] where [t̂] is the timestamp [et] fulfils,
      so each arm only has to get [t̂] — or [F] itself — below [ts(ey)]. *)

  (** ARM (a), FENCE-COVER: a [pw ∧ sw] fence po-between [et] and [ey].
      This is [release_lt] verbatim, at the E edge's own [t̂]; the
      [msg_byte] side condition is [gE_ra]'s [msg_writes] conjunct. *)
  Lemma ee_ok_fence_cover r a e1 et ey y T kf :
    gE_ra TS r a e1 et →
    pt_trs TS !! et.1 = Some T →
    et.1 = ey.1 →
    (et.2 < kf)%nat → (kf < ey.2)%nat →
    (∃ ev, at_evs T !! kf = Some ev ∧ lb_fence_pwsw (ae_lb ev)) →
    gev_ts TS ey = Some y →
    (rd_floor TS r a < y)%nat.
  Proof.
    destruct et as [ie ke], ey as [iy ky]. simpl.
    intros Hra HT <- Hlt1 Hlt2 Hfen Hy.
    destruct Hra
      as (l & ts & tstar & that & _ & _ & _ & _ & _ & Hthat & Hmw & Hfl).
    destruct Hmw as (m & Hm & Hb).
    have Hlt : (that < y)%nat
      by eapply (release_lt ie T ke kf ky that y a m).
    lia.
  Qed.

  (** ARM (b), WAW-COVER: the writer's [w_vwNew] at [et]'s PRE-state was
      already at or above the floor (an ownership transfer the writer had
      itself acquired).  This is [covered_fulfil_lt] verbatim — no use is
      made of the edge beyond naming its target. *)
  Lemma ee_ok_waw_cover r a e1 et ey y T :
    gE_ra TS r a e1 et →
    pt_trs TS !! et.1 = Some T →
    et.1 = ey.1 → (et.2 ≤ ey.2)%nat →
    covered T et.2 (rd_floor TS r a) →
    gev_ts TS ey = Some y →
    (rd_floor TS r a < y)%nat.
  Proof.
    destruct et as [ie ke], ey as [iy ky]. simpl.
    intros _ HT <- Hle Hcov Hy.
    by eapply (covered_fulfil_lt ie T ke ky (rd_floor TS r a) y).
  Qed.

  (** ARM (c), EMPTY FLOOR: a zero floor is below every fulfilled
      timestamp, because fulfilled timestamps are positive. *)
  Lemma ee_ok_zero_floor r a ey y :
    rd_floor TS r a = 0%nat → gev_ts TS ey = Some y →
    (rd_floor TS r a < y)%nat.
  Proof.
    intros Hz Hy. rewrite Hz. by eapply (gev_ts_pos pstep TS).
  Qed.

  (** The three arms, as ONE per-(edge, later fulfil) side condition. *)
  Definition ee_arm (r : gev) (a : Z) (et ey : gev) : Prop :=
    rd_floor TS r a = 0%nat ∨
    (∃ T kf, pt_trs TS !! et.1 = Some T ∧
             (et.2 < kf)%nat ∧ (kf < ey.2)%nat ∧
             ∃ ev, at_evs T !! kf = Some ev ∧ lb_fence_pwsw (ae_lb ev)) ∨
    (∃ T, pt_trs TS !! et.1 = Some T ∧ covered T et.2 (rd_floor TS r a)).

  (** …and the assembly: arm-per-triple gives [WeakRobustAcyc2.ee_ok],
      the premise of [gdep2_acyclic_edges_ok]. *)
  Theorem ee_ok_of_arms :
    (∀ r a e1 et ey y,
       gE_ra TS r a e1 et → et.1 = ey.1 → (et.2 < ey.2)%nat →
       gev_ts TS ey = Some y → ee_arm r a et ey) →
    ee_ok TS.
  Proof.
    intros Harm r a e1 et ey y Hra Hag Hlt Hy.
    destruct (Harm r a e1 et ey y Hra Hag Hlt Hy)
      as [Hz|[(T & kf & HT & H1 & H2 & Hfen)|(T & HT & Hcov)]].
    - by eapply ee_ok_zero_floor.
    - by eapply (ee_ok_fence_cover r a e1 et ey y T kf).
    - eapply (ee_ok_waw_cover r a e1 et ey y T);
        [exact Hra|exact HT|exact Hag|lia|exact Hcov|exact Hy].
  Qed.

End disc.

(* ------------------------------------------------------------------ *)
(** ** What Track B and Track C inherit from this file

    - [disciplined_covered] / [acquire_covered]: "an acquire COVERS
      everything at or below the message it acquired, from the acquire
      on".  The bridge between [WeakRobustAcyc.disciplined] (what the
      racy-read/lock rules deliver) and [WeakRobustAcyc.covered] (what a
      critical-section read needs), and the reason a plain load inside a
      lock never has to be disciplined itself.

    - [release_lt]: the writer-side site fact, "a store, a [fence rw,w],
      a later store ⟹ the timestamps increase".  The ONE place a fence
      is load-bearing on the writer's side.

    - [covered_fulfil_lt] / [acquire_release_lt] / [chain_ok] /
      [chain_end] / [chain_lt]: the hop calculus.  Note the asymmetry the
      proofs expose: passing an ALREADY-ACQUIRED order forward needs no
      fence at all (EXT reads [w_vwNew], where the acquire put it);
      only the ORIGIN hop, whose order sits in [w_vwOld], needs one.

    - [covered_of_release_acquire] / [edge_ok_of_release_acquire] /
      [covered_of_release_two_hops] / [covered_of_release_chain]: A1/A2,
      the [edge_ok] half of [WeakRobustMain.edges_split] for every
      lock/flag-mediated edge, from site facts about the release site and
      the acquire site only.

    - [ee_ok_fence_cover] / [ee_ok_waw_cover] / [ee_ok_zero_floor] /
      [ee_arm] / [ee_ok_of_arms]: A3, [WeakRobustAcyc2.ee_ok] reduced to
      a per-triple choice among three trace-local conditions.

    NOT here: A4 ([ptraces_bytes_ok]), A5 ([dev_epoch_ok]) and A6
    ([bad_wf]) of the design's Track A, and every Track-B export. *)
