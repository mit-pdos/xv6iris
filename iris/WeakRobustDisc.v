(** * WeakRobustDisc.v — COVERAGE FROM RELEASE/ACQUIRE SITE FACTS
      (premise discharge, Track A, items A1–A6)

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

    A4 [excl_byte_of_rmw] / [sw_byte_of_log_single_writer] /
    [handoff_of_sync_chains] / [ptraces_bytes_ok_of_arms]:
    [WeakRobustSer]'s per-byte premises.  The chain's contribution to
    [handoff] is EXACTLY its one order conjunct [tr ≤ t_star]; the four
    structural conjuncts are site facts, and [handoff] demands ONE sync
    byte shared by the two endpoint agents — see the note there.

    A5 [dev_dom] / [dev_epoch_ok_of_dom] / [dev_dom_of_dev_epoch_ok] /
    [dev_epoch_ok_devfree_reader]: the EXACT characterization of
    [WeakRobustOrd.dev_epoch_ok] as a DOMINATION condition, and the
    machine-checked reason it is not dischargeable — see the A5 header
    below.  This is the honest residue of Track A.

    A6 [tc_min] / [bad_wf_of_acyclic] / [bad_wf_of_no_bad]: constructive
    finite-ancestry minimality, and [WeakRobustMain.bad_wf] from
    [gdep3_acyclic] — with the circularity spelled out at the A6 header.

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
                            WeakRobustSer WeakRobustAcyc2 WeakRobustSim
                            WeakRobustMain.

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

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE A4: THE PER-BYTE PREMISES ([WeakRobustSer])

      [ptraces_bytes_ok TS sync] asks, for every byte, one of [sw_byte]
      (single writer), [excl_byte] (rmw-chained) or [handoff] (the
      release/acquire shape) — and, for the SYNC bytes, one of the first
      two only (the stratification note in [WeakRobustSer]'s header: sync
      bytes are closed FIRST, so they may not appeal to [handoff]). *)

  (** (i) EXCLUSIVITY, from the label alone: a byte whose every writing
      event is an [LRmw].  The rmw's read half AUTOMATICALLY covers the
      byte its write half writes — same [base], and [length tvs = length
      data] is a conjunct of [astep_ok]'s [LRmw] arm — so the caller owes
      only "the label is an rmw", never a range calculation. *)
  Definition rmw_written (a : Z) : Prop :=
    ∀ e t, writes_b TS a e t →
      ∃ aq rl base tvs data, gev_lb TS e = Some (LRmw aq rl base tvs data).

  Theorem excl_byte_of_rmw a : rmw_written a → excl_byte TS a.
  Proof.
    intros Hrmw e t Hw. right.
    destruct (Hrmw e t Hw) as (aq & rl & base & tvs & data & Hlb).
    have Hw' := Hw. destruct Hw' as (Hts & m0 & Hm0 & Hb0).
    rewrite /gev_lb in Hlb.
    destruct (gev_ev TS e) as [ev|] eqn:Hev; simpl in Hlb; [|done].
    injection Hlb as Hlbe.
    rewrite /gev_ts Hev /= in Hts.
    destruct (gev_step pstep TS e ev Hwf Hev)
      as (T & ag & ag' & st' & f & HT & Hag & Hag' & _ & Hok & _).
    rewrite Hlbe Hts /= in Hok.
    destruct Hok as (ts' & kc & Hlen & _ & Hlog & _ & _ & _ & _ & Heq).
    injection Heq as <-.
    rewrite Hlog in Hm0. injection Hm0 as <-.
    rewrite /msg_byte /= in Hb0.
    case_bool_decide as Hle; [|by destruct Hb0].
    destruct Hb0 as [v Hv].
    have Hjlt : (Z.to_nat (a - base) < length tvs)%nat.
    { rewrite Hlen. by eapply lookup_lt_Some. }
    have [[tr v'] Htv] : is_Some (tvs !! Z.to_nat (a - base))
      by apply lookup_lt_is_Some_2.
    exists tr, (LRmw aq rl base tvs data).
    split; [by rewrite /gev_lb Hev /= Hlbe|].
    simpl. apply elem_of_tvs_reads.
    exists (Z.to_nat (a - base)), v'. split; [exact Htv|].
    rewrite Z2Nat.id; lia.
  Qed.

  (** (ii) SINGLE WRITER, from the LOG: every message that writes the
      byte is authored by one agent.  (Stated on the log rather than on
      the events because that is the form an ownership argument produces,
      and because [writes_b]'s author IS the message's [wm_tid] —
      [WeakRobustSer.writes_b_author].) *)
  Definition log_single_writer (a : Z) (i : agent) : Prop :=
    ∀ t m, Log !! (t - 1)%nat = Some m → is_Some (msg_byte m a) →
      wm_tid m = Some i.

  Theorem sw_byte_of_log_single_writer a i :
    log_single_writer a i → sw_byte TS a.
  Proof.
    intros H e1 e2 t1 t2 Hw1 Hw2.
    destruct (writes_b_author pstep TS a e1 t1 Hwf Hw1)
      as (m1 & Hm1 & Hb1 & Ht1).
    destruct (writes_b_author pstep TS a e2 t2 Hwf Hw2)
      as (m2 & Hm2 & Hb2 & Ht2).
    have E1 := H t1 m1 Hm1 Hb1. have E2 := H t2 m2 Hm2 Hb2.
    rewrite Ht1 in E1. rewrite Ht2 in E2. by simplify_eq.
  Qed.

  (** (iii) HANDOFF, from release/acquire CHAINS.

      READ [handoff] CAREFULLY BEFORE READING THIS.  It demands, for a
      cross-author co-consecutive pair, ONE sync byte [b] written by
      [e1]'s OWN agent at or po-after [e1] and read by [e2]'s OWN agent
      at or po-before [e2], at a timestamp [t_star ≥ tr].  It demands NO
      fence, NO discipline and NO coverage: the ordering content is
      entirely in the single inequality [tr ≤ t_star].

      THE CHAIN'S JOB IS EXACTLY THAT INEQUALITY.  Intermediate agents
      may re-release [b] (or any byte) any number of times; [chain_lt]
      says the chain's END timestamp is at least its START timestamp,
      because each hop ACQUIRED its predecessor's timestamp and then
      fulfilled strictly above it ([acquire_release_lt], i.e. coverage
      plus EXT).  So the reader may read a much later value of [b] and
      the handoff still holds.

      WHAT THE CHAIN DOES *NOT* GIVE: the four STRUCTURAL conjuncts
      ([sync b], [writes_b TS b er tr], the two agent identities and the
      two po bounds).  Those are pure site facts about the release and
      acquire instructions and must come from Track B.  In particular
      [handoff] insists that the SAME byte [b] be written by [e1]'s agent
      and read by [e2]'s agent, so a chain that routes through a
      DIFFERENT sync byte at each hop does not instantiate it — the
      endpoints' byte is the one that must be shared. *)
  Theorem handoff_of_sync_chains (sync : Z → Prop) a :
    (∀ e1 e2 t1 t2,
       writes_b TS a e1 t1 → writes_b TS a e2 t2 →
       e1.1 ≠ e2.1 → (t1 < t2)%nat → co_consec TS a t1 t2 →
       ∃ b er tr hs elast tlast rr t_star,
         sync b ∧
         writes_b TS b er tr ∧ er.1 = e1.1 ∧ (e1.2 ≤ er.2)%nat ∧
         chain_ok er tr hs ∧ chain_end er tr hs = (elast, tlast) ∧
         gev_reads TS rr b t_star ∧ rr.1 = e2.1 ∧ (rr.2 ≤ e2.2)%nat ∧
         (tlast ≤ t_star)%nat) →
    handoff TS sync a.
  Proof.
    intros Hsite e1 e2 t1 t2 Hw1 Hw2 Hne Hlt Hcc.
    destruct (Hsite e1 e2 t1 t2 Hw1 Hw2 Hne Hlt Hcc)
      as (b & er & tr & hs & elast & tlast & rr & t_star &
          Hsync & Her & Hag1 & Hpo1 & Hch & Hend & Hrr & Hag2 & Hpo2 & Hle).
    destruct (chain_lt er tr hs Hch) as [Hchle _].
    rewrite Hend /= in Hchle.
    exists b, er, tr, rr, t_star.
    split_and!; [done|done|done|done|done|done|done|lia].
  Qed.

  (** THE ZERO-HOP INSTANCE, spelled out: a DIRECT release/acquire needs
      no chain at all, because [chain_ok er tr []] is just "[er] fulfils
      [tr]", which [writes_b] already says. *)
  Corollary handoff_of_direct_sync (sync : Z → Prop) a :
    (∀ e1 e2 t1 t2,
       writes_b TS a e1 t1 → writes_b TS a e2 t2 →
       e1.1 ≠ e2.1 → (t1 < t2)%nat → co_consec TS a t1 t2 →
       ∃ b er tr rr t_star,
         sync b ∧
         writes_b TS b er tr ∧ er.1 = e1.1 ∧ (e1.2 ≤ er.2)%nat ∧
         gev_reads TS rr b t_star ∧ rr.1 = e2.1 ∧ (rr.2 ≤ e2.2)%nat ∧
         (tr ≤ t_star)%nat) →
    handoff TS sync a.
  Proof.
    intros Hsite. apply handoff_of_sync_chains.
    intros e1 e2 t1 t2 Hw1 Hw2 Hne Hlt Hcc.
    destruct (Hsite e1 e2 t1 t2 Hw1 Hw2 Hne Hlt Hcc)
      as (b & er & tr & rr & t_star &
          Hsync & Her & Hag1 & Hpo1 & Hrr & Hag2 & Hpo2 & Hle).
    exists b, er, tr, [], er, tr, rr, t_star.
    split_and!; [done|done|done|done| |done|done|done|done|done].
    by destruct Her.
  Qed.

  (** …and the packaging [ptraces_bytes_ok] wants. *)
  Theorem ptraces_bytes_ok_of_arms (sync : Z → Prop) :
    (∀ b, sync b → sw_byte TS b ∨ excl_byte TS b) →
    (∀ a, sw_byte TS a ∨ excl_byte TS a ∨ handoff TS sync a) →
    ptraces_bytes_ok TS sync.
  Proof. intros H1 H2. split; [exact H1|exact H2]. Qed.

End disc.

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE A5: [dev_epoch_ok] — WHAT IT ACTUALLY DEMANDS

    [WeakRobustOrd.depoch DS e] is the witness position just past the
    LAST fabric-touching event OF [e]'S OWN AGENT at or before [e] in
    that agent's trace (0 if that agent has touched the fabric not at
    all before [e]).  [dev_epoch_ok TS DS] says no [grf] and no [gE]
    edge LOWERS it.

    THE EXACT CONTENT, machine-checked below as an IFF ([dev_dom] /
    [depoch_le_of_dom] / [dom_of_depoch_le]): [dev_epoch_ok] is a
    DOMINATION condition, not an ordering one.  Per edge [e1 → e2] it
    says

      every fabric access of the WRITER's agent po-before [e1] is
      matched by a fabric access of the READER's agent po-before [e2]
      at a witness index that is at least as large.

    TWO CONSEQUENCES, both proved below.

    (1) It is not about promise reads.  [dev_epoch_ok_devfree_reader]:
        if the READER's agent has made no fabric access before its read,
        the premise FORCES the writer's agent to have made none before
        its write.  So the completely ordinary, promise-free, SC-looking
        bundle

          agent A:  <fabric access>  ;  store x = 1
          agent B:  load x  (reads 1)

        already falsifies [dev_epoch_ok] — the rf edge is forward in
        real time, nothing is read early, and yet [depoch] drops from 1
        to 0.  The recorded G5a counterexample (a promise read across a
        device epoch) is therefore not the only failure mode, and not
        the smallest one.

    (2) Coverage cannot help.  A1/A2 constrain TIMESTAMPS; the missing
        ingredient here is EXISTENTIAL — the reader must HAVE a fabric
        access — and no amount of release/acquire discipline creates
        one.  Neither does a real-time embedding: even under the
        (refuted) W7 hypothesis "every rf edge is forward in behavior
        time", the reader may simply never touch the fabric.

    WHAT WOULD DISCHARGE IT, exactly: [dev_dom] at every rf/gE edge.
    That is a real condition on xv6 only if every agent that READS a
    message written after a fabric access has itself performed at least
    as many fabric accesses — e.g. if every fabric access sits inside a
    critical section of one device lock AND every cross-agent flow out
    of a fabric-touching agent passes through that same lock, with the
    reader's own fabric access inside its own critical section BEFORE
    the read.  The disk agent breaks even that: its acquire read of
    [avail->idx] is po-AFTER its fabric-read start event, so for an
    edge INTO that read the reader (the disk) does have an earlier
    fabric access — but for an edge OUT of the disk into a hart that has
    never touched the fabric, the domination fails outright.

    HONEST CONCLUSION: A5 is NOT dischargeable as stated, and the
    obstruction is in the DEFINITION of [depoch] (per-agent), not in the
    bundle.  The two natural repairs are (a) rank by a GLOBAL device
    counter that every event inherits along [gdep3] rather than by the
    agent's own last access, or (b) replace the rank argument for
    [gdep3]-acyclicity altogether.  Both are changes to
    [WeakRobustOrd], hence out of scope for this file; what is in scope
    is the precise statement of the obligation, which is what follows. *)

Section devepoch.
  Context {P D : Type}.
  Context (TS : ptraces P D).

  Implicit Types DS : pdevs D.

  (** The witness position that ACHIEVES the epoch, when it is nonzero.
      ([WeakRobustOrd] proves the lower bound [depoch_lb] and the
      listed-event value [depoch_dev]; the WITNESSING form — the upper
      bound in existential shape — is what the characterization needs
      and is not there.) *)
  Lemma dep_go_witness l e m :
    dep_go l e m = 0%nat ∨
    ∃ i e', l !! i = Some e' ∧ e'.1 = e.1 ∧ (e'.2 ≤ e.2)%nat ∧
            dep_go l e m = S (m + i).
  Proof.
    revert m. induction l as [|x l IH]; intros m; [by left|].
    simpl. case_bool_decide as Hb.
    - destruct (IH (S m)) as [Hz|(i & e' & Hi & Hag & Hle & Heq)].
      + right. exists 0%nat, x. destruct Hb as [Hagx Hlex].
        split_and!; [done|done|done|]. rewrite Hz. lia.
      + right. exists (S i), e'. split_and!; [done|done|done|].
        rewrite Heq. lia.
    - destruct (IH (S m)) as [Hz|(i & e' & Hi & Hag & Hle & Heq)].
      + left. rewrite Hz. lia.
      + right. exists (S i), e'. split_and!; [done|done|done|].
        rewrite Heq. lia.
  Qed.

  Lemma depoch_witness DS e :
    depoch DS e = 0%nat ∨
    ∃ m e', pd_ord DS !! m = Some e' ∧ e'.1 = e.1 ∧ (e'.2 ≤ e.2)%nat ∧
            depoch DS e = S m.
  Proof.
    rewrite /depoch.
    destruct (dep_go_witness (pd_ord DS) e 0%nat)
      as [Hz|(i & e' & Hi & Hag & Hle & Heq)]; [by left|].
    right. exists i, e'. split_and!; [done|done|done|]. rewrite Heq. lia.
  Qed.

  (** THE DOMINATION CONDITION: [e2]'s agent's fabric history dominates
      [e1]'s, position by position, in the witness order. *)
  Definition dev_dom DS (e1 e2 : gev) : Prop :=
    ∀ m ep, pd_ord DS !! m = Some ep → ep.1 = e1.1 → (ep.2 ≤ e1.2)%nat →
      ∃ m' ep', pd_ord DS !! m' = Some ep' ∧ ep'.1 = e2.1 ∧
                (ep'.2 ≤ e2.2)%nat ∧ (m ≤ m')%nat.

  Lemma depoch_le_of_dom DS e1 e2 :
    dev_dom DS e1 e2 → (depoch DS e1 ≤ depoch DS e2)%nat.
  Proof.
    intros Hd.
    destruct (depoch_witness DS e1) as [Hz|(m & ep & Hm & Hag & Hle & Heq)];
      [rewrite Hz; lia|].
    destruct (Hd m ep Hm Hag Hle) as (m' & ep' & Hm' & Hag' & Hle' & Hmm).
    have := depoch_lb DS e2 m' ep' Hm' Hag' Hle'. lia.
  Qed.

  Lemma dom_of_depoch_le DS e1 e2 :
    (depoch DS e1 ≤ depoch DS e2)%nat → dev_dom DS e1 e2.
  Proof.
    intros Hle m ep Hm Hag Hlp.
    have Hlb := depoch_lb DS e1 m ep Hm Hag Hlp.
    destruct (depoch_witness DS e2) as [Hz|(m' & ep' & Hm' & Hag' & Hle' & Heq)];
      [lia|].
    exists m', ep'. split_and!; [done|done|done|lia].
  Qed.

  (** THE CHARACTERIZATION, both directions. *)
  Theorem dev_epoch_ok_of_dom DS :
    (∀ e1 e2, (grf TS e1 e2 ∨ gE TS e1 e2) → dev_dom DS e1 e2) →
    dev_epoch_ok TS DS.
  Proof. intros H e1 e2 He. by apply depoch_le_of_dom, H. Qed.

  Theorem dev_dom_of_dev_epoch_ok DS :
    dev_epoch_ok TS DS →
    ∀ e1 e2, (grf TS e1 e2 ∨ gE TS e1 e2) → dev_dom DS e1 e2.
  Proof. intros H e1 e2 He. by apply dom_of_depoch_le, H. Qed.

  (** THE FAILURE MODE, machine-checked: a reader with no fabric history
      forces the writer to have none either. *)
  Corollary dev_epoch_ok_devfree_reader DS e1 e2 :
    dev_epoch_ok TS DS → (grf TS e1 e2 ∨ gE TS e1 e2) →
    depoch DS e2 = 0%nat → depoch DS e1 = 0%nat.
  Proof. intros H He Hz. have := H e1 e2 He. lia. Qed.

  (** THE ONE ARM THAT IS FREE (besides the empty witness): if no edge
      SOURCE has a fabric access behind it, there is nothing to
      dominate. *)
  Theorem dev_epoch_ok_of_devfree_sources DS :
    (∀ e1 e2, (grf TS e1 e2 ∨ gE TS e1 e2) → depoch DS e1 = 0%nat) →
    dev_epoch_ok TS DS.
  Proof. intros H e1 e2 He. rewrite (H e1 e2 He). lia. Qed.

End devepoch.

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE A6: [bad_wf] FROM FINITE ANCESTRY

    [WeakRobustMain.bad_wf]: whenever a bad edge exists, SOME bad edge's
    target is [bad_min] — no bad edge's target is a strict
    [tc (gdep3)]-ancestor of it.  That is exactly "the bad targets have
    a [tc gdep3]-minimal element", and over a FINITE event set an
    acyclic relation has minimal elements.

    THE GENERIC MACHINERY, constructive.  [WeakRobustMain]'s [anc] is a
    COMPUTED ancestor list (no [Decision (tc R)] needed), so
    [length (anc R carrier x)] is a legitimate measure: it strictly
    decreases along [tc R] ([anc_mu_lt]) as soon as [tc R] is
    irreflexive.  Strong induction on that measure then produces the
    minimal element — CONSTRUCTIVELY, but only for a DECIDABLE predicate
    [Q]: "is there a [Q]-element strictly below me" has to be answered,
    and over a finite carrier that is a decidable [Exists].

    THE CIRCULARITY, stated plainly.  [gdep3_acyclic TS DS] is what
    [WeakRobustMain.robust_main] is trying to establish, and it
    establishes it THROUGH [bad_wf] (pick a minimal bad edge, replay its
    cone, refute it with φ).  So [bad_wf_of_acyclic] cannot be used to
    remove [bad_wf] from [main_premises]: it says only that [bad_wf] is
    free for a bundle already known acyclic on independent grounds.  The
    two situations where that is genuinely useful:
      - a bundle satisfying the STRONG per-edge premise [rf_edges_ok]
        (plus [ee_ok], [dev_epoch_ok]) has no bad edges at all, and then
        [bad_wf] is vacuous — [bad_wf_of_no_bad];
      - a re-derivation of [main_premises] for a bundle whose acyclicity
        was obtained by [gdep2_acyclic_edges_ok] + [gdep3_acyclic_epoch].

    WHAT AN INDEPENDENT ARGUMENT WOULD HAVE TO LOOK LIKE.  [bad_wf] is
    morally "the bad-target ancestry is well-founded".  Acyclicity is the
    only bundle-level fact that gives it generically, so an independent
    argument must supply a WELL-FOUNDED MEASURE that strictly decreases
    along a [gdep3] path FROM one bad target TO another.  Neither
    Layer-1 measure works: [WeakRobustAcyc2.mile_mu_gain] needs
    [rf_edges_ok]/[ee_ok] at every milestone, and a bad edge is exactly
    a milestone where they fail.  The measure therefore has to come from
    the OWNERSHIP structure ("ownership only ever transfers through
    synchronization", the design's own justification): a rank on
    owned-unpublished messages that drops at every ownership transfer.
    That is a Track-B/C fact about the kernel, not a Layer-1 theorem. *)

Section wfmin.
  Context {A : Type} `{!EqDecision A}.
  Context (R : A → A → Prop) `{!RelDecision R}.
  Context (carrier : list A).
  Context (Hcar : ∀ x y, R x y → x ∈ carrier).
  Context (Hnd : NoDup carrier).
  Context (Hacyc : ∀ x, ¬ tc R x x).

  Lemma anc_sub x y :
    x ∈ carrier → y ∈ carrier → tc R y x →
    ∀ z, z ∈ anc R carrier y → z ∈ anc R carrier x.
  Proof.
    intros Hx Hy Htc z Hz.
    apply (elem_of_anc R carrier y Hy Hcar Hnd) in Hz as [->|Hzy];
      apply (elem_of_anc R carrier x Hx Hcar Hnd); right; [done|].
    by eapply tc_transitive.
  Qed.

  Lemma anc_mu_lt x y :
    x ∈ carrier → y ∈ carrier → tc R y x →
    (length (anc R carrier y) < length (anc R carrier x))%nat.
  Proof.
    intros Hx Hy Htc.
    have Hxnin : x ∉ anc R carrier y.
    { intros Hin.
      apply (elem_of_anc R carrier y Hy Hcar Hnd) in Hin as [Heq|Hxy].
      - subst. by eapply Hacyc; exact Htc.
      - apply (Hacyc x). eapply tc_transitive; [exact Hxy|exact Htc]. }
    have Hnd' : NoDup (x :: anc R carrier y).
    { apply list_relations.NoDup_cons. split; [exact Hxnin|].
      apply (anc_iter_nodup R carrier y Hnd). }
    have Hle : (length (x :: anc R carrier y)
                ≤ length (anc R carrier x))%nat.
    { apply list_relations.submseteq_length,
            list_relations.NoDup_submseteq; [exact Hnd'|].
      intros z Hz. apply elem_of_cons in Hz as [->|Hz].
      - apply (elem_of_anc R carrier x Hx Hcar Hnd). by left.
      - by eapply anc_sub. }
    simpl in Hle. lia.
  Qed.

  (** THE MINIMAL ELEMENT.  [Q] must be decidable: the search "is some
      [Q]-element strictly below me" is what the induction step answers,
      and there is no constructive way around it. *)
  Theorem tc_min (Q : A → Prop) `{!∀ x, Decision (Q x)} :
    (∀ x, Q x → x ∈ carrier) →
    ∀ x, Q x → ∃ y, Q y ∧ ∀ z, Q z → ¬ tc R z y.
  Proof.
    intros HQc.
    have Hgen : ∀ n x, Q x → (length (anc R carrier x) ≤ n)%nat →
                  ∃ y, Q y ∧ ∀ z, Q z → ¬ tc R z y.
    { induction n as [|n IH]; intros x Hx Hmu.
      - exfalso.
        have Hin : x ∈ anc R carrier x by apply root_in_anc.
        destruct (anc R carrier x) as [|u l];
          [by apply elem_of_nil in Hin|simpl in Hmu; lia].
      - destruct (decide (Exists (λ z, Q z ∧ z ∈ anc R carrier x ∧ z ≠ x)
                            carrier)) as [Hex|Hnex].
        + apply list_relations.Exists_exists in Hex
            as (z & Hzc & HQz & Hzanc & Hzne).
          have Htc : tc R z x.
          { apply (elem_of_anc R carrier x (HQc x Hx) Hcar Hnd) in Hzanc
              as [->|?]; [done|done]. }
          apply (IH z HQz).
          have := anc_mu_lt x z (HQc x Hx) (HQc z HQz) Htc. lia.
        + exists x. split; [exact Hx|]. intros z HQz Htc.
          apply Hnex, list_relations.Exists_exists. exists z.
          split_and!; [by apply HQc|exact HQz| |].
          * apply (elem_of_anc R carrier x (HQc x Hx) Hcar Hnd). by right.
          * intros Heq. rewrite Heq in Htc.
            by eapply Hacyc; exact Htc. }
    intros x Hx. by eapply (Hgen (length (anc R carrier x))).
  Qed.

End wfmin.

Section badwf.
  Context {P D : Type}.
  Context (TS : ptraces P D).
  Context (DS : pdevs D).

  (** "[e] is the TARGET of some bad edge" — the predicate [bad_min]
      quantifies over. *)
  Definition bad_target (nh : nat) (e : gev) : Prop :=
    ∃ f1, bad nh TS DS f1 e.

  (** No bad edges at all ⟹ [bad_wf] vacuously.  (This is the shape a
      bundle satisfying the STRONG [rf_edges_ok] is in.) *)
  Lemma bad_wf_of_no_bad nh :
    (∀ e1 e2, ¬ bad nh TS DS e1 e2) → bad_wf nh TS DS.
  Proof. intros H e1 e2 Hb. by destruct (H e1 e2 Hb). Qed.

  (** …and the finite-ancestry derivation.  Note what it consumes:
      [gdep3_acyclic], which is the CONCLUSION of the theorem [bad_wf] is
      a premise of — see the header's circularity note. *)
  Theorem bad_wf_of_acyclic nh :
    ptraces_wit TS DS →
    gdep3_acyclic TS DS →
    (∀ e, Decision (bad_target nh e)) →
    bad_wf nh TS DS.
  Proof.
    intros Hwit Hacyc Hdec e1 e2 Hbad.
    have Hcar : ∀ x y, gdep3 TS DS x y → x ∈ gev_enum TS.
    { intros x y Hd. apply elem_of_gev_enum.
      by destruct (gdep3_wf TS DS x y Hwit Hd). }
    have HQc : ∀ e, bad_target nh e → e ∈ gev_enum TS.
    { intros e (f1 & Hb). apply elem_of_gev_enum.
      destruct Hb as ((ts & a & _ & Hrd) & _). by eapply gev_reads_wf. }
    destruct (tc_min (gdep3 TS DS) (gev_enum TS) Hcar (NoDup_gev_enum TS)
                Hacyc (bad_target nh) HQc e2 (ex_intro _ e1 Hbad))
      as (y & (g1 & Hg) & Hmin).
    exists g1, y. split; [exact Hg|].
    intros f1 f2 Hb Htc. eapply (Hmin f2); [by exists f1|exact Htc].
  Qed.

End badwf.

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

    - [rmw_written] / [excl_byte_of_rmw], [log_single_writer] /
      [sw_byte_of_log_single_writer], [handoff_of_sync_chains] /
      [handoff_of_direct_sync] / [ptraces_bytes_ok_of_arms]: A4, the
      per-byte premises of [WeakRobustSer].  The rmw arm asks the caller
      only for "the label is an [LRmw]" — the byte-range calculation is
      done here.  The handoff arm splits cleanly: the CHAIN discharges
      the order conjunct [tr ≤ t_star] (through [chain_lt], i.e.
      coverage plus EXT at every hop), the four structural conjuncts are
      Track-B site facts, and the endpoints' sync byte must be shared.

    - [dev_dom] / [dev_epoch_ok_of_dom] / [dev_dom_of_dev_epoch_ok] /
      [dev_epoch_ok_devfree_reader] / [dev_epoch_ok_of_devfree_sources]:
      A5.  NOT a discharge — a characterization plus a refutation.  The
      finding, in one line: [dev_epoch_ok] forces the READER to have a
      fabric history at least as long as the WRITER's, which ordinary
      promise-free bundles violate.

    - [tc_min] (generic, constructive) and [anc_mu_lt]: an acyclic
      relation over a finite carrier has minimal elements of any
      DECIDABLE predicate, measured by [WeakRobustMain.anc]'s computed
      ancestor list.  [bad_wf_of_acyclic] / [bad_wf_of_no_bad]: A6, with
      the circularity note at its header.

    NOT here: every Track-B export (the site facts these lemmas
    consume), and Track C's composition. *)
