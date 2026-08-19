(** * WeakRobustTrace.v — the TRACED form of a factorized behavior
      (M6 W2a, step 1)

    [WeakPromiseFact.v] delivers the state phase of a lat-free behavior as
    [rtc]s: [wp_phases] is agent 0's whole run, then agent 1's, …, each
    against the frozen log.  An [rtc] ERASES EVENT IDENTITY — which agent
    did what, in what per-agent order, reading which timestamps, fulfilling
    which promise — and event identity is exactly what the Layer-1
    dependency graph (W2a step 2) is built out of.  This file re-presents
    the same state phase as EXPLICIT PER-AGENT TRACES and proves the
    extraction (and the converse replay, for rebuilding runs after graph
    surgery).

    THE TRACE.  Agent [i]'s phase becomes a pair of lists: [at_evs], one
    [aev] per step, and [at_ags], the [S (length at_evs)] agent records the
    steps pass through (so position [k]'s step goes from [at_ags !! k] to
    [at_ags !! S k] emitting [at_evs !! k]).  An event is a LABEL plus the
    FULFILLED TIMESTAMP:

      Record aev := AEv { ae_lb : wlabel; ae_ts : option nat }.

    [ae_ts] is not derivable from the label and MUST be recorded: two log
    positions can hold identical messages [WMsg base data (Some i)], so a
    store label does not determine which promise it consumed — and the
    graph's fulfil→read edges are edges between LOG POSITIONS.

    WHY THE WF CONDITION IS ONE LINE PER STEP.  [WeakPromiseFact]'s
    [astep_ok img log i ag l f Dl] already collects the five state rules'
    side conditions by label, pinning BOTH the [wstate] update [f] and the
    deleted promise [Dl] as functions of the label; [ae_ts] is exactly that
    [Dl].  So [atrace_wf] says, per position: the program steps on the
    label, [astep_ok] holds, and the next agent record is the one
    [wp_astep] would build.  In particular [ae_ts] is FORCED to [None] on
    non-store labels by [astep_ok]'s shape — proved once as
    [atrace_ts_none] rather than duplicated as a wf conjunct.

    DELIVERABLE 4 (fulfilment accounting) IS PROVED:
    [wp_behavior_fulfil_once] — in a traced behavior, every log position
    authored by agent [i] is fulfilled EXACTLY ONCE across agent [i]'s
    trace.  Existence comes from the promise phase ([prom_complete]: an
    authored message's timestamp is in its author's promise set) plus
    [no_promises] at the end; uniqueness from the fact that promise sets
    only SHRINK along a trace and a fulfil deletes its own timestamp.

    DEPENDENCY-FREE like its parents: stdpp, [WeakMem], [WeakPromise],
    [WeakPromiseFact]. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Events and traces *)

(** One state step of one agent: the label it emitted, and the timestamp
    it fulfilled (for [LStore]/[LRmw]; [None] otherwise). *)
(** [ae_dev] is the DEVICE-FABRIC field, and it is also the fabric-touching
    MARKER: [None] says the step is dev-free (it runs at EVERY fabric and
    leaves it alone), [Some (din, dout)] says it read the fabric at [din]
    and left it at [dout].  A dev-flagged event is exactly a node of the
    global device-order witness ([pdevs] below).

    WHY THE FABRIC LIVES HERE and not in the witness: [atrace_wf] must stay
    a SELF-CONTAINED statement about one agent's trace — every downstream
    consumer ([WeakRobustGraph], [WeakRobustSim], …) checks it per agent,
    against the frozen [(img, log)], with no access to the witness.  The
    witness then carries only the ORDER, which is precisely what G3's gdev
    edges consume, and the design kernel's fold reading survives verbatim:
    the fabric at witness position [m] is the [dout] of entry [m-1]
    ([dev_at] below). *)
Record aev (D : Type) := AEv {
  ae_lb  : wlabel;
  ae_ts  : option nat;
  ae_dev : option (D * D);
}.
Add Printing Constructor aev.
Global Arguments AEv {D} _ _ _.
Global Arguments ae_lb {D} _.
Global Arguments ae_ts {D} _.
Global Arguments ae_dev {D} _.

(** One agent's whole state phase.  [at_ags] has one more entry than
    [at_evs]: the records BEFORE each step, plus the final one. *)
Record atrace (P D : Type) := ATr {
  at_ags : list (wpagent P);
  at_evs : list (aev D);
}.
Add Printing Constructor atrace.
Global Arguments ATr {P D} _ _.
Global Arguments at_ags {P D} _.
Global Arguments at_evs {P D} _.

(** The whole state phase: one trace per agent (index = agent), all
    against the same frozen [(img, log)]. *)
Record ptraces (P D : Type) := PTrs {
  pt_img : image;
  pt_log : list wmsg;
  pt_trs : list (atrace P D);
}.
Add Printing Constructor ptraces.
Global Arguments PTrs {P D} _ _ _.
Global Arguments pt_img {P D} _.
Global Arguments pt_log {P D} _.
Global Arguments pt_trs {P D} _.

(* ------------------------------------------------------------------ *)
(** ** THE MESSAGE CLASS OF A TRACED BUNDLE (G6a)

    [WeakPromiseBridge.wp_pf_step] now PINS the class of the message a
    store/rmw appends to [pcls p l ws] at the fulfilling agent's own
    [wstate].  The replay ([WeakRobustSim]) rebuilds pf steps from a traced
    behavior, so it owes that equation at every store it replays, and the
    two halves of the obligation live here because they are statements
    about [ptraces] and about [pcls] alone:

    - [cls_canonical clsf TS] — the RECORDED side: every logged message
      carries the class [clsf] computes at its fulfil event's PRE-record
      agent state — both halves of it, the program state [pa_st ag] and
      the [wstate] [pa_ws ag].  (Moved here from [WeakRetag], which proves
      that every bundle can be brought into this form by retagging —
      [wm_ak] is inert, so the retag moves neither [prog_of] nor
      [mem_of].)

    - [pcls_obl clsf] — the REPLAYED side: the replay hands the same
      events at PERMUTED timestamps, so the class function must not look
      at any timestamp.  It may look at the label's non-timestamp data and
      at [w_relp], which is the only [wstate] field the fold computes from
      labels alone ([WeakRobustProv.w_relp_aevs_post_indep]).  This is the
      exact analogue of [WeakRobustSim.ts_oblivious] for [pstep], and
      [WeakSailLTS2.lbl_class] satisfies it. *)

Definition cls_canonical {P D : Type}
    (clsf : P → wlabel → wstate → wm_class) (TS : ptraces P D) : Prop :=
  ∀ i T k ev ag ts m,
    pt_trs TS !! i = Some T →
    at_evs T !! k = Some ev → at_ags T !! k = Some ag →
    ae_ts ev = Some ts → pt_log TS !! (ts - 1)%nat = Some m →
    wm_ak m = clsf (pa_st ag) (ae_lb ev) (pa_ws ag).

(** The obliviousness half is stated for EACH FIXED program state [p]: the
    replay hands the acting agent its RECORDED [pa_st] verbatim, so the
    program argument is never the thing that moves — only the timestamps
    are. *)
Definition pcls_obl {P : Type} (clsf : P → wlabel → wstate → wm_class)
    : Prop :=
  (∀ p rl base data asrc vsrc ws ws', w_relp ws = w_relp ws' →
     clsf p (LStore rl base data asrc vsrc) ws
     = clsf p (LStore rl base data asrc vsrc) ws') ∧
  (∀ p aq rl base tvs tvs' data asrc vsrc ws ws',
     tvs.*2 = tvs'.*2 → w_relp ws = w_relp ws' →
     clsf p (LRmw aq rl base tvs data asrc vsrc) ws
     = clsf p (LRmw aq rl base tvs' data asrc vsrc) ws').

(** THE GLOBAL DEVICE-ORDER WITNESS.  [pd_init] is the fabric the state
    phase starts at ([pc_dev mid]); [pd_ord] lists, IN BEHAVIOR ORDER,
    every fabric-touching step as the pair (acting agent, index of that
    step in that agent's trace).  It is a pure ORDER on trace positions —
    no fabric values — because the fabric each listed step reads and
    leaves is recorded on its own event; [dev_at] is the fold that ties
    the two together. *)
Record pdevs (D : Type) := PDevs {
  pd_init : D;
  pd_ord  : list (agent * nat);
}.
Add Printing Constructor pdevs.
Global Arguments PDevs {D} _ _.
Global Arguments pd_init {D} _.
Global Arguments pd_ord {D} _.

(** A finite family of existentials collects into a list.  (Used once, to
    turn the per-agent extraction into [ptraces]; nothing here is
    classical — the list is built by recursion on [n].) *)
Lemma list_ex_of_index {A} (Φ : nat → A → Prop) n :
  (∀ i, (i < n)%nat → ∃ x, Φ i x) →
  ∃ xs, length xs = n ∧ ∀ i x, xs !! i = Some x → Φ i x.
Proof.
  induction n as [|n IH]; intros HΦ.
  - exists []. split; [done|]. intros i x Hx. by rewrite lookup_nil in Hx.
  - destruct IH as (xs & Hlen & Hxs); [intros i Hi; apply HΦ; lia|].
    destruct (HΦ n ltac:(lia)) as (x & Hx).
    exists (xs ++ [x]). split; [rewrite length_app /=; lia|].
    intros i y Hy.
    destruct (decide (i < n)%nat) as [Hlt|Hge].
    + rewrite lookup_app_l in Hy; [lia|]. by apply Hxs.
    + have Hi : i = n.
      { apply lookup_lt_Some in Hy. rewrite length_app /= in Hy. lia. }
      subst i. rewrite lookup_app_r in Hy; [lia|].
      rewrite Hlen Nat.sub_diag /= in Hy. by simplify_eq.
Qed.

(** [last] from the index form, given the trace's length relation.
    NOTE: [bitvector.definitions] pulls in [Stdlib.Lists.List], whose
    [last] (a defaulting one, [list A → A → A]) shadows stdpp's — hence
    the qualified [list_basics.last] at every occurrence in this file. *)
Lemma last_of_lookup {A} (l : list A) n x :
  length l = S n → l !! n = Some x → list_basics.last l = Some x.
Proof. intros Hlen Hlk. by rewrite last_lookup Hlen /=. Qed.

(* ------------------------------------------------------------------ *)
Section trace.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  (** The fabric-touching marker, as in [WeakPromiseFact]: it is what lets
      the EXTRACTION classify a step of a given run (dev-freeness is not
      decidable from [pstep]). *)
  Context (pdev : P → wlabel → P → bool).

  Implicit Types c : wpcfg P D.
  Implicit Types T : atrace P D.
  Implicit Types ag : wpagent P.
  Implicit Types ags : list (wpagent P).
  Implicit Types evs : list (aev D).

  (* ---------------------------------------------------------------- *)
  (** ** Well-formed traces *)

  (** The per-position condition, on the two lists (the form the
      inductions work with). *)
  (** The PROGRAM obligation of one traced step, split by the marker.  A
      dev-free event demands the step at EVERY fabric (that is what makes
      it commute with anything — [WeakPromiseFact.wp_afree]); a
      fabric-touching event demands it at the fabric pair the event
      itself records. *)
  Definition astep_prog (ag : wpagent P) (ev : aev D) (st' : P) : Prop :=
    match ae_dev ev with
    | None => ∀ d, pstep (pa_st ag) d (ae_lb ev) st' d
    | Some dd => pstep (pa_st ag) dd.1 (ae_lb ev) st' dd.2
    end.

  (** A traced step IS a program step — at the recorded fabric pair, or
      (dev-free) at any fabric at all, which is why the witness [d0] is
      needed to name one.  [D] is not assumed inhabited anywhere else. *)
  Lemma astep_prog_step (d0 : D) ag ev st' :
    astep_prog ag ev st' → ∃ d d', pstep (pa_st ag) d (ae_lb ev) st' d'.
  Proof.
    rewrite /astep_prog. destruct (ae_dev ev) as [dd|].
    - intros ?. by exists dd.1, dd.2.
    - intros Hall. exists d0, d0. apply Hall.
  Qed.

  Definition asteps_wf (img : image) (log : list wmsg) (i : agent)
      (ags : list (wpagent P)) (evs : list (aev D)) : Prop :=
    length ags = S (length evs) ∧
    ∀ k ev ag ag',
      evs !! k = Some ev → ags !! k = Some ag → ags !! S k = Some ag' →
      ∃ st' f,
        astep_prog ag ev st' ∧
        astep_ok img log i ag (ae_lb ev) f (ae_ts ev) ∧
        ag' = WPAgent st' (f (pa_ws ag)) (prom_del (ae_ts ev) (pa_prom ag)).

  Definition atrace_wf (img : image) (log : list wmsg) (i : agent) T
      : Prop :=
    asteps_wf img log i (at_ags T) (at_evs T).

  Lemma asteps_wf_len img log i ags evs :
    asteps_wf img log i ags evs → length ags = S (length evs).
  Proof. by intros []. Qed.

  Lemma atrace_first_is_Some img log i T :
    atrace_wf img log i T → is_Some (at_ags T !! 0%nat).
  Proof. intros [Hlen _]. apply lookup_lt_is_Some_2. lia. Qed.

  Lemma atrace_last_is_Some img log i T :
    atrace_wf img log i T → is_Some (at_ags T !! length (at_evs T)).
  Proof. intros [Hlen _]. apply lookup_lt_is_Some_2. lia. Qed.

  (** The [last] spelling of the trace's final agent record. *)
  Lemma atrace_last img log i T ag' :
    atrace_wf img log i T →
    at_ags T !! length (at_evs T) = Some ag' →
    list_basics.last (at_ags T) = Some ag'.
  Proof. intros [Hlen _] ?. by eapply last_of_lookup. Qed.

  (** Position [k]'s step, with both endpoints. *)
  Lemma asteps_wf_step img log i ags evs k ev :
    asteps_wf img log i ags evs → evs !! k = Some ev →
    ∃ ag ag' st' f,
      ags !! k = Some ag ∧ ags !! S k = Some ag' ∧
      astep_prog ag ev st' ∧
      astep_ok img log i ag (ae_lb ev) f (ae_ts ev) ∧
      ag' = WPAgent st' (f (pa_ws ag)) (prom_del (ae_ts ev) (pa_prom ag)).
  Proof.
    intros [Hlen Hst] Hev.
    pose proof (lookup_lt_Some _ _ _ Hev) as Hlt.
    have [ag Hag] : is_Some (ags !! k) by apply lookup_lt_is_Some_2; lia.
    have [ag' Hag'] : is_Some (ags !! S k) by apply lookup_lt_is_Some_2; lia.
    destruct (Hst k ev ag ag' Hev Hag Hag') as (st' & f & ? & ? & ?).
    by exists ag, ag', st', f.
  Qed.

  (** The one-element trace, and the cons laws. *)
  Lemma asteps_wf_single img log i ag : asteps_wf img log i [ag] [].
  Proof.
    split; [done|]. intros k ev ?? Hev _ _. by rewrite lookup_nil in Hev.
  Qed.

  Lemma asteps_wf_cons_inv img log i ag ags ev evs :
    asteps_wf img log i (ag :: ags) (ev :: evs) →
    ∃ agn st' f,
      ags !! 0%nat = Some agn ∧
      astep_prog ag ev st' ∧
      astep_ok img log i ag (ae_lb ev) f (ae_ts ev) ∧
      agn = WPAgent st' (f (pa_ws ag)) (prom_del (ae_ts ev) (pa_prom ag)) ∧
      asteps_wf img log i ags evs.
  Proof.
    intros [Hlen Hst]. simpl in Hlen.
    have [agn Hagn] : is_Some (ags !! 0%nat) by apply lookup_lt_is_Some_2; lia.
    destruct (Hst 0%nat ev ag agn) as (st' & f & Hps & Hok & Hag);
      [done|done|done|].
    exists agn, st', f. split_and!; [done|done|done|done|].
    split; [lia|]. intros k ev' a b He Ha Hb.
    by apply (Hst (S k) ev' a b).
  Qed.

  Lemma asteps_wf_cons img log i ag ags ev evs st' f :
    astep_prog ag ev st' →
    astep_ok img log i ag (ae_lb ev) f (ae_ts ev) →
    ags !! 0%nat
      = Some (WPAgent st' (f (pa_ws ag)) (prom_del (ae_ts ev) (pa_prom ag))) →
    asteps_wf img log i ags evs →
    asteps_wf img log i (ag :: ags) (ev :: evs).
  Proof.
    intros Hps Hok H0 [Hlen Hst]. split; [simpl; lia|].
    intros [|k] ev' a b He Ha Hb; simpl in He, Ha, Hb.
    - simplify_eq. by exists st', f.
    - by eapply Hst.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** [ae_ts] is pinned by the label

      [astep_ok] is a specification of a PARTIAL FUNCTION of
      [(img, log, i, ag, l)], so the deletion is determined by the label's
      shape: only a store or an rmw fulfils. *)

  Lemma astep_ok_ts_none img log i (ag : wpagent P) l f Dl :
    astep_ok img log i ag l f Dl →
    match l with
    | LStore _ _ _ _ _ | LRmw _ _ _ _ _ _ _ => True
    | LSilent | LLoad _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
    | LCtrl _ | LInstr => Dl = None
    end.
  Proof.
    destruct l; simpl;
      [by intros [_ ->]|by intros (_ & _ & ->)|done|done|by intros [_ ->]
      |by intros [_ ->]|by intros [_ ->]|by intros [_ ->]|by intros [_ ->]].
  Qed.

  Lemma atrace_ts_none img log i T k ev :
    atrace_wf img log i T → at_evs T !! k = Some ev →
    match ae_lb ev with
    | LStore _ _ _ _ _ | LRmw _ _ _ _ _ _ _ => True
    | LSilent | LLoad _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
    | LCtrl _ | LInstr => ae_ts ev = None
    end.
  Proof.
    intros Hwf Hev.
    destruct (asteps_wf_step _ _ _ _ _ _ _ Hwf Hev)
      as (ag & ag' & st' & f & _ & _ & _ & Hok & _).
    by apply astep_ok_ts_none in Hok.
  Qed.

  (** A lat-free PROGRAM emits only lat-free labels, so every trace of a
      factorized behavior is lat-free (the hypothesis [WeakPromiseFact]'s
      swap needs, recorded on the traced side too). *)
  Lemma atrace_lat_free (d0 : D) img log i T k ev :
    lat_free_prog pstep → atrace_wf img log i T →
    at_evs T !! k = Some ev → lat_free (ae_lb ev).
  Proof.
    intros Hlfp Hwf Hev.
    destruct (asteps_wf_step _ _ _ _ _ _ _ Hwf Hev)
      as (ag & ag' & st' & f & _ & _ & Hps & _ & _).
    apply (astep_prog_step d0) in Hps as (d & d' & Hps).
    destruct (ae_lb ev) as [|aq lat base tvs asrc| | | | | | |]; simpl;
      [done| |done|done|done|done|done|done|done].
    destruct lat; [|done]. by destruct (Hlfp _ _ _ _ _ _ _ _ Hps).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Building an event from a step: the MARKER decides [ae_dev] *)

  Definition mk_aev (din : D) (ag : wpagent P) (l : wlabel) (st' : P)
      (d' : D) (Dl : option nat) : aev D :=
    AEv l Dl (if pdev (pa_st ag) l st' then Some (din, d') else None).

  Lemma mk_aev_lb din ag l st' d' Dl :
    ae_lb (mk_aev din ag l st' d' Dl) = l.
  Proof. done. Qed.
  Lemma mk_aev_ts din ag l st' d' Dl :
    ae_ts (mk_aev din ag l st' d' Dl) = Dl.
  Proof. done. Qed.

  Lemma astep_prog_mk din ag l st' d' Dl :
    pdev_ok pstep pdev →
    pstep (pa_st ag) din l st' d' →
    astep_prog ag (mk_aev din ag l st' d' Dl) st'.
  Proof.
    intros Hpok Hs. rewrite /astep_prog /mk_aev /=.
    destruct (pdev (pa_st ag) l st') eqn:Hp; [exact Hs|].
    by destruct (Hpok _ _ _ _ _ Hs Hp) as [_ ?].
  Qed.

  (** The dev-free case of [mk_aev] also pins the fabric: [pdev_ok] says
      a step the marker calls free leaves the fabric where it found it. *)
  Lemma mk_aev_free din ag l st' d' Dl :
    pdev_ok pstep pdev →
    pstep (pa_st ag) din l st' d' →
    ae_dev (mk_aev din ag l st' d' Dl) = None → d' = din.
  Proof.
    intros Hpok Hs. rewrite /mk_aev /=.
    destruct (pdev (pa_st ag) l st') eqn:Hp; [done|].
    intros _. by destruct (Hpok _ _ _ _ _ Hs Hp) as [-> _].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE EXTRACTION: an [rtc] of one agent's steps IS a trace *)

  (** [wp_astep_inv] (the record-building inversion) and
      [astep_of_rtc_frozen] (the [rtc]-level frame + frozen-log facts) moved
      to [WeakPromiseFact.v] with the W4 lift batch; they are used verbatim
      below. *)

  (** THE EXTRACTION.  Agent [i]'s phase, as a trace against the frozen
      [(img, log)], with its first record [i]'s entry in [c] and its last
      record [i]'s entry in [c'] — plus the frame (no other agent moved)
      and the frozen-log facts. *)
  Lemma astep_of_atrace i c c' ag :
    pdev_ok pstep pdev →
    rtc (wp_astep_of pstep i) c c' →
    pc_ags c !! i = Some ag →
    ∃ T ag',
      atrace_wf (pc_img c) (pc_log c) i T ∧
      at_ags T !! 0%nat = Some ag ∧
      at_ags T !! length (at_evs T) = Some ag' ∧
      list_basics.last (at_ags T) = Some ag' ∧
      pc_ags c' !! i = Some ag' ∧
      (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j) ∧
      pc_log c' = pc_log c ∧ pc_img c' = pc_img c ∧
      length (pc_ags c') = length (pc_ags c).
  Proof.
    intros Hpok Hrun. revert ag.
    induction Hrun as [c|c y c' (l & Hs) Hrun IH]; intros ag Hlk.
    - exists (ATr [ag] []), ag. simpl.
      have Hwf : atrace_wf (pc_img c) (pc_log c) i (ATr [ag] [])
        by apply asteps_wf_single.
      split_and!; [done|done|done|done|done|done|done|done|done].
    - destruct (wp_astep_inv pstep i l c y Hs)
        as (ag0 & st' & d' & f & Dl & Hlk0 & Hps & Hok & Hy).
      assert (ag0 = ag) as -> by congruence.
      have Hlt : (i < length (pc_ags c))%nat by eapply lookup_lt_Some.
      have Hylk : pc_ags y !! i
                  = Some (WPAgent st' (f (pa_ws ag)) (prom_del Dl (pa_prom ag))).
      { rewrite Hy /=. rewrite list_lookup_insert; [done|done]. }
      destruct (IH _ Hylk)
        as (T1 & ag' & Hwf1 & H01 & Hl1 & _ & Hc' & Hfr & Hlog & Himg & Hlen).
      rewrite Hy /= in Hwf1 Hfr Hlog Himg Hlen.
      set ev := mk_aev (pc_dev c) ag l st' d' Dl.
      exists (ATr (ag :: at_ags T1) (ev :: at_evs T1)), ag'.
      have Hwf : atrace_wf (pc_img c) (pc_log c) i
                   (ATr (ag :: at_ags T1) (ev :: at_evs T1)).
      { rewrite /atrace_wf /=.
        eapply (asteps_wf_cons _ _ _ _ _ ev _ st' f);
          [by apply astep_prog_mk|done| |done].
        exact H01. }
      split_and!.
      + done.
      + done.
      + simpl. exact Hl1.
      + eapply atrace_last; [exact Hwf|simpl; exact Hl1].
      + done.
      + intros j Hj. rewrite Hfr //. by rewrite list_lookup_insert_ne //.
      + done.
      + done.
      + by rewrite Hlen length_insert.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE CONVERSE: replaying a trace rebuilds the [rtc]

      Needed by W2b: after surgery on the dependency graph the run has to
      be rebuilt from the (re-ordered) traces. *)

  (** A trace all of whose events are DEV-FREE.  Replay is stated for
      these: a fabric-touching trace can only be replayed in an order
      consistent with the GLOBAL device witness, which is the toposort's
      choice and therefore G3/G4's business, not this file's. *)
  Definition evs_dev_free (evs : list (aev D)) : Prop :=
    ∀ k ev, evs !! k = Some ev → ae_dev ev = None.

  Lemma evs_dev_free_cons ev evs :
    evs_dev_free (ev :: evs) → ae_dev ev = None ∧ evs_dev_free evs.
  Proof.
    intros H. split; [by apply (H 0%nat)|].
    intros k ev' Hk. by apply (H (S k)).
  Qed.

  Lemma asteps_replay i evs :
    ∀ c ags ag ag',
      asteps_wf (pc_img c) (pc_log c) i ags evs →
      evs_dev_free evs →
      pc_ags c !! i = Some ag →
      ags !! 0%nat = Some ag →
      ags !! length evs = Some ag' →
      rtc (wp_afree_of pstep i) c
        (WPCfg (pc_img c) (pc_log c) (pc_dev c) (<[i := ag']> (pc_ags c))).
  Proof.
    induction evs as [|ev evs IH]; intros c ags ag ag' Hwf Hdf Hclk H0 Hl.
    - simpl in Hl. rewrite H0 in Hl. simplify_eq.
      rewrite (list_insert_id _ _ _ Hclk) wpcfg_eta. apply rtc_refl.
    - destruct ags as [|a ags]; [done|]. simpl in H0. simplify_eq.
      apply evs_dev_free_cons in Hdf as [Hdf0 Hdf].
      destruct (asteps_wf_cons_inv _ _ _ _ _ _ _ Hwf)
        as (agn & st' & f & Hagn & Hps & Hok & Hagne & Hwf').
      rewrite /astep_prog Hdf0 in Hps.
      set c2 := WPCfg (pc_img c) (pc_log c) (pc_dev c) (<[i := agn]> (pc_ags c)).
      have Hstep : wp_afree pstep i (ae_lb ev) c c2.
      { rewrite /c2 Hagne.
        by apply (WPAFree pstep i (ae_lb ev) c ag st' f (ae_ts ev)). }
      eapply rtc_l; [by exists (ae_lb ev)|].
      have Hlk2 : pc_ags c2 !! i = Some agn.
      { rewrite /c2 /=. rewrite list_lookup_insert; [|done].
        by eapply lookup_lt_Some. }
      have Hl' : ags !! length evs = Some ag' by exact Hl.
      pose proof (IH c2 ags agn ag' Hwf' Hdf Hlk2 Hagn Hl') as Hrun.
      rewrite /c2 /= list_insert_insert in Hrun. exact Hrun.
  Qed.

  Lemma atrace_replay i c T ag ag' :
    atrace_wf (pc_img c) (pc_log c) i T →
    evs_dev_free (at_evs T) →
    pc_ags c !! i = Some ag →
    at_ags T !! 0%nat = Some ag →
    at_ags T !! length (at_evs T) = Some ag' →
    rtc (wp_afree_of pstep i) c
      (WPCfg (pc_img c) (pc_log c) (pc_dev c) (<[i := ag']> (pc_ags c))).
  Proof. intros. by eapply asteps_replay. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE WHOLE PHASE: [wp_phases] as one [ptraces] *)

  Lemma wp_phases_frozen js c c' :
    wp_phases pstep js c c' →
    pc_log c' = pc_log c ∧ pc_img c' = pc_img c ∧
    length (pc_ags c') = length (pc_ags c).
  Proof.
    revert c c'. induction js as [|j js IH]; intros c c' Hph; simpl in Hph.
    - by subst c'.
    - destruct Hph as (mid & Hrun & Hph).
      destruct (astep_of_rtc_frozen pstep j c mid
                  (wp_afree_of_astep_of pstep j _ _ Hrun)) as (H1 & H2 & H3 & _).
      destruct (IH mid c' Hph) as (H1' & H2' & H3').
      split_and!; [by rewrite H1' H1|by rewrite H2' H2|by rewrite H3' H3].
  Qed.

  Lemma wp_phases_frame js c c' i :
    wp_phases pstep js c c' → i ∉ js → pc_ags c' !! i = pc_ags c !! i.
  Proof.
    revert c c'. induction js as [|j js IH]; intros c c' Hph Hni;
      simpl in Hph.
    - by subst c'.
    - apply not_elem_of_cons in Hni as [Hne Hni].
      destruct Hph as (mid & Hrun & Hph).
      destruct (astep_of_rtc_frozen pstep j c mid
                  (wp_afree_of_astep_of pstep j _ _ Hrun)) as (_ & _ & _ & Hfr).
      rewrite (IH mid c' Hph Hni). by apply Hfr.
  Qed.

  (** Agent [i]'s trace out of a whole [wp_phases] run.  [NoDup js] is
      what makes [i]'s steps contiguous; [i] need not occur in [js] (then
      the trace is the one-record trace and [i] never moved). *)
  Lemma wp_phases_agent js c c' i ag :
    pdev_ok pstep pdev →
    NoDup js → wp_phases pstep js c c' → pc_ags c !! i = Some ag →
    ∃ T ag',
      atrace_wf (pc_img c) (pc_log c) i T ∧
      at_ags T !! 0%nat = Some ag ∧
      at_ags T !! length (at_evs T) = Some ag' ∧
      pc_ags c' !! i = Some ag'.
  Proof.
    intros Hpok. revert c c' ag.
    induction js as [|j js IH]; intros c c' ag Hnd Hph Hlk;
      simpl in Hph.
    - subst c'. exists (ATr [ag] []), ag. simpl.
      split_and!; [by apply asteps_wf_single|done|done|done].
    - apply list_relations.NoDup_cons in Hnd as [Hnj Hnd].
      destruct Hph as (mid & Hrun & Hph).
      destruct (decide (j = i)) as [->|Hne].
      + destruct (astep_of_atrace i c mid ag Hpok
                    (wp_afree_of_astep_of pstep i _ _ Hrun) Hlk)
          as (T & ag' & Hwf & H0 & Hl & _ & Hmid & _).
        exists T, ag'. split_and!; [done|done|done|].
        by rewrite (wp_phases_frame js mid c' i Hph Hnj).
      + destruct (astep_of_rtc_frozen pstep j c mid
                    (wp_afree_of_astep_of pstep j _ _ Hrun))
          as (Hlog & Himg & _ & Hfr).
        have Hmid : pc_ags mid !! i = Some ag by rewrite Hfr //; congruence.
        destruct (IH mid c' ag Hnd Hph Hmid) as (T & ag' & Hwf & H0 & Hl & Hc').
        exists T, ag'. rewrite Hlog Himg in Hwf.
        split_and!; [done|done|done|done].
  Qed.

  (** The traced form of a whole state phase: one trace per agent, all
      against the frozen [(img, log)], first records = [mid]'s agents,
      last records = [c]'s agents. *)
  Definition ptraces_of (TS : ptraces P D) (mid c : wpcfg P D) : Prop :=
    pt_img TS = pc_img mid ∧
    pt_log TS = pc_log mid ∧
    length (pt_trs TS) = length (pc_ags mid) ∧
    (∀ i T, pt_trs TS !! i = Some T →
       atrace_wf (pt_img TS) (pt_log TS) i T) ∧
    (∀ i T, pt_trs TS !! i = Some T → at_ags T !! 0%nat = pc_ags mid !! i) ∧
    (∀ i T, pt_trs TS !! i = Some T →
       at_ags T !! length (at_evs T) = pc_ags c !! i) ∧
    pc_log c = pc_log mid ∧ pc_img c = pc_img mid ∧
    length (pc_ags c) = length (pc_ags mid).

  Lemma phases_ptraces mid c :
    pdev_ok pstep pdev →
    wp_phases pstep (seq 0 (length (pc_ags mid))) mid c →
    ∃ TS, ptraces_of TS mid c.
  Proof.
    intros Hpok Hph.
    destruct (wp_phases_frozen _ _ _ Hph) as (Hlog & Himg & Hlen).
    destruct (list_ex_of_index
      (λ i T, atrace_wf (pc_img mid) (pc_log mid) i T ∧
              at_ags T !! 0%nat = pc_ags mid !! i ∧
              at_ags T !! length (at_evs T) = pc_ags c !! i)
      (length (pc_ags mid))) as (Ts & HlenTs & HTs).
    { intros i Hi.
      have [ag Hag] : is_Some (pc_ags mid !! i) by apply lookup_lt_is_Some_2.
      destruct (wp_phases_agent _ _ _ i ag Hpok (NoDup_seq _ _) Hph Hag)
        as (T & ag' & Hwf & H0 & Hl & Hc).
      exists T. split_and!; [done|by rewrite H0 Hag|by rewrite Hl Hc]. }
    exists (PTrs (pc_img mid) (pc_log mid) Ts). rewrite /ptraces_of /=.
    split_and!; [done|done|done| | | |done|done|done].
    - intros i T Hi. by destruct (HTs i T Hi) as (? & _ & _).
    - intros i T Hi. by destruct (HTs i T Hi) as (_ & ? & _).
    - intros i T Hi. by destruct (HTs i T Hi) as (_ & _ & ?).
  Qed.

  (** [wp_lf_step] ⊆ [wp_state_step] (the factorization's state phase is a
      state phase). *)
  Lemma wp_lf_state_rtc c c' :
    rtc (wp_lf_step pstep) c c' → rtc (wp_state_step pstep) c c'.
  Proof.
    induction 1 as [|x y z (i & l & _ & Hs) _ IH]; [done|].
    eapply rtc_l; [by exists i, l|done].
  Qed.


  (* ---------------------------------------------------------------- *)
  (** ** THE DEVICE-ORDER WITNESS, AND THE EXTRACTION THAT PRODUCES IT

      With a shared fabric the state phase can no longer be reordered
      agent-contiguous — device accesses of different agents do not
      commute — so [phases_ptraces] above only covers a DEV-FREE segment
      (see [WeakPromiseFact] (E')).  The general state phase is handled
      NOT by reordering it but by reading the traces off the
      INTERLEAVING directly, one appended event per step, and recording
      the fabric-touching steps in a global order as we go.

      That is strictly better than reordering: it needs no commutation at
      all, and it hands G3 exactly what the gdev edges want — a total
      order on the fabric-touching trace positions, all of whose edges
      are consistent with the behavior's temporal order by construction. *)

  (** The event at a witness position, and its recorded fabric pair. *)
  Definition ev_at (TS : ptraces P D) (e : agent * nat) : option (aev D) :=
    T ← pt_trs TS !! e.1; at_evs T !! e.2.
  Definition ev_din (TS : ptraces P D) (e : agent * nat) : option D :=
    fst <$> (ev_at TS e ≫= ae_dev).
  Definition ev_dout (TS : ptraces P D) (e : agent * nat) : option D :=
    snd <$> (ev_at TS e ≫= ae_dev).

  (** THE FOLD (the design kernel's reading): the fabric BEFORE witness
      position [m] is [pd_init] at the head and the previous entry's
      [dout] thereafter. *)
  Definition dev_at (TS : ptraces P D) (DS : pdevs D) (m : nat) : D :=
    match m with
    | 0%nat => pd_init DS
    | S m' => default (pd_init DS) (pd_ord DS !! m' ≫= ev_dout TS)
    end.

  Definition ptraces_dev_of (TS : ptraces P D) (DS : pdevs D)
      (mid c : wpcfg P D) : Prop :=
    (** the per-agent traces, EXACTLY as before the fabric *)
    ptraces_of TS mid c ∧
    pd_init DS = pc_dev mid ∧
    (** (W1) every listed position IS a fabric-touching event *)
    (∀ m e, pd_ord DS !! m = Some e →
       ∃ ev, ev_at TS e = Some ev ∧ is_Some (ae_dev ev)) ∧
    (** (W2) and every fabric-touching event IS listed *)
    (∀ i k ev, ev_at TS (i, k) = Some ev → is_Some (ae_dev ev) →
       ∃ m, pd_ord DS !! m = Some (i, k)) ∧
    (** (W3) the witness order REFINES each agent's trace order — the
        "interleaving consistent with (a) and (b)" clause; injectivity of
        the witness follows *)
    (∀ m1 m2 i k1 k2, (m1 < m2)%nat →
       pd_ord DS !! m1 = Some (i, k1) → pd_ord DS !! m2 = Some (i, k2) →
       (k1 < k2)%nat) ∧
    (** (W4) THE FOLD: a listed step reads the fabric its predecessor left *)
    (∀ m e, pd_ord DS !! m = Some e → ev_din TS e = Some (dev_at TS DS m)) ∧
    (** (W5) the phase ends at the fabric the last listed step left *)
    pc_dev c = dev_at TS DS (length (pd_ord DS)) ∧
    (** (W6) THE MARKER IS THE AUTHORITY on the flag: an event is
        fabric-touching only where [pdev] says so.  This is what makes
        the constant-fabric instance collapse — under a marker that never
        fires, every event is dev-free and the witness is empty. *)
    (∀ i T k ev ag ag',
       pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
       at_ags T !! k = Some ag → at_ags T !! S k = Some ag' →
       ae_dev ev = None ∨ pdev (pa_st ag) (ae_lb ev) (pa_st ag') = true).

  (** THE WITNESS ALONE — clauses (W1)–(W4), i.e. everything
      [ptraces_dev_of] says about [DS] that does NOT mention the phase's
      endpoints [mid]/[c].  This is the shape G3's gdev edges and G4's
      fabric fold consume: the replay never sees the behavior's [mid], it
      sees only the bundle and the device order.  ([W5] pins the FINAL
      fabric and [W6] is the marker's authority over the flag; neither is
      needed to replay, so neither is here.) *)
  Definition ptraces_wit (TS : ptraces P D) (DS : pdevs D) : Prop :=
    (∀ m e, pd_ord DS !! m = Some e →
       ∃ ev, ev_at TS e = Some ev ∧ is_Some (ae_dev ev)) ∧
    (∀ i k ev, ev_at TS (i, k) = Some ev → is_Some (ae_dev ev) →
       ∃ m, pd_ord DS !! m = Some (i, k)) ∧
    (∀ m1 m2 i k1 k2, (m1 < m2)%nat →
       pd_ord DS !! m1 = Some (i, k1) → pd_ord DS !! m2 = Some (i, k2) →
       (k1 < k2)%nat) ∧
    (∀ m e, pd_ord DS !! m = Some e → ev_din TS e = Some (dev_at TS DS m)).

  Lemma ptraces_dev_of_wit TS DS mid c :
    ptraces_dev_of TS DS mid c → ptraces_wit TS DS.
  Proof. intros (_ & _ & H1 & H2 & H3 & H4 & _ & _). by split_and!. Qed.

  (** [dev_at] at the EMPTY witness is the initial fabric, always. *)
  Lemma dev_at_nil TS (d : D) m : dev_at TS (PDevs d []) m = d.
  Proof.
    destruct m as [|m']; [done|].
    rewrite /dev_at /pd_ord /pd_init lookup_nil //.
  Qed.

  (** …and the empty witness IS a witness of a DEV-FREE bundle: nothing is
      listed, and nothing needs to be.  (The G3/G4 collapse: every
      consumer scoped to dev-free traces gets the general theorems at this
      instance.) *)
  Lemma ptraces_wit_nil TS (d : D) :
    (∀ i T k ev, pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
       ae_dev ev = None) →
    ptraces_wit TS (PDevs d []).
  Proof.
    intros Hdf. split_and!; simpl.
    - intros m e Hm. by rewrite lookup_nil in Hm.
    - intros i k ev Hev Hdd. rewrite /ev_at /= in Hev.
      destruct (pt_trs TS !! i) as [T|] eqn:HT; simpl in Hev; [|done].
      rewrite (Hdf i T k ev HT Hev) in Hdd. by destruct Hdd.
    - intros ????? _ Hm. by rewrite lookup_nil in Hm.
    - intros m e Hm. by rewrite lookup_nil in Hm.
  Qed.

  (** Appending one step to a well-formed trace. *)
  Lemma asteps_wf_snoc img log i ags evs ag ev st' f :
    asteps_wf img log i ags evs →
    ags !! length evs = Some ag →
    astep_prog ag ev st' →
    astep_ok img log i ag (ae_lb ev) f (ae_ts ev) →
    asteps_wf img log i
      (ags ++ [WPAgent st' (f (pa_ws ag)) (prom_del (ae_ts ev) (pa_prom ag))])
      (evs ++ [ev]).
  Proof.
    intros [Hlen Hst] Hag Hps Hok. split.
    { rewrite !length_app /=. lia. }
    intros k ev0 a b Hev Ha Hb.
    destruct (decide (k < length evs)%nat) as [Hlt|Hge].
    - rewrite lookup_app_l in Hev; [done|].
      rewrite lookup_app_l in Ha; [lia|].
      rewrite lookup_app_l in Hb; [lia|].
      by eapply Hst.
    - have Hk : k = length evs.
      { apply lookup_lt_Some in Hev. rewrite length_app /= in Hev. lia. }
      subst k.
      rewrite lookup_app_r in Hev; [lia|].
      rewrite Nat.sub_diag /= in Hev. simplify_eq.
      rewrite lookup_app_l in Ha; [lia|].
      rewrite Hag in Ha. simplify_eq.
      rewrite lookup_app_r in Hb; [lia|].
      rewrite Hlen Nat.sub_diag /= in Hb. simplify_eq.
      by exists st', f.
  Qed.

  (** The trace at [i] only GROWS, so every position that already
      resolved resolves the same way. *)
  Lemma ev_at_grow TS i T T' e :
    pt_trs TS !! i = Some T →
    (∀ k ev, at_evs T !! k = Some ev → at_evs T' !! k = Some ev) →
    is_Some (ev_at TS e) →
    ev_at (PTrs (pt_img TS) (pt_log TS) (<[i := T']> (pt_trs TS))) e
    = ev_at TS e.
  Proof.
    intros Hi Hgrow [ev Hev]. destruct e as [j k].
    rewrite /ev_at /= in Hev |- *.
    have Hlt : (i < length (pt_trs TS))%nat by eapply lookup_lt_Some.
    destruct (decide (j = i)) as [->|Hne].
    - rewrite Hi /= in Hev.
      rewrite list_lookup_insert //= Hi /=. by rewrite (Hgrow k ev Hev) Hev.
    - by rewrite list_lookup_insert_ne.
  Qed.

  Lemma ev_din_grow TS i T T' e :
    pt_trs TS !! i = Some T →
    (∀ k ev, at_evs T !! k = Some ev → at_evs T' !! k = Some ev) →
    is_Some (ev_at TS e) →
    ev_din (PTrs (pt_img TS) (pt_log TS) (<[i := T']> (pt_trs TS))) e
    = ev_din TS e.
  Proof. intros ???. rewrite /ev_din. by erewrite ev_at_grow. Qed.

  Lemma ev_dout_grow TS i T T' e :
    pt_trs TS !! i = Some T →
    (∀ k ev, at_evs T !! k = Some ev → at_evs T' !! k = Some ev) →
    is_Some (ev_at TS e) →
    ev_dout (PTrs (pt_img TS) (pt_log TS) (<[i := T']> (pt_trs TS))) e
    = ev_dout TS e.
  Proof. intros ???. rewrite /ev_dout. by erewrite ev_at_grow. Qed.

  (** THE EXTRACTION.  Every state phase yields per-agent traces PLUS the
      global device-order witness.  Induction is on the SNOC form of the
      run: one step appends one event to its own agent's trace, and — if
      the marker calls it fabric-touching — one entry to the witness. *)
  Lemma state_ptraces mid cfin :
    pdev_ok pstep pdev →
    rtc (wp_state_step pstep) mid cfin →
    ∃ TS DS, ptraces_dev_of TS DS mid cfin.
  Proof.
    intros Hpok Hrun.
    apply (rtc_ind_r (R := wp_state_step pstep)
             (λ z, ∃ TS DS, ptraces_dev_of TS DS mid z) mid);
      [| |exact Hrun].
    { (* the empty phase: one one-record trace per agent, empty witness *)
      exists (PTrs (pc_img mid) (pc_log mid)
                ((λ ag, ATr [ag] []) <$> pc_ags mid)),
             (PDevs (pc_dev mid) []).
      have Htr : ∀ i T,
        ((λ ag, ATr [ag] []) <$> pc_ags mid) !! i = Some T →
        ∃ ag, pc_ags mid !! i = Some ag ∧ T = ATr [ag] [].
      { intros i T HT. rewrite list_lookup_fmap in HT.
        destruct (pc_ags mid !! i) as [ag|] eqn:Hag; simplify_eq/=.
        by exists ag. }
      split_and!; simpl.
      - split_and!; simpl; [done|done|by rewrite length_fmap| | |
                            |done|done|done].
        + intros i T HT. destruct (Htr i T HT) as (ag & _ & ->).
          by apply asteps_wf_single.
        + intros i T HT. destruct (Htr i T HT) as (ag & Hag & ->). by rewrite Hag.
        + intros i T HT. destruct (Htr i T HT) as (ag & Hag & ->). by rewrite Hag.
      - done.
      - intros m e Hm. by rewrite lookup_nil in Hm.
      - intros i k ev Hev _. rewrite /ev_at /= list_lookup_fmap in Hev.
        destruct (pc_ags mid !! i) as [ag|]; simplify_eq/=.
      - intros ????? _ Hm. by rewrite lookup_nil in Hm.
      - intros m e Hm. by rewrite lookup_nil in Hm.
      - done.
      - intros i T k ev ag ag' HT Hev _ _.
        rewrite list_lookup_fmap in HT.
        destruct (pc_ags mid !! i) as [ag0|]; simplify_eq/=. }
    (* one more step *)
    clear cfin Hrun. intros y c Hrun Hstep IH.
    destruct IH as (TS & DS &
      (Hpt & Hinit & HW1 & HW2 & HW3 & HW4 & HW5 & HW6)).
    destruct Hpt as (Himg & Hlog & HlenTS & Hwf & Hfst & Hlst & Hclog & Hcimg
                     & Hclen).
    destruct Hstep as (i & l & Hs).
    destruct (wp_astep_inv pstep i l y c Hs)
      as (ag & st' & d' & f & Dl & Hlk & Hps & Hok & Hc).
    (* the new event, kept OPAQUE (a bare variable with three field
       equations) so that no [simpl] can unfold it out from under a
       rewrite *)
    have [ev [Hevlb [Hevts Hevdd]]] :
      ∃ ev : aev D, ae_lb ev = l ∧ ae_ts ev = Dl ∧
        ((pdev (pa_st ag) l st' = true ∧ ae_dev ev = Some (pc_dev y, d')) ∨
         (pdev (pa_st ag) l st' = false ∧ ae_dev ev = None)).
    { destruct (pdev (pa_st ag) l st') eqn:Hm0.
      - exists (AEv l Dl (Some (pc_dev y, d'))). split_and!; [done|done|].
        left. by split.
      - exists (AEv l Dl None). split_and!; [done|done|]. right. by split. }
    set agn := WPAgent st' (f (pa_ws ag)) (prom_del Dl (pa_prom ag)).
    have Hilt : (i < length (pt_trs TS))%nat.
    { rewrite HlenTS -Hclen. by eapply lookup_lt_Some. }
    have [T HT] : is_Some (pt_trs TS !! i) by apply lookup_lt_is_Some_2.
    have HwfT : atrace_wf (pt_img TS) (pt_log TS) i T by apply Hwf.
    have HlastT : at_ags T !! length (at_evs T) = Some ag
      by rewrite (Hlst i T HT) -Hlk.
    set T' := ATr (at_ags T ++ [agn]) (at_evs T ++ [ev]).
    set TS' := PTrs (pt_img TS) (pt_log TS) (<[i := T']> (pt_trs TS)).
    have HT'ags : at_ags T' = at_ags T ++ [agn] by rewrite /T'.
    have HT'evs : at_evs T' = at_evs T ++ [ev] by rewrite /T'.
    (* the trace at [i] only grows *)
    have Hgrow : ∀ k e0, at_evs T !! k = Some e0 → at_evs T' !! k = Some e0.
    { intros k e0 Hk. rewrite HT'evs lookup_app_l //.
      by eapply lookup_lt_Some. }
    have Hgrow_at : ∀ e0, is_Some (ev_at TS e0) → ev_at TS' e0 = ev_at TS e0.
    { intros e0 He0. by eapply ev_at_grow. }
    have Hgrow_din : ∀ e0, is_Some (ev_at TS e0) → ev_din TS' e0 = ev_din TS e0.
    { intros e0 He0. by eapply ev_din_grow. }
    have Hgrow_dout : ∀ e0, is_Some (ev_at TS e0) → ev_dout TS' e0 = ev_dout TS e0.
    { intros e0 He0. by eapply ev_dout_grow. }
    (* the OLD witness entries resolve identically in [TS'] *)
    have Hold : ∀ m e0, pd_ord DS !! m = Some e0 → is_Some (ev_at TS e0).
    { intros m e0 Hm. destruct (HW1 m e0 Hm) as (ev0 & Hev0 & _). by eexists. }
    have Hdev_at : ∀ m, (m ≤ length (pd_ord DS))%nat →
                        dev_at TS' DS m = dev_at TS DS m.
    { intros [|m'] Hm; [done|]. simpl.
      destruct (pd_ord DS !! m') as [e0|] eqn:He0; simpl; [|done].
      by rewrite (Hgrow_dout e0 (Hold _ _ He0)). }
    (* the new event's lookups *)
    have HevT' : at_evs T' !! length (at_evs T) = Some ev.
    { rewrite HT'evs lookup_app_r; [lia|]. by rewrite Nat.sub_diag. }
    have HTS'i : pt_trs TS' !! i = Some T'.
    { rewrite /TS' /=. by rewrite list_lookup_insert. }
    have Hev_at_new : ev_at TS' (i, length (at_evs T)) = Some ev.
    { rewrite /ev_at /= HTS'i /=. exact HevT'. }
    (* every event of [TS'] is either an old one or the new one *)
    have Hcases : ∀ j k ev0, ev_at TS' (j, k) = Some ev0 →
      (j = i ∧ k = length (at_evs T) ∧ ev0 = ev) ∨ ev_at TS (j, k) = Some ev0.
    { intros j k ev0. rewrite /ev_at /=.
      destruct (decide (j = i)) as [->|Hne].
      - rewrite list_lookup_insert //=.
        destruct (decide (k < length (at_evs T))%nat) as [Hlt|Hge].
        + rewrite lookup_app_l //. intros ?. right. by rewrite HT /=.
        + intros Hk. left.
          have Hk' : k = length (at_evs T).
          { apply lookup_lt_Some in Hk. rewrite length_app /= in Hk. lia. }
          subst k. rewrite lookup_app_r in Hk; [lia|].
          rewrite Nat.sub_diag /= in Hk. by simplify_eq.
      - rewrite list_lookup_insert_ne //. intros ?. by right. }
    have HwfT' : atrace_wf (pt_img TS) (pt_log TS) i T'.
    { rewrite /atrace_wf /T' /agn -Hevts.
      eapply (asteps_wf_snoc _ _ _ _ _ ag ev st' f);
        [exact HwfT|exact HlastT| |].
      - rewrite /astep_prog Hevlb.
        destruct Hevdd as [[Hm0 Hd]|[Hm0 Hd]]; rewrite Hd; [exact Hps|].
        by destruct (Hpok _ _ _ _ _ Hps Hm0) as [_ ?].
      - rewrite Hevlb Hevts Himg Hlog -Hcimg -Hclog. exact Hok. }
    (* THE TRACE SIDE, common to both cases *)
    have Hpt' : ptraces_of TS' mid c.
    { rewrite /ptraces_of. rewrite Hc /=. split_and!.
      - done.
      - done.
      - rewrite /TS' /= length_insert //.
      - intros j Tj HTj. rewrite /TS' /= in HTj.
        destruct (decide (j = i)) as [->|Hne].
        + rewrite list_lookup_insert // in HTj.
          apply Some_inj in HTj. subst Tj. exact HwfT'.
        + rewrite list_lookup_insert_ne // in HTj. by apply Hwf.
      - intros j Tj HTj. rewrite /TS' /= in HTj.
        destruct (decide (j = i)) as [->|Hne].
        + rewrite list_lookup_insert // in HTj.
          apply Some_inj in HTj. subst Tj.
          rewrite HT'ags lookup_app_l.
          * destruct HwfT as [Hl _]. lia.
          * by rewrite (Hfst i T HT).
        + rewrite list_lookup_insert_ne // in HTj. by apply Hfst.
      - intros j Tj HTj. rewrite /TS' /= in HTj.
        destruct (decide (j = i)) as [->|Hne].
        + rewrite list_lookup_insert // in HTj.
          apply Some_inj in HTj. subst Tj.
          rewrite HT'ags HT'evs length_app /= lookup_app_r.
          * destruct HwfT as [Hl _]. lia.
          * destruct HwfT as [Hl _]. rewrite Hl.
            replace (length (at_evs T) + 1 - S (length (at_evs T)))%nat
              with 0%nat by lia.
            simpl. rewrite list_lookup_insert //.
            by eapply (lookup_lt_Some _ _ _ Hlk).
        + rewrite list_lookup_insert_ne // in HTj.
          rewrite list_lookup_insert_ne //. by apply Hlst.
      - by rewrite Hclog.
      - by rewrite Hcimg.
      - by rewrite length_insert. }
    have HlenT : length (at_ags T) = S (length (at_evs T)) by destruct HwfT.
    have HW6' : ∀ j T0 k ev0 ag0 ag0',
       pt_trs TS' !! j = Some T0 → at_evs T0 !! k = Some ev0 →
       at_ags T0 !! k = Some ag0 → at_ags T0 !! S k = Some ag0' →
       ae_dev ev0 = None ∨ pdev (pa_st ag0) (ae_lb ev0) (pa_st ag0') = true.
    { intros j T0 k ev0 ag0 ag0' HT0 Hev0 Hag0 Hag0'.
      rewrite /TS' /= in HT0.
      destruct (decide (j = i)) as [->|Hne].
      - rewrite list_lookup_insert // in HT0.
        apply Some_inj in HT0. subst T0.
        rewrite HT'evs in Hev0. rewrite HT'ags in Hag0, Hag0'.
        destruct (decide (k < length (at_evs T))%nat) as [Hlt|Hge].
        + rewrite lookup_app_l in Hev0; [done|].
          rewrite lookup_app_l in Hag0; [lia|].
          rewrite lookup_app_l in Hag0'; [lia|].
          by eapply HW6.
        + have Hk : k = length (at_evs T).
          { apply lookup_lt_Some in Hev0. rewrite length_app /= in Hev0. lia. }
          subst k. rewrite lookup_app_r in Hev0; [lia|].
          rewrite Nat.sub_diag /= in Hev0.
          rewrite lookup_app_l in Hag0; [lia|].
          rewrite lookup_app_r in Hag0'; [lia|].
          rewrite HlenT Nat.sub_diag /= in Hag0'.
          rewrite HlastT in Hag0.
          apply Some_inj in Hag0. subst ag0.
          apply Some_inj in Hag0'. subst ag0'.
          apply Some_inj in Hev0. subst ev0.
          destruct Hevdd as [[Hm0 Hd0]|[Hm0 Hd0]].
          * right. rewrite Hevlb /agn /=. exact Hm0.
          * by left.
      - rewrite list_lookup_insert_ne // in HT0. by eapply HW6. }
    have Hcdev : pc_dev c = d' by rewrite Hc.
    destruct Hevdd as [[Hmark Hevdev]|[Hmark Hevdev]].
    - (* FABRIC-TOUCHING: extend the witness *)
      set DS' := PDevs (pd_init DS) (pd_ord DS ++ [(i, length (at_evs T))]).
      have Hdin_new : ev_din TS' (i, length (at_evs T)) = Some (pc_dev y).
      { rewrite /ev_din Hev_at_new /= Hevdev //. }
      have Hdout_new : ev_dout TS' (i, length (at_evs T)) = Some d'.
      { rewrite /ev_dout Hev_at_new /= Hevdev //. }
      have Hordl : length (pd_ord DS') = S (length (pd_ord DS)).
      { rewrite /DS' /= length_app /=. lia. }
      have Hordold : ∀ m, (m < length (pd_ord DS))%nat →
                          pd_ord DS' !! m = pd_ord DS !! m.
      { intros m Hm. rewrite /DS' /= lookup_app_l //. }
      have Hordnew : pd_ord DS' !! length (pd_ord DS)
                     = Some (i, length (at_evs T)).
      { rewrite /DS' /= lookup_app_r; [lia|]. by rewrite Nat.sub_diag. }
      have Hdev_at' : ∀ m, (m ≤ length (pd_ord DS))%nat →
                           dev_at TS' DS' m = dev_at TS DS m.
      { intros [|m'] Hm; [done|]. simpl.
        rewrite Hordold; [lia|]. by apply (Hdev_at (S m')). }
      exists TS', DS'. split_and!.
      + exact Hpt'.
      + by rewrite /DS' /=.
      + intros m e0 Hm.
        destruct (decide (m < length (pd_ord DS))%nat) as [Hlt|Hge].
        * rewrite Hordold // in Hm.
          destruct (HW1 m e0 Hm) as (ev0 & Hev0 & Hdd).
          exists ev0. rewrite Hgrow_at; [by eexists|]. by split.
        * have Hm' : m = length (pd_ord DS).
          { apply lookup_lt_Some in Hm. rewrite Hordl in Hm. lia. }
          subst m. rewrite Hordnew in Hm. simplify_eq.
          exists ev. split; [exact Hev_at_new|]. rewrite Hevdev. by eexists.
      + intros j k ev0 Hev0 Hdd.
        destruct (Hcases j k ev0 Hev0) as [(-> & -> & ->)|Hold0].
        * exists (length (pd_ord DS)). exact Hordnew.
        * destruct (HW2 j k ev0 Hold0 Hdd) as (m & Hm).
          exists m. rewrite Hordold //. by eapply lookup_lt_Some.
      + intros m1 m2 j k1 k2 Hlt Hm1 Hm2.
        destruct (decide (m2 < length (pd_ord DS))%nat) as [H2|H2].
        * rewrite Hordold in Hm1; [lia|]. rewrite Hordold in Hm2; [lia|].
          by apply (HW3 m1 m2 j k1 k2).
        * have Hm2' : m2 = length (pd_ord DS).
          { apply lookup_lt_Some in Hm2. rewrite Hordl in Hm2. lia. }
          subst m2. rewrite Hordnew in Hm2. simplify_eq.
          rewrite Hordold in Hm1; [lia|].
          destruct (HW1 m1 (j, k1) Hm1) as (ev0 & Hev0 & _).
          rewrite /ev_at /= HT /= in Hev0.
          apply lookup_lt_Some in Hev0. lia.
      + intros m e0 Hm.
        destruct (decide (m < length (pd_ord DS))%nat) as [Hlt|Hge].
        * rewrite Hordold // in Hm.
          have Hmle : (m ≤ length (pd_ord DS))%nat by lia.
          rewrite (Hgrow_din e0 (Hold _ _ Hm)) (HW4 m e0 Hm).
          by rewrite (Hdev_at' m Hmle).
        * have Hm' : m = length (pd_ord DS).
          { apply lookup_lt_Some in Hm. rewrite Hordl in Hm. lia. }
          subst m. rewrite Hordnew in Hm. simplify_eq.
          rewrite Hdin_new (Hdev_at' _ (Nat.le_refl _)). by rewrite -HW5.
      + rewrite Hcdev Hordl /= Hordnew /=. by rewrite Hdout_new.
      + exact HW6'.
    - (* DEV-FREE: the witness is unchanged, and so is the fabric *)
      have Hd'y : d' = pc_dev y
        by destruct (Hpok _ _ _ _ _ Hps Hmark) as [-> _].
      exists TS', DS. split_and!.
      + exact Hpt'.
      + exact Hinit.
      + intros m e0 Hm.
        destruct (HW1 m e0 Hm) as (ev0 & Hev0 & Hdd).
        exists ev0. rewrite Hgrow_at; [by eexists|]. by split.
      + intros j k ev0 Hev0 Hdd.
        destruct (Hcases j k ev0 Hev0) as [(-> & -> & ->)|Hold0].
        * rewrite Hevdev in Hdd. by destruct Hdd.
        * by eapply HW2.
      + exact HW3.
      + intros m e0 Hm.
        have Hmle : (m ≤ length (pd_ord DS))%nat.
        { apply lookup_lt_Some in Hm. lia. }
        rewrite (Hgrow_din e0 (Hold _ _ Hm)) (HW4 m e0 Hm).
        by rewrite (Hdev_at m Hmle).
      + rewrite Hcdev Hd'y HW5. by rewrite (Hdev_at _ (Nat.le_refl _)).
      + exact HW6'.
  Qed.

  (** THE CONSTANT-FABRIC COLLAPSE: under a marker that never fires,
      every event of an extracted bundle is dev-free (and hence the
      witness is empty).  This is what lets the archived per-hart
      instances consume the new factorization unchanged. *)
  Lemma ptraces_dev_of_free TS DS mid c :
    (∀ p l p', pdev p l p' = false) →
    ptraces_dev_of TS DS mid c →
    ∀ i T k ev, pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
      ae_dev ev = None.
  Proof.
    intros Hno (Hpt & _ & _ & _ & _ & _ & _ & HW6) i T k ev HT Hev.
    destruct Hpt as (Himg & Hlog & _ & Hwf & _).
    have HwfT : atrace_wf (pt_img TS) (pt_log TS) i T by apply Hwf.
    destruct (asteps_wf_step _ _ _ _ _ _ _ HwfT Hev)
      as (ag & ag' & _ & _ & Hag & Hag' & _).
    destruct (HW6 i T k ev ag ag' HT Hev Hag Hag') as [?|Hm]; [done|].
    by rewrite Hno in Hm.
  Qed.

  (** THE TOP-LEVEL COMPOSITION with the witness: [wp_behavior_factor]'s
      conclusion in traced form.  The promise phase is FABRIC-CONSTANT (no
      program moves in it), so the state phase starts at the behavior's
      initial fabric — [pd_init DS = pc_dev mid = d0] — and the witness is
      the behavior's own device order. *)
  Corollary wp_behavior_traced_dev img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → wp_behavior pstep img d0 ps c →
    ∃ mid TS DS,
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid ∧
      ptraces_dev_of TS DS mid c ∧
      no_promises c.
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_factor pstep img d0 ps c Hlfp Hb)
      as (mid & Hprom & Hstate & Hnp).
    destruct (state_ptraces mid c Hpok) as (TS & DS & HTS).
    { by apply wp_lf_state_rtc. }
    by exists mid, TS, DS.
  Qed.

  (** The witness-free reading, for consumers that do not (yet) need the
      device order — the OLD [wp_behavior_traced], statement for statement
      modulo the fabric parameter. *)
  Corollary wp_behavior_traced img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → wp_behavior pstep img d0 ps c →
    ∃ mid TS,
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid ∧
      ptraces_of TS mid c ∧
      no_promises c.
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_traced_dev img d0 ps c Hpok Hlfp Hb)
      as (mid & TS & DS & ? & (? & _) & ?).
    by exists mid, TS.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** FULFILMENT ACCOUNTING

      Every log position authored by agent [i] is fulfilled exactly once
      across agent [i]'s trace.  Three ingredients:

      (1) the PROMISE PHASE puts an authored message's timestamp into its
          author's promise set ([prom_complete], an invariant of
          [wp_promise_step] runs from [wp_init]);
      (2) a trace step only DELETES from the promise set, and the deleted
          timestamp is one the agent held ([astep_ok_del]) — so membership
          decreases along the trace, strictly at a fulfil;
      (3) [no_promises] at the end forces every member deleted. *)

  Lemma prom_del_subseteq Dl pr : prom_del Dl pr ⊆ pr.
  Proof. destruct Dl as [ts|]; simpl; set_solver. Qed.

  (** (1) The promise-phase invariant. *)
  Definition prom_complete c : Prop :=
    ∀ p m i, pc_log c !! p = Some m → wm_tid m = Some i →
      ∃ ag, pc_ags c !! i = Some ag ∧ S p ∈ pa_prom ag.

  Lemma prom_complete_init img d0 ps : prom_complete (wp_init img d0 ps).
  Proof. intros p m i Hp. by rewrite /wp_init /= lookup_nil in Hp. Qed.

  Lemma prom_complete_step c c' :
    prom_complete c → wp_promise_step c c' → prom_complete c'.
  Proof.
    intros Hpc Hstep.
    destruct (wp_promise_step_inv c c' Hstep)
      as (j & agj & base & data & kc & Hlkj & _ & ->).
    have Hjlt : (j < length (pc_ags c))%nat by eapply lookup_lt_Some.
    intros p m i Hp Hm. simpl in Hp |- *.
    destruct (decide (p < length (pc_log c))%nat) as [Hlt|Hge].
    - rewrite lookup_app_l in Hp; [done|].
      destruct (Hpc p m i Hp Hm) as (ag & Hag & Hin).
      destruct (decide (i = j)) as [->|Hne].
      + exists (prom_add (S (length (pc_log c))) agj).
        split; [rewrite list_lookup_insert //|].
        assert (ag = agj) as -> by congruence.
        rewrite /prom_add /=. by apply elem_of_union_r.
      + exists ag. by rewrite list_lookup_insert_ne //.
    - have Hp' : p = length (pc_log c).
      { apply lookup_lt_Some in Hp. rewrite length_app /= in Hp. lia. }
      subst p. rewrite lookup_app_r in Hp; [lia|].
      rewrite Nat.sub_diag /= in Hp. simplify_eq/=.
      exists (prom_add (S (length (pc_log c))) agj).
      split; [rewrite list_lookup_insert //|].
      rewrite /prom_add /=. by apply elem_of_union_l, elem_of_singleton.
  Qed.

  Lemma prom_complete_run c c' :
    prom_complete c → rtc (wp_promise_step (P:=P)) c c' → prom_complete c'.
  Proof.
    intros H0 Hr. induction Hr as [|??? Hs _ IH]; [done|].
    apply IH. by eapply prom_complete_step.
  Qed.

  (** (2) Promise sets only shrink along a trace. *)
  Lemma asteps_prom_del img log i ags evs k ev ag ag' :
    asteps_wf img log i ags evs →
    evs !! k = Some ev → ags !! k = Some ag → ags !! S k = Some ag' →
    pa_prom ag' = prom_del (ae_ts ev) (pa_prom ag) ∧
    (∀ ts, ae_ts ev = Some ts → ts ∈ pa_prom ag).
  Proof.
    intros [_ Hst] Hev Hk Hk'.
    destruct (Hst k ev ag ag' Hev Hk Hk') as (st' & f & _ & Hok & ->).
    split; [done|]. intros ts Hts. by eapply astep_ok_del.
  Qed.

  Lemma asteps_prom_succ img log i ags evs k ag ag' :
    asteps_wf img log i ags evs →
    ags !! k = Some ag → ags !! S k = Some ag' →
    pa_prom ag' ⊆ pa_prom ag.
  Proof.
    intros Hwf Hk Hk'.
    have [ev Hev] : is_Some (evs !! k).
    { apply lookup_lt_is_Some_2. destruct Hwf as [Hlen _].
      apply lookup_lt_Some in Hk'. lia. }
    destruct (asteps_prom_del _ _ _ _ _ _ _ _ _ Hwf Hev Hk Hk') as [-> _].
    apply prom_del_subseteq.
  Qed.

  Lemma asteps_prom_mono img log i ags evs d :
    ∀ k ag ag',
      asteps_wf img log i ags evs →
      ags !! k = Some ag → ags !! (k + d)%nat = Some ag' →
      pa_prom ag' ⊆ pa_prom ag.
  Proof.
    induction d as [|d IH]; intros k ag ag' Hwf Hk Hkd.
    - rewrite Nat.add_0_r in Hkd. by simplify_eq.
    - have [agn Hagn] : is_Some (ags !! S k).
      { apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hkd. lia. }
      have Hstep : pa_prom agn ⊆ pa_prom ag by eapply asteps_prom_succ.
      have Heq : (k + S d)%nat = (S k + d)%nat by lia.
      rewrite Heq in Hkd.
      have Hrest : pa_prom ag' ⊆ pa_prom agn by eapply IH.
      set_solver.
  Qed.

  Lemma asteps_prom_le img log i ags evs k1 k2 ag1 ag2 :
    asteps_wf img log i ags evs →
    (k1 ≤ k2)%nat → ags !! k1 = Some ag1 → ags !! k2 = Some ag2 →
    pa_prom ag2 ⊆ pa_prom ag1.
  Proof.
    intros Hwf Hle Hk1 Hk2.
    eapply (asteps_prom_mono _ _ _ _ _ (k2 - k1)%nat); [done|done|].
    by rewrite -Nat.le_add_sub.
  Qed.

  (** (3) EXISTENCE: a promise held at the start and gone at the end was
      deleted by some event. *)
  Lemma asteps_prom_deleted img log i evs :
    ∀ ags ag ag' ts,
      asteps_wf img log i ags evs →
      ags !! 0%nat = Some ag → ags !! length evs = Some ag' →
      ts ∈ pa_prom ag → ts ∉ pa_prom ag' →
      ∃ k ev, evs !! k = Some ev ∧ ae_ts ev = Some ts.
  Proof.
    induction evs as [|ev evs IH];
      intros ags ag ag' ts Hwf H0 Hl Hin Hnin.
    - simpl in Hl. rewrite H0 in Hl. by simplify_eq.
    - destruct ags as [|a ags]; [done|]. simpl in H0. simplify_eq.
      destruct (asteps_wf_cons_inv _ _ _ _ _ _ _ Hwf)
        as (agn & st' & f & Hagn & _ & Hok & -> & Hwf').
      simpl in Hl.
      destruct (decide (ae_ts ev = Some ts)) as [Heq|Hne].
      + by exists 0%nat, ev.
      + have Hin' : ts ∈ pa_prom
            (WPAgent st' (f (pa_ws ag)) (prom_del (ae_ts ev) (pa_prom ag))).
        { simpl. destruct (ae_ts ev) as [t|]; [|done]. simpl.
          have Ht : t ≠ ts by congruence. set_solver. }
        destruct (IH ags _ ag' ts Hwf' Hagn Hl Hin' Hnin)
          as (k & ev' & Hev' & Hts').
        by exists (S k), ev'.
  Qed.

  (** UNIQUENESS: a second fulfilment of [ts] would need [ts] in the
      promise set after its first deletion. *)
  Lemma asteps_fulfil_lt img log i ags evs ts k1 k2 ev1 ev2 :
    asteps_wf img log i ags evs →
    (k1 < k2)%nat →
    evs !! k1 = Some ev1 → ae_ts ev1 = Some ts →
    evs !! k2 = Some ev2 → ae_ts ev2 = Some ts →
    False.
  Proof.
    intros Hwf Hlt He1 Hts1 He2 Hts2.
    destruct (asteps_wf_step _ _ _ _ _ _ _ Hwf He1)
      as (a1 & a1' & st1 & f1 & Ha1 & Ha1' & _ & _ & _).
    destruct (asteps_wf_step _ _ _ _ _ _ _ Hwf He2)
      as (a2 & a2' & st2 & f2 & Ha2 & _ & _ & Hok2 & _).
    destruct (asteps_prom_del _ _ _ _ _ _ _ _ _ Hwf He1 Ha1 Ha1') as [Heq _].
    have Hin2 : ts ∈ pa_prom a2 by eapply astep_ok_del.
    have Hsub : pa_prom a2 ⊆ pa_prom a1'
      by eapply (asteps_prom_le _ _ _ _ _ (S k1) k2); [done|lia|done|done].
    have Hin : ts ∈ pa_prom a1' by set_solver.
    rewrite Heq Hts1 /= in Hin. set_solver.
  Qed.

  Lemma asteps_fulfil_unique img log i ags evs ts k1 k2 ev1 ev2 :
    asteps_wf img log i ags evs →
    evs !! k1 = Some ev1 → ae_ts ev1 = Some ts →
    evs !! k2 = Some ev2 → ae_ts ev2 = Some ts →
    k1 = k2.
  Proof.
    intros Hwf He1 Hts1 He2 Hts2.
    destruct (Nat.lt_trichotomy k1 k2) as [Hlt|[->|Hgt]]; [| done |].
    - by destruct (asteps_fulfil_lt img log i ags evs ts k1 k2 ev1 ev2
                     Hwf Hlt He1 Hts1 He2 Hts2).
    - by destruct (asteps_fulfil_lt img log i ags evs ts k2 k1 ev2 ev1
                     Hwf Hgt He2 Hts2 He1 Hts1).
  Qed.

  (** THE ACCOUNTING THEOREM, on a traced behavior. *)
  Theorem wp_behavior_fulfil_once_dev img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → wp_behavior pstep img d0 ps c →
    ∃ mid TS DS,
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid ∧
      ptraces_dev_of TS DS mid c ∧
      no_promises c ∧
      (** every log position [p] authored by agent [i] is fulfilled
          EXACTLY ONCE across agent [i]'s trace *)
      (∀ p m i, pc_log mid !! p = Some m → wm_tid m = Some i →
         ∃ T, pt_trs TS !! i = Some T ∧
           (∃ k ev, at_evs T !! k = Some ev ∧ ae_ts ev = Some (S p)) ∧
           (∀ k1 k2 ev1 ev2,
              at_evs T !! k1 = Some ev1 → ae_ts ev1 = Some (S p) →
              at_evs T !! k2 = Some ev2 → ae_ts ev2 = Some (S p) →
              k1 = k2)).
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_traced_dev img d0 ps c Hpok Hlfp Hb)
      as (mid & TS & DS & Hprom & HTS & Hnp).
    exists mid, TS, DS. split_and!; [done|done|done|].
    destruct HTS as (HTS & _).
    destruct HTS as (Himg & Hlog & HlenTS & Hwf & Hfst & Hlst & _ & _ & Hlenc).
    have Hpc : prom_complete mid.
    { eapply prom_complete_run; [apply prom_complete_init|done]. }
    intros p m i Hp Hm.
    destruct (Hpc p m i Hp Hm) as (ag & Hag & Hin).
    have Hilt : (i < length (pt_trs TS))%nat.
    { rewrite HlenTS. by eapply lookup_lt_Some. }
    have [T HT] : is_Some (pt_trs TS !! i) by apply lookup_lt_is_Some_2.
    exists T. split; [done|].
    specialize (Hwf i T HT). specialize (Hfst i T HT). specialize (Hlst i T HT).
    rewrite Himg Hlog in Hwf.
    have H0 : at_ags T !! 0%nat = Some ag by rewrite Hfst Hag.
    have [agl Hagl] : is_Some (at_ags T !! length (at_evs T))
      by eapply atrace_last_is_Some.
    have Hcl : pc_ags c !! i = Some agl by rewrite -Hlst.
    have Hempty : pa_prom agl = ∅ by eapply Hnp.
    have Hnin : S p ∉ pa_prom agl by rewrite Hempty; set_solver.
    split.
    - eapply (asteps_prom_deleted (pc_img mid) (pc_log mid) i (at_evs T)
                (at_ags T) ag agl); [exact Hwf|done|done|done|done].
    - intros k1 k2 ev1 ev2 ??? ?.
      by eapply (asteps_fulfil_unique (pc_img mid) (pc_log mid) i
                   (at_ags T) (at_evs T) (S p)).
  Qed.

  (** The witness-free reading (the OLD [wp_behavior_fulfil_once]). *)
  Theorem wp_behavior_fulfil_once img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → wp_behavior pstep img d0 ps c →
    ∃ mid TS,
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid ∧
      ptraces_of TS mid c ∧
      no_promises c ∧
      (∀ p m i, pc_log mid !! p = Some m → wm_tid m = Some i →
         ∃ T, pt_trs TS !! i = Some T ∧
           (∃ k ev, at_evs T !! k = Some ev ∧ ae_ts ev = Some (S p)) ∧
           (∀ k1 k2 ev1 ev2,
              at_evs T !! k1 = Some ev1 → ae_ts ev1 = Some (S p) →
              at_evs T !! k2 = Some ev2 → ae_ts ev2 = Some (S p) →
              k1 = k2)).
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_fulfil_once_dev img d0 ps c Hpok Hlfp Hb)
      as (mid & TS & DS & ? & (? & _) & ? & ?).
    by exists mid, TS.
  Qed.

End trace.

Global Arguments astep_prog {P D} _ _ _ _.
Global Arguments asteps_wf {P D} _ _ _ _ _ _.
Global Arguments atrace_wf {P D} _ _ _ _ _.
Global Arguments ptraces_of {P D} _ _ _ _.
Global Arguments ptraces_dev_of {P D} _ _ _ _ _.
Global Arguments ptraces_wit {P D} _ _.
Global Arguments ev_at {P D} _ _.
Global Arguments ev_din {P D} _ _.
Global Arguments ev_dout {P D} _ _.
Global Arguments dev_at {P D} _ _ _.
Global Arguments evs_dev_free {D} _.
Global Arguments mk_aev {P D} _ _ _ _ _ _ _.
Global Arguments prom_complete {P D} _.

(* ------------------------------------------------------------------ *)
(** ** What W2a step 2 (the dependency graph) inherits

    - [wp_behavior_traced_dev]: a lat-free behavior is a promise phase into
      [mid], plus one trace per agent against [mid]'s frozen [(img, log)]
      whose first records are [mid]'s agents and last records are the final
      configuration's, PLUS the GLOBAL DEVICE-ORDER WITNESS [DS].  Per-agent
      program order is LIST ORDER in [at_evs]; that is one of the graph's
      two edge families, and [pd_ord DS] is the third (G3's gdev chain).
      [wp_behavior_traced] is the same statement with the witness dropped —
      the shape every current consumer takes.

    - [wp_behavior_fulfil_once] (+ [_dev]): the rf edge family's
      well-definedness.  A fulfil→read edge goes from the UNIQUE trace
      position that fulfils log position [p] to every read of [p]; this
      theorem is what makes "the" fulfilment a function of [p].  Note the
      quantification: [p] ranges over [pc_log mid] — the log is frozen
      through the whole state phase, so [mid]'s log and the final log are
      the same object.

    - THE WITNESS, for G3.  [pd_ord DS : list (agent * nat)] is a total
      order on the FABRIC-TOUCHING trace positions, in behavior order.  Its
      three usable properties are (W1) every listed position really is a
      dev-flagged event, (W2) every dev-flagged event is listed, and (W3)
      the witness order REFINES per-agent trace order — so the gdev chain's
      edges are consistent with the behavior's temporal order exactly as
      gdep2's are, and acyclicity of the union is free.

    - [ptraces_wit] (+ [ptraces_dev_of_wit], [ptraces_wit_nil]): the
      WITNESS-ONLY part of the bundle (W1–W4), i.e. everything G3/G4 need
      of [DS] that does not mention the phase's endpoints.  The replay
      never sees [mid], so this is the shape it takes; and the EMPTY
      witness satisfies it for a dev-free bundle, which is how every
      dev-free-scoped consumer instantiates the fabric-carrying theorems.

    - THE FOLD, for G4.  [dev_at TS DS m] is the fabric BEFORE witness
      position [m] ([pd_init] at the head, the previous entry's recorded
      [dout] thereafter); (W4) says a listed step reads exactly that, and
      (W5) that the phase ends at the last listed step's [dout].  So a
      replay that processes the device events IN WITNESS ORDER can carry
      the fabric as this fold and every device answer is reproduced.

    - THE CONSTANT-FABRIC COLLAPSE.  [ptraces_dev_of_free]: if the marker
      never fires, no event is dev-flagged (hence the witness is empty and
      [dev_at] is constantly [pd_init]).  That is how the archived
      per-hart-stream instances ([WeakPromise.pstep_unit], [D := unit])
      consume the new factorization unchanged.

    - [atrace_replay] is the inverse of [astep_of_atrace] for a SINGLE
      agent, and is stated for DEV-FREE traces: it rebuilds
      [rtc (wp_afree_of pstep i)] from a wf trace whose first record
      matches the configuration.  A fabric-touching trace can only be
      replayed in an order consistent with the witness, which is the
      toposort's choice and therefore G3/G4's business, not this file's.

    - G5 SANITY (recorded, not yet mechanized).  [WeakEvPf.epf_step] is the
      event language's promise-free machine over its own configuration
      [(epool * wgstate)].  Its five arms are the five [wp_pf_step] arms at
      [P := pexv6], [D := DevModel.dev_state] and [pc_dev := wgdev]
      ([WeakEvPf.ecfg_of] already projects that way).  Its marker is
      [pdev p l p' := true] exactly on the device-access steps — the
      [dev_addr]-hit branches of [EPFCycle], and [EPFDisk]/[EPFUart]/
      [EPFPlic] — all of which carry [LSilent]; every other step is
      fabric-blind and fabric-preserving, so [pdev_ok] holds.  The witness
      of an [epf_run] is then its device-access order, and G5's obligation
      is exactly: exhibit [epf_step] as [wp_pf_step] at that instance, and
      read the decomposition off [state_ptraces]. *)
