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
    [astep_ok img log i ag l f D] already collects the five state rules'
    side conditions by label, pinning BOTH the [wstate] update [f] and the
    deleted promise [D] as functions of the label; [ae_ts] is exactly that
    [D].  So [atrace_wf] says, per position: the program steps on the
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
Record aev := AEv { ae_lb : wlabel; ae_ts : option nat }.
Add Printing Constructor aev.

(** One agent's whole state phase.  [at_ags] has one more entry than
    [at_evs]: the records BEFORE each step, plus the final one. *)
Record atrace (P : Type) := ATr {
  at_ags : list (wpagent P);
  at_evs : list aev;
}.
Add Printing Constructor atrace.
Global Arguments ATr {P} _ _.
Global Arguments at_ags {P} _.
Global Arguments at_evs {P} _.

(** The whole state phase: one trace per agent (index = agent), all
    against the same frozen [(img, log)]. *)
Record ptraces (P : Type) := PTrs {
  pt_img : image;
  pt_log : list wmsg;
  pt_trs : list (atrace P);
}.
Add Printing Constructor ptraces.
Global Arguments PTrs {P} _ _ _.
Global Arguments pt_img {P} _.
Global Arguments pt_log {P} _.
Global Arguments pt_trs {P} _.

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
  Context {P : Type}.
  Context (pstep : P → wlabel → P → Prop).

  Implicit Types c : wpcfg P.
  Implicit Types T : atrace P.
  Implicit Types ag : wpagent P.
  Implicit Types ags : list (wpagent P).
  Implicit Types evs : list aev.

  (* ---------------------------------------------------------------- *)
  (** ** Well-formed traces *)

  (** The per-position condition, on the two lists (the form the
      inductions work with). *)
  Definition asteps_wf (img : image) (log : list wmsg) (i : agent)
      (ags : list (wpagent P)) (evs : list aev) : Prop :=
    length ags = S (length evs) ∧
    ∀ k ev ag ag',
      evs !! k = Some ev → ags !! k = Some ag → ags !! S k = Some ag' →
      ∃ st' f,
        pstep (pa_st ag) (ae_lb ev) st' ∧
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
      pstep (pa_st ag) (ae_lb ev) st' ∧
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
      pstep (pa_st ag) (ae_lb ev) st' ∧
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
    pstep (pa_st ag) (ae_lb ev) st' →
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

  Lemma astep_ok_ts_none img log i (ag : wpagent P) l f D :
    astep_ok img log i ag l f D →
    match l with LStore _ _ _ | LRmw _ _ _ _ _ => True | _ => D = None end.
  Proof.
    destruct l; simpl;
      [by intros [_ ->]|by intros (_ & _ & ->)|done|done|by intros [_ ->]].
  Qed.

  Lemma atrace_ts_none img log i T k ev :
    atrace_wf img log i T → at_evs T !! k = Some ev →
    match ae_lb ev with
    | LStore _ _ _ | LRmw _ _ _ _ _ => True
    | _ => ae_ts ev = None
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
  Lemma atrace_lat_free img log i T k ev :
    lat_free_prog pstep → atrace_wf img log i T →
    at_evs T !! k = Some ev → lat_free (ae_lb ev).
  Proof.
    intros Hlfp Hwf Hev.
    destruct (asteps_wf_step _ _ _ _ _ _ _ Hwf Hev)
      as (ag & ag' & st' & f & _ & _ & Hps & _ & _).
    destruct (ae_lb ev) as [|aq lat base tvs| | |]; simpl; [done| |done|done|done].
    destruct lat; [|done]. by destruct (Hlfp _ _ _ _ _ Hps).
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
    intros Hrun. revert ag.
    induction Hrun as [c|c y c' (l & Hs) Hrun IH]; intros ag Hlk.
    - exists (ATr [ag] []), ag. simpl.
      have Hwf : atrace_wf (pc_img c) (pc_log c) i (ATr [ag] [])
        by apply asteps_wf_single.
      split_and!; [done|done|done|done|done|done|done|done|done].
    - destruct (wp_astep_inv pstep i l c y Hs)
        as (ag0 & st' & f & D & Hlk0 & Hps & Hok & Hy).
      assert (ag0 = ag) as -> by congruence.
      have Hlt : (i < length (pc_ags c))%nat by eapply lookup_lt_Some.
      have Hylk : pc_ags y !! i
                  = Some (WPAgent st' (f (pa_ws ag)) (prom_del D (pa_prom ag))).
      { rewrite Hy /=. rewrite list_lookup_insert; [done|done]. }
      destruct (IH _ Hylk)
        as (T1 & ag' & Hwf1 & H01 & Hl1 & _ & Hc' & Hfr & Hlog & Himg & Hlen).
      rewrite Hy /= in Hwf1 Hfr Hlog Himg Hlen.
      exists (ATr (ag :: at_ags T1) (AEv l D :: at_evs T1)), ag'.
      have Hwf : atrace_wf (pc_img c) (pc_log c) i
                   (ATr (ag :: at_ags T1) (AEv l D :: at_evs T1)).
      { rewrite /atrace_wf /=.
        eapply (asteps_wf_cons _ _ _ _ _ (AEv l D) _ st' f); [done|done| |done].
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

  Lemma asteps_replay i evs :
    ∀ c ags ag ag',
      asteps_wf (pc_img c) (pc_log c) i ags evs →
      pc_ags c !! i = Some ag →
      ags !! 0%nat = Some ag →
      ags !! length evs = Some ag' →
      rtc (wp_astep_of pstep i) c
        (WPCfg (pc_img c) (pc_log c) (<[i := ag']> (pc_ags c))).
  Proof.
    induction evs as [|ev evs IH]; intros c ags ag ag' Hwf Hclk H0 Hl.
    - simpl in Hl. rewrite H0 in Hl. simplify_eq.
      rewrite (list_insert_id _ _ _ Hclk) wpcfg_eta. apply rtc_refl.
    - destruct ags as [|a ags]; [done|]. simpl in H0. simplify_eq.
      destruct (asteps_wf_cons_inv _ _ _ _ _ _ _ Hwf)
        as (agn & st' & f & Hagn & Hps & Hok & Hagne & Hwf').
      set c2 := WPCfg (pc_img c) (pc_log c) (<[i := agn]> (pc_ags c)).
      have Hstep : wp_astep pstep i (ae_lb ev) c c2.
      { rewrite /c2 Hagne.
        by apply (WPAStep pstep i (ae_lb ev) c ag st' f (ae_ts ev)). }
      eapply rtc_l; [by exists (ae_lb ev)|].
      have Hlk2 : pc_ags c2 !! i = Some agn.
      { rewrite /c2 /=. rewrite list_lookup_insert; [|done].
        by eapply lookup_lt_Some. }
      have Hl' : ags !! length evs = Some ag' by exact Hl.
      pose proof (IH c2 ags agn ag' Hwf' Hlk2 Hagn Hl') as Hrun.
      rewrite /c2 /= list_insert_insert in Hrun. exact Hrun.
  Qed.

  Lemma atrace_replay i c T ag ag' :
    atrace_wf (pc_img c) (pc_log c) i T →
    pc_ags c !! i = Some ag →
    at_ags T !! 0%nat = Some ag →
    at_ags T !! length (at_evs T) = Some ag' →
    rtc (wp_astep_of pstep i) c
      (WPCfg (pc_img c) (pc_log c) (<[i := ag']> (pc_ags c))).
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
      destruct (astep_of_rtc_frozen pstep j c mid Hrun) as (H1 & H2 & H3 & _).
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
      destruct (astep_of_rtc_frozen pstep j c mid Hrun) as (_ & _ & _ & Hfr).
      rewrite (IH mid c' Hph Hni). by apply Hfr.
  Qed.

  (** Agent [i]'s trace out of a whole [wp_phases] run.  [NoDup js] is
      what makes [i]'s steps contiguous; [i] need not occur in [js] (then
      the trace is the one-record trace and [i] never moved). *)
  Lemma wp_phases_agent js c c' i ag :
    NoDup js → wp_phases pstep js c c' → pc_ags c !! i = Some ag →
    ∃ T ag',
      atrace_wf (pc_img c) (pc_log c) i T ∧
      at_ags T !! 0%nat = Some ag ∧
      at_ags T !! length (at_evs T) = Some ag' ∧
      pc_ags c' !! i = Some ag'.
  Proof.
    revert c c' ag. induction js as [|j js IH]; intros c c' ag Hnd Hph Hlk;
      simpl in Hph.
    - subst c'. exists (ATr [ag] []), ag. simpl.
      split_and!; [by apply asteps_wf_single|done|done|done].
    - apply list_relations.NoDup_cons in Hnd as [Hnj Hnd].
      destruct Hph as (mid & Hrun & Hph).
      destruct (decide (j = i)) as [->|Hne].
      + destruct (astep_of_atrace i c mid ag Hrun Hlk)
          as (T & ag' & Hwf & H0 & Hl & _ & Hmid & _).
        exists T, ag'. split_and!; [done|done|done|].
        by rewrite (wp_phases_frame js mid c' i Hph Hnj).
      + destruct (astep_of_rtc_frozen pstep j c mid Hrun)
          as (Hlog & Himg & _ & Hfr).
        have Hmid : pc_ags mid !! i = Some ag by rewrite Hfr //; congruence.
        destruct (IH mid c' ag Hnd Hph Hmid) as (T & ag' & Hwf & H0 & Hl & Hc').
        exists T, ag'. rewrite Hlog Himg in Hwf.
        split_and!; [done|done|done|done].
  Qed.

  (** The traced form of a whole state phase: one trace per agent, all
      against the frozen [(img, log)], first records = [mid]'s agents,
      last records = [c]'s agents. *)
  Definition ptraces_of (TS : ptraces P) (mid c : wpcfg P) : Prop :=
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
    wp_phases pstep (seq 0 (length (pc_ags mid))) mid c →
    ∃ TS, ptraces_of TS mid c.
  Proof.
    intros Hph.
    destruct (wp_phases_frozen _ _ _ Hph) as (Hlog & Himg & Hlen).
    destruct (list_ex_of_index
      (λ i T, atrace_wf (pc_img mid) (pc_log mid) i T ∧
              at_ags T !! 0%nat = pc_ags mid !! i ∧
              at_ags T !! length (at_evs T) = pc_ags c !! i)
      (length (pc_ags mid))) as (Ts & HlenTs & HTs).
    { intros i Hi.
      have [ag Hag] : is_Some (pc_ags mid !! i) by apply lookup_lt_is_Some_2.
      destruct (wp_phases_agent _ _ _ i ag (NoDup_seq _ _) Hph Hag)
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

  (** THE TOP-LEVEL COMPOSITION: [wp_behavior_factor]'s conclusion in
      traced form. *)
  Corollary wp_behavior_traced img ps c :
    lat_free_prog pstep → wp_behavior pstep img ps c →
    ∃ mid TS,
      rtc (wp_promise_step (P:=P)) (wp_init img ps) mid ∧
      ptraces_of TS mid c ∧
      no_promises c.
  Proof.
    intros Hlfp Hb.
    destruct (wp_behavior_factor pstep img ps c Hlfp Hb)
      as (mid & Hprom & Hstate & Hnp).
    destruct (phases_ptraces mid c) as (TS & HTS).
    { apply wp_state_exec. by apply wp_lf_state_rtc. }
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

  Lemma prom_del_subseteq D pr : prom_del D pr ⊆ pr.
  Proof. destruct D as [ts|]; simpl; set_solver. Qed.

  (** (1) The promise-phase invariant. *)
  Definition prom_complete c : Prop :=
    ∀ p m i, pc_log c !! p = Some m → wm_tid m = Some i →
      ∃ ag, pc_ags c !! i = Some ag ∧ S p ∈ pa_prom ag.

  Lemma prom_complete_init img ps : prom_complete (wp_init img ps).
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
  Theorem wp_behavior_fulfil_once img ps c :
    lat_free_prog pstep → wp_behavior pstep img ps c →
    ∃ mid TS,
      rtc (wp_promise_step (P:=P)) (wp_init img ps) mid ∧
      ptraces_of TS mid c ∧
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
    intros Hlfp Hb.
    destruct (wp_behavior_traced img ps c Hlfp Hb) as (mid & TS & Hprom & HTS & Hnp).
    exists mid, TS. split_and!; [done|done|done|].
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

End trace.

Global Arguments asteps_wf {P} _ _ _ _ _ _.
Global Arguments atrace_wf {P} _ _ _ _ _.
Global Arguments ptraces_of {P} _ _ _ _.
Global Arguments prom_complete {P} _.

(* ------------------------------------------------------------------ *)
(** ** What W2a step 2 (the dependency graph) inherits

    - [wp_behavior_traced]: a lat-free behavior is a promise phase into
      [mid], plus one trace per agent against [mid]'s frozen [(img, log)],
      whose first records are [mid]'s agents and last records are the
      final configuration's.  Per-agent program order is LIST ORDER in
      [at_evs]; that is one of the graph's two edge families.

    - [wp_behavior_fulfil_once]: the other edge family's well-definedness.
      A fulfil→read edge goes from the UNIQUE trace position that fulfils
      log position [p] to every read of [p]; this theorem is what makes
      "the" fulfilment a function of [p].  Note the quantification: [p]
      ranges over [pc_log mid] — the log is frozen through the whole state
      phase ([ptraces_of]'s [pc_log c = pc_log mid]), so [mid]'s log and
      the final log are the same object.

    - The read side needs no accounting lemma: a read's timestamps are
      recorded IN THE LABEL ([LLoad]/[LRmw]'s [tvs]), so the edge source
      is read off [ae_lb] directly.

    - [atrace_replay] is the inverse of [astep_of_atrace] for a SINGLE
      agent: it rebuilds [rtc (wp_astep_of pstep i)] from a wf trace whose
      first record matches the configuration.  W2b's construction needs
      this to turn a re-ordered graph back into a run; re-assembling the
      whole state phase from per-agent replays is [wp_phases]' definition
      unfolded, and is deliberately left to the consumer (the order of the
      phases is what the topological sort chooses). *)
