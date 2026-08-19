(** * WeakCertify.v — the certification step relation and its two [w_vcap]
      lemmas (D8, slice 1)

    The port of Promising-ARM's [lcertify/Certify.v] to this tree's full
    promising machine ([WeakPromise.wpstep]).  Design and the source-level
    audit: [claude-notes/design/parm-certification-notes.md] (§1 and the
    Recommendation), [claude-notes/design/weak-memory-layer2.md] §8/§11.

    THE RELATION.  PARM's [certify_step tid = ExecUnit.state_step tid ∪
    write_step tid] (Certify.v:38), where [write_step] is
    promise-and-fulfil-at-the-top in ONE step (Certify.v:25).  Both halves
    already exist here, agent-indexed, and are reused verbatim:

      - [WeakPromiseFact.wp_astep_of pstep i] — the nine non-[WPPromise]
        arms of [wpstep] at agent [i], i.e. [state_step]; its fulfil arms
        consume an EXISTING promise at its frozen timestamp, location and
        value.
      - [WeakPromiseBridge.wp_pf_step pstep pcls i] — the promise-free
        fragment, whose [PFStore]/[PFRmw] arms are exactly [write_step]
        (append at [S (length log)], consume in the same step).  Its seven
        other arms are the corresponding [wp_astep] arms verbatim, so the
        union below is literally PARM's, with the pf fragment's class
        pinning ([pcls]) inherited on the certifying run's own appends.

    So neither half alone is the relation: [wp_pf_step] has no arm that
    fulfils an EXISTING promise, and [wp_astep] never appends.

    WHAT THIS SLICE PROVES.  [Certify.v:128/144/166]: [w_vcap] is monotone
    along a certifying run, and — the load-bearing one — once [w_vcap] has
    reached a promise's timestamp that promise can never be fulfilled
    again, because [fulfil_ok_d]'s EXT conjunct puts the pre-view (which
    dominates [w_vcap], deviation D-2) strictly below the fulfilled
    timestamp.  That is the termination guard of the restriction
    simulation ([CertifySim.sim_eu_rtc_step_bot], D8-2).

    DEPENDENCY-FREE like its parents: stdpp only. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge
                            WeakRobustGraph WeakRobustL2 WeakRobustBlocks.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** A fulfil pushes its own timestamp above [w_vcap]

    PARM's [writable]'s [EXT: view_pre.ts < ts] with [view_pre ⊒ vcap]
    (Promising.v:873, 883) — here [fulfil_ok_d]'s second conjunct with
    [WeakRobustL2.fulfil_vpre_d_vcap].  Stated on [astep_ok] so that the
    nine rules are nine lines, and the two that delete a promise are the
    only ones with content. *)
Lemma fulfil_ok_d_vcap ws rl base n ts vd :
  fulfil_ok_d ws rl base n ts vd → (w_vcap ws < ts)%nat.
Proof. intros [_ Hext]. have := fulfil_vpre_d_vcap ws rl vd. lia. Qed.

Lemma astep_ok_del_vcap {P : Type} img log i (ag : wpagent P) l f ts :
  astep_ok img log i ag l f (Some ts) → (w_vcap (pa_ws ag) < ts)%nat.
Proof.
  destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
    simpl.
  - by intros [_ ?].
  - by intros (_ & _ & ?).
  - intros (ts' & k & _ & _ & Hok & _ & [= ->]). by eapply fulfil_ok_d_vcap.
  - intros (ts' & k & _ & _ & _ & _ & _ & Hok & _ & [= ->]).
    (* the rmw checks EXT on the state AFTER its read half, whose [w_vcap]
       is at least the pre-state's *)
    have Hlt := fulfil_ok_d_vcap _ _ _ _ _ _ Hok.
    eapply Nat.le_lt_trans; [|exact Hlt].
    apply ws_le_vcap, load_post_run_d_le.
  - by intros [_ ?].
  - by intros [_ ?].
  - by intros [_ ?].
  - by intros [_ ?].
  - by intros [_ ?].
  - done.
  - done.
Qed.

(* ------------------------------------------------------------------ *)
Section certify.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).

  Implicit Types c cfg : wpcfg P D.

  (* ---------------------------------------------------------------- *)
  (** ** The relation *)

  (** PARM [Certify.v:38].  No new promises: neither disjunct is
      [WPPromise], and the pf fragment's appends are consumed in the
      step that makes them. *)
  Definition wp_cert_step (i : agent) c c' : Prop :=
    wp_astep_of pstep i c c' ∨ ∃ l, wp_pf_step pstep pcls i l c c'.

  (** Agent [i]'s outstanding promises are discharged — the per-agent
      projection of [WeakPromise.no_promises], PARM's
      [lc.(Local.promises) = bot]. *)
  Definition prom_free (i : agent) c : Prop :=
    ∀ ag, pc_ags c !! i = Some ag → pa_prom ag = ∅.

  (** PARM [Certify.v:48]. *)
  Definition wp_certify (i : agent) c : Prop :=
    ∃ c', rtc (wp_cert_step i) c c' ∧ prom_free i c'.

  Lemma no_promises_prom_free i c : no_promises c → prom_free i c.
  Proof. intros Hnp ag Hlk. by eapply Hnp. Qed.

  (** A configuration with nothing outstanding at [i] certifies in zero
      steps (PARM's seed at [Machine.no_promise]). *)
  Lemma wp_certify_prom_free i c : prom_free i c → wp_certify i c.
  Proof. intros Hpf. by exists c. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** The shape of a certification step *)

  Lemma cert_step_shape i c c' :
    wp_cert_step i c c' →
    ∃ ag ag', pc_ags c !! i = Some ag ∧
              pc_ags c' = <[i := ag']> (pc_ags c) ∧
              ws_le (pa_ws ag) (pa_ws ag').
  Proof.
    intros [[l Hs]|[l Hs]].
    - destruct (wp_astep_inv pstep i l c c' Hs)
        as (ag & st' & d' & f & Dl & Hlk & _ & Hok & ->).
      eexists ag, _. split_and!; [done|done|by eapply astep_ok_f_le].
    - by destruct (wp_pf_step_shape pstep pcls i l c c' Hs) as (_ & ? & _).
  Qed.

  Lemma cert_step_lookup i c c' ag :
    wp_cert_step i c c' → pc_ags c !! i = Some ag →
    ∃ ag', pc_ags c' !! i = Some ag' ∧ ws_le (pa_ws ag) (pa_ws ag').
  Proof.
    intros Hs Hlk.
    destruct (cert_step_shape i c c' Hs) as (ag0 & ag' & Hlk0 & Heq & Hle).
    simplify_eq. exists ag'. split; [|done].
    rewrite Heq list_lookup_insert //. by eapply lookup_lt_Some.
  Qed.

  Lemma rtc_cert_step_is_Some i c c' :
    rtc (wp_cert_step i) c c' → is_Some (pc_ags c !! i) → is_Some (pc_ags c' !! i).
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|]. intros [ag Hlk]. apply IH.
    by destruct (cert_step_lookup i x y ag Hs Hlk) as (agy & ? & _).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (1) [w_vcap] is monotone — PARM [Certify.v:128] *)

  Lemma cert_step_vcap i c c' ag ag' :
    wp_cert_step i c c' →
    pc_ags c !! i = Some ag → pc_ags c' !! i = Some ag' →
    (w_vcap (pa_ws ag) ≤ w_vcap (pa_ws ag'))%nat.
  Proof.
    intros Hs Hlk Hlk'.
    destruct (cert_step_lookup i c c' ag Hs Hlk) as (ag0 & Hlk0 & Hle).
    simplify_eq. by apply ws_le_vcap.
  Qed.

  Lemma rtc_cert_step_vcap i c c' ag ag' :
    rtc (wp_cert_step i) c c' →
    pc_ags c !! i = Some ag → pc_ags c' !! i = Some ag' →
    (w_vcap (pa_ws ag) ≤ w_vcap (pa_ws ag'))%nat.
  Proof.
    intros Hr. revert ag ag'.
    induction Hr as [c|x y z Hs _ IH]; intros ag ag' Hlk Hlk'.
    { simplify_eq. lia. }
    destruct (cert_step_lookup i x y ag Hs Hlk) as (agy & Hlky & Hle).
    have := ws_le_vcap _ _ Hle. have := IH agy ag' Hlky Hlk'. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (2) A promise at or below [w_vcap] can never be fulfilled —
         PARM [Certify.v:144]

      The write half deletes nothing: a [wp_pf_step] appends its own
      message and consumes it in the same step, leaving the promise set
      alone.

      The whole content is [astep_ok_del_vcap]: the fulfil arm's EXT check
      puts the fulfilled timestamp strictly above [w_vcap], so it is not
      the promise we are tracking. *)

  Lemma wp_pf_step_prom i l c c' ag ag' :
    wp_pf_step pstep pcls i l c c' →
    pc_ags c !! i = Some ag → pc_ags c' !! i = Some ag' →
    pa_prom ag' = pa_prom ag.
  Proof.
    intros Hs Hlk Hlk'.
    destruct Hs as
      [cfg ag0 st' d' Hlk0 Hps
      |cfg ag0 aq lat base tvs asrc st' d' Hlk0 Hps Hr
      |cfg ag0 rl base data asrc vsrc k st' d' Hlk0 Hps Hnn Hk
      |cfg ag0 aq rl base tvs data asrc vsrc k st' d' Hlk0 Hps Hnn Hlen Hr He Hk
      |cfg ag0 pr pw sr sw st' d' Hlk0 Hps|cfg ag0 st' d' Hlk0 Hps
      |cfg ag0 rd srcs st' d' Hlk0 Hps|cfg ag0 srcs st' d' Hlk0 Hps
      |cfg ag0 st' d' Hlk0 Hps].
    all: rewrite Hlk0 in Hlk; simplify_eq; simpl in Hlk'.
    all: (rewrite list_lookup_insert in Hlk';
            [by eapply lookup_lt_Some|by simplify_eq/=]).
  Qed.

  Lemma cert_step_vcap_promise i c c' ts ag ag' :
    wp_cert_step i c c' →
    pc_ags c !! i = Some ag → pc_ags c' !! i = Some ag' →
    (ts ≤ w_vcap (pa_ws ag))%nat → ts ∈ pa_prom ag → ts ∈ pa_prom ag'.
  Proof.
    intros [[l Hs]|[l Hs]] Hlk Hlk' Hvcap Hts.
    - destruct (wp_astep_inv pstep i l c c' Hs)
        as (ag0 & st' & d' & f & Dl & Hlk0 & _ & Hok & ->).
      rewrite Hlk0 in Hlk. simplify_eq. simpl in Hlk'.
      rewrite list_lookup_insert in Hlk';
        [by eapply lookup_lt_Some|simplify_eq/=].
      destruct Dl as [ts0|]; simpl; [|done].
      have Hvc := astep_ok_del_vcap _ _ _ _ _ _ _ Hok.
      have Hne : ts ≠ ts0 by lia.
      set_solver.
    - by rewrite (wp_pf_step_prom i l c c' ag ag' Hs Hlk Hlk').
  Qed.

  (** PARM [Certify.v:166]. *)
  Lemma rtc_cert_step_vcap_promise i c c' ts ag ag' :
    rtc (wp_cert_step i) c c' →
    pc_ags c !! i = Some ag → pc_ags c' !! i = Some ag' →
    (ts ≤ w_vcap (pa_ws ag))%nat → ts ∈ pa_prom ag → ts ∈ pa_prom ag'.
  Proof.
    intros Hr. revert ag ag'.
    induction Hr as [c|x y z Hs _ IH]; intros ag ag' Hlk Hlk' Hvcap Hts.
    { by simplify_eq. }
    destruct (cert_step_lookup i x y ag Hs Hlk) as (agy & Hlky & Hle).
    eapply (IH agy ag'); [done|done| |].
    - have := ws_le_vcap _ _ Hle. lia.
    - by eapply cert_step_vcap_promise.
  Qed.

  (** The contrapositive, in the shape the simulation's stopping case
      wants: if the promise is gone at the end, [w_vcap] never reached
      it. *)
  Lemma rtc_cert_step_prom_free_vcap i c c' ts ag :
    rtc (wp_cert_step i) c c' → prom_free i c' →
    pc_ags c !! i = Some ag → ts ∈ pa_prom ag →
    (w_vcap (pa_ws ag) < ts)%nat.
  Proof.
    intros Hr Hpf Hlk Hts.
    destruct (decide (ts ≤ w_vcap (pa_ws ag))%nat) as [Hle|]; [|lia].
    exfalso.
    have [ag' Hlk'] : is_Some (pc_ags c' !! i)
      by eapply rtc_cert_step_is_Some; [done|eexists].
    have := rtc_cert_step_vcap_promise i c c' ts ag ag' Hr Hlk Hlk' Hle Hts.
    rewrite (Hpf ag' Hlk'). set_solver.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** A certifying run is a run of the full machine

      [WeakPromiseBridge.wp_pf_step_rtc_wpstep] asks for [no_promises],
      which a CERTIFYING configuration never satisfies — that is the whole
      point of certifying.  The freshness the fused store needs
      ([S (length log) ∉ pa_prom ag]) is available from [cfg_wf] alone:
      [prom_wf] bounds every outstanding timestamp by [length log]. *)

  Lemma wp_pf_step_rtc_wpstep_wf i l c c' :
    cfg_wf c → wp_pf_step pstep pcls i l c c' → rtc (wpstep pstep) c c'.
  Proof.
    intros Hwf Hstep.
    have Hfresh : ∀ ag, pc_ags c !! i = Some ag →
                        S (length (pc_log c)) ∉ pa_prom ag.
    { intros ag Hlk Hin. destruct (Hwf i ag Hlk) as [_ Hp].
      destruct (Hp _ Hin) as (_ & Hle & _). lia. }
    destruct Hstep as
      [cfg ag st' d' Hlk Hps
      |cfg ag aq lat base tvs asrc st' d' Hlk Hps Hr
      |cfg ag rl base data asrc vsrc k st' d' Hlk Hps Hnn Hk
      |cfg ag aq rl base tvs data asrc vsrc k st' d' Hlk Hps Hnn Hlen Hr He Hk
      |cfg ag pr pw sr sw st' d' Hlk Hps|cfg ag st' d' Hlk Hps
      |cfg ag rd srcs st' d' Hlk Hps|cfg ag srcs st' d' Hlk Hps
      |cfg ag st' d' Hlk Hps].
    - apply rtc_once. by eapply WPSilent.
    - apply rtc_once. by eapply WPLoad.
    - eapply wpstep_store_now; [done|done|done| |by apply Hfresh].
      by destruct (Hwf i ag Hlk).
    - eapply wpstep_rmw_now; [done|done|done|done| |by apply Hfresh|done|done].
      by destruct (Hwf i ag Hlk).
    - apply rtc_once. by eapply WPFence.
    - apply rtc_once. by eapply WPDev.
    - apply rtc_once. by eapply WPRegW.
    - apply rtc_once. by eapply WPCtrl.
    - apply rtc_once. by eapply WPInstr.
  Qed.

  Lemma cert_step_rtc_wpstep i c c' :
    cfg_wf c → wp_cert_step i c c' → rtc (wpstep pstep) c c'.
  Proof.
    intros Hwf [[l Hs]|[l Hs]].
    - apply rtc_once. by eapply wp_astep_wpstep.
    - by eapply wp_pf_step_rtc_wpstep_wf.
  Qed.

  Lemma cfg_wf_cert_step i c c' :
    cfg_wf c → wp_cert_step i c c' → cfg_wf c'.
  Proof.
    intros Hwf Hs. eapply cfg_wf_reach; [done|by eapply cert_step_rtc_wpstep].
  Qed.

  Lemma rtc_cert_step_rtc_wpstep i c c' :
    cfg_wf c → rtc (wp_cert_step i) c c' → rtc (wpstep pstep) c c' ∧ cfg_wf c'.
  Proof.
    intros Hwf Hr. induction Hr as [|x y z Hs _ IH]; [by split|].
    have Hxy : rtc (wpstep pstep) x y by eapply cert_step_rtc_wpstep.
    destruct (IH (cfg_wf_reach pstep x y Hwf Hxy)) as [Hyz ?].
    split; [by etrans|done].
  Qed.

End certify.

Global Arguments wp_cert_step {P D} _ _ _ _ _.
Global Arguments wp_certify {P D} _ _ _ _.
Global Arguments prom_free {P D} _ _.

