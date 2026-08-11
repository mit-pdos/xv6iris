(** * WeakPromiseBridge.v — the erasure bridge (M6 W1, last item; D-M6-7)

    [WeakPromise.v] is the FULL promising machine (promise sets, the [lat]
    load kind, PARM-style rmw = [read_ok] + [excl_ok]); [WeakAxiomatic.v] is
    the canonical PROMISE-FREE labelled LTS ([mstate]/[mstep], executions as
    (state list, step list) pairs).  Decision D-M6-7 says the two meet by
    PROJECTION, and this file is that projection:

        every promise-free run of [WeakPromise] projects to an [exec_wf]
        execution of [WeakAxiomatic] with the same image, the same log and
        the same per-agent [wstate]s.

    The five pieces, in order:

    (A) [wp_pf_step] — the promise-free FRAGMENT of the full machine: the
        five state rules with the store and the rmw FUSED (promise at the
        fresh top, fulfil immediately, the [wpstep_store_now] shape), so no
        rule mentions a promise set.  [wp_pf_step_rtc_wpstep] shows a pf step
        is one or two [wpstep]s and [wp_pf_step_no_promises] that it keeps
        every promise set empty; hence [wp_pf_behavior]: a pf run from
        [wp_init] IS a [wp_behavior] of the full machine.

    (B) [proj_lbl] / [cfg_match] — the label and state projections.
        [LSilent ↦ None]: the axiomatic side has no program component and no
        silent arm, so silent steps STUTTER (the projected execution skips
        them).  A [LLoad aq lat …] projects to [LLoad aq …] with the [lat]
        PINNING DROPPED — sound because [WeakMem.latest_readable] says a
        latest read is in particular readable, and [rd_ok] asks only for
        readability.  Configurations project by forgetting program states and
        promise sets; because [mstate]'s [ms_ws] is a FUNCTION and a [wpcfg]'s
        agents are a LIST, the projection is stated RELATIONALLY
        ([cfg_match]) — a functional projection would need [upd_ws f i w] to
        be equal, not merely pointwise equal, to the projected function, i.e.
        functional extensionality, which this tree does not assume.

    (C) [pf_rmw_latest] — THE DOVETAIL.  [mstep]'s rmw arm demands
        [rmw_latest] (the read half takes the globally-latest message), while
        the full machine's [WPRmw] only demands [readable] + [excl_ok].  At a
        FUSED rmw the two coincide, and the missing third of the argument is
        the new configuration invariant [own_coh]: an agent's own messages
        never exceed its own coherence floor for the bytes they write.  A
        write inside the window is either another agent's ([excl_ok] kills it)
        or the reader's own ([own_coh] puts it at or below [coh], where
        [readable]'s window kills it).  This is [WeakLitmus.amo_latest_unique]
        made into an invariant argument.

    (D) [wp_pf_bridge] — the theorem: a pf run from [wp_init] projects to an
        [exec_wf] execution whose final [mstate] matches the final config.

    (E) [exec_wf_pf_run] — the reverse direction, PROVED (not just stated):
        with a program LTS admitting every label ([prog_free], the "programs
        are free" instantiation), every [exec_wf] execution over agents in
        range IS the projection of a pf run.  The bridge is therefore an
        exact characterization of the promise-free fragment, not merely a
        soundness direction.

    DEPENDENCY-FREE like its three inputs: stdpp, [WeakMem], [WeakPromise],
    [WeakPromiseFact], [WeakAxiomatic].  No Iris, no Sail, no [WeakLitmus].

    NOTE ON NAMES.  [WeakPromise] and [WeakAxiomatic] both export constructors
    [LLoad]/[LStore]/[LFence]/[LRmw] (of [wlabel] and [lbl] respectively), and
    the latter shadows the former.  Every occurrence below is therefore
    QUALIFIED. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakAxiomatic.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Two small [WeakMem]-level facts

    (They belong in [WeakMem.v]; they are here because this slice may not
    edit it — same convention as [WeakAxiomatic]'s fold lemmas.) *)

(** A message writes only inside its own byte range. *)
Lemma msg_byte_range m a :
  is_Some (msg_byte m a) →
  ∃ j : nat, (j < length (wm_data m))%nat ∧ a = wm_pa m + Z.of_nat j.
Proof.
  rewrite /msg_byte. case_bool_decide as Hle; [|by intros []].
  intros Hs. exists (Z.to_nat (a - wm_pa m)). split.
  - by eapply lookup_lt_is_Some_1.
  - lia.
Qed.

(** The [Forall] shape [load_post_run_bounded] wants, from a [read_ok].
    ([WeakPromise] proves this as a [Local Lemma], hence the copy.) *)
Lemma read_ok_ts_bounded' img log ws aq lat base tvs :
  read_ok img log ws aq lat base tvs →
  Forall (λ t, (t ≤ length log)%nat) (tvs.*1).
Proof.
  intros Hr. apply Forall_lookup_2. intros j t Hj.
  rewrite list_lookup_fmap in Hj.
  destruct (tvs !! j) as [[t' v]|] eqn:Htv; simplify_eq/=.
  destruct (Hr j t v Htv) as (Hb & _ & _).
  eapply log_byte_bounded. by eexists.
Qed.

(* ================================================================== *)
Section bridge.
  Context {P : Type}.
  Context (pstep : P → wlabel → P → Prop).

  Implicit Types c cfg : wpcfg P.

  (* ---------------------------------------------------------------- *)
  (** ** (A) The promise-free fragment

      Five arms, mirroring [mstep]'s four plus the silent step.  The store
      and rmw arms are FUSED: the message is appended at the fresh top
      [S (length log)] and consumed in the same step, so neither arm mentions
      a promise set and neither carries a [fulfil_ok] side condition — [COH]
      and [EXT] hold by construction there (see [wpstep_store_now]).  The rmw
      keeps [read_ok] and [excl_ok] verbatim from [WPRmw]; the [excl_ok]
      window is the fused one, [(t, length log]]. *)
  Inductive wp_pf_step (i : agent) : wlabel → wpcfg P → wpcfg P → Prop :=
  | PFSilent cfg ag st' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) LSilent st' →
      wp_pf_step i LSilent cfg
        (WPCfg (pc_img cfg) (pc_log cfg)
               (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags cfg)))
  | PFLoad cfg ag aq lat base tvs st' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (WeakPromise.LLoad aq lat base tvs) st' →
      read_ok (pc_img cfg) (pc_log cfg) (pa_ws ag) aq lat base tvs →
      wp_pf_step i (WeakPromise.LLoad aq lat base tvs) cfg
        (WPCfg (pc_img cfg) (pc_log cfg)
               (<[i := WPAgent st'
                         (load_post_run (pa_ws ag) aq base (tvs.*1))
                         (pa_prom ag)]> (pc_ags cfg)))
  | PFStore cfg ag rl base data st' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (WeakPromise.LStore rl base data) st' →
      data ≠ [] →
      wp_pf_step i (WeakPromise.LStore rl base data) cfg
        (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i)])
               (<[i := WPAgent st'
                         (store_post_run (pa_ws ag) rl base (length data)
                            (S (length (pc_log cfg))))
                         (pa_prom ag)]> (pc_ags cfg)))
  | PFRmw cfg ag aq rl base tvs data st' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (WeakPromise.LRmw aq rl base tvs data) st' →
      data ≠ [] →
      length tvs = length data →
      read_ok (pc_img cfg) (pc_log cfg) (pa_ws ag) aq false base tvs →
      excl_ok (pc_log cfg) i base tvs (S (length (pc_log cfg))) →
      wp_pf_step i (WeakPromise.LRmw aq rl base tvs data) cfg
        (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i)])
               (<[i := WPAgent st'
                         (store_post_run
                            (load_post_run (pa_ws ag) aq base (tvs.*1))
                            rl base (length data) (S (length (pc_log cfg))))
                         (pa_prom ag)]> (pc_ags cfg)))
  | PFFence cfg ag pr pw sr sw st' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (WeakPromise.LFence pr pw sr sw) st' →
      wp_pf_step i (WeakPromise.LFence pr pw sr sw) cfg
        (WPCfg (pc_img cfg) (pc_log cfg)
               (<[i := WPAgent st' (fence_post (pa_ws ag) pr pw sr sw)
                         (pa_prom ag)]> (pc_ags cfg))).

  Definition wp_pf_run c c' : Prop := ∃ i l, wp_pf_step i l c c'.

  (* ---------------------------------------------------------------- *)
  (** *** A pf step is one or two [wpstep]s

      The store arm is [WeakPromise.wpstep_store_now]; the rmw arm is its
      missing sibling, proved here the same way. *)

  Lemma wpstep_rmw_now cfg i ag aq rl base tvs data st' :
    pc_ags cfg !! i = Some ag →
    pstep (pa_st ag) (WeakPromise.LRmw aq rl base tvs data) st' →
    data ≠ [] →
    length tvs = length data →
    ws_bounded (pa_ws ag) (length (pc_log cfg)) →
    S (length (pc_log cfg)) ∉ pa_prom ag →
    read_ok (pc_img cfg) (pc_log cfg) (pa_ws ag) aq false base tvs →
    excl_ok (pc_log cfg) i base tvs (S (length (pc_log cfg))) →
    rtc (wpstep pstep) cfg
      (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i)])
             (<[i := WPAgent st'
                       (store_post_run
                          (load_post_run (pa_ws ag) aq base (tvs.*1))
                          rl base (length data) (S (length (pc_log cfg))))
                       (pa_prom ag)]> (pc_ags cfg))).
  Proof.
    intros Hlk Hps Hnn Hlen Hb Hfresh Hr He.
    pose proof (lookup_lt_Some _ _ _ Hlk) as Hlt.
    set ts := S (length (pc_log cfg)).
    (* step 1: promise the message at the fresh top *)
    eapply rtc_l.
    { by eapply (WPPromise pstep cfg i ag base data). }
    set mid := WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i)])
                 (<[i := WPAgent (pa_st ag) (pa_ws ag)
                           ({[ts]} ∪ pa_prom ag)]> (pc_ags cfg)).
    eapply rtc_l; [|apply rtc_refl].
    have Hmidlk : pc_ags mid !! i
                  = Some (WPAgent (pa_st ag) (pa_ws ag) ({[ts]} ∪ pa_prom ag)).
    { rewrite /mid /= list_lookup_insert //. }
    have Hmsg : pc_log mid !! (ts - 1)%nat = Some (WMsg base data (Some i)).
    { rewrite /mid /=. apply list_lookup_middle. rewrite /ts. lia. }
    (* the read half survives the append: it is a plain (lat-free) read *)
    have Hr' : read_ok (pc_img mid) (pc_log mid) (pa_ws ag) aq false base tvs.
    { rewrite /mid /=. by eapply read_ok_app. }
    have He' : excl_ok (pc_log mid) i base tvs ts.
    { rewrite /mid /=. eapply excl_ok_app; [rewrite /ts; lia|done]. }
    (* the fulfil conditions, by construction at the fresh top *)
    have Hbl : ws_bounded (load_post_run (pa_ws ag) aq base (tvs.*1))
                 (length (pc_log cfg)).
    { apply load_post_run_bounded; [done|by eapply read_ok_ts_bounded']. }
    have Hok : fulfil_ok (load_post_run (pa_ws ag) aq base (tvs.*1)) rl base
                 (length data) ts.
    { split.
      - intros j Hj. destruct Hbl as (_&_&_&_&_&Hcoh&_).
        pose proof (Hcoh (base + Z.of_nat j)). rewrite /ts. lia.
      - pose proof (fulfil_vpre_bounded _ rl _ Hbl). rewrite /ts. lia. }
    pose proof (WPRmw pstep mid i _ aq rl base tvs data ts st'
                  Hmidlk Hps Hlen ltac:(set_solver) Hmsg Hr' He' Hok) as Hrmw.
    rewrite /mid /= in Hrmw.
    have Hprom : ({[ts]} ∪ pa_prom ag) ∖ {[ts]} = pa_prom ag by set_solver.
    rewrite Hprom list_insert_insert in Hrmw.
    exact Hrmw.
  Qed.

  Lemma wp_pf_step_rtc_wpstep i l c c' :
    cfg_wf c → no_promises c → wp_pf_step i l c c' → rtc (wpstep pstep) c c'.
  Proof.
    intros Hwf Hnp Hstep. destruct Hstep as
      [cfg ag st' Hlk Hps
      |cfg ag aq lat base tvs st' Hlk Hps Hr
      |cfg ag rl base data st' Hlk Hps Hnn
      |cfg ag aq rl base tvs data st' Hlk Hps Hnn Hlen Hr He
      |cfg ag pr pw sr sw st' Hlk Hps].
    - apply rtc_once. by eapply WPSilent.
    - apply rtc_once. by eapply WPLoad.
    - eapply wpstep_store_now; [done|done|done| |].
      + by destruct (Hwf i ag Hlk).
      + rewrite (Hnp i ag Hlk). apply not_elem_of_empty.
    - eapply wpstep_rmw_now; [done|done|done|done| | |done|done].
      + by destruct (Hwf i ag Hlk).
      + rewrite (Hnp i ag Hlk). apply not_elem_of_empty.
    - apply rtc_once. by eapply WPFence.
  Qed.

  Lemma no_promises_upd c i ag st' w (lg : list wmsg) :
    no_promises c → pc_ags c !! i = Some ag →
    no_promises (WPCfg (pc_img c) lg
                   (<[i := WPAgent st' w (pa_prom ag)]> (pc_ags c))).
  Proof.
    intros Hnp Hlk j agj Hj. simpl in *.
    destruct (decide (j = i)) as [->|Hne].
    - rewrite list_lookup_insert in Hj;
        [by eapply lookup_lt_Some|simplify_eq/=]. by eapply Hnp.
    - rewrite list_lookup_insert_ne // in Hj. by eapply Hnp.
  Qed.

  Lemma wp_pf_step_no_promises i l c c' :
    no_promises c → wp_pf_step i l c c' → no_promises c'.
  Proof.
    intros Hnp Hstep. destruct Hstep; by eapply no_promises_upd.
  Qed.

  Lemma wp_pf_run_rtc_wpstep c c' :
    cfg_wf c → no_promises c → rtc wp_pf_run c c' →
    rtc (wpstep pstep) c c' ∧ cfg_wf c' ∧ no_promises c'.
  Proof.
    intros Hwf Hnp Hrun. induction Hrun as [|x y z (i & l & Hs) _ IH].
    { by split_and!. }
    pose proof (wp_pf_step_rtc_wpstep i l x y Hwf Hnp Hs) as Hxy.
    destruct (IH (cfg_wf_reach pstep x y Hwf Hxy)
                (wp_pf_step_no_promises i l x y Hnp Hs)) as (? & ? & ?).
    split_and!; [|done|done]. by etrans.
  Qed.

  (** SANITY (the worklist's "every promise-free execution is a behavior"):
      a pf run from an initial configuration is a [wp_behavior] of the FULL
      machine. *)
  Lemma wp_pf_behavior img ps c :
    rtc wp_pf_run (wp_init img ps) c → wp_behavior pstep img ps c.
  Proof.
    intros Hrun.
    have Hnp : no_promises (wp_init img ps).
    { intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
      destruct (ps !! i) as [p|]; by simplify_eq/=. }
    destruct (wp_pf_run_rtc_wpstep _ _ (cfg_wf_init img ps) Hnp Hrun)
      as (? & _ & ?).
    by split.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (B) The projections *)

  (** [LSilent] has no image: the axiomatic execution simply skips it. *)
  Definition proj_lbl (l : wlabel) : option WeakAxiomatic.lbl :=
    match l with
    | LSilent => None
    | WeakPromise.LLoad aq lat base tvs =>
        Some (WeakAxiomatic.LLoad aq base (tvs.*1) (tvs.*2))
    | WeakPromise.LStore rl base data =>
        Some (WeakAxiomatic.LStore rl base data)
    | WeakPromise.LRmw aq rl base tvs data =>
        Some (WeakAxiomatic.LRmw aq rl base (tvs.*1) (tvs.*2) data)
    | WeakPromise.LFence pr pw sr sw =>
        Some (WeakAxiomatic.LFence pr pw sr sw)
    end.

  (** The state projection, RELATIONALLY (see the header): same image, same
      log, and the [mstate]'s view function agrees with the agent list where
      the latter is defined.  Agents are the SAME [nat] indices on both
      sides. *)
  Definition cfg_match c (σ : mstate) : Prop :=
    ms_img σ = pc_img c ∧ ms_log σ = pc_log c ∧
    (∀ i ag, pc_ags c !! i = Some ag → ms_ws σ i = pa_ws ag).

  (** The functional projection, for consumers who want one: it matches. *)
  Definition proj_ws c : agent → wstate :=
    λ i, match pc_ags c !! i with Some ag => pa_ws ag | None => ws_init end.
  Definition proj_st c : mstate := MSt (pc_img c) (pc_log c) (proj_ws c).

  Lemma cfg_match_proj c : cfg_match c (proj_st c).
  Proof.
    split_and!; [done|done|]. intros i ag Hlk. rewrite /= /proj_ws Hlk //.
  Qed.

  Lemma cfg_match_log c σ : cfg_match c σ → ms_log σ = pc_log c.
  Proof. by intros (_ & ? & _). Qed.

  Lemma cfg_match_upd_gen (img : image) (lg : list wmsg)
      (ags : list (wpagent P)) i ag st' w pr (f g : agent → wstate) :
    (∀ j agj, ags !! j = Some agj → f j = pa_ws agj) →
    ags !! i = Some ag →
    g i = w →
    (∀ j, j ≠ i → g j = f j) →
    cfg_match (WPCfg img lg (<[i := WPAgent st' w pr]> ags)) (MSt img lg g).
  Proof.
    intros Hf Hlk Hgi Hgne. split_and!; [done|done|].
    intros j agj Hj. simpl in *.
    destruct (decide (j = i)) as [->|Hne].
    - rewrite list_lookup_insert in Hj;
        [by eapply lookup_lt_Some|by simplify_eq/=].
    - rewrite list_lookup_insert_ne // in Hj. rewrite Hgne //. by apply Hf.
  Qed.

  (** The read half projects: [rd_ok] is [read_ok] minus the [lat] pinning
      (which is exactly what D-M6-7's "the pinning is dropped soundly"
      means — see [WeakMem.latest_readable] for why that is the sound
      direction). *)
  Lemma read_ok_rd_ok img log ws aq lat base tvs :
    read_ok img log ws aq lat base tvs →
    rd_ok img log ws aq base (tvs.*1) (tvs.*2).
  Proof.
    intros Hr. split; [by rewrite !length_fmap|].
    intros j t v Ht Hv.
    rewrite list_lookup_fmap in Ht. rewrite list_lookup_fmap in Hv.
    destruct (tvs !! j) as [[t' v']|] eqn:Htv; simplify_eq/=.
    destruct (Hr j t v Htv) as (H1 & H2 & _). by split.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (C) [own_coh] and the dovetail

      THE NEW CONFIGURATION INVARIANT: every message in the log is at or
      below its OWN author's coherence floor for every byte it writes.  It
      holds at [wp_init] (empty log) and is preserved by every pf step: the
      store/rmw arm raises [coh] to the timestamp it just appended
      ([store_post_run_coh]); loads and fences only grow views; and another
      agent's append adds a message authored by THEM, about which the
      invariant says nothing at [i].

      This is the third of the dovetail: [readable] excludes writes in
      [(t, max vpre coh]], [excl_ok] excludes OTHER agents' writes in
      [(t, length log]], and [own_coh] puts the reader's OWN writes at or
      below its [coh] — so nothing at all writes the byte above [t]. *)
  Definition own_coh c : Prop :=
    ∀ (p : nat) m i ag a,
      pc_log c !! p = Some m → wm_tid m = Some i →
      pc_ags c !! i = Some ag → is_Some (msg_byte m a) →
      (S p ≤ coh (pa_ws ag) a)%nat.

  Lemma own_coh_init img ps : own_coh (wp_init img ps).
  Proof. intros p m i ag a Hm. by rewrite lookup_nil in Hm. Qed.

  (** The frozen-log arms (silent, load, fence). *)
  Lemma own_coh_upd c i ag st' w pr :
    own_coh c → pc_ags c !! i = Some ag → ws_le (pa_ws ag) w →
    own_coh (WPCfg (pc_img c) (pc_log c)
               (<[i := WPAgent st' w pr]> (pc_ags c))).
  Proof.
    intros Hoc Hlk Hle p m j agj a Hm Htid Hj Hb. simpl in *.
    destruct (decide (j = i)) as [->|Hne].
    - rewrite list_lookup_insert in Hj;
        [by eapply lookup_lt_Some|simplify_eq/=].
      etrans; [by eapply Hoc|]. by apply (ws_le_coh _ _ a).
    - rewrite list_lookup_insert_ne // in Hj. by eapply Hoc.
  Qed.

  (** The appending arms (store, rmw). *)
  Lemma own_coh_append c i ag st' w pr base data :
    own_coh c → pc_ags c !! i = Some ag → ws_le (pa_ws ag) w →
    (∀ j : nat, (j < length data)%nat →
       (S (length (pc_log c)) ≤ coh w (base + Z.of_nat j))%nat) →
    own_coh (WPCfg (pc_img c) (pc_log c ++ [WMsg base data (Some i)])
               (<[i := WPAgent st' w pr]> (pc_ags c))).
  Proof.
    intros Hoc Hlk Hle Hnew p m j agj a Hm Htid Hj Hb. simpl in *.
    destruct (decide (p < length (pc_log c))%nat) as [Hlt|Hge].
    - rewrite lookup_app_l in Hm; [done|].
      destruct (decide (j = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hj;
          [by eapply lookup_lt_Some|simplify_eq/=].
        etrans; [by eapply Hoc|]. by apply (ws_le_coh _ _ a).
      + rewrite list_lookup_insert_ne // in Hj. by eapply Hoc.
    - pose proof (lookup_lt_Some _ _ _ Hm) as Hp.
      rewrite length_app /= in Hp.
      have Hpe : p = length (pc_log c) by lia.
      subst p. rewrite lookup_app_r in Hm; [lia|].
      rewrite Nat.sub_diag /= in Hm. simplify_eq/=.
      rewrite list_lookup_insert in Hj;
        [by eapply lookup_lt_Some|simplify_eq/=].
      destruct (msg_byte_range _ _ Hb) as (k & Hk & ->). simpl in Hk |- *.
      by apply Hnew.
  Qed.

  Lemma own_coh_step i l c c' :
    own_coh c → wp_pf_step i l c c' → own_coh c'.
  Proof.
    intros Hoc Hstep. destruct Hstep as
      [cfg ag st' Hlk Hps
      |cfg ag aq lat base tvs st' Hlk Hps Hr
      |cfg ag rl base data st' Hlk Hps Hnn
      |cfg ag aq rl base tvs data st' Hlk Hps Hnn Hlen Hr He
      |cfg ag pr pw sr sw st' Hlk Hps].
    - eapply own_coh_upd; [done|done|reflexivity].
    - eapply own_coh_upd; [done|done|apply load_post_run_le].
    - eapply own_coh_append; [done|done|apply store_post_run_le|].
      intros j Hj. by apply (store_post_run_coh _ rl base (length data) _ j).
    - eapply own_coh_append; [done|done| |].
      + etrans; [apply load_post_run_le|apply store_post_run_le].
      + intros j Hj. by apply (store_post_run_coh _ rl base (length data) _ j).
    - eapply own_coh_upd; [done|done|apply fence_post_le].
  Qed.

  Lemma own_coh_run c c' : own_coh c → rtc wp_pf_run c c' → own_coh c'.
  Proof.
    intros Hoc Hrun. induction Hrun as [|x y z (i & l & Hs) _ IH]; [done|].
    apply IH. by eapply own_coh_step.
  Qed.

  (** THE DOVETAIL.  [readable] + [excl_ok] + [own_coh] ⊢ [rmw_latest]. *)
  Lemma pf_rmw_latest c i ag aq base tvs :
    own_coh c →
    pc_ags c !! i = Some ag →
    read_ok (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs →
    excl_ok (pc_log c) i base tvs (S (length (pc_log c))) →
    rmw_latest (pc_img c) (pc_log c) base (tvs.*1).
  Proof.
    intros Hoc Hlk Hr He j t Hj.
    rewrite list_lookup_fmap in Hj.
    destruct (tvs !! j) as [[t' v]|] eqn:Htv; simplify_eq/=.
    destruct (Hr j t v Htv) as (Hlb & [Hs Hnw] & _).
    rewrite /latest /acc_addr. split; [by eexists|].
    intros (t2 & Hlt & Hle & m & Hm & Hbm).
    destruct (decide (wm_tid m = Some i)) as [Htid|Hne].
    - (* the reader's OWN write: [own_coh] puts it at or below [coh] *)
      apply Hnw.
      pose proof (Hoc (t2 - 1)%nat m i ag (base + Z.of_nat j) Hm Htid Hlk Hbm)
        as Hcoh.
      exists t2. split_and!; [done|lia|by exists m].
    - (* another agent's write: [excl_ok] forbids it *)
      eapply (He j t v Htv).
      exists t2. split_and!; [done|lia|]. by exists m.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (D) The bridge

      One pf step projects to one [mstep] (or, for [LSilent], to nothing at
      all — the matching state is unchanged). *)
  Lemma wp_pf_step_mstep i l c c' σ :
    own_coh c → cfg_match c σ → wp_pf_step i l c c' →
    match proj_lbl l with
    | None => cfg_match c' σ
    | Some lb => ∃ σ', mstep σ i lb σ' ∧ cfg_match c' σ'
    end.
  Proof.
    intros Hoc Hm Hstep. destruct σ as [img lg f].
    destruct Hm as (Himg & Hlg & Hf). simpl in Himg, Hlg, Hf.
    destruct Hstep as
      [cfg ag st' Hlk Hps
      |cfg ag aq lat base tvs st' Hlk Hps Hr
      |cfg ag rl base data st' Hlk Hps Hnn
      |cfg ag aq rl base tvs data st' Hlk Hps Hnn Hlen Hr He
      |cfg ag pr pw sr sw st' Hlk Hps]; subst img lg; simpl.
    - (* silent: the projected state does not move *)
      eapply (cfg_match_upd_gen _ _ _ i ag st' (pa_ws ag) _ f f);
        [done|done|by apply Hf|done].
    - (* load *)
      eexists. split.
      + apply MStepLoad. simpl. rewrite (Hf i ag Hlk). by eapply read_ok_rd_ok.
      + simpl. eapply (cfg_match_upd_gen _ _ _ i ag st' _ _ f); [done|done| |].
        * rewrite upd_ws_eq (Hf i ag Hlk) //.
        * intros j Hne. by rewrite upd_ws_ne.
    - (* store *)
      eexists. split.
      + by apply MStepStore.
      + simpl. eapply (cfg_match_upd_gen _ _ _ i ag st' _ _ f); [done|done| |].
        * rewrite upd_ws_eq (Hf i ag Hlk) //.
        * intros j Hne. by rewrite upd_ws_ne.
    - (* rmw: the dovetail supplies [rmw_latest] *)
      eexists. split.
      + apply MStepRmw.
        * done.
        * by rewrite length_fmap Hlen.
        * simpl. rewrite (Hf i ag Hlk). by eapply read_ok_rd_ok.
        * simpl. by eapply pf_rmw_latest.
      + simpl. eapply (cfg_match_upd_gen _ _ _ i ag st' _ _ f); [done|done| |].
        * rewrite upd_ws_eq (Hf i ag Hlk) //.
        * intros j Hne. by rewrite upd_ws_ne.
    - (* fence *)
      eexists. split.
      + apply MStepFence.
      + simpl. eapply (cfg_match_upd_gen _ _ _ i ag st' _ _ f); [done|done| |].
        * rewrite upd_ws_eq (Hf i ag Hlk) //.
        * intros j Hne. by rewrite upd_ws_ne.
  Qed.

  (** Extending the execution by one pf step. *)
  Lemma bridge_step E i l c c' :
    exec_wf E → cfg_match c (stt E (length (ex_tr E))) →
    own_coh c → wp_pf_step i l c c' →
    ∃ E', exec_wf E' ∧ ex_img E' = ex_img E ∧
          cfg_match c' (stt E' (length (ex_tr E'))).
  Proof.
    intros HE Hm Hoc Hstep.
    pose proof (wp_pf_step_mstep i l c c' _ Hoc Hm Hstep) as Hpr.
    destruct (proj_lbl l) as [lb|].
    - destruct Hpr as (σ' & Hms & Hm').
      exists (Exec (ex_st E ++ [σ']) (ex_tr E ++ [EStep i lb])).
      pose proof HE as (Hlen & _ & _).
      have Hst0 : (0 < length (ex_st E))%nat by lia.
      split_and!.
      + apply (exec_snoc E (EStep i lb) σ'); [done|by simpl].
      + rewrite /ex_img /eimg /stt /=. rewrite lookup_app_l; [lia|done].
      + rewrite /stt /= length_app /=.
        rewrite lookup_app_r; [lia|].
        replace (length (ex_tr E) + 1 - length (ex_st E))%nat with 0%nat
          by lia.
        by simpl.
    - exists E. by split_and!.
  Qed.

  Lemma bridge_run c c' :
    rtc wp_pf_run c c' → own_coh c →
    ∀ E, exec_wf E → cfg_match c (stt E (length (ex_tr E))) →
    ∃ E', exec_wf E' ∧ ex_img E' = ex_img E ∧
          cfg_match c' (stt E' (length (ex_tr E'))).
  Proof.
    induction 1 as [|x y z (i & l & Hs) _ IH]; intros Hoc E HE Hm.
    { by exists E. }
    destruct (bridge_step E i l x y HE Hm Hoc Hs) as (E1 & HE1 & Himg1 & Hm1).
    destruct (IH (own_coh_step i l x y Hoc Hs) E1 HE1 Hm1)
      as (E2 & HE2 & Himg2 & Hm2).
    exists E2. split_and!; [done|by rewrite Himg2|done].
  Qed.

  (** THE BRIDGE THEOREM (D-M6-7's W1 obligation).  Every promise-free run
      of the full machine projects to an [exec_wf] execution of
      [WeakAxiomatic] with the same image, and whose FINAL [mstate] has the
      final configuration's log and per-agent [wstate]s.  ([cfg_match]'s
      second conjunct at the final index is literally [ex_log E = pc_log c],
      by definition of [ex_log].) *)
  Theorem wp_pf_bridge img ps c :
    rtc wp_pf_run (wp_init img ps) c →
    ∃ E, exec_wf E ∧ ex_img E = img ∧
         cfg_match c (stt E (length (ex_tr E))).
  Proof.
    intros Hrun.
    set σ0 := MSt img [] (λ _ : agent, ws_init).
    have HE : exec_wf (Exec [σ0] []) by apply exec_nil.
    have Hm0 : cfg_match (wp_init img ps) (stt (Exec [σ0] []) 0%nat).
    { split_and!; [done|done|].
      intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
      destruct (ps !! i) as [p|]; by simplify_eq/=. }
    destruct (bridge_run _ _ Hrun (own_coh_init img ps) (Exec [σ0] []) HE Hm0)
      as (E & HE' & Himg & Hm).
    exists E. by split_and!.
  Qed.

  Corollary wp_pf_bridge_log img ps c :
    rtc wp_pf_run (wp_init img ps) c →
    ∃ E, exec_wf E ∧ ex_img E = img ∧ ex_log E = pc_log c.
  Proof.
    intros Hrun. destruct (wp_pf_bridge img ps c Hrun) as (E & ? & ? & Hm).
    exists E. split_and!; [done|done|]. by apply cfg_match_log.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (E) The reverse direction: "programs are free"

      The projection of (A)–(D) loses exactly two things — the program
      component and the [lat] pinning — so it is onto as soon as the program
      LTS admits every label.  [prog_free] is that instantiation (PARM's
      "the machine is the program-agnostic part"); with it, every [exec_wf]
      execution whose agents are in range is the projection of a pf run.

      The three inverse steps: [rd_ok] rebuilds [read_ok] at [lat = false]
      (nothing to pin), [rmw_latest] rebuilds [excl_ok] (a globally-latest
      read has NO writes above it, in particular none by another agent —
      [writes_in_by_writes_in]), and a store's fresh top is where [mstep]
      appends anyway. *)
  Definition prog_free : Prop := ∀ p l p', pstep p l p'.

  Definition unproj_lbl (lb : WeakAxiomatic.lbl) : wlabel :=
    match lb with
    | WeakAxiomatic.LLoad aq base ts vs =>
        WeakPromise.LLoad aq false base (zip ts vs)
    | WeakAxiomatic.LStore rl base vs => WeakPromise.LStore rl base vs
    | WeakAxiomatic.LFence pr pw sr sw => WeakPromise.LFence pr pw sr sw
    | WeakAxiomatic.LRmw aq rl base ts rvs wvs =>
        WeakPromise.LRmw aq rl base (zip ts rvs) wvs
    end.

  Lemma rd_ok_read_ok img log ws aq base ts vs :
    rd_ok img log ws aq base ts vs →
    read_ok img log ws aq false base (zip ts vs).
  Proof.
    intros [Hlen Hall] j t v Hj. rewrite lookup_zip_with in Hj.
    destruct (ts !! j) as [t'|] eqn:Ht, (vs !! j) as [v'|] eqn:Hv;
      simplify_eq/=.
    destruct (Hall j t v Ht Hv) as [H1 H2]. rewrite /acc_addr in H1, H2.
    by split_and!.
  Qed.

  Lemma rmw_latest_excl_ok img log i base ts vs :
    rmw_latest img log base ts →
    excl_ok log i base (zip ts vs) (S (length log)).
  Proof.
    intros Hlat j t v Hj Hw. rewrite lookup_zip_with in Hj.
    destruct (ts !! j) as [t'|] eqn:Ht, (vs !! j) as [v'|] eqn:Hv;
      simplify_eq/=.
    destruct (Hlat j t Ht) as [_ Hnw]. rewrite /acc_addr in Hnw.
    apply Hnw.
    eapply writes_in_mono;
      [| |by apply (writes_in_by_writes_in log (λ tid, tid ≠ Some i))]; lia.
  Qed.

  Lemma wp_pf_step_ags_length i l c c' :
    wp_pf_step i l c c' → length (pc_ags c') = length (pc_ags c).
  Proof. destruct 1; by rewrite /= length_insert. Qed.

  Lemma mstep_wp_pf_step σ σ' i lb c :
    prog_free → cfg_match c σ → (i < length (pc_ags c))%nat →
    mstep σ i lb σ' →
    ∃ c', wp_pf_step i (unproj_lbl lb) c c' ∧ cfg_match c' σ'.
  Proof.
    intros Hpf Hm Hi Hms.
    destruct (lookup_lt_is_Some_2 (pc_ags c) i Hi) as [ag Hlk].
    destruct σ as [img lg f].
    destruct Hm as (Himg & Hlg & Hf). simpl in Himg, Hlg, Hf.
    subst img lg.
    (* the [cfg_match] obligation is the same three lines in every arm *)
    have Hmatch : ∀ (st' : P) (w : wstate) (pr : gset nat) (lg' : list wmsg),
      cfg_match (WPCfg (pc_img c) lg'
                   (<[i := WPAgent st' w pr]> (pc_ags c)))
                (MSt (pc_img c) lg' (upd_ws f i w)).
    { intros st' w pr lg'.
      eapply (cfg_match_upd_gen _ _ _ i ag st' w pr f); [done|done| |].
      - by rewrite upd_ws_eq.
      - intros j Hne. by rewrite upd_ws_ne. }
    inversion Hms as
      [aq base ts vs Hrd Hlb Hσ'
      |rl base vs Hnn Hlb Hσ'
      |pr pw sr sw Hlb Hσ'
      |aq rl base ts rvs wvs Hnn Hlen Hrd Hlat Hlb Hσ']; simplify_eq/=.
    - (* load *)
      pose proof Hrd as [Hlen _].
      eexists. split.
      + apply (PFLoad i c ag aq false base (zip ts vs) (pa_st ag));
          [done|apply Hpf|].
        rewrite -(Hf i ag Hlk). by apply rd_ok_read_ok.
      + rewrite fst_zip; [lia|]. rewrite (Hf i ag Hlk). apply Hmatch.
    - (* store *)
      eexists. split.
      + apply (PFStore i c ag rl base vs (pa_st ag));
          [done|apply Hpf|done].
      + rewrite (Hf i ag Hlk). apply Hmatch.
    - (* fence *)
      eexists. split.
      + apply (PFFence i c ag pr pw sr sw (pa_st ag)); [done|apply Hpf].
      + rewrite (Hf i ag Hlk). apply Hmatch.
    - (* rmw *)
      pose proof Hrd as [Hlen' _].
      eexists. split.
      + apply (PFRmw i c ag aq rl base (zip ts rvs) wvs (pa_st ag));
          [done|apply Hpf|done| | |].
        * rewrite length_zip_with. lia.
        * rewrite -(Hf i ag Hlk). by apply rd_ok_read_ok.
        * by apply (rmw_latest_excl_ok (pc_img c) _ i base ts rvs).
      + rewrite fst_zip; [lia|]. rewrite (Hf i ag Hlk). apply Hmatch.
  Qed.

  Lemma exec_prefix_pf_run ps E n :
    prog_free → exec_wf E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    (n ≤ length (ex_tr E))%nat →
    ∃ c, rtc wp_pf_run (wp_init (ex_img E) ps) c ∧
         length (pc_ags c) = length ps ∧ cfg_match c (stt E n).
  Proof.
    intros Hpf HE Hag. induction n as [|n IH]; intros Hn.
    - exists (wp_init (ex_img E) ps). split_and!; [done| |].
      + by rewrite /= length_map.
      + split_and!.
        * done.
        * by apply (exec_log_init E HE).
        * intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
          destruct (ps !! i) as [p|]; simplify_eq/=.
          by apply (exec_ws_init E i HE).
    - destruct (IH ltac:(lia)) as (c & Hrun & Hlen & Hm).
      destruct (exec_tr_lookup E n ltac:(lia)) as [s Hs].
      pose proof (exec_step_at E n s HE Hs) as Hms.
      destruct (mstep_wp_pf_step (stt E n) (stt E (S n)) (es_ag s)
                  (es_lb s) c Hpf Hm ltac:(rewrite Hlen; by eapply Hag) Hms)
        as (c' & Hstep & Hm').
      exists c'. split_and!; [|by rewrite (wp_pf_step_ags_length _ _ _ _ Hstep)|done].
      eapply rtc_r; [done|]. by exists (es_ag s), (unproj_lbl (es_lb s)).
  Qed.

  (** THE REVERSE BRIDGE.  With a program LTS that admits everything, every
      [exec_wf] execution over agents [0 .. length ps - 1] is the projection
      of a promise-free run of the full machine. *)
  Theorem exec_wf_pf_run ps E :
    prog_free → exec_wf E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    ∃ c, rtc wp_pf_run (wp_init (ex_img E) ps) c ∧
         cfg_match c (stt E (length (ex_tr E))).
  Proof.
    intros Hpf HE Hag.
    destruct (exec_prefix_pf_run ps E (length (ex_tr E)) Hpf HE Hag
                ltac:(lia)) as (c & ? & _ & ?).
    by exists c.
  Qed.

End bridge.

Global Arguments wp_pf_step {P} _ _ _ _ _.
Global Arguments wp_pf_run {P} _ _ _.
Global Arguments cfg_match {P} _ _.
Global Arguments own_coh {P} _.
Global Arguments proj_ws {P} _ _.
Global Arguments proj_st {P} _.
