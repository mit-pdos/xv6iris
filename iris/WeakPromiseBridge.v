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
        are free" instantiation) and an execution whose labelled classes are
        the ones the fragment would stamp ([exec_cls_ok] — see (A)), every
        [exec_wf] execution over agents in range IS the projection of a pf
        run.  The bridge is therefore an exact characterization of the
        promise-free fragment, not merely a soundness direction.

    THE CLASS IS PINNED (G6a).  Since the fragment's appending arms compute
    the class rather than binding it freely, the fragment is no longer a
    strict over-approximation of a model that computes classes — which is
    what made it unusable as a Layer-1 INSTANCE of such a model.  The
    section header on [pcls] below records the whole argument, including why
    the FULL machine deliberately keeps its free binder.

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
(** ** [msg_byte_range] and [read_ok_ts_bounded]

    Both moved with the W4 lift batch — [msg_byte_range] to [WeakMem.v] and
    [read_ok_ts_bounded] (de-[Local]'d, so the local copy
    [read_ok_ts_bounded] is gone) to [WeakPromise.v].  They are used
    verbatim below. *)

(* ================================================================== *)
Section bridge.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).

  (** THE MESSAGE CLASS, PINNED AT FULFIL TIME (G6a).  [pcls p l ws] is
      the class the machine stamps on the message a store/rmw labelled [l]
      appends, read at the FULFILLING agent's own PRE-STEP program state
      [p] and [wstate] [ws] — which is exactly the data the class is a
      function of on the model side ([WeakInterp.wm_class_of ak ws] reads
      [w_relp ws] and the ACCESS KIND, and the access kind is NOT in the
      label: [wlabel]'s [LStore] carries only [(rl, base, data)], so an
      exclusive RAM write is labelled exactly like a plain one and only the
      residual monad node — the program state — tells them apart).  It is
      ABSTRACT here, as [pstep] is: Layer 1 never inspects it.

      WHY THE PROGRAM STATE IS AN ARGUMENT (G6a follow-up).  With the
      earlier signature [wlabel → wstate → wm_class] the class function
      could not see a conditional RAM write, so an [amoswap.w.aq] (which
      xv6's [acquire] executes on every lock) appends a message the
      interpreter classes [WCexcl] while a label-indexed class function can
      only answer [WCrel]/[WCplain].  Indexing by the program state removes
      that gap at the source; nothing else about the pinning changes.

      WHY AT FULFIL AND NOT AT PROMISE.  The class is not derivable from
      the program state — the program never sees a [wstate] — so [pstep]
      cannot constrain it, and a free binder makes the promise-free
      machine a STRICT over-approximation of any model whose classes are
      computed (the G5c2 finding).  At the fulfil the agent's [wstate] IS
      in scope, so the equation is checkable, and it is checkable exactly
      there: [WeakPromise.wpstep]'s promise arm stays free, so a promise
      may still be appended with any class and only canonically-classed
      promises are ever consumed.

      HARDWARE CONTAINMENT IS PRESERVED (the PARM-containment note's G6
      addendum).  The class is OUR bookkeeping — no PARM rule reads it,
      and no [read_ok]/[excl_ok]/[fulfil_ok]/view update mentions [wm_ak]
      (see [WeakRetag]'s header for the rule-by-rule audit).  Pinning it
      therefore removes no hardware behavior: it selects, among the
      behaviors that differ ONLY in an inert tag, the one whose tag the
      model would have written.  Formally: [wp_pf_step] with [pcls] pinned
      is still a [WeakPromise.wpstep] run ([wp_pf_step_rtc_wpstep] is
      unchanged — the full machine's binder is free and accepts the pinned
      value), so every containment statement proved against the full
      machine still covers it.

      WHY ONLY THE PROMISE-FREE FRAGMENT IS PINNED (deviation, recorded).
      The consumer of the pinning is [WeakRobust.pf_violation_free_hart],
      which quantifies over [wp_pf_run] ONLY; pinning here makes that
      premise WEAKER (fewer runs to rule out) and [WeakRobustMain]'s
      conclusion STRONGER (the exhibited run is canonically classed), so
      both directions of every consumer move the right way.  Pinning
      [WeakPromise.wpstep] as well would in addition make
      [cls_canonical] a machine invariant — but it would also
      make [WeakRetag]'s retag simulation FALSE (a retagged run is not a
      run of a pinned machine), and the retag is what DISCHARGES
      canonicity today.  So the full machine keeps its free binder and the
      replay takes canonicity as [WeakRetag] supplies it. *)
  Context (pcls : P → wlabel → wstate → wm_class).

  Implicit Types c cfg : wpcfg P D.

  (* ---------------------------------------------------------------- *)
  (** ** (A) The promise-free fragment

      Five arms, mirroring [mstep]'s four plus the silent step.  The store
      and rmw arms are FUSED: the message is appended at the fresh top
      [S (length log)] and consumed in the same step, so neither arm mentions
      a promise set and neither carries a [fulfil_ok] side condition — [COH]
      and [EXT] hold by construction there (see [wpstep_store_now]).  The rmw
      keeps [read_ok] and [excl_ok] verbatim from [WPRmw]; the [excl_ok]
      window is the fused one, [(t, length log]]. *)
  Inductive wp_pf_step (i : agent) : wlabel → wpcfg P D → wpcfg P D → Prop :=
  | PFSilent cfg ag st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) LSilent st' d' →
      wp_pf_step i LSilent cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags cfg)))
  | PFLoad cfg ag aq lat base tvs asrc st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg)
            (WeakPromise.LLoad aq lat base tvs asrc) st' d' →
      read_ok_d (pc_img cfg) (pc_log cfg) (pa_ws ag) aq lat base tvs
                (srcs_view (pa_ws ag) asrc) →
      wp_pf_step i (WeakPromise.LLoad aq lat base tvs asrc) cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (load_post_run_d (pa_ws ag) aq
                            (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                         (pa_prom ag)]> (pc_ags cfg)))
  | PFStore cfg ag rl base data asrc vsrc k st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg)
            (WeakPromise.LStore rl base data asrc vsrc) st' d' →
      data ≠ [] →
      k = pcls (pa_st ag) (WeakPromise.LStore rl base data asrc vsrc)
               (pa_ws ag) →
      wp_pf_step i (WeakPromise.LStore rl base data asrc vsrc) cfg
        (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i) k]) d'
               (<[i := WPAgent st'
                         (store_post_run_d (pa_ws ag) rl
                            (srcs_view (pa_ws ag) asrc)
                            (srcs_view (pa_ws ag) vsrc)
                            base (length data)
                            (S (length (pc_log cfg))))
                         (pa_prom ag)]> (pc_ags cfg)))
  | PFRmw cfg ag aq rl base tvs data asrc vsrc k st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg)
            (WeakPromise.LRmw aq rl base tvs data asrc vsrc) st' d' →
      data ≠ [] →
      length tvs = length data →
      read_ok_d (pc_img cfg) (pc_log cfg) (pa_ws ag) aq false base tvs
                (srcs_view (pa_ws ag) asrc) →
      excl_ok (pc_log cfg) i base tvs (S (length (pc_log cfg))) →
      k = pcls (pa_st ag) (WeakPromise.LRmw aq rl base tvs data asrc vsrc)
               (pa_ws ag) →
      wp_pf_step i (WeakPromise.LRmw aq rl base tvs data asrc vsrc) cfg
        (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i) k]) d'
               (<[i := WPAgent st'
                         (store_post_run_d
                            (load_post_run_d (pa_ws ag) aq
                               (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                            rl (srcs_view (pa_ws ag) asrc)
                            (srcs_view (pa_ws ag) vsrc)
                            base (length data) (S (length (pc_log cfg))))
                         (pa_prom ag)]> (pc_ags cfg)))
  | PFFence cfg ag pr pw sr sw st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (WeakPromise.LFence pr pw sr sw) st' d' →
      wp_pf_step i (WeakPromise.LFence pr pw sr sw) cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (fence_post (pa_ws ag) pr pw sr sw)
                         (pa_prom ag)]> (pc_ags cfg)))
  (** [PFSilent]'s twin at the fabric marker [WeakPromise.LDev] — same
      update, same (absent) side conditions.  See [WeakPromise]'s header
      for why this is a separate arm and not a predicate on the silent
      one. *)
  | PFDev cfg ag st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) WeakPromise.LDev st' d' →
      wp_pf_step i WeakPromise.LDev cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags cfg)))
  (** The three dependency-only arms, [PFSilent]'s twins (D2). *)
  | PFRegW cfg ag rd srcs st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (WeakPromise.LRegW rd srcs) st' d' →
      wp_pf_step i (WeakPromise.LRegW rd srcs) cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (regw_post (pa_ws ag) rd
                            (srcs_view (pa_ws ag) srcs))
                         (pa_prom ag)]> (pc_ags cfg)))
  | PFCtrl cfg ag srcs st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (WeakPromise.LCtrl srcs) st' d' →
      wp_pf_step i (WeakPromise.LCtrl srcs) cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (ctrl_post (pa_ws ag) (srcs_view (pa_ws ag) srcs))
                         (pa_prom ag)]> (pc_ags cfg)))
  | PFInstr cfg ag st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) WeakPromise.LInstr st' d' →
      wp_pf_step i WeakPromise.LInstr cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (instr_post (pa_ws ag))
                         (pa_prom ag)]> (pc_ags cfg))).

  Definition wp_pf_run c c' : Prop := ∃ i l, wp_pf_step i l c c'.

  (* ---------------------------------------------------------------- *)
  (** *** A pf step is one or two [wpstep]s

      The store arm is [WeakPromise.wpstep_store_now]; the rmw arm is its
      sibling [WeakPromise.wpstep_rmw_now], which moved next to it with the
      W4 lift batch. *)

  Lemma wp_pf_step_rtc_wpstep i l c c' :
    cfg_wf c → no_promises c → wp_pf_step i l c c' → rtc (wpstep pstep) c c'.
  Proof.
    intros Hwf Hnp Hstep. destruct Hstep as
      [cfg ag st' d' Hlk Hps
      |cfg ag aq lat base tvs asrc st' d' Hlk Hps Hr
      |cfg ag rl base data asrc vsrc k st' d' Hlk Hps Hnn Hk
      |cfg ag aq rl base tvs data asrc vsrc k st' d' Hlk Hps Hnn Hlen Hr He Hk
      |cfg ag pr pw sr sw st' d' Hlk Hps|cfg ag st' d' Hlk Hps
      |cfg ag rd srcs st' d' Hlk Hps|cfg ag srcs st' d' Hlk Hps
      |cfg ag st' d' Hlk Hps].
    - apply rtc_once. by eapply WPSilent.
    - apply rtc_once. by eapply WPLoad.
    - eapply wpstep_store_now; [done|done|done| |].
      + by destruct (Hwf i ag Hlk).
      + rewrite (Hnp i ag Hlk). apply not_elem_of_empty.
    - eapply wpstep_rmw_now; [done|done|done|done| | |done|done].
      + by destruct (Hwf i ag Hlk).
      + rewrite (Hnp i ag Hlk). apply not_elem_of_empty.
    - apply rtc_once. by eapply WPFence.
    - (* dev: [PFSilent]'s twin *) apply rtc_once. by eapply WPDev.
    - apply rtc_once. by eapply WPRegW.
    - apply rtc_once. by eapply WPCtrl.
    - apply rtc_once. by eapply WPInstr.
  Qed.

  Lemma no_promises_upd c i ag st' w (lg : list wmsg) (dv : D) :
    no_promises c → pc_ags c !! i = Some ag →
    no_promises (WPCfg (pc_img c) lg dv
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
  Lemma wp_pf_behavior img d0 ps c :
    rtc wp_pf_run (wp_init img d0 ps) c → wp_behavior pstep img d0 ps c.
  Proof.
    intros Hrun.
    have Hnp : no_promises (wp_init img d0 ps).
    { intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
      destruct (ps !! i) as [p|]; by simplify_eq/=. }
    destruct (wp_pf_run_rtc_wpstep _ _ (cfg_wf_init img d0 ps) Hnp Hrun)
      as (? & _ & ?).
    by split.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (B) The projections *)

  (** [LSilent] and [LDev] have no image: the axiomatic execution simply
      skips them. *)
(** [k] is the class the pf step's append stamped on its message (a free
    binder of the [PFStore]/[PFRmw] arms — the pf fragment mirrors the store
    label and does not compute the class), which the axiomatic label carries
    so that the projected LOG is literally equal. *)
  Definition proj_lbl (k : wm_class) (l : wlabel) : option WeakAxiomatic.lbl :=
    match l with
    | LSilent => None
    | WeakPromise.LLoad aq lat base tvs _ =>
        Some (WeakAxiomatic.LLoad aq base (tvs.*1) (tvs.*2))
    | WeakPromise.LStore rl base data _ _ =>
        Some (WeakAxiomatic.LStore rl base data k)
    | WeakPromise.LRmw aq rl base tvs data _ _ =>
        Some (WeakAxiomatic.LRmw aq rl base (tvs.*1) (tvs.*2) data k)
    | WeakPromise.LFence pr pw sr sw =>
        Some (WeakAxiomatic.LFence pr pw sr sw)
    | WeakPromise.LDev => None   (* [LSilent]'s twin: no axiomatic image *)
    (* The dependency-only labels move no memory, so like [LSilent] they
       have no axiomatic image: the [ppo] they induce is a MACHINE
       ordering, invisible to the per-event projection. *)
    | WeakPromise.LRegW _ _ => None
    | WeakPromise.LCtrl _ => None
    | WeakPromise.LInstr => None
    (* THE RMW SPLIT (S1).  The axiomatic tier stays FUSED, so the split
       labels project to the axiomatic PLAIN load / store — the move
       [WeakInterpProj] already makes.  Nothing emits them yet. *)
    | WeakPromise.LExLoad aq base tvs _ =>
        Some (WeakAxiomatic.LLoad aq base (tvs.*1) (tvs.*2))
    | WeakPromise.LExStore rl base data _ _ =>
        Some (WeakAxiomatic.LStore rl base data k)
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

  Lemma cfg_match_upd_gen (img : image) (lg : list wmsg) (dv : D)
      (ags : list (wpagent P)) i ag st' w pr (f g : agent → wstate) :
    (∀ j agj, ags !! j = Some agj → f j = pa_ws agj) →
    ags !! i = Some ag →
    g i = w →
    (∀ j, j ≠ i → g j = f j) →
    cfg_match (WPCfg img lg dv (<[i := WPAgent st' w pr]> ags)) (MSt img lg g).
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
  (** THE DEPENDENCY VIEW IS DROPPED HERE, SOUNDLY.  [rd_ok] is the
      axiomatic side's readability at the DEPENDENCY-FREE pre-view
      [load_vpre ws aq]; [read_ok_d] gives it at the LARGER
      [load_vpre_d ws aq vaddr], and [readable] is ANTI-monotone in the
      pre-view ([WeakMem.readable_anti_vpre]), so the projection weakens —
      the sound direction, exactly as the [lat] pinning is dropped
      (D-M6-7).  The dependency ordering the machine gains is a PROGRAM
      ordering (ppo 9–11), which the axiomatic tower models on its own
      side; it is deliberately not re-encoded per event. *)
  Lemma read_ok_d_rd_ok img log ws aq lat base tvs va :
    read_ok_d img log ws aq lat base tvs va →
    rd_ok img log ws aq base (tvs.*1) (tvs.*2).
  Proof.
    intros Hr. split; [by rewrite !length_fmap|].
    intros j t v Ht Hv.
    rewrite list_lookup_fmap in Ht. rewrite list_lookup_fmap in Hv.
    destruct (tvs !! j) as [[t' v']|] eqn:Htv; simplify_eq/=.
    destruct (Hr j t v Htv) as (H1 & H2 & _). split; [done|].
    eapply readable_anti_vpre; [|exact H2]. apply load_vpre_load_vpre_d.
  Qed.

  Lemma read_ok_rd_ok img log ws aq lat base tvs :
    read_ok img log ws aq lat base tvs →
    rd_ok img log ws aq base (tvs.*1) (tvs.*2).
  Proof. apply read_ok_d_rd_ok. Qed.

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

  Lemma own_coh_init img d0 ps : own_coh (wp_init img d0 ps).
  Proof. intros p m i ag a Hm. by rewrite lookup_nil in Hm. Qed.

  (** The frozen-log arms (silent, load, fence). *)
  Lemma own_coh_upd c i ag st' w pr (dv : D) :
    own_coh c → pc_ags c !! i = Some ag → ws_le (pa_ws ag) w →
    own_coh (WPCfg (pc_img c) (pc_log c) dv
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
  Lemma own_coh_append c i ag st' w pr base data kc (dv : D) :
    own_coh c → pc_ags c !! i = Some ag → ws_le (pa_ws ag) w →
    (∀ j : nat, (j < length data)%nat →
       (S (length (pc_log c)) ≤ coh w (base + Z.of_nat j))%nat) →
    own_coh (WPCfg (pc_img c) (pc_log c ++ [WMsg base data (Some i) kc]) dv
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
      destruct (msg_byte_range _ _ Hb) as (jb & Hjb & ->). simpl in Hjb |- *.
      by apply Hnew.
  Qed.

  Lemma own_coh_step i l c c' :
    own_coh c → wp_pf_step i l c c' → own_coh c'.
  Proof.
    intros Hoc Hstep. destruct Hstep as
      [cfg ag st' d' Hlk Hps
      |cfg ag aq lat base tvs asrc st' d' Hlk Hps Hr
      |cfg ag rl base data asrc vsrc k st' d' Hlk Hps Hnn Hk
      |cfg ag aq rl base tvs data asrc vsrc k st' d' Hlk Hps Hnn Hlen Hr He Hk
      |cfg ag pr pw sr sw st' d' Hlk Hps|cfg ag st' d' Hlk Hps
      |cfg ag rd srcs st' d' Hlk Hps|cfg ag srcs st' d' Hlk Hps
      |cfg ag st' d' Hlk Hps].
    - eapply (own_coh_upd _ _ _ _ _ _ d'); [done|done|reflexivity].
    - eapply (own_coh_upd _ _ _ _ _ _ d'); [done|done|apply load_post_run_d_le].
    - eapply (own_coh_append _ _ _ _ _ _ _ _ _ d');
        [done|done|apply store_post_run_d_le|].
      intros j Hj. by apply (store_post_run_d_coh _ rl _ _ base (length data) _ j).
    - eapply (own_coh_append _ _ _ _ _ _ _ _ _ d'); [done|done| |].
      + etrans; [apply load_post_run_d_le|apply store_post_run_d_le].
      + intros j Hj. by apply (store_post_run_d_coh _ rl _ _ base (length data) _ j).
    - eapply (own_coh_upd _ _ _ _ _ _ d'); [done|done|apply fence_post_le].
    - (* dev *) eapply (own_coh_upd _ _ _ _ _ _ d'); [done|done|reflexivity].
    - eapply (own_coh_upd _ _ _ _ _ _ d'); [done|done|apply regw_post_le].
    - eapply (own_coh_upd _ _ _ _ _ _ d'); [done|done|apply ctrl_post_le].
    - eapply (own_coh_upd _ _ _ _ _ _ d'); [done|done|apply instr_post_le].
  Qed.

  Lemma own_coh_run c c' : own_coh c → rtc wp_pf_run c c' → own_coh c'.
  Proof.
    intros Hoc Hrun. induction Hrun as [|x y z (i & l & Hs) _ IH]; [done|].
    apply IH. by eapply own_coh_step.
  Qed.

  (** THE DOVETAIL.  [readable] + [excl_ok] + [own_coh] ⊢ [rmw_latest]. *)
  Lemma pf_rmw_latest c i ag aq base tvs va :
    own_coh c →
    pc_ags c !! i = Some ag →
    read_ok_d (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs va →
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
  (** THE DEPENDENCY-FREE PREMISE (D2, recorded residue).  See
      [WeakPromise.lb_depfree]: a machine step that raises a view through
      an operand list has no [mstep] image with an EQUAL post-state,
      because [WeakAxiomatic]'s [mstep] runs the dependency-free
      [load_post_run]/[store_post_run].  Closing the gap means giving the
      axiomatic side RVWMO's ppo 9–11 (deps design §3), which D2 does not
      do; the premise is discharged trivially by every instance in this
      tree, whose labels all carry empty operand lists. *)
  Lemma wp_pf_step_mstep i l c c' σ :
    lb_depfree l →
    own_coh c → cfg_match c σ → wp_pf_step i l c c' →
    ∃ k,
    match proj_lbl k l with
    | None => cfg_match c' σ
    | Some lb => ∃ σ', mstep σ i lb σ' ∧ cfg_match c' σ'
    end.
  Proof.
    intros Hdf Hoc Hm Hstep. destruct σ as [img lg f].
    destruct Hm as (Himg & Hlg & Hf). simpl in Himg, Hlg, Hf.
    destruct Hstep as
      [cfg ag st' d' Hlk Hps
      |cfg ag aq lat base tvs asrc st' d' Hlk Hps Hr
      |cfg ag rl base data asrc vsrc k st' d' Hlk Hps Hnn Hk
      |cfg ag aq rl base tvs data asrc vsrc k st' d' Hlk Hps Hnn Hlen Hr He Hk
      |cfg ag pr pw sr sw st' d' Hlk Hps|cfg ag st' d' Hlk Hps
      |cfg ag rd srcs st' d' Hlk Hps|cfg ag srcs st' d' Hlk Hps
      |cfg ag st' d' Hlk Hps]; subst img lg;
      [exists WCplain| exists WCplain| exists k| exists k| exists WCplain
      | exists WCplain| exists WCplain| exists WCplain| exists WCplain];
      simpl in Hdf |- *;
      (* the three dependency-only arms are excluded outright *)
      [| | | | | |done|done|done].
    all: repeat (match goal with
                 | H : _ ∧ _ |- _ => destruct H
                 | H : _ = [] |- _ => rewrite H; clear H
                 end);
      rewrite ?srcs_view_nil ?load_post_run_d_0 ?store_post_run_d_0.
    - (* silent: the projected state does not move *)
      eapply (cfg_match_upd_gen _ _ _ _ i ag st' (pa_ws ag) _ f f);
        [done|done|by apply Hf|done].
    - (* load *)
      eexists. split.
      + apply MStepLoad. simpl. rewrite (Hf i ag Hlk). by eapply read_ok_d_rd_ok.
      + simpl. eapply (cfg_match_upd_gen _ _ _ _ i ag st' _ _ f); [done|done| |].
        * rewrite upd_ws_eq (Hf i ag Hlk) //.
        * intros j Hne. by rewrite upd_ws_ne.
    - (* store *)
      eexists. split.
      + by apply MStepStore.
      + simpl. eapply (cfg_match_upd_gen _ _ _ _ i ag st' _ _ f); [done|done| |].
        * rewrite upd_ws_eq (Hf i ag Hlk) //.
        * intros j Hne. by rewrite upd_ws_ne.
    - (* rmw: the dovetail supplies [rmw_latest] *)
      eexists. split.
      + apply MStepRmw.
        * done.
        * by rewrite length_fmap Hlen.
        * simpl. rewrite (Hf i ag Hlk). by eapply read_ok_d_rd_ok.
        * simpl. by eapply pf_rmw_latest.
      + simpl. eapply (cfg_match_upd_gen _ _ _ _ i ag st' _ _ f); [done|done| |].
        * rewrite upd_ws_eq (Hf i ag Hlk) //.
        * intros j Hne. by rewrite upd_ws_ne.
    - (* fence *)
      eexists. split.
      + apply MStepFence.
      + simpl. eapply (cfg_match_upd_gen _ _ _ _ i ag st' _ _ f); [done|done| |].
        * rewrite upd_ws_eq (Hf i ag Hlk) //.
        * intros j Hne. by rewrite upd_ws_ne.
    - (* dev: the silent case verbatim *)
      eapply (cfg_match_upd_gen _ _ _ _ i ag st' (pa_ws ag) _ f f);
        [done|done|by apply Hf|done].
  Qed.

  (** Extending the execution by one pf step. *)
  Lemma bridge_step E i l c c' :
    lb_depfree l →
    exec_wf E → cfg_match c (stt E (length (ex_tr E))) →
    own_coh c → wp_pf_step i l c c' →
    ∃ E', exec_wf E' ∧ ex_img E' = ex_img E ∧
          cfg_match c' (stt E' (length (ex_tr E'))).
  Proof.
    intros Hdf HE Hm Hoc Hstep.
    pose proof (wp_pf_step_mstep i l c c' _ Hdf Hoc Hm Hstep) as [k Hpr].
    destruct (proj_lbl k l) as [lb|].
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

  (** The run-level dependency-free premise: the program LTS emits only
      operand-free labels.  [WeakEvPf]'s instance satisfies it at D2. *)
  Definition pstep_depfree : Prop :=
    ∀ p d l p' d', pstep p d l p' d' → lb_depfree l.

  Lemma wp_pf_step_lb_depfree i l c c' :
    pstep_depfree → wp_pf_step i l c c' → lb_depfree l.
  Proof. intros Hdf Hs. destruct Hs; by eapply Hdf. Qed.

  Lemma bridge_run c c' :
    pstep_depfree →
    rtc wp_pf_run c c' → own_coh c →
    ∀ E, exec_wf E → cfg_match c (stt E (length (ex_tr E))) →
    ∃ E', exec_wf E' ∧ ex_img E' = ex_img E ∧
          cfg_match c' (stt E' (length (ex_tr E'))).
  Proof.
    intros Hpdf. induction 1 as [|x y z (i & l & Hs) _ IH]; intros Hoc E HE Hm.
    { by exists E. }
    destruct (bridge_step E i l x y
                (wp_pf_step_lb_depfree i l x y Hpdf Hs) HE Hm Hoc Hs)
      as (E1 & HE1 & Himg1 & Hm1).
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
  Theorem wp_pf_bridge img d0 ps c :
    pstep_depfree →
    rtc wp_pf_run (wp_init img d0 ps) c →
    ∃ E, exec_wf E ∧ ex_img E = img ∧
         cfg_match c (stt E (length (ex_tr E))).
  Proof.
    intros Hpdf Hrun.
    set σ0 := MSt img [] (λ _ : agent, ws_init).
    have HE : exec_wf (Exec [σ0] []) by apply exec_nil.
    have Hm0 : cfg_match (wp_init img d0 ps) (stt (Exec [σ0] []) 0%nat).
    { split_and!; [done|done|].
      intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
      destruct (ps !! i) as [p|]; by simplify_eq/=. }
    destruct (bridge_run _ _ Hpdf Hrun (own_coh_init img d0 ps)
                (Exec [σ0] []) HE Hm0) as (E & HE' & Himg & Hm).
    exists E. by split_and!.
  Qed.

  Corollary wp_pf_bridge_log img d0 ps c :
    pstep_depfree →
    rtc wp_pf_run (wp_init img d0 ps) c →
    ∃ E, exec_wf E ∧ ex_img E = img ∧ ex_log E = pc_log c.
  Proof.
    intros Hpdf Hrun.
    destruct (wp_pf_bridge img d0 ps c Hpdf Hrun) as (E & ? & ? & Hm).
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
  (** "Programs are free" now also means FABRIC-BLIND: the LTS admits
      every label at every fabric and leaves the fabric alone.  That is
      the right generalization for the reverse bridge — the axiomatic
      side has no fabric, so a run it dictates must not need one. *)
  Definition prog_free : Prop := ∀ p d l p', pstep p d l p' d.

  Definition unproj_lbl (lb : WeakAxiomatic.lbl) : wlabel :=
    match lb with
    | WeakAxiomatic.LLoad aq base ts vs =>
        WeakPromise.LLoad aq false base (zip ts vs) []
    | WeakAxiomatic.LStore rl base vs _ => WeakPromise.LStore rl base vs [] []
    | WeakAxiomatic.LFence pr pw sr sw => WeakPromise.LFence pr pw sr sw
    | WeakAxiomatic.LRmw aq rl base ts rvs wvs _ =>
        WeakPromise.LRmw aq rl base (zip ts rvs) wvs [] []
    end.

  (** THE REVERSE BRIDGE'S ONE NEW PREMISE (G6a).  The axiomatic side
      CARRIES the class in its label ([WeakAxiomatic.lb_cls]) and the pf
      fragment now COMPUTES it, so the inverse direction is onto only for
      executions whose labelled classes are the ones [pcls] would have
      written.  This is the exact analogue of [cls_canonical] one
      layer down, and it is free for every consumer that builds its
      execution from a pf run in the first place ([wp_pf_bridge] emits
      [proj_lbl (pcls …) …]). *)
  Definition mstep_cls_ok (p : P) (σ : mstate) (i : agent)
      (lb : WeakAxiomatic.lbl) : Prop :=
    match lb with
    | WeakAxiomatic.LStore _ _ _ k => k = pcls p (unproj_lbl lb) (ms_ws σ i)
    | WeakAxiomatic.LRmw _ _ _ _ _ _ k =>
        k = pcls p (unproj_lbl lb) (ms_ws σ i)
    | _ => True
    end.

  (** The program state the equation is read at is the acting agent's, and
      under [prog_free] that state never moves (every arm below re-uses
      [pa_st ag] as the successor), so it is the agent's INITIAL program
      [ps !! es_ag s] throughout — which is why [exec_cls_ok] is indexed by
      [ps] and not by a per-step program trace ([exec] has none). *)
  Definition exec_cls_ok (ps : list P) (E : exec) : Prop :=
    ∀ n s p, ex_tr E !! n = Some s → ps !! es_ag s = Some p →
      mstep_cls_ok p (stt E n) (es_ag s) (es_lb s).

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

  (** The conclusion also records that the step left every agent's PROGRAM
      state alone: [prog_free] lets each arm re-use [pa_st ag] as the
      successor, and [exec_prefix_pf_run] needs exactly that to know which
      program state [exec_cls_ok] is speaking about. *)
  Lemma mstep_wp_pf_step σ σ' i lb c :
    prog_free → cfg_match c σ → (i < length (pc_ags c))%nat →
    (∀ ag, pc_ags c !! i = Some ag → mstep_cls_ok (pa_st ag) σ i lb) →
    mstep σ i lb σ' →
    ∃ c', wp_pf_step i (unproj_lbl lb) c c' ∧ cfg_match c' σ' ∧
          pa_st <$> pc_ags c' = pa_st <$> pc_ags c.
  Proof.
    intros Hpf Hm Hi Hck0 Hms.
    destruct (lookup_lt_is_Some_2 (pc_ags c) i Hi) as [ag Hlk].
    have Hck := Hck0 ag Hlk. clear Hck0.
    destruct σ as [img lg f].
    destruct Hm as (Himg & Hlg & Hf). simpl in Himg, Hlg, Hf.
    subst img lg.
    (* the [cfg_match] obligation is the same three lines in every arm *)
    have Hmatch : ∀ (st' : P) (w : wstate) (pr : gset nat) (lg' : list wmsg),
      cfg_match (WPCfg (pc_img c) lg' (pc_dev c)
                   (<[i := WPAgent st' w pr]> (pc_ags c)))
                (MSt (pc_img c) lg' (upd_ws f i w)).
    { intros st' w pr lg'.
      eapply (cfg_match_upd_gen _ _ _ _ i ag st' w pr f); [done|done| |].
      - by rewrite upd_ws_eq.
      - intros j Hne. by rewrite upd_ws_ne. }
    (* every arm re-uses [pa_st ag], so the program-state projection is
       untouched *)
    have Hst : ∀ (w : wstate) (pr : gset nat),
      pa_st <$> (<[i := WPAgent (pa_st ag) w pr]> (pc_ags c))
      = pa_st <$> pc_ags c.
    { intros w pr. rewrite list_fmap_insert /=.
      apply list_insert_id. by rewrite list_lookup_fmap Hlk. }
    (* [Hck] is REVERTED across the inversion: [simplify_eq/=] would reduce
       [mstep_cls_ok] at the constructor and substitute the class binder
       away, which is exactly the binder each arm still has to name. *)
    revert Hck.
    inversion Hms as
      [aq base ts vs Hrd Hlb Hσ'
      |rl base vs kc Hnn Hlb Hσ'
      |pr pw sr sw Hlb Hσ'
      |aq rl base ts rvs wvs kc Hnn Hlen Hrd Hlat Hlb Hσ']; simplify_eq/=;
      intros Hck.
    - (* load *)
      pose proof Hrd as [Hlen _].
      eexists. split_and!.
      + apply (PFLoad i c ag aq false base (zip ts vs) [] (pa_st ag)
                 (pc_dev c)); [done|apply Hpf|].
        rewrite srcs_view_nil read_ok_d_0 -(Hf i ag Hlk).
        by apply rd_ok_read_ok.
      + rewrite srcs_view_nil load_post_run_d_0 fst_zip; [lia|].
        rewrite (Hf i ag Hlk). apply Hmatch.
      + apply Hst.
    - (* store *)
      eexists. split_and!.
      + apply (PFStore i c ag rl base vs [] [] kc (pa_st ag) (pc_dev c));
          [done|apply Hpf|done|].
        rewrite -(Hf i ag Hlk). exact Hck.
      + rewrite !srcs_view_nil store_post_run_d_0 (Hf i ag Hlk). apply Hmatch.
      + apply Hst.
    - (* fence *)
      eexists. split_and!.
      + apply (PFFence i c ag pr pw sr sw (pa_st ag) (pc_dev c));
          [done|apply Hpf].
      + rewrite (Hf i ag Hlk). apply Hmatch.
      + apply Hst.
    - (* rmw *)
      pose proof Hrd as [Hlen' _].
      eexists. split_and!.
      + apply (PFRmw i c ag aq rl base (zip ts rvs) wvs [] [] kc (pa_st ag)
                 (pc_dev c));
          [done|apply Hpf|done| | | |].
        * rewrite length_zip_with. lia.
        * rewrite srcs_view_nil read_ok_d_0 -(Hf i ag Hlk).
          by apply rd_ok_read_ok.
        * by apply (rmw_latest_excl_ok (pc_img c) _ i base ts rvs).
        * rewrite -(Hf i ag Hlk). exact Hck.
      + rewrite !srcs_view_nil load_post_run_d_0 store_post_run_d_0 fst_zip;
          [lia|].
        rewrite (Hf i ag Hlk). apply Hmatch.
      + apply Hst.
  Qed.

  Lemma exec_prefix_pf_run ps d0 E n :
    prog_free → exec_wf E → exec_cls_ok ps E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    (n ≤ length (ex_tr E))%nat →
    ∃ c, rtc wp_pf_run (wp_init (ex_img E) d0 ps) c ∧
         length (pc_ags c) = length ps ∧ pa_st <$> pc_ags c = ps ∧
         cfg_match c (stt E n).
  Proof.
    intros Hpf HE Hck Hag. induction n as [|n IH]; intros Hn.
    - exists (wp_init (ex_img E) d0 ps). split_and!; [done| | |].
      + by rewrite /= length_map.
      + rewrite /wp_init /=. rewrite -list_fmap_compose.
        by apply list_fmap_id.
      + split_and!.
        * done.
        * by apply (exec_log_init E HE).
        * intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
          destruct (ps !! i) as [p|]; simplify_eq/=.
          by apply (exec_ws_init E i HE).
    - destruct (IH ltac:(lia)) as (c & Hrun & Hlen & Hst & Hm).
      destruct (exec_tr_lookup E n ltac:(lia)) as [s Hs].
      pose proof (exec_step_at E n s HE Hs) as Hms.
      destruct (mstep_wp_pf_step (stt E n) (stt E (S n)) (es_ag s)
                  (es_lb s) c Hpf Hm ltac:(rewrite Hlen; by eapply Hag)
                  (λ ag Hlk, Hck n s (pa_st ag) Hs
                     ltac:(rewrite -Hst list_lookup_fmap Hlk; done))
                  Hms)
        as (c' & Hstep & Hm' & Hst').
      exists c'. split_and!;
        [|by rewrite (wp_pf_step_ags_length _ _ _ _ Hstep)| |done].
      + eapply rtc_r; [done|]. by exists (es_ag s), (unproj_lbl (es_lb s)).
      + by rewrite Hst'.
  Qed.

  (** THE REVERSE BRIDGE.  With a program LTS that admits everything, every
      [exec_wf] execution over agents [0 .. length ps - 1] is the projection
      of a promise-free run of the full machine. *)
  Theorem exec_wf_pf_run ps d0 E :
    prog_free → exec_wf E → exec_cls_ok ps E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    ∃ c, rtc wp_pf_run (wp_init (ex_img E) d0 ps) c ∧
         cfg_match c (stt E (length (ex_tr E))).
  Proof.
    intros Hpf HE Hck Hag.
    destruct (exec_prefix_pf_run ps d0 E (length (ex_tr E)) Hpf HE Hck Hag
                ltac:(lia)) as (c & ? & _ & _ & ?).
    by exists c.
  Qed.

End bridge.

Global Arguments wp_pf_step {P D} _ _ _ _ _ _.
Global Arguments wp_pf_run {P D} _ _ _ _.
Global Arguments cfg_match {P D} _ _.
Global Arguments own_coh {P D} _.
Global Arguments proj_ws {P D} _ _.
Global Arguments proj_st {P D} _.
