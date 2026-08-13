(** * WeakSailCone.v — THE pxv6 INSTANTIATION OF THE CONE, AND THE
      COMPLETION PASS (lift stage B4)

    [WeakRobustCone.bad_edge_violates_blocks] replays the minimal bad
    edge's cone in a BLOCK-CONTIGUOUS order, over an ABSTRACT boundary
    predicate [bnd] and two premises about it ([Hbnd0], [Hcsl]).  This
    file instantiates that theorem at the concrete xv6 program
    ([WeakCompose.pstep_xv6 riscv_step] on [pxv6]), discharges its two
    boundary premises from sharper trace-level ones, classifies the
    resulting cut states, and runs [WeakSailComplete]'s completions on
    top — producing a promise-free run of the real program that still
    violates and whose every agent is at an instruction boundary.

    ------------------------------------------------------------------------
    §1  THE BOUNDARY AND THE QUIET PREDICATE at [pxv6].

    [pbnd] — a hart with no in-flight instruction and no parked fence, a
    disk with an empty burst buffer.  [pquiet] — a hart whose residual is
    silent-to-[Interface.Ret] ([WeakSailComplete.quiet_tail]), a disk with
    an empty buffer.  [pbnd] implies [pquiet] (a hart at [sp_m = None] is
    vacuously quiet).

    DEVIATION FROM THE STAGE-B4 SKETCH: [pquiet] is NOT decidable and no
    instance is provided.  [quiet_tail] quantifies over EVERY value a
    [Interface.Choose]/[Interface.RegRead] continuation may receive, and
    those types include [Z]; the predicate is a genuine coinductive-flavoured
    ∀ and there is nothing to decide it with.  Nothing needs it:
    [WeakRobustCone] asks for [Decision (bnd p)] only, which [pbnd] has
    ([sp_m]/[sp_fence] are option matches and [pend] a list match).

    §2–§3  THE QUIET STEP LEMMA and the trace induction.  From a [pquiet],
    non-[pbnd] state every [pstep_xv6] step carries a NON-MEMORY label and
    lands [pquiet] again ([pquiet_step]).  Iterated along a trace
    ([pquiet_upto]), that is exactly [WeakRobustCone]'s [Hcsl] — derived
    here ([pcsl_of_pcq]) from the sharper, per-edge premise [Hcq] ("the
    post-state of a cross-edge source is quiet").  [pbnd0_of_ps] is the
    other, trivial half.

    §4–§5  THE [psail] ↔ [pxv6] TRANSPORT.  [WeakSailComplete]'s
    completions live on [wpcfg psail]; the cone's configurations are
    [wpcfg pxv6].  A completion moves ONE agent and reads/writes only the
    log, the image and that agent's slot, so it transports across the
    species embedding under [hlink] (image, log, agent [i]'s record) with
    NO invariant about the other agents.  [prj_cfg] builds the [psail]
    side (non-hart agents get the running hart's own state as an inert
    filler), [pf_step_lift] moves one step back, and [xquiet_complete] /
    [xtail_complete] are the two completions at [pxv6].  [pf_xsolo] /
    [pf_xquiet] are [WeakSailLTS2.pf_solo] / the quiet solo step at
    [pxv6], over [pstep_ni_xv6] (the irq-free fragment).

    §6  [nproc_mem]: an agent's slice of a duplicate-free, downward-closed
    order is exactly its first [nproc] events — the counting fact
    [WeakRobustSim.qcfg]'s cut index needs and that the packaged cone
    theorem does not export.

    §7  THE CUT CLASSIFICATION ([cut_pquiet]).  Every agent but the reader
    is left QUIET by the block-contiguous replay: either it has no cone
    event (and sits at its initial, boundary state — [Hps_bnd]), or its
    LAST cone event is a CROSS SOURCE, because the first [gdep2] step out
    of it cannot stay inside the agent (that would name a strictly later
    cone event of the same agent, contradicting lastness through
    [WeakRobustCone.gdep2_sa_lt]); then [Hcq] applies to the record right
    after it.

    §8–§9  THE COMPLETION PASS and [cone_segments].

    ------------------------------------------------------------------------
    WHAT IS DELIVERED, AND WHAT IS NOT (read before building on this).

    [cone_segments] gives: the block-contiguous cone chain of
    [WeakRobustCone] verbatim at [bnd := pbnd]; a further chain of SOLO,
    irq-free [pf_xsolo] SEGMENTS (one per completed agent, the reader's
    tail first) reaching a configuration [cf] at which EVERY agent is at
    an instruction boundary; and the violation, in both [violates_at] and
    [violation_hart] form, at [cf].

    NOT delivered, and needed by stage B5:

    (i) RUN SURGERY.  The epilogues are appended at the END of the run,
        not spliced back to just after their agent's last chain step.
        [WeakSailComplete.pf_run_insert_local] is the lemma that moves
        them ([pf_xquiet] runs ARE [pf_quiet_run]s of the same agent, and
        the chain's per-event agent list is exported), but the induction
        that performs the splice for every agent at once is not here.
        Consequently [seg_ok] only requires a segment to END at a
        boundary, not to START at one, and the chain's own steps are not
        grouped into blocks at all.

    (ii) The three SEGMENT KINDS.  [seg_ok] has no [irq_deliver] arm and
        no disk burst/emit-group arm, so the premises the sketch called
        [Hirqb] (deliveries land at boundaries) and (P4) (the disk cut is
        at a group boundary) are NOT taken and NOT used.

    (iii) [cls_canon] / [rmw_tight] AT REPLAYED STEPS.  The completions'
        own appends are canonical by construction ([pf_xsolo] carries
        [xcls_canon] and [xrmw_tight]), but the CHAIN's steps are exported
        as bare [WeakRobustBlocks.cstep]s: the [cls_canonical] premise and
        the [w_relp]-independence-of-σ transfer, and the [own_coh]
        derivation of [rmw_tight] at replayed rmws, are not done.  Neither
        premise is taken here.

    THE PREMISE LEDGER of §9, beyond the mirrored [WeakRobustCone] context:
    [Hps_bnd] (initial states are boundaries), [Hcq] (the post-state of a
    cross-edge source is quiet), [Hres] (every trace record's residual is
    [sail_shaped], [sail_live] and oracle-consistent), [Himgt]
    ([img_total]).  Layer-1's two side conditions are NOT premises —
    [WeakCompose.xv6_lat_free] and [xv6_ts_oblivious] discharge them.

    NOTE ON NAMES.  [WeakAxiomatic] is imported FIRST so that
    [WeakPromise]'s [wlabel] constructors shadow its [lbl] ones, exactly
    as in [WeakRobustCone.v] and [WeakSailLTS.v]; every occurrence is
    QUALIFIED [WeakPromise.LLoad] &c. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.
From xv6iris Require Import WeakRobust WeakRobustTrace WeakRobustGraph
                            WeakRobustProv WeakRobustLin WeakRobustOrd
                            WeakRobustSim WeakRobustMain WeakRobustBlocks
                            WeakRobustCone.
From xv6iris Require Import WeakInterp WeakInterpProj WeakSailLTS WeakSailLTS2
                            WeakSailComplete.
Require Import RiscvLang WeakLang.
From xv6iris Require Import WeakCompose.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The boundary and the quiet predicate at [pxv6] *)

Definition pbnd (p : pxv6) : Prop :=
  match p with
  | PHart q => sp_m q = None ∧ sp_fence q = None
  | PDisk _ pend => pend = []
  end.

Definition pquiet (p : pxv6) : Prop :=
  match p with
  | PHart q => psail_quiet q
  | PDisk _ pend => pend = []
  end.

Global Instance pbnd_dec p : Decision (pbnd p).
Proof.
  destruct p as [q|d pend]; simpl.
  - destruct (sp_m q), (sp_fence q);
      solve [left; by split | right; by intros [Hx Hy]].
  - destruct pend; [by left|right; by intros ?].
Defined.

Lemma pbnd_pquiet p : pbnd p → pquiet p.
Proof.
  destruct p as [q|d pend]; simpl; [|done].
  rewrite /psail_quiet. by intros [-> _].
Qed.

(** A quiet label writes nothing and reads nothing. *)
Lemma lbl_quiet_nonmem l :
  lbl_quiet l → lb_writes l = false ∧ lb_loads l = false.
Proof. by intros [->|(?&?&?&?&->)]. Qed.

(* ====================================================================== *)
(** ** 2. The quiet step lemma *)

(** From a QUIET state that is not yet at a boundary, EVERY step of the
    concrete program emits a non-memory label and stays quiet.  This is
    the whole content of [WeakRobustCone]'s [Hcsl] at [pxv6]; §3 iterates
    it along a trace. *)
Lemma pquiet_step (next : bool → M unit) p l p' :
  pquiet p → ¬ pbnd p → pstep_xv6 next p l p' →
  (lb_writes l = false ∧ lb_loads l = false) ∧ pquiet p'.
Proof.
  intros Hq Hnb Hstep.
  (* the mismatched species are stuck, and the disk's own case is VACUOUS:
     there [pquiet] IS [pbnd], so [Hq] and [Hnb] contradict *)
  destruct p as [q|d pend], p' as [q'|d' pend']; simpl in Hstep;
    try (by destruct Hstep).
  simpl in Hq, Hnb |- *. rewrite /psail_quiet in Hq |- *.
  rewrite /sail_step in Hstep.
  destruct (sp_fence q) as [[[[pr pw] sr] sw]|] eqn:Hf.
  { destruct Hstep as [-> ->]. simpl. by split; [split|]. }
  (* no parked fence: [¬ pbnd] forces an in-flight instruction *)
  destruct (sp_m q) as [m|] eqn:Hm; [|exfalso; apply Hnb; by split].
  destruct Hstep as [(-> & v & iq & _ & ->)|Hstep].
  { simpl. rewrite Hm. by split; [split|]. }
  rewrite /sail_mstep in Hstep.
  destruct m as [y|T oc k]; [by destruct Hstep as [-> ->]; split; [split|]|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hq, Hstep;
    try (by destruct Hq); try (by destruct Hstep);
    try (by destruct Hstep as [-> ->]; simpl; split; [split|apply Hq]).
  - (* Barrier: the label table *)
    destruct Hstep as [-> ->]. simpl.
    split; [by apply lbl_quiet_nonmem, barrier_lbl_quiet|by apply Hq].
  - (* Choose *)
    destruct Hstep as [-> (ch & ->)]. simpl.
    split; [by split|by apply (quiet_tail_choose ty k Hq)].
Qed.

(* ====================================================================== *)
(** ** 3. Along a trace: the sharp premise [Hcq] discharges [Hcsl]

    [WeakRobustCone] takes [Hcsl] — "after a cross-edge source, and until
    the next boundary state, the agent's events are non-memory" — as an
    opaque structural premise.  At [pxv6] it is a CONSEQUENCE of the
    sharper, per-edge premise

      [Hcq]:  the POST-STATE of a cross-edge source is [pquiet],

    because §2's step lemma then propagates quietness (and non-memory
    labels) forward until the next boundary. *)

Section trace.
  Context (next : bool → M unit).

  Lemma pquiet_upto (img : image) (log : list wmsg) (i : agent)
      (T : atrace pxv6) (k0 k' : nat) :
    atrace_wf (pstep_xv6 next) img log i T →
    (∀ k'' ag'', (k0 < k'')%nat → (k'' ≤ k')%nat →
       at_ags T !! k'' = Some ag'' → ¬ pbnd (pa_st ag'')) →
    (∀ ag, at_ags T !! S k0 = Some ag → pquiet (pa_st ag)) →
    ∀ m ag, (S k0 ≤ m)%nat → (m ≤ k')%nat →
      at_ags T !! m = Some ag → pquiet (pa_st ag).
  Proof.
    intros Hwf Hnb Hq0 m. induction m as [|m IH]; intros ag Hle1 Hle2 Hlk;
      [lia|].
    destruct (decide (k0 = m)) as [->|Hne]; [by apply Hq0|].
    have Hlem : (S k0 ≤ m)%nat by lia.
    have [ag0 Hag0] : is_Some (at_ags T !! m).
    { apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hlk. lia. }
    have Hqm : pquiet (pa_st ag0) by apply (IH ag0); [lia|lia|done].
    have Hnbm : ¬ pbnd (pa_st ag0) by apply (Hnb m ag0); [lia|lia|done].
    have [ev Hev] : is_Some (at_evs T !! m).
    { apply lookup_lt_is_Some_2. destruct Hwf as [Hlen _].
      apply lookup_lt_Some in Hlk. lia. }
    destruct (asteps_wf_step (pstep_xv6 next) img log i
                (at_ags T) (at_evs T) m ev Hwf Hev)
      as (a1 & a2 & st' & f & Ha1 & Ha2 & Hps & _ & Heq2).
    have Hx1 : a1 = ag0 by congruence. rewrite Hx1 in Hps.
    have Hage : pa_st ag = st'.
    { have Hx2 : ag = a2 by congruence. by rewrite Hx2 Heq2. }
    rewrite Hage.
    by destruct (pquiet_step next (pa_st ag0) (ae_lb ev) st' Hqm Hnbm Hps).
  Qed.

  (** THE DISCHARGE.  Note the shape: [Hcq] speaks about ONE record — the
      one immediately after the cross source — and everything else is
      §2's step lemma iterated. *)
  Lemma pcsl_of_pcq (TS : ptraces pxv6) :
    ptraces_wf (pstep_xv6 next) TS →
    (∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
       ∀ T ag', pt_trs TS !! e1.1 = Some T →
         at_ags T !! S e1.2 = Some ag' → pquiet (pa_st ag')) →
    ∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
    ∀ T, pt_trs TS !! e1.1 = Some T →
    ∀ k' ev', (e1.2 < k')%nat → at_evs T !! k' = Some ev' →
    (∀ k'' ag'', (e1.2 < k'')%nat → (k'' ≤ k')%nat →
       at_ags T !! k'' = Some ag'' → ¬ pbnd (pa_st ag'')) →
    lb_writes (ae_lb ev') = false ∧ lb_loads (ae_lb ev') = false.
  Proof.
    intros Hwf Hcq e1 e2 Hd Hne T HT k' ev' Hlt Hev Hnb.
    have Hatr := Hwf e1.1 T HT.
    destruct (asteps_wf_step (pstep_xv6 next) (pt_img TS) (pt_log TS) e1.1
                (at_ags T) (at_evs T) k' ev' Hatr Hev)
      as (ag & ag' & st' & f & Hag & _ & Hps & _ & _).
    have Hq0 : ∀ a0, at_ags T !! S e1.2 = Some a0 → pquiet (pa_st a0).
    { intros a0 Ha0. by eapply (Hcq e1 e2 Hd Hne T a0 HT). }
    have Hqk : pquiet (pa_st ag)
      := pquiet_upto (pt_img TS) (pt_log TS) e1.1 T e1.2 k' Hatr Hnb Hq0
           k' ag ltac:(lia) ltac:(lia) Hag.
    have Hnbk : ¬ pbnd (pa_st ag) by eapply (Hnb k' ag); [lia|lia|exact Hag].
    by destruct (pquiet_step next (pa_st ag) (ae_lb ev') st' Hqk Hnbk Hps).
  Qed.

  (** …and the trivial half: initial states are boundaries. *)
  Lemma pbnd0_of_ps (TS : ptraces pxv6) (ps : list pxv6) :
    (∀ j T ag0, pt_trs TS !! j = Some T →
       at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)) →
    (∀ i p, ps !! i = Some p → pbnd p) →
    ∀ i T ag0, pt_trs TS !! i = Some T →
      at_ags T !! 0%nat = Some ag0 → pbnd (pa_st ag0).
  Proof. intros Hps0 Hpsb i T ag0 HT H0. by eapply Hpsb, Hps0. Qed.

End trace.

(* ====================================================================== *)
(** ** 4. The [psail] ↔ [pxv6] transport of a SOLO run

    [WeakSailComplete]'s completions live on [wpcfg psail]; the cone's
    configurations are [wpcfg pxv6].  A completion moves ONE agent, reads
    the log and the image and writes the log and that agent's slot, so it
    transports across the species embedding with no invariant about the
    other agents at all: [hlink i c cs] pins the image, the log and agent
    [i]'s record, and nothing else.

    [prj_cfg] is the projection that BUILDS the [psail] side (every
    non-hart agent is given the running hart's own state as a filler — it
    is never stepped and never read), so the transport is used in the
    direction: project, complete, lift back. *)

(** The [pxv6] LTS with the interrupt-delivery arm removed from the harts
    — the relation a [WeakSailLTS2.sail_block] is built over. *)
Definition pstep_ni_xv6 (next : bool → M unit)
    (p : pxv6) (l : wlabel) (p' : pxv6) : Prop :=
  match p with
  | PHart q => match p' with PHart q' => sail_step_ni next q l q' | _ => False end
  | PDisk _ _ => pstep_xv6 next p l p'
  end.

Lemma pstep_ni_xv6_step next p l p' :
  pstep_ni_xv6 next p l p' → pstep_xv6 next p l p'.
Proof.
  destruct p as [q|d pend]; [|done].
  destruct p' as [q'|d' pend']; [|done]. apply sail_step_ni_step.
Qed.

(** The two faithfulness side conditions of [WeakSailLTS2.pf_solo], at
    [pxv6].  Both are the same formulas — [lbl_class] and [read_ok] do not
    mention the program type. *)
Definition xcls_canon (i : agent) (l : wlabel) (c c' : wpcfg pxv6) : Prop :=
  ∀ ag msg, pc_ags c !! i = Some ag → pc_log c' = pc_log c ++ [msg] →
    wm_ak msg = lbl_class l (pa_ws ag).

Definition xrmw_tight (i : agent) (l : wlabel) (c : wpcfg pxv6) : Prop :=
  match l with
  | WeakPromise.LRmw aq _ base tvs _ =>
      ∀ ag, pc_ags c !! i = Some ag →
        read_ok (pc_img c) (pc_log c) (pa_ws ag) aq true base tvs
  | _ => True
  end.

Definition pf_xsolo (next : bool → M unit) (i : agent)
    (c c' : wpcfg pxv6) : Prop :=
  ∃ l : wlabel,
    wp_pf_step (pstep_ni_xv6 next) i l c c' ∧
    xcls_canon i l c c' ∧ xrmw_tight i l c.

Definition pf_xquiet (next : bool → M unit) (i : agent)
    (c c' : wpcfg pxv6) : Prop :=
  ∃ l : wlabel, lbl_quiet l ∧ wp_pf_step (pstep_ni_xv6 next) i l c c'.

Lemma xcls_canon_nolog i l (c c' : wpcfg pxv6) :
  pc_log c' = pc_log c → xcls_canon i l c c'.
Proof.
  intros Hlog ag msg _ Heq. rewrite Hlog in Heq.
  by destruct (app_snoc_absurd _ _ Heq).
Qed.

Lemma pf_xquiet_nolog next i l (c c' : wpcfg pxv6) :
  lbl_quiet l → wp_pf_step (pstep_ni_xv6 next) i l c c' →
  pc_log c' = pc_log c.
Proof.
  intros Hq Hstep. destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kk st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps]; try done;
    by destruct Hq as [Hx|(?&?&?&?&Hx)]; inversion Hx.
Qed.

Lemma pf_xquiet_xsolo next i c c' :
  pf_xquiet next i c c' → pf_xsolo next i c c'.
Proof.
  intros (l & Hq & Hstep). exists l. split_and!; [exact Hstep| |].
  - apply xcls_canon_nolog. exact (pf_xquiet_nolog next i l c c' Hq Hstep).
  - destruct Hq as [->|(?&?&?&?&->)]; exact I.
Qed.

Lemma pf_xsolo_run next i c c' :
  pf_xsolo next i c c' → wp_pf_run (pstep_xv6 next) c c'.
Proof.
  intros (l & Hstep & _ & _). exists i, l.
  destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kk st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps];
    [ by eapply PFSilent, pstep_ni_xv6_step
    | by eapply PFLoad; [done|apply pstep_ni_xv6_step|done]
    | by eapply PFStore; [done|apply pstep_ni_xv6_step|done]
    | by eapply PFRmw; [done|apply pstep_ni_xv6_step|done|done|done|done]
    | by eapply PFFence; [done|apply pstep_ni_xv6_step] ].
Qed.

Lemma pf_xsolo_rtc_run next i c c' :
  rtc (pf_xsolo next i) c c' → rtc (wp_pf_run (pstep_xv6 next)) c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [exact (pf_xsolo_run next i x y Hxy)|exact IH].
Qed.

Section lift.
  Context (next : bool → M unit).

  (** The link: image, log and agent [i]'s record.  Nothing about the
      other agents — the completions never touch them. *)
  Definition hlink (i : agent) (c : wpcfg pxv6) (cs : wpcfg psail) : Prop :=
    pc_img c = pc_img cs ∧ pc_log c = pc_log cs ∧
    ∃ agx ags, pc_ags c !! i = Some agx ∧ pc_ags cs !! i = Some ags ∧
      pa_st agx = PHart (pa_st ags) ∧ pa_ws agx = pa_ws ags ∧
      pa_prom agx = pa_prom ags.

  Lemma pf_step_lift (i : agent) (l : wlabel) (c : wpcfg pxv6)
      (cs cs' : wpcfg psail) :
    wp_pf_step (sail_step_ni next) i l cs cs' →
    cls_canon i l cs cs' → rmw_tight i l cs → hlink i c cs →
    ∃ c', wp_pf_step (pstep_ni_xv6 next) i l c c' ∧
          xcls_canon i l c c' ∧ xrmw_tight i l c ∧ hlink i c' cs' ∧
          (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
  Proof.
    intros Hstep Hcls Hrmw (Himg & Hlog & agx & ags & Hax & Has & Hst & Hws & Hpr).
    destruct Hstep as
      [cfg ag st' Hlk Hps
      |cfg ag aq lat base tvs st' Hlk Hps Hr
      |cfg ag rl base data kk st' Hlk Hps Hne
      |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
      |cfg ag pr pw sr sw st' Hlk Hps];
      simpl in Has, Himg, Hlog; rewrite Hlk in Has; injection Has as <-.
    - (* silent *)
      exists (WPCfg (pc_img c) (pc_log c)
               (<[i := WPAgent (PHart st') (pa_ws agx) (pa_prom agx)]>
                  (pc_ags c))).
      split_and!.
      + apply (PFSilent (pstep_ni_xv6 next) i c agx (PHart st') Hax).
        rewrite Hst /=. exact Hps.
      + by apply xcls_canon_nolog.
      + exact I.
      + split_and!; [exact Himg|exact Hlog|].
        eexists _, _. split_and!;
          [exact (lookup_insert_self _ _ _ _ Hax)
          |exact (lookup_insert_self _ _ _ _ Hlk)|done|exact Hws|exact Hpr].
      + intros j Hj. simpl. by apply lookup_insert_other.
    - (* load *)
      have Hr' : read_ok (pc_img c) (pc_log c) (pa_ws agx) aq lat base tvs
        by rewrite Himg Hlog Hws.
      exists (WPCfg (pc_img c) (pc_log c)
               (<[i := WPAgent (PHart st')
                         (load_post_run (pa_ws agx) aq base tvs.*1)
                         (pa_prom agx)]> (pc_ags c))).
      split_and!.
      + apply (PFLoad (pstep_ni_xv6 next) i c agx aq lat base tvs (PHart st')
                 Hax); [rewrite Hst /=; exact Hps|exact Hr'].
      + by apply xcls_canon_nolog.
      + exact I.
      + split_and!; [exact Himg|exact Hlog|].
        eexists _, _. split_and!;
          [exact (lookup_insert_self _ _ _ _ Hax)
          |exact (lookup_insert_self _ _ _ _ Hlk)|done|by rewrite /= Hws|exact Hpr].
      + intros j Hj. simpl. by apply lookup_insert_other.
    - (* store *)
      have Hkk : kk = lbl_class (WeakPromise.LStore rl base data) (pa_ws ag)
        by exact (Hcls ag (WMsg base data (Some i) kk) Hlk eq_refl).
      exists (WPCfg (pc_img c) (pc_log c ++ [WMsg base data (Some i) kk])
               (<[i := WPAgent (PHart st')
                         (store_post_run (pa_ws agx) rl base (length data)
                            (S (length (pc_log c)))) (pa_prom agx)]>
                  (pc_ags c))).
      split_and!.
      + apply (PFStore (pstep_ni_xv6 next) i c agx rl base data kk
                 (PHart st') Hax); [rewrite Hst /=; exact Hps|exact Hne].
      + intros ag2 msg Hag2 Heq. simpl in Heq.
        apply app_inv_head in Heq. injection Heq as <-.
        rewrite Hax in Hag2. injection Hag2 as <-. by rewrite Hws.
      + exact I.
      + split_and!; [exact Himg|by rewrite /= Hlog|].
        eexists _, _. split_and!;
          [exact (lookup_insert_self _ _ _ _ Hax)
          |exact (lookup_insert_self _ _ _ _ Hlk)|done
          |by rewrite /= Hws Hlog|exact Hpr].
      + intros j Hj. simpl. by apply lookup_insert_other.
    - (* rmw *)
      have Hkk : kk = lbl_class (WeakPromise.LRmw aq rl base tvs data)
                        (pa_ws ag)
        by exact (Hcls ag (WMsg base data (Some i) kk) Hlk eq_refl).
      have Hr' : read_ok (pc_img c) (pc_log c) (pa_ws agx) aq false base tvs
        by rewrite Himg Hlog Hws.
      have He' : excl_ok (pc_log c) i base tvs (S (length (pc_log c)))
        by rewrite Hlog.
      exists (WPCfg (pc_img c) (pc_log c ++ [WMsg base data (Some i) kk])
               (<[i := WPAgent (PHart st')
                         (store_post_run
                            (load_post_run (pa_ws agx) aq base tvs.*1)
                            rl base (length data) (S (length (pc_log c))))
                         (pa_prom agx)]> (pc_ags c))).
      split_and!.
      + apply (PFRmw (pstep_ni_xv6 next) i c agx aq rl base tvs data kk
                 (PHart st') Hax);
          [rewrite Hst /=; exact Hps|exact Hne|exact Hlen|exact Hr'|exact He'].
      + intros ag2 msg Hag2 Heq. simpl in Heq.
        apply app_inv_head in Heq. injection Heq as <-.
        rewrite Hax in Hag2. injection Hag2 as <-. by rewrite Hws.
      + intros ag2 Hag2. rewrite Hax in Hag2. injection Hag2 as <-.
        rewrite Himg Hlog Hws. exact (Hrmw ag Hlk).
      + split_and!; [exact Himg|by rewrite /= Hlog|].
        eexists _, _. split_and!;
          [exact (lookup_insert_self _ _ _ _ Hax)
          |exact (lookup_insert_self _ _ _ _ Hlk)|done
          |by rewrite /= Hws Hlog|exact Hpr].
      + intros j Hj. simpl. by apply lookup_insert_other.
    - (* fence *)
      exists (WPCfg (pc_img c) (pc_log c)
               (<[i := WPAgent (PHart st')
                         (fence_post (pa_ws agx) pr pw sr sw)
                         (pa_prom agx)]> (pc_ags c))).
      split_and!.
      + apply (PFFence (pstep_ni_xv6 next) i c agx pr pw sr sw (PHart st')
                 Hax). rewrite Hst /=. exact Hps.
      + by apply xcls_canon_nolog.
      + exact I.
      + split_and!; [exact Himg|exact Hlog|].
        eexists _, _. split_and!;
          [exact (lookup_insert_self _ _ _ _ Hax)
          |exact (lookup_insert_self _ _ _ _ Hlk)|done|by rewrite /= Hws|exact Hpr].
      + intros j Hj. simpl. by apply lookup_insert_other.
  Qed.

End lift.

Section lift2.
  Context (next : bool → M unit).

  Lemma pf_solo_lift (i : agent) (c : wpcfg pxv6) (cs cs' : wpcfg psail) :
    pf_solo next i cs cs' → hlink i c cs →
    ∃ c', pf_xsolo next i c c' ∧ hlink i c' cs' ∧
          (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
  Proof.
    intros (l & Hstep & Hcls & Hrmw) Hl.
    destruct (pf_step_lift next i l c cs cs' Hstep Hcls Hrmw Hl)
      as (c' & Hs & Hc & Hr & Hl' & Hfr).
    exists c'. split_and!; [by exists l|exact Hl'|exact Hfr].
  Qed.

  Lemma pf_solo_q_lift (i : agent) (c : wpcfg pxv6) (cs cs' : wpcfg psail) :
    pf_solo_q next i cs cs' → hlink i c cs →
    ∃ c', pf_xquiet next i c c' ∧ hlink i c' cs' ∧
          (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
  Proof.
    intros Hq Hl. have Hq2 := Hq. destruct Hq2 as (l & Hql & Hstep).
    destruct (pf_step_lift next i l c cs cs' Hstep
                (cls_canon_nolog i l cs cs'
                   (pf_quiet_nolog next i l cs cs' Hql Hstep))
                ltac:(destruct Hql as [->|(?&?&?&?&->)]; exact I) Hl)
      as (c' & Hs & _ & _ & Hl' & Hfr).
    exists c'. split_and!; [by exists l|exact Hl'|exact Hfr].
  Qed.

  Lemma pf_solo_run_lift (i : agent) (c : wpcfg pxv6) (cs cs' : wpcfg psail) :
    rtc (pf_solo next i) cs cs' → hlink i c cs →
    ∃ c', rtc (pf_xsolo next i) c c' ∧ hlink i c' cs' ∧
          (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
  Proof.
    intros Hrun. revert c. induction Hrun as [x|x y z Hxy _ IH]; intros c Hl.
    { exists c. split_and!; [apply rtc_refl|exact Hl|done]. }
    destruct (pf_solo_lift i c x y Hxy Hl) as (c1 & Hs1 & Hl1 & Hfr1).
    destruct (IH c1 Hl1) as (c2 & Hs2 & Hl2 & Hfr2).
    exists c2. split_and!; [by eapply rtc_l|exact Hl2|].
    intros j Hj. by rewrite (Hfr2 j Hj) (Hfr1 j Hj).
  Qed.

  Lemma pf_solo_q_run_lift (i : agent) (c : wpcfg pxv6) (cs cs' : wpcfg psail) :
    rtc (pf_solo_q next i) cs cs' → hlink i c cs →
    ∃ c', rtc (pf_xquiet next i) c c' ∧ hlink i c' cs' ∧
          (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
  Proof.
    intros Hrun. revert c. induction Hrun as [x|x y z Hxy _ IH]; intros c Hl.
    { exists c. split_and!; [apply rtc_refl|exact Hl|done]. }
    destruct (pf_solo_q_lift i c x y Hxy Hl) as (c1 & Hs1 & Hl1 & Hfr1).
    destruct (IH c1 Hl1) as (c2 & Hs2 & Hl2 & Hfr2).
    exists c2. split_and!; [by eapply rtc_l|exact Hl2|].
    intros j Hj. by rewrite (Hfr2 j Hj) (Hfr1 j Hj).
  Qed.

End lift2.

(** THE PROJECTION.  Every non-hart agent is filled in with the running
    hart's own [psail] state; it is never stepped and never read, so any
    filler would do. *)
Definition prj_ag (q : psail) (ag : wpagent pxv6) : wpagent psail :=
  WPAgent (match pa_st ag with PHart r => r | PDisk _ _ => q end)
          (pa_ws ag) (pa_prom ag).

Definition prj_cfg (q : psail) (c : wpcfg pxv6) : wpcfg psail :=
  WPCfg (pc_img c) (pc_log c) (prj_ag q <$> pc_ags c).

Lemma prj_hlink (q : psail) (i : agent) (c : wpcfg pxv6) ag :
  pc_ags c !! i = Some ag → pa_st ag = PHart q → hlink i c (prj_cfg q c).
Proof.
  intros Hlk Hst. split_and!; [done|done|].
  exists ag, (prj_ag q ag). split_and!;
    [exact Hlk|by rewrite /= list_lookup_fmap Hlk|by rewrite /prj_ag /= Hst
    |done|done].
Qed.

Lemma prj_cfg_bnd q c : cfg_bnd c → cfg_bnd (prj_cfg q c).
Proof.
  intros Hb j ag. rewrite /prj_cfg /= list_lookup_fmap.
  destruct (pc_ags c !! j) as [ag0|] eqn:H0; simpl; [|done].
  intros [= <-]. rewrite /prj_ag /=. by eapply Hb.
Qed.

(* ====================================================================== *)
(** ** 5. The completions, at [pxv6]

    [WeakSailComplete]'s two completions, transported by §4.  The frame
    facts are NOT transported — they are re-derived directly from the
    [pxv6] run by [WeakRobustBlocks]' generic step lemmas ([xtframe]),
    which is both shorter and sharper. *)

Definition xtframe (i : agent) (c c' : wpcfg pxv6) : Prop :=
  (∃ ms, pc_log c' = pc_log c ++ ms ∧
         Forall (λ mq, wm_tid mq = Some i) ms) ∧
  pc_img c' = pc_img c ∧
  (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j) ∧
  (∀ j a, (obs_flr c j a ≤ obs_flr c' j a)%nat).

Lemma xtframe_refl i c : xtframe i c c.
Proof.
  split_and!; [|done|done|by intros j a].
  exists []. rewrite app_nil_r. split; [done|constructor].
Qed.

Lemma xtframe_trans i c1 c2 c3 :
  xtframe i c1 c2 → xtframe i c2 c3 → xtframe i c1 c3.
Proof.
  intros ((ms1 & Hl1 & Hf1) & Hi1 & Hg1 & Ho1)
         ((ms2 & Hl2 & Hf2) & Hi2 & Hg2 & Ho2).
  split_and!.
  - exists (ms1 ++ ms2). split; [by rewrite Hl2 Hl1 app_assoc|].
    by apply Forall_app.
  - by rewrite Hi2.
  - intros j Hj. by rewrite (Hg2 j Hj) (Hg1 j Hj).
  - intros j a. etrans; [by apply Ho1|by apply Ho2].
Qed.

Lemma pf_xsolo_xtframe next i c c' : pf_xsolo next i c c' → xtframe i c c'.
Proof.
  intros (l & Hstep & _ & _).
  destruct (wp_pf_step_shape (pstep_ni_xv6 next) i l c c' Hstep)
    as (Himg & _ & (ms & Hlog & Hall)).
  split_and!; [by exists ms|done| |].
  - intros j Hj.
    exact (wp_pf_step_frame (pstep_ni_xv6 next) i l c c' j Hstep Hj).
  - intros j a.
    exact (wp_pf_step_obs_flr (pstep_ni_xv6 next) i l c c' j a Hstep).
Qed.

Lemma pf_xsolo_run_xtframe next i c c' :
  rtc (pf_xsolo next i) c c' → xtframe i c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply xtframe_refl|].
  apply (xtframe_trans i x y z); [|exact IH].
  exact (pf_xsolo_xtframe next i x y Hxy).
Qed.

Lemma pf_xsolo_run_bnd next i c c' :
  rtc (pf_xsolo next i) c c' → cfg_bnd c → cfg_bnd c'.
Proof.
  induction 1 as [|x y z (l & Hxy & _ & _) _ IH]; [by intros Hb|].
  intros Hb. apply IH.
  exact (wp_pf_step_bnd (pstep_ni_xv6 next) i l x y Hxy Hb).
Qed.

Lemma pf_xquiet_run_solo next i c c' :
  rtc (pf_xquiet next i) c c' → rtc (pf_xsolo next i) c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [exact (pf_xquiet_xsolo next i x y Hxy)|exact IH].
Qed.

Section xcomplete.
  Context (next : bool → M unit).

  (** THE SILENT-EPILOGUE COMPLETION at [pxv6]: appends nothing, moves no
      coherence floor, so no violation is created or destroyed. *)
  Theorem xquiet_complete (i : agent) (c : wpcfg pxv6) ag q :
    pc_ags c !! i = Some ag → pa_st ag = PHart q → psail_quiet q →
    ∃ c' ag' q',
      rtc (pf_xquiet next i) c c' ∧
      pc_ags c' !! i = Some ag' ∧ pa_st ag' = PHart q' ∧
      sp_m q' = None ∧ sp_fence q' = None ∧
      pc_log c' = pc_log c ∧ pc_img c' = pc_img c ∧
      (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
  Proof.
    intros Hlk Hst Hqt.
    have Hl : hlink i c (prj_cfg q c) := prj_hlink q i c ag Hlk Hst.
    have Hlks : pc_ags (prj_cfg q c) !! i = Some (prj_ag q ag)
      by rewrite /= list_lookup_fmap Hlk.
    destruct (quiet_complete_q next i (prj_cfg q c) (prj_ag q ag) Hlks
                ltac:(by rewrite /prj_ag /= Hst))
      as (cs' & ags' & Hrun & (Hql & Hqi & Hqf & Hqa) & Hlk2 & _ & Hm2 & Hf2).
    destruct (pf_solo_q_run_lift next i c (prj_cfg q c) cs' Hrun Hl)
      as (c' & Hxrun & (Himg' & Hlog' & agx & ags & Hax & Has & Hpst & Hpws & Hppr)
          & Hfr).
    have Hags : ags = ags' by congruence. subst ags.
    exists c', agx, (pa_st ags'). split_and!;
      [exact Hxrun|exact Hax|exact Hpst|exact Hm2|exact Hf2| | |exact Hfr].
    - by rewrite Hlog' Hql.
    - by rewrite Himg' Hqi.
  Qed.

  (** THE READER-TAIL COMPLETION at [pxv6]. *)
  Theorem xtail_complete (i : agent) (c : wpcfg pxv6) ag q (m : M unit) :
    img_total (pc_img c) → cfg_bnd c →
    pc_ags c !! i = Some ag → pa_st ag = PHart q → sp_m q = Some m →
    sail_shaped m → sail_live m →
    (∃ dv, oracle_consistent dv m (sp_dev q)) →
    ∃ c' ag' q',
      rtc (pf_xsolo next i) c c' ∧
      pc_ags c' !! i = Some ag' ∧ pa_st ag' = PHart q' ∧
      sp_m q' = None ∧ sp_fence q' = None ∧
      xtframe i c c' ∧ cfg_bnd c'.
  Proof.
    intros Him Hbnd Hlk Hst Hm Hsh Hlv Hoc.
    have Hl : hlink i c (prj_cfg q c) := prj_hlink q i c ag Hlk Hst.
    have Hlks : pc_ags (prj_cfg q c) !! i = Some (prj_ag q ag)
      by rewrite /= list_lookup_fmap Hlk.
    destruct (tail_complete next i (prj_cfg q c) (prj_ag q ag) m Him
                (prj_cfg_bnd q c Hbnd) Hlks
                ltac:(by rewrite /prj_ag /= Hst)
                Hsh Hlv ltac:(by rewrite /prj_ag /= Hst))
      as (cs' & ags' & ms & Hrun & Hlk2 & (agb & Hagb & Hmb) & Hf2 & _).
    destruct (pf_solo_run_lift next i c (prj_cfg q c) cs' Hrun Hl)
      as (c' & Hxrun & (Himg' & Hlog' & agx & ags & Hax & Has & Hpst & Hpws & Hppr)
          & Hfr).
    have Hags : ags = ags' by congruence. subst ags.
    have Hagb' : agb = ags' by congruence. subst agb.
    exists c', agx, (pa_st ags'). split_and!;
      [exact Hxrun|exact Hax|exact Hpst|exact Hmb|exact Hf2
      |exact (pf_xsolo_run_xtframe next i c c' Hxrun)
      |exact (pf_xsolo_run_bnd next i c c' Hxrun Hbnd)].
  Qed.

End xcomplete.

(* ====================================================================== *)
(** ** 6. Counting an agent's processed events

    [WeakRobustSim.qcfg] reads agent [j]'s cut record off the trace at
    index [nproc done j].  The packaged cone theorem exports the ORDER's
    membership and duplicate-freedom but not [qorder]'s counting conjunct,
    so it is re-derived here: an agent's slice of a duplicate-free,
    DOWNWARD-CLOSED order is exactly its first [nproc] events. *)

(** The FIRST STEP of a [tc] chain, with the rest kept.  ([WeakRobustCone]'s
    [tc_first] drops the tail, which is exactly what the cut argument
    needs back.) *)
Lemma tc_first_step {A} (R : relation A) (x z : A) :
  tc R x z → ∃ y, R x y ∧ (y = z ∨ tc R y z).
Proof.
  destruct 1 as [x' y' HR|x' y' z' HR Ht];
    [exists y'; split; [done|by left]|exists y'; split; [done|by right]].
Qed.

Lemma nproc_mem (order : list gev) (j : nat) :
  NoDup order →
  (∀ k k', (k' < k)%nat → (j, k) ∈ order → (j, k') ∈ order) →
  ∀ k, ((j, k) ∈ order ↔ (k < nproc order j)%nat).
Proof.
  intros Hnd Hdc.
  set F := filter (λ e : gev, e.1 = j) order.
  have HFnd : NoDup F by apply list_relations.NoDup_filter.
  have HnpF : nproc order j = length F by done.
  have HFmem : ∀ x, x ∈ F ↔ (x ∈ order ∧ x.1 = j).
  { intros x. rewrite /F elem_of_list_filter. naive_solver. }
  set G := λ n : nat, (λ k : nat, (j, k)) <$> seq 0 n.
  have HGnd : ∀ n, NoDup (G n).
  { intros n. rewrite /G. apply list_monad.NoDup_fmap_2; [|apply list_numbers.NoDup_seq].
    intros a b [= ->]. done. }
  have HGmem : ∀ n x, x ∈ G n ↔ (∃ k, (k < n)%nat ∧ x = (j, k)).
  { intros n x. rewrite /G elem_of_list_fmap. split.
    - intros (k & -> & Hk). exists k. split; [|done].
      apply elem_of_seq in Hk. lia.
    - intros (k & Hk & ->). exists k. split; [done|].
      apply elem_of_seq. lia. }
  have HGlen : ∀ n, length (G n) = n
    by intros n; rewrite /G length_fmap length_seq.
  have Hlow : ∀ n, (∀ k, (k < n)%nat → (j, k) ∈ order) → (n ≤ length F)%nat.
  { intros n Hn.
    have Hsub : G n ⊆+ F.
    { apply list_relations.NoDup_submseteq; [apply HGnd|]. intros x Hx.
      apply HGmem in Hx as (k & Hk & ->). apply HFmem.
      split; [by apply Hn|done]. }
    have Hln := list_relations.submseteq_length _ _ Hsub.
    rewrite HGlen in Hln. exact Hln. }
  have Hhigh : ∀ n, (∀ k, (j, k) ∈ order → (k < n)%nat) → (length F ≤ n)%nat.
  { intros n Hn.
    have Hsub : F ⊆+ G n.
    { apply list_relations.NoDup_submseteq; [apply HFnd|]. intros x Hx.
      apply HFmem in Hx as (Hx1 & Hx2). apply HGmem. exists x.2.
      destruct x as [a b]. simpl in Hx2. subst a. split; [by apply Hn|done]. }
    have Hln := list_relations.submseteq_length _ _ Hsub.
    rewrite HGlen in Hln. exact Hln. }
  intros k. rewrite HnpF. split.
  - intros Hin. have Hle : (S k ≤ length F)%nat.
    { apply Hlow. intros k' Hk'.
      destruct (decide (k' = k)) as [->|Hne]; [done|].
      apply (Hdc k k'); [lia|done]. }
    lia.
  - intros Hlt. destruct (decide ((j,k) ∈ order)) as [?|Hnin]; [done|exfalso].
    have Hb : (length F ≤ k)%nat.
    { apply Hhigh. intros k0 Hk0.
      destruct (decide (k0 < k)%nat) as [?|Hge]; [done|exfalso].
      apply Hnin. destruct (decide (k0 = k)) as [->|Hne]; [done|].
      apply (Hdc k0 k); [lia|done]. }
    lia.
Qed.

(* ====================================================================== *)
(** ** 7. The cone at [pxv6]: premises, cut classification, completion

    The section context mirrors [WeakRobustCone]'s §8 (minus the two
    Layer-1 side conditions, which are THEOREMS for [pstep_xv6]) and adds
    the four premises this stage owns:

      [Hps_bnd]  the initial agent states are at instruction boundaries;
      [Hcq]      the post-state of a cross-edge source is [pquiet];
      [Hres]     every trace record's residual is shaped, live and
                 oracle-consistent (the reader-tail completion's fuel);
      [Himgt]    [img_total] (the boot image covers every RAM byte). *)

Section cone.
  Context (TS : ptraces pxv6) (img : image) (ps : list pxv6).
  Context (Hwf : ptraces_wf (pstep_xv6 riscv_step) TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, WeakRobustSer.co_tc TS a).
  Context (Hwfl : WeakRobustSer.writes_fulfilled TS).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  Context (Hfo : WeakRobustAcyc.ptraces_fwd_own TS).
  Context (Hee : WeakRobustAcyc2.ee_ok TS).
  Context (nh : nat).
  Context (Hsplit : edges_split nh TS).

  (** (B4-1) initial states are boundaries *)
  Context (Hps_bnd : ∀ i p, ps !! i = Some p → pbnd p).
  (** (B4-2) the post-state of a cross-edge source is quiet *)
  Context (Hcq : ∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
                   ∀ T ag', pt_trs TS !! e1.1 = Some T →
                     at_ags T !! S e1.2 = Some ag' → pquiet (pa_st ag')).
  (** (B4-3) every trace record's residual is completable *)
  Context (Hres : ∀ i T k ag q,
             pt_trs TS !! i = Some T → at_ags T !! k = Some ag →
             pa_st ag = PHart q →
             match sp_m q with
             | None => True
             | Some m => sail_shaped m ∧ sail_live m ∧
                         ∃ d, oracle_consistent d m (sp_dev q)
             end).
  (** (B4-4) the image is total *)
  Context (Himgt : img_total img).

  (** The two boundary premises [WeakRobustCone] asks for. *)
  Lemma pbnd0 : ∀ i T ag0, pt_trs TS !! i = Some T →
    at_ags T !! 0%nat = Some ag0 → pbnd (pa_st ag0).
  Proof. exact (pbnd0_of_ps TS ps Hps0 Hps_bnd). Qed.

  Lemma pcsl : ∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
    ∀ T, pt_trs TS !! e1.1 = Some T →
    ∀ k' ev', (e1.2 < k')%nat → at_evs T !! k' = Some ev' →
    (∀ k'' ag'', (e1.2 < k'')%nat → (k'' ≤ k')%nat →
       at_ags T !! k'' = Some ag'' → ¬ pbnd (pa_st ag'')) →
    lb_writes (ae_lb ev') = false ∧ lb_loads (ae_lb ev') = false.
  Proof. exact (pcsl_of_pcq riscv_step TS Hwf Hcq). Qed.

  (** An agent's slice of the order is DOWNWARD CLOSED: a program-order
      predecessor of a cone event is a cone event. *)
  Lemma order_dc (order : list gev) (b2 : gev) :
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2))) →
    ∀ j k k', (k' < k)%nat → (j, k) ∈ order → (j, k') ∈ order.
  Proof.
    intros Hmem j k k' Hlt Hin.
    apply Hmem in Hin as (Hwfk & Hor).
    have Hwfk' : gev_wf TS (j, k').
    { apply gev_wf_bounds. apply gev_wf_bounds in Hwfk as (T & HT & Hb).
      exists T. simpl in HT, Hb |- *. split; [done|lia]. }
    have Hd : gdep2 TS (j, k') (j, k)
      by apply gpo_gdep2; split_and!; [done|simpl;lia|done|done].
    apply Hmem. split; [done|right].
    destruct Hor as [<-|Htc]; [by apply tc_once|by eapply tc_l].
  Qed.

  (** THE CUT CLASSIFICATION.  Every agent but the reader is left QUIET by
      the block-contiguous replay: either it has no cone event at all (and
      sits at its initial, boundary state), or its LAST cone event is a
      CROSS SOURCE — because the first [gdep2] step out of it cannot stay
      inside the agent (that would name a LATER cone event of the same
      agent) — and [Hcq] applies to the record right after it. *)
  Lemma cut_pquiet (order : list gev) (b2 : gev) (cf : wpcfg pxv6) j ag :
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2))) →
    NoDup order →
    qcfg (pstep_xv6 riscv_step) TS img ps order cf →
    j ≠ b2.1 → pc_ags cf !! j = Some ag → pquiet (pa_st ag).
  Proof.
    intros Hmem Hnd (_ & _ & _ & Hlen & Hcags) Hne Hlk.
    have Hjlt : (j < length ps)%nat
      by (apply lookup_lt_Some in Hlk; lia).
    have [T HT] : is_Some (pt_trs TS !! j)
      by (apply lookup_lt_is_Some_2; lia).
    destruct (Hcags j T HT) as (agn & Hagn & Hlk2).
    rewrite Hlk in Hlk2. injection Hlk2 as Hlk2.
    have Hst : pa_st ag = pa_st agn by rewrite Hlk2.
    rewrite Hst. clear Hst Hlk2 Hlk.
    have Hmemj := nproc_mem order j Hnd (order_dc order b2 Hmem j).
    destruct (nproc order j) as [|n'] eqn:Hnp.
    { by apply pbnd_pquiet, (pbnd0 j T agn HT). }
    have Hin : (j, n') ∈ order by apply Hmemj; lia.
    have Hlast : ∀ k, (j, k) ∈ order → (k ≤ n')%nat.
    { intros k Hk. apply Hmemj in Hk. lia. }
    apply Hmem in Hin as (Hwfe & Hor).
    have Hnb2 : (j, n') ≠ b2 by intros Hx; apply Hne; rewrite -Hx.
    have Htc : tc (gdep2 TS) (j, n') b2
      by destruct Hor as [Heq|Ht]; [by destruct (Hnb2 Heq)|exact Ht].
    have Hcross : ∃ y, gdep2 TS (j, n') y ∧ j ≠ y.1.
    { destruct (tc_first_step (gdep2 TS) (j, n') b2 Htc) as (y & Hd & Hy).
      destruct (decide (j = y.1)) as [Hag|Hag]; [|by exists y].
      exfalso.
      have Hlt := gdep2_sa_lt (pstep_xv6 riscv_step) TS ps Hwf Hnag Hee
                    (j, n') y Hd Hag.
      simpl in Hlt.
      have Hwfy : gev_wf TS y by destruct (gdep2_wf TS (j,n') y Hd).
      have Hyin : y ∈ order.
      { apply Hmem. split; [exact Hwfy|].
        destruct Hy as [Heq|Ht]; [by left|by right]. }
      have Hy2 : y = (j, y.2) by destruct y; simpl in Hag |- *; by subst.
      have Hyin2 : (j, y.2) ∈ order by rewrite -Hy2.
      have := Hlast y.2 Hyin2. lia. }
    destruct Hcross as (y & Hd & Hag).
    apply (Hcq (j, n') y Hd Hag T agn HT).
    simpl. exact Hagn.
  Qed.

End cone.

(* ====================================================================== *)
(** ** 8. Segments, and the epilogue pass over the non-reader agents

    A SEGMENT is a contiguous SOLO run of ONE agent over the irq-free LTS
    ([pf_xsolo], i.e. [WeakSailLTS2.pf_solo] transported to [pxv6]) that
    ENDS at an instruction boundary.  [chained] threads them.

    DEVIATION FROM THE B4 SKETCH, recorded precisely.  [seg_ok] does NOT
    require the segment to START at a boundary, and the segments are NOT
    spliced back to their agents' last chain step: the epilogues produced
    here sit at the END of the run, in the order the agents are completed.
    [WeakSailComplete.pf_run_insert_local] is exactly the surgery that
    would move them ([pf_xquiet] runs are [pf_quiet_run]s of the same
    agent), and nothing below depends on their position — but the
    bookkeeping that turns the chain plus the moved epilogues into
    boundary-to-boundary blocks is NOT done here.  See the report. *)

Definition seg : Type := (nat * wpcfg pxv6 * wpcfg pxv6)%type.

Definition seg_ok (next : bool → M unit) (s : seg) : Prop :=
  rtc (pf_xsolo next s.1.1) s.1.2 s.2 ∧
  (∀ ag, pc_ags s.2 !! s.1.1 = Some ag → pbnd (pa_st ag)).

Fixpoint chained (segs : list seg) (c cf : wpcfg pxv6) : Prop :=
  match segs with
  | [] => c = cf
  | s :: rest => s.1.2 = c ∧ chained rest s.2 cf
  end.

Lemma chained_run (next : bool → M unit) segs c cf :
  chained segs c cf → Forall (seg_ok next) segs →
  rtc (wp_pf_run (pstep_xv6 next)) c cf.
Proof.
  revert c. induction segs as [|s segs IH]; intros c Hch Hall; simpl in Hch.
  { by rewrite Hch. }
  destruct Hch as (Hs & Hch).
  apply list_relations.Forall_cons in Hall as [(Hrun & _) Hall].
  rewrite -Hs. etrans; [exact (pf_xsolo_rtc_run next s.1.1 _ _ Hrun)|].
  by apply IH.
Qed.

Lemma chained_app segs1 segs2 c c1 cf :
  chained segs1 c c1 → chained segs2 c1 cf → chained (segs1 ++ segs2) c cf.
Proof.
  revert c. induction segs1 as [|s segs IH]; intros c H1 H2; simpl in H1 |- *.
  - by rewrite H1.
  - destruct H1 as (Hs & H1). split; [exact Hs|by apply IH].
Qed.

Section epilogues.
  Context (next : bool → M unit).

  (** Complete every agent of [ks] whose cut state is QUIET.  The disk's
      quiet state IS its boundary state, so only harts move; the log does
      not move at all. *)
  Lemma complete_agents_quiet (ks : list nat) (c : wpcfg pxv6) :
    NoDup ks →
    (∀ k ag, k ∈ ks → pc_ags c !! k = Some ag → pquiet (pa_st ag)) →
    ∃ c' segs,
      chained segs c c' ∧ Forall (seg_ok next) segs ∧
      (∀ k ag, k ∈ ks → pc_ags c' !! k = Some ag → pbnd (pa_st ag)) ∧
      (∀ k, k ∉ ks → pc_ags c' !! k = pc_ags c !! k) ∧
      pc_log c' = pc_log c ∧ pc_img c' = pc_img c ∧
      (∀ j a, (obs_flr c j a ≤ obs_flr c' j a)%nat).
  Proof.
    revert c. induction ks as [|k ks IH]; intros c Hnd Hq.
    { exists c, []. split_and!; [done|constructor| |done|done|done|by intros].
      intros k ag Hk. by apply elem_of_nil in Hk. }
    apply list_relations.NoDup_cons in Hnd as [Hnk Hnd].
    (* the agent [k]'s own epilogue *)
    have Hstep : ∃ c1 segs1,
        chained segs1 c c1 ∧ Forall (seg_ok next) segs1 ∧
        (∀ ag, pc_ags c1 !! k = Some ag → pbnd (pa_st ag)) ∧
        (∀ k', k' ≠ k → pc_ags c1 !! k' = pc_ags c !! k') ∧
        pc_log c1 = pc_log c ∧ pc_img c1 = pc_img c ∧
        (∀ j a, (obs_flr c j a ≤ obs_flr c1 j a)%nat).
    { destruct (pc_ags c !! k) as [ag|] eqn:Hag; last first.
      { exists c, []. split_and!; [done|constructor| |done|done|done|by intros].
        intros ag Hx. by rewrite Hag in Hx. }
      have Hqk : pquiet (pa_st ag) by apply (Hq k ag); [set_solver|done].
      destruct (pa_st ag) as [q|d pend] eqn:Hst.
      - destruct (xquiet_complete next k c ag q Hag Hst Hqk)
          as (c1 & ag1 & q1 & Hrun & Hlk1 & Hst1 & Hm1 & Hf1 & Hlog1 & Himg1
              & Hfr1).
        exists c1, [(k, c, c1)]. split_and!.
        + by split.
        + apply list_relations.Forall_singleton. split.
          * exact (pf_xquiet_run_solo next k c c1 Hrun).
          * simpl. intros ag2 Hag2. rewrite Hlk1 in Hag2.
            injection Hag2 as <-. by rewrite Hst1.
        + intros ag2 Hag2. rewrite Hlk1 in Hag2. injection Hag2 as <-.
          by rewrite Hst1.
        + exact Hfr1.
        + exact Hlog1.
        + exact Himg1.
        + intros j a. destruct (pf_xsolo_run_xtframe next k c c1
              (pf_xquiet_run_solo next k c c1 Hrun)) as (_ & _ & _ & Ho).
          apply Ho.
      - (* the disk: quiet IS at a boundary *)
        exists c, []. split_and!; [done|constructor| |done|done|done|by intros].
        intros ag2 Hag2. rewrite Hag in Hag2. injection Hag2 as <-.
        by rewrite Hst. }
    destruct Hstep as (c1 & segs1 & Hch1 & Hall1 & Hbd1 & Hfr1 & Hlog1 & Himg1
                       & Hobs1).
    destruct (IH c1 Hnd) as (c' & segs2 & Hch2 & Hall2 & Hbd2 & Hfr2 & Hlog2
                             & Himg2 & Hobs2).
    { intros k' ag Hk' Hlk'. apply (Hq k' ag); [set_solver|].
      rewrite -(Hfr1 k' ltac:(set_solver)). exact Hlk'. }
    exists c', (segs1 ++ segs2). split_and!.
    - by eapply chained_app.
    - by apply Forall_app.
    - intros k0 ag Hk0 Hlk0. apply elem_of_cons in Hk0 as [->|Hk0].
      + apply Hbd1. by rewrite -(Hfr2 k Hnk).
      + by eapply Hbd2.
    - intros k0 Hk0. rewrite (Hfr2 k0 ltac:(set_solver)).
      apply Hfr1. set_solver.
    - by rewrite Hlog2 Hlog1.
    - by rewrite Himg2 Himg1.
    - intros j a. etrans; [apply Hobs1|apply Hobs2].
  Qed.

End epilogues.

(** Two run-level bookkeeping lemmas, generic in the program type. *)
Lemma pf_run_bnd {P : Type} (pstep : P → wlabel → P → Prop) (c c' : wpcfg P) :
  rtc (wp_pf_run pstep) c c' → cfg_bnd c → cfg_bnd c'.
Proof.
  induction 1 as [|x y z (i & l & Hxy) _ IH]; [by intros Hb|].
  intros Hb. apply IH. exact (wp_pf_step_bnd pstep i l x y Hxy Hb).
Qed.

Lemma pf_run_ags_len {P : Type} (pstep : P → wlabel → P → Prop)
    (c c' : wpcfg P) :
  rtc (wp_pf_run pstep) c c' → length (pc_ags c') = length (pc_ags c).
Proof.
  induction 1 as [|x y z (i & l & Hxy) _ IH]; [done|].
  by rewrite IH (wp_pf_step_ags_len pstep i l x y Hxy).
Qed.

Lemma wp_init_ags_len {P : Type} (img : image) (ps : list P) :
  length (pc_ags (wp_init img ps)) = length ps.
Proof. by rewrite /wp_init /= length_fmap. Qed.


(* ====================================================================== *)
(** ** 9. THE PACKAGED THEOREM

    The section context is [WeakRobustCone]'s §8 at [pxv6] plus this
    stage's four premises (§7). *)

Section package.
  Context (TS : ptraces pxv6) (img : image) (ps : list pxv6).
  Context (Hwf : ptraces_wf (pstep_xv6 riscv_step) TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, WeakRobustSer.co_tc TS a).
  Context (Hwfl : WeakRobustSer.writes_fulfilled TS).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  Context (Hfo : WeakRobustAcyc.ptraces_fwd_own TS).
  Context (Hee : WeakRobustAcyc2.ee_ok TS).
  Context (nh : nat).
  Context (Hsplit : edges_split nh TS).
  Context (Hps_bnd : ∀ i p, ps !! i = Some p → pbnd p).
  Context (Hcq : ∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
                   ∀ T ag', pt_trs TS !! e1.1 = Some T →
                     at_ags T !! S e1.2 = Some ag' → pquiet (pa_st ag')).
  Context (Hres : ∀ i T k ag q,
             pt_trs TS !! i = Some T → at_ags T !! k = Some ag →
             pa_st ag = PHart q →
             match sp_m q with
             | None => True
             | Some m => sail_shaped m ∧ sail_live m ∧
                         ∃ d, oracle_consistent d m (sp_dev q)
             end).
  Context (Himgt : img_total img).

  (** THE READER IS A HART.  [b2] emits a reading label, and in
      [pstep_xv6] only the hart arm does; species is preserved by every
      step, so the record right after [b2] is a hart record too. *)
  Lemma reader_hart (b2 : gev) (T2 : atrace pxv6) (agn2 : wpagent pxv6) a ts :
    gev_reads TS b2 a ts →
    pt_trs TS !! b2.1 = Some T2 →
    at_ags T2 !! S b2.2 = Some agn2 →
    ∃ q, pa_st agn2 = PHart q.
  Proof.
    intros (l & Hl & Hin) HT Hagn.
    have Hev : ∃ ev2, at_evs T2 !! b2.2 = Some ev2 ∧ l = ae_lb ev2.
    { rewrite /gev_lb /gev_ev HT /= in Hl.
      destruct (at_evs T2 !! b2.2) as [ev2|] eqn:He; simpl in Hl; [|done].
      exists ev2. split; [done|by injection Hl]. }
    destruct Hev as (ev2 & Hev2 & Hlv).
    have Hatr := Hwf b2.1 T2 HT.
    destruct (asteps_wf_step (pstep_xv6 riscv_step) (pt_img TS) (pt_log TS)
                b2.1 (at_ags T2) (at_evs T2) b2.2 ev2 Hatr Hev2)
      as (ag & ag' & st' & f & Hag & Hag' & Hps & _ & Heq).
    have Hst : pa_st agn2 = st'.
    { have Hx : agn2 = ag' by congruence. by rewrite Hx Heq. }
    rewrite Hst -Hlv in Hps |- *.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data
                  |pr pw sr sw]; simpl in Hin;
      try (by apply elem_of_nil in Hin);
      (destruct (pa_st ag) as [q|d pend]; destruct st' as [q'|d' pend'];
       simpl in Hps; try done; [by exists q'|]);
      by destruct Hps as [(Hc & _)|(? & ? & _ & _ & _ & Hc)].
  Qed.

  (** THE READER'S CUT POSITION: exactly one past its own event. *)
  Lemma reader_nproc (order : list gev) (b2 : gev) :
    ¬ tc (gdep2 TS) b2 b2 → gev_wf TS b2 →
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2))) →
    NoDup order → nproc order b2.1 = S b2.2.
  Proof.
    intros Hrr Hwfb Hmem Hnd.
    have Hmemj := nproc_mem order b2.1 Hnd
                    (order_dc TS ps Hnag order b2 Hmem b2.1).
    have Hb2 : (b2.1, b2.2) = b2 by destruct b2.
    have Hin : (b2.1, b2.2) ∈ order
      by apply Hmem; rewrite Hb2; split; [done|by left].
    have Hlt : (b2.2 < nproc order b2.1)%nat by apply Hmemj.
    destruct (decide (S b2.2 = nproc order b2.1)) as [Heq|Hne]; [done|].
    exfalso.
    have Hin2 : (b2.1, S b2.2) ∈ order by apply Hmemj; lia.
    have Hwf2 : gev_wf TS (b2.1, S b2.2) by apply Hmem in Hin2 as [? _].
    have Hd : gdep2 TS b2 (b2.1, S b2.2).
    { apply gpo_gdep2. rewrite -Hb2. split_and!;
        [done|simpl; lia|by rewrite Hb2|done]. }
    apply Hmem in Hin2 as (_ & Hor2). destruct Hor2 as [Heq2|Htc2].
    - rewrite Heq2 in Hd. by apply Hrr, tc_once.
    - apply Hrr. by eapply tc_l.
  Qed.

  Theorem cone_segments (b1 b2 : gev) :
    bad nh TS b1 b2 → bad_min nh TS b2 →
    ∃ (order : list gev) (cfs : list (wpcfg pxv6)) (cmid : wpcfg pxv6)
      (segs : list seg) (cf : wpcfg pxv6),
      (** (a) THE BLOCK-CONTIGUOUS CONE CHAIN, forwarded from
              [WeakRobustCone.bad_edge_violates_blocks] at [bnd := pbnd]. *)
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2))) ∧
      NoDup order ∧
      order !! (length order - 1)%nat = Some b2 ∧
      (∀ n y, order !! n = Some y → ∀ x, gdep2 TS x y → gev_wf TS x →
         ∃ i, (i < n)%nat ∧ order !! i = Some x) ∧
      (∀ i j k x y z, (i < j)%nat → (j < k)%nat →
         order !! i = Some x → order !! j = Some y → order !! k = Some z →
         bid TS pbnd x = bid TS pbnd z → bid TS pbnd y = bid TS pbnd x) ∧
      (∀ i j x y, (i < j)%nat → order !! i = Some x → order !! j = Some y →
         bid TS pbnd x = bid TS pbnd y → (x.2 < y.2)%nat) ∧
      (∀ i j x y, order !! i = Some x → order !! j = Some y →
         bid TS pbnd y = bid TS pbnd b2 → bid TS pbnd x ≠ bid TS pbnd b2 →
         (i < j)%nat) ∧
      length cfs = S (length order) ∧
      cfs !! 0%nat = Some (wp_init img ps) ∧
      cfs !! (length order) = Some cmid ∧
      (∀ i e c c', order !! i = Some e → cfs !! i = Some c →
         cfs !! S i = Some c' → cstep (pstep_xv6 riscv_step) e.1 c c') ∧
      rtc (wp_pf_run (pstep_xv6 riscv_step)) (wp_init img ps) cmid ∧
      (** (b) THE COMPLETION PASS: a chain of SOLO, irq-free segments, one
              per completed agent (the reader's tail first), after which
              EVERY agent sits at an instruction boundary. *)
      chained segs cmid cf ∧ Forall (seg_ok riscv_step) segs ∧
      rtc (wp_pf_run (pstep_xv6 riscv_step)) cmid cf ∧
      (∀ j ag, pc_ags cf !! j = Some ag → pbnd (pa_st ag)) ∧
      (** (c) …and the violation SURVIVES it, in both forms. *)
      (∃ p m a, violates_at cf p m b1.1 b2.1 a) ∧
      violation_hart cls_of pub_of nh cf.
  Proof.
    intros Hbad Hmin.
    have Hbad2 := Hbad.
    destruct Hbad2 as (Hrf & Hne12 & Hh1 & Hh2 & _ & _).
    have Hrf2 := Hrf. destruct Hrf2 as (ts0 & a0 & Hts0 & Hrd0).
    have Hb2wf : gev_wf TS b2 by eapply gev_reads_wf.
    have Hrr : ¬ tc (gdep2 TS) b2 b2 by apply (Hmin b1 b2 Hbad).
    destruct (bad_edge_violates_blocks (pstep_xv6 riscv_step) TS img ps
                Hwf Hwsi Hco Hwfl (xv6_lat_free riscv_step)
                (xv6_ts_oblivious riscv_step) Himg Hnag Hdata Hps0 Hfo Hee
                nh Hsplit pbnd (pcsl TS Hwf Hcq) b1 b2 Hbad Hmin)
      as (order & cfs & cmid & Hmem & Hnd & Hlast & Hpred & Hcontig & Hinblk
          & Hrdlast & Hlenc & Hc0 & Hcfm & Hstepc & Hqc & Hrunm & Hv1 & Hv2).
    (* ---- the cut configuration ---- *)
    have Hqcm : qcfg (pstep_xv6 riscv_step) TS img ps order cmid.
    { have Hx := Hqc (length order) cmid Hcfm.
      by rewrite (take_ge order (length order) ltac:(lia)) in Hx. }
    have Hqcm2 := Hqcm.
    destruct Hqcm2 as (_ & Hcimg & _ & Hclen & Hcags).
    have Hbndm : cfg_bnd cmid
      by apply (pf_run_bnd _ _ _ Hrunm), cfg_bnd_init.
    (* ---- the reader's record ---- *)
    have Hb2lt : (b2.1 < length ps)%nat.
    { apply gev_wf_bounds in Hb2wf as (T & HT & _).
      apply lookup_lt_Some in HT. lia. }
    have [T2 HT2] : is_Some (pt_trs TS !! b2.1)
      by (apply lookup_lt_is_Some_2; lia).
    destruct (Hcags b2.1 T2 HT2) as (agn2 & Hagn2 & Hlkr).
    rewrite (reader_nproc order b2 Hrr Hb2wf Hmem Hnd) in Hagn2.
    destruct (reader_hart b2 T2 agn2 a0 ts0 Hrd0 HT2 Hagn2) as (qr & Hqr).
    set (agr := WPAgent (pa_st agn2)
                  (aevs_post (pi TS order) (take (nproc order b2.1) (at_evs T2))
                     ws_init) (∅ : gset nat)).
    have Hlkr2 : pc_ags cmid !! b2.1 = Some agr by exact Hlkr.
    have Hstr : pa_st agr = PHart qr by rewrite /agr /= Hqr.
    (* ---- (1) the reader's own completion ---- *)
    have Hrdc : ∃ c1 ag1 q1 ms,
        rtc (pf_xsolo riscv_step b2.1) cmid c1 ∧
        pc_ags c1 !! b2.1 = Some ag1 ∧ pa_st ag1 = PHart q1 ∧
        sp_m q1 = None ∧ sp_fence q1 = None ∧
        pc_log c1 = pc_log cmid ++ ms ∧
        Forall (λ mq, wm_tid mq = Some b2.1) ms ∧
        pc_img c1 = pc_img cmid ∧
        (∀ j, j ≠ b2.1 → pc_ags c1 !! j = pc_ags cmid !! j) ∧
        (∀ j a, (obs_flr cmid j a ≤ obs_flr c1 j a)%nat).
    { destruct (sp_m qr) as [mr|] eqn:Hm.
      - have Hr := Hres b2.1 T2 (S b2.2) agn2 qr HT2 Hagn2 Hqr.
        rewrite Hm in Hr. destruct Hr as (Hsh & Hlv & Hoc).
        destruct (xtail_complete riscv_step b2.1 cmid agr qr mr
                    ltac:(by rewrite Hcimg) Hbndm Hlkr2 Hstr Hm Hsh Hlv Hoc)
          as (c1 & ag1 & q1 & Hrun1 & Hlk1 & Hst1 & Hm1 & Hf1
              & ((msx & Hlogx & Hallx) & Himgx & Hfrx & Hobsx) & _).
        exists c1, ag1, q1, msx. split_and!;
          [exact Hrun1|exact Hlk1|exact Hst1|exact Hm1|exact Hf1
          |exact Hlogx|exact Hallx|exact Himgx|exact Hfrx|exact Hobsx].
      - destruct (xquiet_complete riscv_step b2.1 cmid agr qr Hlkr2 Hstr
                    ltac:(by rewrite /psail_quiet Hm))
          as (c1 & ag1 & q1 & Hrun1 & Hlk1 & Hst1 & Hm1 & Hf1 & Hlogq
              & Himgq & Hfrq).
        have Hrun1' : rtc (pf_xsolo riscv_step b2.1) cmid c1
          := pf_xquiet_run_solo riscv_step b2.1 cmid c1 Hrun1.
        exists c1, ag1, q1, []. split_and!;
          [exact Hrun1'|exact Hlk1|exact Hst1|exact Hm1|exact Hf1
          |by rewrite Hlogq app_nil_r|constructor|exact Himgq|exact Hfrq|].
        by destruct (pf_xsolo_run_xtframe riscv_step b2.1 cmid c1 Hrun1')
          as (_ & _ & _ & Ho). }
    destruct Hrdc as (c1 & ag1 & q1 & ms & Hrun1 & Hlk1 & Hst1 & Hm1 & Hf1
                      & Hlog1 & Hall1 & Himg1 & Hfr1 & Hobs1).
    (* ---- (2) every other agent's epilogue ---- *)
    set (ks := filter (λ k : nat, k ≠ b2.1) (seq 0 (length ps))).
    have Hksnd : NoDup ks
      by apply list_relations.NoDup_filter, list_numbers.NoDup_seq.
    have Hksmem : ∀ k, k ∈ ks ↔ ((k < length ps)%nat ∧ k ≠ b2.1).
    { intros k. rewrite /ks elem_of_list_filter elem_of_seq.
      split; [naive_solver lia|naive_solver lia]. }
    destruct (complete_agents_quiet riscv_step ks c1 Hksnd)
      as (cf & segs & Hch & Hallseg & Hbdf & Hfrf & Hlogf & Himgf & Hobsf).
    { intros k ag Hk Hlk. apply Hksmem in Hk as (Hklt & Hkne).
      eapply (cut_pquiet TS img ps Hwf Himg Hnag Hps0 Hee Hps_bnd Hcq Himgt
                order b2 cmid k ag Hmem Hnd Hqcm Hkne).
      by rewrite -(Hfr1 k Hkne). }
    (* ---- the assembled runs ---- *)
    have Hrun1r : rtc (wp_pf_run (pstep_xv6 riscv_step)) cmid c1
      := pf_xsolo_rtc_run riscv_step b2.1 cmid c1 Hrun1.
    have Hrun2r : rtc (wp_pf_run (pstep_xv6 riscv_step)) c1 cf
      := chained_run riscv_step segs c1 cf Hch Hallseg.
    have Hrunmf : rtc (wp_pf_run (pstep_xv6 riscv_step)) cmid cf
      by etrans; [exact Hrun1r|exact Hrun2r].
    have Hrunall : rtc (wp_pf_run (pstep_xv6 riscv_step)) (wp_init img ps) cf
      by etrans; [exact Hrunm|exact Hrunmf].
    have Hb2nin : b2.1 ∉ ks
      by (intros Hin; apply Hksmem in Hin as (_ & Hx); by apply Hx).
    (* ---- (3) every agent is at a boundary ---- *)
    have Hpbnd : ∀ j ag, pc_ags cf !! j = Some ag → pbnd (pa_st ag).
    { intros j ag Hlkj.
      destruct (decide (j = b2.1)) as [->|Hjne].
      - rewrite (Hfrf b2.1 Hb2nin) Hlk1 in Hlkj. injection Hlkj as <-.
        rewrite Hst1. by split.
      - apply (Hbdf j ag); [|exact Hlkj]. apply Hksmem. split; [|exact Hjne].
        apply lookup_lt_Some in Hlkj.
        rewrite (pf_run_ags_len _ _ _ Hrunall) wp_init_ags_len in Hlkj. lia. }
    (* ---- (4) the violation survives ---- *)
    destruct Hv1 as (p & mv & av & Hviol).
    have Hnej : b2.1 ≠ b1.1 by (intros Hx; apply Hne12; by rewrite Hx).
    have Hviol1 : violates_at c1 p mv b1.1 b2.1 av.
    { eapply (violates_at_append cmid c1 p mv b1.1 b2.1 av ms Hlog1);
        [|apply Hobs1|exact Hviol].
      apply list_relations.Forall_lookup_2. intros n mq Hn. left.
      rewrite (list_relations.Forall_lookup_1 _ _ _ _ Hall1 Hn).
      intros Heq. injection Heq as Heq. by apply Hnej. }
    have Hviolf : violates_at cf p mv b1.1 b2.1 av.
    { eapply (violates_at_append c1 cf p mv b1.1 b2.1 av []);
        [by rewrite Hlogf app_nil_r|constructor|apply Hobsf|exact Hviol1]. }
    (* ---- the package ---- *)
    exists order, cfs, cmid, ((b2.1, cmid, c1) :: segs), cf.
    split_and!; [exact Hmem|exact Hnd|exact Hlast|exact Hpred|exact Hcontig
                |exact Hinblk|exact Hrdlast|exact Hlenc|exact Hc0|exact Hcfm
                |exact Hstepc|exact Hrunm| | |exact Hrunmf|exact Hpbnd| |].
    - by split.
    - apply list_relations.Forall_cons. split; [|exact Hallseg].
      split; [exact Hrun1|].
      simpl. intros ag Hag. rewrite Hlk1 in Hag. injection Hag as <-.
      rewrite Hst1. by split.
    - by exists p, mv, av.
    - destruct Hviolf as (Hlogp & Htid & Hcls & Hpub & Hne' & Hbyte & Hobs).
      exists p, mv, b1.1, b2.1, av. split_and!;
        [exact Hlogp|exact Htid| |exact Hcls|exact Hpub|exact Hne'| |exact Hbyte
        |exact Hobs].
      + exists b1.1. split; [exact Htid|exact Hh1].
      + exists b2.1. split; [done|exact Hh2].
  Qed.

End package.
