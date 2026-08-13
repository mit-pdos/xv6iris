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

    §8  THE COMPLETION PASS and [cone_segments] (the stage-B4 export,
    kept verbatim).

    §9-§12  STAGE B5a: THE FULLY SEGMENTED EXPORT ([cone_segments2]).

    §9   The three upgrades a REPLAYED chain step needs.  (a) [w_relp] --
         the only component [WeakSailLTS2.lbl_class] reads -- is blind to
         the sigma-retiming of a replay ([w_relp_aevs_post]), so the
         trace's own class premise transfers to the replay's [wstate].
         (b) The class of a WRITING label is determined by the pre-state
         alone ([pxv6_class_det]: [sail_mstep]'s [MemWrite] arm pins the
         label outright, and its [MemRead] arm pins the constructor
         through [ak_latest]), so the premise transfers even though the
         replayed label is not literally the trace's.  (c) [rmw_tight] is
         a THEOREM, not a premise: [WeakPromiseBridge.own_coh] +
         [pf_rmw_latest] upgrade the [PFRmw] rule's own [read_ok] /
         [excl_ok] to the [lat := true] form ([xrmw_tight_own_coh]).
         (d) [pf_step_ni_or_irq] splits a pf step into an irq-free one
         and an interrupt delivery.

    §10  [seg2]: a segment is one of (A) [SegHart] -- a contiguous solo
         run of [pf_xsolo] (i.e. over the IRQ-FREE [pstep_ni_xv6], with
         [xcls_canon] and [xrmw_tight] at every step) between two
         instruction boundaries; (B) [SegIrq] -- ONE silent step in which
         a hart consumes the head of [sp_irq], boundary on both sides;
         (C) [SegDisk] -- a contiguous solo run of the disk from an empty
         burst buffer to an empty burst buffer whose log delta is exactly
         [WeakLang.wmsgs_of_map w] of one [WeakLang.wdisk_step]
         (re-stamped with the emitting agent's index -- [dmsgs]; at the
         standard vector [dmsgs n_disk] is the identity).  [chained2]
         threads them.  Two supporting invariants: [disk_relp] (a disk
         agent's [w_relp] is always [false], so its canonical emit class
         is [WCplain] -- which is what [wmsgs_of_map] stamps) and [dopen]
         (inside a group, the messages already emitted followed by what
         is still buffered are exactly one [wdisk_step]'s write set).

    §12  THE SEGMENTATION ITSELF.  [seg_build] walks the block-contiguous
         chain position by position, maintaining a configuration [d] that
         differs from the chain's [cfs !! n] only in the slots of agents
         that have FINISHED (whose silent epilogues have already been
         spliced in AT THE POSITION OF THEIR LAST STEP -- this is the run
         surgery, done by re-taking each chain step at the modified
         configuration with [WeakSailComplete.wp_pf_step_transplant]
         rather than by commuting the epilogues afterwards).  At most one
         agent is ever mid-block (block contiguity), which is what makes
         the walk work: when the stepping agent differs from the open
         one, the open one must already be at a boundary or finished.
         The reader's block is last, and its tail completion closes it.

         AN INTERRUPT DELIVERY IS NOT A CASE OF THAT WALK.  Since stage B
         a delivery is an ordinary step of the segment the agent is in
         ([xstep] = [pf_xsolo] or [pf_xirq]), carrying with it the
         seip-freedom of the residual it interrupts unless it landed at a
         boundary ([xseip_ok], supplied by [Hseip]).  So [seg_build] has
         ONE step case, not two, and the hart segments it exports may
         contain deliveries; [WeakComposeLang]'s refinement is what
         commutes them out to their block boundaries
         ([WeakSailComplete] §9), where they become [SegIrq] segments.
         What this file provides for that is §10b: the [pxv6] delivery
         step [pf_xirq], its forward commutation past a solo step
         ([pf_xirq_commute_step], [xirq_run_commute]) and the
         configuration equivalence [xcfg_eqv] the commutation lands in
         (pointwise-equal register files -- no funext) together with the
         transport of everything the cone exports across it
         ([xcfg_eqv_violates], [xcfg_eqv_violation_hart], [at_pbnd_eqv],
         [seg2_irq_ok_eqv], [seg2_disk_ok_eqv], [pf_xsolo_eqv]).

    ------------------------------------------------------------------------
    WHAT IS DELIVERED.

    [cone_segments] (stage B4) is unchanged: the block-contiguous cone
    chain of [WeakRobustCone] at [bnd := pbnd], a further chain of solo
    irq-free segments (one per completed agent, epilogues APPENDED AT THE
    END), and the violation at the final configuration.

    [cone_segments2] (stage B5a) is the FULLY SEGMENTED export, and is
    what stage B5b builds on:

      exists segs cf, chained2 segs (wp_init img ps) cf /\
        Forall seg2_ok segs /\ (exists p m a, violates_at cf p m b1.1 b2.1 a)
        /\ violation_hart cls_of pub_of nh cf
        /\ (forall j ag, pc_ags cf !! j = Some ag -> pbnd (pa_st ag)).

    Every step of the run is inside a segment; the three deviations the
    B4 header recorded (epilogues at the end; no delivery/disk-group
    arms; no [cls_canon]/[rmw_tight] at replayed steps) are all retired.
    ONE deviation remains, in (C) only: the disk's emitted messages carry
    the EMITTING AGENT's index as author, while [WeakLang.wmsgs_of_map]
    stamps [WeakLang.n_disk]; (C) therefore states the log delta as
    [dmsgs i (wmsgs_of_map w)], and [dmsgs_n_disk] collapses it at the
    standard agent vector.  (This file keeps [ps] abstract, so the disk's
    index is not known here to be [n_disk].)


    THE PREMISE LEDGER of §11-§12, beyond the mirrored [WeakRobustCone] context:
    [Hps_bnd] (initial states are boundaries), [Hcq] (the post-state of a
    cross-edge source is quiet), [Hres] (every trace record's residual is
    [sail_shaped] and [sail_live]), [Himgt]
    ([img_total]).  Layer-1's two side conditions are NOT premises —
    [WeakCompose.xv6_lat_free] and [xv6_ts_oblivious] discharge them.

    STAGE B5a ADDS EXACTLY TWO: [Hseip] (a trace step that is an
    [irq_deliver] from a NON-boundary pre-state interrupts a residual
    that never touches [sig_seip] -- [WeakSailComplete.seip_free_psail])
    and [Hcls] (every logged message carries the class its own author's
    pre-record computes -- [WeakSailLTS2.lbl_class] at the trace's own
    [wstate]).  [rmw_tight] is NOT a premise; it is derived from
    [own_coh].

    [Hseip] REPLACED [Hirqb] ("a delivery has a boundary pre-state"),
    which was a COVERAGE GAP rather than an assumption about the program:
    hardware asserts SEIP mid-instruction, so [Hirqb] excluded those
    behaviors outright.  [Hcls] is not a premise of the CAPSTONE any more
    either -- [WeakComposeLang] hands it in, having brought the behavior
    into canonical form with [WeakRetag] -- but it is still this section's
    hypothesis, since the retag is a whole-behavior operation and this
    file works one bundle at a time.

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
    ∃ c' ag' q',
      rtc (pf_xsolo next i) c c' ∧
      pc_ags c' !! i = Some ag' ∧ pa_st ag' = PHart q' ∧
      sp_m q' = None ∧ sp_fence q' = None ∧
      xtframe i c c' ∧ cfg_bnd c'.
  Proof.
    intros Him Hbnd Hlk Hst Hm Hsh Hlv.
    have Hl : hlink i c (prj_cfg q c) := prj_hlink q i c ag Hlk Hst.
    have Hlks : pc_ags (prj_cfg q c) !! i = Some (prj_ag q ag)
      by rewrite /= list_lookup_fmap Hlk.
    destruct (tail_complete next i (prj_cfg q c) (prj_ag q ag) m Him
                (prj_cfg_bnd q c Hbnd) Hlks
                ltac:(by rewrite /prj_ag /= Hst)
                Hsh Hlv)
      as (cs' & ags' & ms & fu & Hrun & _ & Hlk2 & (agb & Hagb & Hmb) & Hf2 & _).
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
      [Hres]     every trace record's residual is shaped and live (the
                 reader-tail completion's fuel);
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
             | Some m => sail_shaped m ∧ sail_live m
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

  (** The cut classification, TRACE SIDE (the form the segmentation of
      §12 needs: it names the record directly rather than reading it off a
      [qcfg] over the whole order). *)
  Lemma cut_pquiet_tr (order : list gev) (b2 : gev) j T agn :
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2))) →
    NoDup order →
    pt_trs TS !! j = Some T →
    at_ags T !! (nproc order j) = Some agn →
    j ≠ b2.1 → pquiet (pa_st agn).
  Proof.
    intros Hmem Hnd HT Hagn Hne.
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
    apply (Hcq (j, n') y Hd Hag T agn HT). simpl. exact Hagn.
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
(** ** 9. THE THREE UPGRADES a replayed chain step needs

    (a) [w_relp] does not see the transport σ, so the CLASS a canonical
        step would append is the same on the trace's own [wstate] and on
        the replay's σ-retimed one;
    (b) the CLASS of a writing label is determined by the pre-state alone
        ([pstep_xv6] pins the constructor and, for a store, the label
        outright), so the trace's class premise transfers to the replay's
        (possibly different) label;
    (c) [rmw_tight] is a THEOREM, not a premise: [own_coh] +
        [WeakPromiseBridge.pf_rmw_latest] upgrade the [PFRmw] rule's own
        [read_ok]/[excl_ok] to the [lat := true] form. *)

(** *** (a) [w_relp] is σ-blind *)

Lemma w_relp_load_post_bytes ws aq ats :
  w_relp (load_post_bytes ws aq ats) = w_relp ws.
Proof.
  rewrite /load_post_bytes. generalize (load_vpre ws aq) => v.
  revert ws. induction ats as [|at_ ats IH]; intros ws; [done|].
  by rewrite /= IH.
Qed.

Lemma w_relp_load_post_run ws aq base ts :
  w_relp (load_post_run ws aq base ts) = w_relp ws.
Proof. apply w_relp_load_post_bytes. Qed.

Lemma w_relp_store_post_bytes ws ws' rl as_ t t' :
  w_relp ws = w_relp ws' →
  w_relp (store_post_bytes ws rl as_ t) = w_relp (store_post_bytes ws' rl as_ t').
Proof.
  revert ws ws'. induction as_ as [|a as_ IH]; intros ws ws' Heq; [done|].
  by rewrite /store_post_bytes /= -/store_post_bytes; apply IH.
Qed.

Lemma w_relp_store_post_run ws ws' rl base n t t' :
  w_relp ws = w_relp ws' →
  w_relp (store_post_run ws rl base n t) = w_relp (store_post_run ws' rl base n t').
Proof. apply w_relp_store_post_bytes. Qed.

Lemma w_relp_aev_post (σ σ' : nat → nat) ev w w' :
  w_relp w = w_relp w' → w_relp (aev_post σ ev w) = w_relp (aev_post σ' ev w').
Proof.
  intros Heq. rewrite /aev_post.
  destruct (ae_lb ev) as [|aq lat base tvs|rl base data|aq rl base tvs data
                         |pr pw sr sw]; [done| | | |by rewrite /fence_post /= Heq].
  - by rewrite !w_relp_load_post_run.
  - destruct (ae_ts ev) as [ts|]; [|done]. by apply w_relp_store_post_run.
  - destruct (ae_ts ev) as [ts|]; [|done].
    apply w_relp_store_post_run. by rewrite !w_relp_load_post_run.
Qed.

Lemma w_relp_aevs_post (σ σ' : nat → nat) evs w w' :
  w_relp w = w_relp w' →
  w_relp (aevs_post σ evs w) = w_relp (aevs_post σ' evs w').
Proof.
  revert w w'. induction evs as [|ev evs IH] using rev_ind; intros w w' Heq;
    [done|].
  rewrite !aevs_post_app. by apply w_relp_aev_post, IH.
Qed.

(** …hence [lbl_class], which reads only [w_relp], is σ-blind. *)
Lemma lbl_class_relp l w w' :
  w_relp w = w_relp w' → lbl_class l w = lbl_class l w'.
Proof. intros Heq. destruct l; rewrite /lbl_class // Heq //. Qed.

(** *** (b) The class of a writing label is determined by the pre-state *)

Lemma sail_mstep_class_det (m : M unit) rs d iq l1 p1 l2 p2 :
  sail_mstep m rs d iq l1 p1 → sail_mstep m rs d iq l2 p2 →
  lb_writes l1 = true → lb_writes l2 = true →
  ∀ w, lbl_class l1 w = lbl_class l2 w.
Proof.
  destruct m as [y|T oc k].
  { intros [-> _] _ Hx. by simpl in Hx. }
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl;
    intros H1 H2 Hw1 Hw2;
    try (exfalso; exact H1);
    try (by destruct H1 as [-> _]; simpl in Hw1);
    try (by destruct H1 as [-> ?]; simpl in Hw1);
    try (by destruct H1 as [-> _]; destruct bk; simpl in Hw1).
  - (* MemRead *)
    revert H1 H2 Hw1 Hw2.
    destruct (dev_addr (Interface.ReadReq.pa req));
      [by intros [-> _] _ Hw1 _; simpl in Hw1|].
    intros [_ H1] [_ H2] Hw1 Hw2 w.
    destruct l1 as [|aq1 lat1 base1 tvs1|rl1 base1 data1
                   |aq1 rl1 base1 tvs1 data1|?????]; try done.
    destruct l2 as [|aq2 lat2 base2 tvs2|rl2 base2 data2
                   |aq2 rl2 base2 tvs2 data2|?????]; try done.
  - (* MemWrite *)
    revert H1 H2 Hw1 Hw2.
    destruct (dev_addr (Interface.WriteReq.pa req));
      [by intros [-> _] _ Hw1 _; simpl in Hw1|].
    by intros (-> & _) (-> & _) _ _ w.
Qed.

Lemma pxv6_class_det next p l1 p1 l2 p2 :
  pstep_xv6 next p l1 p1 → pstep_xv6 next p l2 p2 →
  lb_writes l1 = true → lb_writes l2 = true →
  ∀ w, lbl_class l1 w = lbl_class l2 w.
Proof.
  destruct p as [q|dv pend].
  - destruct p1 as [q1|??]; [|done]. destruct p2 as [q2|??]; [|done].
    rewrite /pstep_xv6 /sail_step.
    destruct (sp_fence q) as [[[[pr pw] sr] sw]|]; [by intros [-> _] _ Hx|].
    intros [(-> & _)|H1] [(-> & _)|H2] Hw1 Hw2; try done.
    destruct (sp_m q) as [m|]; [|by destruct H1 as [-> _]].
    by eapply sail_mstep_class_det.
  - destruct p1 as [?|d1 pend1]; [done|]. destruct p2 as [?|d2 pend2]; [done|].
    intros [(-> & _)|(m1 & r1 & Hp1 & _ & _ & ->)]
           [(-> & _)|(m2 & r2 & Hp2 & _ & _ & ->)] Hw1 Hw2 w; done.
Qed.

(** *** (c) [rmw_tight] IS A THEOREM: [own_coh] upgrades the [PFRmw]
        rule's own side conditions to the [lat := true] form. *)

Lemma xrmw_tight_own_coh (pstep : pxv6 → wlabel → pxv6 → Prop)
    (i : agent) (l : wlabel) (c c' : wpcfg pxv6) :
  own_coh c → wp_pf_step pstep i l c c' → xrmw_tight i l c.
Proof.
  intros Hoc Hstep.
  destruct Hstep as
    [cfg ag0 st' Hlk0 Hps
    |cfg ag0 aq0 lat0 base0 tvs0 st' Hlk0 Hps Hr
    |cfg ag0 rl0 base0 data0 kk st' Hlk0 Hps Hne
    |cfg ag0 aq0 rl0 base0 tvs0 data0 kk st' Hlk0 Hps Hne Hlen Hr He
    |cfg ag0 pr0 pw0 sr0 sw0 st' Hlk0 Hps]; try exact I.
  simpl. intros ag Hlk. rewrite Hlk0 in Hlk. injection Hlk as <-.
  have Hlat := pf_rmw_latest cfg i ag0 aq0 base0 tvs0 Hoc Hlk0 Hr He.
  intros j t v Htv. destruct (Hr j t v Htv) as (H1 & H2 & _).
  split_and!; [exact H1|exact H2|intros _].
  have Hj : tvs0.*1 !! j = Some t by rewrite list_lookup_fmap Htv.
  by destruct (Hlat j t Hj) as (_ & Hnw).
Qed.

(* ---------------------------------------------------------------- *)
(** *** THE DELIVERY AS A CONFIGURATION STEP, AND THE MIXED SEGMENT STEP

    Stage B's coverage fix (the premise [Hseip] of §12): the hardware
    asserts SEIP mid-instruction, so [WeakSailLTS.sail_step]'s
    [irq_deliver] arm may fire STRICTLY INSIDE a block.  A hart segment's
    run is therefore a MIX of irq-free solo steps and deliveries
    ([xstep]), each delivery carrying the SEIP-FREEDOM of the residual it
    interrupts — unless it lands at an instruction boundary, where there
    is no residual to speak of ([xseip_ok]).  [WeakComposeLang]'s
    refinement pass commutes every mid-block delivery FORWARD to its
    block's end (the kit of [WeakSailComplete] §9), so nothing downstream
    of the refinement ever sees one inside a block, and [seg2_irq_ok]
    keeps its boundary shape. *)

(** "agent [i] is at an instruction boundary in [c]". *)
Definition at_pbnd (i : agent) (c : wpcfg pxv6) : Prop :=
  ∀ ag, pc_ags c !! i = Some ag → pbnd (pa_st ag).

Definition pf_xirq (i : agent) (c c' : wpcfg pxv6) : Prop :=
  ∃ ag q q', pc_ags c !! i = Some ag ∧ pa_st ag = PHart q ∧
    irq_deliver q WeakPromise.LSilent q' ∧
    c' = WPCfg (pc_img c) (pc_log c)
           (<[i := WPAgent (PHart q') (pa_ws ag) (pa_prom ag)]> (pc_ags c)).

(** The delivery arm of [WeakSailLTS.sail_step] is GATED on [sp_fence =
    None] (a parked [fence.tso] admits nothing else), so [pf_xirq] is a
    real step only where the gate is open.  The gate is NOT part of
    [pf_xirq] because the forward commutation may move a delivery past a
    [Barrier], which PARKS a fence: what the refinement needs is that the
    gate is open where the delivery finally FIRES, i.e. at a block
    boundary, and [pbnd] says exactly that. *)
Definition xfence_free (i : agent) (c : wpcfg pxv6) : Prop :=
  ∀ ag q, pc_ags c !! i = Some ag → pa_st ag = PHart q → sp_fence q = None.

(** "this agent's residual never touches the pin" — and its conditional
    form, which is exactly what [Hseip] supplies. *)
Definition xseip_free (i : agent) (c : wpcfg pxv6) : Prop :=
  ∀ ag q, pc_ags c !! i = Some ag → pa_st ag = PHart q → seip_free_psail q.

Definition xseip_ok (i : agent) (c : wpcfg pxv6) : Prop :=
  ∀ ag q, pc_ags c !! i = Some ag → pa_st ag = PHart q →
    ¬ pbnd (PHart q) → seip_free_psail q.

(** ONE STEP OF A HART SEGMENT. *)
Definition xstep (i : agent) (c c' : wpcfg pxv6) : Prop :=
  pf_xsolo riscv_step i c c' ∨
  (xseip_ok i c ∧ xfence_free i c ∧ pf_xirq i c c').

Lemma irq_deliver_shape q q' :
  irq_deliver q WeakPromise.LSilent q' →
  sp_m q' = sp_m q ∧ sp_fence q' = sp_fence q ∧ sp_dev q' = sp_dev q.
Proof. intros (_ & v & iq & _ & ->). by split_and!. Qed.

Lemma sail_step_irq next p l p' :
  sp_fence p = None → irq_deliver p l p' → sail_step next p l p'.
Proof. intros Hf Hd. rewrite /sail_step Hf. by left. Qed.

Lemma pf_xirq_pf_step (next : bool → M unit) i c c' :
  xfence_free i c → pf_xirq i c c' →
  wp_pf_step (pstep_xv6 next) i WeakPromise.LSilent c c'.
Proof.
  intros Hf (ag & q & q' & Hlk & Hst & Hdel & ->).
  apply (PFSilent (pstep_xv6 next) i c ag (PHart q') Hlk).
  rewrite /pstep_xv6 Hst.
  exact (sail_step_irq next q WeakPromise.LSilent q' (Hf ag q Hlk Hst) Hdel).
Qed.

Lemma pf_xirq_run (next : bool → M unit) i c c' :
  xfence_free i c → pf_xirq i c c' → wp_pf_run (pstep_xv6 next) c c'.
Proof. intros Hf H. exists i, WeakPromise.LSilent. by eapply pf_xirq_pf_step. Qed.

Lemma xfence_free_bnd i c : at_pbnd i c → xfence_free i c.
Proof.
  intros Hb ag q Hlk Hst. have Hp := Hb ag Hlk. rewrite Hst in Hp. by apply Hp.
Qed.

Lemma xfence_free_irq i c c' :
  pf_xirq i c c' → xfence_free i c → xfence_free i c'.
Proof.
  intros (ag & q & q0 & Hlk & Hst & Hdel & ->) Hf ag' q' Hlk' Hst'.
  simpl in Hlk'. rewrite (lookup_insert_self (pc_ags c) i _ ag Hlk) in Hlk'.
  injection Hlk' as <-. simpl in Hst'. injection Hst' as <-.
  destruct (irq_deliver_shape q q0 Hdel) as (_ & Hfe & _).
  rewrite Hfe. exact (Hf ag q Hlk Hst).
Qed.

Lemma pf_xirq_frame i c c' :
  pf_xirq i c c' →
  pc_img c' = pc_img c ∧ pc_log c' = pc_log c ∧
  length (pc_ags c') = length (pc_ags c) ∧
  (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
Proof.
  intros (ag & q & q' & Hlk & _ & _ & ->). split_and!; [done|done| |].
  - simpl. by rewrite length_insert.
  - intros j Hj. simpl. by apply lookup_insert_other.
Qed.

Lemma pf_xirq_at i c c' :
  pf_xirq i c c' →
  ∃ ag ag' q q', pc_ags c !! i = Some ag ∧ pa_st ag = PHart q ∧
     pc_ags c' !! i = Some ag' ∧ pa_st ag' = PHart q' ∧
     pa_ws ag' = pa_ws ag ∧ pa_prom ag' = pa_prom ag ∧
     irq_deliver q WeakPromise.LSilent q'.
Proof.
  intros (ag & q & q' & Hlk & Hst & Hdel & ->).
  exists ag, (WPAgent (PHart q') (pa_ws ag) (pa_prom ag)), q, q'.
  split_and!; [exact Hlk|exact Hst| |done|done|done|exact Hdel].
  simpl. by eapply lookup_insert_self, Hlk.
Qed.

Lemma pf_xirq_obs i c c' j a : pf_xirq i c c' → obs_flr c' j a = obs_flr c j a.
Proof.
  intros Hirq. rewrite /obs_flr.
  destruct (pf_xirq_frame i c c' Hirq) as (_ & _ & _ & Hfr).
  destruct (decide (j = i)) as [->|Hj].
  - destruct (pf_xirq_at i c c' Hirq)
      as (ag & ag' & q & q' & Hlk & _ & Hlk' & _ & Hws & _).
    by rewrite Hlk Hlk' Hws.
  - by rewrite (Hfr j Hj).
Qed.

Lemma xstep_run i c c' : xstep i c c' → wp_pf_run (pstep_xv6 riscv_step) c c'.
Proof.
  intros [Hs|(_ & Hf & Hirq)]; [by apply (pf_xsolo_run riscv_step i)|].
  by eapply pf_xirq_run.
Qed.

Lemma xstep_rtc_run i c c' :
  rtc (xstep i) c c' → rtc (wp_pf_run (pstep_xv6 riscv_step)) c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [exact (xstep_run i x y Hxy)|exact IH].
Qed.

Lemma pf_xsolo_rtc_xstep i c c' :
  rtc (pf_xsolo riscv_step i) c c' → rtc (xstep i) c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [by left|exact IH].
Qed.

(* ================================================================== *)
(** *** CONFIGURATIONS THAT AGREE UP TO POINTWISE REGISTER EQUALITY

    The forward commutation of a delivery cannot end at a LITERALLY equal
    configuration ([WeakSailComplete] §9, deviation (b): [regstate]'s
    fields are functions, and swapping two [register_set]s of the same
    field group needs functional extensionality, which this chain does
    not use).  [xcfg_eqv] is the [pxv6] twin of the kit's [cfg_eqv],
    globalised over agents (successive segments move different agents):
    image, log, every [wstate] and promise set and every program state
    EXCEPT the raw register files, which agree register by register.
    Everything the cone exports — [violates_at], [violation_hart],
    boundary-ness, [obs_flr] — is blind to the difference. *)

Definition pxv6_eqv (p q : pxv6) : Prop :=
  match p, q with
  | PHart a, PHart b => psail_eqv a b
  | PDisk d1 l1, PDisk d2 l2 => d1 = d2 ∧ l1 = l2
  | _, _ => False
  end.

Lemma pxv6_eqv_refl p : pxv6_eqv p p.
Proof. destruct p; simpl; [apply psail_eqv_refl|by split]. Qed.

Lemma pxv6_eqv_sym p q : pxv6_eqv p q → pxv6_eqv q p.
Proof.
  destruct p, q; simpl; try done; [apply psail_eqv_sym|by intros [-> ->]].
Qed.

Lemma pxv6_eqv_trans p q r : pxv6_eqv p q → pxv6_eqv q r → pxv6_eqv p r.
Proof.
  destruct p, q, r; simpl; try done;
    [apply psail_eqv_trans|by intros [-> ->] [-> ->]].
Qed.

Lemma pxv6_eqv_pbnd p q : pxv6_eqv p q → pbnd p → pbnd q.
Proof.
  destruct p as [a|d1 l1], q as [b|d2 l2]; simpl; try done.
  - intros ((Hm & _ & Hf & _) & _) (H1 & H2). rewrite -Hm -Hf. by split.
  - by intros [-> ->].
Qed.

Lemma pxv6_eqv_hart a q : pxv6_eqv (PHart a) q → ∃ b, q = PHart b ∧ psail_eqv a b.
Proof. destruct q as [b|??]; [by exists b|done]. Qed.

Definition xag_eqv (ag ag' : wpagent pxv6) : Prop :=
  pa_ws ag' = pa_ws ag ∧ pa_prom ag' = pa_prom ag ∧
  pxv6_eqv (pa_st ag) (pa_st ag').

Lemma xag_eqv_refl ag : xag_eqv ag ag.
Proof. split_and!; [done|done|apply pxv6_eqv_refl]. Qed.

Lemma xag_eqv_sym ag ag' : xag_eqv ag ag' → xag_eqv ag' ag.
Proof.
  intros (H1 & H2 & H3). split_and!; [by rewrite H1|by rewrite H2
                                     |by apply pxv6_eqv_sym].
Qed.

Definition xcfg_eqv (c d : wpcfg pxv6) : Prop :=
  pc_img d = pc_img c ∧ pc_log d = pc_log c ∧
  length (pc_ags d) = length (pc_ags c) ∧
  (∀ j ag, pc_ags c !! j = Some ag →
     ∃ ag', pc_ags d !! j = Some ag' ∧ xag_eqv ag ag').

Lemma xcfg_eqv_refl c : xcfg_eqv c c.
Proof.
  split_and!; [done|done|done|]. intros j ag Hlk.
  exists ag. split; [exact Hlk|apply xag_eqv_refl].
Qed.

Lemma xcfg_eqv_lookup c d j ag :
  xcfg_eqv c d → pc_ags c !! j = Some ag →
  ∃ ag', pc_ags d !! j = Some ag' ∧ xag_eqv ag ag'.
Proof. intros (_ & _ & _ & H). exact (H j ag). Qed.

Lemma xcfg_eqv_sym c d : xcfg_eqv c d → xcfg_eqv d c.
Proof.
  intros (Hi & Hl & Hlen & Hag). split_and!;
    [by rewrite Hi|by rewrite Hl|by rewrite Hlen|].
  intros j ag' Hlk'.
  have Hlt : (j < length (pc_ags c))%nat.
  { rewrite -Hlen. by eapply lookup_lt_Some. }
  have [ag Hlk] : is_Some (pc_ags c !! j) by apply lookup_lt_is_Some_2.
  destruct (Hag j ag Hlk) as (ag2 & Hlk2 & Heq).
  rewrite Hlk' in Hlk2. injection Hlk2 as <-.
  exists ag. split; [exact Hlk|by apply xag_eqv_sym].
Qed.

Lemma xcfg_eqv_trans c d e : xcfg_eqv c d → xcfg_eqv d e → xcfg_eqv c e.
Proof.
  intros (Hi1 & Hl1 & Hn1 & Ha1) (Hi2 & Hl2 & Hn2 & Ha2). split_and!;
    [by rewrite Hi2|by rewrite Hl2|by rewrite Hn2|].
  intros j ag Hlk.
  destruct (Ha1 j ag Hlk) as (ag1 & Hlk1 & (H1 & H2 & H3)).
  destruct (Ha2 j ag1 Hlk1) as (ag2 & Hlk2 & (G1 & G2 & G3)).
  exists ag2. split; [exact Hlk2|].
  split_and!; [by rewrite G1|by rewrite G2|by eapply pxv6_eqv_trans].
Qed.

Lemma xcfg_eqv_obs c d j a : xcfg_eqv c d → obs_flr d j a = obs_flr c j a.
Proof.
  intros Heq. have Heq2 := Heq. destruct Heq2 as (_ & _ & Hlen & Hag).
  rewrite /obs_flr. destruct (pc_ags c !! j) as [ag|] eqn:Hlk.
  - destruct (Hag j ag Hlk) as (ag' & Hlk' & (Hws & _ & _)).
    by rewrite Hlk' Hws.
  - destruct (pc_ags d !! j) as [ag'|] eqn:Hlk'; [|done].
    exfalso. have Hlt : (j < length (pc_ags c))%nat.
    { rewrite -Hlen. by eapply lookup_lt_Some. }
    destruct (lookup_lt_is_Some_2 (pc_ags c) j Hlt) as (agz & Hagz).
    by rewrite Hlk in Hagz.
Qed.

Lemma xcfg_eqv_bnd c d :
  xcfg_eqv c d → (∀ j ag, pc_ags c !! j = Some ag → pbnd (pa_st ag)) →
  ∀ j ag, pc_ags d !! j = Some ag → pbnd (pa_st ag).
Proof.
  intros Heq Hb j ag' Hlk'.
  destruct (xcfg_eqv_lookup d c j ag' (xcfg_eqv_sym c d Heq) Hlk')
    as (ag & Hlk & (_ & _ & Hst)).
  apply (pxv6_eqv_pbnd (pa_st ag') (pa_st ag')); [apply pxv6_eqv_refl|].
  eapply pxv6_eqv_pbnd; [exact (pxv6_eqv_sym _ _ Hst)|].
  exact (Hb j ag Hlk).
Qed.

Lemma xcfg_eqv_violates c d p m i j a :
  xcfg_eqv c d → violates_at c p m i j a → violates_at d p m i j a.
Proof.
  intros Heq (Hlog & Htid & Hcls & Hpub & Hne & Hbyte & Hobs).
  have Hl : pc_log d = pc_log c by destruct Heq as (_ & H & _).
  split_and!; [by rewrite Hl|done|done| |done|done|].
  - intros (p2 & m2 & Heq2 & Hlog2 & Hwp). apply Hpub.
    exists p2, m2. rewrite -Hl. by split_and!.
  - by rewrite (xcfg_eqv_obs c d j a Heq).
Qed.

Lemma xcfg_eqv_violation_hart nh c d :
  xcfg_eqv c d →
  violation_hart cls_of pub_of nh c → violation_hart cls_of pub_of nh d.
Proof.
  intros Heq (p & m & i & j & a & Hlog & Htid & Hh1 & Hcls & Hpub & Hne & Hh2
              & Hbyte & Hobs).
  have Hv : violates_at c p m i j a by split_and!.
  destruct (xcfg_eqv_violates c d p m i j a Heq Hv)
    as (Hlog' & Htid' & Hcls' & Hpub' & Hne' & Hbyte' & Hobs').
  exists p, m, i, j, a. by split_and!.
Qed.

(** The one construction: two configurations that agree except in ONE
    agent's slot, whose two records are [xag_eqv]. *)
Lemma xcfg_eqv_ins (c d : wpcfg pxv6) i x y :
  xcfg_eqv c d → is_Some (pc_ags c !! i) → xag_eqv x y →
  ∀ (img : image) (lg : list wmsg),
    xcfg_eqv (WPCfg img lg (<[i := x]> (pc_ags c)))
             (WPCfg img lg (<[i := y]> (pc_ags d))).
Proof.
  intros Heq [ag0 Hag0] Hxy img lg. have Heq2 := Heq.
  destruct Heq2 as (_ & _ & Hlen & Hag).
  split_and!; [done|done|by rewrite /= !length_insert Hlen|].
  intros j ag Hlk. simpl in Hlk |- *.
  destruct (decide (j = i)) as [->|Hj].
  - rewrite (lookup_insert_self (pc_ags c) i x ag0 Hag0) in Hlk.
    injection Hlk as <-. destruct (Hag i ag0 Hag0) as (ag1 & Hag1 & _).
    exists y. split; [by eapply lookup_insert_self, Hag1|exact Hxy].
  - rewrite (lookup_insert_other (pc_ags c) i x j Hj) in Hlk.
    rewrite (lookup_insert_other (pc_ags d) i y j Hj). by apply Hag.
Qed.

(* ---------------------------------------------------------------- *)
(** *** The LTS is blind to the difference *)

Lemma sail_step_eqv next p q l p' :
  psail_eqv p q → sail_step next p l p' →
  ∃ q', sail_step next q l q' ∧ psail_eqv p' q'.
Proof.
  intros Heqv Hstep.
  destruct (sail_step_irq_or_ni next p l p' Hstep)
    as [[Hf (-> & v & iq & Hiq & ->)]|Hni].
  - have Heqv2 := Heqv. destruct Heqv2 as ((Hm & Hd & Hfe & Hr) & Hirq).
    exists (PSail (sp_m q) (register_set sig_seip v (sp_regs q)) (sp_dev q)
              (sp_fence q) iq).
    have Hfq : sp_fence q = None by rewrite -Hfe.
    split.
    + apply (sail_step_irq next q WeakPromise.LSilent _ Hfq).
      apply irq_deliver_intro. by rewrite -Hirq.
    + split; [split_and!|]; simpl;
        [by rewrite Hm|by rewrite Hd|by rewrite Hfe|by apply regs_agree_set
        |done].
  - destruct (sail_step_ni_frame (λ _, False) next p q l p' (proj1 Heqv)
                (regs_free_psail_triv p) Hni) as (q' & Hq' & Hag & Hirq').
    exists q'. split; [by apply sail_step_ni_step|]. split; [exact Hag|].
    rewrite (sail_step_ni_irq next p l p' Hni) Hirq'. exact (proj2 Heqv).
Qed.

Lemma pstep_xv6_eqv next p q l p' :
  pxv6_eqv p q → pstep_xv6 next p l p' →
  ∃ q', pstep_xv6 next q l q' ∧ pxv6_eqv p' q'.
Proof.
  destruct p as [a|d1 l1], q as [b|d2 l2]; simpl; try done.
  - intros Heqv Hstep. destruct p' as [a'|dd pend]; [|done].
    destruct (sail_step_eqv next a b l a' Heqv Hstep) as (b' & H1 & H2).
    by exists (PHart b').
  - intros [-> ->] Hstep. exists p'. split; [exact Hstep|apply pxv6_eqv_refl].
Qed.

Lemma pstep_ni_xv6_eqv next p q l p' :
  pxv6_eqv p q → pstep_ni_xv6 next p l p' →
  ∃ q', pstep_ni_xv6 next q l q' ∧ pxv6_eqv p' q'.
Proof.
  destruct p as [a|d1 l1], q as [b|d2 l2]; simpl; try done.
  - intros Heqv Hstep. destruct p' as [a'|dd pend]; [|done].
    destruct (sail_step_ni_frame (λ _, False) next a b l a' (proj1 Heqv)
                (regs_free_psail_triv a) Hstep) as (b' & Hb' & Hag & Hirq').
    exists (PHart b'). split; [exact Hb'|]. split; [exact Hag|].
    rewrite (sail_step_ni_irq next a l a' Hstep) Hirq'. exact (proj2 Heqv).
  - intros [-> ->] Hstep. exists p'. split; [exact Hstep|apply pxv6_eqv_refl].
Qed.

Lemma wp_pf_step_agent {P : Type} (pstep : P → wlabel → P → Prop)
    i l (c c' : wpcfg P) :
  wp_pf_step pstep i l c c' → ∃ ag, pc_ags c !! i = Some ag.
Proof.
  intros Hstep. destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kk st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps]; by exists ag.
Qed.

(** THE BISIMULATION for a solo step: same label, same log growth, same
    [wstate], and a twinned successor. *)
Lemma pf_xsolo_eqv i c d c' :
  xcfg_eqv c d → pf_xsolo riscv_step i c c' →
  ∃ d', pf_xsolo riscv_step i d d' ∧ xcfg_eqv c' d'.
Proof.
  intros Heq (l & Hstep & Hcls & Hrmw).
  destruct (wp_pf_step_agent (pstep_ni_xv6 riscv_step) i l c c' Hstep)
    as (ag & Hlk).
  destruct (xcfg_eqv_lookup c d i ag Heq Hlk)
    as (agd & Hlkd & Hws & Hprom & Hst).
  destruct (wp_pf_step_inv (pstep_ni_xv6 riscv_step) i l c c' ag Hstep Hlk)
    as (st' & ms & Hps & Himg' & Hlog' & Hags' & Hre).
  destruct (pstep_ni_xv6_eqv riscv_step (pa_st ag) (pa_st agd) l st' Hst Hps)
    as (stD & HpsD & HstD).
  have Heq2 := Heq. destruct Heq2 as (Himgd & Hlogd & Hlend & _).
  exists (WPCfg (pc_img c) (pc_log c ++ ms)
            (<[i := WPAgent stD (post_ws l (pa_ws ag) (length (pc_log c)))
                      (pa_prom ag)]> (pc_ags d))).
  split.
  - exists l. split_and!.
    + exact (Hre d agd stD Hlkd Hws Hprom Himgd Hlogd HpsD).
    + intros ag2 msg Hag2 Heq2. simpl in Heq2, Hag2.
      rewrite Hlkd in Hag2. injection Hag2 as <-.
      rewrite Hlogd in Heq2. apply app_inv_head in Heq2. subst ms.
      rewrite Hws. apply (Hcls ag msg Hlk). by rewrite Hlog'.
    + rewrite /xrmw_tight in Hrmw |- *. destruct l; try done.
      intros ag2 Hag2. rewrite Hlkd in Hag2. injection Hag2 as <-.
      rewrite Himgd Hlogd Hws. exact (Hrmw ag Hlk).
  - have Hc' : c' = WPCfg (pc_img c) (pc_log c ++ ms)
                      (<[i := WPAgent st'
                                (post_ws l (pa_ws ag) (length (pc_log c)))
                                (pa_prom ag)]> (pc_ags c)).
    { destruct c' as [i' l' a']; simpl in Himg', Hlog', Hags'.
      by rewrite Himg' Hlog' Hags'. }
    rewrite Hc'. apply (xcfg_eqv_ins c d i _ _ Heq); [by exists ag|].
    by split_and!.
Qed.

Lemma pf_xsolo_rtc_eqv i c d c' :
  xcfg_eqv c d → rtc (pf_xsolo riscv_step i) c c' →
  ∃ d', rtc (pf_xsolo riscv_step i) d d' ∧ xcfg_eqv c' d'.
Proof.
  intros Heq Hrun. revert d Heq.
  induction Hrun as [x|x y z Hxy _ IH]; intros d Heq.
  { exists d. split; [apply rtc_refl|exact Heq]. }
  destruct (pf_xsolo_eqv i x d y Heq Hxy) as (dy & Hdy & Heqy).
  destruct (IH dy Heqy) as (dz & Hdz & Heqz).
  exists dz. split; [by eapply rtc_l|exact Heqz].
Qed.

Lemma pf_xirq_eqv i c d c' :
  xcfg_eqv c d → pf_xirq i c c' → ∃ d', pf_xirq i d d' ∧ xcfg_eqv c' d'.
Proof.
  intros Heq (ag & q & q' & Hlk & Hst & Hdel & ->).
  destruct (xcfg_eqv_lookup c d i ag Heq Hlk)
    as (agd & Hlkd & Hws & Hprom & Hstd).
  rewrite Hst in Hstd. destruct (pxv6_eqv_hart q (pa_st agd) Hstd) as (b & Hb & Hqb).
  have Hqb2 := Hqb. destruct Hqb2 as ((Hm & Hdv & Hfe & Hr) & Hirq).
  destruct Hdel as (_ & v & iq & Hiq & ->).
  have Heq2 := Heq. destruct Heq2 as (Himgd & Hlogd & Hlend & _).
  exists (WPCfg (pc_img c) (pc_log c)
            (<[i := WPAgent
                      (PHart (PSail (sp_m b) (register_set sig_seip v (sp_regs b))
                                (sp_dev b) (sp_fence b) iq))
                      (pa_ws ag) (pa_prom ag)]> (pc_ags d))).
  split.
  - exists agd, b,
      (PSail (sp_m b) (register_set sig_seip v (sp_regs b)) (sp_dev b)
         (sp_fence b) iq).
    split_and!; [exact Hlkd|exact Hb| |].
    + apply irq_deliver_intro. by rewrite -Hirq.
    + by rewrite Himgd Hlogd Hws Hprom.
  - apply (xcfg_eqv_ins c d i _ _ Heq); [by exists ag|].
    split_and!; [done|done|]. simpl. split; [split_and!|]; simpl;
      [by rewrite Hm|by rewrite Hdv|by rewrite Hfe|by apply regs_agree_set|done].
Qed.

Lemma pf_xirq_rtc_eqv i c d c' :
  xcfg_eqv c d → rtc (pf_xirq i) c c' →
  ∃ d', rtc (pf_xirq i) d d' ∧ xcfg_eqv c' d'.
Proof.
  intros Heq Hrun. revert d Heq.
  induction Hrun as [x|x y z Hxy _ IH]; intros d Heq.
  { exists d. split; [apply rtc_refl|exact Heq]. }
  destruct (pf_xirq_eqv i x d y Heq Hxy) as (dy & Hdy & Heqy).
  destruct (IH dy Heqy) as (dz & Hdz & Heqz).
  exists dz. split; [by eapply rtc_l|exact Heqz].
Qed.

(* ---------------------------------------------------------------- *)
(** *** SEIP-freedom: transport and preservation *)

Lemma xseip_free_eqv i c d : xcfg_eqv c d → xseip_free i c → xseip_free i d.
Proof.
  intros Heq Hfr ag' q' Hlk' Hst'.
  destruct (xcfg_eqv_lookup d c i ag' (xcfg_eqv_sym c d Heq) Hlk')
    as (ag & Hlk & (_ & _ & Hst)).
  rewrite Hst' in Hst.
  destruct (pxv6_eqv_hart q' (pa_st ag) Hst) as (q & Hq & Hqq).
  have Hm : sp_m q' = sp_m q by apply (proj1 (proj1 Hqq)).
  rewrite /seip_free_psail /regs_free_psail Hm.
  exact (Hfr ag q Hlk Hq).
Qed.

Lemma xseip_free_irq i c c' :
  pf_xirq i c c' → xseip_free i c → xseip_free i c'.
Proof.
  intros Hirq Hfr ag' q' Hlk' Hst'.
  destruct (pf_xirq_at i c c' Hirq)
    as (ag & ag2 & q & q2 & Hlk & Hst & Hlk2 & Hst2 & _ & _ & Hdel).
  rewrite Hlk' in Hlk2. injection Hlk2 as <-.
  rewrite Hst' in Hst2. injection Hst2 as <-.
  destruct (irq_deliver_shape q q' Hdel) as (Hm & _ & _).
  rewrite /seip_free_psail /regs_free_psail Hm. exact (Hfr ag q Hlk Hst).
Qed.

Lemma xseip_free_irq_back i c c' :
  pf_xirq i c c' → xseip_free i c' → xseip_free i c.
Proof.
  intros Hirq Hfr ag q Hlk Hst.
  destruct (pf_xirq_at i c c' Hirq)
    as (ag0 & ag2 & q0 & q2 & Hlk0 & Hst0 & Hlk2 & Hst2 & _ & _ & Hdel).
  rewrite Hlk in Hlk0. injection Hlk0 as <-.
  rewrite Hst in Hst0. injection Hst0 as <-.
  destruct (irq_deliver_shape q q2 Hdel) as (Hm & _ & _).
  rewrite /seip_free_psail /regs_free_psail -Hm. exact (Hfr ag2 q2 Hlk2 Hst2).
Qed.

Lemma xseip_free_irq_rtc_back i c c' :
  rtc (pf_xirq i) c c' → xseip_free i c' → xseip_free i c.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [done|].
  intros Hfr. eapply xseip_free_irq_back; [exact Hxy|by apply IH].
Qed.

Lemma xseip_free_step i c c' :
  (∀ ag q, pc_ags c !! i = Some ag → pa_st ag = PHart q → sp_m q ≠ None) →
  xseip_free i c → pf_xsolo riscv_step i c c' → xseip_free i c'.
Proof.
  intros Hin Hfr (l & Hstep & _ & _) ag' q' Hlk' Hst'.
  destruct (wp_pf_step_agent (pstep_ni_xv6 riscv_step) i l c c' Hstep)
    as (ag & Hlk).
  destruct (wp_pf_step_inv (pstep_ni_xv6 riscv_step) i l c c' ag Hstep Hlk)
    as (st' & ms & Hps & _ & _ & Hags & _).
  rewrite Hags in Hlk'.
  rewrite (lookup_insert_self (pc_ags c) i _ ag Hlk) in Hlk'.
  injection Hlk' as <-. simpl in Hst'. subst st'.
  destruct (pa_st ag) as [q|dd pend] eqn:Hst; [|by destruct Hps].
  simpl in Hps.
  exact (seip_free_res_step riscv_step q l q' (Hin ag q Hlk Hst)
           (Hfr ag q Hlk Hst) Hps).
Qed.

(* ---------------------------------------------------------------- *)
(** *** THE FORWARD COMMUTATION, at [pxv6]

    [WeakSailComplete.irq_commute_step] is the LTS-level core; this is
    its configuration-level packaging, and then the run form: a whole
    chain of pending deliveries commutes past ONE solo step. *)

(** A step that REACHES a boundary leaves no parked fence: the only arm
    that parks one is [Barrier], and it leaves the residual in flight. *)
Lemma sail_step_ni_bnd_fence next p l p' :
  sail_step_ni next p l p' → sp_m p' = None → sp_fence p' = None.
Proof.
  rewrite /sail_step_ni.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|]; [by intros [_ ->] Hm|].
  destruct (sp_m p) as [m|]; [|by intros [_ [tick ->]] Hm].
  rewrite /sail_mstep. destruct m as [y|T oc k]; [by intros [_ ->] Hm|].
  destruct oc; simpl;
    try (by intros [_ ->] Hm);
    try (by intros [_ [ch ->]] Hm);
    try done;
    destruct (dev_addr _); try (by intros [_ ->] Hm).
  - (* MemRead, RAM *)
    intros [_ H].
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data
                  |pr pw sr sw]; try done.
    + destruct lat; [done|].
      destruct H as [(_ & _ & _ & _ & w & _ & ->)
                    |(_ & _ & _ & _ & w & _ & y & rs1 & _ & ->)]; done.
    + by destruct H as (_ & _ & _ & _ & _ & w & m1 & m2 & rs1 & _ & _ & _ & ->).
  - (* MemWrite, RAM *)
    by intros (_ & _ & _ & ->).
Qed.

(** …and its configuration form, which is what the refinement reads off
    the LAST step of a block. *)
Lemma pf_xsolo_bnd_fence i c c' :
  pf_xsolo riscv_step i c c' →
  (∀ ag q, pc_ags c' !! i = Some ag → pa_st ag = PHart q → sp_m q = None) →
  xfence_free i c'.
Proof.
  intros (l & Hstep & _ & _) Hbnd ag' q' Hlk' Hst'.
  have Hm : sp_m q' = None := Hbnd ag' q' Hlk' Hst'.
  destruct (wp_pf_step_agent (pstep_ni_xv6 riscv_step) i l c c' Hstep)
    as (ag & Hlk).
  destruct (wp_pf_step_inv (pstep_ni_xv6 riscv_step) i l c c' ag Hstep Hlk)
    as (st' & ms & Hps & _ & _ & Hags & _).
  rewrite Hags in Hlk'.
  rewrite (lookup_insert_self (pc_ags c) i _ ag Hlk) in Hlk'.
  injection Hlk' as <-. simpl in Hst'. subst st'.
  destruct (pa_st ag) as [q|dd pend]; [|by destruct Hps]. simpl in Hps.
  exact (sail_step_ni_bnd_fence riscv_step q l q' Hps Hm).
Qed.

Lemma pf_xirq_commute_step i c c1 c2 :
  xseip_free i c → pf_xirq i c c1 → pf_xsolo riscv_step i c1 c2 →
  ∃ c1' c2', pf_xsolo riscv_step i c c1' ∧ pf_xirq i c1' c2' ∧
             xcfg_eqv c2 c2'.
Proof.
  intros Hfr (ag & q & q1 & Hlk & Hst & Hdel & ->) (l & Hstep & Hcc & Hrt).
  set (ag1 := WPAgent (PHart q1) (pa_ws ag) (pa_prom ag)).
  have Hlk1 : pc_ags (WPCfg (pc_img c) (pc_log c) (<[i := ag1]> (pc_ags c)))
                !! i = Some ag1
    := lookup_insert_self (pc_ags c) i ag1 ag Hlk.
  destruct (wp_pf_step_inv (pstep_ni_xv6 riscv_step) i l _ c2 ag1 Hstep Hlk1)
    as (st2 & ms & Hps & Himg2 & Hlog2 & Hags2 & Hre).
  simpl in Hps, Himg2, Hlog2, Hags2, Hre.
  destruct st2 as [q2|dd pend]; [|by destruct Hps]. simpl in Hps.
  destruct (irq_commute_step riscv_step q q1 l q2 (Hfr ag q Hlk Hst) Hdel Hps)
    as (q1' & q2' & Hstep1' & Hdel' & Heqv2).
  set (wsp := post_ws l (pa_ws ag) (length (pc_log c))).
  exists (WPCfg (pc_img c) (pc_log c ++ ms)
            (<[i := WPAgent (PHart q1') wsp (pa_prom ag)]> (pc_ags c))),
         (WPCfg (pc_img c) (pc_log c ++ ms)
            (<[i := WPAgent (PHart q2') wsp (pa_prom ag)]> (pc_ags c))).
  split_and!.
  - exists l. split_and!.
    + refine (Hre c ag (PHart q1') Hlk eq_refl eq_refl eq_refl eq_refl _).
      by rewrite Hst.
    + intros ag0 msg Hag0 Heq. simpl in Heq.
      rewrite Hlk in Hag0. injection Hag0 as <-.
      apply app_inv_head in Heq. subst ms.
      exact (Hcc ag1 msg Hlk1 Hlog2).
    + rewrite /xrmw_tight in Hrt |- *. destruct l; try done.
      intros ag0 Hag0. rewrite Hlk in Hag0. injection Hag0 as <-.
      exact (Hrt ag1 Hlk1).
  - exists (WPAgent (PHart q1') wsp (pa_prom ag)), q1', q2'.
    split_and!.
    + simpl. by eapply lookup_insert_self, Hlk.
    + reflexivity.
    + exact Hdel'.
    + by rewrite /= list_insert_insert.
  - have Hc2 : c2 = WPCfg (pc_img c) (pc_log c ++ ms)
                     (<[i := WPAgent (PHart q2) wsp (pa_prom ag)]> (pc_ags c)).
    { destruct c2 as [ci cl ca]; simpl in Himg2, Hlog2, Hags2.
      rewrite Himg2 Hlog2 Hags2 /= list_insert_insert. reflexivity. }
    rewrite Hc2.
    apply (xcfg_eqv_ins c c i _ _ (xcfg_eqv_refl c)); [by exists ag|].
    split_and!; [done|done|]. simpl. exact (psail_eqv_sym _ _ Heqv2).
Qed.

Lemma xirq_run_commute i : ∀ z0 zd, rtc (pf_xirq i) z0 zd →
  ∀ x, xseip_free i z0 → pf_xsolo riscv_step i zd x →
  ∃ z0' xd, pf_xsolo riscv_step i z0 z0' ∧ rtc (pf_xirq i) z0' xd ∧
            xcfg_eqv x xd.
Proof.
  intros z0 zd Hrun. induction Hrun as [z|z z1 zd Hz1 _ IH];
    intros x Hfr Hsolo.
  - exists x, x. split_and!; [exact Hsolo|apply rtc_refl|apply xcfg_eqv_refl].
  - destruct (IH x (xseip_free_irq i z z1 Hz1 Hfr) Hsolo)
      as (z1' & xd1 & Hsolo1 & Hirq1 & Heq1).
    destruct (pf_xirq_commute_step i z z1 z1' Hfr Hz1 Hsolo1)
      as (w1 & w2 & Hsolow & Hirqw & Heqw).
    destruct (pf_xirq_rtc_eqv i z1' w2 xd1 Heqw Hirq1) as (xd2 & Hxd2 & Heq2).
    exists w1, xd2. split_and!;
      [exact Hsolow|by eapply rtc_l|by eapply xcfg_eqv_trans].
Qed.

(** *** (d) The irq split, at the configuration level *)

Lemma pstep_xv6_ni_or_irq next p l p' :
  pstep_xv6 next p l p' →
  pstep_ni_xv6 next p l p' ∨
  (∃ q q', p = PHart q ∧ p' = PHart q' ∧ sp_fence q = None ∧ irq_deliver q l q').
Proof.
  destruct p as [q|d pend]; [|by intros ?; left].
  destruct p' as [q'|d' pend']; [|done].
  simpl. intros Hs.
  destruct (sail_step_irq_or_ni next q l q' Hs) as [[Hf Hirq]|Hni]; [|by left].
  right. by exists q, q'.
Qed.

Lemma pf_step_ni_or_irq next i l (c c' : wpcfg pxv6) :
  wp_pf_step (pstep_xv6 next) i l c c' →
  wp_pf_step (pstep_ni_xv6 next) i l c c' ∨
  (l = WeakPromise.LSilent ∧ xfence_free i c ∧ pf_xirq i c c').
Proof.
  intros Hstep.
  destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kk st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps];
    destruct (pstep_xv6_ni_or_irq next (pa_st ag) _ st' Hps)
      as [Hni|(q & q' & Hq & Hq' & Hf & Hirq)];
    try (by left; econstructor; eauto);
    try (by destruct Hirq as [Hc _]; inversion Hc).
  right. split_and!; [reflexivity| |].
  - intros ag0 q0 Hlk0 Hst0.
    have Ha : ag0 = ag by congruence. subst ag0.
    have Hq0 : q0 = q by congruence. by subst q0.
  - exists ag, q, q'.
    split_and!; [exact Hlk|exact Hq|exact Hirq|by rewrite Hq'].
Qed.

(* ====================================================================== *)
(** ** 10. FULLY SEGMENTED RUNS: the three segment kinds

    [seg2] is ONE of

    (A) [SegHart i c c'] — a contiguous SOLO run of hart [i] over the
        IRQ-FREE LTS ([pf_xsolo], i.e. [pstep_ni_xv6]; every step is
        moreover class-canonical and rmw-tight, both packaged by
        [pf_xsolo]) between two instruction boundaries;
    (B) [SegIrq i c c'] — ONE silent step in which hart [i] consumes the
        head of [sp_irq]; boundary on both sides ([irq_deliver] preserves
        [sp_m] and [sp_fence]);
    (C) [SegDisk i c c'] — a contiguous solo run of the disk agent from
        an empty burst buffer to an empty burst buffer, whose log delta is
        exactly the messages [WeakLang.wmsgs_of_map w] of one
        [WeakLang.wdisk_step] (up to the author stamp — see [dmsgs]). *)

Inductive seg2 :=
| SegHart (i : agent) (c c' : wpcfg pxv6)
| SegIrq  (i : agent) (c c' : wpcfg pxv6)
| SegDisk (i : agent) (c c' : wpcfg pxv6).

Definition seg2_src (s : seg2) : wpcfg pxv6 :=
  match s with SegHart _ c _ | SegIrq _ c _ | SegDisk _ c _ => c end.
Definition seg2_dst (s : seg2) : wpcfg pxv6 :=
  match s with SegHart _ _ c' | SegIrq _ _ c' | SegDisk _ _ c' => c' end.


(** The disk's emitted messages carry the EMITTING AGENT's index as their
    author; [WeakLang.wmsgs_of_map] stamps [WeakLang.n_disk].  At the
    standard agent vector the two coincide ([dmsgs_n_disk]). *)
Definition dmsgs (i : agent) (ns : list wmsg) : list wmsg :=
  (λ m, WMsg (wm_pa m) (wm_data m) (Some i) (wm_ak m)) <$> ns.

Lemma dmsgs_app i ns1 ns2 : dmsgs i (ns1 ++ ns2) = dmsgs i ns1 ++ dmsgs i ns2.
Proof. by rewrite /dmsgs fmap_app. Qed.

Lemma dmsgs_n_disk w : dmsgs n_disk (wmsgs_of_map w) = wmsgs_of_map w.
Proof.
  rewrite /dmsgs /wmsgs_of_map -list_fmap_compose.
  apply list_fmap_ext. by intros k [a b] _.
Qed.

Definition seg2_hart_ok (i : agent) (c c' : wpcfg pxv6) : Prop :=
  (∃ ag q, pc_ags c !! i = Some ag ∧ pa_st ag = PHart q) ∧
  at_pbnd i c ∧ at_pbnd i c' ∧ rtc (xstep i) c c'.

(** A delivery AT A BOUNDARY — the shape [WeakComposeLang]'s lift consumes,
    and (since stage B) the shape the REFINEMENT produces: [seg_build] itself
    keeps every delivery inside the hart segment it interrupts. *)
Definition seg2_irq_ok (i : agent) (c c' : wpcfg pxv6) : Prop :=
  at_pbnd i c ∧ pf_xirq i c c'.

Definition seg2_disk_ok (i : agent) (c c' : wpcfg pxv6) : Prop :=
  ∃ d d' mem w,
    (∃ ag, pc_ags c !! i = Some ag ∧ pa_st ag = PDisk d []) ∧
    (∃ ag', pc_ags c' !! i = Some ag' ∧ pa_st ag' = PDisk d' []) ∧
    rtc (pf_xsolo riscv_step i) c c' ∧
    wdisk_step d mem d' w ∧
    pc_log c' = pc_log c ++ dmsgs i (wmsgs_of_map w).

Definition seg2_ok (s : seg2) : Prop :=
  match s with
  | SegHart i c c' => seg2_hart_ok i c c'
  | SegIrq i c c' => seg2_irq_ok i c c'
  | SegDisk i c c' => seg2_disk_ok i c c'
  end.

Fixpoint chained2 (segs : list seg2) (c cf : wpcfg pxv6) : Prop :=
  match segs with
  | [] => c = cf
  | s :: rest => seg2_src s = c ∧ chained2 rest (seg2_dst s) cf
  end.

Lemma chained2_app segs1 segs2 c c1 cf :
  chained2 segs1 c c1 → chained2 segs2 c1 cf → chained2 (segs1 ++ segs2) c cf.
Proof.
  revert c. induction segs1 as [|s segs IH]; intros c H1 H2; simpl in H1 |- *.
  - by rewrite H1.
  - destruct H1 as (Hs & H1). split; [exact Hs|by apply IH].
Qed.

Lemma seg2_run (s : seg2) :
  seg2_ok s → rtc (wp_pf_run (pstep_xv6 riscv_step)) (seg2_src s) (seg2_dst s).
Proof.
  destruct s as [i c c'|i c c'|i c c']; simpl.
  - intros (_ & _ & _ & Hrun). exact (xstep_rtc_run i c c' Hrun).
  - intros (Hb & Hirq). apply rtc_once.
    eapply pf_xirq_run; [by apply xfence_free_bnd|exact Hirq].
  - intros (?&?&?&?& _ & _ & Hrun & _). exact (pf_xsolo_rtc_run riscv_step i c c' Hrun).
Qed.

Lemma chained2_run segs c cf :
  chained2 segs c cf → Forall seg2_ok segs →
  rtc (wp_pf_run (pstep_xv6 riscv_step)) c cf.
Proof.
  revert c. induction segs as [|s segs IH]; intros c Hch Hall; simpl in Hch.
  { by rewrite Hch. }
  destruct Hch as (Hs & Hch).
  apply list_relations.Forall_cons in Hall as [Hok Hall].
  rewrite -Hs. etrans; [exact (seg2_run s Hok)|by apply IH].
Qed.

(* ---------------------------------------------------------------- *)
(** *** The two OTHER segment kinds transport across [xcfg_eqv]

    (The hart kind does not — its refinement into single blocks is where
    the deliveries are commuted out, and that is [WeakComposeLang]'s.) *)

Lemma at_pbnd_eqv i c d : xcfg_eqv c d → at_pbnd i c → at_pbnd i d.
Proof.
  intros Heq Hb ag' Hlk'.
  destruct (xcfg_eqv_lookup d c i ag' (xcfg_eqv_sym c d Heq) Hlk')
    as (ag & Hlk & (_ & _ & Hst)).
  eapply pxv6_eqv_pbnd; [exact (pxv6_eqv_sym _ _ Hst)|exact (Hb ag Hlk)].
Qed.

Lemma pxv6_eqv_disk dd pend q :
  pxv6_eqv (PDisk dd pend) q → q = PDisk dd pend.
Proof. destruct q as [?|d2 l2]; [done|by intros [-> ->]]. Qed.

Lemma seg2_irq_ok_eqv i c c' d :
  seg2_irq_ok i c c' → xcfg_eqv c d →
  ∃ d', seg2_irq_ok i d d' ∧ xcfg_eqv c' d'.
Proof.
  intros (Hb & Hirq) Heq.
  destruct (pf_xirq_eqv i c d c' Heq Hirq) as (d' & Hd' & Heq').
  exists d'. split; [split; [by eapply at_pbnd_eqv|exact Hd']|exact Heq'].
Qed.

Lemma seg2_disk_ok_eqv i c c' d :
  seg2_disk_ok i c c' → xcfg_eqv c d →
  ∃ d', seg2_disk_ok i d d' ∧ xcfg_eqv c' d'.
Proof.
  intros (dd & dd' & mem & w & (ag & Hlk & Hst) & (ag2 & Hlk2 & Hst2)
          & Hrun & Hws & Hlog) Heq.
  destruct (pf_xsolo_rtc_eqv i c d c' Heq Hrun) as (d' & Hrun' & Heq').
  destruct (xcfg_eqv_lookup c d i ag Heq Hlk) as (agd & Hlkd & (_ & _ & Hsd)).
  destruct (xcfg_eqv_lookup c' d' i ag2 Heq' Hlk2)
    as (agd2 & Hlkd2 & (_ & _ & Hsd2)).
  rewrite Hst in Hsd. rewrite Hst2 in Hsd2.
  exists d'. split; [|exact Heq'].
  exists dd, dd', mem, w. split_and!.
  - exists agd. split; [exact Hlkd|by apply pxv6_eqv_disk].
  - exists agd2. split; [exact Hlkd2|by apply pxv6_eqv_disk].
  - exact Hrun'.
  - exact Hws.
  - destruct Heq as (_ & Hl & _). destruct Heq' as (_ & Hl' & _).
    by rewrite Hl' Hlog Hl.
Qed.

(* ---------------------------------------------------------------- *)
(** *** The disk agent never arms a release ([w_relp] stays [false])

    The disk arm of [pstep_xv6] emits only [LSilent] and [LStore], and a
    store CLEARS [w_relp]; so along any promise-free run of the program
    every disk agent's [w_relp] is [false].  This is what makes the
    canonical class of a disk emit [WCplain] — which is exactly the class
    [WeakLang.wmsgs_of_map] stamps. *)

Lemma w_relp_store_post_bytes_ne ws rl as_ t :
  as_ ≠ [] → w_relp (store_post_bytes ws rl as_ t) = false.
Proof.
  revert ws. induction as_ as [|a as_ IH]; intros ws Hne; [done|].
  destruct as_ as [|b as_]; [done|].
  by apply IH.
Qed.

Lemma w_relp_store_post_run_ne ws rl base n t :
  (0 < n)%nat → w_relp (store_post_run ws rl base n t) = false.
Proof.
  intros Hn. apply w_relp_store_post_bytes_ne.
  destruct n as [|n]; [lia|]. by rewrite /= .
Qed.

Lemma w_relp_ag_store (st' : pxv6) ws rl base n t pr :
  (0 < n)%nat →
  w_relp (pa_ws (WPAgent st' (store_post_run ws rl base n t) pr)) = false.
Proof. apply w_relp_store_post_run_ne. Qed.

Definition disk_relp (c : wpcfg pxv6) : Prop :=
  ∀ j ag dd pend, pc_ags c !! j = Some ag → pa_st ag = PDisk dd pend →
    w_relp (pa_ws ag) = false.

Lemma disk_relp_init img0 ps0 : disk_relp (wp_init img0 ps0).
Proof.
  intros j ag dd pend Hlk _. rewrite /wp_init /= list_lookup_fmap in Hlk.
  destruct (ps0 !! j) as [p|]; simpl in Hlk; [|done]. by injection Hlk as <-.
Qed.

Lemma pstep_xv6_disk_dst next p l dd pend :
  pstep_xv6 next p l (PDisk dd pend) → ∃ d0 p0, p = PDisk d0 p0.
Proof. destruct p as [q|d0 p0]; [by intros []|by eauto]. Qed.

Lemma pstep_xv6_disk_lbl next d0 p0 l p' :
  pstep_xv6 next (PDisk d0 p0) l p' →
  l = WeakPromise.LSilent ∨ ∃ rl base data, l = WeakPromise.LStore rl base data.
Proof.
  destruct p' as [?|d1 p1]; [by intros []|].
  intros [(-> & _)|(m & r & _ & _ & _ & ->)]; [by left|by right; eauto].
Qed.

Lemma disk_relp_step next i l (c c' : wpcfg pxv6) :
  disk_relp c → wp_pf_step (pstep_xv6 next) i l c c' → disk_relp c'.
Proof.
  intros Hdr Hstep.
  destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kk st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps];
    intros j agj dd pend Hlkj Hstj; simpl in Hlkj;
    (destruct (decide (j = i)) as [->|Hne2];
     [rewrite (lookup_insert_self _ _ _ _ Hlk) in Hlkj;
      injection Hlkj as <-; simpl in Hstj; subst st'
     |rewrite (lookup_insert_other _ _ _ _ Hne2) in Hlkj;
      by eapply Hdr]);
    destruct (pstep_xv6_disk_dst next (pa_st ag) _ dd pend Hps)
      as (d0 & p0 & Ha);
    try (by rewrite Ha in Hps;
         destruct (pstep_xv6_disk_lbl next d0 p0 _ _ Hps)
           as [Hc|(? & ? & ? & Hc)]).
  - (* silent *) simpl. by eapply Hdr.
  - (* store *)
    apply w_relp_ag_store. destruct data; [done|]. simpl. lia.
Qed.

Lemma disk_relp_run next (c c' : wpcfg pxv6) :
  disk_relp c → rtc (wp_pf_run (pstep_xv6 next)) c c' → disk_relp c'.
Proof.
  intros Hdr Hrun. induction Hrun as [|x y z (i & l & Hs) _ IH]; [done|].
  apply IH. by eapply disk_relp_step.
Qed.

(* ---------------------------------------------------------------- *)
(** *** The OPEN DISK GROUP invariant

    While the disk agent is inside a group ([pend ≠ []]) the messages it
    has already emitted, followed by what is still buffered, are exactly
    the write set of the ONE [wdisk_step] that opened the group. *)

Definition dopen (i : agent) (c d : wpcfg pxv6) : Prop :=
  ∀ ag dd, pc_ags c !! i = Some ag → pa_st ag = PDisk dd [] →
    ∃ ag' dd' pend ns1 mem w,
      pc_ags d !! i = Some ag' ∧ pa_st ag' = PDisk dd' pend ∧
      wdisk_step dd mem dd' w ∧ wmsgs_of_map w = ns1 ++ pend ∧
      pc_log d = pc_log c ++ dmsgs i ns1.

Lemma dopen_refl i c : dopen i c c.
Proof.
  intros ag dd Hlk Hst. exists ag, dd, [], [], ∅, ∅.
  split_and!; [exact Hlk|exact Hst|apply WDiskStepIdle
              |by rewrite wmsgs_of_map_empty|by rewrite /dmsgs /= app_nil_r].
Qed.

Lemma dopen_step i (c d d2 : wpcfg pxv6) :
  disk_relp d → dopen i c d →
  (∀ ag, pc_ags d !! i = Some ag → ¬ pbnd (pa_st ag)) →
  pf_xsolo riscv_step i d d2 → dopen i c d2.
Proof.
  intros Hdr Hdo Hnb (l & Hstep & Hcls & _) ag dd Hlk Hst.
  destruct (Hdo ag dd Hlk Hst)
    as (ag' & dd' & pend & ns1 & mem & w & Hlk' & Hst' & Hws & Hsplit' & Hlog').
  have Hpne : pend ≠ [].
  { intros ->. apply (Hnb ag' Hlk'). by rewrite Hst'. }
  destruct Hstep as
    [cfg ag0 st' Hlk0 Hps
    |cfg ag0 aq lat base tvs st' Hlk0 Hps Hr
    |cfg ag0 rl base data kk st' Hlk0 Hps Hne
    |cfg ag0 aq rl base tvs data kk st' Hlk0 Hps Hne Hlen Hr He
    |cfg ag0 pr pw sr sw st' Hlk0 Hps];
    rewrite Hlk' in Hlk0; injection Hlk0 as <-;
    (have Hpsx := pstep_ni_xv6_step _ _ _ _ Hps; rewrite Hst' in Hpsx);
    try (by destruct (pstep_xv6_disk_lbl riscv_step dd' pend _ _ Hpsx)
           as [Hc|(? & ? & ? & Hc)]).
  - (* a stutter inside the group *)
    destruct st' as [?|d1 p1]; [by destruct Hpsx|].
    destruct Hpsx as [(_ & [(-> & ->)|(Hpe & _)])|(? & ? & _ & _ & _ & Hc)];
      [|by destruct (Hpne Hpe)|done].
    exists (WPAgent (PDisk dd' pend) (pa_ws ag') (pa_prom ag')),
      dd', pend, ns1, mem, w.
    split_and!; [by eapply lookup_insert_self, Hlk'|done|exact Hws
                |exact Hsplit'|exact Hlog'].
  - (* one EMIT: the head of the buffer becomes this agent's own store *)
    destruct st' as [?|d1 p1]; [by destruct Hpsx|].
    destruct Hpsx as [(Hc & _)|(m & rest & Hpe & -> & -> & Hlbl)]; [done|].
    injection Hlbl as -> -> ->.
    have Hmem : m ∈ wmsgs_of_map w
      by rewrite Hsplit' Hpe elem_of_app; right; apply elem_of_list_here.
    have Hak : wm_ak m = WCplain by apply (wmsgs_of_map_plain w m Hmem).
    have Hrelp : w_relp (pa_ws ag') = false
      by apply (Hdr i ag' dd' pend Hlk' Hst').
    have Hkk : kk = WCplain.
    { have Hx := Hcls ag' (WMsg (wm_pa m) (wm_data m) (Some i) kk) Hlk' eq_refl.
      simpl in Hx. rewrite /lbl_class Hrelp /= in Hx. exact Hx. }
    subst kk.
    eexists _, dd', rest, (ns1 ++ [m]), mem, w.
    split_and!; [by eapply lookup_insert_self, Hlk'|done|exact Hws| |].
    + by rewrite Hsplit' Hpe -app_assoc.
    + simpl. rewrite Hlog' dmsgs_app -app_assoc /dmsgs /=. by rewrite Hak.
Qed.


(* ---------------------------------------------------------------- *)
(** *** Closing a disk group, and "has this agent finished?" *)

Lemma dopen_close i (c d : wpcfg pxv6) ag dd :
  dopen i c d → pc_ags c !! i = Some ag → pa_st ag = PDisk dd [] →
  at_pbnd i d → rtc (pf_xsolo riscv_step i) c d → seg2_disk_ok i c d.
Proof.
  intros Hdo Hlk Hst Hbnd Hrun.
  destruct (Hdo ag dd Hlk Hst)
    as (ag' & dd' & pend & ns1 & mem & w & Hlk' & Hst' & Hws & Hsp & Hlog).
  have Hpe : pend = [].
  { have Hb := Hbnd ag' Hlk'. rewrite Hst' in Hb. exact Hb. }
  subst pend. rewrite app_nil_r in Hsp.
  exists dd, dd', mem, w. split_and!;
    [by exists ag|by exists ag'|exact Hrun|exact Hws|].
  by rewrite Hlog Hsp.
Qed.

(** [unfin order n j]: agent [j] still has an event at position [n] or
    later.  (Decidable: membership in a list of [nat].) *)
Definition unfin (order : list gev) (n j : nat) : Prop :=
  j ∈ (drop n order).*1.

Global Instance unfin_dec order n j : Decision (unfin order n j).
Proof. rewrite /unfin. apply _. Defined.

Lemma unfin_here order n j e :
  order !! n = Some e → e.1 = j → unfin order n j.
Proof.
  intros Hn <-. rewrite /unfin (drop_S order e n Hn) /=.
  apply elem_of_list_here.
Qed.

Lemma unfin_S order n j : unfin order (S n) j → unfin order n j.
Proof.
  rewrite /unfin. intros Hin.
  destruct (order !! n) as [e|] eqn:Hn.
  - rewrite (drop_S order e n Hn) /=. by apply elem_of_list_further.
  - rewrite (drop_ge order n); [|by apply lookup_ge_None in Hn; lia].
    rewrite (drop_ge order (S n)) in Hin; [done|].
    apply lookup_ge_None in Hn. lia.
Qed.

Lemma unfin_split order n j e :
  order !! n = Some e → unfin order n j → e.1 ≠ j → unfin order (S n) j.
Proof.
  intros Hn Hin Hne. rewrite /unfin (drop_S order e n Hn) /= in Hin.
  apply elem_of_cons in Hin as [->|Hin]; [by destruct (Hne eq_refl)|exact Hin].
Qed.

Lemma nproc_app (l1 l2 : list gev) j :
  nproc (l1 ++ l2) j = (nproc l1 j + nproc l2 j)%nat.
Proof. by rewrite /nproc list_basics.filter_app length_app. Qed.

Lemma nproc_pos_of_unfin order n j :
  unfin order n j → (0 < nproc (drop n order) j)%nat.
Proof.
  rewrite /unfin /nproc. intros Hin.
  apply elem_of_list_fmap in Hin as (e & He & Hein).
  destruct (filter (λ e : gev, e.1 = j) (drop n order)) as [|x xs] eqn:Hf;
    [|simpl; lia].
  exfalso.
  have Hx : e ∈ filter (λ e : gev, e.1 = j) (drop n order)
    by apply elem_of_list_filter; split; [by rewrite He|exact Hein].
  rewrite Hf in Hx. by apply elem_of_nil in Hx.
Qed.

Lemma unfin_le order n m j : (n ≤ m)%nat → unfin order m j → unfin order n j.
Proof.
  intros Hle. induction m as [|m IH]; intros Hin.
  - have -> : n = 0%nat by lia. exact Hin.
  - destruct (decide (n = S m)) as [->|Hne]; [exact Hin|].
    apply IH; [lia|]. by apply unfin_S.
Qed.

Lemma nproc_zero_of_not_unfin order n j :
  ¬ unfin order n j → nproc (drop n order) j = 0%nat.
Proof.
  intros Hnf. destruct (nproc (drop n order) j) as [|k] eqn:Hk; [done|].
  exfalso. apply Hnf. rewrite /unfin.
  have Hlen : (0 < length (filter (λ e : gev, e.1 = j) (drop n order)))%nat
    by rewrite /nproc in Hk; lia.
  destruct (filter (λ e : gev, e.1 = j) (drop n order)) as [|x xs] eqn:Hf;
    [simpl in Hlen; lia|].
  have Hx : x ∈ filter (λ e : gev, e.1 = j) (drop n order)
    by rewrite Hf; apply elem_of_list_here.
  apply elem_of_list_filter in Hx as (Hx1 & Hx2).
  apply elem_of_list_fmap. by exists x.
Qed.

Lemma dopen_start i (d d2 : wpcfg pxv6) :
  at_pbnd i d → pf_xsolo riscv_step i d d2 → dopen i d d2.
Proof.
  intros Hbd (l & Hstep & _ & _) ag dd Hlk Hst.
  destruct Hstep as
    [cfg ag0 st' Hlk0 Hps
    |cfg ag0 aq lat base tvs st' Hlk0 Hps Hr
    |cfg ag0 rl base data kk st' Hlk0 Hps Hne
    |cfg ag0 aq rl base tvs data kk st' Hlk0 Hps Hne Hlen Hr He
    |cfg ag0 pr pw sr sw st' Hlk0 Hps];
    rewrite Hlk in Hlk0; injection Hlk0 as <-;
    (have Hpsx := pstep_ni_xv6_step _ _ _ _ Hps; rewrite Hst in Hpsx);
    try (by destruct (pstep_xv6_disk_lbl riscv_step dd [] _ _ Hpsx)
           as [Hc|(? & ? & ? & Hc)]).
  - destruct st' as [?|d1 p1]; [by destruct Hpsx|].
    destruct Hpsx as [(_ & [(-> & ->)|(_ & mem & w & Hws & ->)])
                     |(? & ? & Hc & _)]; [| |done].
    + exists (WPAgent (PDisk dd []) (pa_ws ag) (pa_prom ag)), dd, [], [], ∅, ∅.
      split_and!; [by eapply lookup_insert_self, Hlk|done|apply WDiskStepIdle
                  |by rewrite wmsgs_of_map_empty|by rewrite /dmsgs /= app_nil_r].
    + exists (WPAgent (PDisk d1 (wmsgs_of_map w)) (pa_ws ag) (pa_prom ag)),
        d1, (wmsgs_of_map w), [], mem, w.
      split_and!; [by eapply lookup_insert_self, Hlk|done|exact Hws|done
                  |by rewrite /dmsgs /= app_nil_r].
  - (* an emit needs a nonempty buffer *)
    exfalso. destruct st' as [?|d1 p1]; [by destruct Hpsx|].
    by destruct Hpsx as [(Hc & _)|(? & ? & Hc & _)].
Qed.

Lemma dopen_hart i dstart d d3 agx q :
  dopen i dstart d → pc_ags d !! i = Some agx → pa_st agx = PHart q →
  dopen i dstart d3.
Proof.
  intros Hdo Hlk Hst ag dd Hlk0 Hst0. exfalso.
  destruct (Hdo ag dd Hlk0 Hst0)
    as (ag' & dd' & pend & ns1 & mem & w & Hlk' & Hst' & _).
  rewrite Hlk in Hlk'. injection Hlk' as <-. by rewrite Hst in Hst'.
Qed.

(* ====================================================================== *)
(** ** 11. THE PACKAGED THEOREMS

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
             | Some m => sail_shaped m ∧ sail_live m
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
        rewrite Hm in Hr. destruct Hr as (Hsh & Hlv).
        destruct (xtail_complete riscv_step b2.1 cmid agr qr mr
                    ltac:(by rewrite Hcimg) Hbndm Hlkr2 Hstr Hm Hsh Hlv)
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


  (* ================================================================== *)
  (** ** 12. THE FULL SEGMENTATION (stage B5a)

      Two further premises, and nothing else. *)

  (** (B5a-1) an interrupt DELIVERY is either at an instruction boundary
      or its RESIDUAL never touches the pin ([WeakSailComplete] §9's
      [seip_free]).  Stage B's coverage fix: the old premise [Hirqb]
      demanded the boundary outright, which EXCLUDED the behaviors real
      hardware produces (SEIP is asserted mid-instruction); this one only
      constrains what the interrupted residual may do, and a mid-block
      delivery is COMMUTED FORWARD to the block's end. *)
  Context (Hseip : ∀ i T k ag ag' q q' l,
             pt_trs TS !! i = Some T →
             at_ags T !! k = Some ag → at_ags T !! S k = Some ag' →
             pa_st ag = PHart q → pa_st ag' = PHart q' →
             irq_deliver q l q' → ¬ pbnd (PHart q) → seip_free_psail q).

  (** (B5a-2) every logged message carries the class its own author's
      pre-state computes ([WeakSailLTS2.lbl_class]). *)
  Context (Hcls : ∀ i T k ev ag ts m,
             pt_trs TS !! i = Some T →
             at_evs T !! k = Some ev → at_ags T !! k = Some ag →
             ae_ts ev = Some ts → pt_log TS !! (ts - 1)%nat = Some m →
             wm_ak m = lbl_class (ae_lb ev) (pa_ws ag)).

  (** The replay's σ-retimed [wstate] and the trace's own agree on
      [w_relp] — the only component [lbl_class] reads. *)
  Lemma chain_ws_relp (i : agent) (T : atrace pxv6) (k : nat) agk σ :
    pt_trs TS !! i = Some T → at_ags T !! k = Some agk →
    w_relp (aevs_post σ (take k (at_evs T)) ws_init) = w_relp (pa_ws agk).
  Proof.
    intros HT Hk.
    have Hatr := Hwf i T HT.
    destruct (atrace_first_is_Some (pstep_xv6 riscv_step) (pt_img TS)
                (pt_log TS) i T Hatr) as [ag0 H0].
    have Hfold := asteps_ws_fold (pstep_xv6 riscv_step) (pt_img TS) (pt_log TS)
                    i (at_ags T) (at_evs T) k ag0 agk Hatr H0 Hk.
    rewrite Hfold (Hwsi i T ag0 HT H0). by apply w_relp_aevs_post.
  Qed.

  (** A pf step that appends to the log carries a WRITING label. *)
  Lemma pf_step_writes (i : agent) l (c c' : wpcfg pxv6) msg :
    wp_pf_step (pstep_xv6 riscv_step) i l c c' →
    pc_log c' = pc_log c ++ [msg] → lb_writes l = true.
  Proof.
    intros Hstep Hlog.
    destruct Hstep as
      [cfg ag st' Hlk Hps
      |cfg ag aq lat base tvs st' Hlk Hps Hr
      |cfg ag rl base data kk st' Hlk Hps Hne
      |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
      |cfg ag pr pw sr sw st' Hlk Hps]; try done;
      by destruct (app_snoc_absurd _ _ Hlog).
  Qed.

  Lemma pf_step_pstep (i : agent) l (c c' : wpcfg pxv6) ag :
    wp_pf_step (pstep_xv6 riscv_step) i l c c' → pc_ags c !! i = Some ag →
    ∃ st', pstep_xv6 riscv_step (pa_st ag) l st'.
  Proof.
    intros Hstep Hlk.
    destruct Hstep as
      [cfg ag0 st' Hlk0 Hps
      |cfg ag0 aq lat base tvs st' Hlk0 Hps Hr
      |cfg ag0 rl base data kk st' Hlk0 Hps Hne
      |cfg ag0 aq rl base tvs data kk st' Hlk0 Hps Hne Hlen Hr He
      |cfg ag0 pr pw sr sw st' Hlk0 Hps];
      rewrite Hlk0 in Hlk; injection Hlk as <-; by exists st'.
  Qed.

  (** THE CLASS TRANSFER at a replayed chain step. *)
  Lemma chain_cls (order : list gev) n (e : gev) (T : atrace pxv6) ev
      (c c' : wpcfg pxv6) l ag :
    order !! n = Some e →
    nproc (take n order) e.1 = e.2 →
    qcfg (pstep_xv6 riscv_step) TS img ps (take n order) c →
    qcfg (pstep_xv6 riscv_step) TS img ps (take (S n) order) c' →
    pt_trs TS !! e.1 = Some T → at_evs T !! e.2 = Some ev →
    pc_ags c !! e.1 = Some ag →
    wp_pf_step (pstep_xv6 riscv_step) e.1 l c c' →
    xcls_canon e.1 l c c'.
  Proof.
    intros Hn Hnp Hqc Hqc' HT Hev Hlk Hstep ag2 msg Hag2 Hlogeq.
    rewrite Hlk in Hag2. injection Hag2 as <-.
    have Hwl : lb_writes l = true by eapply pf_step_writes.
    destruct Hqc as (_ & Hcimg & Hclog & _ & Hcags).
    destruct Hqc' as (_ & _ & Hclog' & _ & _).
    have Htk : take (S n) order = take n order ++ [e] by apply take_S_r.
    rewrite Htk in Hclog'.
    have Hgev : gev_ev TS e = Some ev by rewrite /gev_ev HT /=.
    have Hatr := Hwf e.1 T HT.
    have [ag1 Hag1] : is_Some (at_ags T !! e.2).
    { apply lookup_lt_is_Some_2. destruct Hatr as [Hlen _].
      apply lookup_lt_Some in Hev. lia. }
    destruct (asteps_wf_step (pstep_xv6 riscv_step) (pt_img TS) (pt_log TS)
                e.1 (at_ags T) (at_evs T) e.2 ev Hatr Hev)
      as (a1 & a2 & st' & f & Ha1 & Ha2 & Hps & Hok & Heq2).
    have Ha1e : a1 = ag1 by congruence. subst a1.
    (* the config's record IS the trace's, retimed *)
    destruct (Hcags e.1 T HT) as (agn & Hagn & Hclk).
    rewrite Hnp Hag1 in Hagn. injection Hagn as <-. rewrite Hnp in Hclk.
    rewrite Hlk in Hclk. injection Hclk as Hclk.
    (* the appended message is the trace's own *)
    destruct (gev_ts TS e) as [ts|] eqn:Hts.
    - have Hlogc' : pc_log c' = pc_log c ++ [msg_at TS ts].
      { rewrite Hclog' Hclog /pf_log (fl_app_some TS (take n order) e ts Hts)
                fmap_app /=. done. }
      rewrite Hlogeq in Hlogc'. apply app_inv_head in Hlogc'.
      injection Hlogc' as ->.
      have Haets : ae_ts ev = Some ts
        by rewrite /gev_ts Hgev /= in Hts.
      have Hm : ∃ m0, pt_log TS !! (ts - 1)%nat = Some m0 ∧ msg_at TS ts = m0.
      { rewrite /astep_ok Haets in Hok.
        destruct (ae_lb ev) as [|aq lat base tvs|rl base data
                               |aq rl base tvs data|pr pw sr sw];
          [by destruct Hok as (_ & Hc)|by destruct Hok as (_ & _ & Hc)| | |
           by destruct Hok as (_ & Hc)].
        - destruct Hok as (ts' & kc & _ & Hlog0 & _ & _ & Hts').
          injection Hts' as <-. exists (WMsg base data (Some e.1) kc).
          split; [exact Hlog0|by rewrite /msg_at Hlog0].
        - destruct Hok as (ts' & kc & _ & _ & Hlog0 & _ & _ & _ & _ & Hts').
          injection Hts' as <-. exists (WMsg base data (Some e.1) kc).
          split; [exact Hlog0|by rewrite /msg_at Hlog0]. }
      destruct Hm as (m0 & Hlog0 & Hmsg). rewrite Hmsg.
      rewrite (Hcls e.1 T e.2 ev ag1 ts m0 HT Hev Hag1 Haets Hlog0).
      have Hstag : pa_st ag = pa_st ag1 by rewrite Hclk.
      have Hwsag : pa_ws ag
                   = aevs_post (pi TS (take n order)) (take e.2 (at_evs T))
                       ws_init by rewrite Hclk.
      have Hrelp : w_relp (pa_ws ag) = w_relp (pa_ws ag1).
      { rewrite Hwsag. by apply (chain_ws_relp e.1 T e.2 ag1). }
      rewrite (lbl_class_relp (ae_lb ev) (pa_ws ag1) (pa_ws ag)
                 (eq_sym Hrelp)).
      (* and the two labels compute the same class *)
      destruct (pf_step_pstep e.1 l c c' ag Hstep Hlk) as (stp & Hpsc).
      symmetry.
      apply (pxv6_class_det riscv_step (pa_st ag) l stp (ae_lb ev) st');
        [exact Hpsc| |exact Hwl|].
      + rewrite Hstag. exact Hps.
      + destruct (lb_writes (ae_lb ev)) eqn:Hw; [done|].
        exfalso. rewrite (lb_writes_ts_none _ _ _ _ _ _ _ Hok Hw) in Haets.
        done.
    - exfalso.
      have Hlogc' : pc_log c' = pc_log c.
      { rewrite Hclog' Hclog /pf_log (fl_app_none TS (take n order) e Hts).
        done. }
      rewrite Hlogeq in Hlogc'. by destruct (app_snoc_absurd _ _ (eq_sym Hlogc')).
  Qed.


  (* ---------------------------------------------------------------- *)
  (** *** Prefix bookkeeping on the order *)

  Lemma nodup_take (order : list gev) n : NoDup order → NoDup (take n order).
  Proof.
    intros Hnd. rewrite -(take_drop n order) in Hnd.
    by apply list_relations.NoDup_app in Hnd as (H & _ & _).
  Qed.

  Lemma take_dc (order : list gev) (b2 : gev) n
      (Hmem : ∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2)))
      (Hpred : ∀ n0 y, order !! n0 = Some y → ∀ x, gdep2 TS x y → gev_wf TS x →
         ∃ i, (i < n0)%nat ∧ order !! i = Some x) :
    ∀ j k k', (k' < k)%nat → (j, k) ∈ take n order → (j, k') ∈ take n order.
  Proof.
    intros j k k' Hlt Hin.
    apply elem_of_list_lookup in Hin as (p & Hp).
    have Hpn : (p < n)%nat.
    { apply lookup_lt_Some in Hp. rewrite length_take in Hp. lia. }
    have Hpo : order !! p = Some (j, k) by rewrite -Hp lookup_take.
    have Hwfk : gev_wf TS (j, k)
      by apply Hmem, elem_of_list_lookup; by exists p.
    have Hwfk' : gev_wf TS (j, k').
    { apply gev_wf_bounds. apply gev_wf_bounds in Hwfk as (T & HT & Hb).
      exists T. simpl in HT, Hb |- *. split; [done|lia]. }
    have Hd : gdep2 TS (j, k') (j, k)
      by apply gpo_gdep2; split_and!; [done|simpl;lia|done|done].
    destruct (Hpred p (j, k) Hpo (j, k') Hd Hwfk') as (i0 & Hi0 & Hlk0).
    apply elem_of_list_lookup. exists i0. rewrite lookup_take; [exact Hlk0|lia].
  Qed.

  Lemma nproc_take_cur (order : list gev) (b2 : gev) n e
      (Hmem : ∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2)))
      (Hnd : NoDup order)
      (Hpred : ∀ n0 y, order !! n0 = Some y → ∀ x, gdep2 TS x y → gev_wf TS x →
         ∃ i, (i < n0)%nat ∧ order !! i = Some x) :
    order !! n = Some e → nproc (take n order) e.1 = e.2.
  Proof.
    intros He.
    have Hmemj := nproc_mem (take n order) e.1 (nodup_take order n Hnd)
                    (take_dc order b2 n Hmem Hpred e.1).
    have Hnin : e ∉ take n order.
    { intros Hin. apply elem_of_list_lookup in Hin as (p & Hp).
      have Hpn : (p < n)%nat.
      { apply lookup_lt_Some in Hp. rewrite length_take in Hp. lia. }
      have Hpo : order !! p = Some e by rewrite -Hp lookup_take.
      have := NoDup_lookup order p n e Hnd Hpo He. lia. }
    have Hle : (nproc (take n order) e.1 ≤ e.2)%nat.
    { destruct (decide (e.2 < nproc (take n order) e.1)%nat) as [Hlt|?]; [|lia].
      exfalso. apply Hnin. have Hx := proj2 (Hmemj e.2) Hlt.
      by destruct e. }
    have Hge : (e.2 ≤ nproc (take n order) e.1)%nat.
    { destruct e as [j k]. simpl in Hle |- *.
      destruct k as [|k]; [lia|].
      have Hwfk : gev_wf TS (j, S k)
        by apply Hmem, elem_of_list_lookup; by exists n.
      have Hwfk' : gev_wf TS (j, k).
      { apply gev_wf_bounds. apply gev_wf_bounds in Hwfk as (T & HT & Hb).
        exists T. simpl in HT, Hb |- *. split; [done|lia]. }
      have Hd : gdep2 TS (j, k) (j, S k)
        by apply gpo_gdep2; split_and!; [done|simpl;lia|done|done].
      destruct (Hpred n (j, S k) He (j, k) Hd Hwfk') as (i0 & Hi0 & Hlk0).
      have Hin : (j, k) ∈ take n order.
      { apply elem_of_list_lookup. exists i0.
        rewrite lookup_take; [exact Hlk0|lia]. }
      have Hx := proj1 (Hmemj k) Hin. simpl in Hx. lia. }
    lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** An OPEN segment, and how it is closed *)

  (** The open segment: a MIXED run ([xstep]) of the one agent, its disk
      group still accounted for, and — for a DISK segment, which cannot
      contain a delivery — the pure solo run [seg2_disk_ok] wants. *)
  Definition seg_run (i : agent) (dstart d : wpcfg pxv6) : Prop :=
    is_Some (pc_ags dstart !! i) ∧ at_pbnd i dstart ∧
    rtc (xstep i) dstart d ∧ dopen i dstart d ∧
    (∀ ag dd, pc_ags dstart !! i = Some ag → pa_st ag = PDisk dd [] →
       rtc (pf_xsolo riscv_step i) dstart d).

  Lemma seg_run_refl i d : is_Some (pc_ags d !! i) → at_pbnd i d →
    seg_run i d d.
  Proof.
    intros Hs Hb. split_and!;
      [exact Hs|exact Hb|apply rtc_refl|apply dopen_refl|by intros].
  Qed.

  (** A DISK segment is delivery-free by species: the delivery arm needs a
      [PHart], and [dopen] already refutes a hart where a disk started. *)
  Lemma dsolo_hart i dstart d d' ag q :
    dopen i dstart d → pc_ags d !! i = Some ag → pa_st ag = PHart q →
    ∀ ag0 dd, pc_ags dstart !! i = Some ag0 → pa_st ag0 = PDisk dd [] →
      rtc (pf_xsolo riscv_step i) dstart d'.
  Proof.
    intros Hdo Hlk Hst ag0 dd Hlk0 Hst0. exfalso.
    destruct (Hdo ag0 dd Hlk0 Hst0)
      as (ag' & dd' & pend & ns1 & mem & w & Hlk' & Hst' & _).
    rewrite Hlk in Hlk'. injection Hlk' as <-. by rewrite Hst in Hst'.
  Qed.

  Lemma seg_run_step i dstart d d2 :
    disk_relp d → seg_run i dstart d →
    (∀ ag, pc_ags d !! i = Some ag → ¬ pbnd (pa_st ag)) →
    xstep i d d2 → seg_run i dstart d2.
  Proof.
    intros Hdr (Hs & Hb & Hrun & Hdo & Hds) Hnb Hstep.
    have Hrun2 : rtc (xstep i) dstart d2 by eapply rtc_r.
    destruct Hstep as [Hsolo|(_ & _ & Hirq)].
    - split_and!; [exact Hs|exact Hb|exact Hrun2|by eapply dopen_step|].
      intros ag0 dd Hlk0 Hst0.
      eapply rtc_r; [by eapply Hds|exact Hsolo].
    - destruct (pf_xirq_at i d d2 Hirq) as (ag & _ & q & _ & Hlk & Hst & _).
      split_and!; [exact Hs|exact Hb|exact Hrun2|by eapply dopen_hart|].
      by eapply dsolo_hart.
  Qed.

  Lemma seg_run_start i d d2 :
    is_Some (pc_ags d !! i) → at_pbnd i d → xstep i d d2 → seg_run i d d2.
  Proof.
    intros Hs Hb Hstep.
    have Hrun : rtc (xstep i) d d2 by apply rtc_once.
    destruct Hstep as [Hsolo|(_ & _ & Hirq)].
    - split_and!; [exact Hs|exact Hb|exact Hrun|by eapply dopen_start|].
      intros ag0 dd Hlk0 Hst0. by apply rtc_once.
    - destruct (pf_xirq_at i d d2 Hirq) as (ag & _ & q & _ & Hlk & Hst & _).
      split_and!; [exact Hs|exact Hb|exact Hrun| |].
      + eapply dopen_hart; [apply dopen_refl|exact Hlk|exact Hst].
      + eapply (dsolo_hart i d d d2 ag q); [apply dopen_refl|exact Hlk|exact Hst].
  Qed.

  Lemma seg_close (i : agent) (dstart d : wpcfg pxv6) :
    seg_run i dstart d → at_pbnd i d →
    ∃ s, seg2_src s = dstart ∧ seg2_dst s = d ∧ seg2_ok s.
  Proof.
    intros (Hsome & Hbs & Hrun & Hdo & Hds) Hbd.
    destruct Hsome as [ag Hag].
    have Hpb := Hbs ag Hag.
    destruct (pa_st ag) as [q|dd pend] eqn:Hst.
    - exists (SegHart i dstart d). split_and!; [done|done|].
      split_and!; [by exists ag, q|exact Hbs|exact Hbd|exact Hrun].
    - try (rewrite Hst in Hpb). simpl in Hpb. subst pend.
      exists (SegDisk i dstart d). split_and!; [done|done|].
      eapply dopen_close; [exact Hdo|exact Hag|exact Hst|exact Hbd|].
      by eapply Hds.
  Qed.


  (* ---------------------------------------------------------------- *)
  (** *** THE SEGMENTATION INVARIANT and its induction *)

  Definition seg_inv (order : list gev) (n : nat) (c : wpcfg pxv6) : Prop :=
    ∃ segs dstart d op,
      chained2 segs (wp_init img ps) dstart ∧ Forall seg2_ok segs ∧
      rtc (wp_pf_run (pstep_xv6 riscv_step)) (wp_init img ps) d ∧
      (match op with
       | None => d = dstart
       | Some i => seg_run i dstart d ∧
                   (∀ ag, pc_ags d !! i = Some ag → ¬ pbnd (pa_st ag)) ∧
                   (∀ e, order !! n = Some e → e.1 = i) ∧
                   (∃ e, order !! (n - 1)%nat = Some e ∧ e.1 = i) ∧
                   pc_ags d !! i = pc_ags c !! i
       end) ∧
      pc_log d = pc_log c ∧ pc_img d = pc_img c ∧
      length (pc_ags d) = length (pc_ags c) ∧
      (∀ j, unfin order n j → pc_ags d !! j = pc_ags c !! j) ∧
      (∀ j ag, op ≠ Some j → pc_ags d !! j = Some ag → pbnd (pa_st ag)) ∧
      (∀ j a, (obs_flr c j a ≤ obs_flr d j a)%nat).

  Lemma seg_inv_intro (order : list gev) (n : nat) (c : wpcfg pxv6)
      segs dstart d op :
    chained2 segs (wp_init img ps) dstart →
    Forall seg2_ok segs →
    rtc (wp_pf_run (pstep_xv6 riscv_step)) (wp_init img ps) d →
    (match op with
     | None => d = dstart
     | Some i => seg_run i dstart d ∧
                 (∀ ag, pc_ags d !! i = Some ag → ¬ pbnd (pa_st ag)) ∧
                 (∀ e, order !! n = Some e → e.1 = i) ∧
                 (∃ e, order !! (n - 1)%nat = Some e ∧ e.1 = i) ∧
                 pc_ags d !! i = pc_ags c !! i
     end) →
    pc_log d = pc_log c →
    pc_img d = pc_img c →
    length (pc_ags d) = length (pc_ags c) →
    (∀ j, unfin order n j → pc_ags d !! j = pc_ags c !! j) →
    (∀ j ag, op ≠ Some j → pc_ags d !! j = Some ag → pbnd (pa_st ag)) →
    (∀ j a, (obs_flr c j a ≤ obs_flr d j a)%nat) →
    seg_inv order n c.
  Proof. intros. by exists segs, dstart, d, op. Qed.

  Lemma seg_build (order : list gev) (cfs : list (wpcfg pxv6)) (b2 : gev) :
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2))) →
    NoDup order →
    order !! (length order - 1)%nat = Some b2 →
    (∀ n y, order !! n = Some y → ∀ x, gdep2 TS x y → gev_wf TS x →
       ∃ i0, (i0 < n)%nat ∧ order !! i0 = Some x) →
    (∀ i0 j k x y z, (i0 < j)%nat → (j < k)%nat →
       order !! i0 = Some x → order !! j = Some y → order !! k = Some z →
       bid TS pbnd x = bid TS pbnd z → bid TS pbnd y = bid TS pbnd x) →
    length cfs = S (length order) →
    cfs !! 0%nat = Some (wp_init img ps) →
    (∀ n e c c', order !! n = Some e → cfs !! n = Some c →
       cfs !! S n = Some c' → cstep (pstep_xv6 riscv_step) e.1 c c') →
    (∀ n c, cfs !! n = Some c →
       qcfg (pstep_xv6 riscv_step) TS img ps (take n order) c) →
    ∀ n, (n ≤ length order)%nat → ∀ c, cfs !! n = Some c → seg_inv order n c.
  Proof.
    intros Hmem Hnd Hlast Hpred Hcontig Hlenc Hcfs0 Hstepc Hqcp.
    induction n as [|n IH]; intros Hle c Hc.
    { rewrite Hcfs0 in Hc. injection Hc as <-.
      apply (seg_inv_intro order 0%nat (wp_init img ps) []
               (wp_init img ps) (wp_init img ps) None);
        [done|constructor|apply rtc_refl|done|done|done|done|by intros| |by intros].
      intros j ag _ Hlk. rewrite /wp_init /= list_lookup_fmap in Hlk.
      destruct (ps !! j) as [p|] eqn:Hp; simpl in Hlk; [|done].
      injection Hlk as <-. simpl. by eapply Hps_bnd. }
    (* ---- the position being processed ---- *)
    have Hnlt : (n < length order)%nat by lia.
    have [e He] : is_Some (order !! n) by apply lookup_lt_is_Some_2.
    have [c0 Hc0] : is_Some (cfs !! n) by (apply lookup_lt_is_Some_2; lia).
    destruct (IH ltac:(lia) c0 Hc0)
      as (segs & dstart & d & op & Hch & Hall & Hrun & Hop & Hlogd & Himgd
          & Hlend & Hfr & Hbdd & Hobs).
    destruct (Hstepc n e c0 c He Hc0 Hc) as ((l & Hst0) & _).
    have Hwfe : gev_wf TS e
      by (apply Hmem, elem_of_list_lookup; by exists n).
    destruct (proj1 (gev_wf_bounds TS e) Hwfe) as (T & HT & Hklt).
    have [ev Hev] : is_Some (at_evs T !! e.2) by apply lookup_lt_is_Some_2.
    have Hnp : nproc (take n order) e.1 = e.2
      by exact (nproc_take_cur order b2 n e Hmem Hnd Hpred He).
    have Hnp1 : nproc (take (S n) order) e.1 = S e.2.
    { rewrite (take_S_r order n e He) (nproc_app_eq (take n order) e).
      by rewrite Hnp. }
    have Hqc0 := Hqcp n c0 Hc0. have Hqc1 := Hqcp (S n) c Hc.
    have Hqc0' := Hqc0.
    destruct Hqc0' as (_ & Himg0 & Hlog0 & Hlen0 & Hags0).
    have Hqc1' := Hqc1.
    destruct Hqc1' as (_ & Himg1 & Hlog1 & Hlen1 & Hags1).
    destruct (Hags0 e.1 T HT) as (agn & Hagn & Hclk0).
    rewrite Hnp in Hagn Hclk0.
    destruct (Hags1 e.1 T HT) as (agn1 & Hagn1 & Hclk1).
    rewrite Hnp1 in Hagn1 Hclk1.
    have Hunf : unfin order n e.1 by (eapply unfin_here; [exact He|done]).
    have Hdi : pc_ags d !! e.1 = pc_ags c0 !! e.1 by apply Hfr.
    (* ---- the transplanted step ---- *)
    destruct (wp_pf_step_transplant (pstep_xv6 riscv_step) e.1 l c0 c d
                Hst0 Himgd Hlogd Hdi) as (agx & Hagsc & Himgcc & Hstd).
    set (d2 := WPCfg (pc_img c) (pc_log c) (<[e.1 := agx]> (pc_ags d))).
    have Hilt : (e.1 < length (pc_ags d))%nat.
    { apply lookup_lt_is_Some_1. rewrite Hdi Hclk0. by eexists. }
    have Hd2i : pc_ags d2 !! e.1 = Some agx
      by (rewrite /d2 /=; apply list_lookup_insert).
    have Hd2fr : ∀ j, j ≠ e.1 → pc_ags d2 !! j = pc_ags d !! j
      by (intros j Hj; rewrite /d2 /=; by apply lookup_insert_other).
    have Hci : pc_ags c !! e.1 = Some agx
      by (rewrite Hagsc; exact (lookup_insert_self _ _ _ _ Hclk0)).
    have Hcfr : ∀ j, j ≠ e.1 → pc_ags c !! j = pc_ags c0 !! j
      by (intros j Hj; rewrite Hagsc; by apply lookup_insert_other).
    have Hlend2 : length (pc_ags d2) = length (pc_ags c)
      by rewrite /d2 /= length_insert Hlend Hagsc length_insert.
    have Hobs2 : ∀ j a, (obs_flr c j a ≤ obs_flr d2 j a)%nat.
    { intros j a. rewrite /obs_flr.
      destruct (decide (j = e.1)) as [->|Hj].
      - by rewrite Hci Hd2i.
      - rewrite (Hd2fr j Hj) (Hcfr j Hj). have := Hobs j a. by rewrite /obs_flr. }
    have Hfr2 : ∀ j, unfin order (S n) j → pc_ags d2 !! j = pc_ags c !! j.
    { intros j Hj. destruct (decide (j = e.1)) as [->|Hjne];
        [by rewrite Hd2i Hci|].
      rewrite (Hd2fr j Hjne) (Hcfr j Hjne). apply Hfr. by eapply unfin_S. }
    have Hrun2 : rtc (wp_pf_run (pstep_xv6 riscv_step)) (wp_init img ps) d2
      by (eapply rtc_r; [exact Hrun|by exists e.1, l]).
    have Hocd : own_coh d
      by (eapply own_coh_run; [apply own_coh_init|exact Hrun]).
    have Hdrd : disk_relp d
      by (eapply disk_relp_run; [apply disk_relp_init|exact Hrun]).
    (* ---- the two upgrades ---- *)
    have Hclsd : xcls_canon e.1 l d d2.
    { have Hcls0 : xcls_canon e.1 l c0 c
        by exact (chain_cls order n e T ev c0 c l _ He Hnp Hqc0 Hqc1 HT Hev
                    Hclk0 Hst0).
      intros ag2 msg Hag2 Hlogeq. rewrite /d2 /= in Hlogeq.
      rewrite Hlogd in Hlogeq.
      apply (Hcls0 ag2); [by rewrite -Hdi|exact Hlogeq]. }
    have Hrmwd : xrmw_tight e.1 l d
      by exact (xrmw_tight_own_coh (pstep_xv6 riscv_step) e.1 l d d2 Hocd Hstd).
    (* ---- the OPEN agent, if any, is [e.1] ---- *)
    have Hopi : ∀ j, op = Some j → j = e.1.
    { intros j Hj. rewrite Hj in Hop.
      destruct Hop as (_ & _ & Hnx & _). by rewrite (Hnx e He). }
    (* ---- ONE SEGMENT STEP: irq-free, or an interrupt delivery ----

       Since stage B the two are NOT separate cases of the invariant: a
       delivery is an ordinary [xstep] of the agent's segment, carried
       inside the hart segment it interrupts (and commuted out of it by
       [WeakComposeLang]'s refinement).  All [Hseip] has to supply is the
       seip-freedom of the residual, and only when there IS one. *)
    have Hsolo : xstep e.1 d d2.
    { destruct (pf_step_ni_or_irq riscv_step e.1 l d d2 Hstd)
        as [Hni|(Hlsil & Hfen & Hirq)].
      - left. by exists l.
      - right. split_and!; [|exact Hfen|exact Hirq].
        intros agz qz Hlkz Hstz Hnbz.
        destruct (pf_xirq_at e.1 d d2 Hirq)
          as (agD & agD' & qD & qD' & HlkD & HstD & HlkD' & HstD'
              & _ & _ & Hdel).
        have HzagD : agD = agz by congruence. subst agD.
        have HzqD : qD = qz by congruence. subst qD.
        have Hzagx : agD' = agx by (rewrite Hd2i in HlkD'; by injection HlkD').
        have Hzstx : pa_st agx = pa_st agn1
          by (rewrite Hci in Hclk1; injection Hclk1 as Hx; by rewrite Hx).
        have HzagDn : pa_st agz = pa_st agn.
        { rewrite Hdi Hclk0 in Hlkz. injection Hlkz as Hx. by rewrite -Hx. }
        have Hzq : pa_st agn = PHart qz by rewrite -HzagDn.
        have Hzq' : pa_st agn1 = PHart qD'.
        { rewrite -Hzstx -Hzagx. exact HstD'. }
        exact (Hseip e.1 T e.2 agn agn1 qz qD' WeakPromise.LSilent
                 HT Hagn Hagn1 Hzq Hzq' Hdel Hnbz). }
      (* open or extend *)
      have Hsr : ∃ ds, chained2 segs (wp_init img ps) ds ∧
                       seg_run e.1 ds d2 ∧
                       (∀ j, j ≠ e.1 → pc_ags d !! j = pc_ags ds !! j ∨ True).
      { destruct op as [j|].
        - have Hje : j = e.1 by apply Hopi.
          subst j. destruct Hop as (Hsrun & Hnb & _ & _).
          exists dstart. split_and!; [exact Hch| |by right].
          by eapply seg_run_step.
        - subst dstart. exists d. split_and!; [exact Hch| |by right].
          apply seg_run_start; [by rewrite Hdi Hclk0; eexists
                               |intros ag Hag; by eapply Hbdd
                               |exact Hsolo]. }
      destruct Hsr as (ds & Hchs & Hsrun2 & _).
      have Hbddd2 : ∀ j ag, j ≠ e.1 → pc_ags d2 !! j = Some ag → pbnd (pa_st ag).
      { intros j ag Hj Hlkj. rewrite (Hd2fr j Hj) in Hlkj.
        apply (Hbdd j ag); [|exact Hlkj]. intros Hx.
        by destruct (Hj (Hopi j Hx)). }
      (* close, complete-then-close, or stay open *)
      destruct (decide (pbnd (pa_st agx))) as [Hpb|Hnpb].
      + (* the block ends here *)
        destruct (seg_close e.1 ds d2 Hsrun2
                    ltac:(intros ag Hag; rewrite Hd2i in Hag;
                          by injection Hag as <-))
          as (sg & Hsrc & Hdst & Hokg).
        apply (seg_inv_intro order (S n) c (segs ++ [sg]) d2 d2 None);
          [by eapply chained2_app; [exact Hchs|rewrite /= Hsrc Hdst; by split]
          |by apply Forall_app; split; [exact Hall|by apply Forall_singleton]
          |exact Hrun2|done|done|done|exact Hlend2|exact Hfr2| |exact Hobs2].
        intros j ag _ Hlkj. destruct (decide (j = e.1)) as [->|Hj];
          [rewrite Hd2i in Hlkj; by injection Hlkj as <-|].
        by eapply Hbddd2.
      + (* the block continues *)
        destruct (decide (S n = length order)) as [Hend|Hend].
        * apply (seg_inv_intro order (S n) c segs ds d2 (Some e.1));
            [exact Hchs|exact Hall|exact Hrun2| |done|done|exact Hlend2
            |exact Hfr2| |exact Hobs2].
          -- split_and!; [exact Hsrun2| | | |by rewrite Hd2i Hci].
             ++ intros ag Hag. rewrite Hd2i in Hag. by injection Hag as <-.
             ++ intros e' He'. exfalso.
                have Hx : (S n < length order)%nat by eapply lookup_lt_Some.
                lia.
             ++ exists e. split; [by rewrite Nat.sub_succ Nat.sub_0_r|done].
          -- intros j ag Hj Hlkj. apply (Hbddd2 j ag); [|exact Hlkj].
             intros ->. by apply Hj.
        * destruct (decide (unfin order (S n) e.1)) as [Hunf1|Hunf1].
          -- (* stay open: the next position is this same block *)
             have Hnb1 : ¬ pbnd (pa_st agn1).
             { intros Hx. apply Hnpb. rewrite Hci in Hclk1.
               injection Hclk1 as Hclk1. by rewrite Hclk1. }
             have Hbat : bnd_at pbnd T (S e.2) = false.
             { rewrite /bnd_at Hagn1. by apply bool_decide_eq_false. }
             have Hbid : bid TS pbnd (e.1, S e.2) = bid TS pbnd e.
             { rewrite /bid /bno /= HT. f_equal. simpl. rewrite Hbat. lia. }
             have Hsmem := nproc_mem order e.1 Hnd
                             (order_dc TS ps Hnag order b2 Hmem e.1).
             have Hnpo : (S e.2 < nproc order e.1)%nat.
             { rewrite -(take_drop (S n) order) nproc_app Hnp1.
               have := nproc_pos_of_unfin order (S n) e.1 Hunf1. lia. }
             have Hin : (e.1, S e.2) ∈ order by apply Hsmem.
             apply elem_of_list_lookup in Hin as (m & Hm).
             have Hmge : (S n ≤ m)%nat.
             { destruct (decide (m < S n)%nat) as [Hlt|?]; [|lia]. exfalso.
               have Hin' : (e.1, S e.2) ∈ take (S n) order.
               { apply elem_of_list_lookup. exists m.
                 rewrite lookup_take; [exact Hm|lia]. }
               have Hsm := nproc_mem (take (S n) order) e.1
                             (nodup_take order (S n) Hnd)
                             (take_dc order b2 (S n) Hmem Hpred e.1).
               have := proj1 (Hsm (S e.2)) Hin'. rewrite Hnp1. lia. }
             have Hnext : ∀ e', order !! S n = Some e' → e'.1 = e.1.
             { intros e' He'. destruct (decide (m = S n)) as [Hme|Hme].
               - rewrite Hme He' in Hm. by injection Hm as ->.
               - have Hb := Hcontig n (S n) m e e' (e.1, S e.2)
                              ltac:(lia) ltac:(lia) He He' Hm
                              ltac:(by rewrite Hbid).
                 exact (f_equal fst Hb). }
             apply (seg_inv_intro order (S n) c segs ds d2 (Some e.1));
               [exact Hchs|exact Hall|exact Hrun2| |done|done|exact Hlend2
               |exact Hfr2| |exact Hobs2].
             ++ split_and!;
                  [exact Hsrun2| |exact Hnext| |by rewrite Hd2i Hci].
                ** intros ag Hag. rewrite Hd2i in Hag. by injection Hag as <-.
                ** exists e. split; [by rewrite Nat.sub_succ Nat.sub_0_r|done].
             ++ intros j ag Hj Hlkj. apply (Hbddd2 j ag); [|exact Hlkj].
                intros ->. by apply Hj.
          -- (* the agent is finished: splice its silent epilogue in HERE *)
             have Hne_b2 : e.1 ≠ b2.1.
             { intros Hx. apply Hunf1. rewrite Hx.
               eapply (unfin_le order (S n) (length order - 1)); [lia|].
               by eapply unfin_here; [exact Hlast|]. }
             have Hnpo : nproc order e.1 = S e.2.
             { rewrite -(take_drop (S n) order) nproc_app Hnp1
                       (nproc_zero_of_not_unfin order (S n) e.1 Hunf1). lia. }
             have Hqt : pquiet (pa_st agn1).
             { eapply (cut_pquiet_tr TS img ps Hwf Himg Hnag Hps0 Hee Hps_bnd
                         Hcq Himgt order b2 e.1 T agn1 Hmem Hnd HT);
                 [by rewrite Hnpo|exact Hne_b2]. }
             have Hstx : pa_st agx = pa_st agn1
               by (rewrite Hci in Hclk1; injection Hclk1 as Hx; by rewrite Hx).
             destruct (pa_st agn1) as [q|dd pend] eqn:Hsp; last first.
             { exfalso. apply Hnpb. rewrite Hstx. try (rewrite Hsp).
               simpl in Hqt |- *. exact Hqt. }
             destruct (xquiet_complete riscv_step e.1 d2 agx q Hd2i
                         ltac:(by rewrite Hstx) Hqt)
               as (d3 & ag3 & q3 & Hqrun & Hlk3 & Hst3 & Hm3 & Hf3 & Hlog3
                   & Himg3 & Hfr3).
             have Hxrun : rtc (pf_xsolo riscv_step e.1) d2 d3
               := pf_xquiet_run_solo riscv_step e.1 d2 d3 Hqrun.
             have Hrunall : rtc (wp_pf_run (pstep_xv6 riscv_step)) d2 d3
               := pf_xsolo_rtc_run riscv_step e.1 d2 d3 Hxrun.
             have Hsrun3 : seg_run e.1 ds d3.
             { destruct Hsrun2 as (Hs & Hb & Hr0 & Hdo & _). split_and!;
                 [exact Hs|exact Hb
                 |by etrans;
                    [exact Hr0|exact (pf_xsolo_rtc_xstep e.1 d2 d3 Hxrun)]
                 |by eapply (dopen_hart e.1 ds d2 d3 agx q)|].
               eapply (dsolo_hart e.1 ds d2 d3 agx q);
                 [exact Hdo|exact Hd2i|by rewrite Hstx]. }
             have Hbd3 : at_pbnd e.1 d3.
             { intros ag Hag. rewrite Hlk3 in Hag. injection Hag as <-.
               rewrite Hst3. by split. }
             destruct (seg_close e.1 ds d3 Hsrun3 Hbd3)
               as (sg & Hsrc & Hdst & Hokg).
             have Hobs3 : ∀ j a, (obs_flr d2 j a ≤ obs_flr d3 j a)%nat.
             { intros j a.
               by destruct (pf_xsolo_run_xtframe riscv_step e.1 d2 d3 Hxrun)
                 as (_ & _ & _ & Ho). }
             apply (seg_inv_intro order (S n) c (segs ++ [sg]) d3 d3 None);
               [by eapply chained2_app; [exact Hchs|rewrite /= Hsrc Hdst; by split]
               |by apply Forall_app; split; [exact Hall|by apply Forall_singleton]
               |by etrans; [exact Hrun2|exact Hrunall]|done
               |by rewrite Hlog3|by rewrite Himg3| | | |].
             ++ by rewrite (pf_run_ags_len _ _ _ Hrunall).
             ++ intros j Hj. destruct (decide (j = e.1)) as [->|Hjne];
                  [by destruct (Hunf1 Hj)|].
                rewrite (Hfr3 j Hjne). by apply Hfr2.
             ++ intros j ag _ Hlkj. destruct (decide (j = e.1)) as [->|Hjne];
                  [by apply Hbd3|].
                rewrite (Hfr3 j Hjne) in Hlkj. by eapply Hbddd2.
             ++ intros j a. etrans; [by apply Hobs2|by apply Hobs3].
  Qed.


  (* ---------------------------------------------------------------- *)
  (** *** THE PACKAGED, FULLY SEGMENTED THEOREM *)

  Theorem cone_segments2 (b1 b2 : gev) :
    bad nh TS b1 b2 → bad_min nh TS b2 →
    ∃ (segs : list seg2) (cf : wpcfg pxv6),
      chained2 segs (wp_init img ps) cf ∧
      Forall seg2_ok segs ∧
      (∃ p m a, violates_at cf p m b1.1 b2.1 a) ∧
      violation_hart cls_of pub_of nh cf ∧
      (∀ j ag, pc_ags cf !! j = Some ag → pbnd (pa_st ag)).
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
          & Hrdlast & Hlenc & Hcfs0 & Hcfm & Hstepc & Hqc & Hrunm & Hv1 & Hv2).
    destruct (seg_build order cfs b2 Hmem Hnd Hlast Hpred Hcontig Hlenc Hcfs0
                Hstepc Hqc (length order) ltac:(lia) cmid Hcfm)
      as (segs & dstart & d & op & Hch & Hall & Hrun & Hop & Hlogd & Himgd
          & Hlend & Hfr & Hbdd & Hobs).
    have Hbndm : cfg_bnd cmid
      by apply (pf_run_bnd _ _ _ Hrunm), cfg_bnd_init.
    have Hqcm : qcfg (pstep_xv6 riscv_step) TS img ps order cmid.
    { have Hx := Hqc (length order) cmid Hcfm.
      by rewrite (take_ge order (length order) ltac:(lia)) in Hx. }
    have Hqcm2 := Hqcm.
    destruct Hqcm2 as (_ & Hcimg & _ & Hclen & Hcags).
    (* ---- close whatever is still open, completing the reader ---- *)
    have Hfin : ∃ (segs' : list seg2) (cf : wpcfg pxv6),
        chained2 segs' (wp_init img ps) cf ∧ Forall seg2_ok segs' ∧
        (∀ j ag, pc_ags cf !! j = Some ag → pbnd (pa_st ag)) ∧
        (∃ ms, pc_log cf = pc_log cmid ++ ms ∧
               Forall (λ mq, wm_tid mq = Some b2.1) ms) ∧
        (∀ j a, (obs_flr cmid j a ≤ obs_flr cf j a)%nat).
    { destruct op as [i|]; last first.
      { exists segs, d. split_and!;
          [by rewrite Hop|exact Hall| |by exists []; rewrite app_nil_r
          |exact Hobs].
        intros j ag Hlkj. by eapply Hbdd. }
      destruct Hop as (Hsrun & Hnb & _ & (e0 & He0 & He0i) & Hslot).
      have Hib2 : i = b2.1 by (rewrite Hlast in He0; injection He0 as <-).
      rewrite Hib2 in Hsrun Hnb Hslot.
      (* the reader's record at [d] is [cmid]'s *)
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
      have Hlkd : pc_ags d !! b2.1 = Some agr by rewrite Hslot; exact Hlkr.
      have Hstr : pa_st agr = PHart qr by rewrite /agr /= Hqr.
      have Hcompl : ∃ d3 ms,
          rtc (pf_xsolo riscv_step b2.1) d d3 ∧ at_pbnd b2.1 d3 ∧
          pc_log d3 = pc_log d ++ ms ∧
          Forall (λ mq, wm_tid mq = Some b2.1) ms ∧
          (∀ j, j ≠ b2.1 → pc_ags d3 !! j = pc_ags d !! j) ∧
          (∀ j a, (obs_flr d j a ≤ obs_flr d3 j a)%nat) ∧
          (∃ ag3 q3, pc_ags d3 !! b2.1 = Some ag3 ∧ pa_st ag3 = PHart q3).
      { have Hbndd : cfg_bnd d
          by (apply (pf_run_bnd _ _ _ Hrun); apply cfg_bnd_init).
        destruct (sp_m qr) as [mr|] eqn:Hm.
        - have Hr := Hres b2.1 T2 (S b2.2) agn2 qr HT2 Hagn2 Hqr.
          rewrite Hm in Hr. destruct Hr as (Hsh & Hlv).
          destruct (xtail_complete riscv_step b2.1 d agr qr mr
                      ltac:(by rewrite Himgd Hcimg) Hbndd Hlkd Hstr Hm Hsh Hlv)
            as (d3 & ag3 & q3 & Hrun3 & Hlk3 & Hst3 & Hm3 & Hf3
                & ((msx & Hlogx & Hallx) & Himgx & Hfrx & Hobsx) & _).
          exists d3, msx. split_and!;
            [exact Hrun3| |exact Hlogx|exact Hallx|exact Hfrx|exact Hobsx
            |by exists ag3, q3].
          intros ag Hag. rewrite Hlk3 in Hag. injection Hag as <-.
          rewrite Hst3. by split.
        - destruct (xquiet_complete riscv_step b2.1 d agr qr Hlkd Hstr
                      ltac:(by rewrite /psail_quiet Hm))
            as (d3 & ag3 & q3 & Hrun3 & Hlk3 & Hst3 & Hm3 & Hf3 & Hlogq
                & Himgq & Hfrq).
          have Hrun3' : rtc (pf_xsolo riscv_step b2.1) d d3
            := pf_xquiet_run_solo riscv_step b2.1 d d3 Hrun3.
          exists d3, []. split_and!;
            [exact Hrun3'| |by rewrite Hlogq app_nil_r|constructor|exact Hfrq
            | |by exists ag3, q3].
          + intros ag Hag. rewrite Hlk3 in Hag. injection Hag as <-.
            rewrite Hst3. by split.
          + by destruct (pf_xsolo_run_xtframe riscv_step b2.1 d d3 Hrun3')
              as (_ & _ & _ & Ho). }
      destruct Hcompl as (d3 & ms & Hrun3 & Hbd3 & Hlog3 & Hall3 & Hfr3 & Hobs3
                          & (ag3 & q3 & Hlk3 & Hst3)).
      have Hsrun3 : seg_run b2.1 dstart d3.
      { destruct Hsrun as (Hs & Hb & Hr0 & Hdo & _). split_and!;
          [exact Hs|exact Hb
          |by etrans;
             [exact Hr0|exact (pf_xsolo_rtc_xstep b2.1 d d3 Hrun3)]
          |exact (dopen_hart b2.1 dstart d d3 agr qr Hdo Hlkd Hstr)|].
        exact (dsolo_hart b2.1 dstart d d3 agr qr Hdo Hlkd Hstr). }
      destruct (seg_close b2.1 dstart d3 Hsrun3 Hbd3)
        as (sg & Hsrc & Hdst & Hokg).
      exists (segs ++ [sg]), d3. split_and!.
      - by eapply chained2_app; [exact Hch|rewrite /= Hsrc Hdst; by split].
      - by apply Forall_app; split; [exact Hall|by apply Forall_singleton].
      - intros j ag Hlkj. destruct (decide (j = b2.1)) as [->|Hj];
          [by apply Hbd3|].
        rewrite (Hfr3 j Hj) in Hlkj. apply (Hbdd j ag); [|exact Hlkj].
        intros [= Hx]. apply Hj. by rewrite -Hx.
      - exists ms. split; [by rewrite Hlog3 Hlogd|exact Hall3].
      - intros j a. etrans; [by apply Hobs|by apply Hobs3]. }
    destruct Hfin as (segs' & cf & Hch' & Hall' & Hbnd' & (ms & Hlogf & Hallf)
                      & Hobsf).
    (* ---- the violation survives ---- *)
    destruct Hv1 as (p & mv & av & Hviol).
    have Hnej : b2.1 ≠ b1.1 by (intros Hx; apply Hne12; by rewrite Hx).
    have Hviolf : violates_at cf p mv b1.1 b2.1 av.
    { eapply (violates_at_append cmid cf p mv b1.1 b2.1 av ms Hlogf);
        [|apply Hobsf|exact Hviol].
      apply list_relations.Forall_lookup_2. intros n0 mq Hn0. left.
      rewrite (list_relations.Forall_lookup_1 _ _ _ _ Hallf Hn0).
      intros Heq. injection Heq as Heq. by apply Hnej. }
    exists segs', cf. split_and!;
      [exact Hch'|exact Hall'|by exists p, mv, av| |exact Hbnd'].
    destruct Hviolf as (Hlogp & Htid & Hclsv & Hpub & Hne' & Hbyte & Hobsv).
    exists p, mv, b1.1, b2.1, av. split_and!;
      [exact Hlogp|exact Htid| |exact Hclsv|exact Hpub|exact Hne'| |exact Hbyte
      |exact Hobsv].
    - exists b1.1. split; [exact Htid|exact Hh1].
    - exists b2.1. split; [done|exact Hh2].
  Qed.

End package.

(* ====================================================================== *)
(** ** 13. [Hres] IS A DERIVATION, NOT A PREMISE

    §11–§12 take [Hres] — EVERY record of EVERY trace whose state is a
    hart with an in-flight residual has that residual [sail_shaped] and
    [sail_live] — as an opaque premise.  It is not one: it is a trace
    INVARIANT whose only inputs are the two group-3 model facts.

    THE THREE ARMS OF A [PHart] STEP.  [pstep_xv6]'s hart arm is
    [WeakSailLTS.sail_step], and each of its arms does one of three
    things to the reading:

      - the PARKED FENCE arm and [WeakSailLTS.irq_deliver] rebuild the
        record with [sp_m] LITERALLY unchanged (a fence fires and clears
        [sp_fence]; a delivery writes [sig_seip] and pops [sp_irq]) — so
        both properties are preserved outright ([res_ok_frame]);
      - an IN-BLOCK step ([sp_m ≠ None], no parked fence) is exactly a
        [WeakSailLTS2.sail_step_ni], where [WeakSailComplete]'s two
        preservation lemmas apply verbatim;
      - the BOUNDARY arm ([sp_m = None]) is the only one that ESTABLISHES
        a residual, and it establishes [next tick] — about which the
        group-3 facts say everything.

    SINCE STAGE D THERE IS NO RESIDUE AT ALL.  The old derivation kept a
    third conjunct (oracle consistency of the record's device stream) and
    therefore a boundary-record premise [horc_prem] to re-establish it at
    each instruction.  That premise was UNSATISFIABLE (see [WeakSailLTS]
    delta (b)) and, with the stream replaced by the hart's own device
    automaton, it is also unnecessary: the device arms are total, so no
    property of the fabric has to travel with the residual.  [horc_prem]
    is deleted and [hres_derived] takes the two group-3 facts alone.

    The base case is free: an initial record is [pbnd] (§11's [Hps_bnd]),
    hence [sp_m = None], hence the match is [True].

    EXPORTS.  [hres_prem] is a standalone [Prop] over [TS] whose body is
    §11/§12's [Hres] context hypothesis VERBATIM, so the capstone
    ([WeakComposeLang.xv6_no_bad_edge]) discharges that hypothesis with
    [hres_derived] rather than assuming it. *)

(** The per-record reading.  Definitionally the conjunction of
    [WeakSailComplete]'s [shaped_res] and [live_res] ([res_ok_split]), and
    definitionally the body of [Hres]. *)
Definition res_ok (q : psail) : Prop :=
  match sp_m q with
  | None => True
  | Some m => sail_shaped m ∧ sail_live m
  end.

Lemma res_ok_split q : res_ok q ↔ shaped_res q ∧ live_res q.
Proof.
  rewrite /res_ok /shaped_res /live_res. destruct (sp_m q); tauto.
Qed.

(** [WeakComposeLang]'s [Hres], as a standalone [Prop]. *)
Definition hres_prem (TS : ptraces pxv6) : Prop :=
  ∀ i T k ag q,
    pt_trs TS !! i = Some T → at_ags T !! k = Some ag →
    pa_st ag = PHart q →
    match sp_m q with
    | None => True
    | Some m => sail_shaped m ∧ sail_live m
    end.

(* ---------------------------------------------------------------- *)
(** *** The step-level preservation lemma *)

(** Species is preserved BACKWARDS too: only the hart arm of [pstep_xv6]
    can land in a [PHart] state, and it is [sail_step]. *)
Lemma pstep_xv6_hart_pre (next : bool → M unit) p l q' :
  pstep_xv6 next p l (PHart q') → ∃ q, p = PHart q ∧ sail_step next q l q'.
Proof. destruct p as [q|d pend]; [by exists q|done]. Qed.

(** …and forwards, which is the fact §13's induction needs to stay on the
    hart side of the [PHart]/[PDisk] split. *)
Lemma pstep_xv6_hart_post (next : bool → M unit) q l p' :
  pstep_xv6 next (PHart q) l p' → ∃ q', p' = PHart q' ∧ sail_step next q l q'.
Proof. destruct p' as [q'|d pend]; [by exists q'|done]. Qed.

(** An arm that rebuilds the record with the same residual preserves the
    reading — the parked fence and the interrupt delivery. *)
Lemma res_ok_frame q q' :
  sp_m q' = sp_m q → res_ok q → res_ok q'.
Proof. intros Hm Hr. rewrite /res_ok Hm. exact Hr. Qed.

(** THE STEP LEMMA.  Both properties are preserved-or-established by every
    [sail_step], given the two group-3 facts about the generator.  NO
    DEVICE SIDE CONDITION (stage D). *)
Lemma res_ok_step (next : bool → M unit)
    (Hnsh : ∀ b, sail_shaped (next b)) (Hnlv : ∀ b, sail_live (next b))
    q l q' :
  res_ok q → sail_step next q l q' → res_ok q'.
Proof.
  intros Hr Hstep. rewrite /sail_step in Hstep.
  destruct (sp_fence q) as [[[[pr pw] sr] sw]|] eqn:Hf.
  { (* the parked second fence: [sp_m] survives *)
    destruct Hstep as [_ ->]. exact (res_ok_frame q _ eq_refl Hr). }
  destruct Hstep as [Hirq|Hstep].
  { (* an interrupt delivery: ditto *)
    destruct Hirq as (_ & v & iq & _ & ->).
    exact (res_ok_frame q _ eq_refl Hr). }
  destruct (sp_m q) as [m|] eqn:Hm.
  - (* IN-BLOCK: [WeakSailComplete]'s two preservation lemmas *)
    have Hni : sail_step_ni next q l q'
      by rewrite /sail_step_ni Hf Hm.
    have Hne : sp_m q ≠ None by rewrite Hm.
    apply res_ok_split in Hr as (Hs & Hl). apply res_ok_split.
    split_and!.
    + exact (sail_shaped_res_step next q l q' Hne Hs Hni).
    + exact (sail_live_res_step next q l q' Hne Hl Hni).
  - (* BOUNDARY: the fresh instruction, from group 3 *)
    destruct Hstep as (_ & tick & ->). rewrite /res_ok /=.
    split_and!; [apply Hnsh|apply Hnlv].
Qed.

(* ---------------------------------------------------------------- *)
(** *** The trace induction *)

Section hres.
  Context (TS : ptraces pxv6) (ps : list pxv6).
  Context (Hwf : ptraces_wf (pstep_xv6 riscv_step) TS).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  Context (Hps_bnd : ∀ i p, ps !! i = Some p → pbnd p).
  Context (Hnsh : ∀ b, sail_shaped (riscv_step b)).
  Context (Hnlv : ∀ b, sail_live (riscv_step b)).

  (** The invariant, by induction on the record index.  Every consecutive
      pair of records is a [pstep_xv6] step ([asteps_wf_step]); the
      pre-record of a step landing in a hart state is itself a hart
      record, so the induction hypothesis applies to it, and §13's step
      lemma closes. *)
  Lemma res_ok_trace i T k ag q :
    pt_trs TS !! i = Some T → at_ags T !! k = Some ag →
    pa_st ag = PHart q → res_ok q.
  Proof.
    intros HT. revert ag q. induction k as [|k IH]; intros ag q Hag Hq.
    - (* the initial record is a boundary, so the reading is vacuous *)
      have Hb : pbnd (pa_st ag) := Hps_bnd i (pa_st ag) (Hps0 i T ag HT Hag).
      rewrite Hq in Hb. destruct Hb as [Hm _]. by rewrite /res_ok Hm.
    - have Hatr := Hwf i T HT.
      have [ev Hev] : is_Some (at_evs T !! k).
      { apply lookup_lt_is_Some_2. destruct Hatr as [Hlen _].
        apply lookup_lt_Some in Hag. lia. }
      destruct (asteps_wf_step (pstep_xv6 riscv_step) (pt_img TS) (pt_log TS) i
                  (at_ags T) (at_evs T) k ev Hatr Hev)
        as (ag0 & ag1 & st' & f & Hag0 & Hag1 & Hps & _ & Heq).
      have Hst : pa_st ag = st'.
      { have Hx : ag = ag1 by congruence. by rewrite Hx Heq. }
      rewrite Hst in Hq. rewrite Hq in Hps.
      destruct (pstep_xv6_hart_pre riscv_step (pa_st ag0) (ae_lb ev) q Hps)
        as (q0 & Hst0 & Hsl).
      apply (res_ok_step riscv_step Hnsh Hnlv q0 (ae_lb ev) q);
        [by apply (IH ag0 q0)|exact Hsl].
  Qed.

  (** THE EXPORT.  [Hres] from the two group-3 facts and the
      trace/initial-state well-formedness §11 already has in context. *)
  Theorem hres_derived : hres_prem TS.
  Proof.
    intros i T k ag q HT Hag Hq.
    exact (res_ok_trace i T k ag q HT Hag Hq).
  Qed.

End hres.

