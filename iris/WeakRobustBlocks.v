(** * WeakRobustBlocks.v — BLOCK STRUCTURE, THE CONE CUT, and COMPLETION
      (lift stage L1 — obstacles 1 and 2 of
       [claude-notes/completed/weak-memory-lift.md])

    THE GAP THIS FILE CLOSES.  φ is exported at INSTRUCTION boundaries
    (the WP steps whole instructions); the Layer-1 exhibit
    ([WeakRobustMain.bad_edge_violates]) stops at EVENT boundaries — its
    promise-free run replays a downward-closed ANCESTOR CONE of the bad
    read, and each agent is left CUT at whatever event of its trace the
    cone reached.  L3 may only consume such a run if every agent sits at
    an instruction boundary.  Two theorems bridge that:

      1. THE CONE-CUT THEOREM ([cone_boundary_thm]).  Every CROSS edge of
         the extended dependency graph emanates from a FULFIL
         ([cross_edge_fulfil]) — [gpo] is same-agent by definition, [grf]
         and [gE] both pin [gev_ts] of their SOURCE.  Hence the LAST
         processed event of any non-reader agent is a fulfil
         ([cut_last_fulfil]), and under STORE-LAST a fulfil ends its
         block: the cut lands at a boundary, or at the one admitted
         mid-block fulfil, the walker's A/D write-back CAS.

      2. COMPLETION ([complete_block] / [complete_cut] /
         [complete_reader]).  Under [img_total] a read is ALWAYS
         admissible — at the latest write to the byte, or at the
         era-initial image — so a cut agent's residual block always runs
         to its next boundary in the promise-free machine, and the
         VIOLATION SURVIVES the completion.

    WHAT IS ABSTRACT HERE, AND WHAT INSTANTIATES IT.  This is the Iris
    side of the seam: [WeakSailLTS] is NOT imported.  The block discipline
    is a predicate on the pair ([pstep], [at_boundary]) plus a marker
    [ad] for the walker's A/D CAS, and the instantiation obligations
    ([WeakSailLTS], stage L2) are:

      - [at_boundary p := sp_m p = None] — no in-flight micro-state, i.e.
        [sail_step] is between instructions;
      - [ad p l] — the step is the walker's [update_and_write_pte]
        write-back half ([Write_RISCV_conditional], [WCexcl]);
      - [bs_store_last]: a [sail_step] emitting [LStore]/[LRmw] that is
        not the A/D write-back retires its instruction, so its post-state
        has [sp_m = None].  This is "the data store is the block's LAST
        event" and it also gives "≤ one data store per block" — a second
        data store would have to come after a boundary, i.e. in the NEXT
        block.  "Fetch/reads first" needs no separate axiom: everything
        that is not the write is, by store-last, before it.
      - [bs_ad_rmw]/[bs_ad_mid]: the A/D write-back is an [LRmw] and does
        NOT retire the instruction (the translated data access follows).
      - [lts_enabled]: the model reads memory answers as INPUTS, so a
        load/rmw step exists for ANY values of the right width — one
        level up from [WeakRobustSim.ts_oblivious] (obliviousness in the
        TIMESTAMPS, enabledness in the VALUES).
      - [blk_fin]: a block is a finite, never-stuck run of micro-steps.

    THE A/D CORNER, AND WHICH ROUTE CLOSED IT.  Both, and both are here:

      (a) COMPLETION ([complete_cut]).  A cut at a mid-block A/D fulfil
          completes: the residual is the translated data access, and
          [img_total] makes its reads admissible.  The violation survives
          provided the completed agent is NOT the violating message's
          AUTHOR — [¬ pub] is per-author ([WeakMem.wpublished]), and the
          appended messages are the completing agent's own.  This is the
          route the plan names for the READER (necessarily mid-block) and
          for every third agent.
      (b) SUB-BLOCK BOUNDARIES ([cone_boundary_sub]).  Admitting the
          post-A/D-CAS point as a boundary collapses the two disjuncts:
          EVERY non-reader cut is then a boundary and NO completion is
          needed.  This is what closes the corner for the AUTHOR itself,
          where (a) does not apply — completing the author could append a
          [WCrel] message and PUBLISH the very message the violation is
          about.

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported FIRST so that [WeakPromise]'s [wlabel]
    constructors shadow its [lbl] ones. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge
                            WeakRobustTrace WeakRobustGraph WeakRobust
                            WeakRobustProv WeakRobustLin WeakRobustOrd
                            WeakRobustSim WeakRobustMain.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * §1  BLOCK STRUCTURE ON THE ABSTRACT LTS *)

(** A label that APPENDS a message — the two fulfil-carrying shapes. *)
Definition lb_writes (l : wlabel) : bool :=
  match l with LStore _ _ _ | LRmw _ _ _ _ _ => true | _ => false end.

(** A label that READS. *)
Definition lb_loads (l : wlabel) : bool :=
  match l with LLoad _ _ _ _ | LRmw _ _ _ _ _ => true | _ => false end.

(** The shape conditions the promise-free store/rmw rules impose on a
    label ([WeakPromiseBridge.PFStore] / [PFRmw]): a message is nonempty,
    and an rmw's halves have equal width. *)
Definition lb_ok (l : wlabel) : Prop :=
  match l with
  | LStore _ _ data => data ≠ []
  | LRmw _ _ _ tvs data => data ≠ [] ∧ length tvs = length data
  | _ => True
  end.

(** Two side-condition-free readings of a list insert, so that no proof
    below has to sequence [rewrite]'s side goals. *)
Lemma lookup_insert_self {A} (l : list A) i x y :
  l !! i = Some y → (<[i := x]> l) !! i = Some x.
Proof. intros H. apply list_lookup_insert. by eapply lookup_lt_Some. Qed.

Lemma lookup_insert_other {A} (l : list A) i x j :
  j ≠ i → (<[i := x]> l) !! j = l !! j.
Proof. intros Hne. apply list_lookup_insert_ne. intros ->. by apply Hne. Qed.

Lemma lb_writes_ts_none {P : Type} img log i (ag : wpagent P) l f Dl :
  astep_ok img log i ag l f Dl → lb_writes l = false → Dl = None.
Proof. intros Hok. destruct l; simpl; try done; by apply astep_ok_ts_none in Hok. Qed.

Section shape.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).
  (** SOME fabric: a dev-free traced step is a program step at EVERY
      fabric, so reading one out needs a witness that [D] is inhabited.
      Every real configuration supplies one ([pc_dev]). *)
  Context (dflt : D).
  Context (at_boundary : P → Prop).
  (** THE A/D MARKER: [ad p l] — the step is the hardware walker's
      accessed/dirty write-back CAS, the ONE write admitted mid-block. *)
  Context (ad : P → wlabel → Prop).

  (** THE BLOCK DISCIPLINE.  See the header for the [sail_step]
      instantiation obligations. *)
  Record blk_shape : Prop := BlkShape {
    (** STORE-LAST: a step that appends a message ENDS its block, unless
        it is the A/D write-back.  Together with the fact that a block
        starts at a boundary this is also "≤ ONE data store per block",
        and it makes "fetch and reads first" automatic. *)
    bs_store_last : ∀ p d l p' d',
      pstep p d l p' d' → lb_writes l = true → ¬ ad p l → at_boundary p';
    (** The A/D write-back is an [LRmw] (an exclusive-conditional pair). *)
    bs_ad_rmw : ∀ p d l p' d',
      pstep p d l p' d' → ad p l →
      ∃ aq rl base tvs data, l = LRmw aq rl base tvs data;
    (** …and it sits STRICTLY INSIDE its block: the translated data
        access still follows, so it does not retire the instruction. *)
    bs_ad_mid : ∀ p d l p' d', pstep p d l p' d' → ad p l → ¬ at_boundary p';
  }.

  (** STORE-LAST, on a trace of [WeakRobustTrace]: a non-A/D write event
      leaves its agent at a boundary. *)
  Lemma blk_trace_boundary img log i T k ev ag ag' :
    blk_shape → atrace_wf pstep img log i T →
    at_evs T !! k = Some ev → at_ags T !! k = Some ag →
    at_ags T !! S k = Some ag' →
    lb_writes (ae_lb ev) = true → ¬ ad (pa_st ag) (ae_lb ev) →
    at_boundary (pa_st ag').
  Proof.
    intros Hbs Hwf Hev Hag Hag' Hw Hnad.
    destruct (asteps_wf_step pstep img log i (at_ags T) (at_evs T) k ev Hwf Hev)
      as (ag0 & ag0' & st' & f & Hag0 & Hag0' & Hps & _ & ->).
    rewrite Hag in Hag0. rewrite Hag' in Hag0'. simplify_eq/=.
    apply (astep_prog_step pstep dflt) in Hps as (d & d' & Hps).
    by eapply (bs_store_last Hbs).
  Qed.

  (** SUB-BLOCK BOUNDARIES (the plan's fallback, mechanized): a boundary,
      or the point just after an A/D write-back. *)
  Definition at_boundary_ad (p : P) : Prop :=
    at_boundary p ∨ ∃ q d l d', pstep q d l p d' ∧ ad q l.

  Lemma at_boundary_ad_intro p : at_boundary p → at_boundary_ad p.
  Proof. by left. Qed.

End shape.

Global Arguments blk_shape {P D} _ _ _.
Global Arguments at_boundary_ad {P D} _ _ _ _.

(* ================================================================== *)
(** * §2  [img_total] AND READ ADMISSIBILITY (obstacle 2, piece (i))

    THE CHOICE OF FORM, RECORDED.  The primary premise is the SIMPLE one,
    [img_total img := ∀ a, is_Some (img a)]: it is what the boot image
    discharges ([wlat_init] covers every RAM byte) and it is all the
    consumers below need, so no abstract RAM range has to be threaded
    through the completion.  The ranged variant [img_total_on A] is
    provided and the per-byte lemma is proved over IT, so a consumer that
    must confine the premise to a set [A] can take that route with no
    reproving — it then owes "every residual access stays in [A]", an
    extra LTS obligation this file deliberately does not impose. *)

Definition img_total_on (A : Z → Prop) (img : image) : Prop :=
  ∀ a, A a → is_Some (img a).

Definition img_total (img : image) : Prop := ∀ a, is_Some (img a).

Lemma img_total_on_all img : img_total img ↔ img_total_on (λ _, True) img.
Proof. split; [by intros H a _|by intros H a; apply H]. Qed.

(** Under a total image, the byte's LATEST write always holds a value. *)
Lemma latest_log_byte img log a :
  is_Some (img a) → is_Some (log_byte img log (latest_ts log a) a).
Proof.
  intros H. eapply (latest_ts_some img log a 0%nat). by rewrite log_byte_0.
Qed.

(** (i) READ ADMISSIBILITY, PER BYTE.  Whatever the agent has already
    observed, the byte's latest write is readable — and nothing above it
    writes the byte at all, which is what the COHERENT ([lat]) arm and
    the exclusive window both need. *)
Theorem byte_readable_latest (A : Z → Prop) img log ws vpre a :
  img_total_on A img → A a → (Nat.max vpre (coh ws a) ≤ length log)%nat →
  ∃ (t : nat) (v : bv 8),
    log_byte img log t a = Some v ∧ readable img log ws vpre a t ∧
    ¬ writes_in log a t (length log).
Proof.
  intros Hi HA Hle.
  destruct (latest_log_byte img log a (Hi a HA)) as [v Hv].
  exists (latest_ts log a), v. split_and!; [done| |apply latest_ts_top].
  apply latest_readable; [done|]. apply latest_ts_latest. by eexists.
Qed.

(** The multi-byte form: a contiguous run of LATEST reads. *)
Definition read_latest (img : image) (log : list wmsg) (base : Z)
    (tvs : list (nat * bv 8)) : Prop :=
  ∀ j t v, tvs !! j = Some (t, v) →
    log_byte img log t (base + Z.of_nat j) = Some v ∧
    ¬ writes_in log (base + Z.of_nat j) t (length log).

Lemma read_latest_exists img log base n :
  img_total img → ∃ tvs, length tvs = n ∧ read_latest img log base tvs.
Proof.
  intros Hi. induction n as [|n IH].
  - exists []. split; [done|]. intros j t v Hj. by rewrite lookup_nil in Hj.
  - destruct IH as (tvs & Hlen & Hrl).
    destruct (latest_log_byte img log (base + Z.of_nat n) (Hi _)) as [v Hv].
    exists (tvs ++ [(latest_ts log (base + Z.of_nat n), v)]).
    split; [rewrite length_app /=; lia|].
    intros j t v' Hj.
    destruct (decide (j < n)%nat) as [Hlt|Hge].
    + rewrite lookup_app_l in Hj; [lia|]. by apply Hrl.
    + have Hjn : j = n.
      { apply lookup_lt_Some in Hj. rewrite length_app /= in Hj. lia. }
      subst j. rewrite lookup_app_r in Hj; [lia|].
      rewrite Hlen Nat.sub_diag /= in Hj. simplify_eq.
      split; [done|apply latest_ts_top].
Qed.

Lemma read_latest_read_ok img log ws aq lat base tvs :
  ws_bounded ws (length log) → read_latest img log base tvs →
  read_ok img log ws aq lat base tvs.
Proof.
  intros Hb Hrl j t v Hj. destruct (Hrl j t v Hj) as [Hlb Hnw].
  split_and!; [done| |by intros _].
  split; [by eexists|]. intros Hw. apply Hnw.
  eapply writes_in_mono_hi; [|exact Hw].
  have Hvp : (load_vpre ws aq ≤ length log)%nat by apply load_vpre_bounded.
  destruct Hb as (_ & _ & _ & _ & _ & _ & Hcoh & _).
  pose proof (Hcoh (base + Z.of_nat j)). lia.
Qed.

Lemma read_latest_excl_ok img log i base tvs :
  read_latest img log base tvs → excl_ok log i base tvs (S (length log)).
Proof.
  intros Hrl j t v Hj Hw. destruct (Hrl j t v Hj) as [_ Hnw].
  apply Hnw. eapply writes_in_mono_hi; [|by eapply writes_in_by_writes_in].
  lia.
Qed.

Lemma read_latest_ts_le img log base tvs j t v :
  read_latest img log base tvs → tvs !! j = Some (t, v) → (t ≤ length log)%nat.
Proof.
  intros Hrl Hj. destruct (Hrl j t v Hj) as [Hlb _].
  eapply log_byte_bounded. by eexists.
Qed.

(* ================================================================== *)
(** * §3  PROMISE-FREE COMPLETION OF A BLOCK (obstacle 2) *)

Section complete.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types c : wpcfg P D.

  (** VALUE-ENABLEDNESS of the LTS.  The completion runs the residual
      block against WHATEVER memory offers, so the program must accept
      any answer of the right width; and every label it emits must have
      the shape the promise-free rules require. *)
  Record lts_enabled : Prop := LtsEnabled {
    le_lb_ok : ∀ p d l p' d', pstep p d l p' d' → lb_ok l;
    le_load : ∀ p d aq lat base tvs tvs' p' d',
      length tvs = length tvs' → pstep p d (LLoad aq lat base tvs) p' d' →
      ∃ p'' d'', pstep p d (LLoad aq lat base tvs') p'' d'';
    le_rmw : ∀ p d aq rl base tvs data tvs' p' d',
      length tvs = length tvs' → pstep p d (LRmw aq rl base tvs data) p' d' →
      ∃ data' p'' d'', length data' = length data ∧
                   pstep p d (LRmw aq rl base tvs' data') p'' d'';
  }.

  (** A BLOCK IS A FINITE, NEVER-STUCK RUN: off a boundary the program
      always has a step, and every step strictly decreases a measure. *)
  Record blk_fin (at_boundary : P → Prop) (msr : P → nat) : Prop := BlkFin {
    bf_prog : ∀ p d, ¬ at_boundary p → ∃ l p' d', pstep p d l p' d';
    bf_meas : ∀ p d l p' d',
      pstep p d l p' d' → ¬ at_boundary p → (msr p' < msr p)%nat;
  }.

  (* ---------------------------------------------------------------- *)
  (** ** The promise-free step, per agent *)

  (** A COMPLETION STEP by agent [i]: one promise-free step of [i] alone,
      packaged with the log delta and its authorship — the two facts the
      violation-persistence lemma consumes. *)
  Definition cstep (i : agent) c c' : Prop :=
    (∃ l, wp_pf_step pstep i l c c') ∧
    ∃ ms, pc_log c' = pc_log c ++ ms ∧
          Forall (λ mq, wm_tid mq = Some i) ms.

  Lemma cstep_run i c c' : cstep i c c' → wp_pf_run pstep c c'.
  Proof. intros [[l Hs] _]. by exists i, l. Qed.

  Lemma cstep_rtc_run i c c' : rtc (cstep i) c c' → rtc (wp_pf_run pstep) c c'.
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|].
    eapply rtc_l; [by eapply cstep_run|exact IH].
  Qed.

  (** The step's SHAPE: the image is frozen, the agent vector changes at
      [i] only, and the log only grows. *)
  Lemma wp_pf_step_shape i l c c' :
    wp_pf_step pstep i l c c' →
    pc_img c' = pc_img c ∧
    (∃ ag ag', pc_ags c !! i = Some ag ∧
               pc_ags c' = <[i := ag']> (pc_ags c) ∧
               ws_le (pa_ws ag) (pa_ws ag')) ∧
    (∃ ms, pc_log c' = pc_log c ++ ms ∧ Forall (λ mq, wm_tid mq = Some i) ms).
  Proof.
    destruct 1 as [cfg ag st' dd Hag Hps
                  |cfg ag aq lat base tvs st' dd Hag Hps Hro
                  |cfg ag rl base data k st' dd Hag Hps Hdne
                  |cfg ag aq rl base tvs data k st' dd Hag Hps Hdne Hlen Hro Hex
                  |cfg ag pr pw sr sw st' dd Hag Hps]; simpl.
    - split_and!; [done| |exists []; rewrite app_nil_r; by split].
      exists ag, (WPAgent st' (pa_ws ag) (pa_prom ag)). split_and!; [done|done|].
      reflexivity.
    - split_and!; [done| |exists []; rewrite app_nil_r; by split].
      eexists ag, _. split_and!; [done|done|]. apply load_post_run_le.
    - split_and!; [done| |].
      + eexists ag, _. split_and!; [done|done|]. apply store_post_run_le.
      + exists [WMsg base data (Some i) k]. split; [done|].
        by apply list_relations.Forall_singleton.
    - split_and!; [done| |].
      + eexists ag, _. split_and!; [done|done|].
        etrans; [apply load_post_run_le|apply store_post_run_le].
      + exists [WMsg base data (Some i) k]. split; [done|].
        by apply list_relations.Forall_singleton.
    - split_and!; [done| |exists []; rewrite app_nil_r; by split].
      eexists ag, _. split_and!; [done|done|]. apply fence_post_le.
  Qed.

  Lemma wp_pf_step_frame i l c c' j :
    wp_pf_step pstep i l c c' → j ≠ i → pc_ags c' !! j = pc_ags c !! j.
  Proof.
    intros Hs Hne.
    destruct (wp_pf_step_shape i l c c' Hs) as (_ & (ag & ag' & _ & -> & _) & _).
    by apply lookup_insert_other.
  Qed.

  Lemma wp_pf_step_ags_len i l c c' :
    wp_pf_step pstep i l c c' → length (pc_ags c') = length (pc_ags c).
  Proof.
    intros Hs.
    destruct (wp_pf_step_shape i l c c' Hs) as (_ & (ag & ag' & _ & -> & _) & _).
    apply length_insert.
  Qed.

  (** The COHERENCE FLOOR only grows — for the stepping agent by
      [ws_le], for every other agent by the frame. *)
  Lemma wp_pf_step_obs_flr i l c c' j a :
    wp_pf_step pstep i l c c' → (obs_flr c j a ≤ obs_flr c' j a)%nat.
  Proof.
    intros Hs.
    destruct (wp_pf_step_shape i l c c' Hs)
      as (_ & (ag & ag' & Hag & Hins & Hle) & _).
    rewrite /obs_flr Hins.
    destruct (decide (j = i)) as [->|Hne].
    - rewrite Hag (lookup_insert_self _ _ _ _ Hag).
      by apply ws_le_coh.
    - rewrite (lookup_insert_other _ _ _ _ Hne).
      by destruct (pc_ags c !! j).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Boundedness of the configuration *)

  Definition cfg_bnd c : Prop :=
    ∀ j ag, pc_ags c !! j = Some ag → ws_bounded (pa_ws ag) (length (pc_log c)).

  Lemma cfg_bnd_init img d0 ps : cfg_bnd (wp_init (P:=P) (D:=D) img d0 ps).
  Proof.
    intros j ag Hag. rewrite /wp_init /= list_lookup_fmap in Hag.
    destruct (ps !! j) as [p|]; simplify_eq/=. apply ws_bounded_init.
  Qed.

  Lemma read_ok_ts_le img log ws aq lat base tvs j t v :
    read_ok img log ws aq lat base tvs → tvs !! j = Some (t, v) →
    (t ≤ length log)%nat.
  Proof.
    intros Hro Hj. destruct (Hro j t v Hj) as (Hlb & _ & _).
    eapply log_byte_bounded. by eexists.
  Qed.

  Lemma read_ok_forall img log ws aq lat base tvs :
    read_ok img log ws aq lat base tvs →
    Forall (λ t, (t ≤ length log)%nat) (tvs.*1).
  Proof.
    intros Hro. apply list_relations.Forall_lookup_2. intros j t Hj.
    rewrite list_lookup_fmap in Hj.
    destruct (tvs !! j) as [[t0 v0]|] eqn:Ht; simpl in Hj; [|done].
    simplify_eq. by eapply read_ok_ts_le.
  Qed.

  Lemma wp_pf_step_bnd i l c c' :
    wp_pf_step pstep i l c c' → cfg_bnd c → cfg_bnd c'.
  Proof.
    destruct 1 as [cfg ag st' dd Hag Hps
                  |cfg ag aq lat base tvs st' dd Hag Hps Hro
                  |cfg ag rl base data k st' dd Hag Hps Hdne
                  |cfg ag aq rl base tvs data k st' dd Hag Hps Hdne Hlen Hro Hex
                  |cfg ag pr pw sr sw st' dd Hag Hps];
      intros Hb j ag2 Hag2; simpl in Hag2 |- *.
    - destruct (decide (j = i)) as [->|Hne].
      + rewrite (lookup_insert_self _ _ _ _ Hag) in Hag2.
        simplify_eq/=. by eapply Hb.
      + rewrite (lookup_insert_other _ _ _ _ Hne) in Hag2.
        by eapply Hb.
    - destruct (decide (j = i)) as [->|Hne].
      + rewrite (lookup_insert_self _ _ _ _ Hag) in Hag2.
        simplify_eq/=. apply load_post_run_bounded; [by eapply Hb|].
        by eapply read_ok_forall.
      + rewrite (lookup_insert_other _ _ _ _ Hne) in Hag2.
        by eapply Hb.
    - rewrite length_app /=.
      destruct (decide (j = i)) as [->|Hne].
      + rewrite (lookup_insert_self _ _ _ _ Hag) in Hag2.
        simplify_eq/=.
        eapply (store_post_run_bounded _ _ _ _ _ (length (pc_log cfg)));
          [by eapply Hb|lia|lia].
      + rewrite (lookup_insert_other _ _ _ _ Hne) in Hag2.
        eapply ws_bounded_mono; [by eapply Hb|lia].
    - rewrite length_app /=.
      destruct (decide (j = i)) as [->|Hne].
      + rewrite (lookup_insert_self _ _ _ _ Hag) in Hag2.
        simplify_eq/=.
        eapply (store_post_run_bounded _ _ _ _ _ (length (pc_log cfg)));
          [|lia|lia].
        apply load_post_run_bounded; [by eapply Hb|by eapply read_ok_forall].
      + rewrite (lookup_insert_other _ _ _ _ Hne) in Hag2.
        eapply ws_bounded_mono; [by eapply Hb|lia].
    - destruct (decide (j = i)) as [->|Hne].
      + rewrite (lookup_insert_self _ _ _ _ Hag) in Hag2.
        simplify_eq/=. apply fence_post_bounded. by eapply Hb.
      + rewrite (lookup_insert_other _ _ _ _ Hne) in Hag2.
        by eapply Hb.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** ONE completion step is always available *)

  (** THE ADMISSIBILITY THEOREM (obstacle 2, piece (i) at the config
      level): under a total image and a bounded configuration, ANY step
      the program offers can be taken in the promise-free machine — the
      reads land at their bytes' latest writes. *)
  Theorem cstep_available i c ag l p' dd :
    lts_enabled → img_total (pc_img c) →
    ws_bounded (pa_ws ag) (length (pc_log c)) →
    pc_ags c !! i = Some ag → pstep (pa_st ag) (pc_dev c) l p' dd →
    ∃ c' ag', cstep i c c' ∧ pc_ags c' !! i = Some ag' ∧
              ∃ l' d', pstep (pa_st ag) (pc_dev c) l' (pa_st ag') d'.
  Proof.
    intros Hen Hi Hb Hag Hps.
    have Hlt : (i < length (pc_ags c))%nat by eapply lookup_lt_Some.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data
                  |pr pw sr sw].
    - (* silent *)
      eexists _, (WPAgent p' (pa_ws ag) (pa_prom ag)). split_and!.
      + split; [eexists; by apply (PFSilent pstep i c ag p' dd)|].
        exists []. rewrite /= app_nil_r. by split.
      + simpl. by eapply (lookup_insert_self _ _ _ _ Hag).
      + simpl. by exists LSilent, dd.
    - (* load: read every byte at its latest write *)
      destruct (read_latest_exists (pc_img c) (pc_log c) base (length tvs) Hi)
        as (tvs' & Hlen' & Hrl).
      destruct (le_load Hen (pa_st ag) (pc_dev c) aq lat base tvs tvs' p' dd
                  (eq_sym Hlen') Hps) as (p'' & dd' & Hps').
      have Hro : read_ok (pc_img c) (pc_log c) (pa_ws ag) aq lat base tvs'
        by apply read_latest_read_ok.
      eexists _, (WPAgent p'' (load_post_run (pa_ws ag) aq base (tvs'.*1))
                    (pa_prom ag)).
      split_and!.
      + split; [eexists;
                by apply (PFLoad pstep i c ag aq lat base tvs' p'' dd')|].
        exists []. rewrite /= app_nil_r. by split.
      + simpl. by eapply (lookup_insert_self _ _ _ _ Hag).
      + simpl. by exists (LLoad aq lat base tvs'), dd'.
    - (* store *)
      have Hne : data ≠ [] by apply (le_lb_ok Hen (pa_st ag) _ _ p' dd Hps).
      eexists _, (WPAgent p' (store_post_run (pa_ws ag) rl base (length data)
                               (S (length (pc_log c)))) (pa_prom ag)).
      split_and!.
      + split.
        * eexists.
          by apply (PFStore pstep i c ag rl base data WCplain p' dd).
        * exists [WMsg base data (Some i) WCplain]. split; [done|].
          by apply list_relations.Forall_singleton.
      + simpl. by eapply (lookup_insert_self _ _ _ _ Hag).
      + simpl. by exists (LStore rl base data), dd.
    - (* rmw: the exclusive window is clean because the read half is
         LATEST — nothing above it writes the byte at all *)
      destruct (le_lb_ok Hen (pa_st ag) _ _ p' dd Hps) as [Hnedata Hlend].
      destruct (read_latest_exists (pc_img c) (pc_log c) base (length tvs) Hi)
        as (tvs' & Hlen' & Hrl).
      destruct (le_rmw Hen (pa_st ag) (pc_dev c) aq rl base tvs data tvs' p' dd
                  (eq_sym Hlen') Hps) as (data' & p'' & dd' & Hlend' & Hps').
      have Hro : read_ok (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs'
        by apply read_latest_read_ok.
      have Hex : excl_ok (pc_log c) i base tvs' (S (length (pc_log c)))
        by apply (read_latest_excl_ok (pc_img c) (pc_log c) i base tvs').
      have Hne' : data' ≠ [].
      { intros Hnil. rewrite Hnil /= in Hlend'.
        apply Hnedata. by destruct data; simplify_eq/=. }
      have Hlen2 : length tvs' = length data' by lia.
      eexists _, (WPAgent p''
                    (store_post_run (load_post_run (pa_ws ag) aq base (tvs'.*1))
                       rl base (length data') (S (length (pc_log c))))
                    (pa_prom ag)).
      split_and!.
      + split.
        * eexists.
          by apply (PFRmw pstep i c ag aq rl base tvs' data' WCplain p'' dd').
        * exists [WMsg base data' (Some i) WCplain]. split; [done|].
          by apply list_relations.Forall_singleton.
      + simpl. by eapply (lookup_insert_self _ _ _ _ Hag).
      + simpl. by exists (LRmw aq rl base tvs' data'), dd'.
    - (* fence *)
      eexists _, (WPAgent p' (fence_post (pa_ws ag) pr pw sr sw) (pa_prom ag)).
      split_and!.
      + split; [eexists;
                by apply (PFFence pstep i c ag pr pw sr sw p' dd)|].
        exists []. rewrite /= app_nil_r. by split.
      + simpl. by eapply (lookup_insert_self _ _ _ _ Hag).
      + simpl. by exists (LFence pr pw sr sw), dd.
  Qed.

  Lemma cstep_bnd i c c' : cstep i c c' → cfg_bnd c → cfg_bnd c'.
  Proof. intros [[l Hs] _]. by eapply wp_pf_step_bnd. Qed.

  Lemma cstep_img i c c' : cstep i c c' → pc_img c' = pc_img c.
  Proof.
    intros [[l Hs] _]. by destruct (wp_pf_step_shape i l c c' Hs) as (? & _).
  Qed.

  Lemma cstep_frame i c c' j : cstep i c c' → j ≠ i → pc_ags c' !! j = pc_ags c !! j.
  Proof. intros [[l Hs] _] ?. by eapply wp_pf_step_frame. Qed.

  Lemma cstep_ags_len i c c' :
    cstep i c c' → length (pc_ags c') = length (pc_ags c).
  Proof. intros [[l Hs] _]. by eapply wp_pf_step_ags_len. Qed.

  Lemma cstep_obs_flr i c c' j a :
    cstep i c c' → (obs_flr c j a ≤ obs_flr c' j a)%nat.
  Proof. intros [[l Hs] _]. by eapply wp_pf_step_obs_flr. Qed.

  (** The [rtc] closures of the four. *)
  Lemma csteps_img i c c' : rtc (cstep i) c c' → pc_img c' = pc_img c.
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|].
    rewrite IH. by eapply cstep_img.
  Qed.

  Lemma csteps_bnd i c c' : rtc (cstep i) c c' → cfg_bnd c → cfg_bnd c'.
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|]. intros Hb.
    apply IH. by eapply cstep_bnd.
  Qed.

  Lemma csteps_frame i c c' j :
    rtc (cstep i) c c' → j ≠ i → pc_ags c' !! j = pc_ags c !! j.
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|]. intros Hne.
    rewrite (IH Hne). by eapply cstep_frame.
  Qed.

  Lemma csteps_ags_len i c c' :
    rtc (cstep i) c c' → length (pc_ags c') = length (pc_ags c).
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|].
    rewrite IH. by eapply cstep_ags_len.
  Qed.

  Lemma csteps_obs_flr i c c' j a :
    rtc (cstep i) c c' → (obs_flr c j a ≤ obs_flr c' j a)%nat.
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|].
    etrans; [by eapply cstep_obs_flr|exact IH].
  Qed.

  Lemma csteps_log i c c' :
    rtc (cstep i) c c' →
    ∃ ms, pc_log c' = pc_log c ++ ms ∧ Forall (λ mq, wm_tid mq = Some i) ms.
  Proof.
    induction 1 as [x|x y z [_ (ms & Hms & Hall)] _ IH].
    - exists []. rewrite app_nil_r. by split.
    - destruct IH as (ms' & Hms' & Hall').
      exists (ms ++ ms'). rewrite Hms' Hms app_assoc. split; [done|].
      by apply list_relations.Forall_app.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE BLOCK COMPLETION THEOREM *)

  (** (obstacle 2) A cut agent's residual block RUNS TO ITS NEXT
      BOUNDARY in the promise-free machine.  Nothing about the values it
      reads is claimed — completion is allowed to diverge from the
      behavior's own trace, which is exactly why [lts_enabled] is
      needed and why the completed agent's program state is not related
      to anything. *)
  (** The induction runs on the MEASURE, so the auxiliary form
      quantifies the configuration and the agent record INSIDE a strong
      induction over a bound [n]. *)
  Lemma complete_block_aux (at_boundary : P → Prop)
      `{!∀ p, Decision (at_boundary p)} (msr : P → nat) i n :
    lts_enabled → blk_fin at_boundary msr →
    ∀ c ag, (msr (pa_st ag) ≤ n)%nat →
      img_total (pc_img c) → cfg_bnd c → pc_ags c !! i = Some ag →
      ∃ c' ag', rtc (cstep i) c c' ∧ pc_ags c' !! i = Some ag' ∧
                at_boundary (pa_st ag').
  Proof.
    intros Hen Hfin. induction n as [n IH] using lt_wf_ind.
    intros c ag Hn Hi Hb Hag.
    destruct (decide (at_boundary (pa_st ag))) as [Hbd|Hbd].
    { exists c, ag. split_and!; [apply rtc_refl|done|done]. }
    destruct (bf_prog _ _ Hfin (pa_st ag) (pc_dev c) Hbd)
      as (l & p' & dd & Hps).
    destruct (cstep_available i c ag l p' dd Hen Hi (Hb i ag Hag) Hag Hps)
      as (c1 & ag1 & Hstep & Hag1 & (l' & d' & Hps')).
    have Hlt : (msr (pa_st ag1) < msr (pa_st ag))%nat
      by eapply (bf_meas _ _ Hfin).
    destruct (IH (msr (pa_st ag1)) ltac:(lia) c1 ag1 ltac:(lia))
      as (c' & ag' & Hrun & Hag' & Hbd'); [by rewrite (cstep_img i c c1 Hstep)
                                         |by eapply cstep_bnd|done|].
    exists c', ag'. split_and!; [|done|done].
    eapply rtc_l; [exact Hstep|exact Hrun].
  Qed.

  Theorem complete_block (at_boundary : P → Prop)
      `{!∀ p, Decision (at_boundary p)} (msr : P → nat) i c ag :
    lts_enabled → blk_fin at_boundary msr →
    img_total (pc_img c) → cfg_bnd c → pc_ags c !! i = Some ag →
    ∃ c' ag', rtc (cstep i) c c' ∧ pc_ags c' !! i = Some ag' ∧
              at_boundary (pa_st ag').
  Proof.
    intros Hen Hfin Hi Hb Hag.
    by eapply (complete_block_aux at_boundary msr i (msr (pa_st ag))).
  Qed.

End complete.

Global Arguments lts_enabled {P D} _.
Global Arguments blk_fin {P D} _ _ _.
Global Arguments cstep {P D} _ _ _ _.
Global Arguments cfg_bnd {P D} _.

(* ================================================================== *)
(** * §4  THE CONE-CUT THEOREM (obstacle 1) *)

Section cone.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).
  Context (dflt : D).

  Implicit Types TS : ptraces P D.
  Implicit Types e : gev.

  (** THE STRUCTURAL FACT.  Only [gpo] can leave a non-fulfil: [grf]
      pins [gev_ts] of its source (that IS the fulfil the read reads
      from) and so does [gE] (its source fulfils a floor LEAF —
      [WeakRobustOrd.gE_at]). *)
  Lemma gdep2_src_fulfil_or_po TS e1 e2 :
    gdep2 TS e1 e2 → (∃ ts, gev_ts TS e1 = Some ts) ∨ gpo TS e1 e2.
  Proof.
    intros [[Hpo|Hrf]|HE].
    - by right.
    - destruct Hrf as (ts & a & Hts & _). left. by exists ts.
    - destruct HE as (r & l & a & ts & tstar & that & _ & _ & _ & _ & H1 & _).
      left. by exists tstar.
  Qed.

  (** EVERY CROSS EDGE EMANATES FROM A FULFIL. *)
  Corollary cross_edge_fulfil TS e1 e2 :
    gdep2 TS e1 e2 → e1.1 ≠ e2.1 → ∃ ts, gev_ts TS e1 = Some ts.
  Proof.
    intros Hd Hne.
    destruct (gdep2_src_fulfil_or_po TS e1 e2 Hd) as [?|(Hag & _)];
      [done|by destruct (Hne Hag)].
  Qed.

  (** THE CONE: the processed set is exactly the wf strict ancestry of
      the designated read [r] — [WeakRobustMain.cone_Qinv]'s second
      conjunct, verbatim. *)
  Definition cone_of TS (done : list gev) (r : gev) : Prop :=
    ∀ e, e ∈ done ↔ (gev_wf TS e ∧ tc (gdep2 TS) e r).

  (** THE CUT IS A FULFIL.  For any agent OTHER than the reader, the
      last processed event is a fulfil: were it not, its only outgoing
      edges would be [gpo] ones, whose targets are later events of the
      SAME agent that the cone would then also contain — contradicting
      the cut. *)
  Theorem cut_last_fulfil TS done r j T m :
    ptraces_wf pstep TS → qorder TS done → cone_of TS done r → j ≠ r.1 →
    pt_trs TS !! j = Some T → nproc done j = S m →
    (m < length (at_evs T))%nat →
    ∃ ts, gev_ts TS (j, m) = Some ts.
  Proof.
    intros Hwf Hq Hcone Hne HT Hn Hlen.
    have Hwfm : gev_wf TS (j, m) by apply gev_wf_bounds; exists T.
    have Hin : (j, m) ∈ done.
    { apply (qorder_mem TS done j m Hq). split; [done|]. rewrite Hn. lia. }
    have Htc : tc (gdep2 TS) (j, m) r by apply Hcone in Hin as [_ ?].
    (* the first edge of the path out of the cut *)
    have Hfst : ∃ y, gdep2 TS (j, m) y ∧ (y = r ∨ tc (gdep2 TS) y r).
    { destruct Htc as [x y Hxy|x y z Hxy Hyz]; [by exists y; split; [|left]
                                               |by exists y; split; [|right]]. }
    destruct Hfst as (y & Hd & Hy).
    destruct (gdep2_src_fulfil_or_po TS (j, m) y Hd) as [Hf|Hpo]; [exact Hf|].
    exfalso.
    destruct Hpo as (Hag & Hlt & _ & Hwfy). simpl in Hag, Hlt.
    (* [y] is a LATER event of the SAME agent, and it is in the cone *)
    have Hyin : y ∈ done.
    { apply Hcone. split; [done|].
      destruct Hy as [->|Htcy]; [|exact Htcy]. exfalso. by apply Hne. }
    have Hylt : (y.2 < nproc done j)%nat.
    { have Hy2 : (j, y.2) ∈ done.
      { destruct y as [y1 y2]. simpl in Hag. by rewrite Hag. }
      by apply (qorder_mem TS done j y.2 Hq) in Hy2 as [_ ?]. }
    lia.
  Qed.

  (** THE CONE-CUT THEOREM.  Every NON-READER agent's cut in the
      downward-closed cone lands EITHER at a block boundary OR at the
      one admitted mid-block fulfil — the walker's A/D write-back CAS.
      The two disjuncts are kept explicitly labelled, as the design
      asks; [cone_boundary_sub] below collapses them. *)
  Theorem cone_boundary_thm (at_boundary : P → Prop) (ad : P → wlabel → Prop)
      `{!∀ p l, Decision (ad p l)}
      TS done r j T agn :
    ptraces_wf pstep TS →
    blk_shape pstep at_boundary ad →
    (∀ i T0 ag0, pt_trs TS !! i = Some T0 → at_ags T0 !! 0%nat = Some ag0 →
                 at_boundary (pa_st ag0)) →
    qorder TS done → cone_of TS done r → j ≠ r.1 →
    pt_trs TS !! j = Some T → at_ags T !! nproc done j = Some agn →
    (** the cut is at a BLOCK BOUNDARY … *)
    at_boundary (pa_st agn)
    (** … or at a mid-block A/D write-back CAS (an [LRmw] fulfil) *)
    ∨ (∃ m ag ev,
         nproc done j = S m ∧
         at_ags T !! m = Some ag ∧ at_evs T !! m = Some ev ∧
         (∃ ts, ae_ts ev = Some ts) ∧
         (∃ aq rl base tvs data, ae_lb ev = LRmw aq rl base tvs data) ∧
         ad (pa_st ag) (ae_lb ev)).
  Proof.
    intros Hwf Hbs Hinit Hq Hcone Hne HT Hagn.
    have Hatr : atrace_wf pstep (pt_img TS) (pt_log TS) j T by apply Hwf.
    have Hlens : length (at_ags T) = S (length (at_evs T))
      by eapply asteps_wf_len.
    destruct (nproc done j) as [|m] eqn:Hn.
    { left. by eapply Hinit. }
    (* the cut event is a FULFIL *)
    have Hmlt : (m < length (at_evs T))%nat.
    { apply lookup_lt_Some in Hagn. lia. }
    destruct (cut_last_fulfil TS done r j T m Hwf Hq Hcone Hne HT Hn Hmlt)
      as (ts & Hts).
    have [ev Hev] : is_Some (at_evs T !! m) by apply lookup_lt_is_Some_2.
    have Htsev : ae_ts ev = Some ts.
    { move: Hts. by rewrite /gev_ts /gev_ev /= HT /= Hev /=. }
    have [ag Hag] : is_Some (at_ags T !! m)
      by apply lookup_lt_is_Some_2; lia.
    (* a fulfil's label is a store or an rmw *)
    destruct (asteps_wf_step pstep (pt_img TS) (pt_log TS) j
                (at_ags T) (at_evs T) m ev Hatr Hev)
      as (ag0 & ag0' & st' & f & Hag0 & Hag0' & Hps & Hok & Hagne).
    have Heqag : ag0 = ag by congruence. subst ag0.
    have Hw : lb_writes (ae_lb ev) = true.
    { destruct (lb_writes (ae_lb ev)) eqn:Hlw; [done|].
      by rewrite (lb_writes_ts_none _ _ _ _ _ _ _ Hok Hlw) in Htsev. }
    destruct (decide (ad (pa_st ag) (ae_lb ev))) as [Had|Had].
    - right. exists m, ag, ev. split_and!; [done|done|done|by exists ts| |done].
      apply (astep_prog_step pstep dflt) in Hps as (dd & dd' & Hps).
      exact (bs_ad_rmw _ _ _ Hbs (pa_st ag) dd (ae_lb ev) st' dd' Hps Had).
    - left. eapply (blk_trace_boundary pstep dflt at_boundary ad
                      (pt_img TS) (pt_log TS) j T m ev ag agn);
        [exact Hbs|exact Hatr|exact Hev|exact Hag| |exact Hw|exact Had].
      congruence.
  Qed.

  (** THE SUB-BLOCK FORM (the plan's declared fallback, mechanized).
      With the post-A/D-CAS point admitted as a boundary, EVERY
      non-reader cut is a boundary and no completion is needed at all —
      which is what closes the corner for the violating message's own
      AUTHOR, the one agent [complete_cut] may not touch. *)
  Corollary cone_boundary_sub (at_boundary : P → Prop) (ad : P → wlabel → Prop)
      `{!∀ p l, Decision (ad p l)}
      TS done r j T agn :
    ptraces_wf pstep TS →
    blk_shape pstep at_boundary ad →
    (∀ i T0 ag0, pt_trs TS !! i = Some T0 → at_ags T0 !! 0%nat = Some ag0 →
                 at_boundary (pa_st ag0)) →
    qorder TS done → cone_of TS done r → j ≠ r.1 →
    pt_trs TS !! j = Some T → at_ags T !! nproc done j = Some agn →
    at_boundary_ad pstep at_boundary ad (pa_st agn).
  Proof.
    intros Hwf Hbs Hinit Hq Hcone Hne HT Hagn.
    destruct (cone_boundary_thm at_boundary ad TS done r j T agn
                Hwf Hbs Hinit Hq Hcone Hne HT Hagn)
      as [Hb|(m & ag & ev & Hn & Hag & Hev & _ & _ & Had)]; [by left|].
    have Hatr : atrace_wf pstep (pt_img TS) (pt_log TS) j T by apply Hwf.
    destruct (asteps_wf_step pstep (pt_img TS) (pt_log TS) j
                (at_ags T) (at_evs T) m ev Hatr Hev)
      as (ag0 & ag0' & st' & f & Hag0 & Hag0' & Hps & _ & ->).
    apply (astep_prog_step pstep dflt) in Hps as (dd & dd' & Hps).
    right. exists (pa_st ag), dd, (ae_lb ev), dd'. split; [|exact Had].
    have Heqag : ag0 = ag by congruence. subst ag0.
    rewrite Hn in Hagn. rewrite Hagn in Hag0'. by simplify_eq.
  Qed.

End cone.

Global Arguments cone_of {P D} _ _ _.

(* ================================================================== *)
(** * §5  THE COMPLETION LEMMAS: THE VIOLATION SURVIVES (obstacle 2) *)

Section persist.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types c : wpcfg P D.

  (** [WeakRobust.violation] with its witness NAMED: message [m] at log
      position [p], authored by [i], observed by [j] at byte [a]. *)
  Definition violates_at c (p : nat) (m : wmsg) (i j : agent) (a : Z) : Prop :=
    pc_log c !! p = Some m ∧ wm_tid m = Some i ∧ cls_of m = SCowned ∧
    ¬ pub_of c (S p) ∧ j ≠ i ∧ is_Some (msg_byte m a) ∧
    (S p ≤ obs_flr c j a)%nat.

  Lemma violates_at_violation c p m i j a :
    violates_at c p m i j a → violation cls_of (pub_of (P:=P) (D:=D)) c.
  Proof. intros (?&?&?&?&?&?&?). by exists p, m, i, j, a. Qed.

  (** Conversely, a violation always HAS such a witness. *)
  Lemma violation_violates_at c :
    violation cls_of (pub_of (P:=P) (D:=D)) c →
    ∃ p m i j a, violates_at c p m i j a.
  Proof. intros (p & m & i & j & a & ?). by exists p, m, i, j, a. Qed.

  (** …and the HART-RESTRICTED violation ([WeakRobust.violation_hart] —
      the form [WeakRobustMain]'s exhibit produces and the one φ can
      refute) has such a witness with BOTH agent indices bounded. *)
  Lemma violation_hart_violates_at nh c :
    violation_hart cls_of (pub_of (P:=P) (D:=D)) nh c →
    ∃ p m i j a, violates_at c p m i j a ∧ (i < nh)%nat ∧ (j < nh)%nat.
  Proof.
    intros (p & m & i & j & a &
            Hlog & Htid & (i' & Hi' & Hilt) &
            Hcls & Hpub & Hne & (j' & Hj' & Hjlt) & Hbyte & Hobs).
    have Hii : i' = i by congruence. subst i'.
    have Hjj : j' = j by congruence. subst j'.
    exists p, m, i, j, a. split_and!; [|done|done].
    by split_and!.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE PERSISTENCE CORE

      Appending to the log and raising floors cannot destroy a
      violation, PROVIDED no appended message PUBLISHES the violating
      one.  [WeakMem.wpublished] is per-author — "a LATER message of the
      SAME agent is release-class" — so it is enough that no appended
      message is both authored by [i] and [WCrel]. *)
  Lemma violates_at_append c c' p m i j a ms :
    pc_log c' = pc_log c ++ ms →
    Forall (λ mq, wm_tid mq ≠ Some i ∨ wm_ak mq ≠ WCrel) ms →
    (obs_flr c j a ≤ obs_flr c' j a)%nat →
    violates_at c p m i j a → violates_at c' p m i j a.
  Proof.
    intros Hlog Hall Hflr (Hp & Htid & Hcls & Hpub & Hne & Hbyte & Hobs).
    have Hplt : (p < length (pc_log c))%nat by eapply lookup_lt_Some.
    have Hp' : pc_log c' !! p = Some m
      by rewrite Hlog lookup_app_l; [lia|exact Hp].
    split_and!; [done|done|done| |done|done|lia].
    intros (p2 & m2 & Heq & Hlog2 & Hwp).
    have Hp2 : p2 = p by lia.
    subst p2. have Hm2 : m2 = m by congruence. subst m2.
    apply Hpub. exists p, m. split_and!; [done|done|].
    rewrite Htid. rewrite Htid in Hwp.
    destruct Hwp as (q & mq & Hle & Hq & Htidq & Hrel).
    exists q, mq. split_and!; [done| |done|done].
    destruct (decide (q < length (pc_log c))%nat) as [Hlt|Hge].
    - rewrite Hlog lookup_app_l in Hq; [lia|exact Hq].
    - exfalso. rewrite Hlog lookup_app_r in Hq; [lia|].
      by destruct (list_relations.Forall_lookup_1 _ _ _ _ Hall Hq).
  Qed.

  (** …hence a violation survives ANY agent's completion, as long as
      that agent is not the violating message's AUTHOR: the appended
      messages are the completing agent's own, and [¬ pub] is
      per-author.  (This is the [nh] conjunct of
      [WeakRobustMain.bad] doing its work one layer up: the author is a
      HART, and the reader — the agent that must be completed, being
      mid-block by necessity — is a DIFFERENT agent.) *)
  Theorem complete_cut_persists k c c' p m i j a :
    rtc (cstep pstep k) c c' → k ≠ i →
    violates_at c p m i j a → violates_at c' p m i j a.
  Proof.
    intros Hrun Hne Hv.
    destruct (csteps_log pstep k c c' Hrun) as (ms & Hlog & Hall).
    eapply (violates_at_append c c' p m i j a ms Hlog).
    - apply list_relations.Forall_lookup_2. intros q mq Hq. left.
      rewrite (list_relations.Forall_lookup_1 _ _ _ _ Hall Hq).
      by intros [= ->].
    - by eapply csteps_obs_flr.
    - exact Hv.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE TWO PACKAGED LEMMAS L3 CONSUMES *)

  (** COMPLETE A CUT AGENT.  Any agent other than the violating
      message's author runs its residual block to the next boundary,
      and the violation survives. *)
  Theorem complete_cut (at_boundary : P → Prop)
      `{!∀ p, Decision (at_boundary p)} (msr : P → nat)
      k c ag p m i j a :
    lts_enabled pstep → blk_fin pstep at_boundary msr →
    img_total (pc_img c) → cfg_bnd c →
    pc_ags c !! k = Some ag → k ≠ i →
    violates_at c p m i j a →
    ∃ c' ag',
      rtc (wp_pf_run pstep) c c' ∧
      pc_ags c' !! k = Some ag' ∧ at_boundary (pa_st ag') ∧
      violates_at c' p m i j a ∧
      pc_img c' = pc_img c ∧ cfg_bnd c' ∧
      length (pc_ags c') = length (pc_ags c) ∧
      (∀ j', j' ≠ k → pc_ags c' !! j' = pc_ags c !! j').
  Proof.
    intros Hen Hfin Hi Hb Hag Hne Hv.
    destruct (complete_block pstep at_boundary msr k c ag Hen Hfin Hi Hb Hag)
      as (c' & ag' & Hrun & Hag' & Hbd).
    exists c', ag'. split_and!.
    - by eapply cstep_rtc_run.
    - exact Hag'.
    - exact Hbd.
    - by eapply complete_cut_persists.
    - by eapply csteps_img.
    - by eapply csteps_bnd.
    - by eapply csteps_ags_len.
    - intros j' Hj'. by eapply csteps_frame.
  Qed.

  (** COMPLETE THE READER.  The reader of the bad message is mid-block
      BY NECESSITY (the exhibit's last step is its read), so this is the
      instance the exhibit always needs.  Its own appends can never be
      the author's publishing [WCrel] store, because [j ≠ i] is a
      conjunct of the violation itself. *)
  Corollary complete_reader (at_boundary : P → Prop)
      `{!∀ p, Decision (at_boundary p)} (msr : P → nat)
      c ag p m i j a :
    lts_enabled pstep → blk_fin pstep at_boundary msr →
    img_total (pc_img c) → cfg_bnd c →
    pc_ags c !! j = Some ag →
    violates_at c p m i j a →
    ∃ c' ag',
      rtc (wp_pf_run pstep) c c' ∧
      pc_ags c' !! j = Some ag' ∧ at_boundary (pa_st ag') ∧
      violates_at c' p m i j a ∧
      pc_img c' = pc_img c ∧ cfg_bnd c' ∧
      length (pc_ags c') = length (pc_ags c) ∧
      (∀ j', j' ≠ j → pc_ags c' !! j' = pc_ags c !! j').
  Proof.
    intros Hen Hfin Hi Hb Hag Hv. have Hv' := Hv.
    destruct Hv' as (_ & _ & _ & _ & Hne & _ & _).
    by eapply (complete_cut at_boundary msr j c ag p m i j a).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** ALL CUT AGENTS AT ONCE

      Completing agent [k] does not move any other agent, so boundaries
      already reached are kept.  [NoDup ks] is what makes the fold
      well-behaved. *)
  Theorem complete_agents (at_boundary : P → Prop)
      `{!∀ p, Decision (at_boundary p)} (msr : P → nat)
      ks c p m i j a :
    lts_enabled pstep → blk_fin pstep at_boundary msr →
    img_total (pc_img c) → cfg_bnd c →
    NoDup ks → (∀ k, k ∈ ks → k ≠ i) →
    violates_at c p m i j a →
    ∃ c',
      rtc (wp_pf_run pstep) c c' ∧
      violates_at c' p m i j a ∧
      pc_img c' = pc_img c ∧ cfg_bnd c' ∧
      length (pc_ags c') = length (pc_ags c) ∧
      (∀ k ag, k ∈ ks → pc_ags c' !! k = Some ag → at_boundary (pa_st ag)) ∧
      (∀ k, k ∉ ks → pc_ags c' !! k = pc_ags c !! k).
  Proof.
    intros Hen Hfin. revert c.
    induction ks as [|k ks IH]; intros c Hi Hb Hnd Hks Hv.
    { exists c. split_and!; [apply rtc_refl|done|done|done|done| |done].
      intros k ag Hk. by apply elem_of_nil in Hk. }
    apply list_relations.NoDup_cons in Hnd as [Hnk Hnd].
    (* step 1: complete [k], if it is an agent at all *)
    destruct (pc_ags c !! k) as [ag|] eqn:Hag; last first.
    { destruct (IH c Hi Hb Hnd ltac:(set_solver) Hv)
        as (c' & Hrun & Hv' & Himg & Hb' & Hlen & Hbd & Hfr).
      exists c'. split_and!; [done|done|done|done|done| |].
      - intros k0 ag0 Hk0 Hag0. apply elem_of_cons in Hk0 as [->|Hk0].
        + rewrite (Hfr k Hnk) Hag in Hag0. by simplify_eq.
        + by eapply Hbd.
      - intros k0 Hk0. apply Hfr. set_solver. }
    destruct (complete_cut at_boundary msr k c ag p m i j a
                Hen Hfin Hi Hb Hag ltac:(apply Hks; set_solver) Hv)
      as (c1 & ag1 & Hrun1 & Hag1 & Hbd1 & Hv1 & Himg1 & Hb1 & Hlen1 & Hfr1).
    (* step 2: complete the rest; [k] does not move again *)
    destruct (IH c1 ltac:(by rewrite Himg1) Hb1 Hnd
                ltac:(intros k0 Hk0; apply Hks; set_solver) Hv1)
      as (c' & Hrun & Hv' & Himg & Hb' & Hlen & Hbd & Hfr).
    exists c'. split_and!.
    - by eapply rtc_transitive.
    - exact Hv'.
    - by rewrite Himg Himg1.
    - exact Hb'.
    - by rewrite Hlen Hlen1.
    - intros k0 ag0 Hk0 Hag0. apply elem_of_cons in Hk0 as [->|Hk0].
      + rewrite (Hfr k Hnk) Hag1 in Hag0. simplify_eq. exact Hbd1.
      + by eapply Hbd.
    - intros k0 Hk0. rewrite (Hfr k0 ltac:(set_solver)).
      apply Hfr1. set_solver.
  Qed.

End persist.

Global Arguments violates_at {P D} _ _ _ _ _.

(* ================================================================== *)
(** * WHAT L3 CONSUMES, AND WHICH OBSTACLE EACH ITEM CLOSES

    Against the lift plan's obstacle list
    ([claude-notes/completed/weak-memory-lift.md]):

    OBSTACLE 1 (granularity — φ is exported at instruction boundaries,
    the exhibit stops at event boundaries):

      - [blk_shape] + [at_boundary_ad]: the block discipline on the
        abstract LTS ([bs_store_last] = STORE-LAST, [bs_ad_rmw] /
        [bs_ad_mid] = the walker A/D CAS as the ONE mid-block write).
        [blk_trace_boundary] is its trace-level reading.  The
        [sail_step] / [sp_m = None] instantiation obligations are listed
        in the header; nothing here imports [WeakSailLTS].
      - [cross_edge_fulfil] (via [gdep2_src_fulfil_or_po]): every cross
        edge of D⁺ emanates from a FULFIL.
      - [cut_last_fulfil]: hence the last processed event of every
        NON-READER agent in the cone is a fulfil.
      - [cone_boundary_thm]: THE CONE-CUT THEOREM — that cut lands at a
        block boundary, or at a mid-block A/D write-back CAS (the second
        disjunct explicitly labelled, per the design).
      - [cone_boundary_sub]: the SUB-BLOCK reading of the same theorem —
        with post-A/D points admitted as boundaries there is only ONE
        disjunct and no completion is needed.

    OBSTACLE 2 (completion admissibility):

      - [img_total] / [img_total_on] ([img_total_on_all] ties them): the
        lift premise, in the simple form, with the ranged form available.
      - [byte_readable_latest]: (i) a read is ALWAYS admissible at the
        byte's latest write ([latest_readable] + the [ws_bounded]
        window), and nothing above it writes the byte — which serves the
        coherent ([lat]) arm and the exclusive window too.
      - [read_latest] / [read_latest_exists] / [read_latest_read_ok] /
        [read_latest_excl_ok]: the contiguous-run form.
      - [cstep_available]: ANY step the program offers can be taken in
        the promise-free machine; [lts_enabled] is the LTS obligation
        (value-input-enabledness).
      - [complete_block]: the residual block runs to its next boundary
        ([blk_fin] = blocks are finite and never stuck).
      - [violates_at_append]: the persistence core — appending and
        raising floors cannot destroy a violation unless an appended
        message PUBLISHES it, and publication is per-author.
      - [complete_cut] / [complete_reader] / [complete_agents]: (ii) the
        packaged lemmas.  [complete_reader] is the exhibit's own case
        (the reader is mid-block by necessity); [complete_agents]
        completes every cut agent at once.

    THE A/D CORNER, EXPLICITLY: BOTH routes are closed here.
    [complete_cut] completes a mid-block A/D cut for every agent EXCEPT
    the violating message's author; [cone_boundary_sub] removes the need
    for any completion at all, including for the author, at the price of
    the sub-block boundary notion the plan already names as the
    fallback.  L3 should take [cone_boundary_sub] for the author and
    [complete_cut] / [complete_agents] for the rest — or take the
    sub-block notion throughout, in which case [complete_*] is only
    needed for the READER.

    OBSTACLE 3 (publication alignment) is L0's and has landed:
    [pub_of] is the log-based [WeakMem.wpublished] and [bad] carries the
    hart-count parameter [nh]; this file's [violates_at] is stated
    against exactly those. *)
