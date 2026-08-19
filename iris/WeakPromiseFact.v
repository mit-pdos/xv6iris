(** * WeakPromiseFact.v — the front-loading factorization (M6 W1, slice 2)

    The analog of Promising-ARM's Thm 7.1 ([promising_to_promising_pf],
    PtoPF.v) for [WeakPromise.v]'s native full machine: every run whose
    state steps are LAT-FREE factors as

        (all promise steps) ; (only state steps, against the frozen log)

    with the SAME final configuration — no simulation, no relabelling.
    See [claude-notes/projects/weak-memory-m6.md] W1, the factorization
    bullet, for the design and for why [lat] reads are excluded here
    (a latest read is not stable under appending another agent's promise
    to its byte; the conditional version is W2's job).

    Slice-1 structure note, which is what makes this cheap: appends
    happen ONLY in [WPPromise]; [WPFulfil] and [WPRmw] consume the
    promise set and never append.  So a (state; promise) → (promise;
    state) swap keeps every timestamp fixed, and the state step's side
    conditions survive the END-EXTENSION of the log because [cfg_wf]
    bounds every view by the OLD log length, strictly below the appended
    message's timestamp.

    DEPENDENCY-FREE like its two parents: stdpp, [WeakMem], [WeakPromise].

    THE SHAPE OF THE DEVELOPMENT.  The five non-promise rules of
    [wpstep] are repackaged ONCE as a single-constructor relation
    [wp_astep i l], indexed by the acting agent and the label, whose
    per-label side conditions are collected in [astep_ok] and whose
    effect on the agent record is a pair (a [wstate] function [f], a
    promise to delete [Dl]).  That repackaging is the whole trick: the
    four structural lemmas the factorization needs — shape, log
    extension, other-agent framing, own-promise-set augmentation — then
    have ONE case each instead of five, and every per-rule fact is
    proved once inside [astep_ok_app]. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Side conditions survive an end-extension of the log

    [writes_in_by_app_inv], [read_ok_app] and [excl_ok_app] — the entire
    semantic content of the swap (a message appended ABOVE everything the
    stepping agent can see changes none of its admissibility checks) — moved
    to [WeakPromise.v] with the W4 lift batch, next to the definitions they
    are about.  They are used verbatim below. *)

(* ------------------------------------------------------------------ *)
(** ** Lat-freedom

    A state step is LAT-FREE when its label is not a latest-kind load.
    [LRmw]'s read half is already plain in the rule ([read_ok … false]),
    which is why the rmw — the walker's CAS, the kernel's AMOs — is
    lat-free; the only [lat] users are ifetch and read-only walks. *)
Definition lat_free (l : wlabel) : Prop :=
  match l with
  | LLoad _ lat _ _ _ => lat = false
  | LExLoad _ _ _ _ => True
  | LSilent | LStore _ _ _ _ _ | LRmw _ _ _ _ _ _ _ | LFence _ _ _ _
  | LDev | LRegW _ _ | LCtrl _ | LInstr | LExStore _ _ _ _ _ => True
  end.

Lemma lat_free_rmw aq rl base tvs data asrc vsrc :
  lat_free (LRmw aq rl base tvs data asrc vsrc).
Proof. done. Qed.

(** The three dependency-only labels are lat-free by inspection — they are
    not loads at all. *)
Lemma lat_free_regw rd srcs : lat_free (LRegW rd srcs).
Proof. done. Qed.
Lemma lat_free_ctrl srcs : lat_free (LCtrl srcs).
Proof. done. Qed.
Lemma lat_free_instr : lat_free LInstr.
Proof. done. Qed.

(* ------------------------------------------------------------------ *)
Section fact.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).

  Implicit Types cfg c : wpcfg P D.

  (** [wpcfg] is not a primitive record, so its eta law is a lemma; the
      structural lemmas below produce configurations in projected form
      and this is what puts them back. *)
  Lemma wpcfg_eta c : WPCfg (pc_img c) (pc_log c) (pc_dev c) (pc_ags c) = c.
  Proof. by destruct c. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Splitting [wpstep] into promise steps and state steps *)

  (** The promise step's effect on the promising agent. *)
  Definition prom_add (T : nat) (ag : wpagent P) : wpagent P :=
    WPAgent (pa_st ag) (pa_ws ag) ({[T]} ∪ pa_prom ag).

  (** [WPPromise] alone. *)
  Inductive wp_promise_step : wpcfg P D → wpcfg P D → Prop :=
  | WPPromStep cfg i ag base data k :
      pc_ags cfg !! i = Some ag →
      data ≠ [] →
      wp_promise_step cfg
        (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i) k])
               (pc_dev cfg)
               (<[i := prom_add (S (length (pc_log cfg))) ag]> (pc_ags cfg))).

  (** A state step deletes at most one timestamp from its own promise
      set (the one it fulfils). *)
  Definition prom_del (Dl : option nat) (pr : gset nat) : gset nat :=
    match Dl with None => pr | Some ts => pr ∖ {[ts]} end.

  (** The side conditions of the five non-promise rules, collected by
      label.  [f] is the rule's [wstate] update and [Dl] its promise
      deletion; both are PINNED by the label (the equations below), so
      [astep_ok] is a specification of a partial function of
      [(img, log, i, ag, l)] — that is what lets the structural lemmas
      have one case instead of five. *)
  Definition astep_ok (img : image) (log : list wmsg) (i : agent)
      (ag : wpagent P) (l : wlabel)
      (f : wstate → wstate) (Dl : option nat) : Prop :=
    match l with
    | LSilent => f = id ∧ Dl = None
    | LLoad aq lat base tvs asrc =>
        read_ok_d img log (pa_ws ag) aq lat base tvs
                  (srcs_view (pa_ws ag) asrc) ∧
        (* NOTE the [srcs_view w] under the binder: [f] is APPLIED to the
           replayed [wstate] by [WeakRobustProv.astep_ok_aev_post], so the
           operand views must be read off ITS argument, not off [pa_ws ag].
           At [w = pa_ws ag] this is exactly [WPLoad]'s post-state. *)
        f = (λ w, load_post_run_d w aq (srcs_view w asrc) base (tvs.*1)) ∧
        Dl = None
    | LStore rl base data asrc vsrc =>
        ∃ ts k, ts ∈ pa_prom ag ∧
          log !! (ts - 1)%nat = Some (WMsg base data (Some i) k) ∧
          fulfil_ok_d (pa_ws ag) rl base (length data) ts
            (Nat.max (srcs_view (pa_ws ag) asrc)
                     (srcs_view (pa_ws ag) vsrc)) ∧
          f = (λ w, store_post_run_d w rl (srcs_view w asrc)
                      (srcs_view w vsrc) base (length data) ts) ∧
          Dl = Some ts
    | LRmw aq rl base tvs data asrc vsrc =>
        ∃ ts k, length tvs = length data ∧ ts ∈ pa_prom ag ∧
          log !! (ts - 1)%nat = Some (WMsg base data (Some i) k) ∧
          read_ok_d img log (pa_ws ag) aq false base tvs
                    (srcs_view (pa_ws ag) asrc) ∧
          excl_ok log i base tvs ts ∧
          fulfil_ok_d (load_post_run_d (pa_ws ag) aq
                         (srcs_view (pa_ws ag) asrc) base (tvs.*1))
            rl base (length data) ts
            (Nat.max (Nat.max (srcs_view (pa_ws ag) asrc)
                              (srcs_view (pa_ws ag) vsrc))
                     (ldv_of (pa_ws ag) aq (srcs_view (pa_ws ag) asrc)
                        base (tvs.*1))) ∧
          f = (λ w, store_post_run_d
                      (load_post_run_d w aq (srcs_view w asrc) base (tvs.*1))
                      rl (srcs_view w asrc) (srcs_view w vsrc)
                      base (length data) ts) ∧
          Dl = Some ts
    | LFence pr pw sr sw => f = (λ w, fence_post w pr pw sr sw) ∧ Dl = None
    | LDev => f = id ∧ Dl = None   (* [LSilent]'s twin *)
    | LRegW rd srcs => f = (λ w, regw_post w rd (srcs_view w srcs)) ∧ Dl = None
    | LCtrl srcs => f = (λ w, ctrl_post w (srcs_view w srcs)) ∧ Dl = None
    | LInstr => f = instr_post ∧ Dl = None
    (* THE RMW SPLIT (S2).  [astep_ok] is the SIDE CONDITION OF A MACHINE
       ARM — [wp_astep_wpstep] turns it back into a [wpstep] — so these two
       are [WPExLoad]'s and [WPExStore]'s premises, verbatim. *)
    | LExLoad aq base tvs asrc =>
        read_ok_d img log (pa_ws ag) aq false base tvs
                  (srcs_view (pa_ws ag) asrc) ∧
        f = (λ w, exload_post_run_d w aq (srcs_view w asrc) base (tvs.*1)) ∧
        Dl = None
    | LExStore rl base data asrc vsrc =>
        (* NO plain-store fallback (design §4): the reservation is an
           existential of the SIDE CONDITION, not a disjunct. *)
        ∃ ts k R, ts ∈ pa_prom ag ∧
          log !! (ts - 1)%nat = Some (WMsg base data (Some i) k) ∧
          w_res (pa_ws ag) = Some R ∧
          rv_base R = base ∧ length (rv_ts R) = length data ∧
          excl_ok_ts log i base (rv_ts R) ts ∧
          fulfil_ok_d (pa_ws ag) rl base (length data) ts
            (Nat.max (Nat.max (srcs_view (pa_ws ag) asrc)
                              (srcs_view (pa_ws ag) vsrc))
                     (rv_view R)) ∧
          f = (λ w, store_post_run_d w rl (srcs_view w asrc)
                      (srcs_view w vsrc) base (length data) ts) ∧
          Dl = Some ts
    end.

  (** The five non-promise rules of [wpstep], as ONE relation indexed by
      the acting agent and the label. *)
  Inductive wp_astep (i : agent) (l : wlabel) : wpcfg P D → wpcfg P D → Prop :=
  | WPAStep cfg ag st' d' f Dl :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) l st' d' →
      astep_ok (pc_img cfg) (pc_log cfg) i ag l f Dl →
      wp_astep i l cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (f (pa_ws ag))
                         (prom_del Dl (pa_prom ag))]> (pc_ags cfg))).

  Definition wp_state_step c c' : Prop := ∃ i l, wp_astep i l c c'.

  Definition wp_lf_step c c' : Prop :=
    ∃ i l, lat_free l ∧ wp_astep i l c c'.

  (** A lat-free run step: promise, or lat-free state step. *)
  Definition wp_lf_run c c' : Prop :=
    wp_promise_step c c' ∨ wp_lf_step c c'.

  (* ---------------------------------------------------------------- *)
  (** ** The split is exact: [wpstep = wp_promise_step ∪ wp_state_step] *)

  Lemma wp_promise_step_wpstep c c' :
    wp_promise_step c c' → wpstep pstep c c'.
  Proof. destruct 1. by apply WPPromise. Qed.

  Lemma wp_astep_wpstep i l c c' :
    wp_astep i l c c' → wpstep pstep c c'.
  Proof.
    destruct 1 as [cfg ag st' d' f Dl Hlk Hps Hok].
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc|aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl in Hok.
    - destruct Hok as [-> ->]. by apply WPSilent.
    - destruct Hok as (Hr & -> & ->). by eapply WPLoad.
    - destruct Hok as (ts & k & ? & ? & ? & -> & ->). by eapply WPFulfil.
    - destruct Hok as (ts & k & ? & ? & ? & ? & ? & ? & -> & ->). by eapply WPRmw.
    - destruct Hok as [-> ->]. by apply WPFence.
    - destruct Hok as [-> ->]. by apply WPDev.
    - destruct Hok as [-> ->]. by apply WPRegW.
    - destruct Hok as [-> ->]. by apply WPCtrl.
    - destruct Hok as [-> ->]. by apply WPInstr.
    - destruct Hok as (Hr & -> & ->). by eapply WPExLoad.
    - destruct Hok as (ts & k & R & ? & ? & ? & ? & ? & ? & ? & -> & ->).
      by eapply WPExStore.
  Qed.

  Lemma wp_state_step_wpstep c c' : wp_state_step c c' → wpstep pstep c c'.
  Proof. intros (i & l & ?). by eapply wp_astep_wpstep. Qed.

  Lemma wp_lf_run_wpstep c c' : wp_lf_run c c' → wpstep pstep c c'.
  Proof.
    intros [?|(i & l & _ & ?)].
    - by apply wp_promise_step_wpstep.
    - by eapply wp_astep_wpstep.
  Qed.

  Lemma wp_lf_run_rtc_wpstep c c' :
    rtc wp_lf_run c c' → rtc (wpstep pstep) c c'.
  Proof.
    induction 1 as [|???? _ IH]; [done|].
    econstructor; [by apply wp_lf_run_wpstep|done].
  Qed.

  Lemma wpstep_split c c' :
    wpstep pstep c c' → wp_promise_step c c' ∨ wp_state_step c c'.
  Proof.
    destruct 1.
    - left. by econstructor.
    - right. exists i, LSilent.
      by apply (WPAStep i LSilent cfg ag st' d' id None).
    - right. exists i, (LLoad aq lat base tvs asrc).
      apply (WPAStep i _ cfg ag st' d'
               (λ w, load_post_run_d w aq (srcs_view w asrc) base (tvs.*1))
               None); done.
    - right. exists i, (LStore rl base data asrc vsrc).
      apply (WPAStep i _ cfg ag st' d'
               (λ w, store_post_run_d w rl (srcs_view w asrc)
                       (srcs_view w vsrc) base (length data) ts) (Some ts));
        [done|done|]. by exists ts, k.
    - right. exists i, (LRmw aq rl base tvs data asrc vsrc).
      apply (WPAStep i _ cfg ag st' d'
               (λ w, store_post_run_d
                       (load_post_run_d w aq (srcs_view w asrc) base (tvs.*1))
                       rl (srcs_view w asrc) (srcs_view w vsrc)
                       base (length data) ts) (Some ts));
        [done|done|]. exists ts, k. done.
    - right. exists i, (LFence pr pw sr sw).
      by apply (WPAStep i _ cfg ag st' d' (λ w, fence_post w pr pw sr sw) None).
    - right. exists i, LDev.
      by apply (WPAStep i LDev cfg ag st' d' id None).
    - right. exists i, (LRegW rd srcs).
      by apply (WPAStep i _ cfg ag st' d'
                  (λ w, regw_post w rd (srcs_view w srcs)) None).
    - right. exists i, (LCtrl srcs).
      by apply (WPAStep i _ cfg ag st' d'
                  (λ w, ctrl_post w (srcs_view w srcs)) None).
    - right. exists i, LInstr.
      by apply (WPAStep i LInstr cfg ag st' d' instr_post None).
    - right. exists i, (LExLoad aq base tvs asrc).
      apply (WPAStep i _ cfg ag st' d'
               (λ w, exload_post_run_d w aq (srcs_view w asrc) base (tvs.*1))
               None); done.
    - right. exists i, (LExStore rl base data asrc vsrc).
      apply (WPAStep i _ cfg ag st' d'
               (λ w, store_post_run_d w rl (srcs_view w asrc)
                       (srcs_view w vsrc) base (length data) ts) (Some ts));
        [done|done|]. by exists ts, k, R.
  Qed.

  (** THE LAYER-1 PROGRAM-ALPHABET RESTRICTION.  Two conjuncts; the name
      is historical (it was the first alone).

      (1) LAT-FREEDOM: the program never emits a latest-kind load.  For the
      kernel the [lat] users are instruction fetch and the read-only
      page-table walk (design doc Decision 6); the AMO/CAS path is already
      plain ([WPRmw] reads with [lat = false] and pins its window with
      [excl_ok]), so this conjunct is a statement about ifetch and walks
      only — precisely the surface W2's violation-freedom premise takes
      over.

      (2) PRE-SPLIT ([lb_fused]) — THE RMW SPLIT (S2) RESIDUE, TO DIE AT
      S4.  The MACHINE has full arms for [LExLoad]/[LExStore] (this file's
      [astep_ok] included); what is not yet re-indexed is the ROBUSTNESS
      TOWER above it — the pf REPLAY (`WeakRobustSim.Qinv_step`) needs a
      ts-obliviousness conjunct for the exclusive read and the split form
      of `excl_ok_pf` (whose window straddles two events), which is
      design §8's slice S4.  Rather than gate twenty tower theorems one at
      a time, the restriction rides HERE, on the one alphabet premise
      every one of them already carries; every instance in this tree
      discharges it, since no producer emits the split labels yet.  When
      S4 lands, delete the conjunct and this paragraph. *)
  Definition lat_free_prog : Prop :=
    (∀ p d aq base tvs asrc p' d',
       ¬ pstep p d (LLoad aq true base tvs asrc) p' d') ∧
    (∀ p d l p' d', pstep p d l p' d' → lb_fused l).

  Lemma lat_free_prog_lat p d aq base tvs asrc p' d' :
    lat_free_prog → ¬ pstep p d (LLoad aq true base tvs asrc) p' d'.
  Proof. intros [H _]. exact (H p d aq base tvs asrc p' d'). Qed.

  Lemma lat_free_prog_fused p d l p' d' :
    lat_free_prog → pstep p d l p' d' → lb_fused l.
  Proof. intros [_ H]. exact (H p d l p' d'). Qed.

  Lemma lat_free_prog_step c c' :
    lat_free_prog → wpstep pstep c c' → wp_lf_run c c'.
  Proof.
    intros Hlfp Hstep.
    apply wpstep_split in Hstep as [Hpr|(i & l & Hs)]; [by left|].
    right. exists i, l. split; [|done].
    destruct Hs as [cfg ag st' d' f Dl Hlk Hps Hok].
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc|aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl; [done| |done|done|done|done|done|done|done|done|done].
    destruct lat; [|done]. by destruct (lat_free_prog_lat _ _ _ _ _ _ _ _ Hlfp Hps).
  Qed.

  Lemma lat_free_prog_run c c' :
    lat_free_prog → rtc (wpstep pstep) c c' → rtc wp_lf_run c c'.
  Proof.
    intros Hlfp. induction 1 as [|???? _ IH]; [done|].
    econstructor; [by apply lat_free_prog_step|done].
  Qed.

  (** Well-formedness transports to the split relations. *)
  Lemma cfg_wf_promise_step c c' :
    cfg_wf c → wp_promise_step c c' → cfg_wf c'.
  Proof.
    intros ??. eapply (cfg_wf_step pstep); [done|].
    by apply wp_promise_step_wpstep.
  Qed.

  Lemma cfg_wf_astep i l c c' : cfg_wf c → wp_astep i l c c' → cfg_wf c'.
  Proof.
    intros ??. eapply (cfg_wf_step pstep); [done|].
    by eapply wp_astep_wpstep.
  Qed.

  Lemma cfg_wf_lf_run c c' : cfg_wf c → wp_lf_run c c' → cfg_wf c'.
  Proof.
    intros ??. eapply (cfg_wf_step pstep); [done|].
    by apply wp_lf_run_wpstep.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** The four structural lemmas *)

  (** Inversion for the promise step (both indices are variables, so
      this is the form the swap can [destruct] against). *)
  Lemma wp_promise_step_inv c c' :
    wp_promise_step c c' →
    ∃ j agj base data k,
      pc_ags c !! j = Some agj ∧ data ≠ [] ∧
      c' = WPCfg (pc_img c) (pc_log c ++ [WMsg base data (Some j) k])
             (pc_dev c)
             (<[j := prom_add (S (length (pc_log c))) agj]> (pc_ags c)).
  Proof. destruct 1. eexists _, _, _, _, _. done. Qed.

  (** (L1) SHAPE: a state step freezes the image and the log and rewrites
      exactly its own agent's slot. *)
  Lemma wp_astep_shape i l c c' :
    wp_astep i l c c' →
    ∃ ag ag',
      pc_ags c !! i = Some ag ∧
      pc_img c' = pc_img c ∧ pc_log c' = pc_log c ∧
      pc_ags c' = <[i := ag']> (pc_ags c).
  Proof. destruct 1. eexists _, _. done. Qed.

  Lemma wp_astep_log i l c c' :
    wp_astep i l c c' → pc_log c' = pc_log c.
  Proof. by intros (?&?&?&?&?&?)%wp_astep_shape. Qed.

  (** Inversion for [wp_astep] in the shape a TRACE wants (the record the
      step builds, not just "some [ag']" as in [wp_astep_shape]).  Lifted
      from [WeakRobustTrace] by the W4 batch. *)
  Lemma wp_astep_inv i l c c' :
    wp_astep i l c c' →
    ∃ ag st' d' f Dl,
      pc_ags c !! i = Some ag ∧
      pstep (pa_st ag) (pc_dev c) l st' d' ∧
      astep_ok (pc_img c) (pc_log c) i ag l f Dl ∧
      c' = WPCfg (pc_img c) (pc_log c) d'
             (<[i := WPAgent st' (f (pa_ws ag)) (prom_del Dl (pa_prom ag))]>
                (pc_ags c)).
  Proof. destruct 1. by eexists _, _, _, _, _. Qed.

  (** The state phase runs against a FROZEN log — the property that makes
      PARM's [Machine.state_exec] framing available (see [wp_state_project]
      and the closing comment). *)
  Lemma wp_state_step_log c c' :
    rtc wp_state_step c c' → pc_log c' = pc_log c ∧ pc_img c' = pc_img c.
  Proof.
    induction 1 as [|x y z (i & l & Hs) _ IH]; [done|].
    destruct (wp_astep_shape _ _ _ _ Hs) as (?&?&_&?&?&_).
    destruct IH as [-> ->]. done.
  Qed.

  (** (L2, the semantic core) LOG EXTENSION: a lat-free state step is
      admissible verbatim after a message is appended.  [cfg_wf] is
      load-bearing here — it is what puts the reader's coherence window
      at or below the OLD log length. *)
  Lemma astep_ok_app img log l' i ag lb f Dl :
    ws_bounded (pa_ws ag) (length log) →
    lat_free lb →
    astep_ok img log i ag lb f Dl →
    astep_ok img (log ++ l') i ag lb f Dl.
  Proof.
    intros Hb Hlf.
    destruct lb as [|aq lat base tvs asrc|rl base data asrc vsrc|aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl in Hlf |- *.
    - done.
    - subst lat. intros (Hr & -> & ->). split_and!; [|done|done].
      eapply read_ok_d_app; [done|by apply srcs_view_bounded|done].
    - intros (ts & k & Hin & Hlog & Hful & -> & ->).
      exists ts, k. split_and!; [done| |done|done|done].
      rewrite lookup_app_l; [by eapply lookup_lt_Some|done].
    - intros (ts & k & Hlen & Hin & Hlog & Hr & He & Hful & -> & ->).
      pose proof (lookup_lt_Some _ _ _ Hlog) as Hlt.
      exists ts, k. split_and!; [done|done| | | |done|done|done].
      + rewrite lookup_app_l; [done|done].
      + eapply read_ok_d_app; [done|by apply srcs_view_bounded|done].
      + eapply excl_ok_app; [lia|done].
    - done.
    - done.
    - done.
    - done.
    - done.
    (* THE RMW SPLIT (S2): the exclusive read follows [LLoad]'s bullet at
       [lat = false]; the conditional write follows [LStore]'s, with the
       window carried by [excl_ok_ts_app] instead of [excl_ok_app]. *)
    - intros (Hr & -> & ->). split_and!; [|done|done].
      eapply read_ok_d_app; [done|by apply srcs_view_bounded|done].
    - intros (ts & k & R & Hin & Hlog & Hres & Hrb & Hrlen & He & Hful & -> & ->).
      pose proof (lookup_lt_Some _ _ _ Hlog) as Hlt.
      exists ts, k, R. split_and!; try done.
      + rewrite lookup_app_l; [done|done].
      + eapply excl_ok_ts_app; [lia|done].
  Qed.

  Lemma wp_astep_app i l c c' m :
    cfg_wf c → lat_free l → wp_astep i l c c' →
    wp_astep i l (WPCfg (pc_img c) (pc_log c ++ [m]) (pc_dev c) (pc_ags c))
                 (WPCfg (pc_img c) (pc_log c ++ [m]) (pc_dev c') (pc_ags c')).
  Proof.
    intros Hwf Hlf Hs.
    destruct Hs as [cfg ag st' d' f Dl Hlk Hps Hok]; simpl.
    destruct (Hwf i ag Hlk) as [Hb _].
    apply (WPAStep i l (WPCfg (pc_img cfg) (pc_log cfg ++ [m]) (pc_dev cfg)
                          (pc_ags cfg)) ag st' d' f Dl); [done|done|].
    simpl. by eapply astep_ok_app.
  Qed.

  (** (L3) FRAMING: a state step at [i] does not look at agent [j ≠ i],
      so an arbitrary rewrite of [j]'s slot passes through it. *)
  Lemma wp_astep_frame i l c c' j b :
    i ≠ j → wp_astep i l c c' →
    wp_astep i l (WPCfg (pc_img c) (pc_log c) (pc_dev c) (<[j := b]> (pc_ags c)))
                 (WPCfg (pc_img c) (pc_log c) (pc_dev c') (<[j := b]> (pc_ags c'))).
  Proof.
    intros Hne Hs.
    destruct Hs as [cfg ag st' d' f Dl Hlk Hps Hok]; simpl.
    rewrite -(list_insert_commute _ i j); [done|].
    apply (WPAStep i l (WPCfg (pc_img cfg) (pc_log cfg) (pc_dev cfg)
                          (<[j := b]> (pc_ags cfg))) ag st' d' f Dl);
      [|done|done].
    simpl. by rewrite list_lookup_insert_ne.
  Qed.

  (** (L4) OWN PROMISE SET: adding a FRESH timestamp to the acting
      agent's own promise set passes through a state step — the fulfil's
      deletion targets a promise it already held, so the two set
      operations commute. *)
  Lemma prom_del_add T Dl pr :
    T ∉ pr → (∀ ts, Dl = Some ts → ts ∈ pr) →
    prom_del Dl ({[T]} ∪ pr) = {[T]} ∪ prom_del Dl pr.
  Proof.
    intros HT HD. destruct Dl as [ts|]; [|done].
    specialize (HD ts eq_refl). simpl.
    have Hne : ts ≠ T by intros ->.
    set_solver.
  Qed.

  Lemma astep_ok_prom img log i ag ag' l f Dl :
    pa_ws ag' = pa_ws ag → pa_prom ag ⊆ pa_prom ag' →
    astep_ok img log i ag l f Dl → astep_ok img log i ag' l f Dl.
  Proof.
    intros Hws Hpr.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc|aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl; rewrite ?Hws;
      [done|done| | |done|done|done|done|done|done| ].
    - intros (ts & k & ? & ? & ? & ? & ?). exists ts, k.
      split_and!; [by eapply elem_of_weaken|done|done|done|done].
    - intros (ts & k & ? & ? & ? & ? & ? & ? & ? & ?). exists ts, k.
      split_and!; [done|by eapply elem_of_weaken|done|done|done|done|done|done].
    - (* THE RMW SPLIT (S2): [LStore]'s bullet, one more existential wide *)
      intros (ts & k & R & ? & ? & ? & ? & ? & ? & ? & ? & ?).
      exists ts, k, R.
      split_and!;
        [by eapply elem_of_weaken|done|done|done|done|done|done|done|done].
  Qed.

  Lemma astep_ok_del img log i ag l f Dl ts :
    astep_ok img log i ag l f Dl → Dl = Some ts → ts ∈ pa_prom ag.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc|aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [_ ->].
    - by intros (_ & _ & ->).
    - intros (ts' & k & ? & _ & _ & _ & ->). by intros [= <-].
    - intros (ts' & k & _ & ? & _ & _ & _ & _ & _ & ->). by intros [= <-].
    - by intros [_ ->].
    - by intros [_ ->].
    - by intros [_ ->].
    - by intros [_ ->].
    - by intros [_ ->].
    (* THE RMW SPLIT (S2) *)
    - by intros (_ & _ & ->).
    - intros (ts' & k & R & ? & _ & _ & _ & _ & _ & _ & _ & ->).
      by intros [= <-].
  Qed.

  Lemma wp_astep_prom_add i l c c' T ag ag' :
    pc_ags c !! i = Some ag →
    pc_ags c' !! i = Some ag' →
    T ∉ pa_prom ag →
    wp_astep i l c c' →
    wp_astep i l (WPCfg (pc_img c) (pc_log c) (pc_dev c)
                    (<[i := prom_add T ag]> (pc_ags c)))
                 (WPCfg (pc_img c) (pc_log c) (pc_dev c')
                    (<[i := prom_add T ag']> (pc_ags c))).
  Proof.
    intros Hlk0 Hlk1 HT Hs.
    destruct Hs as [cfg ag0 st' d' f Dl Hlk Hps Hok]; simpl in *.
    have Hlt : (i < length (pc_ags cfg))%nat by eapply lookup_lt_Some.
    have Hag : ag0 = ag by congruence.
    subst ag0.
    rewrite list_lookup_insert in Hlk1; [done|].
    have Hag' : ag' = WPAgent st' (f (pa_ws ag)) (prom_del Dl (pa_prom ag))
      by congruence.
    subst ag'.
    have Hstep :
      wp_astep i l
        (WPCfg (pc_img cfg) (pc_log cfg) (pc_dev cfg)
               (<[i := prom_add T ag]> (pc_ags cfg)))
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (f (pa_ws ag))
                        (prom_del Dl ({[T]} ∪ pa_prom ag))]>
                  (<[i := prom_add T ag]> (pc_ags cfg)))).
    { apply (WPAStep i l (WPCfg (pc_img cfg) (pc_log cfg) (pc_dev cfg)
                            (<[i := prom_add T ag]> (pc_ags cfg)))
               (prom_add T ag) st' d' f Dl).
      - simpl. rewrite list_lookup_insert //.
      - done.
      - simpl. apply (astep_ok_prom _ _ _ ag (prom_add T ag) l f Dl);
          [done|by simpl; set_solver|done]. }
    have Hpd : prom_del Dl ({[T]} ∪ pa_prom ag)
               = {[T]} ∪ prom_del Dl (pa_prom ag).
    { apply prom_del_add; [done|]. intros ts Hts. by eapply astep_ok_del. }
    rewrite Hpd list_insert_insert in Hstep. exact Hstep.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (C) THE SWAP LEMMA

      A lat-free state step followed by a promise step is a promise step
      followed by the SAME state step, reaching the SAME configuration —
      no timestamp moves, because the state step never appends. *)

  Lemma wp_swap i l c1 c2 c3 :
    cfg_wf c1 → lat_free l →
    wp_astep i l c1 c2 → wp_promise_step c2 c3 →
    ∃ c2', wp_promise_step c1 c2' ∧ wp_astep i l c2' c3.
  Proof.
    intros Hwf Hlf Hs Hp.
    destruct (wp_astep_shape _ _ _ _ Hs) as (ag & agn & Hlk & Himg & Hlog & Hags).
    destruct (wp_promise_step_inv _ _ Hp)
      as (j & agj & pb & pd & pk & Hlkj & Hnn & ->).
    destruct (Hwf i ag Hlk) as [Hb Hpw].
    have Hlt : (i < length (pc_ags c1))%nat by eapply lookup_lt_Some.
    have HT : S (length (pc_log c1)) ∉ pa_prom ag.
    { intros Hin. destruct (Hpw _ Hin) as (_ & Hle & _). lia. }
    (* the state step, replayed against the extended log *)
    pose proof (wp_astep_app _ _ _ _ (WMsg pb pd (Some j) pk) Hwf Hlf Hs) as Hs2.
    rewrite Himg Hlog Hags. simpl.
    destruct (decide (i = j)) as [Heq|Hne].
    - (* SAME agent: the promise is fresh, so (∪ then ∖) = (∖ then ∪) *)
      subst j.
      rewrite Hags list_lookup_insert in Hlkj; [done|].
      have Hagj : agj = agn by congruence.
      subst agj.
      exists (WPCfg (pc_img c1) (pc_log c1 ++ [WMsg pb pd (Some i) pk])
                (pc_dev c1)
                (<[i := prom_add (S (length (pc_log c1))) ag]> (pc_ags c1))).
      split.
      { by apply (WPPromStep c1 i ag pb pd pk). }
      rewrite list_insert_insert.
      have Hlk2 : pc_ags (WPCfg (pc_img c1) (pc_log c1 ++ [WMsg pb pd (Some i) pk])
                            (pc_dev c2) (pc_ags c2)) !! i = Some agn.
      { simpl. rewrite Hags list_lookup_insert //. }
      pose proof (wp_astep_prom_add i l
                    (WPCfg (pc_img c1) (pc_log c1 ++ [WMsg pb pd (Some i) pk])
                       (pc_dev c1) (pc_ags c1))
                    (WPCfg (pc_img c1) (pc_log c1 ++ [WMsg pb pd (Some i) pk])
                       (pc_dev c2) (pc_ags c2))
                    (S (length (pc_log c1))) ag agn
                    Hlk Hlk2 HT Hs2) as Hs3.
      by simpl in Hs3.
    - (* DISTINCT agents: the two agent-list inserts commute *)
      rewrite Hags list_lookup_insert_ne in Hlkj; [done|].
      exists (WPCfg (pc_img c1) (pc_log c1 ++ [WMsg pb pd (Some j) pk])
                (pc_dev c1)
                (<[j := prom_add (S (length (pc_log c1))) agj]> (pc_ags c1))).
      split.
      { by apply (WPPromStep c1 j agj pb pd pk). }
      pose proof (wp_astep_frame i l _ _ j
                    (prom_add (S (length (pc_log c1))) agj) Hne Hs2) as Hs3.
      rewrite Hags in Hs3. by simpl in Hs3.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (D) THE FACTORIZATION *)

  (** One lat-free state step bubbles to the END of a whole promise
      phase.  [cfg_wf] is re-established at each intermediate
      configuration by [cfg_wf_promise_step]. *)
  Lemma wp_swap_promises c2 c3 :
    rtc wp_promise_step c2 c3 →
    ∀ i l c1, cfg_wf c1 → lat_free l → wp_astep i l c1 c2 →
    ∃ c2', rtc wp_promise_step c1 c2' ∧ wp_astep i l c2' c3.
  Proof.
    induction 1 as [c|c2 ca c3 Hstep _ IH]; intros i l c1 Hwf Hlf Hs.
    - exists c1. split; [done|done].
    - destruct (wp_swap i l c1 c2 ca Hwf Hlf Hs Hstep) as (d & Hpd & Hsd).
      destruct (IH i l d) as (c2' & Hrun & Hfin);
        [by eapply cfg_wf_promise_step|done|done|].
      exists c2'. split; [|done]. by eapply rtc_l.
  Qed.

  (** THE MAIN THEOREM (PARM Thm 7.1's analog, [promising_to_promising_pf]).
      Every lat-free run factors as a promise phase followed by a state
      phase, with the SAME endpoint. *)
  Theorem wp_front_load c0 c :
    cfg_wf c0 → rtc wp_lf_run c0 c →
    ∃ mid, rtc wp_promise_step c0 mid ∧ rtc wp_lf_step mid c.
  Proof.
    intros Hwf Hrun. induction Hrun as [c|c0 c1 c Hstep Hrun IH].
    - exists c. split; [done|done].
    - destruct (IH ltac:(by eapply cfg_wf_lf_run)) as (mid & Hprom & Hstate).
      destruct Hstep as [Hpr|(i & l & Hlf & Hs)].
      + exists mid. split; [|done]. by eapply rtc_l.
      + destruct (wp_swap_promises _ _ Hprom i l c0 Hwf Hlf Hs)
          as (d & Hprom' & Hsd).
        exists d. split; [done|]. eapply rtc_l; [|done]. by exists i, l.
  Qed.

  (** The same, from a PROGRAM-level hypothesis: for a lat-free program
      EVERY run of the full machine front-loads. *)
  Corollary wp_front_load_prog c0 c :
    lat_free_prog → cfg_wf c0 → rtc (wpstep pstep) c0 c →
    ∃ mid, rtc wp_promise_step c0 mid ∧ rtc wp_lf_step mid c.
  Proof.
    intros Hlfp Hwf Hrun.
    apply wp_front_load; [done|]. by apply lat_free_prog_run.
  Qed.

  (** The behavior-level reading (PARM [Machine.pf_exec]): a lat-free
      behavior of the full machine is a promise phase followed by a
      promise-consuming state phase against the frozen log. *)
  Corollary wp_behavior_front_load img d0 ps c :
    rtc wp_lf_run (wp_init img d0 ps) c → no_promises c →
    ∃ mid,
      rtc wp_promise_step (wp_init img d0 ps) mid ∧
      rtc wp_lf_step mid c ∧
      wp_behavior pstep img d0 ps c.
  Proof.
    intros Hrun Hnp.
    destruct (wp_front_load _ _ (cfg_wf_init img d0 ps) Hrun)
      as (mid & Hprom & Hstate).
    exists mid. split_and!; [done|done|].
    split; [by apply wp_lf_run_rtc_wpstep|done].
  Qed.

  (** THE HEADLINE: every BEHAVIOR of a lat-free program is a promise
      phase followed by a state phase — [wp_behavior]'s [no_promises]
      says the state phase discharges every promise the first phase
      made. *)
  Corollary wp_behavior_factor img d0 ps c :
    lat_free_prog → wp_behavior pstep img d0 ps c →
    ∃ mid,
      rtc wp_promise_step (wp_init img d0 ps) mid ∧ rtc wp_lf_step mid c ∧
      no_promises c.
  Proof.
    intros Hlfp [Hrun Hnp].
    destruct (wp_front_load_prog _ _ Hlfp (cfg_wf_init img d0 ps) Hrun)
      as (mid & Hprom & Hstate).
    exists mid. split_and!; [done|done|done].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (E) DEV-FREE STATE STEPS, AND WHAT STILL COMMUTES

      Before the fabric, state steps of DISTINCT agents commuted outright:
      both freeze the log and rewrite disjoint slots of the agent list, so
      the state phase could be reordered agent-contiguous.  A SHARED
      FABRIC BREAKS THAT — two device accesses of different agents do not
      commute, because the second reads what the first left.  What
      survives is the SCOPED law, and it is the exact scope: two state
      steps of distinct agents commute UNLESS BOTH TOUCH THE FABRIC, i.e.
      as soon as ONE of them is dev-free.

      [wp_afree i l] is the dev-free fragment of [wp_astep i l]: the same
      rule with the program step demanded AT EVERY FABRIC (hence in
      particular fabric-blind) and the fabric carried through unchanged.
      [pdev_ok] is what turns the marker into membership of this
      fragment, and it is the ONLY thing the factorization asks of
      [pdev].

      Everything the old development proved about the state phase —
      per-agent extraction, grouping, [wp_state_exec] — is re-proved here
      over [wp_afree], i.e. it now describes a phase BETWEEN two
      consecutive device events rather than a whole state phase. *)

  (** THE FABRIC-TOUCHING MARKER.  Whether a program step reads or moves the
      shared fabric is NOT decidable from [pstep] (it is a statement about
      [pstep] at every fabric), and the factorization has to CLASSIFY the
      steps of a given run — so the marker is a parameter of the program,
      alongside [pstep], exactly as the worklist's "decidable marker you add
      to the step data" asks.  [pdev p l p' = false] claims the step is
      FABRIC-BLIND AND FABRIC-PRESERVING, which is what [pdev_ok] just below
      pins down and what the commutation lemma consumes.

      Only the factorization needs it; the machine ([WeakPromise.wpstep])
      does not, which is why it enters here and not there. *)
  Context (pdev : P → wlabel → P → bool).

  Definition pdev_ok : Prop :=
    ∀ p d l p' d', pstep p d l p' d' → pdev p l p' = false →
      d' = d ∧ ∀ d0, pstep p d0 l p' d0.

  Inductive wp_afree (i : agent) (l : wlabel) : wpcfg P D → wpcfg P D → Prop :=
  | WPAFree cfg ag st' f Dl :
      pc_ags cfg !! i = Some ag →
      (∀ d, pstep (pa_st ag) d l st' d) →
      astep_ok (pc_img cfg) (pc_log cfg) i ag l f Dl →
      wp_afree i l cfg
        (WPCfg (pc_img cfg) (pc_log cfg) (pc_dev cfg)
               (<[i := WPAgent st' (f (pa_ws ag))
                         (prom_del Dl (pa_prom ag))]> (pc_ags cfg))).

  Lemma wp_afree_astep i l c c' : wp_afree i l c c' → wp_astep i l c c'.
  Proof.
    destruct 1 as [cfg ag st' f Dl Hlk Hps Hok].
    by apply (WPAStep i l cfg ag st' (pc_dev cfg) f Dl).
  Qed.

  Lemma wp_afree_dev i l c c' : wp_afree i l c c' → pc_dev c' = pc_dev c.
  Proof. by destruct 1. Qed.

  (** The MARKER puts a step in the fragment: this is the only place
      [pdev]/[pdev_ok] is consumed. *)
  Lemma wp_astep_afree i l c c' :
    pdev_ok → wp_astep i l c c' →
    (∀ ag ag', pc_ags c !! i = Some ag → pc_ags c' !! i = Some ag' →
       pdev (pa_st ag) l (pa_st ag') = false) →
    wp_afree i l c c'.
  Proof.
    intros Hpok Hs Hm.
    destruct Hs as [cfg ag st' d' f Dl Hlk Hps Haok].
    have Hlt : (i < length (pc_ags cfg))%nat by eapply lookup_lt_Some.
    have Hm' : pdev (pa_st ag) l st' = false.
    { apply (Hm ag (WPAgent st' (f (pa_ws ag)) (prom_del Dl (pa_prom ag))));
        [done|]. simpl. by rewrite list_lookup_insert. }
    destruct (Hpok _ _ _ _ _ Hps Hm') as [-> Hany].
    by apply (WPAFree i l cfg ag st' f Dl).
  Qed.

  Lemma wp_afree_shape i l c c' :
    wp_afree i l c c' →
    ∃ ag ag',
      pc_ags c !! i = Some ag ∧
      pc_img c' = pc_img c ∧ pc_log c' = pc_log c ∧ pc_dev c' = pc_dev c ∧
      pc_ags c' = <[i := ag']> (pc_ags c).
  Proof. destruct 1. eexists _, _. done. Qed.

  (** FRAMING for the dev-free fragment.  It frames the FABRIC as well as
      another agent's slot — that is exactly what fabric-blindness buys,
      and it is what the swap below needs (the commuted step runs at the
      fabric the OTHER step left). *)
  Lemma wp_afree_frame i l c c' j b d :
    i ≠ j → wp_afree i l c c' →
    wp_afree i l (WPCfg (pc_img c) (pc_log c) d (<[j := b]> (pc_ags c)))
                 (WPCfg (pc_img c) (pc_log c) d (<[j := b]> (pc_ags c'))).
  Proof.
    intros Hne Hs.
    destruct Hs as [cfg ag st' f Dl Hlk Hps Hok]; simpl.
    rewrite -(list_insert_commute _ i j); [done|].
    apply (WPAFree i l (WPCfg (pc_img cfg) (pc_log cfg) d
                          (<[j := b]> (pc_ags cfg))) ag st' f Dl);
      [|done|done].
    simpl. by rewrite list_lookup_insert_ne.
  Qed.

  (** THE KEY LEMMA, in its two mixed forms: a dev-free step of agent
      [i1] commutes past an ARBITRARY state step of any other agent [i2],
      in either order.  (The one case NOT covered — both steps
      fabric-touching — is the real obstruction; that is what the global
      device-order witness of [WeakRobustTrace] records instead of
      reordering.) *)
  Lemma wp_afree_astep_comm i1 l1 i2 l2 c1 c2 c3 :
    i1 ≠ i2 →
    wp_afree i1 l1 c1 c2 → wp_astep i2 l2 c2 c3 →
    ∃ c2', wp_astep i2 l2 c1 c2' ∧ wp_afree i1 l1 c2' c3.
  Proof.
    intros Hne Hs1 Hs2.
    destruct (wp_afree_shape _ _ _ _ Hs1)
      as (ag1 & A1 & Hlk1 & Hi1 & Hl1 & Hd1 & Ha1).
    destruct (wp_astep_shape _ _ _ _ Hs2) as (ag2 & A2 & Hlk2 & Hi2 & Hl2 & Ha2).
    have Hne2 : i2 ≠ i1 by congruence.
    pose proof (wp_astep_frame i2 l2 c2 c3 i1 ag1 Hne2 Hs2) as Hf.
    rewrite Ha2 Ha1 in Hf.
    rewrite list_insert_insert (list_insert_id _ _ _ Hlk1) in Hf.
    rewrite (list_insert_commute _ i1 i2) in Hf; [done|].
    rewrite list_insert_insert (list_insert_id _ _ _ Hlk1) in Hf.
    rewrite Hi1 Hl1 Hd1 wpcfg_eta in Hf.
    exists (WPCfg (pc_img c1) (pc_log c1) (pc_dev c3) (<[i2 := A2]> (pc_ags c1))).
    split; [exact Hf|].
    pose proof (wp_afree_frame i1 l1 c1 c2 i2 A2 (pc_dev c3) Hne Hs1) as Hg.
    rewrite Ha1 in Hg.
    rewrite -(wpcfg_eta c3) Hi2 Hl2 Ha2 Hi1 Hl1 Ha1.
    exact Hg.
  Qed.

  Lemma wp_astep_afree_comm i1 l1 i2 l2 c1 c2 c3 :
    i1 ≠ i2 →
    wp_astep i1 l1 c1 c2 → wp_afree i2 l2 c2 c3 →
    ∃ c2', wp_afree i2 l2 c1 c2' ∧ wp_astep i1 l1 c2' c3.
  Proof.
    intros Hne Hs1 Hs2.
    destruct (wp_astep_shape _ _ _ _ Hs1) as (ag1 & A1 & Hlk1 & Hi1 & Hl1 & Ha1).
    destruct (wp_afree_shape _ _ _ _ Hs2)
      as (ag2 & A2 & Hlk2 & Hi2 & Hl2 & Hd2 & Ha2).
    have Hne2 : i2 ≠ i1 by congruence.
    pose proof (wp_afree_frame i2 l2 c2 c3 i1 ag1 (pc_dev c1) Hne2 Hs2) as Hf.
    rewrite Ha2 Ha1 in Hf.
    rewrite list_insert_insert (list_insert_id _ _ _ Hlk1) in Hf.
    rewrite (list_insert_commute _ i1 i2) in Hf; [done|].
    rewrite list_insert_insert (list_insert_id _ _ _ Hlk1) in Hf.
    rewrite Hi1 Hl1 wpcfg_eta in Hf.
    exists (WPCfg (pc_img c1) (pc_log c1) (pc_dev c1) (<[i2 := A2]> (pc_ags c1))).
    split; [exact Hf|].
    pose proof (wp_astep_frame i1 l1 c1 c2 i2 A2 Hne Hs1) as Hg.
    rewrite Ha1 in Hg.
    rewrite -(wpcfg_eta c3) Hd2 Hi2 Hl2 Ha2 Hi1 Hl1 Ha1.
    exact Hg.
  Qed.

  (** THE KEY LEMMA, packaged as the worklist states it: distinct agents,
      at least one step NOT fabric-touching. *)
  Lemma wp_astep_comm i1 l1 i2 l2 c1 c2 c3 :
    i1 ≠ i2 →
    wp_astep i1 l1 c1 c2 → wp_astep i2 l2 c2 c3 →
    wp_afree i1 l1 c1 c2 ∨ wp_afree i2 l2 c2 c3 →
    ∃ c2', wp_astep i2 l2 c1 c2' ∧ wp_astep i1 l1 c2' c3.
  Proof.
    intros Hne Hs1 Hs2 [Hfr|Hfr].
    - destruct (wp_afree_astep_comm i1 l1 i2 l2 c1 c2 c3 Hne Hfr Hs2)
        as (d & ? & ?%wp_afree_astep). by exists d.
    - destruct (wp_astep_afree_comm i1 l1 i2 l2 c1 c2 c3 Hne Hs1 Hfr)
        as (d & ?%wp_afree_astep & ?). by exists d.
  Qed.

  (** Both dev-free: the fragment is closed under the swap, which is what
      the per-agent grouping below iterates. *)
  Lemma wp_afree_comm i1 l1 i2 l2 c1 c2 c3 :
    i1 ≠ i2 →
    wp_afree i1 l1 c1 c2 → wp_afree i2 l2 c2 c3 →
    ∃ c2', wp_afree i2 l2 c1 c2' ∧ wp_afree i1 l1 c2' c3.
  Proof.
    intros Hne Hs1 Hs2.
    destruct (wp_afree_shape _ _ _ _ Hs1)
      as (ag1 & A1 & Hlk1 & Hi1 & Hl1 & Hd1 & Ha1).
    destruct (wp_afree_shape _ _ _ _ Hs2)
      as (ag2 & A2 & Hlk2 & Hi2 & Hl2 & Hd2 & Ha2).
    have Hne2 : i2 ≠ i1 by congruence.
    pose proof (wp_afree_frame i2 l2 c2 c3 i1 ag1 (pc_dev c1) Hne2 Hs2) as Hf.
    rewrite Ha2 Ha1 in Hf.
    rewrite list_insert_insert (list_insert_id _ _ _ Hlk1) in Hf.
    rewrite (list_insert_commute _ i1 i2) in Hf; [done|].
    rewrite list_insert_insert (list_insert_id _ _ _ Hlk1) in Hf.
    rewrite Hi1 Hl1 wpcfg_eta in Hf.
    exists (WPCfg (pc_img c1) (pc_log c1) (pc_dev c1) (<[i2 := A2]> (pc_ags c1))).
    split; [exact Hf|].
    pose proof (wp_afree_frame i1 l1 c1 c2 i2 A2 (pc_dev c1) Hne Hs1) as Hg.
    rewrite Ha1 in Hg.
    rewrite -(wpcfg_eta c3) Hd2 Hd1 Hi2 Hl2 Ha2 Hi1 Hl1 Ha1.
    exact Hg.
  Qed.

  (** One agent's steps, and the steps of a SET of agents — in the
      GENERAL fragment (this is what a per-agent TRACE is built out of;
      no commutation is involved). *)
  Definition wp_astep_of (i : agent) c c' : Prop := ∃ l, wp_astep i l c c'.

  (** The frozen-log / framing facts of a whole phase (the [rtc] form of
      [wp_astep_shape]).  Lifted from [WeakRobustTrace] by the W4 batch. *)
  Lemma astep_of_rtc_frozen i c c' :
    rtc (wp_astep_of i) c c' →
    pc_log c' = pc_log c ∧ pc_img c' = pc_img c ∧
    length (pc_ags c') = length (pc_ags c) ∧
    (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
  Proof.
    induction 1 as [|x y z (l & Hs) _ IH]; [done|].
    destruct (wp_astep_shape i l x y Hs) as (ag & ag' & _ & Hi & Hl & Ha).
    destruct IH as (H1 & H2 & H3 & H4). split_and!.
    - by rewrite H1 Hl.
    - by rewrite H2 Hi.
    - by rewrite H3 Ha length_insert.
    - intros j Hj. by rewrite H4 // Ha list_lookup_insert_ne //.
  Qed.
  Definition wp_asteps_of (Q : agent → Prop) c c' : Prop :=
    ∃ i l, Q i ∧ wp_astep i l c c'.
  Definition wp_astep_other (i : agent) c c' : Prop :=
    wp_asteps_of (λ j, j ≠ i) c c'.

  Lemma wp_asteps_of_mono (Q Q' : agent → Prop) c c' :
    (∀ i, Q i → Q' i) →
    rtc (wp_asteps_of Q) c c' → rtc (wp_asteps_of Q') c c'.
  Proof.
    intros HQ. induction 1 as [|x y z (i & l & ? & ?) _ IH]; [done|].
    eapply rtc_l; [|done]. exists i, l. split; [by apply HQ|done].
  Qed.

  (** Every state step is taken by an agent that EXISTS in the list, and
      the list's length never changes — so a state phase is a run of the
      agents [0 … length (pc_ags c) - 1] and of no others. *)
  Lemma wp_astep_lt i l c c' :
    wp_astep i l c c' → (i < length (pc_ags c))%nat.
  Proof.
    intros (?&?&Hlk&_)%wp_astep_shape. by eapply lookup_lt_Some.
  Qed.

  Lemma wp_astep_ags_length i l c c' :
    wp_astep i l c c' → length (pc_ags c') = length (pc_ags c).
  Proof.
    intros (?&?&_&_&_&->)%wp_astep_shape. by rewrite length_insert.
  Qed.

  Lemma wp_state_step_agents c c' :
    rtc wp_state_step c c' →
    rtc (wp_asteps_of (λ i, (i < length (pc_ags c))%nat)) c c'.
  Proof.
    induction 1 as [|x y z (i & l & Hs) _ IH]; [done|].
    eapply rtc_l.
    { exists i, l. split; [by eapply wp_astep_lt|done]. }
    eapply wp_asteps_of_mono; [|done].
    intros k Hk. rewrite (wp_astep_ags_length _ _ _ _ Hs) in Hk. done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (E') The DEV-FREE phase decomposes per agent

      The old [wp_state_exec] verbatim, with [wp_astep] replaced by
      [wp_afree] throughout: a phase whose every step is dev-free
      reorders agent-contiguous.  In the factorized picture such a phase
      is exactly a SEGMENT BETWEEN two consecutive device events, which
      is the successor of "the state phase is agent-contiguous". *)

  Definition wp_afree_of (i : agent) c c' : Prop := ∃ l, wp_afree i l c c'.
  Definition wp_afrees_of (Q : agent → Prop) c c' : Prop :=
    ∃ i l, Q i ∧ wp_afree i l c c'.
  Definition wp_free_step c c' : Prop := ∃ i l, wp_afree i l c c'.
  Definition wp_afree_other (i : agent) c c' : Prop :=
    wp_afrees_of (λ j, j ≠ i) c c'.

  Lemma wp_afree_of_astep_of i c c' :
    rtc (wp_afree_of i) c c' → rtc (wp_astep_of i) c c'.
  Proof.
    induction 1 as [|x y z (l & Hs) _ IH]; [done|].
    eapply rtc_l; [by exists l; apply wp_afree_astep|done].
  Qed.

  Lemma wp_free_step_state_step c c' :
    rtc wp_free_step c c' → rtc wp_state_step c c'.
  Proof.
    induction 1 as [|x y z (i & l & Hs) _ IH]; [done|].
    eapply rtc_l; [by exists i, l; apply wp_afree_astep|done].
  Qed.

  Lemma wp_afrees_of_mono (Q Q' : agent → Prop) c c' :
    (∀ i, Q i → Q' i) →
    rtc (wp_afrees_of Q) c c' → rtc (wp_afrees_of Q') c c'.
  Proof.
    intros HQ. induction 1 as [|x y z (i & l & ? & ?) _ IH]; [done|].
    eapply rtc_l; [|done]. exists i, l. split; [by apply HQ|done].
  Qed.

  Lemma wp_free_step_agents c c' :
    rtc wp_free_step c c' →
    rtc (wp_afrees_of (λ i, (i < length (pc_ags c))%nat)) c c'.
  Proof.
    induction 1 as [|x y z (i & l & Hs) _ IH]; [done|].
    eapply rtc_l.
    { exists i, l. split; [|done].
      by eapply wp_astep_lt, wp_afree_astep. }
    eapply wp_afrees_of_mono; [|done].
    intros k Hk.
    rewrite (wp_astep_ags_length _ _ _ _ (wp_afree_astep _ _ _ _ Hs)) in Hk.
    done.
  Qed.

  Lemma wp_astep_comm_rtc i c2 c3 :
    rtc (wp_afree_of i) c2 c3 →
    ∀ j l c1, j ≠ i → wp_afree j l c1 c2 →
    ∃ c2', rtc (wp_afree_of i) c1 c2' ∧ wp_afree j l c2' c3.
  Proof.
    induction 1 as [c|c2 ca c3 (l2 & Hstep) _ IH]; intros j l c1 Hne Hs.
    - exists c1. split; [done|done].
    - destruct (wp_afree_comm j l i l2 c1 c2 ca Hne Hs Hstep)
        as (d & Hid & Hjd).
      destruct (IH j l d Hne Hjd) as (c2' & Hrun & Hfin).
      exists c2'. split; [|done]. eapply rtc_l; [by exists l2|done].
  Qed.

  (** The per-agent EXTRACTION: any dev-free phase reorders so that all
      of agent [i]'s steps come first, followed by the steps of the other
      agents — same endpoint. *)
  Lemma wp_project_of Q i c c' :
    rtc (wp_afrees_of Q) c c' →
    ∃ mid, rtc (wp_afree_of i) c mid ∧
           rtc (wp_afrees_of (λ j, Q j ∧ j ≠ i)) mid c'.
  Proof.
    induction 1 as [c|c ca c' (k & l & HQ & Hstep) _ IH].
    - exists c. split; [done|done].
    - destruct IH as (mid & Hi & Hoth).
      destruct (decide (k = i)) as [->|Hne].
      + exists mid. split; [|done]. eapply rtc_l; [by exists l|done].
      + destruct (wp_astep_comm_rtc i _ _ Hi k l c Hne Hstep)
          as (d & Hid & Hkd).
        exists d. split; [done|]. eapply rtc_l; [|done]. by exists k, l.
  Qed.

  Lemma wp_state_project i c c' :
    rtc wp_free_step c c' →
    ∃ mid, rtc (wp_afree_of i) c mid ∧ rtc (wp_afree_other i) mid c'.
  Proof.
    intros Hrun.
    destruct (wp_project_of (λ _, True) i c c') as (mid & Hi & Hoth).
    { eapply wp_afrees_of_mono; [|by apply wp_free_step_agents]. done. }
    exists mid. split; [done|].
    eapply wp_afrees_of_mono; [|done]. by intros ? [_ ?].
  Qed.

  (** The per-agent DECOMPOSITION.  [wp_phases js] is the concatenation,
      in the order of [js], of one [rtc] per agent — PARM's
      [Machine.state_exec] (Promising.v:1758), whose per-thread runs are
      likewise against a single frozen memory ([wp_state_step_log]). *)
  Fixpoint wp_phases (js : list agent) (c c' : wpcfg P D) : Prop :=
    match js with
    | [] => c = c'
    | i :: js' => ∃ mid, rtc (wp_afree_of i) c mid ∧ wp_phases js' mid c'
    end.

  Lemma wp_asteps_of_none Q c c' :
    (∀ i, ¬ Q i) → rtc (wp_afrees_of Q) c c' → c = c'.
  Proof.
    intros HQ. induction 1 as [|x y z (i & l & ? & _) _ IH]; [done|].
    by destruct (HQ i).
  Qed.

  Lemma wp_state_group js :
    ∀ Q c c', (∀ i, Q i → i ∈ js) →
    rtc (wp_afrees_of Q) c c' → wp_phases js c c'.
  Proof.
    induction js as [|i js' IH]; intros Q c c' Hcov Hrun; simpl.
    - eapply wp_asteps_of_none; [|done]. intros k HQ.
      by eapply not_elem_of_nil, Hcov.
    - destruct (wp_project_of Q i c c' Hrun) as (mid & Hi & Hoth).
      exists mid. split; [done|].
      eapply IH; [|done]. intros k [HQ Hne].
      specialize (Hcov k HQ).
      apply elem_of_cons in Hcov as [Hki|Hin]; [|done].
      subst k. by destruct (Hne eq_refl).
  Qed.

  (** THE DEV-FREE-PHASE FORM (the [Machine.state_exec] analog): a
      dev-free phase of a configuration with [n] agents is agent 0's
      whole run, then agent 1's, …, then agent [n-1]'s. *)
  Corollary wp_state_exec c c' :
    rtc wp_free_step c c' →
    wp_phases (seq 0 (length (pc_ags c))) c c'.
  Proof.
    intros Hrun.
    apply (wp_state_group _ (λ i, (i < length (pc_ags c))%nat) c c').
    - intros k Hk. apply elem_of_seq. lia.
    - by apply wp_free_step_agents.
  Qed.

End fact.

Global Arguments wp_promise_step {P D} _ _.
Global Arguments prom_add {P} _ _.
Global Arguments astep_ok {P} _ _ _ _ _ _ _.
Global Arguments wp_astep {P D} _ _ _ _ _.
Global Arguments wp_afree {P D} _ _ _ _ _.
Global Arguments pdev_ok {P D} _ _.
Global Arguments wp_state_step {P D} _ _ _.
Global Arguments wp_free_step {P D} _ _ _.
Global Arguments wp_lf_step {P D} _ _ _.
Global Arguments wp_lf_run {P D} _ _ _.
Global Arguments wp_astep_of {P D} _ _ _ _.
Global Arguments wp_asteps_of {P D} _ _ _ _.
Global Arguments wp_astep_other {P D} _ _ _ _.
Global Arguments wp_afree_of {P D} _ _ _ _.
Global Arguments wp_afrees_of {P D} _ _ _ _.
Global Arguments wp_afree_other {P D} _ _ _ _.
Global Arguments wp_phases {P D} _ _ _ _.

(* ------------------------------------------------------------------ *)
(** ** What slice 3 / W2 inherits, and what is deliberately NOT here

    - The factorization is stated for [rtc wp_lf_run], i.e. runs whose
      state steps are lat-free.  [wp_lf_run_rtc_wpstep] shows such a run
      IS a run of [WeakPromise.wpstep], so nothing is smuggled in; what
      is assumed is only that no [LLoad _ true] occurs.  The
      counterexample the restriction dodges is real and is the reason
      the worklist put the general case in W2: appending another agent's
      promise to byte [a] falsifies [read_ok]'s
      [¬ writes_in log a t (length log)] conjunct for a latest read of
      [a] that has already happened, so THAT state step does not survive
      [astep_ok_app] — see [read_ok_app], which is stated at
      [lat = false] for exactly this reason.  W2's violation-freedom
      premise is what pays for the missing case.

    - The state phase is per-agent ([wp_state_exec]) against a frozen
      log ([wp_state_step_log]), which is the framing PARM's
      [Machine.state_exec] gives its Layer-1 simulation.  The promise
      phase is NOT further analysed here (PARM does not either): a
      promise step's only precondition is that the agent exists. *)
