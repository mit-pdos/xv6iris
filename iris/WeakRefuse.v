(** * WeakRefuse.v — THE RE-FUSION SIMULATION (T2 carrier, A2 stage 2)

    Design: [claude-notes/design/weak-memory-srvwmo.md], the "THE T2 CARRIER
    PIPELINE (A2)" block, stage 2; worklist
    [claude-notes/projects/weak-memory-srvwmo.md] (A2).  Stage 1 is
    [WeakErase]; stage 3 is the existing projection
    ([WeakPromiseBridge.wp_pf_bridge_log]).

    THE PROBLEM.  Stage 1 leaves ONE gate: [pstep_fused].  The RMW split
    (R1–R3) made the event instance emit [LExLoad]/[LExStore], and the
    axiomatic tier's alphabet is FUSED ([WeakAxiomatic.LRmw] is one event),
    so a split pair has no per-event axiomatic image and the projection
    refuses the run.

    THE MOVE.  Simulate the split run by a run of the SAME program over the
    FUSED alphabet:

      - an [LExLoad] step becomes an [LSilent] step ([RFDrop]) — the read
        moves to the write's position, so nothing happens here;
      - its [LExStore] becomes ONE [PFRmw] step ([RFFuse]) whose read half
        RE-READS the reservation's timestamps at the write's position, with
        the values the exclusive read saw.

    The log, the image, the fabric and every program state are preserved
    STEP FOR STEP (the simulation is 1:1 — no step is deleted, the read is
    only moved), which is exactly what T2 consumes.  A DANGLING exclusive
    read (the walker's O-FRESH, an AMOCAS mismatch) is simply the case where
    no [RFFuse] ever follows the [RFDrop]: it needs no separate treatment,
    and it is the one deviation from the design block, recorded in §0 below.

    ** §0 DEVIATION: A DANGLING EXCLUSIVE READ PROJECTS TO *NOTHING*, NOT TO
       A PLAIN LOAD

    The design block asks for [LExLoad ↦ LLoad] when the read dangles and
    [LExLoad ↦ deleted] when it pairs.  Deciding which needs LOOKAHEAD (at
    the read's own position the run's future is not available to a forward
    induction), so this file makes the ONE uniform choice that needs none:
    every exclusive read becomes [LSilent].  Consequences, both benign for
    T2 — whose claim is about the LOG:

    - a paired read is projected exactly as intended (it reappears inside
      the [LRmw]); the alternative uniform choice ([LExLoad ↦ LLoad]) is
      strictly worse here, since it would INVENT a duplicate read event
      beside the rmw's own read half;
    - a dangling read loses its axiomatic event.  Nothing is invented, the
      log is identical, and the fused run's agent is left with LOWER views
      than the split run's, which is the ≤-simulation's sound direction.
      Recovering the plain-load projection means either a lookahead
      (materialise the run as a list and transform it with the pairing
      known) or a program-level "this read will pair" predicate.

    ** WHY A PAIRING PREMISE IS UNAVOIDABLE (finding, 2026-08-19)

    Re-fusion is NOT unconditional, and the obstacle is not the class, the
    window or the re-read — those all go through.  It is the READ'S
    POST-VIEW.  The fused read happens at the WRITE's position, so its
    pre-view is the agent's view floor THERE; if the agent raised that floor
    between the pair — one [fence r,r] is enough — the fused rmw's post-view
    STRICTLY EXCEEDS the split run's, and a later read of the fused agent
    can be blocked where the split run's was not.  Concretely
    [lr x; fence rw,rw; sc x] has no fused counterpart with the same
    behaviour: an [amo x] cannot read x before the fence.  No repair is
    available on this side — the fallback "emit a plain [PFStore] instead"
    is refuted by the MESSAGE CLASS (a conditional write is [WCexcl], a
    plain store is not, so the LOGS would differ, and the log is the whole
    content of T2), and "emit the read early, as a plain [PFLoad]" is
    refuted by the same view arithmetic, run at the rmw's re-read.

    The premise is therefore about the PROGRAM: between an exclusive read
    and its conditional write the agent takes only steps that do not move
    its [wstate] — [LSilent] and [LDev].  That is [pstep_paired] below, and
    it is exactly what the instance does: the AMO's and the walker's
    internal steps between the two halves are register writes, control
    resolutions and instruction markers, ALL OF WHICH STAGE 1 HAS ALREADY
    ERASED TO [LSilent].  (This is why stage 2 runs on stage 1's output and
    not on the raw instance: on the raw alphabet the window is full of
    [LRegW]/[LCtrl]/[LInstr] and the premise would be false as stated —
    [LInstr] even CLEARS [w_res], which is also why the erasure must come
    first for the reservation to survive the window at all.  See
    [pstep_paired_erase] for the form a producer states.)

    ** THE STATE RELATION

    [rf_ws wF wS] = [er_ws wF (ws_res_set wS None)] — stage 1's ≤-relation
    against the split state WITH ITS RESERVATION FORGOTTEN.  The forgetting
    is forced, and is the one place this file departs from [WeakErase]: the
    fused run never executes a [PFExLoad], so [w_res] of every fused agent
    is [None] forever, and [er_ws]'s [res_rel] ("wherever the right side
    holds a reservation the left side holds a matching one") is FALSE of the
    pair.  Nothing needs it: [PFExStore] is the only rule that reads
    [w_res], and the fused side never takes it.  Writing the relation as
    [er_ws] at a doctored state — rather than re-proving a reservation-free
    twin of the whole [_er] family — is what keeps this file's ≤-vocabulary
    literally [WeakErase]'s; §1's commutation lemmas are the price, and they
    are conversions.

    ** THE PENDING-PAIR INVARIANT (the last conjunct of [rf_ag])

    Indexed by the PROGRAM's own pending predicate [expend] and by the
    SPLIT agent's reservation — rather than by a mode in the relation, so
    that ABANDONMENT needs no case (after any non-silent step [expend]
    cannot hold, by [pstep_paired]'s second clause, and the obligation is
    vacuous) and so that the INITIAL configuration needs no premise (an
    agent at [ws_init] has [w_res = None], and the obligation is guarded by
    it):

      [∀ aq base tvs R, expend (pa_st agS) aq base tvs →
                        w_res (pa_ws agS) = Some R →
         read_ok_d img log (pa_ws agF) aq false base tvs 0 ∧
         rf_ws (load_post_run_d (pa_ws agF) aq 0 base tvs.*1) (pa_ws agS) ∧
         rv_base R = base ∧ rv_ts R = tvs.*1]

    The four conjuncts are exactly what [PFRmw] needs at the write's
    position and the write itself does not supply:

    - the READ SIDE CONDITION, carried from the exclusive read's own
      [read_ok_d] (weakened to the fused agent's LOWER floors, which is the
      ≤-simulation's direction) and kept alive across FOREIGN appends by
      [WeakPromise.read_ok_d_app] — whose [ws_bounded] premise comes from
      [cfg_wf] of the fused configuration;
    - the POST-STATE ALIGNMENT: the fused side WITH the pending read applied
      is below the split side.  This is where the silent window is spent —
      an [LSilent]/[LDev] step moves neither side's [wstate], so the
      conjunct survives verbatim — and it is the conjunct the counterexample
      above breaks;
    - the RESERVATION's identity, which turns [PFExStore]'s [excl_ok_ts]
      into [PFRmw]'s [excl_ok] on the same timestamps, and its width into
      [length tvs = length data].

    The VALUES are not re-derived at the write: they ride in [tvs]. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakPromise.
From xv6iris Require Import WeakPromiseFact.
From xv6iris Require Import WeakPromiseBridge.
From xv6iris Require Import WeakErase.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. [ws_res_set] commutes with every step function the fused side runs

    All four byte-level ones are CONVERSIONS ([ws_res_set] rebuilds the
    record from projections, so every field but [w_res] reduces away); the
    two run-level ones need the fold's induction.  The store's is stated at
    [None] on purpose: [store_post_d] CLEARS [w_res], so the generic
    commutation is false and the [None] instance is the true one. *)

Lemma ws_res_set_idem ws r1 r2 :
  ws_res_set (ws_res_set ws r1) r2 = ws_res_set ws r2.
Proof. done. Qed.

Lemma ctrl_post_res ws r v :
  ctrl_post (ws_res_set ws r) v = ws_res_set (ctrl_post ws v) r.
Proof. done. Qed.

Lemma load_post_at_res ws r aq vpre a t :
  load_post_at (ws_res_set ws r) aq vpre a t
  = ws_res_set (load_post_at ws aq vpre a t) r.
Proof. done. Qed.

Lemma store_post_d_res ws rl vf a t :
  store_post_d (ws_res_set ws None) rl vf a t
  = ws_res_set (store_post_d ws rl vf a t) None.
Proof. done. Qed.

Lemma fence_post_res ws r pr pw sr sw :
  fence_post (ws_res_set ws r) pr pw sr sw
  = ws_res_set (fence_post ws pr pw sr sw) r.
Proof. done. Qed.

Lemma load_post_fold_res aq vpre ats ws r :
  foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) (ws_res_set ws r) ats
  = ws_res_set (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) r.
Proof.
  revert ws. induction ats as [|a l IH]; intros ws; [done|].
  by rewrite /= load_post_at_res IH.
Qed.

Lemma load_post_run_d_res ws r aq vaddr base ts :
  load_post_run_d (ws_res_set ws r) aq vaddr base ts
  = ws_res_set (load_post_run_d ws aq vaddr base ts) r.
Proof.
  rewrite /load_post_run_d /load_post_bytes_d.
  by rewrite load_post_fold_res ctrl_post_res.
Qed.

Lemma store_post_fold_res rl vf t as_ ws :
  foldl (λ w a, store_post_d w rl vf a t) (ws_res_set ws None) as_
  = ws_res_set (foldl (λ w a, store_post_d w rl vf a t) ws as_) None.
Proof.
  revert ws. induction as_ as [|a l IH]; intros ws; [done|].
  by rewrite /= store_post_d_res IH.
Qed.

Lemma store_post_run_d_res ws rl vaddr vdata base n t :
  store_post_run_d (ws_res_set ws None) rl vaddr vdata base n t
  = ws_res_set (store_post_run_d ws rl vaddr vdata base n t) None.
Proof.
  rewrite /store_post_run_d /store_post_bytes_d.
  by rewrite store_post_fold_res ctrl_post_res.
Qed.

Lemma exload_post_run_d_resN ws aq vaddr base ts :
  ws_res_set (exload_post_run_d ws aq vaddr base ts) None
  = ws_res_set (load_post_run_d ws aq vaddr base ts) None.
Proof. done. Qed.

(* ====================================================================== *)
(** ** 2. [rf_ws]: stage 1's ≤-relation, with the reservation forgotten *)

Definition rf_ws (wF wS : wstate) : Prop := er_ws wF (ws_res_set wS None).

Lemma rf_ws_ws_le wF wS : rf_ws wF wS → ws_le wF wS.
Proof. intros H. exact (er_ws_ws_le _ _ H). Qed.

Lemma rf_ws_relp wF wS : rf_ws wF wS → w_relp wF = w_relp wS.
Proof. intros H. exact (er_ws_relp _ _ H). Qed.

Lemma rf_ws_fwd wF wS : rf_ws wF wS → fwd_le wF wS.
Proof. intros H. exact (er_ws_fwd _ _ H). Qed.

Global Instance rf_ws_refl : Reflexive rf_ws.
Proof.
  intros w. rewrite /rf_ws. split_and!.
  - rewrite /ws_le /ws_res_set /=. split_and!; auto with lia.
  - done.
  - intros aq a t. rewrite /fwd_view /ws_res_set /=. lia.
  - by intros Ri HR.
Qed.

(** The ONE-SIDED step: the split side takes the exclusive read the fused
    side does not, which only RAISES it. *)
Lemma rf_ws_load_r wF wS aq vaddr base ts :
  rf_ws wF wS → rf_ws wF (load_post_run_d wS aq vaddr base ts).
Proof.
  rewrite /rf_ws. intros H. etrans; [exact H|]. split_and!.
  - rewrite /ws_le /ws_res_set /=. by apply (load_post_run_d_le wS).
  - by rewrite /= load_post_run_d_relp.
  - intros aq' a t. rewrite /fwd_view /ws_res_set /= load_post_run_d_fwd. lia.
  - by intros Ri HR.
Qed.

Lemma rf_ws_exload_r wF wS aq vaddr base ts :
  rf_ws wF wS → rf_ws wF (exload_post_run_d wS aq vaddr base ts).
Proof.
  intros H. rewrite /rf_ws exload_post_run_d_resN. by apply rf_ws_load_r.
Qed.

(** The two-sided steps.  The fused side always runs at operand view [0] —
    stage 1's output is dependency-free, so [srcs_view _ [] = 0] BY
    CONVERSION on both sides; the [vaddr]/[vdata] arguments stay general
    because that costs nothing. *)
Lemma rf_ws_load wF wS aq vaddr base ts :
  rf_ws wF wS →
  rf_ws (load_post_run_d wF aq 0%nat base ts)
        (load_post_run_d wS aq vaddr base ts).
Proof.
  intros H. rewrite /rf_ws -load_post_run_d_res.
  by apply load_post_run_d_er0.
Qed.

Lemma rf_ws_load_exload wF wS aq vaddr base ts :
  rf_ws wF wS →
  rf_ws (load_post_run_d wF aq 0%nat base ts)
        (exload_post_run_d wS aq vaddr base ts).
Proof.
  intros H. rewrite /rf_ws exload_post_run_d_resN -load_post_run_d_res.
  by apply load_post_run_d_er0.
Qed.

Lemma rf_ws_store wF wS rl vaddr vdata base n t :
  rf_ws wF wS →
  rf_ws (store_post_run_d wF rl 0%nat 0%nat base n t)
        (store_post_run_d wS rl vaddr vdata base n t).
Proof.
  intros H. rewrite /rf_ws -store_post_run_d_res.
  by apply store_post_run_d_er0.
Qed.

Lemma rf_ws_fence wF wS pr pw sr sw :
  rf_ws wF wS → rf_ws (fence_post wF pr pw sr sw) (fence_post wS pr pw sr sw).
Proof.
  intros H. rewrite /rf_ws -fence_post_res. by apply fence_post_er.
Qed.

(** Readability is ANTI-monotone, so the fused agent's LOWER floors admit
    every timestamp the split agent could read (stage 1's polarity). *)
Lemma read_ok_d_rf img log wF wS aq lat base tvs va :
  rf_ws wF wS → read_ok_d img log wS aq lat base tvs va →
  read_ok_d img log wF aq lat base tvs 0%nat.
Proof. intros H Hr. by eapply read_ok_d_er0; [exact H|exact Hr]. Qed.

(** The reservation's timestamp column carries [excl_ok] back to the pairs
    the fused label rebuilds — the converse of
    [WeakPromise.excl_ok_ts_of_excl_ok]. *)
Lemma excl_ok_of_excl_ok_ts log i base tvs ts :
  excl_ok_ts log i base tvs.*1 ts → excl_ok log i base tvs ts.
Proof.
  intros He j t v Hj. apply (He j t). by rewrite list_lookup_fmap Hj.
Qed.

(* ====================================================================== *)
Section refuse.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).

  (** [expend p aq base tvs] — "the agent's program state [p] has the
      exclusive read [(aq, base, tvs)] in flight".  It is a PARAMETER, not a
      definition: the machine cannot see it ([w_res] carries the timestamps
      but neither the acquire bit, nor the values, nor the fact that the
      window has stayed quiet), and the program is what knows. *)
  Context (expend : P → bool → Z → list (nat * bv 8) → Prop).

  Implicit Types c : wpcfg P D.

  (* -------------------------------------------------------------------- *)
  (** ** 3. The pairing discipline

      Three clauses, all about the PROGRAM.  Together: an exclusive read
      opens a pending window; the window is entered ONLY by such a read and
      survives ONLY [wstate]-inert steps; a conditional write is emitted
      only inside one.  ABANDONMENT needs no clause — the second one simply
      lets [expend] stop holding. *)
  Definition pstep_paired : Prop :=
    (∀ p d aq base tvs asrc p' d',
       pstep p d (LExLoad aq base tvs asrc) p' d' → expend p' aq base tvs) ∧
    (∀ p d l p' d' aq base tvs,
       pstep p d l p' d' → expend p' aq base tvs →
       (∃ asrc, l = LExLoad aq base tvs asrc) ∨
       ((l = LSilent ∨ l = LDev) ∧ expend p aq base tvs)) ∧
    (∀ p d rl base data asrc vsrc p' d',
       pstep p d (LExStore rl base data asrc vsrc) p' d' →
       ∃ aq tvs, expend p aq base tvs).

  (** THE MESSAGE-CLASS PREMISE (stage 2's twin of
      [WeakErase.pcls_erasable]).  The fused run must append the SAME
      message, so the class the agent computes at the REBUILT [LRmw] must be
      the class it computed at the [LExStore] — at a different (lower)
      [wstate], of which [w_relp] equality is all [rf_ws] offers.

      IT IS QUANTIFIED OVER A STEP, not over all program states, and that is
      not cosmetic: the event instance's [pcls_ev] answers [WCexcl] at
      [LRmw] outright but COMPUTES the conditional write's class off the
      monad node ([pnode_wclass]); the two agree exactly where that node is
      a conditional write — i.e. exactly where the [LExStore] step exists.
      An unquantified equation would be FALSE of the instance. *)
  Definition pcls_fusable : Prop :=
    ∀ p d rl base data asrc vsrc p' d' aq tvs wF wS,
      pstep p d (LExStore rl base data asrc vsrc) p' d' →
      w_relp wF = w_relp wS →
      pcls p (LRmw aq rl base tvs data [] []) wF
      = pcls p (LExStore rl base data asrc vsrc) wS.

  (* -------------------------------------------------------------------- *)
  (** ** 4. The fused program LTS

      Same program states, same fabric, same steps — only the ALPHABET
      changes, and only on the two split labels.  [RFFuse] is the one arm
      that reads the program's pending predicate: the rebuilt [LRmw] needs
      the read half's [aq] bit and its values, which the conditional write's
      own label does not carry. *)
  Inductive refuse_pstep (p : P) (d : D) : wlabel → P → D → Prop :=
  | RFKeep l p' d' :
      lb_fused l → pstep p d l p' d' → refuse_pstep p d l p' d'
  | RFDrop aq base tvs asrc p' d' :
      pstep p d (LExLoad aq base tvs asrc) p' d' →
      refuse_pstep p d LSilent p' d'
  | RFFuse aq rl base tvs data asrc vsrc p' d' :
      expend p aq base tvs →
      pstep p d (LExStore rl base data asrc vsrc) p' d' →
      refuse_pstep p d (LRmw aq rl base tvs data [] []) p' d'.

  (** THE GATE, DISCHARGED BY CONSTRUCTION — stage 2's whole content. *)
  Lemma refuse_pstep_fused : pstep_fused refuse_pstep.
  Proof. intros p d l p' d' H. by destruct H. Qed.

  (** Stage 1's gate rides through: the two new labels are operand-free. *)
  Lemma refuse_pstep_depfree :
    pstep_depfree pstep → pstep_depfree refuse_pstep.
  Proof.
    intros Hdf p d l p' d' H. destruct H; [by eapply Hdf|done|by split].
  Qed.

  Lemma refuse_pstep_lat_free :
    (∀ p d l p' d', pstep p d l p' d' → lat_free l) →
    ∀ p d l p' d', refuse_pstep p d l p' d' → lat_free l.
  Proof.
    intros Hlf p d l p' d' H. destruct H; [by eapply Hlf|done|done].
  Qed.

  (* -------------------------------------------------------------------- *)
  (** ** 5. The configuration relation *)

  Definition rf_pend (img : image) (log : list wmsg) (wF wS : wstate)
      (aq : bool) (base : Z) (tvs : list (nat * bv 8)) (R : wresv) : Prop :=
    read_ok_d img log wF aq false base tvs 0%nat ∧
    rf_ws (load_post_run_d wF aq 0%nat base tvs.*1) wS ∧
    rv_base R = base ∧ rv_ts R = tvs.*1.

  Definition rf_ag (img : image) (log : list wmsg) (agF agS : wpagent P)
      : Prop :=
    pa_st agF = pa_st agS ∧ pa_prom agF = pa_prom agS ∧
    rf_ws (pa_ws agF) (pa_ws agS) ∧
    (∀ aq base tvs R, expend (pa_st agS) aq base tvs →
       w_res (pa_ws agS) = Some R →
       rf_pend img log (pa_ws agF) (pa_ws agS) aq base tvs R).

  Definition rf_cfg (cF cS : wpcfg P D) : Prop :=
    pc_img cF = pc_img cS ∧ pc_log cF = pc_log cS ∧ pc_dev cF = pc_dev cS ∧
    length (pc_ags cF) = length (pc_ags cS) ∧
    (∀ i agS, pc_ags cS !! i = Some agS →
       ∃ agF, pc_ags cF !! i = Some agF ∧
              rf_ag (pc_img cF) (pc_log cF) agF agS).

  Lemma rf_cfg_log cF cS : rf_cfg cF cS → pc_log cF = pc_log cS.
  Proof. by intros (_ & ? & _). Qed.

  (** THE INITIAL CONFIGURATION needs no premise about [expend]: an agent at
      [ws_init] holds no reservation, and the pending obligation is guarded
      by one. *)
  Lemma rf_cfg_init img d0 (ps : list P) :
    rf_cfg (wp_init img d0 ps) (wp_init img d0 ps).
  Proof.
    split_and!; [done|done|done|done|].
    intros i agS Hlk. exists agS. split; [done|].
    rewrite list_lookup_fmap in Hlk.
    destruct (ps !! i) as [p|] eqn:Hp; simplify_eq/=.
    split_and!; [done|done|reflexivity|].
    by intros aq base tvs R _ HR.
  Qed.

  (** The pending read side condition survives an append: the read's window
      tops out at the fused agent's own view floors, which [cfg_wf] pins at
      or below the OLD log length. *)
  Lemma rf_ag_app img lg lg' ext agF agS :
    lg' = lg ++ ext → ws_bounded (pa_ws agF) (length lg) →
    rf_ag img lg agF agS → rf_ag img lg' agF agS.
  Proof.
    intros -> Hb (Hst & Hpr & Hws & Hpd). split_and!; [done|done|done|].
    intros aq base tvs R Hex HR.
    destruct (Hpd aq base tvs R Hex HR) as (Hr & Hal & Hrb & Hrts).
    split_and!; [|done|done|done]. by apply read_ok_d_app; [done|lia|].
  Qed.

  (** The one configuration-update lemma every arm uses.  Both sides insert
      at [i], both logs move by the same [ext] ([] on the frozen arms), and
      every OTHER agent rides through by [rf_ag_app]. *)
  Lemma rf_cfg_upd (img : image) (lg lg' ext : list wmsg) (dv : D)
      (agsF agsS : list (wpagent P)) i agF agS st' wF wS pr :
    lg' = lg ++ ext →
    length agsF = length agsS →
    (∀ j agj, agsS !! j = Some agj →
       ∃ agFj, agsF !! j = Some agFj ∧ rf_ag img lg agFj agj ∧
               ws_bounded (pa_ws agFj) (length lg)) →
    agsS !! i = Some agS → agsF !! i = Some agF →
    rf_ws wF wS →
    (∀ aq base tvs R, expend st' aq base tvs → w_res wS = Some R →
       rf_pend img lg' wF wS aq base tvs R) →
    rf_cfg (WPCfg img lg' dv (<[i := WPAgent st' wF pr]> agsF))
           (WPCfg img lg' dv (<[i := WPAgent st' wS pr]> agsS)).
  Proof.
    intros Hext Hlen Hags Hi Hie Hws Hpd.
    pose proof (lookup_lt_Some _ _ _ Hi) as Hlti.
    pose proof (lookup_lt_Some _ _ _ Hie) as Hltie.
    split_and!; [done|done|done| |].
    { rewrite /= !length_insert //. }
    intros j agj Hj. simpl in Hj |- *.
    destruct (decide (j = i)) as [->|Hne].
    - rewrite list_lookup_insert in Hj; [done|]. simplify_eq/=.
      eexists. rewrite list_lookup_insert; [done|]. split; [done|].
      by split_and!.
    - rewrite list_lookup_insert_ne // in Hj.
      destruct (Hags j agj Hj) as (agFj & Hlk & Hrel & Hb).
      exists agFj. rewrite list_lookup_insert_ne //.
      split; [done|]. by eapply rf_ag_app.
  Qed.

  (* ==================================================================== *)
  (** ** 6. THE STEP SIMULATION *)

  Lemma refuse_step i l cS cS' cF :
    pcls_erasable pcls → pcls_fusable → pstep_paired → pstep_depfree pstep →
    cfg_wf cF → rf_cfg cF cS → wp_pf_step pstep pcls i l cS cS' →
    ∃ lF cF', wp_pf_step refuse_pstep pcls i lF cF cF' ∧ rf_cfg cF' cS'.
  Proof.
    intros Hcls Hfus (Hp1 & Hp2 & Hp3) Hdf Hwf Hm Hstep.
    destruct Hm as (Himg & Hlog & Hdev & Hlen & Hags).
    (* the per-agent package every arm feeds to [rf_cfg_upd], already read
       at the SPLIT side's image and log (they are equal) *)
    have Hags' : ∀ j agj, pc_ags cS !! j = Some agj →
       ∃ agFj, pc_ags cF !! j = Some agFj ∧
               rf_ag (pc_img cS) (pc_log cS) agFj agj ∧
               ws_bounded (pa_ws agFj) (length (pc_log cS)).
    { intros j agj Hj. destruct (Hags j agj Hj) as (agFj & Hlk & Hrel).
      rewrite Himg Hlog in Hrel. exists agFj. split_and!; [done|done|].
      rewrite -Hlog. by destruct (Hwf j agFj Hlk). }
    clear Hags.
    destruct Hstep as
      [cS ag st' d' Hlk Hps
      |cS ag aq lat base tvs asrc st' d' Hlk Hps Hr
      |cS ag rl base data asrc vsrc k st' d' Hlk Hps Hnn Hk
      |cS ag aq rl base tvs data asrc vsrc k st' d' Hlk Hps Hnn Hlen' Hr He Hk
      |cS ag pr pw sr sw st' d' Hlk Hps|cS ag st' d' Hlk Hps
      |cS ag rd srcs st' d' Hlk Hps|cS ag srcs st' d' Hlk Hps
      |cS ag st' d' Hlk Hps
      |cS ag aq base tvs asrc st' d' Hlk Hps Hr
      |cS ag rl base data asrc vsrc k R st' d'
         Hlk Hps Hnn Hres Hrb Hrlen He Hk];
      destruct (Hags' i ag Hlk) as (agF & Hlke & (Hst & Hprm & Hws & Hpd) & Hbd);
      try (by destruct (Hdf _ _ _ _ _ Hps)).
    - (* LSilent: the pending window's own step *)
      exists LSilent. eexists. split.
      + apply (PFSilent refuse_pstep pcls i cF agF st' d' Hlke).
        rewrite Hst Hdev. by apply RFKeep.
      + rewrite Himg Hlog Hprm.
        eapply (rf_cfg_upd _ (pc_log cS) _ []);
          [by rewrite app_nil_r|exact Hlen|exact Hags'|exact Hlk|exact Hlke
          |exact Hws|].
        intros aq base tvs R Hex HR.
        destruct (Hp2 _ _ _ _ _ aq base tvs Hps Hex) as [(? & ?)|(_ & Hex0)];
          [done|]. by apply Hpd.
    - (* LLoad *)
      pose proof (Hdf _ _ _ _ _ Hps) as Hd. simpl in Hd. subst asrc.
      exists (LLoad aq lat base tvs []). eexists. split.
      + apply (PFLoad refuse_pstep pcls i cF agF aq lat base tvs [] st' d'
                 Hlke).
        * rewrite Hst Hdev. by apply RFKeep.
        * rewrite Himg Hlog. by eapply read_ok_d_rf; [exact Hws|exact Hr].
      + rewrite Himg Hlog Hprm.
        eapply (rf_cfg_upd _ (pc_log cS) _ []);
          [by rewrite app_nil_r|exact Hlen|exact Hags'|exact Hlk|exact Hlke| |].
        * by apply rf_ws_load.
        * intros aq0 base0 tvs0 R Hex HR.
          destruct (Hp2 _ _ _ _ _ aq0 base0 tvs0 Hps Hex)
            as [(? & Heq)|([Heq|Heq] & _)]; discriminate.
    - (* LStore *)
      pose proof (Hdf _ _ _ _ _ Hps) as Hd. simpl in Hd.
      destruct Hd as [-> ->].
      have Hkk : pcls (pa_st agF) (LStore rl base data [] []) (pa_ws agF) = k.
      { rewrite Hst Hk.
        by apply (Hcls (pa_st ag) (LStore rl base data [] [])),
                 (rf_ws_relp _ _ Hws). }
      exists (LStore rl base data [] []). eexists. split.
      + apply (PFStore refuse_pstep pcls i cF agF rl base data [] [] k st' d'
                 Hlke); [|done|by rewrite Hkk].
        rewrite Hst Hdev. by apply RFKeep.
      + rewrite Himg Hlog Hprm.
        eapply (rf_cfg_upd _ (pc_log cS) _ [WMsg base data (Some i) k]);
          [done|exact Hlen|exact Hags'|exact Hlk|exact Hlke| |].
        * by apply rf_ws_store.
        * intros aq0 base0 tvs0 R Hex HR.
          destruct (Hp2 _ _ _ _ _ aq0 base0 tvs0 Hps Hex)
            as [(? & Heq)|([Heq|Heq] & _)]; discriminate.
    - (* LRmw: already fused *)
      pose proof (Hdf _ _ _ _ _ Hps) as Hd. simpl in Hd.
      destruct Hd as [-> ->].
      have Hkk : pcls (pa_st agF) (LRmw aq rl base tvs data [] []) (pa_ws agF)
                 = k.
      { rewrite Hst Hk.
        by apply (Hcls (pa_st ag) (LRmw aq rl base tvs data [] [])),
                 (rf_ws_relp _ _ Hws). }
      exists (LRmw aq rl base tvs data [] []). eexists. split.
      + apply (PFRmw refuse_pstep pcls i cF agF aq rl base tvs data [] [] k
                 st' d' Hlke); [| |done| | |by rewrite Hkk].
        * rewrite Hst Hdev. by apply RFKeep.
        * done.
        * rewrite Himg Hlog. by eapply read_ok_d_rf; [exact Hws|exact Hr].
        * rewrite Hlog. exact He.
      + rewrite Himg Hlog Hprm.
        eapply (rf_cfg_upd _ (pc_log cS) _ [WMsg base data (Some i) k]);
          [done|exact Hlen|exact Hags'|exact Hlk|exact Hlke| |].
        * apply rf_ws_store. by apply rf_ws_load.
        * intros aq0 base0 tvs0 R Hex HR.
          destruct (Hp2 _ _ _ _ _ aq0 base0 tvs0 Hps Hex)
            as [(? & Heq)|([Heq|Heq] & _)]; discriminate.
    - (* LFence *)
      exists (LFence pr pw sr sw). eexists. split.
      + apply (PFFence refuse_pstep pcls i cF agF pr pw sr sw st' d' Hlke).
        rewrite Hst Hdev. by apply RFKeep.
      + rewrite Himg Hlog Hprm.
        eapply (rf_cfg_upd _ (pc_log cS) _ []);
          [by rewrite app_nil_r|exact Hlen|exact Hags'|exact Hlk|exact Hlke| |].
        * by apply rf_ws_fence.
        * intros aq0 base0 tvs0 R Hex HR.
          destruct (Hp2 _ _ _ _ _ aq0 base0 tvs0 Hps Hex)
            as [(? & Heq)|([Heq|Heq] & _)]; discriminate.
    - (* LDev: the pending window's other step *)
      exists LDev. eexists. split.
      + apply (PFDev refuse_pstep pcls i cF agF st' d' Hlke).
        rewrite Hst Hdev. by apply RFKeep.
      + rewrite Himg Hlog Hprm.
        eapply (rf_cfg_upd _ (pc_log cS) _ []);
          [by rewrite app_nil_r|exact Hlen|exact Hags'|exact Hlk|exact Hlke
          |exact Hws|].
        intros aq base tvs R Hex HR.
        destruct (Hp2 _ _ _ _ _ aq base tvs Hps Hex) as [(? & ?)|(_ & Hex0)];
          [done|]. by apply Hpd.
    - (* LExLoad ↦ LSilent: the pair OPENS *)
      pose proof (Hdf _ _ _ _ _ Hps) as Hd. simpl in Hd. subst asrc.
      exists LSilent. eexists. split.
      + apply (PFSilent refuse_pstep pcls i cF agF st' d' Hlke).
        rewrite Hst Hdev. by eapply RFDrop.
      + rewrite Himg Hlog Hprm.
        eapply (rf_cfg_upd _ (pc_log cS) _ []);
          [by rewrite app_nil_r|exact Hlen|exact Hags'|exact Hlk|exact Hlke| |].
        * by apply rf_ws_exload_r.
        * intros aq0 base0 tvs0 R Hex HR.
          destruct (Hp2 _ _ _ _ _ aq0 base0 tvs0 Hps Hex)
            as [(asrc0 & Heq)|([Heq|Heq] & _)]; [|discriminate|discriminate].
          injection Heq as -> -> ->.
          rewrite exload_post_run_d_res in HR. simplify_eq/=.
          split_and!.
          { by eapply read_ok_d_rf; [exact Hws|exact Hr]. }
          { by apply rf_ws_load_exload. }
          { done. }
          { done. }
    - (* LExStore ↦ LRmw: the pair CLOSES *)
      pose proof (Hdf _ _ _ _ _ Hps) as Hd. simpl in Hd.
      destruct Hd as [-> ->].
      destruct (Hp3 _ _ _ _ _ _ _ _ _ Hps) as (aq & tvs & Hex).
      destruct (Hpd aq base tvs R Hex Hres) as (Hrok & Hal & Hrb' & Hrts').
      have Hkk : pcls (pa_st agF) (LRmw aq rl base tvs data [] []) (pa_ws agF)
                 = k.
      { rewrite Hst Hk. eapply Hfus; [exact Hps|]. by apply rf_ws_relp. }
      exists (LRmw aq rl base tvs data [] []). eexists. split.
      + apply (PFRmw refuse_pstep pcls i cF agF aq rl base tvs data [] [] k
                 st' d' Hlke); [|done| | | |by rewrite Hkk].
        * rewrite Hst Hdev. eapply RFFuse; [exact Hex|exact Hps].
        * by rewrite -Hrlen Hrts' length_fmap.
        * rewrite Himg Hlog. exact Hrok.
        * rewrite Hlog. apply excl_ok_of_excl_ok_ts. by rewrite -Hrts'.
      + rewrite Himg Hlog Hprm.
        eapply (rf_cfg_upd _ (pc_log cS) _ [WMsg base data (Some i) k]);
          [done|exact Hlen|exact Hags'|exact Hlk|exact Hlke| |].
        * by apply rf_ws_store.
        * intros aq0 base0 tvs0 R0 Hex0 HR0.
          destruct (Hp2 _ _ _ _ _ aq0 base0 tvs0 Hps Hex0)
            as [(? & Heq)|([Heq|Heq] & _)]; discriminate.
  Qed.

  (* ==================================================================== *)
  (** ** 7. The run level and the endpoint *)

  Lemma refuse_run_step cF cS cS' :
    pcls_erasable pcls → pcls_fusable → pstep_paired → pstep_depfree pstep →
    cfg_wf cF → no_promises cF → rf_cfg cF cS →
    wp_pf_run pstep pcls cS cS' →
    ∃ cF', wp_pf_run refuse_pstep pcls cF cF' ∧ rf_cfg cF' cS' ∧
           cfg_wf cF' ∧ no_promises cF'.
  Proof.
    intros Hcls Hfus Hpa Hdf Hwf Hnp Hm (i & l & Hs).
    destruct (refuse_step i l cS cS' cF Hcls Hfus Hpa Hdf Hwf Hm Hs)
      as (lF & cF' & Hse & Hm').
    have Hrun : wp_pf_run refuse_pstep pcls cF cF' by exists i, lF.
    destruct (wp_pf_run_rtc_wpstep refuse_pstep pcls cF cF' Hwf Hnp
                (rtc_once _ _ Hrun)) as (_ & Hwf' & Hnp').
    by exists cF'.
  Qed.

  Lemma refuse_rtc cF cS cS' :
    pcls_erasable pcls → pcls_fusable → pstep_paired → pstep_depfree pstep →
    cfg_wf cF → no_promises cF → rf_cfg cF cS →
    rtc (wp_pf_run pstep pcls) cS cS' →
    ∃ cF', rtc (wp_pf_run refuse_pstep pcls) cF cF' ∧ rf_cfg cF' cS'.
  Proof.
    intros Hcls Hfus Hpa Hdf Hwf Hnp Hm Hrun. revert cF Hwf Hnp Hm.
    induction Hrun as [x|x y z Hxy _ IH]; intros cF Hwf Hnp Hm.
    { by exists cF. }
    destruct (refuse_run_step cF x y Hcls Hfus Hpa Hdf Hwf Hnp Hm Hxy)
      as (cF1 & Hs1 & Hm1 & Hwf1 & Hnp1).
    destruct (IH cF1 Hwf1 Hnp1 Hm1) as (cF2 & Hs2 & Hm2).
    exists cF2. split; [|done]. by econstructor.
  Qed.

  (** THE ENDPOINT (stage 2's deliverable).  Every DEPENDENCY-FREE pf run of
      a program that pairs its exclusives is matched, step for step, by a pf
      run of the SAME program over the FUSED alphabet, with the same image,
      THE SAME LOG, the same fabric and the same program states. *)
  Theorem refuse_run img d0 (ps : list P) c :
    pcls_erasable pcls → pcls_fusable → pstep_paired → pstep_depfree pstep →
    rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) c →
    ∃ cF, rtc (wp_pf_run refuse_pstep pcls) (wp_init img d0 ps) cF ∧
          pc_img cF = pc_img c ∧ pc_log cF = pc_log c ∧ pc_dev cF = pc_dev c ∧
          (∀ i agS, pc_ags c !! i = Some agS →
             ∃ agF, pc_ags cF !! i = Some agF ∧ pa_st agF = pa_st agS) ∧
          pstep_fused refuse_pstep ∧ pstep_depfree refuse_pstep.
  Proof.
    intros Hcls Hfus Hpa Hdf Hrun.
    have Hnp : no_promises (wp_init img d0 ps).
    { intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
      destruct (ps !! i) as [p|]; by simplify_eq/=. }
    destruct (refuse_rtc (wp_init img d0 ps) (wp_init img d0 ps) c Hcls Hfus
                Hpa Hdf (cfg_wf_init img d0 ps) Hnp (rf_cfg_init img d0 ps)
                Hrun) as (cF & HrunF & Hm).
    exists cF. split; [done|].
    destruct Hm as (Himg & Hlog & Hdev & _ & Hags).
    split_and!; [done|done|done| |apply refuse_pstep_fused
                |by apply refuse_pstep_depfree].
    intros i agS Hlk. destruct (Hags i agS Hlk) as (agF & Hlke & Hst & _).
    by exists agF.
  Qed.

  (** STAGE 2's PAYOFF: T2 containment for a DEPENDENCY-FREE run that emits
      the SPLIT alphabet.  [wp_pf_bridge_log]'s [pstep_fused] premise — the
      last gate stage 1 left standing — is discharged by construction. *)
  Corollary refuse_bridge_log img d0 (ps : list P) c :
    pcls_erasable pcls → pcls_fusable → pstep_paired → pstep_depfree pstep →
    rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) c →
    ∃ E, exec_wf E ∧ ex_img E = img ∧ ex_log E = pc_log c.
  Proof.
    intros Hcls Hfus Hpa Hdf Hrun.
    destruct (refuse_run img d0 ps c Hcls Hfus Hpa Hdf Hrun)
      as (cF & HrunF & Himg & Hlog & _).
    destruct (wp_pf_bridge_log refuse_pstep pcls img d0 ps cF
                (refuse_pstep_depfree Hdf) refuse_pstep_fused HrunF)
      as (E & HE & HEimg & HElog).
    exists E. split_and!; [done|done|]. by rewrite HElog Hlog.
  Qed.

End refuse.

Global Arguments refuse_pstep {P D} _ _ _ _ _ _ _.
Global Arguments pstep_paired {P D} _ _.
Global Arguments pcls_fusable {P D} _ _.

(* ====================================================================== *)
(** ** 8. THE COMPOSITION: T2 FOR THE DEPENDENCY-CARRYING, SPLIT INSTANCE *)

Section compose.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).
  Context (expend : P → bool → Z → list (nat * bv 8) → Prop).

  (** The pairing discipline is stated on the ERASED LTS (stage 2's input).
      On the raw instance the window between the two halves is full of
      [LRegW]/[LCtrl]/[LInstr]; this lemma is the convenience that lets a
      producer state its discipline over THOSE labels and hand it to
      [t2_bridge].  [lb_win] is "erases to a [wstate]-inert label". *)
  Definition lb_win (l : wlabel) : Prop :=
    erase_lbl l = LSilent ∨ erase_lbl l = LDev.

  Lemma pstep_paired_erase :
    (∀ p d aq base tvs asrc p' d',
       pstep p d (LExLoad aq base tvs asrc) p' d' → expend p' aq base tvs) →
    (∀ p d l p' d' aq base tvs,
       pstep p d l p' d' → expend p' aq base tvs →
       (∃ asrc, l = LExLoad aq base tvs asrc) ∨
       (lb_win l ∧ expend p aq base tvs)) →
    (∀ p d rl base data asrc vsrc p' d',
       pstep p d (LExStore rl base data asrc vsrc) p' d' →
       ∃ aq tvs, expend p aq base tvs) →
    pstep_paired (erase_pstep pstep) expend.
  Proof.
    intros H1 H2 H3. split_and!.
    - intros p d aq base tvs asrc p' d' (l0 & Hl0 & Hs).
      destruct l0; simplify_eq/=. by eapply H1.
    - intros p d l p' d' aq base tvs (l0 & -> & Hs) Hex.
      destruct (H2 p d l0 p' d' aq base tvs Hs Hex)
        as [(asrc & ->)|(Hw & Hex0)].
      + left. by exists [].
      + right. split; [exact Hw|exact Hex0].
    - intros p d rl base data asrc vsrc p' d' (l0 & Hl0 & Hs).
      destruct l0; simplify_eq/=. by eapply H3.
  Qed.

  (** The class premise transfers to the erased LTS: an erased conditional
      write comes from a real one, and [pcls_erasable] absorbs the blanked
      operand lists. *)
  Lemma pcls_fusable_erase :
    pcls_erasable pcls → pcls_fusable pstep pcls →
    pcls_fusable (erase_pstep pstep) pcls.
  Proof.
    intros Her Hfu p d rl base data asrc vsrc p' d' aq tvs wF wS
           (l0 & Hl0 & Hs) Hrelp.
    destruct l0; simplify_eq/=.
    (* the surviving names after [simplify_eq] are the ORIGINAL label's, so
       the pre-erasure label is read off [Hs] rather than spelled out *)
    lazymatch type of Hs with
    | pstep _ _ ?lab _ _ =>
        etrans; [by eapply Hfu|]; symmetry; by apply (Her p lab wS wS)
    end.
  Qed.

  (** T2 FINAL for the dependency-carrying, split-alphabet instance: no
      [pstep_depfree], no [pstep_fused].  Every promise-free run of the real
      program projects to an [exec_wf] axiomatic execution with the SAME
      image and the SAME LOG. *)
  Theorem t2_bridge img d0 (ps : list P) c :
    pcls_erasable pcls → pcls_fusable pstep pcls →
    pstep_paired (erase_pstep pstep) expend →
    rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) c →
    ∃ E, exec_wf E ∧ ex_img E = img ∧ ex_log E = pc_log c.
  Proof.
    intros Hcls Hfus Hpa Hrun.
    destruct (erase_rtc pstep pcls (wp_init img d0 ps) (wp_init img d0 ps) c
                Hcls (er_cfg_init img d0 ps) Hrun) as (ce & Hrune & Hme).
    destruct (refuse_bridge_log (erase_pstep pstep) pcls expend img d0 ps ce
                Hcls (pcls_fusable_erase Hcls Hfus) Hpa
                (erase_pstep_depfree pstep) Hrune)
      as (E & HE & Himg & Hlog).
    exists E. split_and!; [done|done|]. by rewrite Hlog (er_cfg_log _ _ Hme).
  Qed.

End compose.
