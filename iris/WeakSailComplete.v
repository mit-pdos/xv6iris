(** * WeakSailComplete.v — the SAIL-LEVEL COMPLETION KIT (lift stage B1+B2)

    Stage B of [claude-notes/projects/weak-memory-lift.md] re-derives the
    φ-consumption inside the minimal-bad-edge exhibit.  Two of its pieces are
    purely local to the Sail LTS and are delivered here:

    (1) the SILENT-EPILOGUE completion ([quiet_complete]): an agent whose
        residual monad is silent-to-[Interface.Ret] runs to an instruction
        boundary APPENDING NOTHING — safe for every agent, including the
        author of the violating message, because the log does not move and
        the agent's coherence floors do not move either;

    (2) the READER-TAIL completion ([tail_complete]): an ARBITRARY shaped
        residual runs to a boundary with FREE read values (under
        [img_total], via [WeakRobustBlocks]'s [read_latest_*]) and CANONICAL
        message classes ([WeakSailLTS2.lbl_class], so [pf_solo]'s
        [cls_canon] holds by construction), appending only messages the
        completing agent itself authored and moving no other agent's slot;

    plus the RUN SURGERY the plan's step 3 needs: a solo silent/fence pf step
    of agent [k] commutes left past any step of another agent
    ([pf_local_commute]), hence a whole quiet epilogue of [k] can be spliced
    back to any earlier point of the run ([pf_run_insert_local]).

    ------------------------------------------------------------------------
    THE WELL-FOUNDEDNESS KIT (§1).  Both completions are inductions on the
    RESIDUAL MONAD, and [WeakRobustBlocks]'s abstract [blk_fin] measure
    ([msr : P → nat]) does not exist for the free monad.  It is not needed:
    [Interface.iMon] is an inductive type whose recursive occurrence sits
    under a function type, so [k v] is a structural subterm of
    [Interface.Next oc k] and the immediate-subterm relation [mchild] is
    well founded by a one-line structural [Fixpoint] ([macc]).  The
    silent-epilogue induction only ever descends to an immediate child;
    the reader-tail induction's FUSED-RMW arm descends through the whole
    [silent_run] window and the [wr_node], so it runs on the TRANSITIVE
    closure [tc mchild] ([msub_wf]).

    ------------------------------------------------------------------------
    TWO PREMISE DEVIATIONS FROM THE STAGE-B SKETCH, both forced and both
    recorded here rather than hidden in a proof.

    (a) [sail_live] (§2).  [sail_shaped] does NOT exclude the model's three
        FAILURE outcomes ([Interface.GenericFail], [Interface.Discard],
        [Interface.ExtraOutcome]): their result types are empty (or
        abstract), so [sail_shaped]'s default arm [∀ r, sail_shaped (k r)]
        is VACUOUSLY true at such a node, while [sail_mstep] has no arm for
        them at all — the agent is stuck and no completion exists.
        [tail_complete] therefore takes [sail_live], a second shape premise
        in exactly the same epistemic slot as [sail_shaped] (a per-
        instruction, decoder-checkable property of the decoded monad,
        declared not proved).  [quiet_tail] excludes the three by hand, so
        [quiet_complete] needs nothing extra.

    (b) The two residual-invariant preservation lemmas (§6) are stated for
        IN-BLOCK steps ([sp_m p ≠ None]).  At a boundary [sail_step_ni]
        loads [next tick], and neither [sail_shaped (next tick)] nor an
        oracle-consistency statement about it is available without a
        hypothesis on [next] itself; the consumers (this file's §7, and
        stage B3/B4) only ever run inside a block.

    (c) AN AUDIT NOTE FOR STAGE B6.  A completion has to CHOOSE a value at
        every [Interface.Choose] node (the LTS's arm is existential in it),
        and the only inhabitant available is [SailStdpp.Values]'
        [choose_type_inhabited].  At [ChooseReal] that is a real number, so
        [quiet_complete] / [tail_complete] and everything above them carry
        Stdlib's [ClassicalDedekindReals.sig_forall_dec] in their
        [Print Assumptions] output.  It is a STDLIB axiom inherited through
        [R], not a project assumption, and it is unavoidable while the choice
        value must be produced rather than supplied; rv64d never emits
        [ChooseReal].  Expect it in the B6 audit list and do not mistake it
        for a lift residue.

    ------------------------------------------------------------------------
    THE INDEX (what stage B3/B4/B5 will name).

      §1  [mchild], [macc], [mchild_wf], [msub_wf] — the [iMon] subterm kit;
          [silent_run_mchild] (the fused window descends).
      §2  [quiet_tail], [sail_live], [psail_quiet], [shaped_res],
          [live_res], [ocons_res].
      §3  [pf_solo_q] (a [pf_solo] step with a quiet label), [qframe] /
          [tframe] and their run forms, [pf_solo_run_bnd].
      §4  [pf_qstep], [pf_unpark] (the parked [fence.tso] half),
          [quiet_step], [quiet_run].
      §5  [quiet_complete_q] / [quiet_complete].
      §6  [amo_reach] (walk the fused window), [sail_shaped_res_step],
          [oracle_consistent_res_step], [sail_live_res_step].
      §7  [bytes_to_word], [pf_lstep]/[pf_sstep]/[pf_rstep] (the canonical-
          class step wrappers), [tail_step], [tail_run], [tail_complete].
      §8  [pf_local_commute], [pf_run_insert_local], and the bridge
          [pf_solo_q_run_quiet_run].

    DEPENDENCIES: [WeakSailLTS]/[WeakSailLTS2] (the LTS, [pf_solo],
    [oracle_consistent]) and [WeakRobustBlocks] ([img_total],
    [read_latest_*], [cfg_bnd], the pf-step frame lemmas).

    NOTE ON NAMES.  [WeakPromise] and [WeakAxiomatic] both export
    [LLoad]/[LStore]/[LFence]/[LRmw]; every occurrence below is QUALIFIED
    [WeakPromise.LLoad] &c., as in [WeakSailLTS.v]. *)
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.
From xv6iris Require Import WeakInterp WeakInterpProj WeakSailLTS WeakSailLTS2.
From xv6iris Require Import WeakRobust WeakRobustBlocks.

Local Open Scope Z_scope.

(** A VALUE FOR EVERY [Interface.Choose].  The completions have to pick one
    (the LTS's [Choose] arm is existential in it); [SailStdpp.Values] proves
    every choose type inhabited.  The instance is named EXPLICITLY rather
    than found by typeclass search because [SailStdpp.Values] may not be
    [Import]ed here — importing it rebinds [++] to [String.append] and
    silently breaks every list append in the file. *)
Definition chosen (ty : Values.ChooseType) : Values.choose_type ty :=
  @inhabitant _ (@Values.choose_type_inhabited ty).

(* ====================================================================== *)
(** ** 1. The [iMon] well-foundedness kit

    [mchild y m] — [y] is an immediate continuation of [m].  [Acc] is in
    [Prop], so the existential in the [Next] arm may be eliminated into it,
    and the recursive call [macc (k v)] is structural: [k] is a subterm of
    [m] and the recursion goes through its function argument. *)

Definition mchild (y m : M unit) : Prop :=
  match m with
  | Interface.Ret _ => False
  | Interface.Next _ k => ∃ v, y = k v
  end.

Fixpoint macc (m : M unit) {struct m} : Acc mchild m.
Proof.
  constructor. intros y Hy. destruct m as [x|T oc k]; cbn in Hy.
  - destruct Hy.
  - destruct Hy as [v ->]. apply macc.
Defined.

Lemma mchild_wf : well_founded mchild.
Proof. exact macc. Qed.

(** The transitive closure of a well-founded relation is well founded.
    (stdpp defines [tc] but proves no well-foundedness lemma for it.) *)
Lemma Acc_tc {A} (R : relation A) (x : A) : Acc R x → Acc (tc R) x.
Proof.
  induction 1 as [x _ IH]. constructor. intros y Hy.
  revert IH. induction Hy as [y z Hyz|y z w Hyz Hzw IHzw]; intros IH.
  - by apply IH.
  - eapply Acc_inv; [by apply IHzw|]. by apply tc_once.
Qed.

Lemma msub_wf : well_founded (tc mchild).
Proof. intros m. apply Acc_tc. apply macc. Qed.

(** One step of the fused-RMW window is one [mchild] descent. *)
Lemma silent1_mchild (a b : M unit * regstate) : silent1 a b → mchild b.1 a.1.
Proof.
  destruct a as [m rs]. rewrite /silent1 /=.
  destruct m as [y|T oc k]; [done|].
  destruct oc; simpl; try done;
    try (by intros ->; simpl; eexists);
    try (by intros [ch ->]; simpl; eexists).
Qed.

Lemma silent_run_mchild (a b : M unit * regstate) :
  silent_run a b → rtc mchild b.1 a.1.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_r; [exact IH|]. by apply silent1_mchild.
Qed.

Lemma tc_rtc_step {A} (R : relation A) (x y z : A) :
  rtc R x y → R y z → tc R x z.
Proof. intros H1 H2. eapply tc_rtc_l; [exact H1|]. by apply tc_once. Qed.

(* ====================================================================== *)
(** ** 2. Quiet tails, and liveness

    [quiet_tail m]: every path of [m] reaches [Interface.Ret] through
    register/trace/choice code and BARRIERS only.  Barriers are admitted
    because they append nothing to the log — a fence emits [LFence] and
    moves only the fencing agent's own views (and may park a second fence,
    which §4 fires).  Memory accesses and the three failure outcomes are
    excluded.

    [sail_live m]: no path of [m] runs into a failure outcome.  See header
    deviation (a): [sail_shaped] does NOT imply this, because the failure
    outcomes' result types are empty and its default arm is then vacuous. *)

Fixpoint quiet_tail (m : M unit) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.MemRead _ _ => λ _, False
       | Interface.MemWrite _ _ => λ _, False
       | Interface.ExtraOutcome _ => λ _, False
       | Interface.GenericFail _ => λ _, False
       | Interface.Discard => λ _, False
       | _ => λ k, ∀ r, quiet_tail (k r)
       end) k
  end.

Fixpoint sail_live (m : M unit) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.ExtraOutcome _ => λ _, False
       | Interface.GenericFail _ => λ _, False
       | Interface.Discard => λ _, False
       | _ => λ k, ∀ r, sail_live (k r)
       end) k
  end.

(** The agent-state readings. *)
Definition psail_quiet (p : psail) : Prop :=
  match sp_m p with None => True | Some m => quiet_tail m end.

Definition shaped_res (p : psail) : Prop :=
  match sp_m p with None => True | Some m => sail_shaped m end.

Definition live_res (p : psail) : Prop :=
  match sp_m p with None => True | Some m => sail_live m end.

Definition ocons_res (p : psail) : Prop :=
  match sp_m p with
  | None => True
  | Some m => ∃ d : dev_state, oracle_consistent d m (sp_dev p)
  end.

(* ====================================================================== *)
(** ** 3. Packaging a step as [pf_solo], and the two frames

    Every completion step below is built by one of five intro lemmas.  The
    two faithfulness side conditions of [WeakSailLTS2.pf_solo] are discharged
    ONCE here: [cls_canon] is VACUOUS whenever the log does not grow (its
    hypothesis [pc_log c' = pc_log c ++ [msg]] is then refutable) and holds by
    CONSTRUCTION at the store/rmw arms because we choose the canonical class
    [lbl_class]; [rmw_tight] is [True] at every label but [LRmw], and at the
    [LRmw] arm it is exactly the [lat := true] read the latest-write
    admissibility of [WeakRobustBlocks] provides anyway. *)

Lemma app_snoc_absurd {A} (l : list A) (x : A) : l = l ++ [x] → False.
Proof.
  intros H. apply (f_equal length) in H. rewrite length_app /= in H. lia.
Qed.

Lemma cls_canon_nolog i l (c c' : wpcfg psail) :
  pc_log c' = pc_log c → cls_canon i l c c'.
Proof.
  intros Hlog ag msg _ Heq. rewrite Hlog in Heq.
  by destruct (app_snoc_absurd _ _ Heq).
Qed.

Lemma coh_fence_post ws pr pw sr sw a :
  coh (fence_post ws pr pw sr sw) a = coh ws a.
Proof. by rewrite /coh /fence_post /=. Qed.

(** A label that appends nothing and reads nothing shared. *)
Definition lbl_quiet (l : wlabel) : Prop :=
  l = WeakPromise.LSilent ∨
  ∃ pr pw sr sw, l = WeakPromise.LFence pr pw sr sw.

Lemma barrier_lbl_quiet b : lbl_quiet (barrier_lbl b).1.
Proof.
  destruct b; simpl; (by left) || (right; by eexists _, _, _, _).
Qed.

(** The QUIET solo step — a [pf_solo] step whose label is quiet.  It is the
    relation the epilogue completion produces, and the one the commutation
    of §8 moves across other agents' steps. *)
Definition pf_solo_q (next : bool → M unit) (i : agent)
    (c c' : wpcfg psail) : Prop :=
  ∃ l, lbl_quiet l ∧ wp_pf_step (sail_step_ni next) i l c c'.

Lemma pf_quiet_nolog next i l c c' :
  lbl_quiet l → wp_pf_step (sail_step_ni next) i l c c' → pc_log c' = pc_log c.
Proof.
  intros Hq Hstep. destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kk st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps]; try done;
    by destruct Hq as [Hx|(?&?&?&?&Hx)]; inversion Hx.
Qed.

Lemma pf_solo_q_solo next i c c' : pf_solo_q next i c c' → pf_solo next i c c'.
Proof.
  intros (l & Hq & Hstep). exists l. split_and!; [exact Hstep| |].
  - apply cls_canon_nolog. exact (pf_quiet_nolog next i l c c' Hq Hstep).
  - destruct Hq as [->|(?&?&?&?&->)]; exact I.
Qed.

(** The FRAME of a quiet run: nothing at all moves except agent [i]'s
    program state and its (view-only) [wstate] — in particular the log, the
    image, every other agent, [i]'s promise set and [i]'s coherence floors
    are literally unchanged. *)
Definition qframe (i : agent) (c c' : wpcfg psail) : Prop :=
  pc_log c' = pc_log c ∧ pc_img c' = pc_img c ∧
  (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j) ∧
  (∀ ag, pc_ags c !! i = Some ag →
     ∃ ag', pc_ags c' !! i = Some ag' ∧ pa_prom ag' = pa_prom ag ∧
            (∀ a, coh (pa_ws ag') a = coh (pa_ws ag) a)).

Lemma qframe_refl i c : qframe i c c.
Proof. split_and!; [done|done|done|]. intros ag Hag. by exists ag. Qed.

Lemma qframe_trans i c1 c2 c3 :
  qframe i c1 c2 → qframe i c2 c3 → qframe i c1 c3.
Proof.
  intros (Hl1 & Hi1 & Hf1 & Ha1) (Hl2 & Hi2 & Hf2 & Ha2).
  split_and!; [by rewrite Hl2|by rewrite Hi2
              |by intros j Hj; rewrite (Hf2 j Hj) (Hf1 j Hj)|].
  intros ag Hag. destruct (Ha1 ag Hag) as (ag1 & Hag1 & Hp1 & Hc1).
  destruct (Ha2 ag1 Hag1) as (ag2 & Hag2 & Hp2 & Hc2).
  exists ag2. split_and!; [done|by rewrite Hp2|]. intros a. by rewrite Hc2.
Qed.

Lemma pf_solo_q_qframe next i c c' : pf_solo_q next i c c' → qframe i c c'.
Proof.
  intros (l & Hq & Hstep).
  destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kk st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps];
    try (by destruct Hq as [Hx|(?&?&?&?&Hx)]; inversion Hx).
  - split_and!; [done|done|by intros j Hj; apply lookup_insert_other|].
    intros ag2 Hag2. simpl in Hag2. rewrite Hlk in Hag2. injection Hag2 as <-.
    eexists. split; [by eapply lookup_insert_at, Hlk|by split].
  - split_and!; [done|done|by intros j Hj; apply lookup_insert_other|].
    intros ag2 Hag2. simpl in Hag2. rewrite Hlk in Hag2. injection Hag2 as <-.
    eexists. split; [by eapply lookup_insert_at, Hlk|].
    split; [done|]. intros a. by rewrite /= coh_fence_post.
Qed.

Lemma pf_solo_q_run_qframe next i c c' :
  rtc (pf_solo_q next i) c c' → qframe i c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply qframe_refl|].
  apply (qframe_trans i x y z); [|exact IH].
  exact (pf_solo_q_qframe next i x y Hxy).
Qed.

Lemma pf_solo_q_run_solo next i c c' :
  rtc (pf_solo_q next i) c c' → rtc (pf_solo next i) c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [exact (pf_solo_q_solo next i x y Hxy)|exact IH].
Qed.

(** The FRAME of an arbitrary solo run: the log grows only by messages this
    agent authored, the image is frozen, every other agent's slot is
    untouched, and no observation floor anywhere goes down. *)
Definition tframe (i : agent) (c c' : wpcfg psail) : Prop :=
  (∃ ms, pc_log c' = pc_log c ++ ms ∧
         Forall (λ mq, wm_tid mq = Some i) ms) ∧
  pc_img c' = pc_img c ∧
  (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j) ∧
  (∀ j a, (obs_flr c j a ≤ obs_flr c' j a)%nat).

Lemma tframe_refl i c : tframe i c c.
Proof.
  split_and!; [|done|done|by intros j a].
  exists []. rewrite app_nil_r. split; [done|constructor].
Qed.

Lemma tframe_trans i c1 c2 c3 :
  tframe i c1 c2 → tframe i c2 c3 → tframe i c1 c3.
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

Lemma qframe_tframe i c c' : qframe i c c' → tframe i c c'.
Proof.
  intros (Hl & Hi & Hf & Ha). split_and!.
  - exists []. rewrite app_nil_r. split; [done|constructor].
  - done.
  - done.
  - intros j a. rewrite /obs_flr.
    destruct (decide (j = i)) as [->|Hne].
    + destruct (pc_ags c !! i) as [ag|] eqn:Hag; [|lia].
      destruct (Ha ag eq_refl) as (ag' & Hag' & _ & Hcoh).
      rewrite Hag' Hcoh. lia.
    + rewrite (Hf j Hne). lia.
Qed.

Lemma pf_solo_tframe next i c c' : pf_solo next i c c' → tframe i c c'.
Proof.
  intros (l & Hstep & _ & _).
  destruct (wp_pf_step_shape (sail_step_ni next) i l c c' Hstep)
    as (Himg & _ & (ms & Hlog & Hall)).
  split_and!; [by exists ms|done| |].
  - intros j Hj. exact (wp_pf_step_frame (sail_step_ni next) i l c c' j Hstep Hj).
  - intros j a. exact (wp_pf_step_obs_flr (sail_step_ni next) i l c c' j a Hstep).
Qed.

Lemma pf_solo_run_tframe next i c c' :
  rtc (pf_solo next i) c c' → tframe i c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply tframe_refl|].
  apply (tframe_trans i x y z); [|exact IH].
  exact (pf_solo_tframe next i x y Hxy).
Qed.

Lemma pf_solo_run_bnd next i c c' :
  rtc (pf_solo next i) c c' → cfg_bnd c → cfg_bnd c'.
Proof.
  induction 1 as [|x y z (l & Hxy & _ & _) _ IH]; [by intros Hb|].
  intros Hb. apply IH. exact (wp_pf_step_bnd (sail_step_ni next) i l x y Hxy Hb).
Qed.

(* ====================================================================== *)
(** ** 4. The completion, agent by agent

    Everything below is parametric in the instruction generator [next], as
    [WeakSailLTS]'s bracket is. *)

Section complete.
  Context (next : bool → M unit).

  Implicit Types c : wpcfg psail.

  (** A record with its fence field known to be [None] is its own
      eta-expansion — the shape the completions carry along. *)
  Lemma psail_eta (p : psail) :
    sp_fence p = None →
    p = PSail (sp_m p) (sp_regs p) (sp_dev p) None (sp_irq p).
  Proof. destruct p; simpl; by intros ->. Qed.

  (** ONE QUIET STEP, packaged.  This is the only place the [wp_pf_step]
      constructors are applied for a silent or fence label. *)
  Lemma pf_qstep (i : agent) c ag (l : wlabel) (st' : psail) :
    pc_ags c !! i = Some ag → lbl_quiet l →
    sail_step_ni next (pa_st ag) l st' →
    ∃ c' ag', pf_solo_q next i c c' ∧ pc_ags c' !! i = Some ag' ∧
              pa_st ag' = st'.
  Proof.
    intros Hlk Hq Hstep. destruct Hq as [->|(pr & pw & sr & sw & ->)].
    - exists (WPCfg (pc_img c) (pc_log c)
               (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags c))),
             (WPAgent st' (pa_ws ag) (pa_prom ag)).
      split_and!; [|exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
      exists WeakPromise.LSilent. split; [by left|].
      exact (PFSilent (sail_step_ni next) i c ag st' Hlk Hstep).
    - exists (WPCfg (pc_img c) (pc_log c)
               (<[i := WPAgent st' (fence_post (pa_ws ag) pr pw sr sw)
                         (pa_prom ag)]> (pc_ags c))),
             (WPAgent st' (fence_post (pa_ws ag) pr pw sr sw) (pa_prom ag)).
      split_and!; [|exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
      exists (WeakPromise.LFence pr pw sr sw).
      split; [right; by eexists _, _, _, _|].
      exact (PFFence (sail_step_ni next) i c ag pr pw sr sw st' Hlk Hstep).
  Qed.

  (** THE PARKED FENCE (WeakSailLTS delta (c)).  While [sp_fence] is set no
      other arm may fire, so every completion starts by firing it; it is one
      quiet step and it moves NO coherence floor ([fence_post] does not touch
      [w_coh]). *)
  Lemma pf_unpark (i : agent) c ag :
    pc_ags c !! i = Some ag →
    ∃ c' ag', rtc (pf_solo_q next i) c c' ∧ pc_ags c' !! i = Some ag' ∧
      pa_st ag' = PSail (sp_m (pa_st ag)) (sp_regs (pa_st ag))
                        (sp_dev (pa_st ag)) None (sp_irq (pa_st ag)).
  Proof.
    intros Hlk. destruct (sp_fence (pa_st ag)) as [[[[pr pw] sr] sw]|] eqn:Hf.
    - destruct (pf_qstep i c ag (WeakPromise.LFence pr pw sr sw)
                  (PSail (sp_m (pa_st ag)) (sp_regs (pa_st ag))
                     (sp_dev (pa_st ag)) None (sp_irq (pa_st ag)))
                  Hlk ltac:(right; by eexists _, _, _, _)
                  ltac:(rewrite /sail_step_ni Hf; by split))
        as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
      exists c1, ag1. split_and!; [by apply rtc_once|exact Hlk1|exact Hpa1].
    - exists c, ag. split_and!; [apply rtc_refl|exact Hlk|by apply psail_eta].
  Qed.

  (** *** One step of a quiet tail

      Off [Interface.Ret], a quiet residual always HAS a step, that step is
      quiet (silent, or the fence a barrier emits), it descends to an
      immediate continuation which is itself quiet, and it leaves the
      registers/oracles alone up to the value it just computed.  A barrier
      may PARK a second fence ([fo]); §4's [pf_unpark] fires it. *)
  Lemma quiet_step (m : M unit) rs d iq :
    quiet_tail m →
    (∃ y, m = Interface.Ret y) ∨
    ∃ (l : wlabel) (m' : M unit) (rs' : regstate)
      (fo : option (bool * bool * bool * bool)),
      sail_step_ni next (PSail (Some m) rs d None iq) l
                   (PSail (Some m') rs' d fo iq) ∧
      lbl_quiet l ∧ mchild m' m ∧ quiet_tail m'.
  Proof.
    intros Hq. destruct m as [y|T oc k]; [left; by exists y|]. right.
    destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                   |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hq;
      try (by destruct Hq);
      try (by do 4 eexists;
             split_and!;
               [rewrite /sail_step_ni /=; by split
               |by left|by eexists|by apply Hq]).
    - (* Barrier: the label table, and the possible parked second fence *)
      exists (barrier_lbl bk).1, (k tt), rs, (barrier_lbl bk).2.
      split_and!; [rewrite /sail_step_ni /=; by split
                  |by apply barrier_lbl_quiet|by eexists|by apply Hq].
    - (* Choose: any inhabitant will do *)
      exists WeakPromise.LSilent, (k (chosen ty)), rs, None.
      split_and!; [rewrite /sail_step_ni /=; split;
                     [reflexivity|by exists (chosen ty)]
                  |by left|by eexists|by apply Hq].
  Qed.

  (** *** The silent-epilogue run

      [m] is silent-to-[Interface.Ret]; the agent runs to the boundary by
      quiet steps alone.  The induction is on [mchild] — every quiet step
      descends to an immediate continuation. *)
  Lemma quiet_run : ∀ (m : M unit),
    quiet_tail m →
    ∀ (i : agent) c ag rs d iq,
      pc_ags c !! i = Some ag → pa_st ag = PSail (Some m) rs d None iq →
      ∃ c' ag', rtc (pf_solo_q next i) c c' ∧ pc_ags c' !! i = Some ag' ∧
                sp_m (pa_st ag') = None ∧ sp_fence (pa_st ag') = None.
  Proof.
    intros m. induction m as [m IH] using (well_founded_ind mchild_wf).
    intros Hq i c ag rs d iq Hlk Hst.
    destruct (quiet_step m rs d iq Hq)
      as [[y ->]|(l & m' & rs' & fo & Hstep & Hql & Hch & Hq')].
    - destruct (pf_qstep i c ag WeakPromise.LSilent
                  (PSail None rs d None iq) Hlk (or_introl eq_refl)
                  ltac:(rewrite Hst /sail_step_ni /=; by split))
        as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
      exists c1, ag1. split_and!;
        [by apply rtc_once|exact Hlk1|by rewrite Hpa1|by rewrite Hpa1].
    - destruct (pf_qstep i c ag l (PSail (Some m') rs' d fo iq) Hlk Hql
                  ltac:(rewrite Hst; exact Hstep))
        as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
      destruct (pf_unpark i c1 ag1 Hlk1) as (c2 & ag2 & Hs2 & Hlk2 & Hpa2).
      rewrite Hpa1 /= in Hpa2.
      destruct (IH m' Hch Hq' i c2 ag2 _ _ _ Hlk2 Hpa2)
        as (c3 & ag3 & Hs3 & Hlk3 & Hm3 & Hf3).
      exists c3, ag3. split_and!; [|exact Hlk3|exact Hm3|exact Hf3].
      eapply rtc_l; [exact Hs1|]. by etrans; [exact Hs2|exact Hs3].
  Qed.

  (* ==================================================================== *)
  (** ** 5. EPILOGUE COMPLETION *)

  (** The quiet form, which is what the run surgery of §8 splices. *)
  Theorem quiet_complete_q (i : agent) c ag :
    pc_ags c !! i = Some ag → psail_quiet (pa_st ag) →
    ∃ c' ag',
      rtc (pf_solo_q next i) c c' ∧ qframe i c c' ∧
      pc_ags c' !! i = Some ag' ∧ at_boundary i c' ∧
      sp_m (pa_st ag') = None ∧ sp_fence (pa_st ag') = None.
  Proof.
    intros Hlk Hqt.
    destruct (pf_unpark i c ag Hlk) as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
    rewrite /psail_quiet in Hqt.
    destruct (sp_m (pa_st ag)) as [m|] eqn:Hm.
    - destruct (quiet_run m Hqt i c1 ag1 _ _ _ Hlk1 Hpa1)
        as (c2 & ag2 & Hs2 & Hlk2 & Hm2 & Hf2).
      have Hs : rtc (pf_solo_q next i) c c2 by etrans; [exact Hs1|exact Hs2].
      exists c2, ag2. split_and!;
        [exact Hs|exact (pf_solo_q_run_qframe next i c c2 Hs)|exact Hlk2
        |by exists ag2|exact Hm2|exact Hf2].
    - exists c1, ag1. split_and!;
        [exact Hs1|exact (pf_solo_q_run_qframe next i c c1 Hs1)|exact Hlk1
        |by exists ag1; rewrite Hpa1|by rewrite Hpa1|by rewrite Hpa1].
  Qed.

  (** THE SILENT-EPILOGUE COMPLETION (stage B's "safe for every agent
      including the author"): the log does not move, the image does not
      move, no other agent moves, and the completing agent's promise set and
      COHERENCE FLOORS do not move — so no [WeakRobust.violation] can be
      created or destroyed by running an epilogue. *)
  Theorem quiet_complete (i : agent) c ag :
    pc_ags c !! i = Some ag → psail_quiet (pa_st ag) →
    ∃ c' ag',
      rtc (pf_solo next i) c c' ∧
      pc_ags c' !! i = Some ag' ∧ at_boundary i c' ∧
      sp_m (pa_st ag') = None ∧ sp_fence (pa_st ag') = None ∧
      pc_log c' = pc_log c ∧ pc_img c' = pc_img c ∧
      (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j) ∧
      pa_prom ag' = pa_prom ag ∧
      (∀ a, coh (pa_ws ag') a = coh (pa_ws ag) a).
  Proof.
    intros Hlk Hqt.
    destruct (quiet_complete_q i c ag Hlk Hqt)
      as (c' & ag' & Hrun & (Hl & Hi & Hf & Ha) & Hlk' & Hbd & Hm & Hfn).
    destruct (Ha ag Hlk) as (ag'' & Hlk'' & Hprom & Hcoh).
    rewrite Hlk' in Hlk''. injection Hlk'' as <-.
    exists c', ag'. split_and!;
      [exact (pf_solo_q_run_solo next i c c' Hrun)|exact Hlk'|exact Hbd|exact Hm|exact Hfn
      |exact Hl|exact Hi|exact Hf|exact Hprom|exact Hcoh].
  Qed.

End complete.

(* ====================================================================== *)
(** ** 6. Residual invariants: the fused-RMW window

    The only arm of [sail_step_ni] that does NOT descend to an immediate
    continuation is the fused RMW, which jumps across a whole [silent_run]
    window and a [wr_node].  Three little lemmas carry [amo_tail],
    [sail_shaped]/[sail_live] and [oracle_consistent] across it; they are
    what both preservation lemmas and the reader-tail completion need. *)

Lemma amo_tail_silent1 pa n (m : M unit) rs (b : M unit * regstate) :
  amo_tail pa n m → silent1 (m, rs) b → amo_tail pa n b.1.
Proof.
  destruct m as [y|T oc k]; [by intros _ []|].
  destruct oc; simpl; try (by intros _ []);
    try (by intros Hat ->; simpl; apply Hat);
    try (by intros Hat [ch ->]; simpl; apply Hat).
Qed.

Lemma amo_tail_silent_run pa n (m m1 : M unit) rs rs1 :
  amo_tail pa n m → silent_run (m, rs) (m1, rs1) → amo_tail pa n m1.
Proof.
  intros Hat Hrun.
  change m with (m, rs).1 in Hat. change m1 with (m1, rs1).1.
  remember (m, rs) as a. remember (m1, rs1) as b. clear Heqa Heqb m rs m1 rs1.
  revert Hat. induction Hrun as [|x y z Hxy _ IH]; [done|].
  intros Hat. apply IH. destruct x as [mx rsx].
  exact (amo_tail_silent1 pa n mx rsx y Hat Hxy).
Qed.

Lemma sail_live_silent1 (m : M unit) rs (b : M unit * regstate) :
  sail_live m → silent1 (m, rs) b → sail_live b.1.
Proof.
  destruct m as [y|T oc k]; [by intros _ []|].
  destruct oc; simpl; try (by intros _ []);
    try (by intros Hlv ->; simpl; apply Hlv);
    try (by intros Hlv [ch ->]; simpl; apply Hlv).
Qed.

Lemma sail_live_silent_run (m m1 : M unit) rs rs1 :
  sail_live m → silent_run (m, rs) (m1, rs1) → sail_live m1.
Proof.
  intros Hlv Hrun.
  change m with (m, rs).1 in Hlv. change m1 with (m1, rs1).1.
  remember (m, rs) as a. remember (m1, rs1) as b. clear Heqa Heqb m rs m1 rs1.
  revert Hlv. induction Hrun as [|x y z Hxy _ IH]; [done|].
  intros Hlv. apply IH. destruct x as [mx rsx].
  exact (sail_live_silent1 mx rsx y Hlv Hxy).
Qed.

Lemma wr_node_mchild m1 rl base data m2 :
  wr_node m1 rl base data m2 → mchild m2 m1.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros (_ & _ & _ & _ & _ & _ & ->). by eexists.
Qed.

Lemma wr_node_shaped pa n m1 rl base data m2 :
  amo_tail pa n m1 → wr_node m1 rl base data m2 → sail_shaped m2.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros (_ & _ & _ & _ & _ & Hsh) (_ & _ & _ & _ & _ & _ & ->). by apply Hsh.
Qed.

Lemma wr_node_live m1 rl base data m2 :
  sail_live m1 → wr_node m1 rl base data m2 → sail_live m2.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros Hlv (_ & _ & _ & _ & _ & _ & ->). by apply Hlv.
Qed.

Lemma oracle_consistent_silent1 dv (m : M unit) rs (b : M unit * regstate) str :
  oracle_consistent dv m str → silent1 (m, rs) b →
  oracle_consistent dv b.1 str.
Proof.
  destruct m as [y|T oc k]; [by intros _ []|].
  destruct oc; simpl; try (by intros _ []);
    try (by intros Hoc ->; simpl; apply Hoc);
    try (by intros Hoc [ch ->]; simpl; apply Hoc).
Qed.

Lemma oracle_consistent_silent_run dv (m m1 : M unit) rs rs1 str :
  oracle_consistent dv m str → silent_run (m, rs) (m1, rs1) →
  oracle_consistent dv m1 str.
Proof.
  intros Hoc Hrun.
  change m with (m, rs).1 in Hoc. change m1 with (m1, rs1).1.
  remember (m, rs) as a. remember (m1, rs1) as b. clear Heqa Heqb m rs m1 rs1.
  revert Hoc. induction Hrun as [|x y z Hxy _ IH]; [done|].
  intros Hoc. apply IH. destruct x as [mx rsx].
  exact (oracle_consistent_silent1 dv mx rsx y str Hoc Hxy).
Qed.

Lemma oracle_consistent_wr_node dv m1 rl base data m2 str :
  oracle_consistent dv m1 str → wr_node m1 rl base data m2 →
  oracle_consistent dv m2 str.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros Hoc (Hd & _ & _ & _ & _ & _ & ->). rewrite Hd in Hoc. by apply Hoc.
Qed.

(** ONE STEP OF AN AMO TAIL: either the conditional write is here, or one
    silent step gets closer to it. *)
Lemma amo_step (pa : Arch.pa) (n : N) (m : M unit) (rs : regstate) :
  amo_tail pa n m → sail_live m →
  (∃ rl data m2,
     wr_node m rl (pa_z pa) data m2 ∧ length data = N.to_nat n ∧
     data ≠ [] ∧ sail_shaped m2 ∧ sail_live m2) ∨
  (∃ m' rs', silent1 (m, rs) (m', rs') ∧ amo_tail pa n m' ∧ sail_live m').
Proof.
  intros Hat Hlv. destruct m as [y|T oc k]; [by destruct Hat|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2];
    simpl in Hat, Hlv;
    try (by destruct Hat); try (by destruct Hlv);
    try (by right; do 2 eexists;
           split_and!; [rewrite /silent1 /=; reflexivity
                       |by apply Hat|by apply Hlv]).
  - (* the conditional write: the fused arm's second half *)
    destruct Hat as (Hd & Hpa & Hn & Hn0 & Hlat & Hsh).
    left.
    exists (ak_sync (classify (Interface.WriteReq.access_kind req))),
           (wbytes nn (Interface.WriteReq.value req)), (k (inl None)).
    split_and!.
    + rewrite /wr_node. split_and!;
        [exact Hd|exact Hn0|exact Hlat|reflexivity|by rewrite Hpa
        |reflexivity|reflexivity].
    + rewrite wbytes_length. by rewrite Hn.
    + by apply wbytes_nonnil.
    + by apply Hsh.
    + by apply Hlv.
  - (* Choose *)
    right. exists (k (chosen ty)), rs.
    split_and!; [rewrite /silent1 /=; by exists (chosen ty)
                |by apply Hat|by apply Hlv].
Qed.

(** THE WINDOW, WALKED: from an [amo_tail] the LTS reaches its conditional
    write by silent steps alone, and the post-write residual is shaped, live
    and a STRICT DESCENDANT of where the window started ([rtc mchild], which
    is what makes the reader tail's induction well founded). *)
Lemma amo_reach (pa : Arch.pa) (n : N) : ∀ (m : M unit),
  amo_tail pa n m → sail_live m → ∀ (rs : regstate),
  ∃ (m1 m2 : M unit) (rs1 : regstate) (rl : bool) (data : list (bv 8)),
    silent_run (m, rs) (m1, rs1) ∧ wr_node m1 rl (pa_z pa) data m2 ∧
    length data = N.to_nat n ∧ data ≠ [] ∧
    sail_shaped m2 ∧ sail_live m2 ∧ rtc mchild m2 m.
Proof.
  intros m. induction m as [m IH] using (well_founded_ind mchild_wf).
  intros Hat Hlv rs.
  destruct (amo_step pa n m rs Hat Hlv)
    as [(rl & data & m2 & Hwr & Hlen & Hne & Hsh & Hlv2)
       |(m' & rs' & Hs1 & Hat' & Hlv')].
  - exists m, m2, rs, rl, data. split_and!;
      [apply rtc_refl|exact Hwr|exact Hlen|exact Hne|exact Hsh|exact Hlv2|].
    apply rtc_once. exact (wr_node_mchild m rl (pa_z pa) data m2 Hwr).
  - have Hch : mchild m' m
      by exact (silent1_mchild (m, rs) (m', rs') Hs1).
    destruct (IH m' Hch Hat' Hlv' rs')
      as (m1 & m2 & rs1 & rl & data & Hrun & Hwr & Hlen & Hne & Hsh & Hlv2 & Hd).
    exists m1, m2, rs1, rl, data. split_and!;
      [|exact Hwr|exact Hlen|exact Hne|exact Hsh|exact Hlv2|].
    + eapply rtc_l; [exact Hs1|exact Hrun].
    + eapply rtc_r; [exact Hd|exact Hch].
Qed.

(* ---------------------------------------------------------------- *)
(** *** The two preservation lemmas

    Both are stated for IN-BLOCK steps — see header deviation (b): at a
    boundary the step loads [next tick], about which nothing is known. *)

Section residual.
  Context (next : bool → M unit).

  Lemma sail_shaped_res_step p l p' :
    sp_m p ≠ None → shaped_res p → sail_step_ni next p l p' → shaped_res p'.
  Proof.
    intros Hne Hsh Hstep.
    rewrite /sail_step_ni in Hstep. rewrite /shaped_res in Hsh |- *.
    destruct (sp_fence p) as [[[[pr pw] sr] sw]|].
    { destruct Hstep as [_ ->]. simpl. exact Hsh. }
    destruct (sp_m p) as [m|]; [|by destruct (Hne eq_refl)].
    rewrite /sail_mstep in Hstep.
    destruct m as [y|T oc k]; [by destruct Hstep as [_ ->]; simpl|].
    destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                   |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hstep, Hsh;
      try (by destruct Hstep);
      try (by destruct Hstep as [_ ->]; simpl; apply Hsh).
    - (* MemRead *)
      destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
      + destruct Hstep as (_ & e & d2 & w2 & _ & _ & _ & ->). simpl. by apply Hsh.
      + destruct Hsh as (Hcoh & Hsh). destruct Hstep as (_ & Hstep).
        destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data
                      |pr pw sr sw]; try (by destruct Hstep).
        * destruct lat; [by destruct Hstep|].
          destruct Hstep as (Hlat & _ & _ & _ & w & _ & ->).
          rewrite Hlat in Hsh. simpl. by apply Hsh.
        * destruct Hstep as (Hlat & _ & _ & _ & _ & w & m1 & m2 & rs1
                             & _ & Hsil & Hwr & ->).
          rewrite Hlat in Hsh. simpl.
          eapply wr_node_shaped; [|exact Hwr].
          eapply amo_tail_silent_run; [apply (Hsh w)|exact Hsil].
    - (* MemWrite *)
      destruct Hsh as (_ & Hsh).
      destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
      + destruct Hstep as [_ ->]. simpl. by apply Hsh.
      + destruct Hstep as (_ & _ & _ & ->). simpl. by apply Hsh.
    - (* Choose *)
      destruct Hstep as (_ & ch & ->). simpl. by apply Hsh.
  Qed.

  Lemma oracle_consistent_res_step p l p' :
    sp_m p ≠ None → ocons_res p → sail_step_ni next p l p' → ocons_res p'.
  Proof.
    intros Hne Hoc Hstep.
    rewrite /sail_step_ni in Hstep. rewrite /ocons_res in Hoc |- *.
    destruct (sp_fence p) as [[[[pr pw] sr] sw]|].
    { destruct Hstep as [_ ->]. simpl. exact Hoc. }
    destruct (sp_m p) as [m|]; [|by destruct (Hne eq_refl)].
    destruct Hoc as (dv & Hoc).
    rewrite /sail_mstep in Hstep.
    destruct m as [y|T oc k]; [by destruct Hstep as [_ ->]; simpl|].
    destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                   |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hstep, Hoc;
      try (by destruct Hstep);
      try (by destruct Hstep as [_ ->]; simpl; exists dv; apply Hoc).
    - (* MemRead *)
      destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
      + destruct Hoc as (w & dv' & str' & Hdr & Hstr & Hoc').
        destruct Hstep as (_ & e & d2 & w2 & He & Hlen & Hbytes & ->).
        rewrite Hstr in He. injection He as He1 He2. subst e d2.
        have -> : w2 = w.
        { apply bv_eq_of_bytes. intros j Hj.
          have Hb := Hbytes j ltac:(lia).
          rewrite (wbytes_lookup nn w j ltac:(lia)) in Hb.
          apply Some_inj in Hb. by rewrite Hb. }
        simpl. by exists dv'.
      + destruct Hstep as (_ & Hstep).
        destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data
                      |pr pw sr sw]; try (by destruct Hstep).
        * destruct lat; [by destruct Hstep|].
          destruct Hstep as (_ & _ & _ & _ & w & _ & ->). simpl.
          exists dv. by apply Hoc.
        * destruct Hstep as (_ & _ & _ & _ & _ & w & m1 & m2 & rs1
                             & _ & Hsil & Hwr & ->).
          simpl. exists dv.
          eapply oracle_consistent_wr_node; [|exact Hwr].
          eapply oracle_consistent_silent_run;
            [apply (Hoc (inl (w, None)))|exact Hsil].
    - (* MemWrite *)
      destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
      + destruct Hoc as (dv' & Hdw & Hoc').
        destruct Hstep as [_ ->]. simpl. by exists dv'.
      + destruct Hstep as (_ & _ & _ & ->). simpl. exists dv. by apply Hoc.
    - (* Choose *)
      destruct Hstep as (_ & ch & ->). simpl. exists dv. by apply Hoc.
  Qed.

  Lemma sail_live_res_step p l p' :
    sp_m p ≠ None → live_res p → sail_step_ni next p l p' → live_res p'.
  Proof.
    intros Hne Hlv Hstep.
    rewrite /sail_step_ni in Hstep. rewrite /live_res in Hlv |- *.
    destruct (sp_fence p) as [[[[pr pw] sr] sw]|].
    { destruct Hstep as [_ ->]. simpl. exact Hlv. }
    destruct (sp_m p) as [m|]; [|by destruct (Hne eq_refl)].
    rewrite /sail_mstep in Hstep.
    destruct m as [y|T oc k]; [by destruct Hstep as [_ ->]; simpl|].
    destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                   |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hstep, Hlv;
      try (by destruct Hstep);
      try (by destruct Hstep as [_ ->]; simpl; apply Hlv).
    - (* MemRead *)
      destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
      + destruct Hstep as (_ & e & d2 & w2 & _ & _ & _ & ->). simpl. by apply Hlv.
      + destruct Hstep as (_ & Hstep).
        destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data
                      |pr pw sr sw]; try (by destruct Hstep).
        * destruct lat; [by destruct Hstep|].
          destruct Hstep as (_ & _ & _ & _ & w & _ & ->). simpl. by apply Hlv.
        * destruct Hstep as (_ & _ & _ & _ & _ & w & m1 & m2 & rs1
                             & _ & Hsil & Hwr & ->).
          simpl. eapply wr_node_live; [|exact Hwr].
          eapply sail_live_silent_run; [apply (Hlv (inl (w, None)))|exact Hsil].
    - (* MemWrite *)
      destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
      + destruct Hstep as [_ ->]. simpl. by apply Hlv.
      + destruct Hstep as (_ & _ & _ & ->). simpl. by apply Hlv.
    - (* Choose *)
      destruct Hstep as (_ & ch & ->). simpl. by apply Hlv.
  Qed.

End residual.

(* ====================================================================== *)
(** ** 7. READER-TAIL COMPLETION

    An arbitrary shaped, live residual runs to its next instruction boundary
    in the promise-free machine.  The reads take FREE values — under
    [img_total] every byte's LATEST write is admissible
    ([WeakRobustBlocks.read_latest_*]) — and the appended messages carry the
    CANONICAL class [WeakSailLTS2.lbl_class], which is what makes every step
    a [pf_solo] one. *)

(** Assembling a word from a byte window: the converse of [nth_byte], which
    is what turns the timestamp/value list the machine offers into the value
    the model's [MemRead] continuation consumes. *)
Lemma bytes_to_word (nn : N) (bs : list (bv 8)) :
  length bs = N.to_nat nn →
  ∃ w : bv (8 * nn),
    ∀ j : nat, (j < N.to_nat nn)%nat → bs !! j = Some (nth_byte w j).
Proof.
  intros Hlen. exists (Z_to_bv (8 * nn) (assemble_bytes bs)).
  intros j Hj. rewrite (nth_byte_assemble_len (8 * nn) bs j).
  - apply list_lookup_lookup_total_lt. lia.
  - rewrite Hlen N2Z.inj_mul. pose proof (N_nat_Z nn). lia.
  - lia.
Qed.

Section tail.
  Context (next : bool → M unit).

  Implicit Types c : wpcfg psail.

  (** The three non-quiet step wrappers.  [cls_canon] is vacuous for the
      load (the log is frozen) and holds by CONSTRUCTION for the store and
      the rmw (the class is [lbl_class] at the pre-state); [rmw_tight] is
      [True] but at the rmw, where it is the [lat := true] read the caller
      supplies from [read_latest]. *)

  Lemma pf_lstep (i : agent) c ag aq base tvs st' :
    pc_ags c !! i = Some ag →
    sail_step_ni next (pa_st ag) (WeakPromise.LLoad aq false base tvs) st' →
    read_ok (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs →
    ∃ c' ag', pf_solo next i c c' ∧ pc_ags c' !! i = Some ag' ∧ pa_st ag' = st'.
  Proof.
    intros Hlk Hstep Hro.
    exists (WPCfg (pc_img c) (pc_log c)
             (<[i := WPAgent st' (load_post_run (pa_ws ag) aq base tvs.*1)
                       (pa_prom ag)]> (pc_ags c))),
           (WPAgent st' (load_post_run (pa_ws ag) aq base tvs.*1) (pa_prom ag)).
    split_and!; [|exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
    exists (WeakPromise.LLoad aq false base tvs). split_and!;
      [exact (PFLoad (sail_step_ni next) i c ag aq false base tvs st' Hlk Hstep Hro)
      |by apply cls_canon_nolog|exact I].
  Qed.

  Lemma pf_sstep (i : agent) c ag rl base data st' :
    pc_ags c !! i = Some ag →
    sail_step_ni next (pa_st ag) (WeakPromise.LStore rl base data) st' →
    data ≠ [] →
    ∃ c' ag', pf_solo next i c c' ∧ pc_ags c' !! i = Some ag' ∧ pa_st ag' = st'.
  Proof.
    intros Hlk Hstep Hne.
    set (kc := lbl_class (WeakPromise.LStore rl base data) (pa_ws ag)).
    exists (WPCfg (pc_img c) (pc_log c ++ [WMsg base data (Some i) kc])
             (<[i := WPAgent st'
                       (store_post_run (pa_ws ag) rl base (length data)
                          (S (length (pc_log c)))) (pa_prom ag)]> (pc_ags c))),
           (WPAgent st'
              (store_post_run (pa_ws ag) rl base (length data)
                 (S (length (pc_log c)))) (pa_prom ag)).
    split_and!; [|exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
    exists (WeakPromise.LStore rl base data). split_and!.
    - exact (PFStore (sail_step_ni next) i c ag rl base data kc st'
               Hlk Hstep Hne).
    - intros ag2 msg Hag2 Heq. simpl in Heq.
      apply app_inv_head in Heq. injection Heq as <-.
      rewrite Hlk in Hag2. by injection Hag2 as <-.
    - exact I.
  Qed.

  Lemma pf_rstep (i : agent) c ag aq rl base tvs data st' :
    pc_ags c !! i = Some ag →
    sail_step_ni next (pa_st ag) (WeakPromise.LRmw aq rl base tvs data) st' →
    data ≠ [] → length tvs = length data →
    read_ok (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs →
    read_ok (pc_img c) (pc_log c) (pa_ws ag) aq true base tvs →
    excl_ok (pc_log c) i base tvs (S (length (pc_log c))) →
    ∃ c' ag', pf_solo next i c c' ∧ pc_ags c' !! i = Some ag' ∧ pa_st ag' = st'.
  Proof.
    intros Hlk Hstep Hne Hlen Hro Hrot Hex.
    set (kc := lbl_class (WeakPromise.LRmw aq rl base tvs data) (pa_ws ag)).
    exists (WPCfg (pc_img c) (pc_log c ++ [WMsg base data (Some i) kc])
             (<[i := WPAgent st'
                       (store_post_run
                          (load_post_run (pa_ws ag) aq base tvs.*1)
                          rl base (length data) (S (length (pc_log c))))
                       (pa_prom ag)]> (pc_ags c))),
           (WPAgent st'
              (store_post_run (load_post_run (pa_ws ag) aq base tvs.*1)
                 rl base (length data) (S (length (pc_log c))))
              (pa_prom ag)).
    split_and!; [|exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
    exists (WeakPromise.LRmw aq rl base tvs data). split_and!.
    - exact (PFRmw (sail_step_ni next) i c ag aq rl base tvs data kc st'
               Hlk Hstep Hne Hlen Hro Hex).
    - intros ag2 msg Hag2 Heq. simpl in Heq.
      apply app_inv_head in Heq. injection Heq as <-.
      rewrite Hlk in Hag2. by injection Hag2 as <-.
    - intros ag2 Hag2. rewrite Hlk in Hag2. by injection Hag2 as <-.
  Qed.

  (** The residual after one step of the tail: either the agent has reached
      the boundary, or it sits at a STRICTLY SMALLER residual which is still
      shaped, live and oracle-consistent (with a possibly parked fence, which
      [pf_unpark] fires). *)
  Definition tail_post (i : agent) (m : M unit) (iq : istream)
      (c' : wpcfg psail) (ag' : wpagent psail) : Prop :=
    (sp_m (pa_st ag') = None ∧ sp_fence (pa_st ag') = None) ∨
    ∃ (m' : M unit) (rs' : regstate) (d' : dstream)
      (fo : option (bool * bool * bool * bool)),
      pa_st ag' = PSail (Some m') rs' d' fo iq ∧
      tc mchild m' m ∧ sail_shaped m' ∧ sail_live m' ∧
      (∃ dv, oracle_consistent dv m' d').

  (** The QUIET arms of the tail, factored: one silent (or barrier) step to a
      smaller residual. *)
  Lemma tail_qcase (i : agent) c ag (l : wlabel) (m m' : M unit) rs' d'
      fo iq :
    pc_ags c !! i = Some ag → lbl_quiet l →
    sail_step_ni next (pa_st ag) l (PSail (Some m') rs' d' fo iq) →
    tc mchild m' m → sail_shaped m' → sail_live m' →
    (∃ dv, oracle_consistent dv m' d') →
    ∃ c' ag', pf_solo next i c c' ∧ pc_ags c' !! i = Some ag' ∧
              tail_post i m iq c' ag'.
  Proof.
    intros Hlk Hql Hstep Hch Hsh Hlv Hoc.
    destruct (pf_qstep next i c ag l _ Hlk Hql Hstep)
      as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
    exists c1, ag1. split_and!;
      [exact (pf_solo_q_solo next i c c1 Hs1)|exact Hlk1|].
    right. exists m', rs', d', fo.
    split_and!; [exact Hpa1|exact Hch|exact Hsh|exact Hlv|exact Hoc].
  Qed.

  (** ONE STEP OF THE READER TAIL. *)
  Lemma tail_step (i : agent) c ag (m : M unit) rs d iq :
    img_total (pc_img c) → cfg_bnd c →
    pc_ags c !! i = Some ag → pa_st ag = PSail (Some m) rs d None iq →
    sail_shaped m → sail_live m → (∃ dv, oracle_consistent dv m d) →
    ∃ c' ag', pf_solo next i c c' ∧ pc_ags c' !! i = Some ag' ∧
              tail_post i m iq c' ag'.
  Proof.
    intros Him Hbnd Hlk Hst Hsh Hlv (dv & Hoc).
    have Hws : ws_bounded (pa_ws ag) (length (pc_log c)) := Hbnd i ag Hlk.
    destruct m as [y|T oc k].
    { (* Ret: the last silent step, back to the boundary *)
      destruct (pf_qstep next i c ag WeakPromise.LSilent
                  (PSail None rs d None iq) Hlk (or_introl eq_refl)
                  ltac:(rewrite Hst /sail_step_ni /=; by split))
        as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
      exists c1, ag1. split_and!;
        [exact (pf_solo_q_solo next i c c1 Hs1)|exact Hlk1|].
      left. by rewrite Hpa1. }
    destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                   |epa|tst|tnd|A eo|msg| | |ty| |msg2];
      simpl in Hsh, Hlv, Hoc; try (by destruct Hlv).
    - (* RegRead *)
      apply (tail_qcase i c ag WeakPromise.LSilent _
               (k (register_lookup rg rs)) rs d None iq Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* RegWrite *)
      apply (tail_qcase i c ag WeakPromise.LSilent _
               (k tt) (register_set rg rv rs) d None iq Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* MemRead *)
      destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
      + (* MMIO: the oracle serves it, silently *)
        destruct Hoc as (w & dv' & str' & Hdr & Hstr & Hoc').
        apply (tail_qcase i c ag WeakPromise.LSilent _
                 (k (inl (w, None))) rs str' None iq Hlk (or_introl eq_refl));
          [rewrite Hst /sail_step_ni /sail_mstep /= Hd; split; [reflexivity|];
           exists (wbytes nn w), str', w;
           split_and!; [exact Hstr|apply wbytes_length
                       |intros j Hj; by apply wbytes_lookup|reflexivity]
          |apply tc_once; by eexists|by apply Hsh|by apply Hlv
          |by exists dv'].
      + (* RAM *)
        destruct Hsh as (Hcoh & Hsh).
        destruct (read_latest_exists (pc_img c) (pc_log c)
                    (pa_z (Interface.ReadReq.pa req)) (N.to_nat nn) Him)
          as (tvs & Hlent & Hrl).
        have Hlent2 : length tvs.*2 = N.to_nat nn by rewrite length_fmap.
        destruct (bytes_to_word nn tvs.*2 Hlent2) as (w & Hw).
        destruct (ak_latest (classify (Interface.ReadReq.access_kind req)))
          eqn:Hlat.
        * (* THE FUSED RMW: walk the window to the conditional write *)
          destruct (amo_reach (Interface.ReadReq.pa req) nn
                      (k (inl (w, None))) (Hsh w) (Hlv _) rs)
            as (m1 & m2 & rs1 & rl & data & Hsil & Hwr & Hlend & Hned
                & Hsh2 & Hlv2 & Hdesc).
          have Hro : read_ok (pc_img c) (pc_log c) (pa_ws ag)
                       (ak_sync (classify (Interface.ReadReq.access_kind req)))
                       false (pa_z (Interface.ReadReq.pa req)) tvs
            by apply read_latest_read_ok.
          have Hrot : read_ok (pc_img c) (pc_log c) (pa_ws ag)
                        (ak_sync (classify (Interface.ReadReq.access_kind req)))
                        true (pa_z (Interface.ReadReq.pa req)) tvs
            by apply read_latest_read_ok.
          have Hex : excl_ok (pc_log c) i (pa_z (Interface.ReadReq.pa req)) tvs
                       (S (length (pc_log c)))
            by apply (read_latest_excl_ok (pc_img c) (pc_log c) i).
          destruct (pf_rstep i c ag
                      (ak_sync (classify (Interface.ReadReq.access_kind req)))
                      rl (pa_z (Interface.ReadReq.pa req)) tvs data
                      (PSail (Some m2) rs1 d None iq) Hlk
                      ltac:(rewrite Hst /sail_step_ni /sail_mstep /= Hd;
                            split; [exact Hcoh|];
                            split_and!;
                              [exact Hlat|reflexivity|reflexivity
                              |exact Hlent|exact Hlend|];
                            exists w, m1, m2, rs1;
                            split_and!;
                              [exact Hw|exact Hsil|exact Hwr|reflexivity])
                      Hned ltac:(rewrite Hlent Hlend; reflexivity) Hro Hrot Hex)
            as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
          exists c1, ag1. split_and!; [exact Hs1|exact Hlk1|].
          right. exists m2, rs1, d, None.
          split_and!; [exact Hpa1| |exact Hsh2|exact Hlv2|].
          { eapply tc_rtc_step; [exact Hdesc|by eexists]. }
          { exists dv. eapply oracle_consistent_wr_node; [|exact Hwr].
            eapply oracle_consistent_silent_run;
              [apply (Hoc (inl (w, None)))|exact Hsil]. }
        * (* a plain load: every byte at its latest write *)
          have Hro : read_ok (pc_img c) (pc_log c) (pa_ws ag)
                       (ak_sync (classify (Interface.ReadReq.access_kind req)))
                       false (pa_z (Interface.ReadReq.pa req)) tvs
            by apply read_latest_read_ok.
          destruct (pf_lstep i c ag
                      (ak_sync (classify (Interface.ReadReq.access_kind req)))
                      (pa_z (Interface.ReadReq.pa req)) tvs
                      (PSail (Some (k (inl (w, None)))) rs d None iq) Hlk
                      ltac:(rewrite Hst /sail_step_ni /sail_mstep /= Hd;
                            split; [exact Hcoh|];
                            split_and!;
                              [exact Hlat|reflexivity|reflexivity|exact Hlent|];
                            exists w; split; [exact Hw|reflexivity])
                      Hro)
            as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
          exists c1, ag1. split_and!; [exact Hs1|exact Hlk1|].
          right. exists (k (inl (w, None))), rs, d, None.
          split_and!; [exact Hpa1|apply tc_once; by eexists
                      |by apply Hsh|by apply Hlv|exists dv; by apply Hoc].
    - (* MemWrite *)
      destruct Hsh as (Hn & Hsh).
      destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
      + destruct Hoc as (dv' & Hdw & Hoc').
        apply (tail_qcase i c ag WeakPromise.LSilent _
                 (k (inl None)) rs d None iq Hlk (or_introl eq_refl));
          [rewrite Hst /sail_step_ni /sail_mstep /= Hd; by split
          |apply tc_once; by eexists|by apply Hsh|by apply Hlv|by exists dv'].
      + destruct Hn as (Hn0 & Hnlat).
        destruct (pf_sstep i c ag
                    (ak_sync (classify (Interface.WriteReq.access_kind req)))
                    (pa_z (Interface.WriteReq.pa req))
                    (wbytes nn (Interface.WriteReq.value req))
                    (PSail (Some (k (inl None))) rs d None iq) Hlk
                    ltac:(rewrite Hst /sail_step_ni /sail_mstep /= Hd;
                          split_and!;
                            [reflexivity|exact Hn0|exact Hnlat|reflexivity])
                    ltac:(by apply wbytes_nonnil))
          as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
        exists c1, ag1. split_and!; [exact Hs1|exact Hlk1|].
        right. exists (k (inl None)), rs, d, None.
        split_and!; [exact Hpa1|apply tc_once; by eexists
                    |by apply Hsh|by apply Hlv|exists dv; by apply Hoc].
    - (* InstrAnnounce *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* BranchAnnounce *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* Barrier: the label table, and the possible parked second fence *)
      apply (tail_qcase i c ag (barrier_lbl bk).1 _ (k tt) rs d
               (barrier_lbl bk).2 iq Hlk (barrier_lbl_quiet bk));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* CacheOp *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* TlbOp *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* TakeException *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* ReturnException *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* TranslationStart *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* TranslationEnd *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* CycleCount *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* GetCycleCount *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k 0%Z) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* Choose *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k (chosen ty)) rs d None
               iq Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; split;
           [reflexivity|by exists (chosen ty)]
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
    - (* Message *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv
        |exists dv; by apply Hoc].
  Qed.

  (** THE READER TAIL, run to the boundary.  The induction is on
      [tc mchild]: every arm but the fused RMW descends to an immediate
      continuation, and the fused arm descends across the whole
      [silent_run] window and the [wr_node] ([amo_reach]'s [rtc mchild]). *)
  Lemma tail_run : ∀ (m : M unit) (i : agent) c ag rs d iq,
    img_total (pc_img c) → cfg_bnd c →
    pc_ags c !! i = Some ag → pa_st ag = PSail (Some m) rs d None iq →
    sail_shaped m → sail_live m → (∃ dv, oracle_consistent dv m d) →
    ∃ c' ag', rtc (pf_solo next i) c c' ∧ pc_ags c' !! i = Some ag' ∧
              sp_m (pa_st ag') = None ∧ sp_fence (pa_st ag') = None.
  Proof.
    intros m. induction m as [m IH] using (well_founded_ind msub_wf).
    intros i c ag rs d iq Him Hbnd Hlk Hst Hsh Hlv Hoc.
    destruct (tail_step i c ag m rs d iq Him Hbnd Hlk Hst Hsh Hlv Hoc)
      as (c1 & ag1 & Hs1 & Hlk1
          & [[Hm1 Hf1]
            |(m' & rs' & d' & fo & Hpa1 & Hch & Hsh' & Hlv' & Hoc')]).
    - exists c1, ag1.
      split_and!; [by apply rtc_once|exact Hlk1|exact Hm1|exact Hf1].
    - destruct (pf_unpark next i c1 ag1 Hlk1) as (c2 & ag2 & Hs2 & Hlk2 & Hpa2).
      rewrite Hpa1 /= in Hpa2.
      have Hrun : rtc (pf_solo next i) c c2.
      { eapply rtc_l; [exact Hs1|exact (pf_solo_q_run_solo next i c1 c2 Hs2)]. }
      have Hbnd2 : cfg_bnd c2 := pf_solo_run_bnd next i c c2 Hrun Hbnd.
      have Him2 : img_total (pc_img c2).
      { destruct (pf_solo_run_tframe next i c c2 Hrun) as (_ & Himg & _ & _).
        by rewrite Himg. }
      destruct (IH m' Hch i c2 ag2 rs' d' iq Him2 Hbnd2 Hlk2 Hpa2 Hsh' Hlv' Hoc')
        as (c3 & ag3 & Hs3 & Hlk3 & Hm3 & Hf3).
      exists c3, ag3. split_and!;
        [by etrans; [exact Hrun|exact Hs3]|exact Hlk3|exact Hm3|exact Hf3].
  Qed.

  (** THE READER-TAIL COMPLETION.  Note what the conclusion does NOT claim:
      the appended messages [ms] are the completing agent's OWN (which is
      what [WeakRobustBlocks]'s violation-persistence consumes — the reader
      is not the violating message's author), the image is frozen and every
      other agent's slot is untouched, and no observation floor anywhere
      goes DOWN (so a floor that already reached the violating message still
      does). *)
  Theorem tail_complete (i : agent) c ag (m : M unit) :
    img_total (pc_img c) → cfg_bnd c →
    pc_ags c !! i = Some ag → sp_m (pa_st ag) = Some m →
    sail_shaped m → sail_live m →
    (∃ dv, oracle_consistent dv m (sp_dev (pa_st ag))) →
    ∃ c' ag' ms,
      rtc (pf_solo next i) c c' ∧
      pc_ags c' !! i = Some ag' ∧ at_boundary i c' ∧
      sp_fence (pa_st ag') = None ∧
      pc_log c' = pc_log c ++ ms ∧
      Forall (λ mq, wm_tid mq = Some i) ms ∧
      pc_img c' = pc_img c ∧ cfg_bnd c' ∧
      (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j) ∧
      (∀ j a, (obs_flr c j a ≤ obs_flr c' j a)%nat).
  Proof.
    intros Him Hbnd Hlk Hm Hsh Hlv Hoc.
    destruct (pf_unpark next i c ag Hlk) as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
    have Hrun01 : rtc (pf_solo next i) c c1
      := pf_solo_q_run_solo next i c c1 Hs1.
    have Hbnd1 : cfg_bnd c1 := pf_solo_run_bnd next i c c1 Hrun01 Hbnd.
    have Him1 : img_total (pc_img c1).
    { destruct (pf_solo_q_run_qframe next i c c1 Hs1) as (_ & Himg & _ & _).
      by rewrite Himg. }
    rewrite Hm in Hpa1.
    destruct (tail_run m i c1 ag1 (sp_regs (pa_st ag)) (sp_dev (pa_st ag))
                (sp_irq (pa_st ag)) Him1 Hbnd1 Hlk1 Hpa1 Hsh Hlv Hoc)
      as (c2 & ag2 & Hs2 & Hlk2 & Hm2 & Hf2).
    have Hrun : rtc (pf_solo next i) c c2
      by etrans; [exact Hrun01|exact Hs2].
    destruct (pf_solo_run_tframe next i c c2 Hrun)
      as ((ms & Hlog & Hall) & Himg & Hfr & Hobs).
    exists c2, ag2, ms. split_and!;
      [exact Hrun|exact Hlk2|by exists ag2|exact Hf2|exact Hlog|exact Hall
      |exact Himg|exact (pf_solo_run_bnd next i c c2 Hrun Hbnd)
      |exact Hfr|exact Hobs].
  Qed.

End tail.

(* ====================================================================== *)
(** ** 8. RUN SURGERY: a quiet step commutes left

    Stage B's step 3.  A silent or fence step of agent [k] reads NOTHING
    shared (the [PFSilent]/[PFFence] rules have no [read_ok]/[excl_ok]
    premise and no log premise) and writes only agent [k]'s slot, so it
    commutes past any step of any OTHER agent.  Hence a whole quiet
    epilogue — which is exactly what [quiet_complete_q] produces — can be
    spliced back to right after its agent's last event.

    Stated GENERICALLY over the program LTS: nothing here is Sail-specific,
    and stage B3/B4 applies it at [sail_step_ni]. *)

(** Re-taking an arbitrary pf step from a configuration that agrees on the
    image, the log, and the stepping agent's slot.  This is what lets the
    OTHER agent's step be replayed after the quiet step has moved in front
    of it. *)
Lemma wp_pf_step_transplant {P : Type} (pstep : P → wlabel → P → Prop)
    i l (c c' d : wpcfg P) :
  wp_pf_step pstep i l c c' →
  pc_img d = pc_img c → pc_log d = pc_log c → pc_ags d !! i = pc_ags c !! i →
  ∃ ag', pc_ags c' = <[i := ag']> (pc_ags c) ∧ pc_img c' = pc_img c ∧
         wp_pf_step pstep i l d
           (WPCfg (pc_img c') (pc_log c') (<[i := ag']> (pc_ags d))).
Proof.
  intros Hstep Himg Hlog Hags.
  destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kk st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kk st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps];
    have Hlkd : pc_ags d !! i = Some ag by rewrite Hags.
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog. exact (PFSilent pstep i d ag st' Hlkd Hps).
  - have Hr' : read_ok (pc_img d) (pc_log d) (pa_ws ag) aq lat base tvs
      by rewrite Himg Hlog.
    eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFLoad pstep i d ag aq lat base tvs st' Hlkd Hps Hr').
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFStore pstep i d ag rl base data kk st' Hlkd Hps Hne).
  - have Hr' : read_ok (pc_img d) (pc_log d) (pa_ws ag) aq false base tvs
      by rewrite Himg Hlog.
    have He' : excl_ok (pc_log d) i base tvs (S (length (pc_log d)))
      by rewrite Hlog.
    eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFRmw pstep i d ag aq rl base tvs data kk st'
             Hlkd Hps Hne Hlen Hr' He').
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFFence pstep i d ag pr pw sr sw st' Hlkd Hps).
Qed.

(** The QUIET transplant, which needs only the stepping agent's slot: a
    silent/fence step neither reads nor writes the log or the image. *)
Lemma quiet_transplant {P : Type} (pstep : P → wlabel → P → Prop)
    k lk (c1 c2 d : wpcfg P) :
  wp_pf_step pstep k lk c1 c2 → lbl_quiet lk →
  pc_ags d !! k = pc_ags c1 !! k →
  ∃ agk', pc_ags c2 = <[k := agk']> (pc_ags c1) ∧
          pc_img c2 = pc_img c1 ∧ pc_log c2 = pc_log c1 ∧
          wp_pf_step pstep k lk d
            (WPCfg (pc_img d) (pc_log d) (<[k := agk']> (pc_ags d))).
Proof.
  intros Hstep Hq Hags.
  destruct Hstep as
    [cfg ag st' Hlk Hps
    |cfg ag aq lat base tvs st' Hlk Hps Hr
    |cfg ag rl base data kc st' Hlk Hps Hne
    |cfg ag aq rl base tvs data kc st' Hlk Hps Hne Hlen Hr He
    |cfg ag pr pw sr sw st' Hlk Hps];
    try (by destruct Hq as [Hx|(?&?&?&?&Hx)]; inversion Hx);
    have Hlkd : pc_ags d !! k = Some ag by rewrite Hags.
  - eexists. split_and!; [reflexivity|reflexivity|reflexivity|].
    exact (PFSilent pstep k d ag st' Hlkd Hps).
  - eexists. split_and!; [reflexivity|reflexivity|reflexivity|].
    exact (PFFence pstep k d ag pr pw sr sw st' Hlkd Hps).
Qed.

(** THE COMMUTATION.  ([lbl_quiet lk] is the disjunction
    "[lk = LSilent] or [lk] is a fence".) *)
Lemma pf_local_commute {P : Type} (pstep : P → wlabel → P → Prop)
    i l k lk (c c1 c2 : wpcfg P) :
  wp_pf_step pstep i l c c1 → wp_pf_step pstep k lk c1 c2 → k ≠ i →
  lbl_quiet lk →
  ∃ c1', wp_pf_step pstep k lk c c1' ∧ wp_pf_step pstep i l c1' c2.
Proof.
  intros Hi Hk Hne Hq.
  have Hfr : pc_ags c !! k = pc_ags c1 !! k.
  { symmetry. exact (wp_pf_step_frame pstep i l c c1 k Hi Hne). }
  destruct (quiet_transplant pstep k lk c1 c2 c Hk Hq Hfr)
    as (agk' & Hags2 & Himg2 & Hlog2 & Hstepk).
  exists (WPCfg (pc_img c) (pc_log c) (<[k := agk']> (pc_ags c))).
  split; [exact Hstepk|].
  destruct (wp_pf_step_transplant pstep i l c c1
              (WPCfg (pc_img c) (pc_log c) (<[k := agk']> (pc_ags c)))
              Hi eq_refl eq_refl
              ltac:(simpl; apply lookup_insert_other; by intros ->))
    as (ag' & Hags1 & Himg1 & Hstepi).
  have Hc2 : c2 = WPCfg (pc_img c1) (pc_log c1)
                    (<[i := ag']> (<[k := agk']> (pc_ags c))).
  { destruct c2 as [img2 log2 ags2]. simpl in Himg2, Hlog2, Hags2.
    rewrite Himg2 Hlog2 Hags2 Hags1.
    by rewrite (list_insert_commute (pc_ags c) k i agk' ag' Hne). }
  rewrite Hc2. exact Hstepi.
Qed.

(** The two run relations the surgery is stated over: [k]'s own quiet steps,
    and everybody else's steps. *)
Definition pf_quiet_run {P : Type} (pstep : P → wlabel → P → Prop)
    (k : agent) (c c' : wpcfg P) : Prop :=
  ∃ lk, lbl_quiet lk ∧ wp_pf_step pstep k lk c c'.

Definition pf_other_run {P : Type} (pstep : P → wlabel → P → Prop)
    (k : agent) (c c' : wpcfg P) : Prop :=
  ∃ j l, j ≠ k ∧ wp_pf_step pstep j l c c'.

Lemma pf_quiet_commute_run {P : Type} (pstep : P → wlabel → P → Prop)
    k (c c1 c2 : wpcfg P) :
  rtc (pf_other_run pstep k) c c1 → pf_quiet_run pstep k c1 c2 →
  ∃ c1', pf_quiet_run pstep k c c1' ∧ rtc (pf_other_run pstep k) c1' c2.
Proof.
  intros Hrun. revert c2. induction Hrun as [|x y z Hxy _ IH]; intros c2 Hq.
  { exists c2. split; [exact Hq|apply rtc_refl]. }
  destruct (IH c2 Hq) as (y' & (lk & Hlk & Hstepk) & Hrest).
  destruct Hxy as (j & lj & Hjne & Hstepj).
  destruct (pf_local_commute pstep j lj k lk x y y' Hstepj Hstepk
              (not_eq_sym Hjne) Hlk)
    as (x' & Hqx & Hjx).
  exists x'. split; [by exists lk|].
  eapply rtc_l; [exists j, lj; split; [exact Hjne|exact Hjx]|exact Hrest].
Qed.

(** THE SPLICE.  A contiguous quiet run of agent [k] appended after a run of
    OTHER agents' steps can be moved to the FRONT of that run — which is how
    an epilogue completion is inserted right after its agent's last event. *)
Lemma pf_run_insert_local {P : Type} (pstep : P → wlabel → P → Prop)
    k (c c1 c2 : wpcfg P) :
  rtc (pf_other_run pstep k) c c1 → rtc (pf_quiet_run pstep k) c1 c2 →
  ∃ c1', rtc (pf_quiet_run pstep k) c c1' ∧
         rtc (pf_other_run pstep k) c1' c2.
Proof.
  intros Hoth Hqui. revert c Hoth.
  induction Hqui as [|x y z Hxy _ IH]; intros c Hoth.
  { exists c. split; [apply rtc_refl|exact Hoth]. }
  destruct (pf_quiet_commute_run pstep k c x y Hoth Hxy)
    as (c1' & Hq1 & Hoth1).
  destruct (IH c1' Hoth1) as (c2' & Hq2 & Hoth2).
  exists c2'. split; [|exact Hoth2]. eapply rtc_l; [exact Hq1|exact Hq2].
Qed.

(** A quiet solo run at the Sail LTS IS a [pf_quiet_run], so the splice
    applies directly to [quiet_complete_q]'s output. *)
Lemma pf_solo_q_quiet_run next i c c' :
  pf_solo_q next i c c' → pf_quiet_run (sail_step_ni next) i c c'.
Proof. by intros (l & Hq & Hstep); exists l. Qed.

Lemma pf_solo_q_run_quiet_run next i c c' :
  rtc (pf_solo_q next i) c c' → rtc (pf_quiet_run (sail_step_ni next) i) c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [exact (pf_solo_q_quiet_run next i x y Hxy)|exact IH].
Qed.
