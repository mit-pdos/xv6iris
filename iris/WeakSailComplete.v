(** * WeakSailComplete.v — the SAIL-LEVEL COMPLETION KIT (lift stage B1+B2)

    Stage B of [claude-notes/completed/weak-memory-lift.md] re-derives the
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

    (a) [sail_live_st] (§2).  [sail_shaped] does NOT exclude the model's three
        FAILURE outcomes ([Interface.GenericFail], [Interface.Discard],
        [Interface.ExtraOutcome]): their result types are empty (or
        abstract), so [sail_shaped]'s default arm [∀ r, sail_shaped (k r)]
        is VACUOUSLY true at such a node, while [sail_mstep] has no arm for
        them at all — the agent is stuck and no completion exists.
        [tail_complete] therefore takes [sail_live_st], a second shape premise
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

    (c) [Values.ChooseReal] IS EXCLUDED BY THE SHAPE PREDICATES, AND THAT IS
        AN AXIOM-FOOTPRINT DECISION.  A completion has to CHOOSE a value at
        every [Interface.Choose] node (the LTS's arm is existential in it).
        Taking [SailStdpp.Values]' [choose_type_inhabited] means building an
        [R] at [Values.ChooseReal], which alone puts Stdlib's
        [ClassicalDedekindReals.sig_forall_dec] into the [Print Assumptions]
        output of [quiet_complete] / [tail_complete] and of everything above
        them.  So [quiet_tail] and [sail_live_st] refute the [Values.ChooseReal]
        node outright (their [Interface.Choose] arm is [False] there and
        [∀ r, …] at every other choose type), and [choose_val] produces the
        value per constructor with no [R] anywhere.  rv64d never emits
        [Values.ChooseReal], so this costs nothing and it is in the same
        epistemic slot as the rest of the shape predicate.  All four exports
        are now "Closed under the global context".

    ------------------------------------------------------------------------
    THE INDEX (what stage B3/B4/B5 will name).

      §1  [mchild], [macc], [mchild_wf], [msub_wf] — the [iMon] subterm kit;
          [silent_run_mchild] (the fused window descends).
      §2  [quiet_tail], [sail_live_st] (state-conditioned — see (f)/(g)),
          [priv_ok], [quiet_tail_choose], [sail_live_st_choose],
          [sail_live_st_regread], [choose_val], [choose_val_q],
          [psail_quiet], [shaped_res], [live_res].
      §3  [pf_solo_q] (a [pf_solo] step with a quiet label), [qframe] /
          [tframe] and their run forms, [pf_solo_run_bnd].
      §4  [pf_qstep], [pf_unpark] (the parked [fence.tso] half),
          [quiet_step], [quiet_run].
      §5  [quiet_complete_q] / [quiet_complete].
      §6  the fused-window carriers ([sail_shaped_silent_run] &c),
          [sail_shaped_res_step], [sail_live_res_step].
      §7  [bytes_to_word], [pf_lstep]/[pf_sstep]/[pf_rstep] (the canonical-
          class step wrappers), [tail_step], [tail_run], [tail_complete].
      §8  [pf_local_commute], [pf_run_insert_local], and the bridge
          [pf_solo_q_run_quiet_run].
      §9  THE SEIP KIT (stage A3): [seip_free] and its frame/stability
          simulation, and the forward commutation of a mid-block interrupt
          delivery ([irq_commute_step], [irq_commute_fwd]).  §9 has its own
          index and its own deviation notes, at its head.

    DEPENDENCIES: [WeakSailLTS]/[WeakSailLTS2] (the LTS, [pf_solo],
    [dev_ok_blk]) and [WeakRobustBlocks] ([img_total],
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

(** A VALUE FOR EVERY [Interface.Choose] BUT [Values.ChooseReal].  The
    completions have to pick one (the LTS's [Choose] arm is existential in
    it).  [SailStdpp.Values]' [choose_type_inhabited] would serve, but at
    [Values.ChooseReal] its inhabitant is a REAL NUMBER, and merely BUILDING
    an [R] drags Stdlib's [ClassicalDedekindReals.sig_forall_dec] into the
    axiom footprint of everything above (see the header's note (c)).  So the
    shape predicates of §2 EXCLUDE [Values.ChooseReal] outright — rv64d never
    emits it — and the value is then produced per constructor by [choose_val]
    (§2), no arm of which mentions [R]. *)

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

    [sail_live_st rs m]: no path of [m], RUN FROM THE REGISTER FILE [rs],
    runs into a failure outcome.  See header deviation (a): [sail_shaped]
    does NOT imply this, because the failure outcomes' result types are empty
    and its default arm is then vacuous.

    ------------------------------------------------------------------------
    (f) WHY IT IS STATE-CONDITIONED, AND NOT [∀ b, sail_live (riscv_step b)]
    (stage C9; the state-free [sail_live] this replaces is DELETED).  Finding
    (O9): [Interface.RegRead]'s answer type is inhabited and the LTS answers
    it CONCRETELY ([sail_mstep]'s arm is [k (register_lookup r rs)]), so a
    predicate arm [∀ v, P (k v)] is the same silent, unbounded strengthening
    the memory arms carried before stage C2 — and it BITES:
    [rv64d.encdec_backwards] reaches [zicfiss_xSSE priv] with [priv] read
    from [cur_privilege], and [zicfiss_xSSE VirtualSupervisor] is an
    [internal_error].  The register-generic statement is therefore FALSE,
    while the concrete-answer one is exactly what the machine needs.  So
    every [RegRead] is answered from [rs] and every [RegWrite] THREADS it,
    which is what makes the residual invariant "live AT THE RECORD'S OWN
    REGISTERS" ([live_res]) preserved by [sail_mstep] step for step.

    (g) THE ONE REGISTER THAT IS STILL ∀-QUANTIFIED IS [sig_seip], AND IT IS
    FORCED BY THE LTS, NOT BY CONVENIENCE.  [WeakSailLTS.irq_deliver] writes
    the external-interrupt pin BEHIND THE RESIDUAL'S BACK — the residual
    monad does not move, the register file does — so a residual whose
    liveness depended on the pin's value would lose it at a delivery, and
    [WeakSailCone.res_ok_frame] (the arm that carries the invariant across a
    delivery) would be false.  Answering [sig_seip] with [∀ v] makes
    liveness invariant under any pin write ([sail_live_st_agree] /
    [sail_live_st_seip], §9.4), which is exactly the closure the LTS asks
    for.  Nothing else in the file is quantified: the pin is the only
    register any OTHER agent writes.

    THE MEMORY ARMS QUANTIFY OVER THE ANSWERS THE LTS SUPPLIES — [inl (w,
    None)] and [inl None] — exactly as [WeakSailLTS.sail_shaped]'s do
    ([WeakSailLTS] delta (e')).  The ∀-over-every-answer reading was
    REFUTABLE: it included the abort [inr ab], which [rv64d.read_ram] answers
    with [exit tt], so it was false at every load (stage C1 finding (O1)).
    Nothing downstream weakens: every consumer instantiates the arm at
    exactly those answers, because they are the only ones [sail_mstep]
    produces. *)

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
       | Interface.Choose ty =>
           match ty as t return (Values.choose_type t → M unit) → Prop with
           | Values.ChooseReal => λ _, False
           | _ => λ k, ∀ r, quiet_tail (k r)
           end
       | _ => λ k, ∀ r, quiet_tail (k r)
       end) k
  end.

Fixpoint sail_live_st (rs : regstate) (m : M unit) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       (* (f)/(g): concrete from [rs], except the pin another agent writes *)
       | Interface.RegRead r _ => λ k,
           if register_beq r (sig_seip : register)
           then ∀ v, sail_live_st rs (k v)
           else sail_live_st rs (k (register_lookup r rs))
       | Interface.RegWrite r _ v => λ k,
           sail_live_st (register_set r v rs) (k tt)
       | Interface.MemRead n req => λ k,
           ∀ w : bv (8 * n), sail_live_st rs (k (inl (w, None)))
       | Interface.MemWrite _ _ => λ k, sail_live_st rs (k (inl None))
       | Interface.ExtraOutcome _ => λ _, False
       | Interface.GenericFail _ => λ _, False
       | Interface.Discard => λ _, False
       | Interface.Choose ty =>
           match ty as t return (Values.choose_type t → M unit) → Prop with
           | Values.ChooseReal => λ _, False
           | _ => λ k, ∀ r, sail_live_st rs (k r)
           end
       | _ => λ k, ∀ r, sail_live_st rs (k r)
       end) k
  end.

(** THE PRIVILEGE SIDE CONDITION (stage C9).  The state precondition finding
    (O9) forces, and the whole of it: [cur_privilege] is one of the three
    privileges an H-less machine can be in.  It is what the [zicfiss_xSSE] /
    [_rec_get_xLPE] [internal_error] arms need, and it is stated over the
    register file rather than over a trace so that the per-boundary liveness
    fact is a statement about ONE record.

    PER-IMAGE DISCHARGE: xv6 never enables the hypervisor extension
    (misa.H is clear at reset and nothing writes it), so no [riscv_step] can
    ever enter [VirtualUser]/[VirtualSupervisor].  Making THAT a theorem is
    the model-level reachability invariant recorded as the upgrade path in
    [claude-notes/projects/weak-memory-premises.md]; until it exists,
    [WeakComposeLang]'s [Hpriv] carries it per trace record, exactly as
    [Hcq]/[Hseip] carry their own per-image facts. *)
Definition priv_ok (rs : regstate) : Prop :=
  register_lookup cur_privilege rs = Machine ∨
  register_lookup cur_privilege rs = Supervisor ∨
  register_lookup cur_privilege rs = User.

(** The three CHOOSE lemmas.  [quiet_tail] / [sail_live_st] at a [Choose]
    node still give the continuation at EVERY value (so the LTS's
    adversarial choice is covered); and they give a VALUE, produced without
    touching [R] — which is what a completion needs to step the node. *)

Lemma quiet_tail_choose (ty : Values.ChooseType)
    (k : Values.choose_type ty → M unit) :
  quiet_tail (Interface.Next (Interface.Choose ty) k) →
  ∀ r, quiet_tail (k r).
Proof. destruct ty; simpl; intros H; (exact H || destruct H). Qed.

Lemma sail_live_st_choose rs (ty : Values.ChooseType)
    (k : Values.choose_type ty → M unit) :
  sail_live_st rs (Interface.Next (Interface.Choose ty) k) →
  ∀ r, sail_live_st rs (k r).
Proof. destruct ty; simpl; intros H; (exact H || destruct H). Qed.

(** The [RegRead] answer, whichever arm the register takes: the LTS supplies
    [register_lookup r rs], and both arms give the continuation there. *)
Lemma sail_live_st_regread rs (r : register) ak
    (k : type_of_register r → M unit) :
  sail_live_st rs (Interface.Next (Interface.RegRead r ak) k) →
  sail_live_st rs (k (register_lookup r rs)).
Proof.
  simpl. destruct (register_beq r (sig_seip : register)); [|done].
  intros H. apply H.
Qed.

(** A value at every choose type the shape predicates admit.  [choose_prop]
    is NOT enforced by the LTS's [Choose] arm (it is existential in the
    value), so any inhabitant serves; the point is that none of these is an
    [R]. *)
Lemma choose_val rs (ty : Values.ChooseType)
    (k : Values.choose_type ty → M unit) :
  sail_live_st rs (Interface.Next (Interface.Choose ty) k) →
  ∃ r : Values.choose_type ty, True.
Proof.
  destruct ty; simpl; intros H;
    [by exists false|by exists 0%Z|by exists 0%Z|destruct H
    |by exists String.EmptyString|by exists 0%Z
    |by exists (Values.mword_of_int 0)].
Qed.

Lemma choose_val_q (ty : Values.ChooseType)
    (k : Values.choose_type ty → M unit) :
  quiet_tail (Interface.Next (Interface.Choose ty) k) →
  ∃ r : Values.choose_type ty, True.
Proof.
  destruct ty; simpl; intros H;
    [by exists false|by exists 0%Z|by exists 0%Z|destruct H
    |by exists String.EmptyString|by exists 0%Z
    |by exists (Values.mword_of_int 0)].
Qed.

(** The agent-state readings. *)
Definition psail_quiet (p : psail) : Prop :=
  match sp_m p with None => True | Some m => quiet_tail m end.

Definition shaped_res (p : psail) : Prop :=
  match sp_m p with None => True | Some m => sail_shaped m end.

(** LIVE AT THE RECORD'S OWN REGISTERS — the invariant shape stage C9
    settled on.  A step CHANGES [sp_regs], and [sail_live_st] threads exactly
    the writes the step makes, so this reading is preserved step for step
    ([sail_live_res_step]); a mid-instruction privilege write (trap entry
    sets [cur_privilege] INSIDE the monad) is covered for free, because the
    residual after it is measured at the state the write produced. *)
Definition live_res (p : psail) : Prop :=
  match sp_m p with None => True | Some m => sail_live_st (sp_regs p) m end.


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

Lemma cls_canon_nolog i l (c c' : wpcfg psail unit) :
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
    (c c' : wpcfg psail unit) : Prop :=
  ∃ l, lbl_quiet l ∧ wp_pf_step (pstep_unit (sail_step_ni next)) lbl_class_p i l c c'.

Lemma pf_quiet_nolog next i l c c' :
  lbl_quiet l → wp_pf_step (pstep_unit (sail_step_ni next)) lbl_class_p i l c c' → pc_log c' = pc_log c.
Proof.
  intros Hq Hstep. destruct Hstep as
    [cfg ag st' dd Hlk Hps
    |cfg ag aq lat base tvs asrc st' dd Hlk Hps Hr
    |cfg ag rl base data asrc vsrc kk st' dd Hlk Hps Hne Hkc
    |cfg ag aq rl base tvs data asrc vsrc kk st' dd Hlk Hps Hne Hlen Hr He Hkc
    |cfg ag pr pw sr sw st' dd Hlk Hps|cfg ag st' dd Hlk Hps
    |cfg ag rdw wsrc st' dd Hlk Hps|cfg ag csrc st' dd Hlk Hps
    |cfg ag st' dd Hlk Hps]; try done;
    by destruct Hq as [Hx|(?&?&?&?&Hx)]; inversion Hx.
Qed.

(** A step from an EXCLUSIVE-READ node carries a MEMORY label: the LTS
    offers exactly two arms there — the fused [LRmw] and the bare [LLoad]
    ([WeakSailLTS] delta (e)) — and nothing else fires. *)
Lemma excl_read_lbl next p l p' :
  sp_fence p = None → excl_read_node (sp_m p) → sail_step_ni next p l p' →
  (∃ aq base tvs, l = WeakPromise.LLoad aq false base tvs []) ∨
  (∃ aq rl base tvs data, l = WeakPromise.LRmw aq rl base tvs data [] []).
Proof.
  intros Hf Hex Hstep. rewrite /sail_step_ni Hf in Hstep.
  rewrite /excl_read_node in Hex.
  destruct (sp_m p) as [m|]; [|done].
  destruct m as [y|T oc k]; [done|].
  destruct oc; try done.
  rewrite /sail_mstep /= in Hstep. destruct Hex as [Hd Hlat].
  rewrite Hd in Hstep. destruct Hstep as (_ & Hstep).
  destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc|];
    try done.
  - destruct lat; [done|]. destruct asrc as [|x asrc']; [|done].
    left. by exists aq, base, tvs.
  - destruct asrc as [|x asrc']; [|done]. destruct vsrc as [|y vsrc']; [|done].
    right. by exists aq, rl, base, tvs, data.
Qed.

Lemma pf_solo_q_solo next i c c' : pf_solo_q next i c c' → pf_solo next i c c'.
Proof.
  intros (l & Hq & Hstep). exists l. split_and!; [exact Hstep| |].
  - apply cls_canon_nolog. exact (pf_quiet_nolog next i l c c' Hq Hstep).
  - destruct Hq as [->|(?&?&?&?&->)]; exact I.
Qed.

(** The MIRROR of [excl_read_lbl] ([WeakSailLTS] delta (e'')): a step from a
    CONDITIONAL-WRITE node carries an [LStore] — the RAM write arm is the
    only one that fires there, and since C4 it accepts any [ak_latest]. *)
Lemma con_write_lbl next p l p' :
  sp_fence p = None → con_write_node (sp_m p) → sail_step_ni next p l p' →
  ∃ rl base data, l = WeakPromise.LStore rl base data [] [].
Proof.
  intros Hf Hcw Hstep. rewrite /sail_step_ni Hf in Hstep.
  rewrite /con_write_node in Hcw.
  destruct (sp_m p) as [m|]; [|done].
  destruct m as [y|T oc k]; [done|].
  destruct oc; try done.
  rewrite /sail_mstep /= in Hstep. destruct Hcw as [Hd Hlat].
  rewrite Hd in Hstep. destruct Hstep as (-> & _ & _).
  by eexists _, _, _.
Qed.

(** …and a quiet step is a FUSED one ([WeakSailLTS2.pf_solo_f]) for free: at
    an exclusive-read node the LTS emits an [LLoad] or an [LRmw] and at a
    conditional-write node an [LStore], never a quiet label, so both of
    [pf_solo_f]'s obligations are vacuous there.  This is what lets the whole
    quiet skeleton of the completions below carry the "no half-window arm"
    export at no cost. *)
Lemma pf_solo_q_f next i c c' : pf_solo_q next i c c' → pf_solo_f next i c c'.
Proof.
  intros Hq. split_and!; [by apply pf_solo_q_solo| |].
  - intros (ag & Hlk & Hfe & Hex).
    destruct Hq as (l & Hql & Hstep).
    destruct Hstep as
      [cfg ag0 st' dd Hlk0 Hps
      |cfg ag0 aq lat base tvs asrc st' dd Hlk0 Hps Hr
      |cfg ag0 rl base data asrc vsrc kk st' dd Hlk0 Hps Hne
      |cfg ag0 aq rl base tvs data asrc vsrc kk st' dd
           Hlk0 Hps Hne Hlen Hr He Hkc
      |cfg ag0 pr pw sr sw st' dd Hlk0 Hps|cfg ag0 st' dd Hlk0 Hps
      |cfg ag0 rdw wsrc st' dd Hlk0 Hps|cfg ag0 csrc st' dd Hlk0 Hps
      |cfg ag0 st' dd Hlk0 Hps];
      simpl in Hlk; rewrite Hlk in Hlk0; injection Hlk0 as <-;
      try (by destruct Hql as [Hx|(?&?&?&?&Hx)]; inversion Hx);
      destruct (excl_read_lbl next (pa_st ag) _ st' Hfe Hex Hps)
        as [(? & ? & ? & Hl)|(? & ? & ? & ? & ? & Hl)]; inversion Hl.
  - intros (ag & Hlk & Hfe & Hcw).
    destruct Hq as (l & Hql & Hstep).
    destruct Hstep as
      [cfg ag0 st' dd Hlk0 Hps
      |cfg ag0 aq lat base tvs asrc st' dd Hlk0 Hps Hr
      |cfg ag0 rl base data asrc vsrc kk st' dd Hlk0 Hps Hne
      |cfg ag0 aq rl base tvs data asrc vsrc kk st' dd
           Hlk0 Hps Hne Hlen Hr He Hkc
      |cfg ag0 pr pw sr sw st' dd Hlk0 Hps|cfg ag0 st' dd Hlk0 Hps
      |cfg ag0 rdw wsrc st' dd Hlk0 Hps|cfg ag0 csrc st' dd Hlk0 Hps
      |cfg ag0 st' dd Hlk0 Hps];
      simpl in Hlk; rewrite Hlk in Hlk0; injection Hlk0 as <-;
      try (by destruct Hql as [Hx|(?&?&?&?&Hx)]; inversion Hx);
      destruct (con_write_lbl next (pa_st ag) _ st' Hfe Hcw Hps)
        as (? & ? & ? & Hl); inversion Hl.
Qed.

Lemma pf_solo_q_run_f next i c c' :
  rtc (pf_solo_q next i) c c' → rtc (pf_solo_f next i) c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [exact (pf_solo_q_f next i x y Hxy)|exact IH].
Qed.

Lemma both_true (a b : bool) : (a && b)%bool = true → a = true ∧ b = true.
Proof. by destruct a, b. Qed.

(** The FRAME of a quiet run: nothing at all moves except agent [i]'s
    program state and its (view-only) [wstate] — in particular the log, the
    image, every other agent, [i]'s promise set and [i]'s coherence floors
    are literally unchanged. *)
Definition qframe (i : agent) (c c' : wpcfg psail unit) : Prop :=
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
    [cfg ag st' dd Hlk Hps
    |cfg ag aq lat base tvs asrc st' dd Hlk Hps Hr
    |cfg ag rl base data asrc vsrc kk st' dd Hlk Hps Hne Hkc
    |cfg ag aq rl base tvs data asrc vsrc kk st' dd Hlk Hps Hne Hlen Hr He Hkc
    |cfg ag pr pw sr sw st' dd Hlk Hps|cfg ag st' dd Hlk Hps
    |cfg ag rdw wsrc st' dd Hlk Hps|cfg ag csrc st' dd Hlk Hps
    |cfg ag st' dd Hlk Hps];
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
Definition tframe (i : agent) (c c' : wpcfg psail unit) : Prop :=
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
  destruct (wp_pf_step_shape (pstep_unit (sail_step_ni next)) lbl_class_p i l c c' Hstep)
    as (Himg & _ & (ms & Hlog & Hall)).
  split_and!; [by exists ms|done| |].
  - intros j Hj. exact (wp_pf_step_frame (pstep_unit (sail_step_ni next)) lbl_class_p i l c c' j Hstep Hj).
  - intros j a. exact (wp_pf_step_obs_flr (pstep_unit (sail_step_ni next)) lbl_class_p i l c c' j a Hstep).
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
  intros Hb. apply IH. exact (wp_pf_step_bnd (pstep_unit (sail_step_ni next)) lbl_class_p i l x y Hxy Hb).
Qed.

(* ====================================================================== *)
(** ** 4. The completion, agent by agent

    Everything below is parametric in the instruction generator [next], as
    [WeakSailLTS]'s bracket is. *)

Section complete.
  Context (next : bool → M unit).

  Implicit Types c : wpcfg psail unit.

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
    - exists (WPCfgU (pc_img c) (pc_log c)
               (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags c))),
             (WPAgent st' (pa_ws ag) (pa_prom ag)).
      split_and!; [|exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
      exists WeakPromise.LSilent. split; [by left|].
      exact (PFSilent (pstep_unit (sail_step_ni next)) lbl_class_p i c ag st' tt Hlk Hstep).
    - exists (WPCfgU (pc_img c) (pc_log c)
               (<[i := WPAgent st' (fence_post (pa_ws ag) pr pw sr sw)
                         (pa_prom ag)]> (pc_ags c))),
             (WPAgent st' (fence_post (pa_ws ag) pr pw sr sw) (pa_prom ag)).
      split_and!; [|exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
      exists (WeakPromise.LFence pr pw sr sw).
      split; [right; by eexists _, _, _, _|].
      exact (PFFence (pstep_unit (sail_step_ni next)) lbl_class_p i c ag pr pw sr sw st' tt
               Hlk Hstep).
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
    - (* Choose: any inhabitant that is not a real will do *)
      destruct (choose_val_q ty k Hq) as (v & _).
      exists WeakPromise.LSilent, (k v), rs, None.
      split_and!; [rewrite /sail_step_ni /=; split;
                     [reflexivity|by exists v]
                  |by left|by eexists
                  |by apply (quiet_tail_choose ty k Hq)].
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
    window and a [wr_node].  Four little lemmas carry [sail_shaped] and
    [sail_live_st] across it; they are what the two preservation lemmas need.

    SINCE STAGE C8 THE CARRIER IS [sail_shaped] ITSELF (finding (O10)):
    [amo_tail] is gone, so the residual after a fused step is shaped for the
    ordinary reason — the silent prefix preserves the shape predicate, and
    the write node's own arm hands the shape of its continuation over.  The
    window's ADDRESS agreement, which [amo_tail] used to state, is supplied
    by the LTS arm ([WeakSailLTS2.amo_unbracket]'s header).  [amo_reach] —
    the walk that decided FUSED-vs-ABANDONED for the reader tail — is gone
    with it: at an exclusive read the completion now has exactly one arm. *)

Lemma sail_shaped_silent1 (m : M unit) rs (b : M unit * regstate) :
  sail_shaped m → silent1 (m, rs) b → sail_shaped b.1.
Proof.
  destruct m as [y|T oc k]; [by intros _ []|].
  destruct oc; simpl; try (by intros _ []);
    try (by intros Hsh ->; simpl; apply Hsh);
    try (by intros Hsh [ch ->]; simpl; apply Hsh).
Qed.

Lemma sail_shaped_silent_run (m m1 : M unit) rs rs1 :
  sail_shaped m → silent_run (m, rs) (m1, rs1) → sail_shaped m1.
Proof.
  intros Hsh Hrun.
  change m with (m, rs).1 in Hsh. change m1 with (m1, rs1).1.
  remember (m, rs) as a. remember (m1, rs1) as b. clear Heqa Heqb m rs m1 rs1.
  revert Hsh. induction Hrun as [|x y z Hxy _ IH]; [done|].
  intros Hsh. apply IH. destruct x as [mx rsx].
  exact (sail_shaped_silent1 mx rsx y Hsh Hxy).
Qed.

(** THE STATE THREADS THROUGH THE WINDOW.  A silent step may be a [RegRead]
    (answered from the current file) or a [RegWrite] (which MOVES the file),
    so the carrier is stated over the pair: liveness at [b.2] of [b.1]. *)
Lemma sail_live_st_silent1 (m : M unit) rs (b : M unit * regstate) :
  sail_live_st rs m → silent1 (m, rs) b → sail_live_st b.2 b.1.
Proof.
  destruct m as [y|T oc k]; [by intros _ []|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl;
    try (by intros _ []);
    (* RegRead: the LTS answers concretely, and both arms of the predicate
       give the continuation at exactly that value *)
    try (by intros Hlv ->; simpl; exact (sail_live_st_regread rs rg akk k Hlv));
    (* RegWrite threads the write; every other silent arm keeps [rs] *)
    try (by intros Hlv ->; simpl; apply Hlv);
    try (by intros Hlv [ch ->]; simpl; apply (sail_live_st_choose rs _ _ Hlv)).
Qed.

Lemma sail_live_st_silent_run (m m1 : M unit) rs rs1 :
  sail_live_st rs m → silent_run (m, rs) (m1, rs1) → sail_live_st rs1 m1.
Proof.
  intros Hlv Hrun.
  change (sail_live_st (m, rs).2 (m, rs).1) in Hlv.
  change (sail_live_st (m1, rs1).2 (m1, rs1).1).
  remember (m, rs) as a. remember (m1, rs1) as b. clear Heqa Heqb m rs m1 rs1.
  revert Hlv. induction Hrun as [|x y z Hxy _ IH]; [done|].
  intros Hlv. apply IH. destruct x as [mx rsx].
  exact (sail_live_st_silent1 mx rsx y Hlv Hxy).
Qed.

Lemma wr_node_mchild m1 rl base data m2 :
  wr_node m1 rl base data m2 → mchild m2 m1.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros (_ & _ & _ & _ & _ & _ & ->). by eexists.
Qed.

Lemma wr_node_shaped m1 rl base data m2 :
  sail_shaped m1 → wr_node m1 rl base data m2 → sail_shaped m2.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros (_ & Hsh) (_ & _ & _ & _ & _ & _ & ->). exact Hsh.
Qed.

Lemma wr_node_live rs m1 rl base data m2 :
  sail_live_st rs m1 → wr_node m1 rl base data m2 → sail_live_st rs m2.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros Hlv (_ & _ & _ & _ & _ & _ & ->). exact Hlv.
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
      + destruct Hstep as [_ ->]. simpl. by apply (proj2 Hsh).
      + destruct Hsh as (Hcoh & Hsh). destruct Hstep as (_ & Hstep).
        destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                      |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc
                      |csrc|]; try (by destruct Hstep).
        * (* the ONE load arm, exclusive or not *)
          destruct lat; [by destruct Hstep|].
          destruct asrc as [|x asrc']; [|by destruct Hstep].
          destruct Hstep as (_ & _ & _ & w & _ & ->). simpl. by apply Hsh.
        * (* the fused rmw: the shape crosses the silent window and the
             write node, both by the run's own evidence *)
          destruct asrc as [|x asrc']; [|by destruct Hstep].
          destruct vsrc as [|y vsrc']; [|by destruct Hstep].
          destruct Hstep as (_ & _ & _ & _ & _ & w & m1 & m2 & rs1
                             & _ & Hsil & Hwr & ->).
          simpl. eapply wr_node_shaped; [|exact Hwr].
          eapply sail_shaped_silent_run; [apply (Hsh w)|exact Hsil].
    - (* MemWrite *)
      destruct Hsh as (_ & Hsh).
      destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
      + destruct Hstep as [_ ->]. simpl. exact Hsh.
      + destruct Hstep as (_ & _ & ->). simpl. exact Hsh.
    - (* Choose *)
      destruct Hstep as (_ & ch & ->). simpl. by apply Hsh.
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
      try (by destruct Hstep as [_ ->]; simpl;
             exact (sail_live_st_regread (sp_regs p) rg akk k Hlv));
      try (by destruct Hstep as [_ ->]; simpl; apply Hlv).
    - (* MemRead *)
      destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
      + destruct Hstep as [_ ->]. simpl. by apply Hlv.
      + destruct Hstep as (_ & Hstep).
        destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                      |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc
                      |csrc|]; try (by destruct Hstep).
        * destruct lat; [by destruct Hstep|].
          destruct asrc as [|x asrc']; [|by destruct Hstep].
          destruct Hstep as (_ & _ & _ & w & _ & ->). simpl. by apply Hlv.
        * (* the fused rmw: the register file MOVES across the silent
             window, and the residual is measured at where it lands *)
          destruct asrc as [|x asrc']; [|by destruct Hstep].
          destruct vsrc as [|y vsrc']; [|by destruct Hstep].
          destruct Hstep as (_ & _ & _ & _ & _ & w & m1 & m2 & rs1
                             & _ & Hsil & Hwr & ->).
          simpl. eapply wr_node_live; [|exact Hwr].
          eapply sail_live_st_silent_run; [apply (Hlv w)|exact Hsil].
    - (* MemWrite *)
      destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
      + destruct Hstep as [_ ->]. simpl. exact Hlv.
      + destruct Hstep as (_ & _ & ->). simpl. exact Hlv.
    - (* Choose *)
      destruct Hstep as (_ & ch & ->). simpl.
      by apply (sail_live_st_choose _ ty k Hlv).
  Qed.

End residual.

(* ====================================================================== *)
(** ** 7. READER-TAIL COMPLETION

    An arbitrary shaped, live residual runs to its next instruction boundary
    in the promise-free machine.  The reads take FREE values — under
    [img_total] every byte's LATEST write is admissible
    ([WeakRobustBlocks.read_latest_*]) — and the appended messages carry the
    CANONICAL class [WeakSailLTS2.lbl_class], which is what makes every step
    a [pf_solo] one.

    AT AN EXCLUSIVE READ THE COMPLETION HAS NO CHOICE ANY MORE (stage C8,
    finding (O10)): the LTS's bare arm is one plain [LLoad] step to the
    read's own continuation, so the completion takes it and walks on, exactly
    as at a plain load.  What survives is the ACCOUNTING, because the ⇐
    bracket still refuses blocks containing a half-window arm
    ([WeakSailLTS2.fused_blk]): [tail_step]/[tail_run]/[tail_complete] carry
    a flag [fu : bool] and the conjunct
    [fu = true → rtc (pf_solo_f next i) c c'], i.e. "the completed run is
    bare-free", and an exclusive read (like a standalone conditional write)
    sets it to [false].  It costs nothing on the quiet skeleton:
    [pf_solo_q_f] says a quiet step is fused vacuously, because an
    exclusive-read node emits only [LLoad] or [LRmw]. *)

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

  Implicit Types c : wpcfg psail unit.

  (** The three non-quiet step wrappers.  [cls_canon] is vacuous for the
      load (the log is frozen) and holds by CONSTRUCTION for the store and
      the rmw (the class is [lbl_class] at the pre-state); [rmw_tight] is
      [True] but at the rmw, where it is the [lat := true] read the caller
      supplies from [read_latest]. *)

  Lemma pf_lstep (i : agent) c ag aq base tvs st' :
    pc_ags c !! i = Some ag →
    sail_step_ni next (pa_st ag) (WeakPromise.LLoad aq false base tvs []) st' →
    read_ok (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs →
    ∃ c' ag', pf_solo next i c c' ∧ pc_ags c' !! i = Some ag' ∧ pa_st ag' = st'
              ∧ pc_log c' = pc_log c.
  Proof.
    intros Hlk Hstep Hro.
    exists (WPCfgU (pc_img c) (pc_log c)
             (<[i := WPAgent st' (load_post_run (pa_ws ag) aq base tvs.*1)
                       (pa_prom ag)]> (pc_ags c))),
           (WPAgent st' (load_post_run (pa_ws ag) aq base tvs.*1) (pa_prom ag)).
    split_and!; [|exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done|done].
    exists (WeakPromise.LLoad aq false base tvs []). split_and!;
      [rewrite -(load_post_run_d_0 (pa_ws ag) aq base (tvs.*1));
       exact (PFLoad (pstep_unit (sail_step_ni next)) lbl_class_p i c ag aq
                false base tvs [] st' tt Hlk Hstep Hro)
      |by apply cls_canon_nolog|exact I].
  Qed.

  (** The store wrapper.  It cannot claim [pf_solo_f] outright since C4: a
      step from a STANDALONE conditional-write node is an [LStore] too
      ([WeakSailLTS] delta (e'')) and is exactly what [pf_solo_f] excludes.
      So the fused reading is handed back conditionally, and the caller —
      which knows the node's [ak_latest] — decides. *)
  Lemma pf_sstep (i : agent) c ag rl base data st' :
    pc_ags c !! i = Some ag →
    sail_step_ni next (pa_st ag) (WeakPromise.LStore rl base data [] []) st' →
    data ≠ [] →
    ∃ c' ag', pf_solo next i c c' ∧
              (¬ at_con_write i c → pf_solo_f next i c c') ∧
              pc_ags c' !! i = Some ag' ∧ pa_st ag' = st'.
  Proof.
    intros Hlk Hstep Hne.
    set (kc := lbl_class (WeakPromise.LStore rl base data [] []) (pa_ws ag)).
    have Hsolo : pf_solo next i c
        (WPCfgU (pc_img c) (pc_log c ++ [WMsg base data (Some i) kc])
           (<[i := WPAgent st'
                     (store_post_run (pa_ws ag) rl base (length data)
                        (S (length (pc_log c)))) (pa_prom ag)]> (pc_ags c))).
    { exists (WeakPromise.LStore rl base data [] []). split_and!.
      - rewrite -(store_post_run_d_0 (pa_ws ag) rl base (length data)
                    (S (length (pc_log c)))).
        exact (PFStore (pstep_unit (sail_step_ni next)) lbl_class_p i c ag rl
                 base data [] [] kc st' tt Hlk Hstep Hne eq_refl).
      - intros ag2 msg Hag2 Heq. simpl in Heq.
        apply app_inv_head in Heq. injection Heq as <-.
        rewrite Hlk in Hag2. by injection Hag2 as <-.
      - exact I. }
    exists (WPCfgU (pc_img c) (pc_log c ++ [WMsg base data (Some i) kc])
             (<[i := WPAgent st'
                       (store_post_run (pa_ws ag) rl base (length data)
                          (S (length (pc_log c)))) (pa_prom ag)]> (pc_ags c))),
           (WPAgent st'
              (store_post_run (pa_ws ag) rl base (length data)
                 (S (length (pc_log c)))) (pa_prom ag)).
    split_and!;
      [exact Hsolo
      |intros Hncw; split_and!;
         [exact Hsolo
         |by intros _ Hlog; exact (app_snoc_absurd _ _ (eq_sym Hlog))
         |exact Hncw]
      |exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
  Qed.

  Lemma pf_rstep (i : agent) c ag aq rl base tvs data st' :
    pc_ags c !! i = Some ag →
    sail_step_ni next (pa_st ag)
      (WeakPromise.LRmw aq rl base tvs data [] []) st' →
    data ≠ [] → length tvs = length data →
    read_ok (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs →
    read_ok (pc_img c) (pc_log c) (pa_ws ag) aq true base tvs →
    excl_ok (pc_log c) i base tvs (S (length (pc_log c))) →
    ∃ c' ag', pf_solo_f next i c c' ∧ pc_ags c' !! i = Some ag' ∧ pa_st ag' = st'.
  Proof.
    intros Hlk Hstep Hne Hlen Hro Hrot Hex.
    have Hncw : ¬ at_con_write i c.
    { intros (ag0 & Hlk0 & Hfe & Hcw). rewrite Hlk in Hlk0.
      injection Hlk0 as <-.
      destruct (con_write_lbl next (pa_st ag) _ st' Hfe Hcw Hstep)
        as (? & ? & ? & Hl). inversion Hl. }
    set (kc := lbl_class (WeakPromise.LRmw aq rl base tvs data [] [])
                 (pa_ws ag)).
    exists (WPCfgU (pc_img c) (pc_log c ++ [WMsg base data (Some i) kc])
             (<[i := WPAgent st'
                       (store_post_run
                          (load_post_run (pa_ws ag) aq base tvs.*1)
                          rl base (length data) (S (length (pc_log c))))
                       (pa_prom ag)]> (pc_ags c))),
           (WPAgent st'
              (store_post_run (load_post_run (pa_ws ag) aq base tvs.*1)
                 rl base (length data) (S (length (pc_log c))))
              (pa_prom ag)).
    split_and!;
      [split_and!;
         [|by intros _ Hlog; exact (app_snoc_absurd _ _ (eq_sym Hlog))
          |exact Hncw]
      |exact (lookup_insert_at (pc_ags c) i ag _ Hlk)|done].
    exists (WeakPromise.LRmw aq rl base tvs data [] []). split_and!.
    - rewrite -(load_post_run_d_0 (pa_ws ag) aq base (tvs.*1))
              -(store_post_run_d_0
                  (load_post_run_d (pa_ws ag) aq 0%nat base (tvs.*1))
                  rl base (length data) (S (length (pc_log c)))).
      exact (PFRmw (pstep_unit (sail_step_ni next)) lbl_class_p i c ag aq rl
               base tvs data [] [] kc st' tt Hlk Hstep Hne Hlen Hro Hex
               eq_refl).
    - intros ag2 msg Hag2 Heq. simpl in Heq.
      apply app_inv_head in Heq. injection Heq as <-.
      rewrite Hlk in Hag2. by injection Hag2 as <-.
    - intros ag2 Hag2. rewrite Hlk in Hag2. by injection Hag2 as <-.
  Qed.

  (** The residual after one step of the tail: either the agent has reached
      the boundary, or it sits at a STRICTLY SMALLER residual which is still
      shaped and live (with a possibly parked fence, which [pf_unpark]
      fires).  NO DEVICE SIDE CONDITION: since stage D the device arms are
      TOTAL, so a completion never gets stuck at one and never has to know
      what the fabric would answer. *)
  Definition tail_post (i : agent) (m : M unit) (iq : istream)
      (c' : wpcfg psail unit) (ag' : wpagent psail) : Prop :=
    (sp_m (pa_st ag') = None ∧ sp_fence (pa_st ag') = None) ∨
    ∃ (m' : M unit) (rs' : regstate) (d' : dev_state)
      (fo : option (bool * bool * bool * bool)),
      pa_st ag' = PSail (Some m') rs' d' fo iq ∧
      tc mchild m' m ∧ sail_shaped m' ∧ sail_live_st rs' m'.

  (** The QUIET arms of the tail, factored: one silent (or barrier) step to a
      smaller residual. *)
  Lemma tail_qcase (i : agent) c ag (l : wlabel) (m m' : M unit) rs' d'
      fo iq :
    pc_ags c !! i = Some ag → lbl_quiet l →
    sail_step_ni next (pa_st ag) l (PSail (Some m') rs' d' fo iq) →
    tc mchild m' m → sail_shaped m' → sail_live_st rs' m' →
    ∃ c' ag' (fu : bool), pf_solo next i c c' ∧
              (fu = true → pf_solo_f next i c c') ∧
              pc_ags c' !! i = Some ag' ∧ tail_post i m iq c' ag'.
  Proof.
    intros Hlk Hql Hstep Hch Hsh Hlv.
    destruct (pf_qstep next i c ag l _ Hlk Hql Hstep)
      as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
    exists c1, ag1, true. split_and!;
      [exact (pf_solo_q_solo next i c c1 Hs1)
      |by intros _; apply pf_solo_q_f|exact Hlk1|].
    right. exists m', rs', d', fo.
    split_and!; [exact Hpa1|exact Hch|exact Hsh|exact Hlv].
  Qed.

  (** ONE STEP OF THE READER TAIL. *)
  Lemma tail_step (i : agent) c ag (m : M unit) rs (d : dev_state) iq :
    img_total (pc_img c) → cfg_bnd c →
    pc_ags c !! i = Some ag → pa_st ag = PSail (Some m) rs d None iq →
    sail_shaped m → sail_live_st rs m →
    ∃ c' ag' (fu : bool), pf_solo next i c c' ∧
              (fu = true → pf_solo_f next i c c') ∧
              pc_ags c' !! i = Some ag' ∧ tail_post i m iq c' ag'.
  Proof.
    intros Him Hbnd Hlk Hst Hsh Hlv.
    have Hws : ws_bounded (pa_ws ag) (length (pc_log c)) := Hbnd i ag Hlk.
    destruct m as [y|T oc k].
    { (* Ret: the last silent step, back to the boundary *)
      destruct (pf_qstep next i c ag WeakPromise.LSilent
                  (PSail None rs d None iq) Hlk (or_introl eq_refl)
                  ltac:(rewrite Hst /sail_step_ni /=; by split))
        as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
      exists c1, ag1, true. split_and!;
        [exact (pf_solo_q_solo next i c c1 Hs1)
        |by intros _; apply pf_solo_q_f|exact Hlk1|].
      left. by rewrite Hpa1. }
    destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                   |epa|tst|tnd|A eo|msg| | |ty| |msg2];
      simpl in Hsh, Hlv; try (by destruct Hlv).
    - (* RegRead *)
      apply (tail_qcase i c ag WeakPromise.LSilent _
               (k (register_lookup rg rs)) rs d None iq Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh
        |exact (sail_live_st_regread rs rg akk k Hlv)].
    - (* RegWrite *)
      apply (tail_qcase i c ag WeakPromise.LSilent _
               (k tt) (register_set rg rv rs) d None iq Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* MemRead *)
      destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
      + (* MMIO: the hart's own fabric serves it, silently and TOTALLY *)
        apply (tail_qcase i c ag WeakPromise.LSilent _
                 (k (inl ((dev_read_t d (Interface.ReadReq.pa req) nn).1, None)))
                 rs (dev_read_t d (Interface.ReadReq.pa req) nn).2 None iq
                 Hlk (or_introl eq_refl));
          [rewrite Hst /sail_step_ni /sail_mstep /= Hd; by split
          |apply tc_once; by eexists|by apply (proj2 Hsh)|by apply Hlv].
      + (* A RAM READ, exclusive or not ([WeakSailLTS] delta (e), stage C8).
             ONE arm: the plain [LLoad] to the read's own continuation.  What
             differs between the two access kinds is only whether the step is
             a half-window arm, i.e. whether the completion can export
             [fused_blk]-compatibility — so an EXCLUSIVE read sets
             [fu := false], exactly as a standalone conditional write does
             below. *)
        destruct Hsh as (Hcoh & Hsh).
        destruct (read_latest_exists (pc_img c) (pc_log c)
                    (pa_z (Interface.ReadReq.pa req)) (N.to_nat nn) Him)
          as (tvs & Hlent & Hrl).
        have Hlent2 : length tvs.*2 = N.to_nat nn by rewrite length_fmap.
        destruct (bytes_to_word nn tvs.*2 Hlent2) as (w & Hw).
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
                            [reflexivity|reflexivity|exact Hlent|];
                          exists w; split; [exact Hw|reflexivity])
                    Hro)
          as (c1 & ag1 & Hs1 & Hlk1 & Hpa1 & Hlog1).
        destruct (ak_latest (classify (Interface.ReadReq.access_kind req)))
          eqn:Hlat.
        * (* THE BARE EXCLUSIVE READ: no fused export *)
          exists c1, ag1, false. split_and!; [exact Hs1|done|exact Hlk1|].
          right. exists (k (inl (w, None))), rs, d, None.
          split_and!; [exact Hpa1|apply tc_once; by eexists
                      |by apply Hsh|by apply Hlv].
        * exists c1, ag1, true. split_and!; [exact Hs1| |exact Hlk1|].
          { (* a PLAIN load is fused-vacuously: the node is neither an
               exclusive read nor a conditional write *)
            intros _. split_and!; [exact Hs1| |].
            - intros (ag0 & Hlk0 & _ & Hex). rewrite Hlk in Hlk0.
              injection Hlk0 as <-. rewrite Hst /= Hlat in Hex.
              by destruct Hex as [_ ?].
            - intros (ag0 & Hlk0 & _ & Hcw). rewrite Hlk in Hlk0.
              injection Hlk0 as <-. by rewrite Hst /= in Hcw. }
          right. exists (k (inl (w, None))), rs, d, None.
          split_and!; [exact Hpa1|apply tc_once; by eexists
                      |by apply Hsh|by apply Hlv].
    - (* MemWrite *)
      destruct Hsh as (Hn & Hsh).
      destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
      + apply (tail_qcase i c ag WeakPromise.LSilent _
                 (k (inl None)) rs
                 (dev_write_t d (Interface.WriteReq.pa req) nn
                    (Interface.WriteReq.value req)) None iq
                 Hlk (or_introl eq_refl));
          [rewrite Hst /sail_step_ni /sail_mstep /= Hd; by split
          |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
      + (* A RAM WRITE, conditional or not ([WeakSailLTS] delta (e'')).  The
             step is the same [LStore] either way; what differs is whether it
             is a half-window arm, i.e. whether the completion can export
             [fused_blk]-compatibility — so a STANDALONE conditional write
             sets [fu := false], exactly as the bare exclusive read does. *)
        destruct (pf_sstep i c ag
                    (ak_sync (classify (Interface.WriteReq.access_kind req)))
                    (pa_z (Interface.WriteReq.pa req))
                    (wbytes nn (Interface.WriteReq.value req))
                    (PSail (Some (k (inl None))) rs d None iq) Hlk
                    ltac:(rewrite Hst /sail_step_ni /sail_mstep /= Hd;
                          split_and!; [reflexivity|exact Hn|reflexivity])
                    ltac:(by apply wbytes_nonnil))
          as (c1 & ag1 & Hs1 & Hfu1 & Hlk1 & Hpa1).
        destruct (ak_latest (classify (Interface.WriteReq.access_kind req)))
          eqn:Hlat.
        * (* THE STANDALONE CONDITIONAL WRITE: no fused export *)
          exists c1, ag1, false. split_and!; [exact Hs1|done|exact Hlk1|].
          right. exists (k (inl None)), rs, d, None.
          split_and!; [exact Hpa1|apply tc_once; by eexists
                      |exact Hsh|exact Hlv].
        * exists c1, ag1, true. split_and!; [exact Hs1| |exact Hlk1|].
          { intros _. apply Hfu1.
            intros (ag0 & Hlk0 & _ & Hcw). rewrite Hlk in Hlk0.
            injection Hlk0 as <-. rewrite Hst /= Hd Hlat in Hcw.
            by destruct Hcw as [_ ?]. }
          right. exists (k (inl None)), rs, d, None.
          split_and!; [exact Hpa1|apply tc_once; by eexists
                      |exact Hsh|exact Hlv].
    - (* InstrAnnounce *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* BranchAnnounce *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* Barrier: the label table, and the possible parked second fence *)
      apply (tail_qcase i c ag (barrier_lbl bk).1 _ (k tt) rs d
               (barrier_lbl bk).2 iq Hlk (barrier_lbl_quiet bk));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* CacheOp *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* TlbOp *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* TakeException *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* ReturnException *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* TranslationStart *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* TranslationEnd *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* CycleCount *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* GetCycleCount *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k 0%Z) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
    - (* Choose *)
      destruct (choose_val rs ty k Hlv) as (v & _).
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k v) rs d None
               iq Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; split;
           [reflexivity|by exists v]
        |apply tc_once; by eexists|by apply Hsh
        |by apply (sail_live_st_choose rs ty k Hlv)].
    - (* Message *)
      apply (tail_qcase i c ag WeakPromise.LSilent _ (k tt) rs d None iq
               Hlk (or_introl eq_refl));
        [rewrite Hst /sail_step_ni /=; by split
        |apply tc_once; by eexists|by apply Hsh|by apply Hlv].
  Qed.

  (** THE READER TAIL, run to the boundary.  The induction is on
      [tc mchild]: every arm descends to an immediate continuation.  (The
      [tc] rather than [mchild] is the LTS's fused arm, which jumps across a
      whole silent window — the completion never takes it, but [tail_post] is
      stated over the general residual.) *)
  Lemma tail_run : ∀ (m : M unit) (i : agent) c ag rs (d : dev_state) iq,
    img_total (pc_img c) → cfg_bnd c →
    pc_ags c !! i = Some ag → pa_st ag = PSail (Some m) rs d None iq →
    sail_shaped m → sail_live_st rs m →
    ∃ c' ag' (fu : bool), rtc (pf_solo next i) c c' ∧
              (fu = true → rtc (pf_solo_f next i) c c') ∧
              pc_ags c' !! i = Some ag' ∧
              sp_m (pa_st ag') = None ∧ sp_fence (pa_st ag') = None.
  Proof.
    intros m. induction m as [m IH] using (well_founded_ind msub_wf).
    intros i c ag rs d iq Him Hbnd Hlk Hst Hsh Hlv.
    destruct (tail_step i c ag m rs d iq Him Hbnd Hlk Hst Hsh Hlv)
      as (c1 & ag1 & fu1 & Hs1 & Hfu1 & Hlk1
          & [[Hm1 Hf1]
            |(m' & rs' & d' & fo & Hpa1 & Hch & Hsh' & Hlv')]).
    - exists c1, ag1, fu1.
      split_and!; [by apply rtc_once| |exact Hlk1|exact Hm1|exact Hf1].
      intros Hb. apply rtc_once. by apply Hfu1.
    - destruct (pf_unpark next i c1 ag1 Hlk1) as (c2 & ag2 & Hs2 & Hlk2 & Hpa2).
      rewrite Hpa1 /= in Hpa2.
      have Hrun : rtc (pf_solo next i) c c2.
      { eapply rtc_l; [exact Hs1|exact (pf_solo_q_run_solo next i c1 c2 Hs2)]. }
      have Hbnd2 : cfg_bnd c2 := pf_solo_run_bnd next i c c2 Hrun Hbnd.
      have Him2 : img_total (pc_img c2).
      { destruct (pf_solo_run_tframe next i c c2 Hrun) as (_ & Himg & _ & _).
        by rewrite Himg. }
      destruct (IH m' Hch i c2 ag2 rs' d' iq Him2 Hbnd2 Hlk2 Hpa2 Hsh' Hlv')
        as (c3 & ag3 & fu3 & Hs3 & Hfu3 & Hlk3 & Hm3 & Hf3).
      exists c3, ag3, (fu1 && fu3)%bool. split_and!;
        [by etrans; [exact Hrun|exact Hs3]| |exact Hlk3|exact Hm3|exact Hf3].
      intros [Hb1 Hb3]%both_true.
      etrans; [|exact (Hfu3 Hb3)].
      eapply rtc_l; [exact (Hfu1 Hb1)|exact (pf_solo_q_run_f next i c1 c2 Hs2)].
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
    sail_shaped m → sail_live_st (sp_regs (pa_st ag)) m →
    ∃ c' ag' ms (fu : bool),
      rtc (pf_solo next i) c c' ∧
      (fu = true → rtc (pf_solo_f next i) c c') ∧
      pc_ags c' !! i = Some ag' ∧ at_boundary i c' ∧
      sp_fence (pa_st ag') = None ∧
      pc_log c' = pc_log c ++ ms ∧
      Forall (λ mq, wm_tid mq = Some i) ms ∧
      pc_img c' = pc_img c ∧ cfg_bnd c' ∧
      (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j) ∧
      (∀ j a, (obs_flr c j a ≤ obs_flr c' j a)%nat).
  Proof.
    intros Him Hbnd Hlk Hm Hsh Hlv.
    destruct (pf_unpark next i c ag Hlk) as (c1 & ag1 & Hs1 & Hlk1 & Hpa1).
    have Hrun01 : rtc (pf_solo next i) c c1
      := pf_solo_q_run_solo next i c c1 Hs1.
    have Hbnd1 : cfg_bnd c1 := pf_solo_run_bnd next i c c1 Hrun01 Hbnd.
    have Him1 : img_total (pc_img c1).
    { destruct (pf_solo_q_run_qframe next i c c1 Hs1) as (_ & Himg & _ & _).
      by rewrite Himg. }
    rewrite Hm in Hpa1.
    destruct (tail_run m i c1 ag1 (sp_regs (pa_st ag)) (sp_dev (pa_st ag))
                (sp_irq (pa_st ag)) Him1 Hbnd1 Hlk1 Hpa1 Hsh Hlv)
      as (c2 & ag2 & fu & Hs2 & Hfu & Hlk2 & Hm2 & Hf2).
    have Hrun : rtc (pf_solo next i) c c2
      by etrans; [exact Hrun01|exact Hs2].
    destruct (pf_solo_run_tframe next i c c2 Hrun)
      as ((ms & Hlog & Hall) & Himg & Hfr & Hobs).
    exists c2, ag2, ms, fu. split_and!;
      [exact Hrun| |exact Hlk2|by exists ag2|exact Hf2|exact Hlog|exact Hall
      |exact Himg|exact (pf_solo_run_bnd next i c c2 Hrun Hbnd)
      |exact Hfr|exact Hobs].
    intros Hb. etrans; [exact (pf_solo_q_run_f next i c c1 Hs1)|exact (Hfu Hb)].
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
Lemma wp_pf_step_transplant {P : Type} (pstep : P → unit → wlabel → P → unit → Prop)
    (pcls : P → wlabel → wstate → wm_class)
    i l (c c' d : wpcfg P unit) :
  wp_pf_step pstep pcls i l c c' →
  pc_img d = pc_img c → pc_log d = pc_log c → pc_ags d !! i = pc_ags c !! i →
  ∃ ag', pc_ags c' = <[i := ag']> (pc_ags c) ∧ pc_img c' = pc_img c ∧
         wp_pf_step pstep pcls i l d
           (WPCfgU (pc_img c') (pc_log c') (<[i := ag']> (pc_ags d))).
Proof.
  intros Hstep Himg Hlog Hags.
  have Hdev : pc_dev c = pc_dev d by destruct (pc_dev c), (pc_dev d).
  destruct Hstep as
    [cfg ag st' dd Hlk Hps
    |cfg ag aq lat base tvs asrc st' dd Hlk Hps Hr
    |cfg ag rl base data asrc vsrc kk st' dd Hlk Hps Hne Hkc
    |cfg ag aq rl base tvs data asrc vsrc kk st' dd Hlk Hps Hne Hlen Hr He Hkc
    |cfg ag pr pw sr sw st' dd Hlk Hps|cfg ag st' dd Hlk Hps
    |cfg ag rdw wsrc st' dd Hlk Hps|cfg ag csrc st' dd Hlk Hps
    |cfg ag st' dd Hlk Hps];
    destruct dd; rewrite Hdev in Hps;
    have Hlkd : pc_ags d !! i = Some ag by rewrite Hags.
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog. exact (PFSilent pstep pcls i d ag st' tt Hlkd Hps).
  - have Hr' : read_ok_d (pc_img d) (pc_log d) (pa_ws ag) aq lat base tvs
                 (srcs_view (pa_ws ag) asrc)
      by rewrite Himg Hlog.
    eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFLoad pstep pcls i d ag aq lat base tvs asrc st' tt Hlkd Hps Hr').
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFStore pstep pcls i d ag rl base data asrc vsrc kk st' tt
             Hlkd Hps Hne Hkc).
  - have Hr' : read_ok_d (pc_img d) (pc_log d) (pa_ws ag) aq false base tvs
                 (srcs_view (pa_ws ag) asrc)
      by rewrite Himg Hlog.
    have He' : excl_ok (pc_log d) i base tvs (S (length (pc_log d)))
      by rewrite Hlog.
    eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFRmw pstep pcls i d ag aq rl base tvs data asrc vsrc kk st' tt
             Hlkd Hps Hne Hlen Hr' He' Hkc).
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFFence pstep pcls i d ag pr pw sr sw st' tt Hlkd Hps).
  - (* dev: [PFSilent]'s twin *)
    eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog. exact (PFDev pstep pcls i d ag st' tt Hlkd Hps).
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog.
    exact (PFRegW pstep pcls i d ag rdw wsrc st' tt Hlkd Hps).
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog. exact (PFCtrl pstep pcls i d ag csrc st' tt Hlkd Hps).
  - eexists. split_and!; [reflexivity|reflexivity|]. simpl.
    rewrite -Himg -Hlog. exact (PFInstr pstep pcls i d ag st' tt Hlkd Hps).
Qed.

(** The QUIET transplant, which needs only the stepping agent's slot: a
    silent/fence step neither reads nor writes the log or the image. *)
Lemma quiet_transplant {P : Type} (pstep : P → unit → wlabel → P → unit → Prop)
    (pcls : P → wlabel → wstate → wm_class)
    k lk (c1 c2 d : wpcfg P unit) :
  wp_pf_step pstep pcls k lk c1 c2 → lbl_quiet lk →
  pc_ags d !! k = pc_ags c1 !! k →
  ∃ agk', pc_ags c2 = <[k := agk']> (pc_ags c1) ∧
          pc_img c2 = pc_img c1 ∧ pc_log c2 = pc_log c1 ∧
          wp_pf_step pstep pcls k lk d
            (WPCfgU (pc_img d) (pc_log d) (<[k := agk']> (pc_ags d))).
Proof.
  intros Hstep Hq Hags.
  have Hdev : pc_dev c1 = pc_dev d by destruct (pc_dev c1), (pc_dev d).
  destruct Hstep as
    [cfg ag st' dd Hlk Hps
    |cfg ag aq lat base tvs asrc st' dd Hlk Hps Hr
    |cfg ag rl base data asrc vsrc kc st' dd Hlk Hps Hne Hkc
    |cfg ag aq rl base tvs data asrc vsrc kc st' dd Hlk Hps Hne Hlen Hr He Hkc
    |cfg ag pr pw sr sw st' dd Hlk Hps|cfg ag st' dd Hlk Hps
    |cfg ag rdw wsrc st' dd Hlk Hps|cfg ag csrc st' dd Hlk Hps
    |cfg ag st' dd Hlk Hps];
    try (by destruct Hq as [Hx|(?&?&?&?&Hx)]; inversion Hx);
    destruct dd; rewrite Hdev in Hps;
    have Hlkd : pc_ags d !! k = Some ag by rewrite Hags.
  - eexists. split_and!; [reflexivity|reflexivity|reflexivity|].
    exact (PFSilent pstep pcls k d ag st' tt Hlkd Hps).
  - eexists. split_and!; [reflexivity|reflexivity|reflexivity|].
    exact (PFFence pstep pcls k d ag pr pw sr sw st' tt Hlkd Hps).
Qed.

(** THE COMMUTATION.  ([lbl_quiet lk] is the disjunction
    "[lk = LSilent] or [lk] is a fence".) *)
Lemma pf_local_commute {P : Type} (pstep : P → unit → wlabel → P → unit → Prop)
    (pcls : P → wlabel → wstate → wm_class)
    i l k lk (c c1 c2 : wpcfg P unit) :
  wp_pf_step pstep pcls i l c c1 → wp_pf_step pstep pcls k lk c1 c2 → k ≠ i →
  lbl_quiet lk →
  ∃ c1', wp_pf_step pstep pcls k lk c c1' ∧ wp_pf_step pstep pcls i l c1' c2.
Proof.
  intros Hi Hk Hne Hq.
  have Hfr : pc_ags c !! k = pc_ags c1 !! k.
  { symmetry. exact (wp_pf_step_frame pstep pcls i l c c1 k Hi Hne). }
  destruct (quiet_transplant pstep pcls k lk c1 c2 c Hk Hq Hfr)
    as (agk' & Hags2 & Himg2 & Hlog2 & Hstepk).
  exists (WPCfgU (pc_img c) (pc_log c) (<[k := agk']> (pc_ags c))).
  split; [exact Hstepk|].
  destruct (wp_pf_step_transplant pstep pcls i l c c1
              (WPCfgU (pc_img c) (pc_log c) (<[k := agk']> (pc_ags c)))
              Hi eq_refl eq_refl
              ltac:(simpl; apply lookup_insert_other; by intros ->))
    as (ag' & Hags1 & Himg1 & Hstepi).
  have Hc2 : c2 = WPCfgU (pc_img c1) (pc_log c1)
                    (<[i := ag']> (<[k := agk']> (pc_ags c))).
  { destruct c2 as [img2 log2 dv2 ags2]. destruct dv2.
    simpl in Himg2, Hlog2, Hags2.
    rewrite Himg2 Hlog2 Hags2 Hags1.
    by rewrite (list_insert_commute (pc_ags c) k i agk' ag' Hne). }
  rewrite Hc2. exact Hstepi.
Qed.

(** The two run relations the surgery is stated over: [k]'s own quiet steps,
    and everybody else's steps. *)
Definition pf_quiet_run {P : Type} (pstep : P → unit → wlabel → P → unit → Prop)
    (pcls : P → wlabel → wstate → wm_class)
    (k : agent) (c c' : wpcfg P unit) : Prop :=
  ∃ lk, lbl_quiet lk ∧ wp_pf_step pstep pcls k lk c c'.

Definition pf_other_run {P : Type} (pstep : P → unit → wlabel → P → unit → Prop)
    (pcls : P → wlabel → wstate → wm_class)
    (k : agent) (c c' : wpcfg P unit) : Prop :=
  ∃ j l, j ≠ k ∧ wp_pf_step pstep pcls j l c c'.

Lemma pf_quiet_commute_run {P : Type} (pstep : P → unit → wlabel → P → unit → Prop)
    (pcls : P → wlabel → wstate → wm_class)
    k (c c1 c2 : wpcfg P unit) :
  rtc (pf_other_run pstep pcls k) c c1 → pf_quiet_run pstep pcls k c1 c2 →
  ∃ c1', pf_quiet_run pstep pcls k c c1' ∧ rtc (pf_other_run pstep pcls k) c1' c2.
Proof.
  intros Hrun. revert c2. induction Hrun as [|x y z Hxy _ IH]; intros c2 Hq.
  { exists c2. split; [exact Hq|apply rtc_refl]. }
  destruct (IH c2 Hq) as (y' & (lk & Hlk & Hstepk) & Hrest).
  destruct Hxy as (j & lj & Hjne & Hstepj).
  destruct (pf_local_commute pstep pcls j lj k lk x y y' Hstepj Hstepk
              (not_eq_sym Hjne) Hlk)
    as (x' & Hqx & Hjx).
  exists x'. split; [by exists lk|].
  eapply rtc_l; [exists j, lj; split; [exact Hjne|exact Hjx]|exact Hrest].
Qed.

(** THE SPLICE.  A contiguous quiet run of agent [k] appended after a run of
    OTHER agents' steps can be moved to the FRONT of that run — which is how
    an epilogue completion is inserted right after its agent's last event. *)
Lemma pf_run_insert_local {P : Type} (pstep : P → unit → wlabel → P → unit → Prop)
    (pcls : P → wlabel → wstate → wm_class)
    k (c c1 c2 : wpcfg P unit) :
  rtc (pf_other_run pstep pcls k) c c1 → rtc (pf_quiet_run pstep pcls k) c1 c2 →
  ∃ c1', rtc (pf_quiet_run pstep pcls k) c c1' ∧
         rtc (pf_other_run pstep pcls k) c1' c2.
Proof.
  intros Hoth Hqui. revert c Hoth.
  induction Hqui as [|x y z Hxy _ IH]; intros c Hoth.
  { exists c. split; [apply rtc_refl|exact Hoth]. }
  destruct (pf_quiet_commute_run pstep pcls k c x y Hoth Hxy)
    as (c1' & Hq1 & Hoth1).
  destruct (IH c1' Hoth1) as (c2' & Hq2 & Hoth2).
  exists c2'. split; [|exact Hoth2]. eapply rtc_l; [exact Hq1|exact Hq2].
Qed.

(** A quiet solo run at the Sail LTS IS a [pf_quiet_run], so the splice
    applies directly to [quiet_complete_q]'s output. *)
Lemma pf_solo_q_quiet_run next i c c' :
  pf_solo_q next i c c' → pf_quiet_run (pstep_unit (sail_step_ni next)) lbl_class_p i c c'.
Proof. by intros (l & Hq & Hstep); exists l. Qed.

Lemma pf_solo_q_run_quiet_run next i c c' :
  rtc (pf_solo_q next i) c c' → rtc (pf_quiet_run (pstep_unit (sail_step_ni next)) lbl_class_p i) c c'.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [exact (pf_solo_q_quiet_run next i x y Hxy)|exact IH].
Qed.

(* ====================================================================== *)
(** ** 9. THE SEIP KIT: a mid-block interrupt delivery commutes FORWARD
       (lift stage A3 of [claude-notes/projects/weak-memory-premises.md])

    [WeakSailLTS.sail_step]'s [irq_deliver] arm fires at ANY point, including
    strictly inside an instruction — which is what the hardware does, and
    what the lift's [Hirqb] premise ("deliveries only at block boundaries")
    excludes.  This section is the reusable core of the fix: a delivery
    landing mid-block is MOVED FORWARD to the next instruction boundary,
    which is sound exactly when the residual monad neither reads nor writes
    the delivered pin.  Stage B consumes (a) [seip_free] and its
    preservation along in-block steps, and (b) the packaged reordering
    [irq_commute_fwd].

    THE ARGUMENT.  [irq_deliver] is [register_set sig_seip v] and nothing
    else.  If the rest of the block never READS [sig_seip], running it from
    [rs] and from [register_set sig_seip v rs] produces THE SAME LABELS and
    THE SAME residual monads, with register files agreeing off [sig_seip]
    ([sail_mstep_frame], [sail_step_ni_frame]); if it never WRITES
    [sig_seip] either, the pin still holds [v] at the boundary
    ([sail_step_ni_stable]), so re-appending the delivery there lands on the
    same state.  Everything is proved for an ARBITRARY excluded-register set
    [X] ([regs_agree X] / [regs_free X]), because the [X := ∅] instance is
    the register-file congruence the reordering also needs (§9.7).

    ------------------------------------------------------------------------
    THREE DEVIATIONS, all forced; read them before consuming the kit.

    (a) [seip_free] FORBIDS [RegWrite sig_seip] AS WELL AS [RegRead
        sig_seip], where the stage-A3 statement asked only for the read.
        The write restriction is NOT a convenience: without it the
        reordering is FALSE.  If the block writes the pin ([y]) after the
        delivery ([v]), then delivery-then-block ends with [y] and
        block-then-delivery ends with [v], and the difference is visible to
        the next instruction — the two orders are genuinely different
        behaviors, and no bookkeeping recovers one from the other.  (rv64d
        writes [sig_seip] in exactly two places: the [plat_sig_base] MMIO
        window of the platform's interrupt-injection register, and
        [reset].  Both are the premise's business — [Hseip] is a
        per-image, checker-style fact, exactly like [sail_shaped].)

    (b) THE FINAL CONFIGURATION IS EQUAL UP TO POINTWISE REGISTER EQUALITY
        ([cfg_eqv]), NOT UP TO [=].  [regstate]'s fields are FUNCTIONS
        ([register_bitvector_1 → mword 1] &c.), so for two distinct
        registers of the SAME field group
          [register_set r y (register_set sig_seip v rs)]
        and
          [register_set sig_seip v (register_set r y rs)]
        are two distinct lambda terms whose equality needs FUNCTIONAL
        EXTENSIONALITY — and the whole weak-memory chain is deliberately
        funext-free (see [claude-notes/completed/weak-memory-lift.md]: "no
        funext, no classical axiom"), which is worth more than a syntactic
        equality here.  So the reordered run ends at a configuration
        [cfg_eqv]-related to the original: the image, the log, every other
        agent's slot, the promise set, the [wstate] and the residual monad
        are LITERALLY equal, and agent [i]'s register file is equal at every
        register.  The cost to the consumer is zero, because [cfg_eqv] is
        (i) transitive ([cfg_eqv_trans]), (ii) a STRONG BISIMULATION for
        [pf_solo] / [pf_in_block] ([pf_solo_eqv], [pf_in_block_eqv] — same
        label, same log growth, same [wstate]), and (iii) preserved by and
        transparent to [at_boundary] / [in_block] / [seip_free_cfg].

    (c) The frame's PRESERVATION lemma ([seip_free_res_step]) and the
        commutation runs are scoped to IN-BLOCK steps ([sp_m p ≠ None] /
        [pf_in_block]), for the same reason as §6's [*_res_step]: at a
        boundary the step loads [next tick], about which nothing is known.
        The frame ([sail_step_ni_frame]) and the stability lemma
        ([sail_step_ni_stable]) themselves need no such restriction — the
        boundary arm copies the register file.

    ------------------------------------------------------------------------
    THE INDEX.

      §9.1 [register_beq_true]/[register_beq_ne]/[register_lookup_set_ne];
           [regs_agree] (+refl/sym/trans), [regs_agree_set],
           [regs_agree_set_excluded].
      §9.2 [regs_free] (the [quiet_tail]-style Fixpoint), [regs_free_triv]
           (the [X := ∅] instance), [regs_free_psail].
      §9.3 [regs_free_silent1]/[_silent_run]/[_wr_node] (descent),
           [silent1_frame], [silent_run_frame], [psail_agree] (+refl/sym/
           trans/[psail_agree_regs]), [sail_mstep_frame],
           [sail_step_ni_frame], [regs_free_res_step]; the stability chain
           [silent1_stable], [silent_run_stable], [sail_mstep_stable],
           [sail_step_ni_stable].
      §9.4 the instances: [seip_reg], [seip_free], [seip_free_psail],
           [regs_seip_eq], [regs_eqv], [psail_eqv] (+refl/sym/trans),
           [seip_free_res_step], [irq_deliver_intro].
      §9.5 [irq_commute_step] — ONE delivery past ONE step, at the LTS
           level; [sail_mstep_seip_frame] (the [X := sig_seip] frame).
      §9.6 [post_ws], [wp_pf_step_inv] — the one-shot inversion/re-taking
           lemma for a pf step of a GIVEN agent (all five arms, once).
      §9.7 [cfg_eqv] (+[cfg_eqv_lookup]/[_refl]/[_trans]),
           [regs_free_psail_triv], [pf_solo_eqv], [in_block_eqv],
           [at_boundary_eqv], [pf_in_block_eqv].
      §9.8 [pf_irq] (the delivery as a configuration step), [pf_irq_pf_step],
           [pf_irq_frame], [wp_pf_step_irq_or_ni], [seip_free_cfg] (+its
           three preservation lemmas), [pf_irq_commute_step],
           [pf_irq_commute_run], and the packaged [irq_commute_fwd].

    All of §9 is "Closed under the global context". *)


(** *** 9.1 register-file algebra *)

Lemma register_beq_true (r r' : register) : register_beq r r' = true → r = r'.
Proof.
  destruct r, r'; simpl; try discriminate; intro H;
    autorewrite with register_beq_iffs in H; subst; reflexivity.
Qed.

Lemma register_beq_ne (r r' : register) : r ≠ r' → register_beq r r' = false.
Proof.
  intros Hne. destruct (register_beq r r') eqn:Hb; [|done].
  by destruct (Hne (register_beq_true r r' Hb)).
Qed.

Lemma register_lookup_set_ne (r0 r : register) (v : type_of_register r)
    (rs : regstate) :
  r0 ≠ r → register_lookup r0 (register_set r v rs) = register_lookup r0 rs.
Proof. intros Hne. by apply irrelevant_register_set, register_beq_ne. Qed.

Definition regs_agree (X : register → Prop) (rs rs' : regstate) : Prop :=
  ∀ r : register, ¬ X r → register_lookup r rs = register_lookup r rs'.

Lemma regs_agree_refl X rs : regs_agree X rs rs.
Proof. by intros r _. Qed.

Lemma regs_agree_sym X rs rs' : regs_agree X rs rs' → regs_agree X rs' rs.
Proof. intros H r Hr. by rewrite (H r Hr). Qed.

Lemma regs_agree_trans X rs1 rs2 rs3 :
  regs_agree X rs1 rs2 → regs_agree X rs2 rs3 → regs_agree X rs1 rs3.
Proof. intros H1 H2 r Hr. by rewrite (H1 r Hr) (H2 r Hr). Qed.

Lemma regs_agree_set X rs rs' (r : register) (v : type_of_register r) :
  regs_agree X rs rs' →
  regs_agree X (register_set r v rs) (register_set r v rs').
Proof.
  intros H r0 Hr0. destruct (decide (r0 = r)) as [->|Hne].
  - by rewrite !register_lookup_set.
  - rewrite !(register_lookup_set_ne r0 r v _ Hne). by apply H.
Qed.

Lemma regs_agree_set_excluded X rs (r : register) (v : type_of_register r) :
  X r → regs_agree X rs (register_set r v rs).
Proof.
  intros HX r0 Hr0. symmetry. apply register_lookup_set_ne.
  intros ->. exact (Hr0 HX).
Qed.

(** *** 9.2 the monad predicate *)

Fixpoint regs_free (X : register → Prop) (m : M unit) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → M unit) → Prop with
       | Interface.RegRead r _ => λ k, ¬ X r ∧ ∀ v, regs_free X (k v)
       | Interface.RegWrite r _ _ => λ k, ¬ X r ∧ ∀ u, regs_free X (k u)
       | _ => λ k, ∀ r, regs_free X (k r)
       end) k
  end.

Fixpoint regs_free_triv (m : M unit) {struct m} : regs_free (λ _, False) m.
Proof.
  destruct m as [x|T oc k]; [exact I|].
  destruct oc; simpl; try (by intros r; apply regs_free_triv);
    (split; [exact (λ H, H)|intros r; apply regs_free_triv]).
Defined.

Definition regs_free_psail (X : register → Prop) (p : psail) : Prop :=
  match sp_m p with None => True | Some m => regs_free X m end.

(** *** 9.3 descent and the register frame *)

Lemma regs_free_silent1 X (m : M unit) rs (b : M unit * regstate) :
  regs_free X m → silent1 (m, rs) b → regs_free X b.1.
Proof.
  destruct m as [y|T oc k]; [by intros _ []|].
  destruct oc; simpl; try (by intros _ []);
    try (by intros Hfr ->; simpl; apply Hfr);
    try (by intros Hfr [ch ->]; simpl; apply Hfr);
    try (by intros [_ Hfr] ->; simpl; apply Hfr).
Qed.

Lemma silent1_frame X (m : M unit) rs rs' (b : M unit * regstate) :
  regs_agree X rs rs' → regs_free X m → silent1 (m, rs) b →
  ∃ rs2, silent1 (m, rs') (b.1, rs2) ∧ regs_agree X b.2 rs2.
Proof.
  intros Hag Hfr Hst. destruct m as [y|T oc k]; [by destruct Hst|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hfr, Hst;
    try (by destruct Hst);
    try (by rewrite Hst; exists rs'; split; [reflexivity|exact Hag]).
  - (* RegRead *)
    destruct Hfr as [Hne Hk]. rewrite Hst. exists rs'.
    rewrite /silent1 /= (Hag rg Hne). by split.
  - (* RegWrite *)
    rewrite Hst. exists (register_set rg rv rs').
    split; [reflexivity|by apply regs_agree_set].
  - (* Choose *)
    destruct Hst as [ch ->]. exists rs'. split; [by exists ch|exact Hag].
Qed.

Lemma silent_run_frame X (a b : M unit * regstate) :
  silent_run a b → regs_free X a.1 → ∀ rs',
  regs_agree X a.2 rs' →
  ∃ rs2, silent_run (a.1, rs') (b.1, rs2) ∧ regs_agree X b.2 rs2 ∧
         regs_free X b.1.
Proof.
  induction 1 as [x|x y z Hxy _ IH]; intros Hfr rs' Hag.
  { exists rs'. split_and!; [apply rtc_refl|exact Hag|exact Hfr]. }
  destruct x as [mx rsx]. simpl in Hfr, Hag.
  destruct (silent1_frame X mx rsx rs' y Hag Hfr Hxy) as (rs2 & Hs2 & Hag2).
  have Hfy : regs_free X y.1 := regs_free_silent1 X mx rsx y Hfr Hxy.
  destruct (IH Hfy rs2 Hag2) as (rs3 & Hs3 & Hag3 & Hfz).
  exists rs3. split_and!; [|exact Hag3|exact Hfz].
  eapply rtc_l; [|exact Hs3]. destruct y. exact Hs2.
Qed.

Lemma regs_free_wr_node X m1 rl base data m2 :
  regs_free X m1 → wr_node m1 rl base data m2 → regs_free X m2.
Proof.
  destruct m1 as [y|T oc k]; [done|].
  destruct oc; try done. simpl.
  intros Hfr (_ & _ & _ & _ & _ & _ & ->). by apply Hfr.
Qed.

Definition psail_agree (X : register → Prop) (p q : psail) : Prop :=
  sp_m p = sp_m q ∧ sp_dev p = sp_dev q ∧ sp_fence p = sp_fence q ∧
  regs_agree X (sp_regs p) (sp_regs q).

Lemma psail_agree_refl X p : psail_agree X p p.
Proof. split_and!; [done|done|done|apply regs_agree_refl]. Qed.

Lemma psail_agree_sym X p q : psail_agree X p q → psail_agree X q p.
Proof.
  intros (H1 & H2 & H3 & H4). split_and!; [done|done|done|by apply regs_agree_sym].
Qed.

Lemma psail_agree_trans X p q r :
  psail_agree X p q → psail_agree X q r → psail_agree X p r.
Proof.
  intros (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4).
  split_and!; [by rewrite H1|by rewrite H2|by rewrite H3
              |exact (regs_agree_trans X _ _ _ H4 G4)].
Qed.

Lemma psail_agree_regs X m dv fo rs rs' iq iq' :
  regs_agree X rs rs' →
  psail_agree X (PSail m rs dv fo iq) (PSail m rs' dv fo iq').
Proof. intros Hag. by split_and!. Qed.

Local Ltac pafin :=
  first [reflexivity | by apply psail_agree_regs
        | by apply psail_agree_regs, regs_agree_set | assumption].

Lemma sail_mstep_frame X (m : M unit) rs rs' d iq iq' l p' :
  regs_agree X rs rs' → regs_free X m → sail_mstep m rs d iq l p' →
  ∃ p'', sail_mstep m rs' d iq' l p'' ∧ psail_agree X p' p'' ∧ sp_irq p'' = iq'.
Proof.
  intros Hag Hfr Hstep. rewrite /sail_mstep in Hstep |- *.
  destruct m as [y|T oc k].
  { destruct Hstep as [-> ->]. exists (PSail None rs' d None iq').
    split_and!; pafin. }
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hfr, Hstep |- *;
    try (by destruct Hstep);
    try (by destruct Hstep as [-> ->]; eexists; split_and!;
           pafin).
  - (* RegRead *)
    destruct Hfr as [Hne Hk]. destruct Hstep as [-> ->].
    exists (PSail (Some (k (register_lookup rg rs'))) rs' d None iq').
    rewrite (Hag rg Hne). split_and!; pafin.
  - (* MemRead *)
    destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
    + destruct Hstep as [-> ->]. eexists. split_and!; pafin.
    + destruct Hstep as (Hcoh & Hstep).
      destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                    |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc
                    |csrc|]; try (by destruct Hstep).
      * destruct lat; [by destruct Hstep|].
        destruct asrc as [|x asrc']; [|by destruct Hstep].
        destruct Hstep as (Haq & Hbase & Hlent & w & Hw & ->).
        exists (PSail (Some (k (inl (w, None)))) rs' d None iq').
        split.
        { split; [exact Hcoh|]. split_and!;
            [exact Haq|exact Hbase|exact Hlent|].
          exists w. split; [exact Hw|reflexivity]. }
        split_and!; pafin.
      * destruct asrc as [|x asrc']; [|by destruct Hstep].
        destruct vsrc as [|y vsrc']; [|by destruct Hstep].
        destruct Hstep as (Hlat & Haq & Hbase & Hlent & Hlend & w & m1 & m2
                           & rs1 & Hw & Hsil & Hwr & ->).
        destruct (silent_run_frame X (k (inl (w, None)), rs) (m1, rs1)
                    Hsil (Hfr (inl (w, None))) rs' Hag)
          as (rs2 & Hs2 & Hag2 & _). simpl in Hs2.
        exists (PSail (Some m2) rs2 d None iq').
        split.
        { split; [exact Hcoh|]. split_and!;
            [exact Hlat|exact Haq|exact Hbase|exact Hlent|exact Hlend|].
          exists w, m1, m2, rs2.
          split_and!; [exact Hw|exact Hs2|exact Hwr|reflexivity]. }
        split_and!; pafin.
  - (* MemWrite *)
    destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
    + destruct Hstep as [-> ->].
      eexists. split_and!; pafin.
    + destruct Hstep as (-> & Hn & ->).
      eexists. split_and!; pafin.
  - (* Choose *)
    destruct Hstep as [-> [ch ->]].
    exists (PSail (Some (k ch)) rs' d None iq').
    split.
    { split; [reflexivity|]. by exists ch. }
    split_and!; pafin.
Qed.

Lemma sail_step_ni_frame X next p q l p' :
  psail_agree X p q → regs_free_psail X p →
  sail_step_ni next p l p' →
  ∃ q', sail_step_ni next q l q' ∧ psail_agree X p' q' ∧ sp_irq q' = sp_irq q.
Proof.
  intros (Hm & Hd & Hf & Hr) Hfr Hstep.
  rewrite /sail_step_ni in Hstep |- *. rewrite /regs_free_psail in Hfr.
  rewrite -?Hf -?Hd -?Hm.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|].
  { destruct Hstep as [-> ->].
    exists (PSail (sp_m p) (sp_regs q) (sp_dev p) None (sp_irq q)).
    split_and!; pafin. }
  destruct (sp_m p) as [m|] eqn:Hmp.
  - destruct (sail_mstep_frame X m (sp_regs p) (sp_regs q) (sp_dev p)
                (sp_irq p) (sp_irq q) l p' Hr Hfr Hstep)
      as (q' & Hq' & Hag' & Hirq').
    by exists q'.
  - destruct Hstep as [-> [tick ->]].
    exists (PSail (Some (next tick)) (sp_regs q) (sp_dev p) None (sp_irq q)).
    split_and!; [reflexivity|by exists tick|by apply psail_agree_regs
                |reflexivity].
Qed.

Lemma regs_free_silent_run X (m m1 : M unit) rs rs1 :
  regs_free X m → silent_run (m, rs) (m1, rs1) → regs_free X m1.
Proof.
  intros Hfr Hrun.
  change m with (m, rs).1 in Hfr. change m1 with (m1, rs1).1.
  remember (m, rs) as a. remember (m1, rs1) as b. clear Heqa Heqb m rs m1 rs1.
  revert Hfr. induction Hrun as [|x y z Hxy _ IH]; [done|].
  intros Hfr. apply IH. destruct x as [mx rsx].
  exact (regs_free_silent1 X mx rsx y Hfr Hxy).
Qed.

(** PRESERVATION: the residual of an IN-BLOCK step is again free (header
    deviation (b): at a boundary the step loads [next tick]). *)
Lemma regs_free_res_step X next p l p' :
  sp_m p ≠ None → regs_free_psail X p → sail_step_ni next p l p' →
  regs_free_psail X p'.
Proof.
  intros Hne Hfr Hstep.
  rewrite /sail_step_ni in Hstep. rewrite /regs_free_psail in Hfr |- *.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|].
  { destruct Hstep as [_ ->]. simpl. exact Hfr. }
  destruct (sp_m p) as [m|]; [|by destruct (Hne eq_refl)].
  rewrite /sail_mstep in Hstep.
  destruct m as [y|T oc k]; [by destruct Hstep as [_ ->]; simpl|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hstep, Hfr;
    try (by destruct Hstep);
    try (by destruct Hstep as [_ ->]; simpl; apply Hfr).
  - (* MemRead *)
    destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
    + destruct Hstep as [_ ->]. simpl. by apply Hfr.
    + destruct Hstep as (_ & Hstep).
      destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                    |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc
                    |csrc|]; try (by destruct Hstep).
      * destruct lat; [by destruct Hstep|].
        destruct asrc as [|x asrc']; [|by destruct Hstep].
        destruct Hstep as (_ & _ & _ & w & _ & ->). simpl. by apply Hfr.
      * destruct asrc as [|x asrc']; [|by destruct Hstep].
        destruct vsrc as [|y vsrc']; [|by destruct Hstep].
        destruct Hstep as (_ & _ & _ & _ & _ & w & m1 & m2 & rs1
                           & _ & Hsil & Hwr & ->).
        simpl. eapply regs_free_wr_node; [|exact Hwr].
        eapply regs_free_silent_run; [apply (Hfr (inl (w, None)))|exact Hsil].
  - (* MemWrite *)
    destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
    + destruct Hstep as [_ ->]. simpl. by apply Hfr.
    + destruct Hstep as (_ & _ & ->). simpl. by apply Hfr.
  - (* Choose *)
    destruct Hstep as (_ & ch & ->). simpl. by apply Hfr.
Qed.

(** STABILITY: a free monad never WRITES an excluded register either, so the
    value the delivery installed is still there at the end of the block. *)
Lemma silent1_stable X (m : M unit) rs (b : M unit * regstate) (r0 : register) :
  X r0 → regs_free X m → silent1 (m, rs) b →
  register_lookup r0 b.2 = register_lookup r0 rs.
Proof.
  intros HX Hfr Hst. destruct m as [y|T oc k]; [by destruct Hst|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hfr, Hst;
    try (by destruct Hst); try (by rewrite Hst).
  - (* RegWrite: the only arm that moves the register file *)
    destruct Hfr as [Hne _]. rewrite Hst /=.
    apply register_lookup_set_ne. intros ->. exact (Hne HX).
  - (* Choose *)
    by destruct Hst as [ch ->].
Qed.

Lemma silent_run_stable X (a b : M unit * regstate) (r0 : register) :
  silent_run a b → X r0 → regs_free X a.1 →
  register_lookup r0 b.2 = register_lookup r0 a.2.
Proof.
  induction 1 as [x|x y z Hxy _ IH]; intros HX Hfr; [reflexivity|].
  destruct x as [mx rsx]. simpl in Hfr |- *.
  rewrite (IH HX (regs_free_silent1 X mx rsx y Hfr Hxy)).
  exact (silent1_stable X mx rsx y r0 HX Hfr Hxy).
Qed.

Lemma sail_mstep_stable X (m : M unit) rs d iq l p' (r0 : register) :
  X r0 → regs_free X m → sail_mstep m rs d iq l p' →
  register_lookup r0 (sp_regs p') = register_lookup r0 rs.
Proof.
  intros HX Hfr Hstep. rewrite /sail_mstep in Hstep.
  destruct m as [y|T oc k]; [by destruct Hstep as [_ ->]|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl in Hfr, Hstep;
    try (by destruct Hstep);
    try (by destruct Hstep as [_ ->]).
  - (* RegWrite *)
    destruct Hfr as [Hne _]. destruct Hstep as [_ ->]. simpl.
    apply register_lookup_set_ne. intros ->. exact (Hne HX).
  - (* MemRead *)
    destruct (dev_addr (Interface.ReadReq.pa req)) eqn:Hd.
    + by destruct Hstep as [_ ->].
    + destruct Hstep as (_ & Hstep).
      destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                    |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc
                    |csrc|]; try (by destruct Hstep).
      * destruct lat; [by destruct Hstep|].
        destruct asrc as [|x asrc']; [|by destruct Hstep].
        by destruct Hstep as (_ & _ & _ & w & _ & ->).
      * destruct asrc as [|x asrc']; [|by destruct Hstep].
        destruct vsrc as [|y vsrc']; [|by destruct Hstep].
        destruct Hstep as (_ & _ & _ & _ & _ & w & m1 & m2 & rs1
                           & _ & Hsil & _ & ->).
        exact (silent_run_stable X (k (inl (w, None)), rs) (m1, rs1) r0
                 Hsil HX (Hfr (inl (w, None)))).
  - (* MemWrite *)
    destruct (dev_addr (Interface.WriteReq.pa req)) eqn:Hd.
    + by destruct Hstep as [_ ->].
    + by destruct Hstep as (_ & _ & ->).
  - (* Choose *)
    by destruct Hstep as (_ & ch & ->).
Qed.

Lemma sail_step_ni_stable X next p l p' (r0 : register) :
  X r0 → regs_free_psail X p → sail_step_ni next p l p' →
  register_lookup r0 (sp_regs p') = register_lookup r0 (sp_regs p).
Proof.
  intros HX Hfr Hstep.
  rewrite /sail_step_ni in Hstep. rewrite /regs_free_psail in Hfr.
  destruct (sp_fence p) as [[[[pr pw] sr] sw]|].
  { by destruct Hstep as [_ ->]. }
  destruct (sp_m p) as [m|].
  - exact (sail_mstep_stable X m (sp_regs p) (sp_dev p) (sp_irq p) l p' r0
             HX Hfr Hstep).
  - by destruct Hstep as [_ [tick ->]].
Qed.

(** *** 9.4 the seip instances *)

Definition seip_reg (r : register) : Prop := r = (sig_seip : register).

Definition seip_free : M unit → Prop := regs_free seip_reg.
Definition seip_free_psail : psail → Prop := regs_free_psail seip_reg.
Definition regs_seip_eq : regstate → regstate → Prop := regs_agree seip_reg.

Definition regs_eqv : regstate → regstate → Prop := regs_agree (λ _, False).

Definition psail_eqv (p q : psail) : Prop :=
  psail_agree (λ _, False) p q ∧ sp_irq p = sp_irq q.

Lemma psail_eqv_refl p : psail_eqv p p.
Proof. split; [apply psail_agree_refl|reflexivity]. Qed.

Lemma psail_eqv_sym p q : psail_eqv p q → psail_eqv q p.
Proof. intros [H1 H2]. split; [by apply psail_agree_sym|by rewrite H2]. Qed.

Lemma psail_eqv_trans p q r : psail_eqv p q → psail_eqv q r → psail_eqv p r.
Proof.
  intros [H1 H2] [G1 G2].
  split; [exact (psail_agree_trans _ _ _ _ H1 G1)|by rewrite H2].
Qed.

Lemma seip_free_res_step next p l p' :
  sp_m p ≠ None → seip_free_psail p → sail_step_ni next p l p' →
  seip_free_psail p'.
Proof. apply regs_free_res_step. Qed.

(** THE PIN FRAME FOR LIVENESS (stage C9; §2 note (g)).  [sail_live_st] is
    invariant under any change confined to [sig_seip], because its [RegRead]
    arm answers that ONE register with [∀ v] and every other one from the
    file.  This is what [WeakSailCone.res_ok_frame] consumes at
    [irq_deliver], the LTS arm that writes the pin BEHIND the residual's
    back — and it needs no [seip_free] hypothesis at all, unlike the
    commutation of §9.5, because it says nothing about the values that flow,
    only that no path FAILS. *)
Lemma register_beq_refl (r : register) : register_beq r r = true.
Proof.
  destruct r; simpl; autorewrite with register_beq_refls; reflexivity.
Qed.

Lemma sail_live_st_agree (m : M unit) rs rs' :
  regs_seip_eq rs rs' → sail_live_st rs m → sail_live_st rs' m.
Proof.
  revert rs rs'. induction m as [x|T oc k IH]; intros rs rs' Hag; [done|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|A eo|msg| | |ty| |msg2]; simpl;
    try done;
    try (intros H r; by apply (IH r rs rs')).
  - (* RegRead: the pin is ∀-quantified, every other register agrees *)
    destruct (register_beq rg (sig_seip : register)) eqn:Hb.
    + intros H v. by apply (IH v rs rs').
    + rewrite -(Hag rg). { intros H. by apply (IH _ rs rs'). }
      intros Hs. rewrite /seip_reg in Hs. rewrite Hs in Hb.
      by rewrite register_beq_refl in Hb.
  - (* RegWrite: the same agreement survives the write *)
    intros H. apply (IH tt (register_set rg rv rs) (register_set rg rv rs'));
      [by apply regs_agree_set|exact H].
  - (* MemRead *) intros H w. by apply (IH _ rs rs').
  - (* MemWrite *) intros H. by apply (IH _ rs rs').
  - (* Choose *) destruct ty; simpl; try done; intros H r; by apply (IH r rs rs').
Qed.

Lemma sail_live_st_seip (m : M unit) rs (v : type_of_register (sig_seip : register)) :
  sail_live_st rs m → sail_live_st (register_set sig_seip v rs) m.
Proof.
  apply sail_live_st_agree.
  exact (regs_agree_set_excluded seip_reg rs (sig_seip : register) v eq_refl).
Qed.

Lemma irq_deliver_intro p v iq :
  sp_irq p = v :: iq →
  irq_deliver p WeakPromise.LSilent
    (PSail (sp_m p) (register_set sig_seip v (sp_regs p)) (sp_dev p)
           (sp_fence p) iq).
Proof. intros H. split; [reflexivity|]. by exists v, iq. Qed.

(** *** 9.5 ONE DELIVERY COMMUTES FORWARD PAST ONE IN-BLOCK STEP *)
Lemma sail_mstep_seip_frame (m : M unit) rs rs' d iq l p' :
  regs_seip_eq rs rs' → seip_free m → sail_mstep m rs d iq l p' →
  ∃ p'', sail_mstep m rs' d iq l p'' ∧ psail_agree seip_reg p' p''.
Proof.
  intros Hag Hfr Hstep.
  destruct (sail_mstep_frame seip_reg m rs rs' d iq iq l p' Hag Hfr Hstep)
    as (p'' & H1 & H2 & _). by exists p''.
Qed.

Lemma irq_commute_step next q q1 l q2 :
  seip_free_psail q →
  irq_deliver q WeakPromise.LSilent q1 →
  sail_step_ni next q1 l q2 →
  ∃ q1' q2', sail_step_ni next q l q1' ∧
             irq_deliver q1' WeakPromise.LSilent q2' ∧ psail_eqv q2' q2.
Proof.
  intros Hfr [_ (v & iq & Hiq & ->)] Hstep.
  have Hag : psail_agree seip_reg
               (PSail (sp_m q) (register_set sig_seip v (sp_regs q)) (sp_dev q)
                      (sp_fence q) iq) q.
  { split_and!; [reflexivity|reflexivity|reflexivity|].
    simpl. apply regs_agree_sym, regs_agree_set_excluded. reflexivity. }
  have Hfr1 : regs_free_psail seip_reg
                (PSail (sp_m q) (register_set sig_seip v (sp_regs q)) (sp_dev q)
                       (sp_fence q) iq) := Hfr.
  destruct (sail_step_ni_frame seip_reg next _ q l q2 Hag Hfr1 Hstep)
    as (q1' & Hq1' & (Hm2 & Hd2 & Hf2 & Hr2) & Hirq1').
  have Hiq1' : sp_irq q1' = v :: iq by rewrite Hirq1'.
  exists q1', (PSail (sp_m q1') (register_set sig_seip v (sp_regs q1'))
                 (sp_dev q1') (sp_fence q1') iq).
  split_and!; [exact Hq1'|by apply irq_deliver_intro|].
  have Hseip : register_lookup sig_seip (sp_regs q2) = v.
  { rewrite (sail_step_ni_stable seip_reg next _ l q2 sig_seip
               eq_refl Hfr1 Hstep) /=.
    exact (register_lookup_set (sig_seip : register) (sp_regs q) v). }
  have Hirq2 : sp_irq q2 = iq.
  { by rewrite (sail_step_ni_irq next _ l q2 Hstep). }
  split; [split_and!|by rewrite /= Hirq2].
  - by rewrite /= Hm2.
  - by rewrite /= Hd2.
  - by rewrite /= Hf2.
  - intros r0 _. simpl. destruct (decide (r0 = (sig_seip : register))) as [->|Hne].
    + by rewrite register_lookup_set Hseip.
    + rewrite (register_lookup_set_ne r0 sig_seip v _ Hne).
      symmetry. by apply Hr2.
Qed.

(** *** 9.6 re-taking a pf step of the SAME agent from a modified state *)

Definition post_ws (l : wlabel) (ws : wstate) (n : nat) : wstate :=
  match l with
  | WeakPromise.LSilent => ws
  | WeakPromise.LLoad aq lat base tvs asrc =>
      load_post_run_d ws aq (srcs_view ws asrc) base tvs.*1
  | WeakPromise.LStore rl base data asrc vsrc =>
      store_post_run_d ws rl (srcs_view ws asrc) (srcs_view ws vsrc)
        base (length data) (S n)
  | WeakPromise.LRmw aq rl base tvs data asrc vsrc =>
      store_post_run_d
        (load_post_run_d ws aq (srcs_view ws asrc) base tvs.*1)
        rl (srcs_view ws asrc) (srcs_view ws vsrc) base (length data) (S n)
  | WeakPromise.LFence pr pw sr sw => fence_post ws pr pw sr sw
  | WeakPromise.LDev => ws   (* [LSilent]'s twin *)
  | WeakPromise.LRegW rd srcs => regw_post ws rd (srcs_view ws srcs)
  | WeakPromise.LCtrl srcs => ctrl_post ws (srcs_view ws srcs)
  | WeakPromise.LInstr => instr_post ws
  end.

Lemma wp_pf_step_inv {P : Type} (pstep : P → unit → wlabel → P → unit → Prop)
    (pcls : P → wlabel → wstate → wm_class)
    i l (c c' : wpcfg P unit) ag :
  wp_pf_step pstep pcls i l c c' → pc_ags c !! i = Some ag →
  ∃ st' ms,
    pstep (pa_st ag) tt l st' tt ∧
    pc_img c' = pc_img c ∧ pc_log c' = pc_log c ++ ms ∧
    pc_ags c' = <[i := WPAgent st' (post_ws l (pa_ws ag) (length (pc_log c)))
                          (pa_prom ag)]> (pc_ags c) ∧
    (∀ (d : wpcfg P unit) agd stD,
       pc_ags d !! i = Some agd → pa_ws agd = pa_ws ag →
       pa_prom agd = pa_prom ag →
       pc_img d = pc_img c → pc_log d = pc_log c →
       pstep (pa_st agd) (pc_dev d) l stD tt →
       (** THE ONE PREMISE THE PROGRAM-INDEXED CLASS ADDS (G6a follow-up).
           The re-taking agent [agd] is only required to agree with [ag] on
           the [wstate]; its PROGRAM state may differ (this lemma is used at
           [cfg_eqv], which twins two register files).  Since [pcls] now
           reads the program state, the message it stamps has to be the
           same one — which is exactly this equation, and it is trivial for
           a program-blind class function such as
           [WeakSailLTS2.lbl_class_p]. *)
       pcls (pa_st agd) l (pa_ws agd) = pcls (pa_st ag) l (pa_ws ag) →
       wp_pf_step pstep pcls i l d
         (WPCfgU (pc_img c) (pc_log c ++ ms)
            (<[i := WPAgent stD (post_ws l (pa_ws ag) (length (pc_log c)))
                       (pa_prom ag)]> (pc_ags d)))).
Proof.
  intros Hstep Hlk0.
  destruct Hstep as
    [cfg ag0 st' dd Hlk Hps
    |cfg ag0 aq lat base tvs asrc st' dd Hlk Hps Hr
    |cfg ag0 rl base data asrc vsrc kk st' dd Hlk Hps Hne Hkc
    |cfg ag0 aq rl base tvs data asrc vsrc kk st' dd Hlk Hps Hne Hlen Hr He Hkc
    |cfg ag0 pr pw sr sw st' dd Hlk Hps|cfg ag0 st' dd Hlk Hps
    |cfg ag0 rdw wsrc st' dd Hlk Hps|cfg ag0 csrc st' dd Hlk Hps
    |cfg ag0 st' dd Hlk Hps];
    destruct dd;
    (have Hdv : pc_dev cfg = tt by destruct (pc_dev cfg));
    rewrite Hdv in Hps;
    rewrite Hlk0 in Hlk; injection Hlk as <-.
  - exists st', []. split_and!;
      [exact Hps|reflexivity|by rewrite app_nil_r|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    rewrite app_nil_r -Himg -Hlog -Hws -Hprom.
    exact (PFSilent pstep pcls i d agd stD tt Hlkd Hpsd).
  - exists st', []. split_and!;
      [exact Hps|reflexivity|by rewrite app_nil_r|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    have Hr' : read_ok_d (pc_img d) (pc_log d) (pa_ws agd) aq lat base tvs
                 (srcs_view (pa_ws agd) asrc)
      by rewrite Himg Hlog Hws.
    rewrite app_nil_r -Himg -Hlog -Hws -Hprom.
    exact (PFLoad pstep pcls i d agd aq lat base tvs asrc stD tt
             Hlkd Hpsd Hr').
  - exists st', [WMsg base data (Some i) kk]. split_and!;
      [exact Hps|reflexivity|reflexivity|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    have Hkc' : kk = pcls (pa_st agd) (WeakPromise.LStore rl base data
                             asrc vsrc) (pa_ws agd) by rewrite Hkcls.
    rewrite -Himg -{1}Hlog -{1}Hlog -Hws -Hprom.
    exact (PFStore pstep pcls i d agd rl base data asrc vsrc kk stD tt
             Hlkd Hpsd Hne Hkc').
  - exists st', [WMsg base data (Some i) kk]. split_and!;
      [exact Hps|reflexivity|reflexivity|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    have Hr' : read_ok_d (pc_img d) (pc_log d) (pa_ws agd) aq false base tvs
                 (srcs_view (pa_ws agd) asrc)
      by rewrite Himg Hlog Hws.
    have He' : excl_ok (pc_log d) i base tvs (S (length (pc_log d)))
      by rewrite Hlog.
    have Hkc' : kk = pcls (pa_st agd) (WeakPromise.LRmw aq rl base tvs data
                             asrc vsrc) (pa_ws agd) by rewrite Hkcls.
    rewrite -Himg -{1}Hlog -{1}Hlog -Hws -Hprom.
    exact (PFRmw pstep pcls i d agd aq rl base tvs data asrc vsrc kk stD tt
             Hlkd Hpsd Hne Hlen Hr' He' Hkc').
  - exists st', []. split_and!;
      [exact Hps|reflexivity|by rewrite app_nil_r|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    rewrite app_nil_r -Himg -Hlog -Hws -Hprom.
    exact (PFFence pstep pcls i d agd pr pw sr sw stD tt Hlkd Hpsd).
  - (* dev: [PFSilent]'s twin *)
    exists st', []. split_and!;
      [exact Hps|reflexivity|by rewrite app_nil_r|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    rewrite app_nil_r -Himg -Hlog -Hws -Hprom.
    exact (PFDev pstep pcls i d agd stD tt Hlkd Hpsd).
  - (* regw / ctrl / instr: [PFSilent]'s twins with a [wstate]-only update *)
    exists st', []. split_and!;
      [exact Hps|reflexivity|by rewrite app_nil_r|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    rewrite app_nil_r -Himg -Hlog -Hws -Hprom.
    exact (PFRegW pstep pcls i d agd rdw wsrc stD tt Hlkd Hpsd).
  - exists st', []. split_and!;
      [exact Hps|reflexivity|by rewrite app_nil_r|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    rewrite app_nil_r -Himg -Hlog -Hws -Hprom.
    exact (PFCtrl pstep pcls i d agd csrc stD tt Hlkd Hpsd).
  - exists st', []. split_and!;
      [exact Hps|reflexivity|by rewrite app_nil_r|reflexivity|].
    intros d agd stD Hlkd Hws Hprom Himg Hlog Hpsd Hkcls.
    rewrite app_nil_r -Himg -Hlog -Hws -Hprom.
    exact (PFInstr pstep pcls i d agd stD tt Hlkd Hpsd).
Qed.

(** *** 9.7 configurations that differ only in one agent's register file *)

Definition cfg_eqv (i : agent) (c d : wpcfg psail unit) : Prop :=
  pc_img d = pc_img c ∧ pc_log d = pc_log c ∧
  ∃ ag ag', pc_ags c !! i = Some ag ∧ pc_ags d = <[i := ag']> (pc_ags c) ∧
            pa_ws ag' = pa_ws ag ∧ pa_prom ag' = pa_prom ag ∧
            psail_eqv (pa_st ag) (pa_st ag').

Lemma cfg_eqv_lookup i c d ag :
  cfg_eqv i c d → pc_ags c !! i = Some ag →
  ∃ ag', pc_ags d !! i = Some ag' ∧ pa_ws ag' = pa_ws ag ∧
         pa_prom ag' = pa_prom ag ∧ psail_eqv (pa_st ag) (pa_st ag').
Proof.
  intros (_ & _ & ag0 & ag' & Hlk0 & Hags & Hws & Hprom & Heqv) Hlk.
  rewrite Hlk in Hlk0. injection Hlk0 as <-.
  exists ag'. split_and!; [|exact Hws|exact Hprom|exact Heqv].
  rewrite Hags. by eapply lookup_insert_at, Hlk.
Qed.

Lemma cfg_eqv_refl i c ag : pc_ags c !! i = Some ag → cfg_eqv i c c.
Proof.
  intros Hlk. split_and!; [reflexivity|reflexivity|].
  exists ag, ag. split_and!;
    [exact Hlk|by rewrite (list_insert_id _ _ _ Hlk)|reflexivity|reflexivity
    |apply psail_eqv_refl].
Qed.

Lemma regs_free_psail_triv p : regs_free_psail (λ _, False) p.
Proof.
  rewrite /regs_free_psail. destruct (sp_m p) as [m|];
    [apply regs_free_triv|exact I].
Qed.

(** THE BISIMULATION.  Registers that agree everywhere are indistinguishable
    to the LTS, so a [pf_solo] step of the SAME agent is available from the
    twinned configuration, with the same label, the same log growth, and a
    twinned successor. *)
Lemma pf_solo_eqv next i c d c' :
  cfg_eqv i c d → pf_solo next i c c' →
  ∃ d', pf_solo next i d d' ∧ cfg_eqv i c' d'.
Proof.
  intros Heq Hsolo.
  destruct Heq as (Himg & Hlog & ag & ag' & Hlk & Hags & Hws & Hprom & Heqv).
  have Hlkd : pc_ags d !! i = Some ag'
    by rewrite Hags; eapply lookup_insert_at, Hlk.
  destruct Hsolo as (l & Hstep & Hcc & Hrt).
  destruct (wp_pf_step_inv (pstep_unit (sail_step_ni next)) lbl_class_p i l c c' ag Hstep Hlk)
    as (st' & ms & Hps & Himg' & Hlog' & Hags' & Hre).
  destruct Heqv as (Hpa & Hirq).
  destruct (sail_step_ni_frame (λ _, False) next (pa_st ag) (pa_st ag') l st'
              Hpa (regs_free_psail_triv _) Hps)
    as (stD & HpsD & HagD & HirqD).
  have HeqvD : psail_eqv st' stD.
  { split; [exact HagD|].
    rewrite (sail_step_ni_irq next (pa_st ag) l st' Hps) HirqD. exact Hirq. }
  set (wsp := post_ws l (pa_ws ag) (length (pc_log c))).
  exists (WPCfgU (pc_img c) (pc_log c ++ ms)
            (<[i := WPAgent stD wsp (pa_prom ag)]> (pc_ags d))).
  split.
  - exists l. split_and!.
    + refine (Hre d ag' stD Hlkd Hws Hprom Himg Hlog HpsD _).
      rewrite /lbl_class_p. by rewrite Hws.
    + intros ag2 msg Hag2 Heq2. simpl in Heq2.
      rewrite Hlkd in Hag2. injection Hag2 as <-.
      rewrite Hlog in Heq2. apply app_inv_head in Heq2. subst ms.
      rewrite Hws. apply (Hcc ag msg Hlk). by rewrite Hlog'.
    + rewrite /rmw_tight in Hrt |- *. destruct l; try done.
      intros ag2 Hag2. rewrite Hlkd in Hag2. injection Hag2 as <-.
      rewrite Himg Hlog Hws. exact (Hrt ag Hlk).
  - split_and!; [by rewrite /= Himg'|by rewrite /= Hlog'|].
    exists (WPAgent st' wsp (pa_prom ag)), (WPAgent stD wsp (pa_prom ag)).
    split_and!; [by rewrite Hags'; eapply lookup_insert_at, Hlk| |done|done
                |exact HeqvD].
    rewrite /= Hags' Hags !list_insert_insert. reflexivity.
Qed.

Lemma cfg_eqv_trans i c d e : cfg_eqv i c d → cfg_eqv i d e → cfg_eqv i c e.
Proof.
  intros (Hi1 & Hl1 & ag & ag1 & Hlk & Hags1 & Hws1 & Hp1 & He1).
  intros (Hi2 & Hl2 & ag1' & ag2 & Hlk1 & Hags2 & Hws2 & Hp2 & He2).
  have Hlk1' : pc_ags d !! i = Some ag1
    by rewrite Hags1; eapply lookup_insert_at, Hlk.
  rewrite Hlk1 in Hlk1'. injection Hlk1' as <-.
  split_and!; [by rewrite Hi2|by rewrite Hl2|].
  exists ag, ag2. split_and!;
    [exact Hlk|by rewrite Hags2 Hags1 list_insert_insert
    |by rewrite Hws2|by rewrite Hp2|exact (psail_eqv_trans _ _ _ He1 He2)].
Qed.

Lemma in_block_eqv i c d : cfg_eqv i c d → in_block i c → in_block i d.
Proof.
  intros Heq (ag & Hlk & Hm).
  destruct (cfg_eqv_lookup i c d ag Heq Hlk) as (ag' & Hlk' & _ & _ & Heqv).
  exists ag'. split; [exact Hlk'|]. destruct Heqv as ((Hm' & _) & _).
  by rewrite -Hm'.
Qed.

Lemma at_boundary_eqv i c d : cfg_eqv i c d → at_boundary i c → at_boundary i d.
Proof.
  intros Heq (ag & Hlk & Hm).
  destruct (cfg_eqv_lookup i c d ag Heq Hlk) as (ag' & Hlk' & _ & _ & Heqv).
  exists ag'. split; [exact Hlk'|]. destruct Heqv as ((Hm' & _) & _).
  by rewrite -Hm'.
Qed.

Lemma pf_in_block_eqv next i c d c' :
  cfg_eqv i c d → pf_in_block next i c c' →
  ∃ d', pf_in_block next i d d' ∧ cfg_eqv i c' d'.
Proof.
  intros Heq (Hin & Hsolo).
  destruct (pf_solo_eqv next i c d c' Heq Hsolo) as (d' & Hd' & Heq').
  exists d'.
  split; [split; [exact (in_block_eqv i c d Heq Hin)|exact Hd']|exact Heq'].
Qed.

(** *** 9.8 the delivery as a configuration step, and the commutation *)

Definition pf_irq (i : agent) (c c' : wpcfg psail unit) : Prop :=
  ∃ ag st', pc_ags c !! i = Some ag ∧
            irq_deliver (pa_st ag) WeakPromise.LSilent st' ∧
            c' = WPCfgU (pc_img c) (pc_log c)
                   (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags c)).

(** A delivery IS a [wp_pf_step] of the FULL LTS (the [irq_deliver] arm is
    gated by [sp_fence = None], delta (c) of [WeakSailLTS]). *)
Lemma pf_irq_pf_step next i c c' :
  pf_irq i c c' →
  (∀ ag, pc_ags c !! i = Some ag → sp_fence (pa_st ag) = None) →
  wp_pf_step (pstep_unit (sail_step next)) lbl_class_p i WeakPromise.LSilent c c'.
Proof.
  intros (ag & st' & Hlk & Hdel & ->) Hf.
  apply (PFSilent (pstep_unit (sail_step next)) lbl_class_p i c ag st' tt Hlk).
  rewrite /pstep_unit /sail_step (Hf ag Hlk). by left.
Qed.
Lemma pf_irq_frame i c c' :
  pf_irq i c c' →
  pc_img c' = pc_img c ∧ pc_log c' = pc_log c ∧
  (∀ j, j ≠ i → pc_ags c' !! j = pc_ags c !! j).
Proof.
  intros (ag & st' & Hlk & _ & ->). split_and!; [done|done|].
  intros j Hj. simpl. by apply lookup_insert_other.
Qed.

Lemma wp_pf_step_irq_or_ni next i l c c' :
  wp_pf_step (pstep_unit (sail_step next)) lbl_class_p i l c c' →
  (l = WeakPromise.LSilent ∧ pf_irq i c c')
  ∨ wp_pf_step (pstep_unit (sail_step_ni next)) lbl_class_p i l c c'.
Proof.
  intros Hstep.
  destruct Hstep as
    [cfg ag st' dd Hlk Hps
    |cfg ag aq lat base tvs asrc st' dd Hlk Hps Hr
    |cfg ag rl base data asrc vsrc kk st' dd Hlk Hps Hne Hkc
    |cfg ag aq rl base tvs data asrc vsrc kk st' dd Hlk Hps Hne Hlen Hr He Hkc
    |cfg ag pr pw sr sw st' dd Hlk Hps|cfg ag st' dd Hlk Hps
    |cfg ag rdw wsrc st' dd Hlk Hps|cfg ag csrc st' dd Hlk Hps
    |cfg ag st' dd Hlk Hps];
    destruct dd; rewrite /pstep_unit in Hps;
    destruct (sail_step_irq_or_ni next (pa_st ag) _ st' Hps)
      as [[Hf Hirq]|Hni];
    try (by destruct Hirq as [Hx _]; inversion Hx).
  - left. split; [reflexivity|]. by exists ag, st'.
  - right. by eapply PFSilent.
  - right. by eapply PFLoad.
  - right. by eapply PFStore.
  - right. by eapply PFRmw.
  - right. by eapply PFFence.
  - right. by eapply PFDev.
  - right. by eapply PFRegW.
  - right. by eapply PFCtrl.
  - right. by eapply PFInstr.
Qed.


Definition seip_free_cfg (i : agent) (c : wpcfg psail unit) : Prop :=
  ∀ ag, pc_ags c !! i = Some ag → seip_free_psail (pa_st ag).

Lemma seip_free_cfg_eqv i c d :
  cfg_eqv i c d → seip_free_cfg i c → seip_free_cfg i d.
Proof.
  intros Heq Hfr ag' Hlk'.
  destruct Heq as (_ & _ & ag0 & ag1 & Hlk0 & Hags & _ & _ & (Hpa & _)).
  have Hlk1 : pc_ags d !! i = Some ag1
    by rewrite Hags; eapply lookup_insert_at, Hlk0.
  rewrite Hlk' in Hlk1. injection Hlk1 as <-.
  rewrite /seip_free_psail /regs_free_psail -(proj1 Hpa).
  exact (Hfr ag0 Hlk0).
Qed.

Lemma seip_free_cfg_irq i c c' :
  pf_irq i c c' → seip_free_cfg i c → seip_free_cfg i c'.
Proof.
  intros (ag & st' & Hlk & [_ (v & iq & Hiq & ->)] & ->) Hfr ag2 Hlk2.
  simpl in Hlk2. rewrite (lookup_insert_at (pc_ags c) i ag _ Hlk) in Hlk2.
  injection Hlk2 as <-. exact (Hfr ag Hlk).
Qed.

Lemma seip_free_cfg_step next i c c' :
  in_block i c → seip_free_cfg i c → pf_solo next i c c' → seip_free_cfg i c'.
Proof.
  intros (ag & Hlk & Hm) Hfr (l & Hstep & _ & _).
  destruct (wp_pf_step_inv (pstep_unit (sail_step_ni next)) lbl_class_p i l c c' ag Hstep Hlk)
    as (st' & ms & Hps & _ & _ & Hags & _).
  intros ag2 Hlk2. rewrite Hags in Hlk2.
  rewrite (lookup_insert_at (pc_ags c) i ag _ Hlk) in Hlk2.
  injection Hlk2 as <-. simpl.
  exact (seip_free_res_step next (pa_st ag) l st' Hm (Hfr ag Hlk) Hps).
Qed.

(** ONE DELIVERY COMMUTES FORWARD PAST ONE SOLO IN-BLOCK STEP OF THE SAME
    AGENT: same label, same log growth, same [wstate]; the successor differs
    only in that agent's register file, and only where the pin was written
    (which the delivery re-appended at the end restores). *)
Lemma pf_irq_commute_step next i c c1 c2 :
  seip_free_cfg i c → pf_irq i c c1 → pf_solo next i c1 c2 →
  ∃ c1' c2', pf_solo next i c c1' ∧ pf_irq i c1' c2' ∧ cfg_eqv i c2 c2'.
Proof.
  intros Hfr (ag & stD & Hlk & Hdel & ->) (l & Hstep & Hcc & Hrt).
  have Hlk1 : pc_ags (WPCfgU (pc_img c) (pc_log c)
                        (<[i := WPAgent stD (pa_ws ag) (pa_prom ag)]>
                           (pc_ags c))) !! i
              = Some (WPAgent stD (pa_ws ag) (pa_prom ag))
    := lookup_insert_at (pc_ags c) i ag _ Hlk.
  destruct (wp_pf_step_inv (pstep_unit (sail_step_ni next)) lbl_class_p i l _ c2 _ Hstep Hlk1)
    as (st2 & ms & Hps & Himg2 & Hlog2 & Hags2 & Hre).
  simpl in Hps, Himg2, Hlog2, Hags2, Hre.
  destruct (irq_commute_step next (pa_st ag) stD l st2 (Hfr ag Hlk) Hdel Hps)
    as (st1' & st2' & Hstep1' & Hdel' & Heqv2).
  exists (WPCfgU (pc_img c) (pc_log c ++ ms)
            (<[i := WPAgent st1' (post_ws l (pa_ws ag) (length (pc_log c)))
                      (pa_prom ag)]> (pc_ags c))).
  eexists. split_and!.
  - exists l. split_and!.
    + exact (Hre c ag st1' Hlk eq_refl eq_refl eq_refl eq_refl Hstep1'
               eq_refl).
    + intros ag0 msg Hag0 Heq. simpl in Heq.
      rewrite Hlk in Hag0. injection Hag0 as <-.
      apply app_inv_head in Heq. subst ms.
      exact (Hcc _ msg Hlk1 Hlog2).
    + rewrite /rmw_tight in Hrt |- *. destruct l; try done.
      intros ag0 Hag0. rewrite Hlk in Hag0. injection Hag0 as <-.
      exact (Hrt _ Hlk1).
  - exists (WPAgent st1' (post_ws l (pa_ws ag) (length (pc_log c)))
              (pa_prom ag)), st2'.
    split_and!; [by eapply lookup_insert_at, Hlk|exact Hdel'|reflexivity].
  - split_and!; [by rewrite Himg2|by rewrite Hlog2|].
    exists (WPAgent st2 (post_ws l (pa_ws ag) (length (pc_log c))) (pa_prom ag)),
           (WPAgent st2' (post_ws l (pa_ws ag) (length (pc_log c))) (pa_prom ag)).
    split_and!.
    + rewrite Hags2. by eapply lookup_insert_at, Hlk1.
    + rewrite /= Hags2 !list_insert_insert. reflexivity.
    + reflexivity.
    + reflexivity.
    + exact (psail_eqv_sym _ _ Heqv2).
Qed.

Lemma in_block_irq i c c' : pf_irq i c c' → in_block i c' → in_block i c.
Proof.
  intros (ag & st' & Hlk & [_ (v & iq & Hiq & ->)] & ->) (ag2 & Hlk2 & Hm2).
  simpl in Hlk2. rewrite (lookup_insert_at (pc_ags c) i ag _ Hlk) in Hlk2.
  injection Hlk2 as <-. simpl in Hm2. by exists ag.
Qed.

Lemma at_boundary_irq i c c' :
  pf_irq i c c' → at_boundary i c' → at_boundary i c.
Proof.
  intros (ag & st' & Hlk & [_ (v & iq & Hiq & ->)] & ->) (ag2 & Hlk2 & Hm2).
  simpl in Hlk2. rewrite (lookup_insert_at (pc_ags c) i ag _ Hlk) in Hlk2.
  injection Hlk2 as <-. simpl in Hm2. by exists ag.
Qed.

(** THE RUN FORM: a delivery in front of a whole in-block run of the same
    agent commutes to the END of that run. *)
Lemma pf_irq_commute_run next i : ∀ c1 c2, rtc (pf_in_block next i) c1 c2 →
  ∀ c d, seip_free_cfg i c → pf_irq i c d → cfg_eqv i c1 d →
  ∃ c1' c2', rtc (pf_in_block next i) c c1' ∧ pf_irq i c1' c2' ∧
             cfg_eqv i c2 c2'.
Proof.
  intros c1 c2 Hrun.
  induction Hrun as [x|x y z Hxy _ IH]; intros c d Hfr Hdel Heq.
  - exists c, d. split_and!; [apply rtc_refl|exact Hdel|exact Heq].
  - destruct (pf_in_block_eqv next i x d y Heq Hxy) as (yd & Hyd & Heqy).
    destruct Hyd as (Hind & Hsolod).
    destruct (pf_irq_commute_step next i c d yd Hfr Hdel Hsolod)
      as (c1' & y'' & Hsolo & Hdel'' & Heqy'').
    have Hin : in_block i c := in_block_irq i c d Hdel Hind.
    have Hfr' : seip_free_cfg i c1'
      := seip_free_cfg_step next i c c1' Hin Hfr Hsolo.
    destruct (IH c1' y'' Hfr' Hdel''
                (cfg_eqv_trans i y yd y'' Heqy Heqy''))
      as (c2' & c3' & Hrun' & Hdel3 & Heq3).
    exists c2', c3'. split_and!; [|exact Hdel3|exact Heq3].
    eapply rtc_l; [split; [exact Hin|exact Hsolo]|exact Hrun'].
Qed.

(** THE PACKAGED REORDERING (what stage B splices).  A delivery landing
    STRICTLY INSIDE a block, followed by the rest of the block, is the same
    block followed by the delivery at the instruction boundary — same
    labels, same log, same [wstate]s, and a final configuration that differs
    from the original in NOTHING (registers included: the pin the delivery
    installs is the one the original block carried, by
    [sail_step_ni_stable]) except that the equality of the register files is
    POINTWISE ([cfg_eqv]) rather than Leibniz. *)
Theorem irq_commute_fwd next i c c1 c2 :
  seip_free_cfg i c →
  pf_irq i c c1 →
  rtc (pf_in_block next i) c1 c2 →
  at_boundary i c2 →
  ∃ c1' c2', rtc (pf_in_block next i) c c1' ∧ at_boundary i c1' ∧
             pf_irq i c1' c2' ∧ cfg_eqv i c2 c2'.
Proof.
  intros Hfr Hdel Hrun Hbd.
  have Hlk1 : ∃ ag1, pc_ags c1 !! i = Some ag1.
  { destruct Hdel as (ag & st' & Hlk & _ & ->). eexists.
    by eapply lookup_insert_at, Hlk. }
  destruct Hlk1 as (ag1 & Hlk1).
  destruct (pf_irq_commute_run next i c1 c2 Hrun c c1 Hfr Hdel
              (cfg_eqv_refl i c1 ag1 Hlk1))
    as (c1' & c2' & Hrun' & Hdel' & Heq').
  exists c1', c2'. split_and!; [exact Hrun'| |exact Hdel'|exact Heq'].
  exact (at_boundary_irq i c1' c2' Hdel' (at_boundary_eqv i c2 c2' Heq' Hbd)).
Qed.
