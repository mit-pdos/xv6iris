(** * WeakAxRealize — the PROGRAM-CARRYING reverse bridge (A3(iii), T1-D)

    [WeakPromiseBridge] part (E) replays an axiomatic execution as a
    promise-free run of the FULL machine, but only for a program LTS that
    admits every label ([prog_free]) — "programs are free".  xv6 is not
    free, so that form cannot compose with the real instance: T1's
    conclusion (`srvwmo_realizable`: an sRVWMO-consistent candidate yields
    an [exec_wf] execution) has to become a pf run OF A GIVEN PROGRAM
    before adequacy can be applied to it.

    This file is that generalization.  [prog_free] is replaced by a
    PER-EVENT SUPPLY of program steps along the execution's trace
    ([exec_prog_ok']), and [WeakPromiseBridge.exec_cls_ok]'s fixed-[ps]
    indexing — which is an artefact of [prog_free] (under it no program
    state ever moves, so the class equation could be read at the agent's
    INITIAL state) — disappears into that supply, at the per-step program
    state where it belongs.

    NOTHING IN [WeakPromiseBridge] IS EDITED except additively (T1-D added
    [ws_eqr]/[cfg_matchd]/[cfg_eqr]/[pcls_eqr] there, next to [cfg_match]);
    this is a leaf file built on its exported lemmas.

    ** T1-D: WHAT THE SUPPLY LOOKS LIKE, AND WHY

    The pre-T1-D shape of this file was UNSATISFIABLE for the real xv6
    image, in two independent ways (worklist "THE TIER-1 CONFORMANCE GAP"):

    - [lbl_realizes] gated on [lb_depfree], while [WeakEvInst.pnode_step]
      PINS a store's label to the instruction's real operand lists
      ([deps_asrc (deps_of_ib ib)] &c.), which is non-empty for every
      register-addressed store — i.e. essentially every real store;
    - the ONE-PSTEP-PER-TRACE-EVENT shape could not thread the instance's
      node stream at all: every instruction also takes ADMINISTRATIVE steps
      ([LInstr] at the announce and at the boundary, [LRegW], [LCtrl],
      [LSilent], [LDev]), which have no trace event and for which
      [lb_depfree] is outright [False].

    Both are repaired here, and NEITHER needs a model change: in the PF
    FRAGMENT the dependency machinery never feeds a side condition.  The two
    channels by which a dependency view used to reach admissibility are both
    closed — the forward bank's view column is [0] (D-7r) and the exclusive
    read folds at the plain pre-view (D-2r) — so the operands survive only
    in [w_vcap] (and, for the exclusive read, in [w_res]), which is exactly
    what [WeakPromiseBridge.ws_eqr] declines to relate.

    ** The hypothesis' shape, and why it is this one

    The supply hands the machine a WLABEL [l] and a [pstep] at it; the
    axiomatic side only has its own [lbl].  Two shapes were available:

    (1) demand the step at the CANONICAL machine label
        [WeakPromiseBridge.unproj_lbl lb] (empty operand lists,
        [lat := false]), or
    (2) demand it at ANY label that PROJECTS to the execution's label,
        [proj_lbl (pcls …) l = Some lb].

    (2) is chosen, as [lbl_realizes] below.  The reasons:

    - IT IS THE EXACT INVERSE OF THE FORWARD PROJECTION.  The forward
      bridge [WeakPromiseBridge.wp_pf_step_mstep] takes [lb_depfree l] and
      [lb_fused l] and produces [proj_lbl k l = Some lb] together with the
      [mstep].  Stating the reverse direction over the same relation makes
      the two composable by name rather than by re-derivation.

    - THE RESTRICTIONS ARE NAMED, NOT BAKED IN, and T1-D cashed two of the
      three in.  THE GATE TABLE, as it now stands:

      * [lb_nobarex] — "not a BARE conditional write".  A lone [LExStore]
        is genuinely unrealizable: it has no reservation to consume, and
        the axiomatic [mstate] has no room for one.  [LExLoad] is NOT
        gated any more: a DANGLING exclusive read (the walker's A/D
        re-read race, an amocas miss — both real xv6 shapes) realizes an
        axiomatic PLAIN LOAD in the single-step form, which is what
        [proj_lbl]'s own [LExLoad ↦ LLoad] arm always said.  This
        REPLACES [lb_fused]: the exclusive PAIR realizes an axiomatic
        [LRmw] through [lbl_realizes_pair] (A3(iv)).
      * [lat_free] — the one gate the forward direction does not need
        (it already HAS a [read_ok_d]); the axiomatic [rd_ok] carries no
        "no writes above" evidence, so a [lat = true] load cannot be
        replayed.  The instance discharges it today
        ([WeakEvCapstone.pstep_ev_lat_free_prog]).
      * [lb_rfoldfree] — "every operand list that still reaches a BYTE
        FOLD is empty".  This REPLACES [lb_depfree], and since D-7r/D-2r
        that is exactly TWO places: a plain load's [asrc] (which is
        [WeakPromise.lb_ldepfree], deviation D-8 — the instance satisfies
        it by construction) and the FUSED rmw's read half.  Stores'
        [asrc]/[vsrc] and the exclusives' operands are FREE.  See
        [lb_rfoldfree] below for why the fused rmw's pin is a recorded
        D-2r residue and not a design choice.

    - IT ABSORBS THE CLASS PREMISE.  [proj_lbl] carries the message class
      in the [LStore]/[LRmw]/[LExStore] arms, so
      [proj_lbl (pcls p l ws) l = Some lb] SAYS
      [WeakPromiseBridge.mstep_cls_ok] at the acting agent's own per-step
      program state and wstate.  The separate [exec_cls_ok] premise
      therefore does not need re-indexing — it is gone.  What T1-D adds
      beside it is [WeakPromiseBridge.pcls_eqr pcls], an
      INSTANCE-DISCHARGED obligation (the analogue of
      [WeakRobustTrace.pcls_obl]): the class the supply names is read at
      the AXIOMATIC [wstate] and the class the machine stamps at the
      MACHINE one, and those two are [ws_eqr]-equal, not equal.

    ** What the realization now concludes

    [cfg_matchd], not [cfg_match].  The image and the LOG are still EQUAL —
    which is all the capstone's conclusion rides on — and the per-agent
    [wstate]s are related by [ws_eqr].  The [cfg_match]-tier statements
    remain available, unweakened, in [WeakPromiseBridge] itself
    ([exec_prefix_pf_run] / [exec_wf_pf_run]); this file's [prog_free]
    corollaries below are their [cfg_matchd] shadows, kept to show the
    supply generalizes them, NOT as replacements (the pre-T1-D header claim
    that the bridge's own copies were redundant is retracted: at the real
    alphabet the machine's [wstate] is not the axiomatic one).

    DEPENDENCY-FREE like the bridge: stdpp, [WeakMem], [WeakPromise],
    [WeakPromiseFact], [WeakAxiomatic], [WeakPromiseBridge].  No Iris, no
    Sail.

    NOTE ON NAMES: [WeakPromise] and [WeakAxiomatic] both export
    [LLoad]/[LStore]/[LFence]/[LRmw]; the latter shadows the former, so
    every occurrence below is QUALIFIED. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakAxiomatic
     WeakPromiseBridge.

Local Open Scope Z_scope.

(* ================================================================== *)
(** ** (0) THE THREE LABEL GATES *)

(** [l] IS NOT A BARE CONDITIONAL WRITE.  [lb_fused]'s T1-D replacement:
    where [lb_fused] excluded BOTH split labels, this excludes only
    [LExStore].

    WHY [LExLoad] MAY NOW STAND ALONE.  [proj_lbl] sends it to the
    axiomatic PLAIN LOAD, and since D-2r the exclusive read IS the plain
    read plus a reservation ([WeakMem.exload_post_run_d] folds at the plain
    pre-view and is admissible at the plain floor) — so the only thing
    separating it from [LLoad] is [w_res], which [ws_eqr] does not relate.
    A dangling exclusive read is therefore realizable, which matters
    because the real image HAS them (the page walker's abandoned
    reservation, an [amocas] miss).

    WHY [LExStore] MAY NOT.  Its arm [PFExStore] READS [w_res], and the
    axiomatic [mstate] has no reservation to supply — a bare conditional
    write has no per-event axiomatic image at all.  It is realizable only
    as the SECOND HALF OF A PAIR, which is [lbl_realizes_pair]. *)
Definition lb_nobarex (l : wlabel) : Prop :=
  match l with
  | LSilent | WeakPromise.LLoad _ _ _ _ _ | WeakPromise.LStore _ _ _ _ _ | WeakPromise.LRmw _ _ _ _ _ _ _
  | WeakPromise.LFence _ _ _ _ | LDev | LRegW _ _ | LCtrl _ | LInstr
  | LExLoad _ _ _ _ => True
  | LExStore _ _ _ _ _ => False
  end.

(** EVERY OPERAND LIST THAT STILL REACHES A BYTE FOLD IS EMPTY.
    [lb_depfree]'s T1-D replacement, and a strict WEAKENING of it
    ([lb_depfree_rfoldfree]).

    [ws_eqr] relates the components a byte fold writes ([coh], the four
    frontiers, [w_vRel], [w_fwd], [w_pub], [w_relp]) but not [w_vcap], so a
    machine post-state is [ws_eqr]-related to the [mstep] one exactly when
    the operands it carries never leave [w_vcap].  Since D-7r
    ([WeakMem.store_post_d] ignores [vf]) and D-2r
    ([WeakMem.exload_post_run_d] folds at the plain pre-view) that holds for
    stores, for the exclusive read and for the conditional write.  Two
    read folds are left:

    - A PLAIN LOAD'S [asrc], which enters [load_vpre_d] and hence every
      byte's post-view.  This conjunct is literally
      [WeakPromise.lb_ldepfree] ([lb_rfoldfree_ldepfree]), D3-2's gate:
      the event instance satisfies it BY CONSTRUCTION (deviation D-8 — a
      load's data read and the walker's PTE read are indistinguishable at
      the node, so attaching the base register would be a strengthening
      beyond RVWMO's syntactic dependencies).
    - THE FUSED [LRmw]'s read half.  [WeakPromiseBridge.PFRmw]'s POST-STATE
      still folds at [load_vpre_d … (srcs_view asrc)] — D-2r's deliberately
      recorded residue ("the fused [WPRmw]/[PFRmw] post-state/EXT keep the
      address view; they die at R6").  Its ADMISSIBILITY is already at the
      0 floor, so this is a post-state pin only, and it is exactly the pin
      [lb_depfree] gave the fused rmw before T1-D: nothing is lost.  No
      producer in this tree emits [LRmw] anyway
      ([WeakEvInst.pstep_ev_no_rmw]), and when R6 deletes the fused arms
      this conjunct becomes literally [lb_ldepfree]. *)
Definition lb_rfoldfree (l : wlabel) : Prop :=
  match l with
  | WeakPromise.LLoad _ _ _ _ asrc => asrc = []
  | WeakPromise.LRmw _ _ _ _ _ asrc _ => asrc = []
  | LSilent | WeakPromise.LStore _ _ _ _ _ | WeakPromise.LFence _ _ _ _ | LDev
  | LRegW _ _ | LCtrl _ | LInstr
  | LExLoad _ _ _ _ | LExStore _ _ _ _ _ => True
  end.

Lemma lb_depfree_rfoldfree l : lb_depfree l → lb_rfoldfree l.
Proof. destruct l; simpl; by try (intros [-> ?] || intros ->). Qed.

Lemma lb_rfoldfree_ldepfree l : lb_rfoldfree l → lb_ldepfree l.
Proof. destruct l; simpl; by try (intros ->). Qed.

Lemma lb_fused_nobarex l : lb_fused l → lb_nobarex l.
Proof. by destruct l. Qed.

(* ------------------------------------------------------------------ *)
(** ** (0b) THE ADMINISTRATIVE ALPHABET

    THE ADMIN CLASS IS EXACTLY THE LABELS [proj_lbl] SENDS TO [None]:
    [LSilent], [LDev] and the three dependency-only labels
    [LRegW]/[LCtrl]/[LInstr].  Each has a [wp_pf_step] arm, each leaves the
    image and the LOG alone, and each moves the [wstate] only through the
    dependency components — i.e. within [ws_eqr]
    ([WeakMem.ws_depmove], [WeakPromiseBridge.ws_depmove_ws_eqr]).  That is
    what lets a whole STRETCH of them run between two trace events without
    the axiomatic side moving at all.

    THE BOOLEAN INDEX IS [LInstr]'s.  [WeakMem.instr_post] CLEARS [w_res],
    so an [LInstr] inside an exclusive pair would destroy the reservation
    the conditional write consumes; the intra-pair star therefore runs at
    [instr := false].  The instance discharges the exclusion trivially:
    there is no instruction boundary inside an instruction.

    AND NOTE WHAT IS NOT ADMIN: a LOAD.  [WeakMem.load_post_at] clears
    [w_res] per byte (the clear-on-own-load rule), so a load inside the
    pair would starve [PFExStore] just as [LInstr] would — but a load is
    not in this alphabet at all, so the star cannot contain one.  That is
    the whole argument for the pair's reservation survival, and it is
    structural, not an invariant. *)
Definition lb_admin (instr : bool) (l : wlabel) : Prop :=
  match l with
  | LSilent | LDev | LRegW _ _ | LCtrl _ => True
  | LInstr => instr = true
  | WeakPromise.LLoad _ _ _ _ _ | WeakPromise.LStore _ _ _ _ _ | WeakPromise.LRmw _ _ _ _ _ _ _
  | WeakPromise.LFence _ _ _ _ | LExLoad _ _ _ _ | LExStore _ _ _ _ _ => False
  end.

(** The [LInstr]-free star is a sub-alphabet of the full one. *)
Lemma lb_admin_mono instr l : lb_admin false l → lb_admin instr l.
Proof. by destruct l. Qed.

(** ... and the whole alphabet is invisible to the projection. *)
Lemma lb_admin_proj k instr l : lb_admin instr l → proj_lbl k l = None.
Proof. by destruct l. Qed.

(* ================================================================== *)
Section realize.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).

  Implicit Types c : wpcfg P D.

  (* ---------------------------------------------------------------- *)
  (** ** (1) The label-supply relation *)

  (** [l] REALIZES the axiomatic label [lb] for agent [i] at state [σ],
      run at the acting agent's program state [p]: it is a label outside
      the three gates above whose projection — with the class the machine
      would stamp, read at [p] and the agent's own [wstate] — is [lb]. *)
  Definition lbl_realizes (p : P) (σ : mstate) (i : agent)
      (lb : WeakAxiomatic.lbl) (l : wlabel) : Prop :=
    lb_nobarex l ∧ lat_free l ∧ lb_rfoldfree l ∧
    proj_lbl (pcls p l (ms_ws σ i)) l = Some lb.

  (** Under the PRE-T1-D gates the relation is FUNCTIONAL, and its value is
      the canonical [unproj_lbl]; the class side condition it carries is
      exactly [mstep_cls_ok].  The two gates are now premises rather than
      conjuncts — which is precisely the coverage T1-D bought: at
      [lb_depfree ∧ lb_fused] shape (2) is still shape (1), and OFF them it
      is strictly more. *)
  Lemma lbl_realizes_unproj p σ i lb l :
    lb_depfree l → lb_fused l →
    lbl_realizes p σ i lb l →
    l = unproj_lbl lb ∧ mstep_cls_ok pcls p σ i lb.
  Proof.
    intros Hdf Hfu (_ & Hlat & _ & Hpr).
    destruct l; simpl in Hfu, Hlat, Hdf, Hpr; try done.
    - (* load: [lat_free] gives [lat = false], [lb_depfree] gives
         [asrc = []], and [zip] round-trips a list of pairs *)
      subst lat asrc. simplify_eq/=. by rewrite zip_fst_snd.
    - (* store: the class binder is [pcls] applied to THIS label *)
      destruct Hdf as [-> ->]. simplify_eq/=. done.
    - (* rmw *)
      destruct Hdf as [-> ->]. simplify_eq/=.
      by rewrite zip_fst_snd.
    - (* fence *) by simplify_eq/=.
  Qed.

  (** The converse, at a label the axiomatic side actually stepped with:
      the [rd_ok] lengths inside [mstep] are what make [zip] round-trip. *)
  Lemma lbl_realizes_intro p σ σ' i lb :
    mstep σ i lb σ' → mstep_cls_ok pcls p σ i lb →
    lbl_realizes p σ i lb (unproj_lbl lb).
  Proof.
    intros Hms Hck.
    have Hzip : ∀ (ts : list nat) (vs : list (bv 8)),
      length ts = length vs →
      (zip ts vs).*1 = ts ∧ (zip ts vs).*2 = vs.
    { intros ts vs Hlen. split; [apply fst_zip|apply snd_zip]; lia. }
    inversion Hms as
      [aq base ts vs Hrd Hlb Hσ'
      |rl base vs kc Hnn Hlb Hσ'
      |pr pw sr sw Hlb Hσ'
      |aq rl base ts rvs wvs kc Hnn Hlen Hrd Hlat Hlb Hσ']; subst lb;
      rewrite /lbl_realizes;
      cbn [unproj_lbl proj_lbl lb_nobarex lat_free lb_rfoldfree] in Hck |- *;
      split_and!; try done.
    - (* load: the projection re-splits the zip *)
      destruct Hrd as [Hlen _]. destruct (Hzip ts vs ltac:(lia)) as [-> ->].
      done.
    - (* store: the class equation IS [mstep_cls_ok] *)
      by rewrite Hck.
    - (* rmw: both *)
      destruct Hrd as [Hlen' _]. destruct (Hzip ts rvs ltac:(lia)) as [-> ->].
      by rewrite Hck.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (1b) THE PAIR (A3(iv)): one axiomatic rmw, two machine steps

      A LONE split label is unrealizable in one direction only — a bare
      [LExStore] has no reservation to consume — so the alphabet gate
      [lb_nobarex] keeps just that one out, and ONE axiomatic step is
      realized by a SHORT SEQUENCE instead: the exclusive pair, same agent,
      with an ADMINISTRATIVE STRETCH allowed between the halves (the AMO's
      own [LRegW]s and [LCtrl]s live there).

      WHY THE PAIR IS EXACTLY EQUIVALENT HERE.  [exload_post_run_d] is
      [load_post_run_d] under [ws_res_set], and the conditional write's
      [store_post_run_d] CLEARS [w_res] on its first byte ([data ≠ []]), so
      the reservation is created and consumed inside the pair; the window
      premise is the same fact twice, since the axiomatic [rmw_latest] gives
      [excl_ok_ts] on the reservation's own timestamp column
      ([rmw_latest_excl_ok_ts]).

      THE CLASS is read at the CONDITIONAL WRITE's own program state [pm]
      — the state the intra-pair star ENDS at, which is where [PFExStore]
      reads it — and at the AXIOMATIC read post-state
      [load_post_run (ms_ws σ i) …], which is the only [wstate] the caller
      can name (the machine's has a reservation [mstate] has no room for).
      The two differ only within [ws_eqr], which is what [pcls_eqr] absorbs. *)
  Definition lbl_realizes_pair (p pm : P) (σ : mstate) (i : agent)
      (lb : WeakAxiomatic.lbl) (l1 l2 : wlabel) : Prop :=
    ∃ aq rl base tvs data asrc1 asrc2 vsrc2,
      l1 = LExLoad aq base tvs asrc1 ∧
      l2 = LExStore rl base data asrc2 vsrc2 ∧
      data ≠ [] ∧ length tvs = length data ∧
      lb = WeakAxiomatic.LRmw aq rl base tvs.*1 tvs.*2 data
             (pcls pm l2 (load_post_run (ms_ws σ i) aq base tvs.*1)).

  (** The pair's composition, as a state equation.  [ws_res_set] is
      invisible to a store run that writes at least one byte, because
      [WeakMem.store_post_d] assigns [w_res := None] per byte.  (The
      [None]-instance twin of this lemma, used by the FORWARD direction, is
      [WeakRefuse.store_post_run_d_res]; neither file depends on the other,
      and the fact is five lines of conversion.) *)
  Lemma store_post_run_d_res_pair ws r rl vaddr vdata base n t :
    (0 < n)%nat →
    store_post_run_d (ws_res_set ws r) rl vaddr vdata base n t
    = store_post_run_d ws rl vaddr vdata base n t.
  Proof.
    intros Hn. rewrite /store_post_run_d /store_post_bytes_d /store_run_as.
    destruct n as [|m]; [lia|done].
  Qed.

  (** [excl_ok] on the reservation's timestamp column — the shape
      [PFExStore] asks for. *)
  Lemma rmw_latest_excl_ok_ts img log i base ts :
    rmw_latest img log base ts →
    excl_ok_ts log i base ts (S (length log)).
  Proof.
    intros Hlat j t Ht Hw. destruct (Hlat j t Ht) as [_ Hnw].
    rewrite /acc_addr in Hnw. apply Hnw.
    eapply writes_in_mono;
      [| |by apply (writes_in_by_writes_in log (λ tid, tid ≠ Some i))]; lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (2) The administrative star, on the PROGRAM side *)

  Definition adm_step (instr : bool) (x y : P * D) : Prop :=
    ∃ l, lb_admin instr l ∧ pstep x.1 x.2 l y.1 y.2.

  (** A finite run of administrative program steps, fabric threaded (the
      intermediate device states are existential — the axiomatic trace has
      no position for them). *)
  Definition adm_star (instr : bool) (p : P) (d : D) (p' : P) (d' : D) : Prop :=
    rtc (adm_step instr) (p, d) (p', d').

  Lemma adm_star_refl instr p d : adm_star instr p d p d.
  Proof. apply rtc_refl. Qed.

  Lemma adm_star_l instr p d l p1 d1 p' d' :
    lb_admin instr l → pstep p d l p1 d1 → adm_star instr p1 d1 p' d' →
    adm_star instr p d p' d'.
  Proof. intros Ha Hs Hr. eapply rtc_l; [|exact Hr]. by exists l. Qed.

  Lemma adm_step_mono instr x y : adm_step false x y → adm_step instr x y.
  Proof.
    intros (l & Ha & Hs). exists l. split; [by apply lb_admin_mono|done].
  Qed.

  Lemma adm_star_mono_rtc instr x y :
    rtc (adm_step false) x y → rtc (adm_step instr) x y.
  Proof.
    induction 1 as [x|x y z Hs _ IH]; [apply rtc_refl|].
    eapply rtc_l; [|exact IH]. by apply adm_step_mono.
  Qed.

  Lemma adm_star_mono instr p d p' d' :
    adm_star false p d p' d' → adm_star instr p d p' d'.
  Proof. apply adm_star_mono_rtc. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (3) The program-carrying hypothesis

      A per-event assignment of program states ([pst k] = the agent list as
      of trace position [k]) and of the FABRIC ([dv k]), together with the
      [pstep]s that carry position [k] to [k+1]: an ADMINISTRATIVE STAR and
      then the realizing step — or, for the exclusive PAIR (A3(iv)),
      an administrative star, the exclusive read, an [LInstr]-FREE
      administrative star, and the conditional write.  The frame condition —
      every other agent's program state is untouched — is spelled as the
      list INSERT, which also keeps [length (pst k)] constant for free; note
      that the stars' and the pair's INTERMEDIATE program states and fabrics
      are existential and never appear in [pst]/[dv], since the axiomatic
      trace has no position for them. *)
  Definition exec_prog_ok' (pst : nat → list P) (dv : nat → D)
      (E : exec) : Prop :=
    ∀ k s, ex_tr E !! k = Some s →
      ∃ p pa da p',
        pst k !! es_ag s = Some p ∧
        pst (S k) = <[es_ag s := p']> (pst k) ∧
        adm_star true p (dv k) pa da ∧
        ((∃ l, lbl_realizes pa (stt E k) (es_ag s) (es_lb s) l ∧
               pstep pa da l p' (dv (S k)))
         ∨ (∃ pm dm pm2 dm2 l1 l2,
              lbl_realizes_pair pa pm2 (stt E k) (es_ag s) (es_lb s) l1 l2 ∧
              pstep pa da l1 pm dm ∧
              adm_star false pm dm pm2 dm2 ∧
              pstep pm2 dm2 l2 p' (dv (S k)))).

  (** THE EMPTY-STAR SPECIALIZATION — the pre-T1-D shape of the hypothesis,
      kept because it is the one a [prog_free] instance supplies (nothing
      administrative happens when every label is admitted at every state).
      [prog_free] itself got the same treatment in part (5) below. *)
  Definition exec_prog_ok (pst : nat → list P) (dv : nat → D)
      (E : exec) : Prop :=
    ∀ k s, ex_tr E !! k = Some s →
      ∃ p p',
        pst k !! es_ag s = Some p ∧
        pst (S k) = <[es_ag s := p']> (pst k) ∧
        ((∃ l, lbl_realizes p (stt E k) (es_ag s) (es_lb s) l ∧
               pstep p (dv k) l p' (dv (S k)))
         ∨ (∃ pm dm l1 l2,
              lbl_realizes_pair p pm (stt E k) (es_ag s) (es_lb s) l1 l2 ∧
              pstep p (dv k) l1 pm dm ∧ pstep pm dm l2 p' (dv (S k)))).

  Lemma exec_prog_ok_star pst dv E :
    exec_prog_ok pst dv E → exec_prog_ok' pst dv E.
  Proof.
    intros H k s Hs. destruct (H k s Hs) as (p & p' & Hp & Hn & Hsup).
    exists p, p, (dv k), p'. split_and!; [done|done|apply adm_star_refl|].
    destruct Hsup as [(l & Hre & Hps)|(pm & dm & l1 & l2 & Hre & Hps1 & Hps2)].
    - left. by exists l.
    - right. exists pm, dm, pm, dm, l1, l2.
      split_and!; [done|done|apply adm_star_refl|done].
  Qed.

  (** The old one-step form is the left disjunct of the empty-star shape. *)
  Lemma exec_prog_ok_single pst dv E :
    (∀ k s, ex_tr E !! k = Some s →
       ∃ p p' l,
         pst k !! es_ag s = Some p ∧
         lbl_realizes p (stt E k) (es_ag s) (es_lb s) l ∧
         pstep p (dv k) l p' (dv (S k)) ∧
         pst (S k) = <[es_ag s := p']> (pst k)) →
    exec_prog_ok pst dv E.
  Proof.
    intros H k s Hs. destruct (H k s Hs) as (p & p' & l & Hp & Hre & Hps & Hn).
    exists p, p'. split_and!; [done|done|]. left. by exists l.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (4) The administrative star, on the MACHINE side

      One admin step, then the star.  The conclusion never mentions an
      [mstate]: it says the configuration moved within [cfg_eqr] (same
      image, same log, every agent's [wstate] moved only within [ws_eqr]),
      which is what carries BOTH [cfg_matchd] (through
      [cfg_eqr_matchd]) and — inside the exclusive pair, where no
      [cfg_matchd] holds in the middle — the reservation. *)
  Lemma adm_step_pf instr c i ag l p' d' :
    lb_admin instr l →
    pc_ags c !! i = Some ag →
    pstep (pa_st ag) (pc_dev c) l p' d' →
    ∃ c' ag',
      wp_pf_step pstep pcls i l c c' ∧ cfg_eqr c c' ∧ pc_dev c' = d' ∧
      pc_ags c' !! i = Some ag' ∧ pa_st ag' = p' ∧
      ws_eqr (pa_ws ag) (pa_ws ag') ∧
      (instr = false → w_res (pa_ws ag') = w_res (pa_ws ag)) ∧
      pa_st <$> pc_ags c' = <[i := p']> (pa_st <$> pc_ags c).
  Proof.
    intros Hadm Hlk Hps.
    pose proof (lookup_lt_Some _ _ _ Hlk) as Hlti.
    (* the three configuration facts are the same in every arm *)
    have Hpkg : ∀ (w : wstate) (d0 : D),
      ws_eqr (pa_ws ag) w →
      cfg_eqr c (WPCfg (pc_img c) (pc_log c) d0
                   (<[i := WPAgent p' w (pa_prom ag)]> (pc_ags c))) ∧
      (<[i := WPAgent p' w (pa_prom ag)]> (pc_ags c)) !! i
        = Some (WPAgent p' w (pa_prom ag)) ∧
      pa_st <$> (<[i := WPAgent p' w (pa_prom ag)]> (pc_ags c))
        = <[i := p']> (pa_st <$> pc_ags c).
    { intros w d0 He. split_and!.
      - split_and!; [done|done|]. intros j agj' Hj. simpl in Hj.
        destruct (decide (j = i)) as [->|Hne].
        + rewrite list_lookup_insert in Hj; [done|simplify_eq/=].
          exists ag. by split.
        + rewrite list_lookup_insert_ne // in Hj. exists agj'. split; [done|].
          reflexivity.
      - by rewrite list_lookup_insert.
      - by rewrite list_fmap_insert. }
    destruct l as [ |aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rd srcs|srcs| |
                   aq base tvs asrc|rl base data asrc vsrc];
      simpl in Hadm; try done.
    - (* LSilent *)
      destruct (Hpkg (pa_ws ag) d' ltac:(reflexivity)) as (H1 & H2 & H3).
      eexists _, _. split_and!;
        [by eapply PFSilent|exact H1|done|exact H2|done|reflexivity|
         intros _; reflexivity|exact H3].
    - (* LDev *)
      destruct (Hpkg (pa_ws ag) d' ltac:(reflexivity)) as (H1 & H2 & H3).
      eexists _, _. split_and!;
        [by eapply PFDev|exact H1|done|exact H2|done|reflexivity|
         intros _; reflexivity|exact H3].
    - (* LRegW *)
      destruct (Hpkg (regw_post (pa_ws ag) rd (srcs_view (pa_ws ag) srcs)) d'
                  (ws_eqr_regw_post _ _ _)) as (H1 & H2 & H3).
      eexists _, _. split_and!;
        [by eapply PFRegW|exact H1|done|exact H2|done|
         apply ws_eqr_regw_post|intros _; reflexivity|exact H3].
    - (* LCtrl *)
      destruct (Hpkg (ctrl_post (pa_ws ag) (srcs_view (pa_ws ag) srcs)) d'
                  (ws_eqr_ctrl_post _ _)) as (H1 & H2 & H3).
      eexists _, _. split_and!;
        [by eapply PFCtrl|exact H1|done|exact H2|done|
         apply ws_eqr_ctrl_post|intros _; reflexivity|exact H3].
    - (* LInstr: only in the [instr = true] star, so the reservation
         obligation is vacuous *)
      destruct (Hpkg (instr_post (pa_ws ag)) d'
                  (ws_eqr_instr_post _)) as (H1 & H2 & H3).
      eexists _, _. split_and!;
        [by eapply PFInstr|exact H1|done|exact H2|done|
         apply ws_eqr_instr_post| |exact H3].
      intros Hf. rewrite Hf in Hadm. done.
  Qed.

  Lemma adm_star_pf_run instr x y :
    rtc (adm_step instr) x y →
    ∀ c i ag, pc_ags c !! i = Some ag → pa_st ag = x.1 → pc_dev c = x.2 →
    ∃ c' ag',
      rtc (wp_pf_run pstep pcls) c c' ∧ cfg_eqr c c' ∧ pc_dev c' = y.2 ∧
      pc_ags c' !! i = Some ag' ∧ pa_st ag' = y.1 ∧
      ws_eqr (pa_ws ag) (pa_ws ag') ∧
      (instr = false → w_res (pa_ws ag') = w_res (pa_ws ag)) ∧
      pa_st <$> pc_ags c' = <[i := y.1]> (pa_st <$> pc_ags c).
  Proof.
    induction 1 as [x|x y z (l & Hadm & Hps) _ IH];
      intros c i ag Hlk Hst Hdev.
    - exists c, ag. split_and!.
      + apply rtc_refl.
      + apply cfg_eqr_refl.
      + exact Hdev.
      + exact Hlk.
      + exact Hst.
      + reflexivity.
      + intros _. reflexivity.
      + rewrite -Hst list_insert_id;
          [by rewrite list_lookup_fmap Hlk|reflexivity].
    - destruct (adm_step_pf instr c i ag l y.1 y.2 Hadm Hlk
                  ltac:(rewrite Hst Hdev; exact Hps))
        as (c1 & ag1 & Hstep & He1 & Hd1 & Hl1 & Hs1 & Hw1 & Hr1 & Hf1).
      destruct (IH c1 i ag1 Hl1 Hs1 Hd1)
        as (c2 & ag2 & Hrun & He2 & Hd2 & Hl2 & Hs2 & Hw2 & Hr2 & Hf2).
      exists c2, ag2. split_and!; [| |done|done|done| | |].
      + eapply rtc_l; [|exact Hrun]. by exists i, l.
      + by eapply cfg_eqr_trans.
      + by etrans.
      + intros Hi. by rewrite (Hr2 Hi) (Hr1 Hi).
      + rewrite Hf2 Hf1 list_insert_insert //.
  Qed.

  Lemma adm_star_pf instr c i ag p' d' :
    pc_ags c !! i = Some ag →
    adm_star instr (pa_st ag) (pc_dev c) p' d' →
    ∃ c' ag',
      rtc (wp_pf_run pstep pcls) c c' ∧ cfg_eqr c c' ∧ pc_dev c' = d' ∧
      pc_ags c' !! i = Some ag' ∧ pa_st ag' = p' ∧
      ws_eqr (pa_ws ag) (pa_ws ag') ∧
      (instr = false → w_res (pa_ws ag') = w_res (pa_ws ag)) ∧
      pa_st <$> pc_ags c' = <[i := p']> (pa_st <$> pc_ags c).
  Proof.
    intros Hlk Hst.
    by apply (adm_star_pf_run instr (pa_st ag, pc_dev c) (p', d') Hst c i ag).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (5) One realizing step

      [WeakPromiseBridge.mstep_wp_pf_step] with the [prog_free] supply
      replaced by the given [pstep], the "program states are untouched"
      conclusion replaced by the insert, and the state relation weakened to
      [cfg_matchd].  The case analysis is on the MACHINE LABEL now (it is no
      longer determined by [lb]), which is also where the alphabet gates are
      consumed. *)
  Lemma mstep_wp_pf_step_prog σ σ' i lb c ag p p' l dn :
    pcls_eqr pcls →
    cfg_matchd c σ → pc_ags c !! i = Some ag → pa_st ag = p →
    lbl_realizes p σ i lb l →
    pstep p (pc_dev c) l p' dn →
    mstep σ i lb σ' →
    ∃ c', wp_pf_step pstep pcls i l c c' ∧ cfg_matchd c' σ' ∧
          pa_st <$> pc_ags c' = <[i := p']> (pa_st <$> pc_ags c) ∧
          pc_dev c' = dn.
  Proof.
    intros Hce Hm Hlk Hag (Hnb & Hlat & Hrf & Hpr) Hps Hms.
    subst p.
    pose proof (cfg_matchd_ws c σ i ag Hm Hlk) as Hew.
    destruct σ as [img lg f].
    destruct Hm as (Himg & Hlg & Hf). simpl in Himg, Hlg, Hf, Hew.
    subst img lg.
    (* the [cfg_matchd] obligation is the same three lines in every arm *)
    have Hmatch : ∀ (st' : P) (w : wstate) (pr : gset nat) (lg' : list wmsg)
                    (d' : D) (g : agent → wstate),
      ws_eqr (g i) w → (∀ j, j ≠ i → g j = f j) →
      cfg_matchd (WPCfg (pc_img c) lg' d'
                   (<[i := WPAgent st' w pr]> (pc_ags c)))
                (MSt (pc_img c) lg' g).
    { intros st' w pr lg' d' g Hgi Hgne.
      by eapply (cfg_matchd_upd_gen _ _ _ _ i ag st' w pr f g). }
    (* the program projection moves by exactly the insert *)
    have Hst : ∀ (st' : P) (w : wstate) (pr : gset nat),
      pa_st <$> (<[i := WPAgent st' w pr]> (pc_ags c))
      = <[i := st']> (pa_st <$> pc_ags c).
    { intros st' w pr. by rewrite list_fmap_insert. }
    destruct l as [ |aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rd srcs|srcs| |
                   aq base tvs asrc|rl base data asrc vsrc];
      simpl in Hnb, Hlat, Hrf, Hpr; try done.
    - (* PLAIN LOAD.  [lb_rfoldfree] pins [asrc = []], so both the read
         floor and the byte fold are the dependency-free ones. *)
      subst lat asrc. simplify_eq/=.
      inversion Hms as [aq0 base0 ts0 vs0 Hrd Hlb Hσ'| | | ]; simplify_eq/=.
      eexists. split_and!.
      + apply (PFLoad pstep pcls i c ag aq false base tvs [] p' dn);
          [done|exact Hps|].
        rewrite srcs_view_nil read_ok_d_0.
        eapply ws_eqr_read_ok; [exact Hew|].
        rewrite -(zip_fst_snd tvs). by apply rd_ok_read_ok.
      + rewrite srcs_view_nil load_post_run_d_0.
        apply Hmatch; [rewrite upd_ws_eq; by apply ws_eqr_load_post_run|].
        intros j Hne. by rewrite upd_ws_ne.
      + apply Hst.
      + done.
    - (* STORE at a REAL operand list.  No admissibility; the byte fold is
         [store_post_bytes] on both sides (D-7r), and the class equation is
         [pcls_eqr]. *)
      simplify_eq/=.
      inversion Hms as [ |rl0 base0 vs0 kc0 Hnn Hlb Hσ'| | ]; simplify_eq/=.
      have Hk : pcls (pa_st ag) (WeakPromise.LStore rl base data asrc vsrc) (f i)
              = pcls (pa_st ag) (WeakPromise.LStore rl base data asrc vsrc)
                  (pa_ws ag)
        by apply Hce.
      eexists. split_and!.
      + apply (PFStore pstep pcls i c ag rl base data asrc vsrc
                 (pcls (pa_st ag) (WeakPromise.LStore rl base data asrc vsrc)
                    (pa_ws ag)) p' dn);
          [done|exact Hps|done|reflexivity].
      + rewrite Hk.
        apply Hmatch; [rewrite upd_ws_eq; by apply ws_eqr_store_post_run_d|].
        intros j Hne. by rewrite upd_ws_ne.
      + apply Hst.
      + done.
    - (* THE FUSED RMW.  [lb_rfoldfree] pins [asrc = []] (D-2r's post-state
         residue); [vsrc] is free. *)
      subst asrc. simplify_eq/=.
      inversion Hms as [ | |
                        |aq0 rl0 base0 ts0 rvs0 wvs0 kc0 Hnn Hlen Hrd Hlt Hlb
                           Hσ']; simplify_eq/=.
      have Hk : pcls (pa_st ag) (WeakPromise.LRmw aq rl base tvs data [] vsrc)
                  (f i)
              = pcls (pa_st ag) (WeakPromise.LRmw aq rl base tvs data [] vsrc)
                  (pa_ws ag)
        by apply Hce.
      have Hro : read_ok (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs.
      { eapply ws_eqr_read_ok; [exact Hew|].
        rewrite -(zip_fst_snd tvs). by apply rd_ok_read_ok. }
      eexists. split_and!.
      + apply (PFRmw pstep pcls i c ag aq rl base tvs data [] vsrc
                 (pcls (pa_st ag) (WeakPromise.LRmw aq rl base tvs data [] vsrc)
                    (pa_ws ag)) p' dn);
          [done|exact Hps|done| |exact Hro| |reflexivity].
        * rewrite length_fmap in Hlen. lia.
        * rewrite -(zip_fst_snd tvs).
          by apply (rmw_latest_excl_ok (pc_img c) _ i base tvs.*1 tvs.*2).
      + rewrite Hk srcs_view_nil load_post_run_d_0.
        apply Hmatch;
          [rewrite upd_ws_eq; apply ws_eqr_store_post_run_d;
             by apply ws_eqr_load_post_run|].
        intros j Hne. by rewrite upd_ws_ne.
      + apply Hst.
      + done.
    - (* FENCE: unchanged. *)
      simplify_eq/=.
      inversion Hms as [ | |pr0 pw0 sr0 sw0 Hlb Hσ'| ]; simplify_eq/=.
      eexists. split_and!.
      + apply (PFFence pstep pcls i c ag pr pw sr sw p' dn); [done|exact Hps].
      + apply Hmatch; [rewrite upd_ws_eq; by apply ws_eqr_fence_post|].
        intros j Hne. by rewrite upd_ws_ne.
      + apply Hst.
      + done.
    - (* THE DANGLING EXCLUSIVE READ, realizing a PLAIN axiomatic load.
         Admissibility is at the 0 floor and the byte fold is the plain one
         (D-2r); the reservation lands in [w_res], which [ws_eqr] does not
         relate. *)
      simplify_eq/=.
      inversion Hms as [aq0 base0 ts0 vs0 Hrd Hlb Hσ'| | | ]; simplify_eq/=.
      eexists. split_and!.
      + apply (PFExLoad pstep pcls i c ag aq base tvs asrc p' dn);
          [done|exact Hps|].
        eapply ws_eqr_read_ok; [exact Hew|].
        rewrite -(zip_fst_snd tvs). by apply rd_ok_read_ok.
      + apply Hmatch;
          [rewrite upd_ws_eq; by apply ws_eqr_exload_post_run_d|].
        intros j Hne. by rewrite upd_ws_ne.
      + apply Hst.
      + done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (5b) The PAIR step (A3(iv))

      [mstep_wp_pf_step_prog]'s twin for an axiomatic [LRmw] realized by
      [LExLoad; administrative star; LExStore].  What is new relative to a
      single step is only that the reservation is created by the first step,
      SURVIVES the star (its labels are the ones that keep [w_res]:
      [regw_post]/[ctrl_post] copy it, [LSilent]/[LDev] do not touch the
      [wstate] at all, and the star's alphabet contains neither [LInstr] nor
      any load) and is consumed by the last step, and that [cfg_matchd] is
      restored at the END — never in the middle, since the intermediate
      configuration's views have already moved past σ's. *)
  Lemma mstep_wp_pf_step_pair σ σ' i lb c ag p pm pm2 p' l1 l2 dm dm2 dn :
    pcls_eqr pcls →
    cfg_matchd c σ → pc_ags c !! i = Some ag → pa_st ag = p →
    lbl_realizes_pair p pm2 σ i lb l1 l2 →
    pstep p (pc_dev c) l1 pm dm →
    adm_star false pm dm pm2 dm2 →
    pstep pm2 dm2 l2 p' dn →
    mstep σ i lb σ' →
    ∃ c', rtc (wp_pf_run pstep pcls) c c' ∧ cfg_matchd c' σ' ∧
          pa_st <$> pc_ags c' = <[i := p']> (pa_st <$> pc_ags c) ∧
          pc_dev c' = dn.
  Proof.
    intros Hce Hm Hlk Hag Hre Hps1 Hstar Hps2 Hms.
    subst p.
    pose proof (cfg_matchd_ws c σ i ag Hm Hlk) as Hew.
    pose proof (lookup_lt_Some _ _ _ Hlk) as Hlti.
    destruct Hre as (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
                     -> & -> & Hnn & Hlen & Hlb).
    destruct σ as [img lg f].
    destruct Hm as (Himg & Hlg & Hf). simpl in Himg, Hlg, Hf, Hew, Hlb.
    subst img lg lb.
    inversion Hms as [ | |
                      |aq0 rl0 base0 ts0 rvs0 wvs0 kc0 Hnn0 Hlen0 Hrd Hlt Hlb0
                         Hσ']; simplify_eq/=.
    (* --- the configuration after the exclusive read --- *)
    set W1 := exload_post_run_d (pa_ws ag) aq (srcs_view (pa_ws ag) asrc1)
                base tvs.*1.
    set ag1 := WPAgent pm W1 (pa_prom ag).
    set c1 := WPCfg (pc_img c) (pc_log c) dm (<[i := ag1]> (pc_ags c)).
    have Hro : read_ok (pc_img c) (pc_log c) (pa_ws ag) aq false base tvs.
    { eapply ws_eqr_read_ok; [exact Hew|].
      rewrite -(zip_fst_snd tvs). by apply rd_ok_read_ok. }
    have Hstep1 : wp_pf_step pstep pcls i (LExLoad aq base tvs asrc1) c c1
      by apply (PFExLoad pstep pcls i c ag aq base tvs asrc1 pm dm).
    have Hlk1 : pc_ags c1 !! i = Some ag1
      by rewrite /c1 /= list_lookup_insert.
    (* --- the intra-pair administrative star.  NOTE there is no
       [cfg_eqr c c1]: the exclusive read is a MEMORY step, and agent [i]'s
       views have genuinely moved.  What survives across the pair is
       [cfg_eqr c1 c2] (the star's own move) plus the fact that the star
       touched no OTHER agent. --- *)
    destruct (adm_star_pf false c1 i ag1 pm2 dm2 Hlk1
                ltac:(rewrite /ag1 /c1 /=; exact Hstar))
      as (c2 & ag2 & Hrun2 & Heq2 & Hd2 & Hlk2 & Hs2 & Hw2 & Hr2 & Hfm2).
    have Hres2 : w_res (pa_ws ag2)
               = Some (WResv base tvs.*1
                         (ldv_of (pa_ws ag) aq 0%nat base tvs.*1)).
    { rewrite (Hr2 eq_refl) /ag1 /W1. apply exload_post_run_d_res. }
    have Himg2 : pc_img c2 = pc_img c by apply Heq2.
    have Hlog2 : pc_log c2 = pc_log c by apply Heq2.
    have Hoth : ∀ j agj, j ≠ i → pc_ags c2 !! j = Some agj →
                  ws_eqr (f j) (pa_ws agj).
    { intros j agj Hne Hj. destruct Heq2 as (_ & _ & Ha).
      destruct (Ha j agj Hj) as (agj1 & Hj1 & He1).
      rewrite /c1 /= list_lookup_insert_ne // in Hj1.
      etrans; [by apply Hf|exact He1]. }
    (* --- the wstate the class is read at --- *)
    have Hwm : ws_eqr (load_post_run (f i) aq base tvs.*1) (pa_ws ag2).
    { etrans; [|exact Hw2]. rewrite /ag1 /W1.
      by apply ws_eqr_exload_post_run_d. }
    have Hk : pcls pm2 (LExStore rl base data asrc2 vsrc2)
                (load_post_run (f i) aq base tvs.*1)
            = pcls (pa_st ag2) (LExStore rl base data asrc2 vsrc2) (pa_ws ag2)
      by rewrite Hs2; apply Hce.
    (* --- the conditional write --- *)
    eexists. split_and!.
    - eapply rtc_r; [eapply rtc_l; [|exact Hrun2]|].
      + by exists i, (LExLoad aq base tvs asrc1).
      + exists i, (LExStore rl base data asrc2 vsrc2).
        apply (PFExStore pstep pcls i c2 ag2 rl base data asrc2 vsrc2
                 (pcls (pa_st ag2) (LExStore rl base data asrc2 vsrc2)
                    (pa_ws ag2))
                 (WResv base tvs.*1 (ldv_of (pa_ws ag) aq 0%nat base tvs.*1))
                 p' dn); [done| |done|done|done| | |reflexivity].
        * rewrite Hs2 Hd2. exact Hps2.
        * cbn [rv_ts]. rewrite length_fmap. lia.
        * cbn [rv_ts]. rewrite Hlog2.
          by apply (rmw_latest_excl_ok_ts (pc_img c)).
    - simpl. rewrite Hlog2 Himg2 -Hk.
      eapply (cfg_matchd_upd_gen _ _ _ _ i ag2 p' _ _
                (upd_ws f i (pa_ws ag2))
                (upd_ws f i (store_post_run (load_post_run (f i) aq base tvs.*1)
                               rl base (length data) (S (length (pc_log c)))))).
      + intros j agj Hj. destruct (decide (j = i)) as [->|Hne].
        * rewrite Hlk2 in Hj. simplify_eq. rewrite upd_ws_eq. reflexivity.
        * rewrite upd_ws_ne //. by apply Hoth.
      + exact Hlk2.
      + rewrite upd_ws_eq.
        apply ws_eqr_store_post_run_d. exact Hwm.
      + intros j Hne. by rewrite !upd_ws_ne.
    - simpl. rewrite list_fmap_insert Hfm2 /c1 /ag1 /= list_fmap_insert
                    !list_insert_insert //.
    - done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (6) The replay

      Note what is NOT a premise any more: the agent-range side condition
      ([es_ag s < length ps]) is implied by [exec_prog_ok']'s own lookup,
      and [exec_cls_ok] is absorbed into [lbl_realizes]. *)
  Lemma exec_prefix_pf_run_prog pst dv E n :
    pcls_eqr pcls →
    exec_wf E → exec_prog_ok' pst dv E →
    (n ≤ length (ex_tr E))%nat →
    ∃ c, rtc (wp_pf_run pstep pcls)
             (wp_init (ex_img E) (dv 0%nat) (pst 0%nat)) c ∧
         pa_st <$> pc_ags c = pst n ∧ pc_dev c = dv n ∧
         cfg_matchd c (stt E n).
  Proof.
    intros Hce HE Hpr. induction n as [|n IH]; intros Hn.
    - exists (wp_init (ex_img E) (dv 0%nat) (pst 0%nat)). split_and!.
      + done.
      + rewrite /wp_init /=. rewrite -list_fmap_compose.
        by apply list_fmap_id.
      + done.
      + split_and!.
        * done.
        * by apply (exec_log_init E HE).
        * intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
          destruct (pst 0%nat !! i) as [p|]; simplify_eq/=.
          have Hw0 : ms_ws (stt E 0%nat) i = ws_init
            by apply (exec_ws_init E i HE).
          rewrite Hw0. reflexivity.
    - destruct (IH ltac:(lia)) as (c & Hrun & Hst & Hdev & Hm).
      destruct (exec_tr_lookup E n ltac:(lia)) as [s Hs].
      pose proof (exec_step_at E n s HE Hs) as Hms.
      destruct (Hpr n s Hs) as (p & pa & da & p' & Hp & Hnext & Hstar & Hsup).
      have Hex : ∃ ag, pc_ags c !! es_ag s = Some ag ∧ pa_st ag = p.
      { rewrite -Hst list_lookup_fmap in Hp.
        destruct (pc_ags c !! es_ag s) as [ag|] eqn:Hag; simplify_eq/=.
        by exists ag. }
      destruct Hex as (ag & Hag & Hagp).
      (* the leading administrative star *)
      destruct (adm_star_pf true c (es_ag s) ag pa da Hag
                  ltac:(rewrite Hagp Hdev; exact Hstar))
        as (c0 & ag0 & Hrun0 & Heq0 & Hd0 & Hlk0 & Hs0 & _ & _ & Hfm0).
      have Hm0 : cfg_matchd c0 (stt E n) by eapply cfg_eqr_matchd.
      destruct Hsup as [(l & Hre & Hps)|
                        (pm & dm & pm2 & dm2 & l1 & l2 & Hre & Hps1 & Hstar2 &
                         Hps2)].
      + destruct (mstep_wp_pf_step_prog (stt E n) (stt E (S n)) (es_ag s)
                    (es_lb s) c0 ag0 pa p' l (dv (S n)) Hce Hm0 Hlk0 Hs0 Hre
                    ltac:(rewrite Hd0; exact Hps) Hms)
          as (c2 & Hstep & Hm2 & Hst2 & Hdev2).
        exists c2. split_and!.
        * eapply rtc_r; [by etrans|]. by exists (es_ag s), l.
        * rewrite Hst2 Hfm0 Hst list_insert_insert -Hnext //.
        * done.
        * done.
      + destruct (mstep_wp_pf_step_pair (stt E n) (stt E (S n)) (es_ag s)
                    (es_lb s) c0 ag0 pa pm pm2 p' l1 l2 dm dm2 (dv (S n))
                    Hce Hm0 Hlk0 Hs0 Hre ltac:(rewrite Hd0; exact Hps1)
                    Hstar2 Hps2 Hms)
          as (c2 & Hstep & Hm2 & Hst2 & Hdev2).
        exists c2. split_and!.
        * etrans; [by etrans|exact Hstep].
        * rewrite Hst2 Hfm0 Hst list_insert_insert -Hnext //.
        * done.
        * done.
  Qed.

  (** THE PROGRAM-CARRYING REVERSE BRIDGE.  Every [exec_wf] execution whose
      trace is carried by a run of the given program LTS is the projection
      of a promise-free run of the full machine — at the program states, the
      fabric states and the labels that run supplies, and with the SAME LOG
      ([cfg_matchd]'s second conjunct). *)
  Theorem exec_wf_pf_run_prog pst dv E :
    pcls_eqr pcls →
    exec_wf E → exec_prog_ok' pst dv E →
    ∃ c, rtc (wp_pf_run pstep pcls)
             (wp_init (ex_img E) (dv 0%nat) (pst 0%nat)) c ∧
         pa_st <$> pc_ags c = pst (length (ex_tr E)) ∧
         pc_dev c = dv (length (ex_tr E)) ∧
         cfg_matchd c (stt E (length (ex_tr E))).
  Proof.
    intros Hce HE Hpr.
    destruct (exec_prefix_pf_run_prog pst dv E (length (ex_tr E)) Hce HE Hpr
                ltac:(lia)) as (c & ? & ? & ? & ?).
    by exists c.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (7) The [prog_free] forms are corollaries

      [prog_free] supplies the trivial assignment: every agent keeps its
      initial program state ([<[i := p]> ps = ps] when [ps !! i = Some p]),
      the fabric never moves, the star is empty, and the label is the
      canonical one, whose class premise is exactly what [exec_cls_ok]
      states.

      THESE ARE THE [cfg_matchd] SHADOWS of
      [WeakPromiseBridge.exec_prefix_pf_run] / [.exec_wf_pf_run], not
      replacements for them (T1-D finding): at the real label alphabet the
      machine's per-agent [wstate] is [ws_eqr]-related to the axiomatic one,
      not equal to it, so this file's induction can only conclude
      [cfg_matchd].  The bridge's own [cfg_match] statements therefore stay
      where they are. *)
  Lemma prog_free_exec_prog_ok ps d0 E :
    prog_free pstep → exec_wf E → exec_cls_ok pcls ps E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    exec_prog_ok (λ _, ps) (λ _, d0) E.
  Proof.
    intros Hpf HE Hck Hag. apply exec_prog_ok_single. intros k s Hs.
    destruct (lookup_lt_is_Some_2 ps (es_ag s) (Hag k s Hs)) as [p Hp].
    exists p, p, (unproj_lbl (es_lb s)). split_and!.
    - done.
    - eapply (lbl_realizes_intro p (stt E k) (stt E (S k)));
        [by eapply exec_step_at|by eapply Hck].
    - apply Hpf.
    - by rewrite list_insert_id.
  Qed.

  Lemma exec_prefix_pf_run_pf ps d0 E n :
    pcls_eqr pcls →
    prog_free pstep → exec_wf E → exec_cls_ok pcls ps E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    (n ≤ length (ex_tr E))%nat →
    ∃ c, rtc (wp_pf_run pstep pcls) (wp_init (ex_img E) d0 ps) c ∧
         length (pc_ags c) = length ps ∧ pa_st <$> pc_ags c = ps ∧
         cfg_matchd c (stt E n).
  Proof.
    intros Hce Hpf HE Hck Hag Hn.
    destruct (exec_prefix_pf_run_prog (λ _, ps) (λ _, d0) E n Hce HE
                (exec_prog_ok_star _ _ _
                   (prog_free_exec_prog_ok ps d0 E Hpf HE Hck Hag)) Hn)
      as (c & Hrun & Hst & _ & Hm).
    exists c. split_and!; [done| |done|done].
    by rewrite -Hst length_fmap.
  Qed.

  Theorem exec_wf_pf_run_pf ps d0 E :
    pcls_eqr pcls →
    prog_free pstep → exec_wf E → exec_cls_ok pcls ps E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    ∃ c, rtc (wp_pf_run pstep pcls) (wp_init (ex_img E) d0 ps) c ∧
         cfg_matchd c (stt E (length (ex_tr E))).
  Proof.
    intros Hce Hpf HE Hck Hag.
    destruct (exec_prefix_pf_run_pf ps d0 E (length (ex_tr E)) Hce Hpf HE Hck
                Hag ltac:(lia)) as (c & ? & _ & _ & ?).
    by exists c.
  Qed.

End realize.

Global Arguments lbl_realizes {P} _ _ _ _ _ _.
Global Arguments lbl_realizes_pair {P} _ _ _ _ _ _ _ _.
Global Arguments adm_step {P D} _ _ _ _.
Global Arguments adm_star {P D} _ _ _ _ _ _.
Global Arguments exec_prog_ok {P D} _ _ _ _.
Global Arguments exec_prog_ok' {P D} _ _ _ _.
