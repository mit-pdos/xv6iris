(** * WeakCompose.v — M6 W5: THE COMPOSITION

    This is the last build step of the M6 effort.  Everything above it is
    machine-checked: [WeakRobustMain.robust_main] is the assembled Layer-1
    robustness theorem over an ABSTRACT per-agent program LTS, and
    [WeakSailLTS] is the instantiation of that parameter at the real Sail
    event-level machine.  This file does the honest assembly:

    (a) the MULTI-AGENT program type [pxv6] — harts run [WeakSailLTS.psail],
        the disk is ONE MORE AGENT of the same LTS (D-M6-4) — with its two
        Layer-1 side conditions ([xv6_lat_free], [xv6_ts_oblivious]) proved
        from [WeakSailLTS]'s theorems plus the trivial disk arms; the DECLARED
        premise bundle [m6_side_conditions] (D-M6-8's package, ONE named
        definition); and THE HEADLINE THEOREM [xv6_weak_robust] — literally
        [robust_main] applied — plus the completable-prefix corollary
        [xv6_weak_robust_prefix] via [robust_transport];

    (b) the pf-side bridge to the real machine: the FRAME lemmas
        ([pf_step_frame], [pf_run_frame]) that embed a [psail]-typed pf run
        into the [pxv6]-typed multi-agent configuration with the other agents
        (in particular the disk) untouched, and [xv6_pf_instr] — one whole
        [wrun] instruction of hart [i] is a [wp_pf_run] sequence of the
        n-agent configuration.  This is the ⇒ half of the WeakLang
        correspondence at the wp level;

    (c) THE SEAM RECORD (the closing comment block): exactly what remains
        DECLARED between [xv6_weak_robust] and [WeakAdequacy]'s
        [weak_system_adequacy], each with its justification and upgrade path.

    NO [Axiom], NO [Admitted].  Every remaining seam is a hypothesis of a
    theorem or a definition whose discharge is named in the seam record.

    ------------------------------------------------------------------------
    DESIGN DELTAS (deliberate; read before extending).

    (i) THE DISK AGENT SIMULATES [WeakLang.wdisk_step] (THE SUPERSET IS
        RETIRED — L0(d) of the lift plan, 2026-08-12).  Its program state is
        [DevModel.dev_state] together with the RESIDUAL MESSAGE BURST of the
        DMA step in flight, and its LTS has exactly two moving arms: a silent
        BURST step, which takes one [WeakLang.wdisk_step] and loads
        [WeakLang.wmsgs_of_map w] into the burst buffer, and an EMIT step,
        which turns the head buffered message into its own
        [LStore false (wm_pa m) (wm_data m)].  So ONE [WeakLang] disk arm is
        [1 + |w|] steps here — the lift's disk arm maps 1:1 — and no store
        the real DMA cannot make is admitted any more.  (Previously the arm
        admitted ANY nonempty non-release store at any time, which was honest
        but strengthened the declared premise [m6_side_conditions] over
        behaviors the real disk has not got.)

        THE ONE RESIDUE, and it is the M5 device-view seam (4), not a new
        one: [wdisk_step] reads the FLAT MEMORY, which a [wpcfg] does not
        carry (its memory is the log).  The burst arm therefore quantifies
        the memory argument EXISTENTIALLY — "some flat memory would have
        produced this write set".  Pinning it to [wflat (pc_img c)
        (pc_log c)] needs the disk's own view, which is exactly what M5
        adds.

    (ii) THE TID DELTA IS GONE (L0(a) of the lift plan, 2026-08-12).
        [WeakLang.wmsgs_of_map] now stamps [wm_tid = Some WeakLang.n_disk]
        with [n_disk = NCPU], which is precisely the disk's index in
        [xv6_ps] below (harts occupy [0 .. NCPU-1]), so the two machines
        stamp the SAME tid on the same message and the old [None ↦ Some
        n_disk] renaming of seam (1d) has no content left.  What the
        unification buys downstream is that "the author is a hart" is a
        uniform test on BOTH sides: [WeakGhost]'s C/D/S invariants exempt
        every non-hart author, and [WeakRobustMain.bad] carries the matching
        [e1.1 < nh] conjunct, instantiated here at [WeakLang.n_disk].

    (iii) THE FRAME IS AT THE PROGRAM-TYPE LEVEL, not at the agent-list level.
        [WeakSailLTS.sail_instr_bracket] is ALREADY stated over an arbitrary
        agent list with slot [i] pinned and every other slot framed, so the
        agent-list framing the task calls for is already delivered there.
        What this file adds is the [psail ↪ pxv6] embedding: [lift_cfg dks]
        maps a [psail] configuration to the [pxv6] configuration whose agents
        are the lifted harts followed by the framed extra agents [dks] (the
        disk).  Harts therefore occupy indices [0 .. n-1] and the disk index
        [n]; that layout is what keeps agent indices — and hence every
        [wm_tid] in the log — stable under the embedding.

    (iv) [m6_side_conditions] QUANTIFIES OVER THE BEHAVIOR.  [robust_main]
        fixes [c] and asks for [main_premises] of every traced bundle of that
        [c]; [robust_transport] quantifies over the completion [cend].  One
        definition serving both takes the [robust_transport] shape (the [c]
        binder inside), and [xv6_weak_robust] is then [robust_main] applied to
        [λ mid TS, Hprem c mid TS Hbeh] — i.e. literally [robust_main], with
        the behavior binder instantiated.

    DEPENDENCIES: the whole Layer-1 stack ([WeakRobustMain] and its parents),
    the Sail LTS ([WeakSailLTS], hence [WeakInterp] and the rv64d model), and
    [RiscvLang] for [riscv_step].  NOT imported: [WeakLang] / [WeakAdequacy] —
    the correspondence to [wprim_step]/[erased_step] is seam (1), stated in
    the record below and deliberately NOT half-built here.

    NOTE ON NAMES: [WeakPromise] and [WeakAxiomatic] both export
    [LLoad]/[LStore]/[LFence]/[LRmw]; every occurrence below is QUALIFIED
    [WeakPromise.LLoad] &c. even where the ambient import order would make it
    unambiguous. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.
From xv6iris Require Import WeakRobust WeakRobustTrace WeakRobustSim WeakRobustMain.
From xv6iris Require Import WeakInterp WeakSailLTS.
Require Import RiscvLang.
(* L0(d): the disk arm is now [WeakLang.wdisk_step]-shaped, and L0(a) fixes
   the DMA tid at [WeakLang.n_disk] — so this file DOES import [WeakLang]
   for those two definitions.  It still does NOT build the [wprim_step] ⇔
   [wp_pf_run] correspondence (seam (1)); [WeakAdequacy] stays out. *)
Require Import WeakLang.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The multi-agent xv6 program

    D-M6-4: M6 is stated over the harts PLUS the one disk agent, as one more
    agent of the same LTS.  A hart's program state is [WeakSailLTS.psail] (the
    residual instruction monad, the register file, the MMIO oracle stream and
    the parked second fence of a [fence.tso]); the disk's is [unit] — delta
    (i) above explains why, and what it costs. *)

Inductive pxv6 :=
| PHart (p : psail)
| PDisk (d : dev_state) (pend : list wmsg).

(** The step relation.  The hart arm is [WeakSailLTS.sail_step] verbatim; the
    disk arm SIMULATES [WeakLang.wdisk_step] per delta (i) — a silent BURST
    that advances the device fabric and buffers the DMA write set as the very
    messages [WeakLang.wmsgs_of_map] would append, then one EMIT per buffered
    message.  A stutter arm keeps the agent reducible with an empty log
    effect (the [WDiskStepIdle] / not-live cases of [WeakLang]).  An agent
    never changes species, so mismatched constructors are stuck.

    THE MEMORY ARGUMENT IS EXISTENTIAL — see delta (i): a [wpcfg] has no flat
    memory to feed [wdisk_step], and pinning it is M5's device-view work. *)
Definition pstep_xv6 (next : bool → M unit)
    (p : pxv6) (l : wlabel) (p' : pxv6) : Prop :=
  match p, p' with
  | PHart q, PHart q' => sail_step next q l q'
  | PDisk d pend, PDisk d' pend' =>
      (* silent: stutter, or one [wdisk_step] loading the burst buffer *)
      (l = WeakPromise.LSilent ∧
       ((d' = d ∧ pend' = pend) ∨
        (pend = [] ∧ ∃ mem w, wdisk_step d mem d' w ∧
                              pend' = wmsgs_of_map w)))
      ∨
      (* emit: the head buffered message becomes this agent's own store *)
      (∃ (m : wmsg) (rest : list wmsg),
         pend = m :: rest ∧ pend' = rest ∧ d' = d ∧
         l = WeakPromise.LStore false (wm_pa m) (wm_data m))
  | _, _ => False
  end.

(** The standard xv6 agent vector: [n] harts at indices [0 .. n-1], the disk
    at index [n], starting from the device fabric [d0] with an empty burst
    buffer.  Keeping the harts at a prefix is what makes the framing of §5
    index-stable — AND, at [n = NCPU], what makes the disk's index equal
    [WeakLang.n_disk], which is the tid [WeakLang.wmsgs_of_map] stamps
    (delta (ii)) and the hart bound [m6_side_conditions] passes to
    [main_premises]. *)
Definition xv6_ps (d0 : dev_state) (hs : list psail) : list pxv6 :=
  (PHart <$> hs) ++ [PDisk d0 []].

(* ====================================================================== *)
(** ** 2. The two Layer-1 side conditions

    Both are [WeakSailLTS]'s theorems on the hart arm plus a one-line
    refutation on the disk arm (which emits no load and no rmw at all). *)

(** THE FABRIC MARKER OF THIS (ARCHIVED, per-hart-stream) INSTANCE: the
    program never touches the shared fabric — [pstep_xv6] carries the
    device state PER AGENT ([psail]'s [sp_dev]), which is exactly the
    modelling debt the G-series fixes on the EVENT language.  So the
    marker is constantly false and Layer 1's device machinery collapses:
    the witness of every run is empty. *)
Definition xv6_pdev : pxv6 → wlabel → pxv6 → bool := λ _ _ _, false.

Lemma xv6_pdev_false : ∀ p l p', xv6_pdev p l p' = false.
Proof. done. Qed.

Lemma xv6_pdev_ok next :
  pdev_ok (pstep_unit (pstep_xv6 next)) xv6_pdev.
Proof. intros p d l p' d' Hs _. split; [by destruct d, d'|done]. Qed.

(** LAT-FREEDOM — the hypothesis [WeakPromiseFact]'s front-loading
    factorization takes, and hence [robust_main]. *)
Theorem xv6_lat_free next : lat_free_prog (pstep_unit (pstep_xv6 next)).
Proof.
  intros p d0 aq base tvs p' d0' H.
  destruct p as [q|d pend], p' as [q'|d' pend']; simpl in H;
    try (exfalso; exact H).
  - exact (sail_lat_free next q d0 aq base tvs q' d0' H).
  - destruct H as [(Hc & _)|(? & ? & _ & _ & _ & Hc)]; discriminate.
Qed.

(** TIMESTAMP-OBLIVIOUSNESS — worklist finding (v): the pf witness steps the
    program with π-retimed labels, so [robust_main] is only true of programs
    that see VALUES and never timestamps.  [sail_ts_oblivious] and
    [sail_ts_oblivious_rmw] assemble LITERALLY into the conjunction
    [WeakRobustSim.ts_oblivious] asks for. *)
Theorem xv6_ts_oblivious next : ts_oblivious (pstep_unit (pstep_xv6 next)).
Proof.
  split.
  - intros p dv aq lat base tvs tvs' p' dv' Heq H.
    destruct p as [q|d pend], p' as [q'|d' pend']; simpl in H |- *;
      try (exfalso; exact H).
    + exact (sail_ts_oblivious next q aq lat base tvs tvs' q' Heq H).
    + destruct H as [(Hc & _)|(? & ? & _ & _ & _ & Hc)]; discriminate.
  - intros p dv aq rl base tvs tvs' data p' dv' Heq H.
    destruct p as [q|d pend], p' as [q'|d' pend']; simpl in H |- *;
      try (exfalso; exact H).
    + exact (sail_ts_oblivious_rmw next q aq rl base tvs tvs' data q' Heq H).
    + destruct H as [(Hc & _)|(? & ? & _ & _ & _ & Hc)]; discriminate.
Qed.

(* ====================================================================== *)
(** ** 3. THE DECLARED PREMISE BUNDLE (D-M6-8's package)

    ONE named definition, so that the exact content of what M6 declares is a
    single auditable object.  Two conjuncts:

    - THE PER-BUNDLE STATIC SIDE CONDITIONS.  For every full-machine behavior
      [c] of the program and every traced factorization of it (a promise phase
      reaching [mid], then per-agent state phases recorded as [TS]),
      [WeakRobustMain.main_premises TS] holds.  Unfolded, that is
      [edges_split TS] (every cross rf edge is discipline-ok OR [bad] — the
      shape φ refutes), [bad_wf TS] (no "bad SCC": whenever a bad edge exists,
      some bad edge has bad-target-free strict ancestry), [ee_ok TS] (W2b's
      E-edge obligation: fence-cover, waw-cover, or an empty floor), and the
      byte classification [∃ sync, ptraces_bytes_ok TS sync] (W2b's
      write-serialization premise).  D-M6-8 splits this content three ways —
      machine-side facts, value-independent SITE facts, and the residue of
      positions po-after an unsupported read — and DECIDES that the residue is
      carried as an explicit, per-site-checkable static condition on the kernel
      image.  A checker tool over the enumerated racy/release sites is the
      recorded upgrade path.

    - [pf_violation_free_hart cls_of pub_of n_disk]: no promise-free run of
      the program reaches a configuration in which a foreign HART's coherence
      floor has reached an OWNED-UNPUBLISHED message of a HART author.  This
      is the ONE place φ/Iris remains load-bearing (W3's rescoping: the
      conjunct is deferred, and the ↦w transfer-discipline rework is its
      upgrade path).  It is instantiated at the MACHINE-SYNTACTIC [cls_of]
      (read off the message's inert [wm_ak]) and [pub_of] (the log predicate
      [WeakMem.wpublished]), so it is sharply checkable and Iris-refinable
      later.

      BOTH AGENTS ARE HART-RESTRICTED, at the bound [n_disk = NCPU] that the
      first conjunct already passes to [main_premises].  The unrestricted
      [pf_violation_free] would be REFUTABLE here rather than merely
      undischarged: with the DMA-tid unification the disk is an ordinary
      agent, so a hart reading DMA'd bytes is a [violation] with the disk as
      AUTHOR, and a DMA over plainly-written hart bytes is one with the disk
      as OBSERVER — neither is anything φ (a statement about harts) can say
      a word about.  See [WeakRobust.violation_hart]; the exhibit
      ([WeakRobustMain.bad_edge_violates]) produces exactly the restricted
      form, because [bad] bounds both ends of its edge. *)
Definition m6_side_conditions (next : bool → M unit) (img : image)
    (ps : list pxv6) : Prop :=
  (∀ (c mid : wpcfg pxv6 unit) (TS : ptraces pxv6 unit) (DS : pdevs unit),
     wp_behavior (pstep_unit (pstep_xv6 next)) img tt ps c →
     rtc (wp_promise_step (P := pxv6) (D := unit)) (wp_init img tt ps) mid →
     ptraces_dev_of (pstep_unit (pstep_xv6 next)) xv6_pdev TS DS mid c →
     main_premises n_disk TS DS)
  ∧ pf_violation_free_hart cls_of pub_of n_disk (pstep_unit (pstep_xv6 next)) img tt ps.

(* ====================================================================== *)
(** ** 4. THE HEADLINE THEOREM

    Every full-machine BEHAVIOR of the xv6 agent vector — a run of the
    promising machine (harts + disk, promises and all) that has drained every
    promise — is matched by a PROMISE-FREE run with the same per-agent program
    states and the same flat memory.  The promise-free machine is thereby
    visibly scaffolding: it is where the Iris program logic lives, and this
    theorem says nothing observable is lost by working there.

    The store-reordering assumption is RETIRED into: this theorem, plus
    [m6_side_conditions], plus the D-M6-3 correspondence note at the PARM
    seam, plus the seams recorded in §6. *)
Theorem xv6_weak_robust (next : bool → M unit) (img : image) (ps : list pxv6)
    (c : wpcfg pxv6 unit) :
  m6_side_conditions next img ps →
  wp_behavior (pstep_unit (pstep_xv6 next)) img tt ps c →
  ∃ cf, rtc (wp_pf_run (pstep_unit (pstep_xv6 next))) (wp_init img tt ps) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros [Hprem Hvf] Hbeh.
  apply (robust_main (pstep_unit (pstep_xv6 next)) xv6_pdev n_disk img tt ps c
           (xv6_pdev_ok next)
           (xv6_lat_free next) (xv6_ts_oblivious next) Hbeh
           (λ mid TS DS, Hprem c mid TS DS Hbeh) Hvf).
Qed.

(** W2c's COMPLETABLE-PREFIX form — the shape the adequacy composition wants,
    because the full machine is never [wpstep]-stuck: a reachable prefix that
    can still drain its promises has a completion whose observables a
    promise-free run reproduces. *)
Corollary xv6_weak_robust_prefix (next : bool → M unit) (img : image)
    (ps : list pxv6) (c : wpcfg pxv6 unit) :
  m6_side_conditions next img ps →
  completable (pstep_unit (pstep_xv6 next)) img tt ps c →
  ∃ cend cf,
    rtc (wpstep (pstep_unit (pstep_xv6 next))) c cend ∧ no_promises cend ∧
    rtc (wp_pf_run (pstep_unit (pstep_xv6 next))) (wp_init img tt ps) cf ∧
    prog_of cf = prog_of cend ∧ (∀ a, mem_of cf a = mem_of cend a).
Proof.
  intros [Hprem Hvf] Hc.
  apply (robust_transport (pstep_unit (pstep_xv6 next)) xv6_pdev n_disk img tt
           ps c (xv6_pdev_ok next)
           (xv6_lat_free next) (xv6_ts_oblivious next) Hc Hprem Hvf).
Qed.

(* ====================================================================== *)
(** ** 5. The pf-side bridge to the real machine

    [WeakSailLTS.sail_instr_bracket] already brackets ONE [WeakInterp.wrun]
    instruction of hart [i] into an [rtc (wp_pf_run (pstep_unit (sail_step riscv_step)))]
    of the one stepping agent, with every OTHER agent of the list framed.  Two
    things are missing for the composition, and both are here:

    - the PROGRAM-TYPE embedding [psail ↪ pxv6] (delta (iii)): a pf run of the
      [psail]-typed machine is a pf run of the [pxv6]-typed machine on the
      configuration whose agents are the lifted harts followed by any extra
      agents [dks] — the disk — which the run never touches;
    - the resulting whole-instruction corollary [xv6_pf_instr] on the n-agent
      configuration.

    The frame lemma is proved DIRECTLY from [wp_pf_step]'s five arms, exactly
    as [WeakPromiseFact.wp_astep_frame] does at the astep layer: every arm
    reads agent [i] and the log, and writes agent [i] (by [insert]) and the
    log (by [app]).  Nothing else in the configuration is mentioned, which is
    the whole content of the framing. *)

Definition lift_ag (a : wpagent psail) : wpagent pxv6 :=
  WPAgent (PHart (pa_st a)) (pa_ws a) (pa_prom a).

(** The embedding: same image, same log, harts lifted at the same indices,
    [dks] appended (and framed). *)
Definition lift_cfg (dks : list (wpagent pxv6)) (c : wpcfg psail unit) : wpcfg pxv6 unit :=
  WPCfgU (pc_img c) (pc_log c) ((lift_ag <$> pc_ags c) ++ dks).

Lemma lift_ags_lookup dks ags i ag :
  ags !! i = Some ag → ((lift_ag <$> ags) ++ dks) !! i = Some (lift_ag ag).
Proof.
  intros H. rewrite lookup_app_l.
  - by rewrite list_lookup_fmap H.
  - rewrite length_fmap. exact (lookup_lt_Some _ _ _ H).
Qed.

Lemma lift_ags_insert dks ags i a :
  (i < length ags)%nat →
  (lift_ag <$> <[i := a]> ags) ++ dks
  = <[i := lift_ag a]> ((lift_ag <$> ags) ++ dks).
Proof.
  intros Hi. rewrite list_fmap_insert insert_app_l.
  - reflexivity.
  - by rewrite length_fmap.
Qed.

(** THE FRAME LEMMA, one pf step. *)
Lemma pf_step_frame (next : bool → M unit) (dks : list (wpagent pxv6))
    (i : agent) (l : wlabel) (c c' : wpcfg psail unit) :
  wp_pf_step (pstep_unit (sail_step next)) i l c c' →
  wp_pf_step (pstep_unit (pstep_xv6 next)) i l (lift_cfg dks c) (lift_cfg dks c').
Proof.
  intros Hst.
  destruct Hst as
    [cfg ag st' dd Hag Hps
    |cfg ag aq lat base tvs st' dd Hag Hps Hok
    |cfg ag rl base data k st' dd Hag Hps Hne
    |cfg ag aq rl base tvs data k st' dd Hag Hps Hne Hlen Hok Hex
    |cfg ag pr pw sr sw st' dd Hag Hps]; destruct dd;
    (have Hlt : (i < length (pc_ags cfg))%nat
       by exact (lookup_lt_Some _ _ _ Hag));
    (have Hlk := lift_ags_lookup dks (pc_ags cfg) i ag Hag);
    rewrite /lift_cfg; cbn [pc_img pc_log pc_ags];
    rewrite (lift_ags_insert dks (pc_ags cfg) i _ Hlt).
  - exact (PFSilent (pstep_unit (pstep_xv6 next)) i
             (WPCfgU (pc_img cfg) (pc_log cfg) ((lift_ag <$> pc_ags cfg) ++ dks))
             (lift_ag ag) (PHart st') tt Hlk Hps).
  - exact (PFLoad (pstep_unit (pstep_xv6 next)) i
             (WPCfgU (pc_img cfg) (pc_log cfg) ((lift_ag <$> pc_ags cfg) ++ dks))
             (lift_ag ag) aq lat base tvs (PHart st') tt Hlk Hps Hok).
  - exact (PFStore (pstep_unit (pstep_xv6 next)) i
             (WPCfgU (pc_img cfg) (pc_log cfg) ((lift_ag <$> pc_ags cfg) ++ dks))
             (lift_ag ag) rl base data k (PHart st') tt Hlk Hps Hne).
  - exact (PFRmw (pstep_unit (pstep_xv6 next)) i
             (WPCfgU (pc_img cfg) (pc_log cfg) ((lift_ag <$> pc_ags cfg) ++ dks))
             (lift_ag ag) aq rl base tvs data k (PHart st') tt
             Hlk Hps Hne Hlen Hok Hex).
  - exact (PFFence (pstep_unit (pstep_xv6 next)) i
             (WPCfgU (pc_img cfg) (pc_log cfg) ((lift_ag <$> pc_ags cfg) ++ dks))
             (lift_ag ag) pr pw sr sw (PHart st') tt Hlk Hps).
Qed.

(** …and the run-level form: a whole [psail] pf run embeds, the framed agents
    untouched throughout. *)
Lemma pf_run_frame (next : bool → M unit) (dks : list (wpagent pxv6))
    (c c' : wpcfg psail unit) :
  rtc (wp_pf_run (pstep_unit (sail_step next))) c c' →
  rtc (wp_pf_run (pstep_unit (pstep_xv6 next))) (lift_cfg dks c) (lift_cfg dks c').
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  destruct Hxy as (i & l & Hst).
  eapply rtc_l; [|exact IH]. exists i, l. by apply pf_step_frame.
Qed.

(** The initial configuration of the xv6 agent vector IS the embedding of the
    harts' initial configuration with the disk framed — so the frame lemmas
    apply from [wp_init] onwards. *)
Definition xv6_disk_agent (d0 : dev_state) : wpagent pxv6 :=
  WPAgent (PDisk d0 []) ws_init ∅.

Lemma wp_init_xv6 img d0 hs :
  wp_init img tt (xv6_ps d0 hs)
  = lift_cfg [xv6_disk_agent d0] (wp_init (P := psail) (D := unit) img tt hs).
Proof.
  rewrite /xv6_ps /lift_cfg /wp_init /xv6_disk_agent.
  cbn [pc_img pc_log pc_ags]. f_equal.
  induction hs as [|h hs IH]; simpl; [done|by rewrite IH].
Qed.

(** THE ⇒ HALF OF THE WEAKLANG CORRESPONDENCE, at the wp level.

    One whole instruction executed by hart [i] on the real machine — i.e. one
    [WeakInterp.wrun (Some i) (riscv_step tick)], which is EXACTLY what
    [WeakLang.wprim_step]'s hart arm runs against [whart_view g cpu] — is a
    [wp_pf_run] sequence of the n-agent [pxv6] configuration in which hart [i]
    sits at index [i], every other hart is framed, and the disk agents [dks]
    are framed.

    [sail_shaped] is the caller's obligation (rv64d facts, seam (6)).  The
    hart's DEVICE FABRIC ([WeakSailLTS] delta (b)) travels with the
    interpreter's: the agent starts at [wm_dev s] and lands at [wm_dev s'],
    so there is no oracle stream and nothing existential about it.  [iq] is the
    INTERRUPT ORACLE (delta (b') there), framed: one [wrun] instruction never
    consumes an entry, because delivery is its own silent LTS arm — which is
    exactly what makes [RiscvLang.plic_step]'s cross-hart register write
    expressible in the per-agent LTS (L0(b) of the lift plan). *)
Corollary xv6_pf_instr (i : agent) (tick : bool) (s : wmstate) (x : unit)
    (s' : wmstate) (dks : list (wpagent pxv6)) :
  sail_shaped (riscv_step tick) →
  wrun (Some i) (riscv_step tick) s x s' →
  ∀ (iq : istream) (prom : gset nat) (ags : list (wpagent psail)),
    ags !! i = Some (WPAgent (PSail None (wm_regs s) (wm_dev s) None iq)
                       (wm_ws s) prom) →
    rtc (wp_pf_run (pstep_unit (pstep_xv6 riscv_step)))
      (WPCfgU (wimg s) (wm_log s) ((lift_ag <$> ags) ++ dks))
      (WPCfgU (wimg s) (wm_log s')
         (<[i := WPAgent (PHart (PSail None (wm_regs s') (wm_dev s') None iq))
                   (wm_ws s') prom]> ((lift_ag <$> ags) ++ dks))).
Proof.
  intros Hsh Hrun.
  pose proof (sail_instr_bracket i tick s x s' Hsh Hrun) as Hch.
  intros iq prom ags Hlk.
  have Hlt : (i < length ags)%nat by exact (lookup_lt_Some _ _ _ Hlk).
  have Hr := pf_run_frame riscv_step dks _ _ (Hch iq prom ags Hlk).
  rewrite /lift_cfg in Hr. cbn [pc_img pc_log pc_ags] in Hr.
  rewrite (lift_ags_insert dks ags i _ Hlt) in Hr.
  exact Hr.
Qed.

(* ====================================================================== *)
(** ** 6. THE SEAM RECORD

    What follows is the complete, precise list of what remains DECLARED
    between [xv6_weak_robust] (above) and [WeakAdequacy.weak_system_adequacy]'s
    statement.  Nothing here is an [Axiom] in this development: each item is
    either a hypothesis of a theorem in this file, a definition whose
    discharge is named, or a statement whose composition step has not been
    built.  Each entry says WHAT is declared, WHY it is honest to declare it,
    and the UPGRADE PATH.

    ------------------------------------------------------------------------
    (1) THE MULTI-HART WEAKLANG ↔ WP-MACHINE CORRESPONDENCE RESIDUE.

    [weak_system_adequacy] speaks about [rtc erased_step] over
    [WeakLang.weak_riscv_lang], whose state is a [wgstate] (a shared image, a
    shared log, a per-CPU [wstate] function, a [dev_state], a generation and a
    power bit) and whose steps are [wprim_step]'s five arms (hart / uart /
    disk / plic / power).  [xv6_weak_robust] speaks about [wpcfg pxv6 unit] (a
    shared image, a shared log, a LIST of agents each carrying a [wstate], a
    program state and a promise set).

    DELIVERED by (b) above: the ⇒ direction for the HART arm.
    [wprim_step]'s hart arm is literally
      [wrun (Some (fin_to_nat cpu)) (riscv_step tick) (whart_view g cpu) u s']
      [∧ g' = whart_write g cpu s'],
    and [whart_view]/[whart_write] are exactly "read the shared image+log and
    hart [cpu]'s [wstate]" / "write back the log and hart [cpu]'s [wstate],
    leaving every other hart's [wstate] and the registers of every other hart
    alone" ([WeakLang.whart_view_img/_log/_ws], [whart_write_ws_ne],
    [whart_write_regs_ne]).  So [xv6_pf_instr] IS that arm's image under the
    correspondence, with the other harts framed at their own indices.

    CLOSED (the lift, stages L2/L3/B, 2026-08-12/13) — every sub-item is
    now machine-checked; the entries are kept for the record:
      (1a) the ⇐ direction — BUILT ([WeakSailLTS2.sail_block_wrun]): a
           boundary-to-boundary solo pf block IS a [wrun].  No determinism
           argument was needed after all — [silent_run] existentially
           contains the Choose values, so the inverse walks the block and
           supplies them.
      (1b) INTERLEAVING REGROUPING — BUILT, in the direction the
           φ-consumption needs ([WeakComposeLang]: the block-contiguous
           cone replay [WeakRobustCone]/[WeakSailCone] + [wl_lift]).  The
           naive reading of this entry ("bookkeeping, not mathematics")
           was WRONG: an arbitrary pf run does NOT regroup — see the
           [xv6_block_cover] refutability finding in [WeakComposeLang] §B
           — and the honest statement goes through the minimal-bad-edge
           cone, where cross-edge sources are block-last and the
           contracted block graph inherits acyclicity.
      (1c) THE DEVICE AND POWER ARMS — BUILT where needed: the plic arm
           is [wl_lift]'s [SegIrq] case, the disk arm its [SegDisk] case
           (1:1 by delta (i)); the uart arm has no wp-side agent and the
           power arm is vacuous at a pinned generation, so the produced
           WeakLang runs simply never take them (existence is all the
           consumption needs).  The per-era decomposition across reboots
           remains out of scope, as before: M6 is stated per-era.
      (1d) THE TID RENAMING — RESOLVED (L0(a), 2026-08-12), NOTHING IS
           DECLARED HERE ANY MORE.  [WeakLang.wmsgs_of_map] stamps
           [Some WeakLang.n_disk] with [n_disk = NCPU], which IS the disk's
           index in [xv6_ps], so the two machines agree on every message's
           [wm_tid] and no renaming happens at the seam.  What the
           unification replaced it with is a UNIFORM "the author is a hart"
           test on both sides: [WeakMem.tid_hart] / [WeakLang.tid_is_hart],
           spent by [WeakGhost.wcds_clean]/[wcds_dirty] (which exempt
           non-hart authors, because a device never publishes) and by
           [WeakRobustMain.bad]'s [e1.1 < nh] / [e2.1 < nh] conjuncts
           (instantiated at [n_disk] in [m6_side_conditions], and the reason
           its exhibit concludes [WeakRobust.violation_hart]).  Likewise the DISK ARM itself
           is now a simulation rather than a superset (delta (i)), so (1b)'s
           regrouping has a 1:1 disk case to work with.
    The carrier is [WeakComposeLang.v]; the residue that replaces this
    seam is the sharply-scoped premise family listed there (§D): the
    per-trace cone premises ([xv6_cone_premises]) and the per-segment
    device seam ([cone_liftable]), both in the same epistemic slot as
    (3)'s static side conditions and (4)'s MMIO assumption.

    ------------------------------------------------------------------------
    (2) [pf_violation_free_hart cls_of pub_of n_disk] — DECLARED (the second
    conjunct of [m6_side_conditions]).

    This is the Layer-2 premise: no promise-free run of the program reaches a
    configuration where some foreign HART's per-byte coherence floor has
    reached an owned ([wm_ak = WCplain]) message a HART author has not yet
    published.  PUBLICATION IS NOW THE LOG PREDICATE [WeakMem.wpublished]
    (L0(c), 2026-08-12): [WeakRobustMain.pub_of] no longer reads the author's
    [w_pub] watermark out of the agent vector, and the HART RESTRICTION
    (2026-08-12) closes the remaining gap.  Without the restriction the
    conjunct would be FALSE for xv6 (the disk as author or as observer; see
    §3), i.e. the theorem would be vacuous on every DMA-touching run.

    SUPERSEDED AS THE COMPOSITION'S ROUTE (stage B, 2026-08-13).  Even
    hart-restricted, this premise is NOT derivable from φ — and is
    REFUTABLE for kernels with the wrong code shape: at EVENT granularity
    a pf run can park an author mid-instruction between its walker A/D
    CAS and its release-pending ([w_relp]) data store, and a foreign
    hart's observation through that dangling CAS is a real pf-reachable
    hart violation that NO instruction-atomic WeakLang run exhibits
    ([WeakComposeLang] §B, finding 2).  [xv6_weak_robust] below is kept
    as the archived M6 statement over this premise; the composition to
    USE is [WeakComposeLang.xv6_weak_robust_lifted] / [_adequate], which
    consume φ directly through the minimal-bad-edge cone (block-contiguous
    replay + completion + [wl_lift]) and need this conjunct nowhere.  The
    exhibit machinery ([bad_edge_violates], [no_bad_edge],
    [gdep2_acyclic_main]) likewise remains valid over the premise but is
    bypassed by [robust_main_no_bad] + [gdep2_acyclic_bad_free].

    HISTORICAL (why it was declared rather than proved, at the pf level):
    W3's φ analysis found the whole pf-level obligation concentrates in
    ONE arm — a fragment-backed load of a byte carrying a foreign
    unpublished [WCplain] message — and refuting that arm needs the state
    interpretation to observe the DISTRIBUTION of outstanding [↦w]
    fractions, the analysis that motivated the [↦w] transfer-discipline /
    three-state-protocol work.  The supersession above makes the pf-level
    statement unnecessary: the lift consumes the WEAKLANG-level export
    ([WeakAdequacy.weak_system_adequacy_phi] → [WeakGhost.no_violation]),
    which quantifies at instruction granularity, where φ is actually
    provable — and the refutability finding shows the pf-level form was
    never going to be provable at all.

    ------------------------------------------------------------------------
    (3) [main_premises] PER TRACED BUNDLE — DECLARED (the first conjunct of
    [m6_side_conditions]), = D-M6-8's static side conditions + [bad_wf] + the
    byte classification.  Four sub-items, each with a different character:

      (3a) [edges_split TS]: every cross rf edge is [edge_ok] (the reader is
           acquire-DISCIPLINED, or its floor already COVERS the message) OR
           [bad] (an owned-unpublished read, which (2) refutes).  D-M6-8 splits
           its content: the machine-side view arithmetic is per-trace and
           premise-free; the VALUE-INDEPENDENT SITE facts (the [aq] bit of the
           reading instruction, "the fence is the instruction immediately after
           the racy load") depend only on the pc at the event, and minimal-cycle
           structure makes that pc Iris-covered; the RESIDUE is discipline at
           positions po-after a pf-unsupported read, where only a static,
           value-independent code property can help.  DECISION (D-M6-8): the
           residue is carried as an explicit, sharply-scoped, per-site-checkable
           static side condition on the kernel image.
      (3b) [bad_wf TS]: whenever a bad edge exists, SOME bad edge has
           bad-target-free strict ancestry.  What this excludes is a "bad SCC" —
           mutually-justified owned reads, i.e. thin-air ownership — for which
           no minimal element and hence no exhibit exists.  Same epistemic
           category as (3a)'s residue, and the same justification: it is
           exactly the shape the kernel's ownership discipline excludes.
      (3c) [ee_ok TS]: W2b's per-triple E-edge obligation, a disjunction of
           FENCE-COVER (a [pw ∧ sw] fence po-between the two fulfils — the
           release/publish sites), WAW-COVER (the writer had already
           synchronized past the prior reader's epoch — the ownership-transfer
           story), and the free arm (an empty floor generates no E edge at all).
           Counterexample 2 of the W2b design is precisely a violation of the
           fence-cover arm with no rescue, so this premise is NOT slack.
      (3d) THE BYTE CLASSIFICATION [∃ sync, ptraces_bytes_ok TS sync]: the
           write-serialization premise.  Without a classification, two agents'
           interleaved same-byte write pairs form a realizable behavior whose
           co+po constraints are cyclic for ANY pf log — the escape is that for
           disciplined programs every same-byte write pair is already
           tc(D⁺)-connected in timestamp order.
    UPGRADE PATH: a static checker over the enumerated racy-read / release /
    publish sites of the kernel image, emitting (3a)/(3c) per site; (3b) and
    (3d) follow from the same enumeration.  (3a)'s site facts are also
    Iris-checkable at the racy-read rules ([WeakRacy.v], [WkStartedLoad.v]) if
    the reader/writer discipline exports of W3 are built.

    ------------------------------------------------------------------------
    (4) THE MMIO / DEVICE-FABRIC SEAM — the RETAINED MMIO-ORDERING
    ASSUMPTION (resolved as such 2026-08-12; restated 2026-08-13, stage D).

    [wpcfg] has no device component, while the real machine carries shared
    MMIO state as a second communication channel.  The composition therefore
    scopes M6 to the harts plus the disk agent OVER THE LOG, and gives each
    hart a PRIVATE COPY OF THE DEVICE AUTOMATON inside its program state:
    [WeakSailLTS.psail]'s [sp_dev : dev_state], read and written silently
    through the TOTALIZED [dev_read_t]/[dev_write_t].  This is well-posed
    because φ is device-OBLIVIOUS: the device arms touch neither the log nor
    any [wstate], so a violation is invariant under changing the device
    interleaving.

    FINDING (2026-08-13) — WHAT THIS REPLACED, AND WHY IT HAD TO BE REPLACED.
    Until stage D the hart's device responses came from a per-behavior ORACLE
    STREAM ([sp_dev : dstream], one little-endian byte list per read), and the
    ⇐ direction needed a premise saying the stream is what the device would
    have answered — [WeakSailLTS2.oracle_consistent], threaded as [Horc] /
    [seg_hart]'s [Hoc] / [cone_liftable]'s hart conjunct.  That premise is
    UNSATISFIABLE, and had been since L3.  [WeakInterp.wrun]'s RAM-read arm
    quantifies over EVERY read value — including the fetched word (ifetch is a
    plain RAM read) and every page-walk PTE — so stream consistency "along
    every path" demands ONE positional stream serve, from ONE device state,
    every device access every junk fetch decodes to along every
    junk-but-valid-PTE translation: two fetched words decoding to [lw] and
    [lb] at the same VA, steered by the same junk PTE path to a device
    address, demand the same stream head have length 4 AND length 1.  An empty
    stream fails on any junk path reaching a device read.  So
    [∃ d, oracle_consistent d (riscv_step b) str] is FALSE at essentially
    every S-mode record, for any stream, and every premise built on it was
    vacuity-making (the third finding of that genre; cf. §B(B)/(D) of
    [WeakComposeLang]).  Request-keyed entries do not fix it — answer #2
    depends on how request #1 evolved the device, i.e. on the path; the only
    oracle that answers an arbitrary request sequence IS the device automaton.

    THE RETAINED ASSUMPTION, in its new and satisfiable form, is per hart
    SEGMENT rather than per path:
      (i)  FABRIC AGREEMENT — the hart's private fabric equals the machine's
           at the start of each of its segments ([WeakComposeLang]'s
           [wl_lift] SegHart carries [wa_dev u cpu = wgdev g], the exact twin
           of the disk agent's [wa_dd u = wgdev g]); the segment's successor
           re-establishes it for that hart by construction, since
           [WeakLang.whart_write] sets [wgdev] to the block's own [wm_dev s'].
      (ii) DEVICE DECODABILITY ALONG THE SEGMENT'S OWN RUN —
           [WeakSailLTS2.dev_ok_blk], i.e. every device access the block
           ACTUALLY performed is one [DevModel.dev_read]/[dev_write] accepts.
           This is a predicate on the run, not on the monad, which is what
           keeps it satisfiable where the ∀-path form was not.
    Nothing else about the device is assumed: the ⇒ direction needs nothing at
    all (a [wrun] cannot take an access the partial functions decline), and
    the reader-tail completion needs nothing (the pf-side arms are total).
    NOT DONE, deliberately: a device-aware full promising machine.  Richer
    device memory models are deferred with M5.
    UPGRADE PATH: M5's device views, at which point the disk agent's DMA
    appends get real classes ([WeakExec.wp_wdisk_step]) and the per-hart
    fabric can be replaced by a shared device component in [wpcfg] — which
    retires (i) outright.

    ------------------------------------------------------------------------
    (5) THE D-M6-3 PARM CORRESPONDENCE NOTE — [full machine ≡ axiomatic RVWMO],
    BY CONTAINMENT.

    The full promising machine is restated NATIVELY in this tree
    ([WeakPromise.v], per-byte, dependency-free) rather than imported: PARM is
    Coq 8.15 + sflib + hahn (~17k lines) and this tree is Rocq 9.x, so the
    published [promising ≡ axiomatic] equivalence cannot be [Require]d.  The
    leg is therefore a DEFINITIONAL-CORRESPONDENCE NOTE — the same epistemic
    category as the model↔hardware seam — not a machine-checked link.

    The note argues CONTAINMENT, not parallelism (D-M6-5): the native machine
    carries NO register views and NO [vcap], so removing join components from
    [view_pre] only LOWERS it, admitting MORE fulfilments.  Our machine is
    therefore WEAKER than PARM's, which is the free direction for
    hardware ⊆ native-full.  The PARM-side [vcap] arithmetic recorded in the
    worklist's §0 is background: it shows PARM pins even MORE promises than we
    assume, and Layer 1 deliberately does not rely on it.

    Independently machine-checked in this tree, which is what makes the note
    auditable rather than a leap: [WeakAxiomatic.promise_free_sound]
    (promise-free runs satisfy the axiomatic model), [WeakAxiomatic2]'s global
    memory order on per-byte OPERATIONS with [ob ⊆ gmo_op], and
    [WeakAxiomatic3.promise_free_complete_clean] (the corrected completeness
    theorem, under [cand_rl_free] and [cand_pub_clean]).  Three of the effort's
    findings are machine-checked REFUTATIONS
    ([ev_rfe_co_fr_cyclic], [promise_free_complete_false],
    [view_domination_false]), so the axiomatic side is pinned by counterexample
    where it is not pinned by proof.
    RECORDED POLARITY EXCEPTION: RVWMO ppo rule 6 ([.rl] on the successor) is
    not enforced by the machine — weaker than RVWMO on that one axis, free for
    adequacy, currently vacuous (the kernel image contains no release store).
    UPGRADE PATH: a Rocq-9 port of PARM.  Not undertaken.

    ------------------------------------------------------------------------
    (6) [sail_shaped] / [nz_writes] / NO-COHERENT-READS — rv64d facts, per
    [WeakInterp] §3.

    [xv6_pf_instr] takes [sail_shaped (riscv_step tick)] as a premise.  Its
    three conjuncts are all properties of the DECODED INSTRUCTION, all vacuous
    for rv64d, and all of the same character as [WeakInterpProj.nz_writes]:
      - NO COHERENT READS: no [MemRead] with [ak_coh = true].  rv64d never
        emits [AK_ifetch] or [AK_ttw] (the W3 recon's finding (1)); this is
        what makes the program LAT-FREE at the instruction level, which is in
        turn what [lat_free_prog] needs at the LTS level ([xv6_lat_free] proves
        the LTS-level statement outright — the arm is spelled stuck).
      - NO ZERO-WIDTH RAM WRITE: an [n = 0] append would grow the log with an
        empty message no label can mirror.
      - (AMO PAIRING — GONE since stage C8, see (O10).  Through C7 the
        premise also demanded that every exclusive [MemRead] OPEN A WINDOW
        that closes at a conditional [MemWrite] to the same address and
        width.  [sail_step] still BRACKETS an AMO into one fused [LRmw] label
        (D-M6-5, the fix point [WeakInterpProj]'s header (4) deferred to W5),
        but that arm's evidence is now the RUN's own [silent_run]/[wr_node],
        not a claim the shape premise makes; a bare exclusive read and a
        standalone conditional write each step as one ordinary label.)
    WHY DECLARED: discharging them means a syntactic analysis of the rv64d
    decoder's ~thousands of generated branches.

    STATUS AFTER STAGE C8 (2026-08-14) — THE SHAPE HALF OF THIS SEAM IS
    CLOSED; what follows is the history of the five findings it took.  The
    syntactic analysis exists and is mechanized: [WeakShape.v] (the
    compositional kit), [WeakShapeOverrides.v] (the [gwalk]-mode combinators
    and [gsilent]), [WeakShapeOverrides2.v] ([gpost], the value side) and the
    COMPLETE generated sweep [WeakShapeGen01..15.v] ([tools/gen_shape.py],
    [make gen-shape]) machine-check [gwalk] — i.e. [sail_shaped] — for
    all 294 generatable monadic definitions reachable from [rv64d.try_step]
    (5 min 20 s of [coqc] for the whole tower, since stage C5's (O8) fixed
    the sweep's leaf tactic).
    On top of it [WeakShapePeel.v] peels [try_step], [run_hart_active] and
    [execute], so [WeakShapeTop.riscv_step_shaped_residue] reduces the whole
    premise to [fetch] plus the eleven memory [execute_*] clauses, and stage
    C8's [WeakShapeMem.v] discharges those.  What kept the seam open for five
    stages was never the volume of branches but FACTS ABOUT THE MODEL — four
    of them answered by specification changes, one an irreducible assumption:

      (O4) [∀ b, sail_shaped (riscv_step b)] was FALSE, and STAGE C4 FIXED
           THE SPECIFICATION.  A STANDALONE STORE-CONDITIONAL
           ([rv64d.execute_STORECON]) issues a [Write_RISCV_conditional] RAM
           write — [ak_latest = true] — with NO exclusive [MemRead] in the
           same instruction, because the lr/sc reservation lives in the
           model's pure axioms and the matching [lr] is a different
           [riscv_step]; the old AMO-PAIRING conjunct forbade exactly that.
           It is the mirror of stage C1's (O2) (an exclusive read with no
           conditional write), which C2 fixed by weakening [amo_tail]'s
           [Interface.Ret] arm and adding [sail_mstep]'s bare exclusive-read
           arm, and C4 took the symmetric treatment: the window-closed
           [MemWrite] arms of [sail_shaped] and [sail_mstep] lost their
           [ak_latest = false] conjunct, so a standalone conditional write is
           shaped and steps as a plain [LStore] (the machine only gains
           behaviors).  The ⇐ cost went into the existing [fused_blk], whose
           [pf_solo_f] now also forbids stepping from a conditional-write
           node — no new premise.
      (O5) Three of [rv64d]'s [Axiom]s are MONADIC ([load_reservation],
           [cancel_reservation], [plat_term_write]) and all three are
           reachable from [try_step], so no shape fact about them is provable
           at all.  The seam's residue after (O4) is therefore three POINT
           premises about those axioms, not a [∀ b] premise.
      (O6) THE NO-ZERO-WIDTH-WRITE CONJUNCT NEEDS A DECODER POSTCONDITION,
           not a memory-cone lemma.  Sail's [0 < width ≤ 4096] precondition
           is emitted as a COMMENT and [word_width] is [Z], so
           [execute_STORE imm rs2 rs1 0] is a well-typed [instruction] on
           which the model issues a zero-width [MemWrite]
           ([WeakShapeOverrides2.gwalk_write_ram_zero_False]) — i.e.
           [∀ ast, gwalk (execute ast)], the only form the compositional
           route can use, is FALSE.  [sail_shaped (riscv_step tick)] itself is
           not refuted (the decoder only builds widths in [[1;2;4;8]]); what
           is refuted is the route, and closing it means a [gpost] sweep over
           [encdec_backwards].  The same machinery supplies the last piece of
           AMO PAIRING: [pmaCheck] answers [CannotSplit] for every exclusive
           access kind, hence [split_misaligned] returns [N = 1] and the
           window is opened at most once per instruction.

      (O9) (stage C6) the [Interface.ExtraOutcome] arm of
           [sail_shaped]/[amo_tail] OVER-QUANTIFIED — a raised Sail exception
           is a dead end the LTS has no arm for, and the old [∀ r, …] arm
           walked the whole rest of the instruction at every value of the
           thrown-at type.  FIXED in the specification ([WeakSailLTS] delta
           (e''')): the arm is [True].
      (O10) (stage C7) [∀ b, sail_shaped (riscv_step b)] WAS FALSE AGAIN,
           and this time AMO PAIRING was what was wrong.
           [rv64d.update_and_write_pte] — on the path of EVERY memory
           instruction, since every one of them translates — issues an
           EXCLUSIVE PTE read for the A/D update and then, on the arm where
           the RE-READ entry needs no update, returns SUCCESSFULLY with no
           conditional write; the instruction goes on to its own data access,
           which was a [MemRead] inside the open window and [amo_tail]
           refused it.  The abandonment C2 legalised had assumed the
           abandoned tail is SILENT ([sail_mstep] BRACKETED it to an
           [Interface.Ret]); here it is the rest of the instruction.  A "the
           tail is quiet from here" bracket is only as good as the CALL DEPTH
           at which the window is abandoned.
           FIXED IN STAGE C8, by the narrowing the other two deltas already
           took: [sail_shaped]'s [MemRead] arm DROPS the window (an exclusive
           read is shaped exactly like a plain one), [amo_tail] is DELETED,
           and [sail_mstep]'s bare exclusive-read arm is ONE STEP — the plain
           [LLoad] arm simply stopped requiring [ak_latest = false], exactly
           as (O4) stopped requiring it on the write side.  The ⇐ cost fell
           where (O2)'s and (O4)'s did, into [fused_blk], with NO new premise;
           the fused rmw arm stays (it is how an rmw appends one message) and
           takes its amo-structure evidence from the RUN, not from a claim
           the shape predicate makes.  AND IT COLLAPSED THE KIT: the window
           index left [gwalk], [gwalkx] disappeared, and the memory cone lost
           its hardest obligation — the read/write address-and-width
           agreement, which had needed [pmaCheck]'s [CannotSplit]
           postcondition and an [untilMT] unfolding at [N = 1].

    STATUS AFTER STAGE C9 (2026-08-14) — THE SEAM IS FULLY CLOSED, MODULO
    TWO NAMED RECORDS AND ONE PER-TRACE PREMISE.  Both halves are theorems:

      SHAPE     [WeakShapeTop.riscv_step_shaped_ax :
                   rv64d_axiom_shapes → ∀ b, sail_shaped (riscv_step b)]
      LIVENESS  [WeakShapeLive.riscv_step_live_ax :
                   rv64d_live_residue →
                   ∀ rs b, priv_ok rs → sail_live_st rs (riscv_step b)]

    and [WeakComposeLang]'s capstones take the two RECORDS in place of the
    two [∀ b] premises, plus [Hpriv] (every hart record's [cur_privilege] is
    one of [Machine]/[Supervisor]/[User]) inside [xv6_cone_premises].

    THE LIVENESS HALF IS NOT A [∀ b] FACT, AND THAT IS THE STAGE'S FINDING
    (O9's other half, settled in C9).  The old premise
    [∀ b, sail_live (riscv_step b)] is REFUTED — liveness forbids a raised
    Sail exception, and [rv64d.zicfiss_xSSE] raises one at
    [VirtualSupervisor], a value the old [RegRead] arm quantified over — so
    a capstone carrying it was VACUOUS, the same genre as the ∀-path oracle
    premise and (O10).  The repair is the same narrowing all five earlier
    findings took: [WeakSailLTS.sail_mstep] answers a [RegRead] CONCRETELY
    ([k (register_lookup r rs)]), so the predicate does too —
    [WeakSailComplete.sail_live_st rs m], with [RegWrite] THREADING the
    state.  The only register still ∀-quantified is [sig_seip], because
    [irq_deliver] writes it behind the residual's back.  The residual
    invariant becomes "live at the record's OWN registers"
    ([WeakSailCone.res_ok]), which is inductive step for step, and the
    boundary arm is where [Hpriv] enters.

    THE TWO RECORDS ARE NOT THE SAME KIND OF THING.
    [WeakShapeMem.rv64d_axiom_shapes] is IRREDUCIBLE (three opaque monadic
    [Axiom]s of the generated model).  [WeakShapeLive.rv64d_live_residue] is
    a WORK ITEM: the (O3) liveness sweep, un-run.  Its size is now measured
    ([make live-sites]): of the 345 monadic definitions reachable from
    [try_step], 123 carry a failure node directly and 302 carry one in their
    cone — 431 sites in all (187 [assert_exp], 130 [exit], 107
    [internal_error], 4 [reserved_behavior], 3 [untilMT]) — and each needs a
    REACHABILITY argument, not a shape lemma.  40 functions are failure-free
    and could be emitted mechanically today.

    UPGRADE PATH: (O4)'s LTS fix LANDED in stage C4, the generated tower
    LANDED complete in C5, (O6)'s DECODER POSTCONDITION LANDED in C6
    ([WeakShapeAst.ast_wf], [WeakShapeDec.gpureP_ext_decode]) and C7 CONSUMED
    it at [run_hart_active] ([WeakShapeWin]'s [gwpx] mode, the 116-lemma
    value sweep [WeakShapeExecGen01..03], [WeakShapeExec]); C8 fixed (O10)
    and closed the memory cone; C9 restated and closed the liveness half.
    What remains is the (O3) sweep behind [rv64d_live_residue] and the
    model-level reachability invariant that would delete [Hpriv].  Details
    and the ordered plan: [claude-notes/projects/weak-memory-premises.md].

    ------------------------------------------------------------------------
    WHAT IS *NOT* ON THIS LIST, because it is machine-checked: the Layer-1
    robustness theorem itself ([robust_main] — acyclicity of D⁺ from the
    discipline premises, the π-permuted simulation, the minimal-bad-edge
    exhibit, the completable-prefix transport), the promise-free ⊆ full
    inclusion and its strictness ([WeakPromiseLitmus.lb_weak_outcome_reachable]),
    the front-loading factorization and per-agent state phases
    ([WeakPromiseFact]), the erasure bridge in BOTH directions
    ([WeakPromiseBridge]), the Sail LTS's lat-freedom and
    timestamp-obliviousness ([WeakSailLTS], lifted here to [pxv6] by
    [xv6_lat_free]/[xv6_ts_oblivious]), and the ⇒ instruction bracket
    ([xv6_pf_instr]). *)
