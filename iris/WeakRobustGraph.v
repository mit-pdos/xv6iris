(** * WeakRobustGraph.v — the dependency graph over a traced behavior
      (M6 W2a, step 2: the INFRASTRUCTURE slice)

    [WeakRobustTrace.v] delivers a lat-free full-machine behavior as a
    promise phase into [mid] plus ONE TRACE PER AGENT against [mid]'s
    frozen [(img, log)], with the fulfilled timestamp recorded per event
    ([ae_ts]) and the fulfilment accounting proved
    ([wp_behavior_fulfil_once]).  This file builds the VOCABULARY the
    per-class acyclicity theorem is stated in — event identity, the
    reads-of relation, the dependency relation [gdep] — and the
    STRUCTURAL lemmas that theorem will consume.  The per-class
    refutation itself (SCowned via the violation premise, SCfenced and
    SCexcl via timestamp arithmetic) is NOT here; the goal it proves is
    stated at the bottom as [gdep_acyclicity_goal].

    THE FOUR DELIVERABLES.

    (1) EVENT IDENTITY.  An event is [gev := (agent index, step index)];
        [gev_ev] looks it up in the bundle, [gev_lb] is its label and
        [gev_ts] the timestamp it fulfilled.  Well-formedness
        ([gev_wf]) is [is_Some ∘ gev_ev], equivalently the two index
        bounds ([gev_wf_bounds]).

    (2) READS-OF.  [lb_reads l] is the list of (byte address, timestamp)
        pairs the label reads: [LLoad] and [LRmw] read [(base + j,
        tvs.j.1)] per byte [j] (an [LRmw]'s read half and write half
        share [base], which is what makes the same-step case of the
        own-read lemma close — see below); every other label reads
        nothing.

    (3) THE DEPENDENCY RELATION [gdep = gpo ∪ grf], EVENT-LEVEL.  Per
        the worklist's post-W4 note: a machine step is atomic in the
        promise-free interleaving, so its bytes cannot split across the
        topological sort, and [gdep] carries no co/fr edges — so
        [WeakAxiomatic2.ev_rfe_co_fr_cyclic] (which refutes an
        event-level EXTERNAL axiom) does not apply here.

    (4) THE DEVICE-ORDER EDGES [gdev] (G3).  The successor relation on
        the global device-order witness [pd_ord DS]
        ([WeakRobustTrace.pdevs]): [gdev TS DS e1 e2] iff [e1] and [e2]
        are CONSECUTIVE entries.  Adding it to the graph is what makes a
        topological sort keep the fabric-touching events in the
        behavior's own order, which is what lets the replay hand each of
        them the fabric it recorded ([WeakRobustSim], G4).  Successor
        rather than transitive chain: the closure machinery walks
        predecessors one at a time and wants a small decidable relation
        ([gdev_dec]); the transitive facts are derived once
        ([gdev_chain]).  Two structural facts pay for themselves later:
        the witness is duplicate-free ([pd_ord_index_inj], from W3) and a
        SAME-AGENT gdev edge is already a [gpo] edge ([gdev_gpo]) — so
        the edges [gdev] genuinely adds are the CROSS-agent ones.

    THE OWN-READ FINDING, PROVED ([atrace_own_read] / [grf_own_lt]):
    inside ONE agent's trace, a read of [(a, ts)] can only sit trace
    AFTER the event fulfilling [ts].  Three cases:

      - [k = k'] (a step reading its own fulfilment): only [LRmw] both
        reads and fulfils, and its [fulfil_ok] is checked on the state
        AFTER [load_post_run], whose [coh] at the read byte is already
        ≥ [ts] ([load_post_run_coh]) while [fulfil_ok] demands
        [coh < ts] on every written byte.  The geometry closes because
        the read bytes ARE the written bytes: the label's read half is
        [tvs] at [base] and its write half is [data] at the SAME [base],
        with [length tvs = length data] forced by [astep_ok].
      - [k < k'] (read before fulfil): the read raises [coh a] to ≥ [ts]
        ([astep_ok_read_coh]), [coh] only grows along a trace
        ([asteps_ws_le], from the step functions' [_le] lemmas), and the
        fulfil needs [coh a < ts] — the read's own timestamp names the
        fulfilled message, so [a] IS one of its bytes
        ([astep_ok_fulfil_coh]).
      - [k' < k] is the conclusion.

    Consequently rf edges never contradict po, every [gdep] edge inside
    one agent strictly increases the step index ([gdep_same_agent_lt]),
    and every [gdep] cycle is genuinely CROSS-agent
    ([tc_gdep_cross] — the LB shape).

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported for the two parked [WeakMem] fold lemmas
    ([load_post_run_coh], [store_post_run_coh] — see the owed-lifts batch
    under W4); it is imported FIRST so that [WeakPromise]'s [wlabel]
    constructors shadow its [lbl] ones. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobust.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** A [WeakMem]-level fact — LIFTED

    "A message writes only inside its own byte range" is now
    [WeakMem.msg_byte_range] (the W4 lift batch made it canonical there and
    dropped this file's and [WeakPromiseBridge]'s copies).  The local name
    is kept as an alias so the uses below read unchanged. *)
Notation msg_byte_in_range := msg_byte_range (only parsing).

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE 2: what a label READS

    Byte [j] of a load/rmw run reads address [base + j] at timestamp
    [tvs.j.1] — [WeakMem]'s contiguous-run convention, the same one
    [read_ok] and [load_post_run] use. *)

Definition tvs_reads (base : Z) (tvs : list (nat * bv 8)) : list (Z * nat) :=
  imap (λ j tv, (base + Z.of_nat j, tv.1)) tvs.

Definition lb_reads (l : wlabel) : list (Z * nat) :=
  match l with
  | LLoad _ _ base tvs _ => tvs_reads base tvs
  | LRmw _ _ base tvs _ _ _ => tvs_reads base tvs
  | LExLoad _ base tvs _ => tvs_reads base tvs
  | LSilent | LStore _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
  | LCtrl _ | LInstr | LExStore _ _ _ _ _ => []
  end.

(** THE ADDRESS-OPERAND LIST of a label (D2).  [[]] on every label that
    has none, so the dependency-free instance sees the old vocabulary
    BY CONVERSION ([srcs_view _ [] = 0], [lsrcs_view _ [] = []]). *)
Definition lb_asrc (l : wlabel) : list dsrc :=
  match l with
  | LLoad _ _ _ _ asrc => asrc
  | LStore _ _ _ asrc _ => asrc
  | LRmw _ _ _ _ _ asrc _ => asrc
  | LExLoad _ _ _ asrc => asrc
  | LExStore _ _ _ asrc _ => asrc
  | LSilent | LFence _ _ _ _ | LDev | LRegW _ _ | LCtrl _ | LInstr => []
  end.

Lemma elem_of_tvs_reads base tvs a ts :
  (a, ts) ∈ tvs_reads base tvs ↔
  ∃ (j : nat) (v : bv 8), tvs !! j = Some (ts, v) ∧ a = base + Z.of_nat j.
Proof.
  rewrite /tvs_reads elem_of_lookup_imap. split.
  - intros (j & [t v] & Hj & Heq). simplify_eq/=. by exists j, v.
  - intros (j & v & Hj & ->). exists j, (ts, v). by rewrite Hj.
Qed.

Lemma lb_reads_nil_silent : lb_reads LSilent = [].
Proof. done. Qed.
Lemma lb_reads_nil_store rl base data asrc vsrc :
  lb_reads (LStore rl base data asrc vsrc) = [].
Proof. done. Qed.
Lemma lb_reads_nil_fence pr pw sr sw : lb_reads (LFence pr pw sr sw) = [].
Proof. done. Qed.

(* ------------------------------------------------------------------ *)
(** ** [astep_ok]-level facts: reads, fulfils and [coh]

    Everything the own-read lemma needs, stated on the ONE per-step
    specification [WeakPromiseFact.astep_ok] rather than on the five
    rules — the packaging that gives these proofs one case per label
    instead of one per rule. *)

Section astep.
  Context {P : Type}.
  Implicit Types ag : wpagent P.

  (** Every step function only RAISES views (the [_le] lemmas of
      [WeakMem], collected by label). *)
  Lemma astep_ok_f_le img log i ag l f D :
    astep_ok img log i ag l f D → ∀ w, ws_le w (f w).
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - intros [-> _] w. reflexivity.
    - intros (_ & -> & _) w. apply load_post_run_d_le.
    - intros (ts & kc & _ & _ & _ & -> & _) w. apply store_post_run_d_le.
    - intros (ts & kc & _ & _ & _ & _ & _ & _ & -> & _) w.
      etrans; [apply load_post_run_d_le|apply store_post_run_d_le].
    - intros [-> _] w. apply fence_post_le.
    - (* dev: [LSilent]'s twin *) intros [-> _] w. reflexivity.
    - intros [-> _] w. apply regw_post_le.
    - intros [-> _] w. apply ctrl_post_le.
    - intros [-> _] w. apply instr_post_le.
    - done.
    - done.
  Qed.

  (** A fulfilled timestamp is nonzero: [fulfil_ok]'s EXT conjunct
      ([fulfil_vpre < ts]) is already unsatisfiable at [ts = 0].  This is
      what makes "timestamp 0 is the era-initial image, never a fulfil"
      a theorem rather than a well-formedness assumption. *)
  Lemma astep_ok_ts_pos img log i ag l f ts :
    astep_ok img log i ag l f (Some ts) → (0 < ts)%nat.
  Proof.
    destruct l; simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros (ts' & kc & _ & _ & (_ & Hext) & _ & Heq). simplify_eq. lia.
    - intros (ts' & kc & _ & _ & _ & _ & _ & (_ & Hext) & _ & Heq).
      simplify_eq. lia.
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - done.
    - done.
  Qed.

  (** A read's timestamp names a real write of the byte it reads
      ([read_ok]'s [log_byte] conjunct). *)
  Lemma astep_ok_read_log_byte img log i ag l f D a ts :
    astep_ok img log i ag l f D → (a, ts) ∈ lb_reads l →
    is_Some (log_byte img log ts a).
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - intros _ Hin%elem_of_nil. done.
    - intros (Hro & _ & _) [j [v [Hj ->]]]%elem_of_tvs_reads.
      destruct (Hro j ts v Hj) as (Hb & _ & _). by eexists.
    - intros _ Hin%elem_of_nil. done.
    - intros (ts' & kc & _ & _ & _ & Hro & _) [j [v [Hj ->]]]%elem_of_tvs_reads.
      destruct (Hro j ts v Hj) as (Hb & _ & _). by eexists.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - done.
    - done.
  Qed.

  (** THE READ RAISES [coh]: after a step whose label reads [(a, ts)],
      the agent's coherence floor at [a] is at least [ts].  For [LLoad]
      this is [load_post_run_coh] verbatim; for [LRmw] the write half's
      [store_post_run] can only raise it further. *)
  Lemma astep_ok_read_coh img log i ag l f D a ts :
    astep_ok img log i ag l f D → (a, ts) ∈ lb_reads l →
    (ts ≤ coh (f (pa_ws ag)) a)%nat.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - intros _ Hin%elem_of_nil. done.
    - intros (_ & -> & _) [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      by apply (load_post_run_d_coh (pa_ws ag) aq (srcs_view (pa_ws ag) asrc) base (tvs.*1) j ts Hts).
    - intros _ Hin%elem_of_nil. done.
    - intros (ts' & kc & _ & _ & _ & _ & _ & _ & -> & _)
             [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      etrans;
        [by apply (load_post_run_d_coh (pa_ws ag) aq (srcs_view (pa_ws ag) asrc) base (tvs.*1) j ts Hts)|].
      apply ws_le_coh, store_post_run_d_le.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - intros _ Hin%elem_of_nil. done.
    - done.
    - done.
  Qed.

  (** THE FULFIL LOWERS NOTHING BUT DEMANDS [coh < ts] on every byte of
      the message it fulfils. *)
  Lemma astep_ok_fulfil_msg img log i ag l f ts :
    astep_ok img log i ag l f (Some ts) →
    ∃ base data k, log !! (ts - 1)%nat = Some (WMsg base data (Some i) k).
  Proof.
    destruct l; simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros (ts' & kc & _ & Hlog & _ & _ & Heq). simplify_eq. by eexists _, _, _.
    - intros (ts' & kc & _ & _ & Hlog & _ & _ & _ & _ & Heq).
      simplify_eq. by eexists _, _, _.
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - done.
    - done.
  Qed.

  Lemma astep_ok_fulfil_coh img log i ag l f ts m a :
    astep_ok img log i ag l f (Some ts) →
    log !! (ts - 1)%nat = Some m → is_Some (msg_byte m a) →
    (coh (pa_ws ag) a < ts)%nat.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros (ts' & kc & _ & Hlog & (Hcoh & _) & _ & Heq) Hm Hb. simplify_eq.
      destruct (msg_byte_in_range _ _ Hb) as (j & Hj & ->). simpl in Hj |- *.
      by apply Hcoh.
    - intros (ts' & kc & Hlen & _ & Hlog & _ & _ & (Hcoh & _) & _ & Heq) Hm Hb.
      simplify_eq.
      destruct (msg_byte_in_range _ _ Hb) as (j & Hj & ->). simpl in Hj |- *.
      eapply Nat.le_lt_trans; [|by apply Hcoh].
      apply ws_le_coh, load_post_run_d_le.
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - done.
    - done.
  Qed.

  (** THE SAME-STEP CASE of the own-read lemma: a step can NEVER read
      the very timestamp it fulfils.  Only [LRmw] has both halves, and
      its read bytes are exactly its written bytes ([length tvs =
      length data] at a common [base]) — so [load_post_run_coh] and
      [fulfil_ok]'s COH conjunct meet on the same address. *)
  Lemma astep_ok_read_fulfil_same img log i ag l f ts a :
    astep_ok img log i ag l f (Some ts) → (a, ts) ∈ lb_reads l → False.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros _ Hin%elem_of_nil. done.
    - intros (ts' & kc & Hlen & _ & _ & _ & _ & (Hcoh & _) & _ & Heq)
             [j [v [Hj ->]]]%elem_of_tvs_reads.
      injection Heq as Heq. subst ts'.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      have Hjlt : (j < length data)%nat.
      { rewrite -Hlen. by eapply lookup_lt_Some. }
      have Hge := load_post_run_d_coh (pa_ws ag) aq
                    (srcs_view (pa_ws ag) asrc) base (tvs.*1) j ts Hts.
      have Hlt := Hcoh j Hjlt. rewrite /acc_addr in Hge. lia.
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - done.
    - done.
  Qed.

End astep.

(* ------------------------------------------------------------------ *)
Section graph.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types TS : ptraces P D.
  Implicit Types T : atrace P D.
  Implicit Types c : wpcfg P D.

  (* ---------------------------------------------------------------- *)
  (** ** Trace-level plumbing *)

  (** The wf conjunct of [ptraces_of] on its own: every trace of the
      bundle is a wf trace of its agent against the frozen log. *)
  Definition ptraces_wf TS : Prop :=
    ∀ i T, pt_trs TS !! i = Some T → atrace_wf pstep (pt_img TS) (pt_log TS) i T.

  Lemma ptraces_of_wf TS mid c : ptraces_of pstep TS mid c → ptraces_wf TS.
  Proof. by intros (_ & _ & _ & Hwf & _). Qed.

  (** Views only grow along one agent's trace: the [ws_le] analog of
      [WeakRobustTrace]'s [asteps_prom_le]. *)
  Lemma asteps_ws_succ img log i ags evs k ag ag' :
    asteps_wf pstep img log i ags evs →
    ags !! k = Some ag → ags !! S k = Some ag' →
    ws_le (pa_ws ag) (pa_ws ag').
  Proof.
    intros Hwf Hk Hk'.
    have [ev Hev] : is_Some (evs !! k).
    { apply lookup_lt_is_Some_2. destruct Hwf as [Hlen _].
      apply lookup_lt_Some in Hk'. lia. }
    destruct (asteps_wf_step pstep img log i ags evs k ev Hwf Hev)
      as (a1 & a2 & st' & f & Ha1 & Ha2 & _ & Hok & Heq).
    simplify_eq. simpl. by eapply astep_ok_f_le.
  Qed.

  Lemma asteps_ws_mono img log i ags evs d :
    ∀ k ag ag',
      asteps_wf pstep img log i ags evs →
      ags !! k = Some ag → ags !! (k + d)%nat = Some ag' →
      ws_le (pa_ws ag) (pa_ws ag').
  Proof.
    induction d as [|d IH]; intros k ag ag' Hwf Hk Hkd.
    - rewrite Nat.add_0_r in Hkd. simplify_eq. reflexivity.
    - have [agn Hagn] : is_Some (ags !! S k).
      { apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hkd. lia. }
      have Hstep : ws_le (pa_ws ag) (pa_ws agn) by eapply asteps_ws_succ.
      have Heq : (k + S d)%nat = (S k + d)%nat by lia.
      rewrite Heq in Hkd.
      etrans; [exact Hstep|by eapply IH].
  Qed.

  Lemma asteps_ws_le img log i ags evs k1 k2 ag1 ag2 :
    asteps_wf pstep img log i ags evs →
    (k1 ≤ k2)%nat → ags !! k1 = Some ag1 → ags !! k2 = Some ag2 →
    ws_le (pa_ws ag1) (pa_ws ag2).
  Proof.
    intros Hwf Hle Hk1 Hk2.
    eapply (asteps_ws_mono _ _ _ _ _ (k2 - k1)%nat); [done|done|].
    by rewrite -Nat.le_add_sub.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 4: THE OWN-READ LEMMA

      In one agent's wf trace, the event fulfilling [ts] strictly
      PRECEDES every event of that agent reading [ts]. *)

  Theorem atrace_own_read img log i T k k' ev ev' a ts :
    atrace_wf pstep img log i T →
    at_evs T !! k = Some ev → (a, ts) ∈ lb_reads (ae_lb ev) →
    at_evs T !! k' = Some ev' → ae_ts ev' = Some ts →
    (k' < k)%nat.
  Proof.
    intros Hwf Hev Hin Hev' Hts.
    destruct (asteps_wf_step pstep img log i (at_ags T) (at_evs T) k ev
                Hwf Hev)
      as (ag & agn & st' & f & Hag & Hagn & _ & Hok & Hagne).
    destruct (asteps_wf_step pstep img log i (at_ags T) (at_evs T) k' ev'
                Hwf Hev')
      as (ag' & agn' & st'' & f' & Hag' & Hagn' & _ & Hok' & _).
    rewrite Hts in Hok'.
    destruct (Nat.lt_trichotomy k' k) as [Hlt|[->|Hgt]]; [done| |].
    (* k = k': a step reading its own fulfilment — refuted by geometry *)
    { rewrite Hev in Hev'. simplify_eq. exfalso.
      eapply (astep_ok_read_fulfil_same _ _ _ _ _ _ ts a); [exact Hok'|done]. }
    (* k < k': the read raised coh(a) past ts, the fulfil needs it below *)
    exfalso.
    (* THE READ'S GAIN, transported along the trace to the fulfil *)
    have Hge : (ts ≤ coh (pa_ws agn) a)%nat.
    { rewrite Hagne /=.
      eapply (astep_ok_read_coh img log i ag (ae_lb ev) f (ae_ts ev) a ts);
        [exact Hok|exact Hin]. }
    have Hmono : ws_le (pa_ws agn) (pa_ws ag').
    { eapply (asteps_ws_le img log i (at_ags T) (at_evs T) (S k) k');
        [exact Hwf|lia|exact Hagn|exact Hag']. }
    have Hle := ws_le_coh (pa_ws agn) (pa_ws ag') a Hmono.
    (* THE READ'S TIMESTAMP NAMES THE FULFILLED MESSAGE, so [a] is one of
       its bytes and the fulfil's COH condition covers it *)
    have Hpos : (0 < ts)%nat by eapply astep_ok_ts_pos.
    have Hlb : is_Some (log_byte img log ts a).
    { eapply (astep_ok_read_log_byte img log i ag (ae_lb ev) f (ae_ts ev) a ts);
        [exact Hok|exact Hin]. }
    have Hmsg : ∃ m, log !! (ts - 1)%nat = Some m ∧ is_Some (msg_byte m a).
    { destruct ts as [|p]; [lia|]. rewrite log_byte_S in Hlb.
      destruct (log !! p) as [m|] eqn:Hm; [|by destruct Hlb].
      exists m. have Hp : (S p - 1)%nat = p by lia. rewrite Hp Hm. by split. }
    destruct Hmsg as (m & Hm1 & Hm2).
    have Hlt' : (coh (pa_ws ag') a < ts)%nat.
    { eapply (astep_ok_fulfil_coh img log i ag' (ae_lb ev') f' ts m a);
        [exact Hok'|exact Hm1|exact Hm2]. }
    lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 1: EVENT IDENTITY over a bundle *)

  (** An event of a traced behavior: (agent index, step index). *)
  Definition gev : Type := (nat * nat)%type.

  Implicit Types e : gev.

  Definition gev_tr TS e : option (atrace P D) := pt_trs TS !! e.1.
  Definition gev_ev TS e : option (aev D) :=
    T ← pt_trs TS !! e.1; at_evs T !! e.2.
  Definition gev_lb TS e : option wlabel := ae_lb <$> gev_ev TS e.
  (** The timestamp the event FULFILLED ([None] for a non-store). *)
  Definition gev_ts TS e : option nat := gev_ev TS e ≫= ae_ts.

  Definition gev_wf TS e : Prop := is_Some (gev_ev TS e).

  Lemma gev_wf_bounds TS e :
    gev_wf TS e ↔
    ∃ T, pt_trs TS !! e.1 = Some T ∧ (e.2 < length (at_evs T))%nat.
  Proof.
    rewrite /gev_wf /gev_ev. split.
    - intros [ev Hev]. destruct (pt_trs TS !! e.1) as [T|] eqn:HT;
        simpl in Hev; [|done].
      exists T. split; [done|]. by eapply lookup_lt_Some.
    - intros (T & HT & Hlt). rewrite HT /=. by apply lookup_lt_is_Some_2.
  Qed.

  Lemma gev_wf_index TS e : gev_wf TS e → (e.1 < length (pt_trs TS))%nat.
  Proof.
    intros [T [HT _]]%gev_wf_bounds. by eapply lookup_lt_Some.
  Qed.

  Lemma gev_ts_wf TS e ts : gev_ts TS e = Some ts → gev_wf TS e.
  Proof.
    rewrite /gev_ts /gev_wf. destruct (gev_ev TS e) as [ev|]; [|done].
    intros _. by eexists.
  Qed.

  Lemma gev_lb_wf TS e l : gev_lb TS e = Some l → gev_wf TS e.
  Proof.
    rewrite /gev_lb /gev_wf. destruct (gev_ev TS e) as [ev|]; [|done].
    intros _. by eexists.
  Qed.

  (** The step an event names, with its [astep_ok] and the two agent
      records it runs between.  (The single point where the graph meets
      [WeakRobustTrace]'s [asteps_wf].) *)
  Lemma gev_step TS e ev :
    ptraces_wf TS → gev_ev TS e = Some ev →
    ∃ T ag ag' st' f,
      pt_trs TS !! e.1 = Some T ∧
      at_ags T !! e.2 = Some ag ∧ at_ags T !! S e.2 = Some ag' ∧
      astep_prog pstep ag ev st' ∧
      astep_ok (pt_img TS) (pt_log TS) e.1 ag (ae_lb ev) f (ae_ts ev) ∧
      pa_ws ag' = f (pa_ws ag).
  Proof.
    rewrite /gev_ev. intros Hwf Hev.
    destruct (pt_trs TS !! e.1) as [T|] eqn:HT; simpl in Hev; [|done].
    destruct (asteps_wf_step pstep (pt_img TS) (pt_log TS) e.1
                (at_ags T) (at_evs T) e.2 ev (Hwf _ _ HT) Hev)
      as (ag & ag' & st' & f & Hag & Hag' & Hps & Hok & Hagn).
    exists T, ag, ag', st', f. split_and!; [done|done|done|done|done|].
    by subst ag'.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 2 (continued): the reads-of PREDICATE *)

  (** [gev_reads TS e a ts]: event [e] reads byte [a] at timestamp [ts]. *)
  Definition gev_reads TS e (a : Z) (ts : nat) : Prop :=
    ∃ l, gev_lb TS e = Some l ∧ (a, ts) ∈ lb_reads l.

  Lemma gev_reads_wf TS e a ts : gev_reads TS e a ts → gev_wf TS e.
  Proof. intros (l & Hl & _). by eapply gev_lb_wf. Qed.

  (** A read's timestamp names a real write of the byte read. *)
  Lemma gev_reads_log_byte TS e a ts :
    ptraces_wf TS → gev_reads TS e a ts →
    is_Some (log_byte (pt_img TS) (pt_log TS) ts a).
  Proof.
    intros Hwf (l & Hl & Hin). rewrite /gev_lb in Hl.
    destruct (gev_ev TS e) as [ev|] eqn:Hev; simpl in Hl; [|done].
    simplify_eq.
    destruct (gev_step TS e ev Hwf Hev)
      as (T & ag & ag' & st' & f & _ & _ & _ & _ & Hok & _).
    by eapply astep_ok_read_log_byte.
  Qed.

  (** A read of a NONZERO timestamp names a log message
      ([WeakMem]'s convention: timestamp [S p] is log position [p];
      timestamp 0 is the era-initial image and has no author). *)
  Lemma gev_reads_msg TS e a p :
    ptraces_wf TS → gev_reads TS e a (S p) →
    ∃ m, pt_log TS !! p = Some m ∧ is_Some (msg_byte m a).
  Proof.
    intros Hwf Hr.
    have Hlb := gev_reads_log_byte TS e a (S p) Hwf Hr.
    rewrite log_byte_S in Hlb.
    destruct (pt_log TS !! p) as [m|] eqn:Hm; [|by destruct Hlb].
    by exists m.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 3: THE DEPENDENCY RELATION [gdep] *)

  (** Per-agent program order: same trace, earlier step index.  The two
      [gev_wf] conjuncts are the one addition to the worklist's spelling
      ("same agent ∧ k1 < k2"): they keep [gdep] a relation on REAL
      events, which the rf arm gets for free ([grf_wf]) and which W2b's
      topological sort needs (it sorts the events of the bundle, not
      arbitrary index pairs). *)
  Definition gpo TS e1 e2 : Prop :=
    e1.1 = e2.1 ∧ (e1.2 < e2.2)%nat ∧ gev_wf TS e1 ∧ gev_wf TS e2.

  (** Reads-from: the event that FULFILLED a timestamp, to every event
      that reads it.  Only timestamps ≥ 1 can appear
      ([grf_ts_pos] — timestamp 0 is the era-initial image), and the
      source is UNIQUE ([grf_source_unique]). *)
  Definition grf TS e1 e2 : Prop :=
    ∃ (ts : nat) (a : Z), gev_ts TS e1 = Some ts ∧ gev_reads TS e2 a ts.

  Definition gdep TS e1 e2 : Prop := gpo TS e1 e2 ∨ grf TS e1 e2.

  Lemma grf_wf TS e1 e2 : grf TS e1 e2 → gev_wf TS e1 ∧ gev_wf TS e2.
  Proof.
    intros (ts & a & Hts & Hr).
    split; [by eapply gev_ts_wf|by eapply gev_reads_wf].
  Qed.

  Lemma gdep_wf TS e1 e2 : gdep TS e1 e2 → gev_wf TS e1 ∧ gev_wf TS e2.
  Proof.
    intros [(_ & _ & ? & ?)|Hrf]; [done|by apply grf_wf].
  Qed.

  (** Fulfilled timestamps are nonzero. *)
  Lemma gev_ts_pos TS e ts :
    ptraces_wf TS → gev_ts TS e = Some ts → (0 < ts)%nat.
  Proof.
    rewrite /gev_ts. intros Hwf Hts.
    destruct (gev_ev TS e) as [ev|] eqn:Hev; simpl in Hts; [|done].
    destruct (gev_step TS e ev Hwf Hev)
      as (T & ag & ag' & st' & f & _ & _ & _ & _ & Hok & _).
    rewrite Hts in Hok. by eapply astep_ok_ts_pos.
  Qed.

  Lemma grf_ts_pos TS e1 e2 ts a :
    ptraces_wf TS → gev_ts TS e1 = Some ts → gev_reads TS e2 a ts →
    (0 < ts)%nat.
  Proof. intros. by eapply gev_ts_pos. Qed.

  (** The AUTHOR of a fulfilled message is the fulfilling agent — the
      fulfil rule matches the promised message EXACTLY, tid included. *)
  Lemma gev_ts_msg TS e ts :
    ptraces_wf TS → gev_ts TS e = Some ts →
    ∃ base data k, pt_log TS !! (ts - 1)%nat = Some (WMsg base data (Some e.1) k).
  Proof.
    rewrite /gev_ts. intros Hwf Hts.
    destruct (gev_ev TS e) as [ev|] eqn:Hev; simpl in Hts; [|done].
    destruct (gev_step TS e ev Hwf Hev)
      as (T & ag & ag' & st' & f & _ & _ & _ & _ & Hok & _).
    rewrite Hts in Hok. by eapply astep_ok_fulfil_msg.
  Qed.

  (** UNIQUENESS of the rf source: two events fulfilling the same
      timestamp are the same event.  Same agent because the message's
      [wm_tid] pins the author; same index by
      [WeakRobustTrace.asteps_fulfil_unique]. *)
  Lemma grf_source_unique TS e1 e2 ts :
    ptraces_wf TS → gev_ts TS e1 = Some ts → gev_ts TS e2 = Some ts →
    e1 = e2.
  Proof.
    intros Hwf H1 H2.
    destruct (gev_ts_msg TS e1 ts Hwf H1) as (b1 & d1 & kc1 & Hm1).
    destruct (gev_ts_msg TS e2 ts Hwf H2) as (b2 & d2 & kc2 & Hm2).
    rewrite Hm1 in Hm2. simplify_eq.
    have Hag : e1.1 = e2.1 by [].
    (* same agent: now the trace-level uniqueness applies *)
    move: H1 H2. rewrite /gev_ts /gev_ev -Hag.
    destruct (pt_trs TS !! e1.1) as [T|] eqn:HT; simpl; [|done].
    destruct (at_evs T !! e1.2) as [ev1|] eqn:Hev1; simpl; [|done].
    destruct (at_evs T !! e2.2) as [ev2|] eqn:Hev2; simpl; [|done].
    intros Hts1 Hts2.
    have Hk : e1.2 = e2.2.
    { eapply (asteps_fulfil_unique pstep pdev (pt_img TS) (pt_log TS) e1.1
                (at_ags T) (at_evs T) ts); [by apply Hwf|done|done|done|done]. }
    destruct e1 as [i1 k1], e2 as [i2 k2]. simpl in Hag, Hk. by subst.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 4 (at the graph level): the own-read lemma *)

  (** Inside ONE agent, an rf edge points FORWARD in trace order — the
      worklist's "an agent can never read its own unfulfilled promise". *)
  Theorem grf_own_lt TS e1 e2 :
    ptraces_wf TS → grf TS e1 e2 → e1.1 = e2.1 → (e1.2 < e2.2)%nat.
  Proof.
    intros Hwf (ts & a & Hts & (l & Hl & Hin)) Hag.
    move: Hts Hl. rewrite /gev_ts /gev_lb /gev_ev Hag.
    destruct (pt_trs TS !! e2.1) as [T|] eqn:HT; simpl; [|done].
    destruct (at_evs T !! e1.2) as [ev1|] eqn:Hev1; simpl; [|done].
    destruct (at_evs T !! e2.2) as [ev2|] eqn:Hev2; simpl; [|done].
    intros Hts Hl. simplify_eq.
    eapply (atrace_own_read (pt_img TS) (pt_log TS) e2.1 T e2.2 e1.2 ev2 ev1 a ts);
      [by apply Hwf|done|done|done|done].
  Qed.

  (** ALL [gdep] edges inside one agent strictly increase the step
      index — po by definition, rf by the own-read lemma. *)
  Lemma gdep_same_agent_lt TS e1 e2 :
    ptraces_wf TS → gdep TS e1 e2 → e1.1 = e2.1 → (e1.2 < e2.2)%nat.
  Proof.
    intros Hwf [(_ & ? & _)|Hrf] Hag; [done|by eapply (grf_own_lt TS)].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 6 (G3): THE DEVICE-ORDER EDGES

      A shared device fabric breaks the replay's freedom to reorder: two
      fabric-touching steps of different agents do not commute, so the
      toposort must keep them in the behavior's own order.  That order is
      the witness [pd_ord DS] ([WeakRobustTrace.pdevs]), and the edges
      that make a topological sort respect it are the SUCCESSOR edges of
      that list — [gdev].

      SUCCESSOR, not the transitive chain, deliberately: the closure
      machinery ([WeakRobustOrd.dc], [WeakRobustMain]'s [anc]) walks
      predecessors one at a time and wants a FINITE, decidable relation;
      the transitive facts are derived here once and for all
      ([gdev_chain]). *)

  (** The graph's event lookup IS the witness's — same [option] monad
      expression, so the two vocabularies need no bridge. *)
  Lemma gev_ev_ev_at TS e : gev_ev TS e = ev_at TS e.
  Proof. done. Qed.

  (** A FABRIC-TOUCHING event: one that carries a recorded fabric pair. *)
  Definition gev_dev TS e : Prop :=
    ∃ ev, gev_ev TS e = Some ev ∧ is_Some (ae_dev ev).

  Global Instance gev_dev_dec TS e : Decision (gev_dev TS e).
  Proof.
    rewrite /gev_dev. destruct (gev_ev TS e) as [ev|] eqn:Hev.
    - destruct (ae_dev ev) as [dd|] eqn:Hdd.
      + left. exists ev. rewrite Hdd. split; [done|by eexists].
      + right. intros (ev' & Hev' & Hs). simplify_eq.
        rewrite Hdd in Hs. by destruct Hs.
    - right. intros (ev' & Hev' & _). by simplify_eq.
  Qed.

  Lemma gev_dev_wf TS e : gev_dev TS e → gev_wf TS e.
  Proof. intros (ev & Hev & _). by exists ev. Qed.

  (** THE GDEV CHAIN. *)
  Definition gdev TS (DS : pdevs D) (e1 e2 : gev) : Prop :=
    ∃ m, pd_ord DS !! m = Some e1 ∧ pd_ord DS !! S m = Some e2.

  Global Instance gdev_dec TS DS e1 e2 : Decision (gdev TS DS e1 e2).
  Proof.
    destruct (decide (Exists
      (λ m, pd_ord DS !! m = Some e1 ∧ pd_ord DS !! S m = Some e2)
      (seq 0 (length (pd_ord DS))))) as [Hex|Hex].
    - left. apply list_relations.Exists_exists in Hex as (m & _ & Hm).
      by exists m.
    - right. intros (m & H1 & H2). apply Hex, list_relations.Exists_exists.
      exists m. split; [|by split].
      apply elem_of_seq. split; [lia|].
      rewrite Nat.add_0_l. by eapply lookup_lt_Some.
  Qed.

  Global Instance gdev_rel_dec TS DS : RelDecision (gdev TS DS).
  Proof. intros e1 e2. apply _. Qed.

  (** Every listed position is a real, fabric-touching event (W1). *)
  Lemma pd_ord_dev TS DS m e :
    ptraces_wit TS DS → pd_ord DS !! m = Some e → gev_dev TS e.
  Proof.
    intros (HW1 & _) Hm. destruct (HW1 m e Hm) as (ev & Hev & Hdd).
    by exists ev.
  Qed.

  Lemma gdev_wf TS DS e1 e2 :
    ptraces_wit TS DS → gdev TS DS e1 e2 → gev_wf TS e1 ∧ gev_wf TS e2.
  Proof.
    intros Hwit (m & H1 & H2).
    split; apply gev_dev_wf; by eapply pd_ord_dev.
  Qed.

  (** THE WITNESS IS DUPLICATE-FREE: (W3) already forbids one agent's
      position from being listed twice, and two entries of the same agent
      are the only way two entries can coincide. *)
  Lemma pd_ord_index_inj TS DS m1 m2 e :
    ptraces_wit TS DS →
    pd_ord DS !! m1 = Some e → pd_ord DS !! m2 = Some e → m1 = m2.
  Proof.
    intros (_ & _ & HW3 & _) H1 H2. destruct e as [i k].
    destruct (Nat.lt_trichotomy m1 m2) as [Hlt|[->|Hgt]]; [|done|].
    - have := HW3 m1 m2 i k k Hlt H1 H2. lia.
    - have := HW3 m2 m1 i k k Hgt H2 H1. lia.
  Qed.

  (** A SAME-AGENT gdev edge IS ALREADY A [gpo] EDGE — (W3) says the
      witness refines each agent's trace order.  So the edges [gdev]
      genuinely ADDS to the graph are the CROSS-agent ones. *)
  Lemma gdev_gpo TS DS e1 e2 :
    ptraces_wit TS DS → gdev TS DS e1 e2 → e1.1 = e2.1 → gpo TS e1 e2.
  Proof.
    intros Hwit Hd Hag.
    destruct (gdev_wf TS DS e1 e2 Hwit Hd) as (Hw1 & Hw2).
    have Hwit' := Hwit. destruct Hwit' as (_ & _ & HW3 & _).
    destruct Hd as (m & H1 & H2).
    destruct e1 as [i1 k1], e2 as [i2 k2]. simpl in Hag. subst i2.
    split_and!; [done| |done|done].
    apply (HW3 m (S m) i1 k1 k2); [lia|exact H1|exact H2].
  Qed.

  (** THE TRANSITIVE FACT, derived once: earlier in the witness means
      [tc gdev]-earlier. *)
  Lemma gdev_chain TS DS m1 m2 e1 e2 :
    pd_ord DS !! m1 = Some e1 → pd_ord DS !! m2 = Some e2 → (m1 < m2)%nat →
    tc (gdev TS DS) e1 e2.
  Proof.
    intros H1 H2 Hlt. remember (m2 - S m1)%nat as d eqn:Hd.
    revert m2 e2 H2 Hlt Hd.
    induction d as [|d IH]; intros m2 e2 H2 Hlt Hd.
    - have Hm2 : m2 = S m1 by lia. subst m2.
      apply tc_once. by exists m1.
    - have [e He] : is_Some (pd_ord DS !! (m2 - 1)%nat).
      { apply lookup_lt_is_Some_2.
        (* NOTE: state the bound with [pd_ord DS] SPELLED OUT — reading it
           off [H2] gives [@length gev], the goal wants
           [@length (agent * nat)], and [lia] does not identify the two
           atoms even though they are convertible. *)
        have Hb : (m2 < length (pd_ord DS))%nat by eapply lookup_lt_Some.
        lia. }
      have Htc : tc (gdev TS DS) e1 e
        by eapply (IH (m2 - 1)%nat e); [exact He|lia|lia].
      eapply tc_r; [exact Htc|]. exists (m2 - 1)%nat. split; [done|].
      by replace (S (m2 - 1))%nat with m2 by lia.
  Qed.

  Lemma gdev_nil TS (d : D) e1 e2 : ¬ gdev TS (PDevs d []) e1 e2.
  Proof. intros (m & H1 & _). by rewrite lookup_nil in H1. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 5: STRUCTURAL ACYCLICITY PIECES *)

  (** (a) The po part embeds into the step index, so po-only paths are
      acyclic. *)
  Lemma gpo_lt TS e1 e2 : gpo TS e1 e2 → (e1.2 < e2.2)%nat.
  Proof. by intros (_ & ? & _). Qed.

  Lemma tc_gpo_lt TS e1 e2 : tc (gpo TS) e1 e2 → (e1.2 < e2.2)%nat.
  Proof.
    induction 1 as [x y Hxy|x y z Hxy _ IH]; apply gpo_lt in Hxy; lia.
  Qed.

  Lemma gpo_acyclic TS e : ¬ tc (gpo TS) e e.
  Proof. intros Hc. apply tc_gpo_lt in Hc. lia. Qed.

  (** (b) SINGLE-AGENT ACYCLICITY: the same-agent fragment of [gdep]
      strictly increases the step index, hence has no cycle. *)
  Definition gdep_sa TS e1 e2 : Prop := gdep TS e1 e2 ∧ e1.1 = e2.1.

  Lemma tc_gdep_sa_lt TS e1 e2 :
    ptraces_wf TS → tc (gdep_sa TS) e1 e2 →
    e1.1 = e2.1 ∧ (e1.2 < e2.2)%nat.
  Proof.
    intros Hwf. induction 1 as [x y [Hxy Hag]|x y z [Hxy Hag] _ IH].
    - split; [done|by eapply (gdep_same_agent_lt TS)].
    - have Hlt : (x.2 < y.2)%nat by eapply (gdep_same_agent_lt TS).
      destruct IH as [Hag' Hlt']. split; [by etrans|lia].
  Qed.

  Lemma gdep_sa_acyclic TS e : ptraces_wf TS → ¬ tc (gdep_sa TS) e e.
  Proof. intros Hwf Hc. apply (tc_gdep_sa_lt TS e e Hwf) in Hc. lia. Qed.

  (** (c) THE NORMAL FORM a cycle analysis wants: a [gdep] path either
      stayed inside ONE agent (and then its step index strictly grew) or
      it crosses agents somewhere — the path splits as
      [rtc gdep · (cross-agent edge) · rtc gdep]. *)
  Lemma tc_gdep_split TS e1 e2 :
    ptraces_wf TS → tc (gdep TS) e1 e2 →
    (e1.1 = e2.1 ∧ (e1.2 < e2.2)%nat) ∨
    (∃ x y, rtc (gdep TS) e1 x ∧ gdep TS x y ∧ x.1 ≠ y.1 ∧
            rtc (gdep TS) y e2).
  Proof.
    intros Hwf. induction 1 as [x y Hxy|x y z Hxy Hyz IH].
    - destruct (decide (x.1 = y.1)) as [Hag|Hne].
      + left. split; [done|by eapply (gdep_same_agent_lt TS)].
      + right. exists x, y. split_and!; [done|done|done|done].
    - destruct (decide (x.1 = y.1)) as [Hag|Hne].
      + have Hlt : (x.2 < y.2)%nat by eapply (gdep_same_agent_lt TS).
        destruct IH as [[Hag' Hlt']|(u & v & Hru & Huv & Hne & Hrv)].
        * left. split; [by etrans|lia].
        * right. exists u, v. split_and!; [|done|done|done].
          eapply rtc_l; [exact Hxy|exact Hru].
      + right. exists x, y. split_and!; [done|done|done|by apply tc_rtc].
  Qed.

  (** Hence: ANY [gdep] cycle contains a CROSS-AGENT edge — and since
      [gpo] is same-agent by definition, that edge is an rf edge.  This
      is the "every potential D-cycle is genuinely cross-agent — the LB
      shape" of the worklist. *)
  Theorem tc_gdep_cross TS e :
    ptraces_wf TS → tc (gdep TS) e e →
    ∃ x y, rtc (gdep TS) e x ∧ grf TS x y ∧ x.1 ≠ y.1 ∧ rtc (gdep TS) y e.
  Proof.
    intros Hwf Hc.
    destruct (tc_gdep_split TS e e Hwf Hc)
      as [[_ Hlt]|(x & y & Hrx & Hxy & Hne & Hry)]; [lia|].
    exists x, y. split_and!; [done| |done|done].
    by destruct Hxy as [(Hag & _)|Hrf].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** rf TOTALITY on a behavior: every read has a source

      A read's timestamp names a log message ([read_ok]); the log at the
      state phase is FROZEN (= [mid]'s log); every logged message is
      authored (the promise rule always stamps [Some i]); and
      [wp_behavior_fulfil_once] turns the author into the UNIQUE trace
      event fulfilling that position.  So a read of a position never
      fulfilled in the behavior cannot occur — it is not assumed. *)

  Definition log_authored (log : list wmsg) : Prop :=
    ∀ p m, log !! p = Some m → is_Some (wm_tid m).

  Lemma log_authored_promise_step c c' :
    log_authored (pc_log c) → wp_promise_step c c' →
    log_authored (pc_log c').
  Proof.
    intros Hla Hs.
    destruct (wp_promise_step_inv c c' Hs)
      as (j & agj & base & data & kc & _ & _ & ->).
    intros p m Hp. simpl in Hp.
    destruct (decide (p < length (pc_log c))%nat) as [Hlt|Hge].
    - rewrite lookup_app_l in Hp; [done|]. by eapply Hla.
    - have Hp' : p = length (pc_log c).
      { apply lookup_lt_Some in Hp. rewrite length_app /= in Hp. lia. }
      subst p. rewrite lookup_app_r in Hp; [lia|].
      rewrite Nat.sub_diag /= in Hp. simplify_eq/=. by eexists.
  Qed.

  Lemma log_authored_promise_run c c' :
    log_authored (pc_log c) → rtc (wp_promise_step (P:=P) (D:=D)) c c' →
    log_authored (pc_log c').
  Proof.
    intros H0 Hr. induction Hr as [|??? Hs _ IH]; [done|].
    apply IH. by eapply log_authored_promise_step.
  Qed.

  Lemma log_authored_init img d0 ps :
    log_authored (pc_log (wp_init (P:=P) (D:=D) img d0 ps)).
  Proof. intros p m Hp. by rewrite /wp_init /= lookup_nil in Hp. Qed.

  (** THE TRACED BEHAVIOR, GRAPH-READY: the traced form plus rf
      totality (every read of a nonzero timestamp has a source) and rf
      functionality (that source is unique). *)
  Theorem wp_behavior_graph img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → wp_behavior pstep img d0 ps c →
    ∃ mid TS,
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid ∧
      ptraces_of pstep TS mid c ∧
      no_promises c ∧
      (** rf TOTALITY *)
      (∀ e a ts, gev_reads TS e a ts → (0 < ts)%nat →
         ∃ e1, gev_ts TS e1 = Some ts ∧ grf TS e1 e) ∧
      (** rf FUNCTIONALITY *)
      (∀ e1 e2 ts, gev_ts TS e1 = Some ts → gev_ts TS e2 = Some ts →
         e1 = e2).
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_fulfil_once pstep pdev img d0 ps c Hpok Hlfp Hb)
      as (mid & TS & Hprom & HTS & Hnp & Hacct).
    have Hwf : ptraces_wf TS by eapply ptraces_of_wf.
    exists mid, TS. split_and!; [done|done|done| |].
    - intros e a ts Hr Hpos.
      destruct ts as [|p]; [lia|].
      destruct (gev_reads_msg TS e a p Hwf Hr) as (m & Hm & Hb').
      have Hlog : pt_log TS = pc_log mid by destruct HTS as (_ & ? & _).
      rewrite Hlog in Hm.
      have Hla : log_authored (pc_log mid).
      { eapply log_authored_promise_run; [apply log_authored_init|done]. }
      destruct (Hla p m Hm) as [i Hi].
      destruct (Hacct p m i Hm Hi) as (T & HT & (k & ev & Hev & Hts) & _).
      exists (i, k). split.
      + rewrite /gev_ts /gev_ev /= HT /= Hev /=. exact Hts.
      + exists (S p), a. split; [|done].
        rewrite /gev_ts /gev_ev /= HT /= Hev /=. exact Hts.
    - intros e1 e2 ts H1 H2. by eapply grf_source_unique.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE ACYCLICITY GOAL (statement only — the coordinator's)

      What W2a step 2's per-class theorem must prove, and what W2b's
      topological sort consumes. *)

  Definition gdep_acyclic TS : Prop := ∀ e, ¬ tc (gdep TS) e e.

  (** The target theorem's SHAPE.  [pf_violation_free] ([WeakRobust]) is
      the SCowned arm's premise — a foreign read of an owned,
      unpublished message exhibits the violation in the promise-free
      prefix under construction.  The SCfenced and SCexcl arms are
      timestamp arithmetic over the classification, and what they need
      of it is not yet fixed; it enters here as the abstract premise
      [class_pins], to be replaced by the coordinator with the concrete
      per-class conjunction (fence: [pr = true] pins every po-earlier
      read below the fenced store's EXT-pinned timestamp; excl: the
      [excl_ok] window plus [ak_latest] value pinning).  Stating the
      goal with the premise abstract keeps this file honest: nothing
      here claims violation-freedom ALONE suffices. *)
  Definition gdep_acyclicity_goal
      (cls : wmsg → store_class) (pub : wpcfg P D → nat → Prop)
      (class_pins : image → list P → Prop) : Prop :=
    ∀ img d0 ps c mid TS,
      lat_free_prog pstep →
      pf_violation_free cls pub pstep pcls img d0 ps →
      class_pins img ps →
      wp_behavior pstep img d0 ps c →
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
      ptraces_of pstep TS mid c →
      gdep_acyclic TS.

  (** What the goal is WORTH, structurally, from this file: by
      [tc_gdep_cross] a counterexample cycle must contain a cross-agent
      rf edge, so the per-class refutation only ever has to look at
      FOREIGN reads of a message — never at an agent reading its own
      write. *)
  Corollary gdep_acyclic_suffices TS :
    ptraces_wf TS →
    (∀ e x y, rtc (gdep TS) e x → grf TS x y → x.1 ≠ y.1 →
              rtc (gdep TS) y e → False) →
    gdep_acyclic TS.
  Proof.
    intros Hwf Href e Hc.
    destruct (tc_gdep_cross TS e Hwf Hc) as (x & y & Hrx & Hxy & Hne & Hry).
    eapply (Href e x y); [exact Hrx|exact Hxy|exact Hne|exact Hry].
  Qed.

End graph.

(** No [Global Arguments] block is needed: [P] is already implicit from the
    section's [Context {P : Type}], and only [ptraces_wf] /
    [gdep_acyclicity_goal] mention [pstep] (which discharge makes their
    first explicit argument, as for [WeakRobustTrace]'s [atrace_wf]).  The
    graph relations themselves — [gpo], [grf], [gdep], [gdep_sa],
    [gdep_acyclic] and the [gev_*] accessors — are pstep-FREE: they are
    functions of the trace bundle alone. *)

(* ------------------------------------------------------------------ *)
(** ** What the per-class theorem (W2a step 2, the coordinator's slice)
       inherits from this file

    - [gdep] and [gdep_acyclic]: the vocabulary and the goal.
    - [wp_behavior_graph]: a lat-free behavior as a bundle of traces
      with rf TOTAL and FUNCTIONAL on it — so "the" source of a read is
      well defined and no read dangles.
    - [grf_own_lt] / [gdep_same_agent_lt]: rf never contradicts po, so
      the graph restricted to one agent is a strict order on step
      indices.
    - [tc_gdep_cross] / [gdep_acyclic_suffices]: a cycle must contain a
      CROSS-AGENT rf edge, which is where the three class arms attach.
    - [gdev] / [gdev_chain] / [gdev_gpo] / [pd_ord_index_inj] /
      [gev_dev]: the device-order edges and their structure — what
      [WeakRobustOrd.gdep3] is built from and what [WeakRobustSim]'s
      fabric fold consumes.
    - [asteps_ws_le] and the [astep_ok_*] facts: the [coh] arithmetic
      the SCfenced/SCexcl arms will re-use (a fulfil demands
      [coh < ts] on every byte of its message; a read pushes [coh] to
      ≥ its timestamp; views only grow).

    NOT here, deliberately: any co/fr edge (the graph is event-level and
    has none — see the header), any use of the classification [cls] or
    the publication [pub], and any topological sort (W2b). *)
