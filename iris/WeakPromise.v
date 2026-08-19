(** * WeakPromise.v — the FULL promising machine (M6 W1, slice 1)

    The native restatement of the Promising-RISC-V machine that
    [claude-notes/projects/weak-memory-m6.md] (W1, decisions D-M6-3/4/5)
    calls for: [WeakMem.v]'s promise-free view machine EXTENDED with
    per-agent promise sets, so that the robustness theorem (W2) can be
    stated inside this tree.  Correspondence to snu-sf/promising-arm
    (@10291375, `Promising.v`) is BY INSPECTION per D-M6-3; every rule
    below cites the PARM rule it mirrors and the deliberate deltas.

    DELIBERATELY DEPENDENCY-FREE, like [WeakMem.v]: stdpp only — no Iris,
    no Sail.  Agents are [nat]s indexing a list (harts AND the disk agent,
    uniformly — D-M6-4); programs are an ABSTRACT per-agent LTS over
    labels, so no toy language enters the statement and the Sail machine
    can instantiate it later (W5).

    THE DELIBERATE DELTAS from PARM (all recorded in the worklist):

    - NO register views and NO [vcap]; a write's fulfil pre-view is
      [fulfil_vpre] = [w_vwNew ⊔ (rl ? w_vrOld ⊔ w_vwOld)], a LOWER BOUND
      of PARM's [joins [view_loc; view_val; vcap; vwn; ifc rel …]]
      (Promising.v:873–881).  Lowering the pre-view only admits MORE
      fulfilments, so this machine is WEAKER than PARM's — the free
      direction for hardware ⊆ model (D-M6-5).
    - NO exclusives bank: the kernel's AMO and the walker's CAS are ONE
      [LRmw] event (read half and write half in one step), carrying
      PARM's store-exclusive window ([Memory.exclusive], Promising.v:886)
      as an explicit no-other-agent-writes side condition [excl_ok].
    - Byte granularity, multi-byte messages: a promise is a whole [wmsg];
      fulfilment must match the promised message EXACTLY (base, data and
      tid) — no partial or split fulfilment.  This is the W1 mixed-size
      decision: a promise/fulfil width mismatch is ruled out by the rule
      itself, so no cross-width crack exists for W2 to worry about.
    - Reads with the [lat] (coherent/latest) kind — ifetch, the walker —
      read the latest message of the WHOLE log, promises included: a
      promoted-but-unfulfilled write-back is visible to another agent's
      walker, which is exactly the early-read surface W2's [SCexcl] arm
      must handle.

    Slice 1 (this file): the machine, its well-formedness invariant, and
    the fused promise+fulfil derivations that make the promise-free
    machine a sub-machine.  Slice 2 (NOT here): the front-loading
    factorization (PARM Thm 7.1's analog) and the erasure bridge to
    [WeakMem]'s machine as instantiated by [WeakLang]/[WeakLitmus]. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Labels: the event alphabet an agent's program emits

    The label carries the memory system's ANSWERS (timestamps and values
    read), so a program's data/control dependencies live in its own step
    relation — the machine never inspects the program state.  Multi-byte
    accesses are contiguous runs based at [base], byte [j] at address
    [base + j], exactly [WeakMem]'s [_run] convention. *)
Inductive wlabel :=
| LSilent
    (** program-internal step: no memory interaction *)
| LLoad (aq lat : bool) (base : Z) (tvs : list (nat * bv 8))
        (asrc : list dsrc)
    (** read [length tvs] bytes; byte [j] reads timestamp [tvs.j.1] with
        value [tvs.j.2].  [aq] = acquire; [lat] = coherent/latest kind
        (ifetch, walker — design doc Decision 6).  [asrc] NAMES the
        registers the ADDRESS was computed from (RVWMO ppo 9); the machine
        looks their views up ([WeakMem.srcs_view]). *)
| LStore (rl : bool) (base : Z) (data : list (bv 8))
         (asrc vsrc : list dsrc)
    (** write [data] at [base]; [rl] = release annotation (inert for the
        kernel, which releases via fences, but kept faithful).  [asrc] /
        [vsrc] name the ADDRESS / DATA dependency sources (RVWMO ppo 9,
        10).  [vsrc] is the deps design's [dsrc] field, renamed because
        [dsrc] is the TYPE of its elements. *)
| LRmw (aq rl : bool) (base : Z) (tvs : list (nat * bv 8))
       (data : list (bv 8)) (asrc vsrc : list dsrc)
    (** the AMO / walker-CAS shape: read half [tvs] and write half [data]
        in ONE event.  The written data is chosen by the program, which
        sees the read values through the label — that is where the
        value dependency of amoswap/CAS lives. *)
| LFence (pr pw sr sw : bool)
| LDev
    (** THE FABRIC MARKER (M5).  A SILENT-EFFECT label: like [LSilent] it
        touches no message log, no [wstate] and no view — its ONLY role is
        to mark a step as fabric-touching, so that [WeakPromiseFact.pdev]
        can decide it.  The instance's [pdev] becomes [λ _ l _, l = LDev].

        WHY A LABEL AND NOT A PREDICATE ON THE PROGRAM STATES.  [pdev] is
        given only [(p, l, p')], and "this silent step read the fabric" is
        NOT a function of that triple: the PLIC wire is a step of the
        TARGET hart's agent whose program transition is indistinguishable
        from an ordinary internal step (design note
        [claude-notes/design/weak-memory-m5.md], "The label [LDev]").
        Marking it in the label is the smallest change that makes the
        distinction decidable.

        EVERYTHING IN LAYER 1 TREATS [LDev] EXACTLY AS [LSilent]: it reads
        nothing, writes nothing, is neither an rf source nor an rf sink,
        carries no fulfil timestamp, and leaves the [wstate] alone.  It is
        NOT a load, so [lat_free]/[ts_oblivious]/[pcls_obl] are unaffected.
        The one thing that distinguishes it is that [pdev] may answer
        [true] on it, and hence that it may carry [ae_dev = Some _]. *)
| LRegW (rd : wreg) (srcs : list dsrc)
    (** THE DEPENDENCY-ONLY REGISTER WRITE (D2): PARM's [step_assign].
        [w_regv[rd] := V(srcs)] and nothing else — no memory, no log, no
        memory view.  Register writes with NO dependency role (CSRs, the
        PC, [minstret], [x0]) stay [LSilent], which UNDER-approximates
        syntactic dependency through CSRs — the safe polarity (D-4). *)
| LCtrl (srcs : list dsrc)
    (** PARM's [Local.control]: a branch or indirect jump resolves and
        [w_vcap ⊔= V(srcs)] (RVWMO ppo 11). *)
| LInstr
    (** Instruction start: [w_ldv := 0], scoping [DLdRes] to one
        instruction.  Carries nothing else. *)
| LExLoad (aq : bool) (base : Z) (tvs : list (nat * bv 8))
          (asrc : list dsrc)
    (** THE EXCLUSIVE READ HALF of the RMW split (design
        [claude-notes/design/weak-memory-rmw-split.md] §2).  Read
        semantics are [LLoad]'s with [lat := false] hardwired — the
        payload is [LLoad]'s minus [lat] — plus, once the machine arms
        land (slice S2), the write of the agent-local reservation
        [WeakMem.w_res]. *)
| LExStore (rl : bool) (base : Z) (data : list (bv 8))
           (asrc vsrc : list dsrc)
    (** THE CONDITIONAL WRITE HALF of the RMW split (design §2/§4).
        Write semantics are [LStore]'s — same payload — plus, at fulfil,
        the per-byte exclusivity window [excl_ok_ts] against the
        reservation set by the matching [LExLoad], and the clearing of
        that reservation. *)
.

(** WHY THE THREE NEW ARMS COME AFTER [LDev] rather than beside the memory
    labels.  Same argument as [LDev]'s own placement (see above): a
    trailing constructor leaves every existing intro pattern's bullet
    ORDER intact, so a downstream script gains three bullets AT THE END
    and nothing above it moves.  The memory arms' new operand fields do
    force every pattern to gain binders, but that is a local edit inside
    one bracket; a REORDERING would be a rewrite of the whole script. *)

(** THE MACHINE ARMS FOR [LDev]: A SEPARATE CONSTRUCTOR PER MACHINE
    ([WPDev] here, [WeakPromiseBridge.PFDev] there), NOT a generalization
    of the silent arm over a predicate [lb_silent l].  Both shapes were
    considered; the arm was chosen because it leaves every EXISTING arm
    byte-identical.

    The alternative — [WPSilent cfg i ag l st' d' : lb_silent l → …] —
    changes the shape of an arm that ~30 downstream proofs invert with an
    explicit intro pattern AND that ~15 sites APPLY as a constructor: each
    inversion pattern would gain two binders, each application an
    argument, and — the real cost — the silent arm's label would become a
    VARIABLE, so every downstream computation that reduces [post_ws],
    [aev_post], [astep_ok], [lat_free] … at the concrete [LSilent] would
    need a case split to get going again.  With a separate arm every
    existing intro pattern and every existing constructor application
    stays valid verbatim; the downstream cost is exactly "+1 arm in the
    pattern, +1 bullet that COPIES the silent one", which is mechanical
    and local.  [LDev] is placed LAST in [wlabel] and [WPDev]/[PFDev] LAST
    in their machines for the same reason: a pattern gains a trailing
    [|…] and a bulleted script gains a trailing bullet, so nothing above
    it moves. *)

(** THE DEPENDENCY-FREE FRAGMENT OF THE LABEL ALPHABET.

    A label is dependency-free when it names NO operands — which is exactly
    the alphabet the machine had before D2, and exactly the alphabet the D2
    event language emits (D3 supplies [deps_of_bits]).  On this fragment
    every [_d] step function collapses to its old instance BY CONVERSION,
    so every statement about the old machine is literally a statement about
    the new one restricted here.

    IT IS USED AS A PREMISE IN ONE PLACE ONLY: the AXIOMATIC PROJECTION
    ([WeakPromiseBridge] part (D)).  [WeakAxiomatic]'s [mstate] steps with
    the dependency-free [load_post_run]/[store_post_run], so a machine step
    that raises a view through an operand list has no [mstep] image with an
    equal post-state — the axiomatic side would first have to gain RVWMO's
    ppo 9–11 (deps design §3, deferred past D2).  The residue is recorded
    there and is VACUOUS for every instance in this tree today. *)
Definition lb_depfree (l : wlabel) : Prop :=
  match l with
  | LSilent | LFence _ _ _ _ | LDev => True
  | LLoad _ _ _ _ asrc => asrc = []
  | LStore _ _ _ asrc vsrc => asrc = [] ∧ vsrc = []
  | LRmw _ _ _ _ _ asrc vsrc => asrc = [] ∧ vsrc = []
  | LRegW _ _ | LCtrl _ | LInstr => False
  | LExLoad _ _ _ asrc => asrc = []
  | LExStore _ _ _ asrc vsrc => asrc = [] ∧ vsrc = []
  end.

(** D3-2: THE WEAKER PIN THE EVENT INSTANCE ACTUALLY SATISFIES.

    Once the event language emits real operand lists, [lb_depfree] is false
    of it — but its LOADS still carry none (deviation D-8: a load's data read
    and the page walker's PTE read are indistinguishable at the node, so
    attaching the base register to a read would be a STRENGTHENING beyond
    RVWMO's syntactic dependencies).  That one pin is all the instance's
    uniform-shape inversion needs, so it gets its own name.

    THE EXCLUSIVE READ IS **NOT** PINNED (RMW split S3).  [LExLoad] is the
    read half of what used to be [LRmw], and [LRmw] was never pinned: an
    exclusive access is unambiguous at the node, so its address operands
    are the instruction's own and the arm is admissible at ITS OWN address
    view (PARM's [Local.read]).  Pinning it — as the additive slice's
    copy-from-[LLoad] did — would silently delete deviation D-2 from every
    AMO and from the walker's A/D update. *)
Definition lb_ldepfree (l : wlabel) : Prop :=
  match l with
  | LLoad _ _ _ _ asrc => asrc = []
  | LSilent | LStore _ _ _ _ _ | LRmw _ _ _ _ _ _ _ | LFence _ _ _ _
  | LDev | LRegW _ _ | LCtrl _ | LInstr
  | LExLoad _ _ _ _ | LExStore _ _ _ _ _ => True
  end.

Lemma lb_depfree_ldepfree l : lb_depfree l → lb_ldepfree l.
Proof. destruct l; simpl; by try (intros ->). Qed.

(** THE FUSED FRAGMENT OF THE LABEL ALPHABET (RMW split S2).

    The nine PRE-SPLIT constructors — the alphabet in which an exclusive
    access is ONE event ([LRmw]).  It is used as a premise in one place
    only: the AXIOMATIC PROJECTION ([WeakPromiseBridge] part (D)), whose
    target [WeakAxiomatic.lbl] is deliberately still fused (design §2:
    its [LRmw] carries [rmw_latest], strictly stronger than [excl_ok], and
    its [mstate] has no per-agent scratch for a two-step reservation).  A
    split pair therefore has no PER-EVENT axiomatic image: the projection
    of a split run is an ERASURE-then-RE-FUSION, which is the A2 track's
    subject and NOT a step-local simulation.  Every instance in this tree
    satisfies the premise today (no producer emits the split labels). *)
Definition lb_fused (l : wlabel) : Prop :=
  match l with
  | LSilent | LLoad _ _ _ _ _ | LStore _ _ _ _ _ | LRmw _ _ _ _ _ _ _
  | LFence _ _ _ _ | LDev | LRegW _ _ | LCtrl _ | LInstr => True
  | LExLoad _ _ _ _ | LExStore _ _ _ _ _ => False
  end.

(* ------------------------------------------------------------------ *)
(** ** Per-agent state and configurations *)

(** [WeakMem.wstate] plus the promise set: the timestamps of this agent's
    appended-but-not-yet-fulfilled messages (PARM [Local.promises]). *)
Record wpagent (P : Type) := WPAgent {
  pa_st   : P;
  pa_ws   : wstate;
  pa_prom : gset nat;
}.
Add Printing Constructor wpagent.
Global Arguments WPAgent {P} _ _ _.
Global Arguments pa_st {P} _.
Global Arguments pa_ws {P} _.
Global Arguments pa_prom {P} _.

(** A configuration has THREE shared components — the era-initial image, the
    write log, and the DEVICE FABRIC [pc_dev] — plus the per-agent records.
    The fabric is an ABSTRACT type parameter [D] here and in every Layer-1
    file: nothing below ever inspects it, exactly as nothing inspects [P].
    (The event language instantiates [D := DevModel.dev_state]; the archived
    per-hart-stream machines instantiate [D := unit], see [pstep_of_pure].) *)
Record wpcfg (P D : Type) := WPCfg {
  pc_img : image;
  pc_log : list wmsg;
  pc_dev : D;
  pc_ags : list (wpagent P);
}.
Add Printing Constructor wpcfg.
Global Arguments WPCfg {P D} _ _ _ _.
Global Arguments pc_img {P D} _.
Global Arguments pc_log {P D} _.
Global Arguments pc_dev {P D} _.
Global Arguments pc_ags {P D} _.

(* ------------------------------------------------------------------ *)
(** ** Side conditions *)

(** The fulfil pre-view.  PARM [writable]'s [view_pre] (Promising.v:873)
    is [view_loc ⊔ view_val ⊔ vcap ⊔ vwn ⊔ (rel_pc ? vro ⊔ vwo)
        ⊔ (ex ∧ riscv ? exbank.view)].  D2 restores TWO of the three
    components D-M6-5 dropped:

      - [w_vcap] joins HERE, in the state-only part, because it is a
        component of the [wstate] and not of the label.  Every consumer
        that discharges [fulfil_vpre _ _ < ts] goes through
        [fulfil_vpre_bounded], which still holds — [ws_bounded] bounds
        [w_vcap] — so no consumer's proof obligation changes shape.
      - [view_loc ⊔ view_val] (and, at an rmw, the exclusive bank's view)
        are LABEL data, so they arrive as the extra argument [vd] of
        [fulfil_vpre_d] / [fulfil_ok_d] below. *)
Definition fulfil_vpre (ws : wstate) (rl : bool) : nat :=
  Nat.max (w_vcap ws)
          (Nat.max (w_vwNew ws)
                   (if rl then Nat.max (w_vrOld ws) (w_vwOld ws) else 0%nat)).

Lemma fulfil_vpre_bounded ws rl n :
  ws_bounded ws n → (fulfil_vpre ws rl ≤ n)%nat.
Proof.
  intros Hb. pose proof (ws_bounded_vcap _ _ Hb) as Hvc.
  destruct Hb as (Hro & Hwo & _ & Hwn & _). rewrite /fulfil_vpre.
  destruct rl; lia.
Qed.

(** The label half.  [vd] is [V(asrc) ⊔ V(dsrc)] — joined with the read
    half's post-view at an rmw (deviation D-2, PARM's [Exbank.view]).
    [0] recovers the dependency-free pre-view BY CONVERSION. *)
Definition fulfil_vpre_d (ws : wstate) (rl : bool) (vd : nat) : nat :=
  Nat.max vd (fulfil_vpre ws rl).

Lemma fulfil_vpre_d_0 ws rl : fulfil_vpre_d ws rl 0%nat = fulfil_vpre ws rl.
Proof. done. Qed.

Lemma fulfil_vpre_d_vwNew ws rl vd : (w_vwNew ws ≤ fulfil_vpre_d ws rl vd)%nat.
Proof. rewrite /fulfil_vpre_d /fulfil_vpre. lia. Qed.

Lemma fulfil_vpre_d_vd ws rl vd : (vd ≤ fulfil_vpre_d ws rl vd)%nat.
Proof. rewrite /fulfil_vpre_d. lia. Qed.

Lemma fulfil_vpre_d_bounded ws rl vd n :
  ws_bounded ws n → (vd ≤ n)%nat → (fulfil_vpre_d ws rl vd ≤ n)%nat.
Proof.
  intros Hb Hvd. pose proof (fulfil_vpre_bounded ws rl n Hb).
  rewrite /fulfil_vpre_d. lia.
Qed.

(** [writes_in_by log Q a lo hi]: some message in the window whose tid
    satisfies [Q] writes byte [a] — [WeakMem.writes_in] refined by author.
    The instance [Q := (≠ Some i)] is PARM's [Memory.exclusive]. *)
Definition writes_in_by (log : list wmsg) (Q : option agent → Prop)
    (a : Z) (lo hi : nat) : Prop :=
  ∃ t : nat, (lo < t)%nat ∧ (t ≤ hi)%nat ∧
             ∃ m, log !! (t - 1)%nat = Some m ∧ is_Some (msg_byte m a) ∧
                  Q (wm_tid m).

Lemma writes_in_by_writes_in log Q a lo hi :
  writes_in_by log Q a lo hi → writes_in log a lo hi.
Proof.
  intros (t & ? & ? & m & ? & ? & ?). exists t. split_and!; [done|done|].
  by exists m.
Qed.

(** The read half of a load/rmw: byte [j] of the run may read [(t, v)].
    [vaddr] is the ADDRESS dependency view [V(asrc)], which PARM's
    [Local.read] joins into [view_pre] (Promising.v:841); the
    dependency-free [read_ok] is this at [vaddr = 0], BY CONVERSION. *)
Definition read_ok_d (img : image) (log : list wmsg) (ws : wstate)
    (aq lat : bool) (base : Z) (tvs : list (nat * bv 8)) (vaddr : nat)
    : Prop :=
  ∀ j t v, tvs !! j = Some (t, v) →
    log_byte img log t (base + Z.of_nat j) = Some v ∧
    readable img log ws (load_vpre_d ws aq vaddr) (base + Z.of_nat j) t ∧
    (lat = true → ¬ writes_in log (base + Z.of_nat j) t (length log)).

Definition read_ok (img : image) (log : list wmsg) (ws : wstate)
    (aq lat : bool) (base : Z) (tvs : list (nat * bv 8)) : Prop :=
  read_ok_d img log ws aq lat base tvs 0%nat.

Lemma read_ok_d_0 img log ws aq lat base tvs :
  read_ok_d img log ws aq lat base tvs 0%nat = read_ok img log ws aq lat base tvs.
Proof. done. Qed.

(** A bigger address view only SHRINKS the admissible set. *)
Lemma read_ok_d_mono img log ws aq lat base tvs va va' :
  (va' ≤ va)%nat → read_ok_d img log ws aq lat base tvs va →
  read_ok_d img log ws aq lat base tvs va'.
Proof.
  intros Hle Hr j t v Hj. destruct (Hr j t v Hj) as (H1 & H2 & H3).
  split_and!; [done| |done]. eapply readable_anti_vpre; [|exact H2].
  rewrite /load_vpre_d. lia.
Qed.

(** The fulfil conditions at timestamp [ts], PARM [writable]
    (Promising.v:864–886) minus the D-M6-5 components:
    COH ([lc.(coh) loc < ts], per byte of the run) and EXT
    ([view_pre < ts]).  The message-match and promise-membership
    conditions live in the step rule itself. *)
Definition fulfil_ok_d (ws : wstate) (rl : bool) (base : Z) (n : nat)
    (ts : nat) (vd : nat) : Prop :=
  (∀ j, (j < n)%nat → (coh ws (base + Z.of_nat j) < ts)%nat) ∧
  (fulfil_vpre_d ws rl vd < ts)%nat.

Definition fulfil_ok (ws : wstate) (rl : bool) (base : Z) (n : nat)
    (ts : nat) : Prop := fulfil_ok_d ws rl base n ts 0%nat.

Lemma fulfil_ok_d_0 ws rl base n ts :
  fulfil_ok_d ws rl base n ts 0%nat = fulfil_ok ws rl base n ts.
Proof. done. Qed.

(** PARM's [Memory.exclusive]: no OTHER agent's write to byte [j] of the
    run lands strictly between the read-half timestamp and [ts]. *)
Definition excl_ok (log : list wmsg) (i : agent) (base : Z)
    (tvs : list (nat * bv 8)) (ts : nat) : Prop :=
  ∀ j t v, tvs !! j = Some (t, v) →
    ¬ writes_in_by log (λ tid, tid ≠ Some i) (base + Z.of_nat j)
        t (ts - 1)%nat.

(** [excl_ok] RESTATED OVER THE RESERVATION'S TIMESTAMP COLUMN ALONE
    (RMW split §4).  [excl_ok] consumes only [tvs.*1] — the value column
    was dead — so the split's reservation ([WeakMem.wresv]) banks just the
    timestamps and the write half checks the same per-byte window
    [(rts_j, ts - 1]] at byte [base + j]. *)
Definition excl_ok_ts (log : list wmsg) (i : agent) (base : Z)
    (rts : list nat) (ts : nat) : Prop :=
  ∀ j t, rts !! j = Some t →
    ¬ writes_in_by log (λ tid, tid ≠ Some i) (base + Z.of_nat j)
        t (ts - 1)%nat.

(** The two agree on a reservation banked from a read's [tvs]. *)
Lemma excl_ok_ts_of_excl_ok log i base tvs ts :
  excl_ok log i base tvs ts → excl_ok_ts log i base tvs.*1 ts.
Proof.
  intros He j t Ht. rewrite list_lookup_fmap in Ht.
  destruct (tvs !! j) as [[t' v]|] eqn:Hj; simplify_eq/=.
  by eapply He.
Qed.

(** *** THE CONDITIONAL WRITE'S WHOLE SIDE CONDITION, AS ONE PREDICATE —
    AND AS A BOOLEAN (RMW split §4/§5).

    [exwin_ok log i ws base n ts] is exactly what [WPExStore] /
    [WeakPromiseBridge.PFExStore] ask of the agent besides [data ≠ []]:
    a matching reservation of the right width whose per-byte window is
    still clean at [ts].  Naming it once is what lets the event language's
    side condition ([WeakEvInst.elab_ok]) and the uniform pf side condition
    ([WeakEvCapstone.pf_ok]) be the SAME text as the machine arm.

    THE BOOLEAN IS NOT A CONVENIENCE: design §5's RETRY ARM splits the
    event language's conditional-write node on "is the window still
    clean?", and a WP rule for that node must DECIDE the question at the
    node's own σ before it may open the caller's callback (the mask goes
    ⊤→∅ once, ahead of the step).  [writes_in_by] is a bounded existential
    over the log with a decidable body, so the decision is a computation —
    [WeakMem.writes_inb]'s pattern, refined by author. *)
Definition writes_in_byb (log : list wmsg) (i : agent) (a : Z) (lo hi : nat)
    : bool :=
  existsb (λ t, bool_decide (lo < t)%nat && bool_decide (t ≤ hi)%nat &&
                match log !! (t - 1)%nat with
                | Some m => msg_writesb m a && bool_decide (wm_tid m ≠ Some i)
                | None => false
                end)
          (seq 1 (length log)).

Lemma writes_in_byb_spec log i a lo hi :
  writes_in_by log (λ tid, tid ≠ Some i) a lo hi
  ↔ writes_in_byb log i a lo hi = true.
Proof.
  rewrite /writes_in_byb existsb_exists. split.
  - intros (t & Hlo & Hhi & m & Hm & Hs & HQ).
    pose proof (lookup_lt_Some _ _ _ Hm) as Hlt.
    exists t. split.
    + apply elem_of_list_In, elem_of_seq. lia.
    + rewrite Hm. rewrite !andb_true_iff. split_and!.
      * by apply bool_decide_eq_true_2.
      * by apply bool_decide_eq_true_2.
      * by apply msg_writesb_true.
      * by apply bool_decide_eq_true_2.
  - intros (t & Ht & Hb). apply elem_of_list_In, elem_of_seq in Ht.
    rewrite !andb_true_iff in Hb. destruct Hb as [[H1 H2] H3].
    apply bool_decide_eq_true_1 in H1. apply bool_decide_eq_true_1 in H2.
    destruct (log !! (t - 1)%nat) as [m|] eqn:Hm; [|done].
    rewrite andb_true_iff in H3. destruct H3 as [H3 H4].
    apply msg_writesb_true in H3. apply bool_decide_eq_true_1 in H4.
    exists t. split_and!; [done|done|]. by exists m.
Qed.

Definition excl_ok_tsb (log : list wmsg) (i : agent) (base : Z)
    (rts : list nat) (ts : nat) : bool :=
  forallb (λ j, match rts !! j with
                | Some t =>
                    negb (writes_in_byb log i (base + Z.of_nat j) t (ts - 1)%nat)
                | None => true
                end)
          (seq 0 (length rts)).

Lemma excl_ok_tsb_spec log i base rts ts :
  excl_ok_ts log i base rts ts ↔ excl_ok_tsb log i base rts ts = true.
Proof.
  rewrite /excl_ok_ts /excl_ok_tsb forallb_forall. split.
  - intros He j Hj. apply elem_of_list_In, elem_of_seq in Hj.
    destruct (rts !! j) as [t|] eqn:Ht; [|done].
    rewrite negb_true_iff. apply not_true_is_false.
    rewrite -writes_in_byb_spec. by eapply He.
  - intros Hb j t Ht Hw.
    have Hj : In j (seq 0 (length rts)).
    { apply elem_of_list_In, elem_of_seq.
      pose proof (lookup_lt_Some _ _ _ Ht). lia. }
    pose proof (Hb j Hj) as Hbj. rewrite Ht negb_true_iff in Hbj.
    apply writes_in_byb_spec in Hw. by rewrite Hw in Hbj.
Qed.

Definition exwin_ok (log : list wmsg) (i : agent) (ws : wstate) (base : Z)
    (n : nat) (ts : nat) : Prop :=
  ∃ R, w_res ws = Some R ∧ rv_base R = base ∧ length (rv_ts R) = n ∧
       excl_ok_ts log i base (rv_ts R) ts.

Definition exwin_okb (log : list wmsg) (i : agent) (ws : wstate) (base : Z)
    (n : nat) (ts : nat) : bool :=
  match w_res ws with
  | Some R => bool_decide (rv_base R = base) &&
              bool_decide (length (rv_ts R) = n) &&
              excl_ok_tsb log i base (rv_ts R) ts
  | None => false
  end.

Lemma exwin_okb_spec log i ws base n ts :
  exwin_ok log i ws base n ts ↔ exwin_okb log i ws base n ts = true.
Proof.
  rewrite /exwin_ok /exwin_okb. split.
  - intros (R & HR & Hb & Hl & He). rewrite HR !andb_true_iff. split_and!.
    + by apply bool_decide_eq_true_2.
    + by apply bool_decide_eq_true_2.
    + by apply excl_ok_tsb_spec.
  - destruct (w_res ws) as [R|] eqn:HR; [|done].
    rewrite !andb_true_iff. intros [[H1 H2] H3].
    apply bool_decide_eq_true_1 in H1. apply bool_decide_eq_true_1 in H2.
    exists R. split_and!; [done|done|done|by apply excl_ok_tsb_spec].
Qed.

Lemma exwin_okb_false log i ws base n ts :
  exwin_okb log i ws base n ts = false → ¬ exwin_ok log i ws base n ts.
Proof.
  intros Hf Hok. apply exwin_okb_spec in Hok. by rewrite Hok in Hf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The side conditions under an end-extension of the log, and the
       singleton collapse

    (Lifted from [WeakPromiseFact]/[WeakPromiseLitmus] by the W4 batch: they
    are statements about [read_ok]/[excl_ok]/[writes_in_by], all of which are
    defined right above, so this is their home.) *)

(** The [writes_in_by] analog of [WeakMem.writes_in_app_inv]. *)
Lemma writes_in_by_app_inv log l Q a lo hi :
  (hi ≤ length log)%nat →
  writes_in_by (log ++ l) Q a lo hi → writes_in_by log Q a lo hi.
Proof.
  intros Hle (t & Hlo & Hhi & m & Hm & Hb & HQ).
  rewrite lookup_app_l in Hm; [lia|].
  exists t. split_and!; [done|done|]. exists m. done.
Qed.

(** A PLAIN (non-latest) read is stable under appending: the value it
    reads is at an old timestamp ([log_byte_app]) and its coherence
    window is bounded by the reader's views, which [ws_bounded] pins at
    or below the old log length — strictly below the new message. *)
Lemma read_ok_d_app img log l ws aq base tvs va :
  ws_bounded ws (length log) → (va ≤ length log)%nat →
  read_ok_d img log ws aq false base tvs va →
  read_ok_d img (log ++ l) ws aq false base tvs va.
Proof.
  intros Hb Hva Hr j t v Htv.
  destruct (Hr j t v Htv) as (Hlb & [Hs Hn] & _).
  have Ht : (t ≤ length log)%nat by eapply log_byte_bounded; eexists.
  split_and!.
  - rewrite log_byte_app //.
  - split; [rewrite log_byte_app //|].
    intros Hw. apply Hn. eapply writes_in_app_inv; [|done].
    pose proof (load_vpre_d_bounded ws aq va _ Hb Hva) as Hv.
    destruct Hb as (_&_&_&_&_&_&Hcoh&_).
    pose proof (Hcoh (base + Z.of_nat j)). lia.
  - done.
Qed.

Lemma read_ok_app img log l ws aq base tvs :
  ws_bounded ws (length log) →
  read_ok img log ws aq false base tvs →
  read_ok img (log ++ l) ws aq false base tvs.
Proof. intros Hb. apply read_ok_d_app; [done|lia]. Qed.

(** The exclusivity window [(t, ts-1]] of an rmw ends at [ts - 1], and
    [ts] is a promised timestamp, hence at most the old log length. *)
Lemma excl_ok_app log l i base tvs ts :
  (ts - 1 ≤ length log)%nat →
  excl_ok log i base tvs ts → excl_ok (log ++ l) i base tvs ts.
Proof.
  intros Hle He j t v Htv Hw. eapply He; [done|].
  by eapply writes_in_by_app_inv.
Qed.

(** [excl_ok_app] for the reservation form. *)
Lemma excl_ok_ts_app log l i base rts ts :
  (ts - 1 ≤ length log)%nat →
  excl_ok_ts log i base rts ts → excl_ok_ts (log ++ l) i base rts ts.
Proof.
  intros Hle He j t Ht Hw. eapply He; [done|].
  by eapply writes_in_by_app_inv.
Qed.

(** A single-byte [read_ok]: [read_ok]'s [∀ j] collapses to [j = 0], where
    the byte address [base + 0] is [base]. *)
Lemma read_ok_single img log ws base t v :
  log_byte img log t base = Some v →
  readable img log ws (load_vpre ws false) base t →
  read_ok img log ws false false base [(t, v)].
Proof.
  intros Hv Hr j t' v' Hj.
  destruct j as [|j]; [|by simplify_eq/=].
  simplify_eq/=. rewrite Z.add_0_r. split_and!; [done|done|done].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The machine *)

Section machine.
  Context {P D : Type}.
  (** The abstract per-agent program: [pstep p d l p' d'] — in state [p],
      with the shared device fabric at [d], the program can emit label [l]
      and continue as [p'] with the fabric moved to [d'].  All dependency
      structure (what the program does with values it read) lives here, and
      so does every device access: a step may READ and MOVE the fabric.

      THE GENERAL FORM IS DELIBERATE.  All five state rules thread the
      fabric, including the memory-labeled ones — a single program step may
      well be both an MMIO access and (in another instantiation) a memory
      event, and nothing in the machine needs the restriction.  The event
      language's instance moves the fabric only on device-access SILENT
      steps, which is the special case [pdev]-marked in
      [WeakPromiseFact]. *)
  Context (pstep : P → D → wlabel → P → D → Prop).

  Implicit Types cfg : wpcfg P D.

  (** One machine step.  [WPPromise] is PARM's [promise_step]
      (unconditional, program does not move, Promising.v:798); every
      other rule is a [state_step] arm.  A plain (non-promised) store
      does not exist as a primitive: it is promise-then-fulfil, exactly
      as in PARM — see [wpstep_store_now] below for the fused form. *)
  Inductive wpstep : wpcfg P D → wpcfg P D → Prop :=
  | WPPromise cfg i ag base data k :
      pc_ags cfg !! i = Some ag →
      data ≠ [] →
      wpstep cfg
        (WPCfg (pc_img cfg)
               (pc_log cfg ++ [WMsg base data (Some i) k])
               (pc_dev cfg)
               (<[i := WPAgent (pa_st ag) (pa_ws ag)
                         ({[S (length (pc_log cfg))]} ∪ pa_prom ag)]>
                  (pc_ags cfg)))
  | WPSilent cfg i ag st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) LSilent st' d' →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags cfg)))
  | WPLoad cfg i ag aq lat base tvs asrc st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (LLoad aq lat base tvs asrc) st' d' →
      read_ok_d (pc_img cfg) (pc_log cfg) (pa_ws ag) aq lat base tvs
                (srcs_view (pa_ws ag) asrc) →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (load_post_run_d (pa_ws ag) aq
                            (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                         (pa_prom ag)]> (pc_ags cfg)))
  | WPFulfil cfg i ag rl base data asrc vsrc k ts st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (LStore rl base data asrc vsrc) st' d' →
      ts ∈ pa_prom ag →
      pc_log cfg !! (ts - 1)%nat = Some (WMsg base data (Some i) k) →
      fulfil_ok_d (pa_ws ag) rl base (length data) ts
                  (Nat.max (srcs_view (pa_ws ag) asrc)
                           (srcs_view (pa_ws ag) vsrc)) →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (store_post_run_d (pa_ws ag) rl
                            (srcs_view (pa_ws ag) asrc)
                            (srcs_view (pa_ws ag) vsrc)
                            base (length data) ts)
                         (pa_prom ag ∖ {[ts]})]> (pc_ags cfg)))
  | WPRmw cfg i ag aq rl base tvs data asrc vsrc k ts st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (LRmw aq rl base tvs data asrc vsrc)
            st' d' →
      length tvs = length data →
      ts ∈ pa_prom ag →
      pc_log cfg !! (ts - 1)%nat = Some (WMsg base data (Some i) k) →
      read_ok_d (pc_img cfg) (pc_log cfg) (pa_ws ag) aq false base tvs
                (srcs_view (pa_ws ag) asrc) →
      excl_ok (pc_log cfg) i base tvs ts →
      fulfil_ok_d (load_post_run_d (pa_ws ag) aq (srcs_view (pa_ws ag) asrc)
                     base (tvs.*1))
                  rl base (length data) ts
                  (Nat.max (Nat.max (srcs_view (pa_ws ag) asrc)
                                    (srcs_view (pa_ws ag) vsrc))
                           (ldv_of (pa_ws ag) aq (srcs_view (pa_ws ag) asrc)
                              base (tvs.*1))) →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (store_post_run_d
                            (load_post_run_d (pa_ws ag) aq
                               (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                            rl (srcs_view (pa_ws ag) asrc)
                            (srcs_view (pa_ws ag) vsrc)
                            base (length data) ts)
                         (pa_prom ag ∖ {[ts]})]> (pc_ags cfg)))
  | WPFence cfg i ag pr pw sr sw st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (LFence pr pw sr sw) st' d' →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (fence_post (pa_ws ag) pr pw sr sw)
                         (pa_prom ag)]> (pc_ags cfg)))
  (** [WPSilent]'s twin at the fabric marker: the SAME configuration
      update, the SAME (absent) side conditions.  Only the label differs,
      and only [pdev] reads it. *)
  | WPDev cfg i ag st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) LDev st' d' →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (pa_ws ag) (pa_prom ag)]> (pc_ags cfg)))
  (** THE THREE DEPENDENCY-ONLY ARMS (D2).  Each is [WPSilent] with a
      different [wstate] update: no log, no promise set, no side
      condition — the views they move are computed from the label's
      NAMES and the agent's own state. *)
  | WPRegW cfg i ag rd srcs st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (LRegW rd srcs) st' d' →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (regw_post (pa_ws ag) rd
                            (srcs_view (pa_ws ag) srcs))
                         (pa_prom ag)]> (pc_ags cfg)))
  | WPCtrl cfg i ag srcs st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (LCtrl srcs) st' d' →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (ctrl_post (pa_ws ag) (srcs_view (pa_ws ag) srcs))
                         (pa_prom ag)]> (pc_ags cfg)))
  | WPInstr cfg i ag st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) LInstr st' d' →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st' (instr_post (pa_ws ag))
                         (pa_prom ag)]> (pc_ags cfg)))
  (** THE RMW SPLIT (S2), the two halves.

      [WPExLoad] is [WPLoad]'s arm at [lat := false] — the exclusive read
      is never latest-indexed (design §2) — plus the agent-local
      reservation, which [exload_post_run_d] writes SUPERSEDING whatever
      [w_res] held.  It is a STATE step: no log, no promise set. *)
  | WPExLoad cfg i ag aq base tvs asrc st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (LExLoad aq base tvs asrc) st' d' →
      read_ok_d (pc_img cfg) (pc_log cfg) (pa_ws ag) aq false base tvs
                (srcs_view (pa_ws ag) asrc) →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (exload_post_run_d (pa_ws ag) aq
                            (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                         (pa_prom ag)]> (pc_ags cfg)))
  (** [WPExStore] is [WPFulfil]'s arm plus the RESERVATION (design §4):

      - the agent MUST hold a matching reservation ([w_res = Some R] with
        [rv_base R = base] and the widths agreeing).  There is NO
        plain-store fallback: a partnerless conditional write has no arm at
        all, which is sound because the promising machine carries no
        totality obligation and the model never produces the case.
      - the ATOMICITY WINDOW moves here: [excl_ok_ts] checks, per byte,
        that no OTHER agent wrote between the reservation's timestamp and
        [ts].  The clear-on-own-store rule (see [store_post_d]) is what
        rules out the SAME agent's intervening writes.
      - EXT gains [rv_view R], the read half's banked post-view — deviation
        D-2, PARM's [Exbank.view] contribution, which the fused [WPRmw]
        supplied as [ldv_of].
      - the fulfil CLEARS the reservation; that is already what
        [store_post_run_d] does (per byte, in [store_post_d]). *)
  | WPExStore cfg i ag rl base data asrc vsrc k ts R st' d' :
      pc_ags cfg !! i = Some ag →
      pstep (pa_st ag) (pc_dev cfg) (LExStore rl base data asrc vsrc) st' d' →
      ts ∈ pa_prom ag →
      pc_log cfg !! (ts - 1)%nat = Some (WMsg base data (Some i) k) →
      w_res (pa_ws ag) = Some R →
      rv_base R = base →
      length (rv_ts R) = length data →
      excl_ok_ts (pc_log cfg) i base (rv_ts R) ts →
      fulfil_ok_d (pa_ws ag) rl base (length data) ts
                  (Nat.max (Nat.max (srcs_view (pa_ws ag) asrc)
                                    (srcs_view (pa_ws ag) vsrc))
                           (rv_view R)) →
      wpstep cfg
        (WPCfg (pc_img cfg) (pc_log cfg) d'
               (<[i := WPAgent st'
                         (store_post_run_d (pa_ws ag) rl
                            (srcs_view (pa_ws ag) asrc)
                            (srcs_view (pa_ws ag) vsrc)
                            base (length data) ts)
                         (pa_prom ag ∖ {[ts]})]> (pc_ags cfg))).

  (* ---------------------------------------------------------------- *)
  (** ** Initial configurations and behaviors *)

  Definition wp_init (img : image) (d0 : D) (ps : list P) : wpcfg P D :=
    WPCfg img [] d0 (map (λ p, WPAgent p ws_init ∅) ps).

  (** All promises discharged — PARM [Machine.no_promise]
      (Promising.v:1576). *)
  Definition no_promises cfg : Prop :=
    ∀ i ag, pc_ags cfg !! i = Some ag → pa_prom ag = ∅.

  (** A BEHAVIOR — PARM [Machine.exec] (Promising.v:1750): a reachable
      configuration whose every promise set is empty.  Doomed runs
      (undischargeable promises) are model artifacts pruned here, which
      is why full-machine adequacy quantifies over completable prefixes
      (design doc §2 consequence (a)). *)
  Definition wp_behavior (img : image) (d0 : D) (ps : list P) cfg : Prop :=
    rtc wpstep (wp_init img d0 ps) cfg ∧ no_promises cfg.

  (* ---------------------------------------------------------------- *)
  (** ** Well-formedness: the machine invariant

      Views are real timestamps ([ws_bounded], as in the promise-free
      machine) and every promised timestamp names a real log message by
      the promising agent.  Slice 2's factorization commutes promise
      steps forward through OTHER agents' steps; both commutations lean
      on exactly these bounds. *)

  Definition prom_wf (log : list wmsg) (i : agent) (ag : wpagent P)
      : Prop :=
    ∀ ts, ts ∈ pa_prom ag →
      (0 < ts)%nat ∧ (ts ≤ length log)%nat ∧
      ∃ m, log !! (ts - 1)%nat = Some m ∧ wm_tid m = Some i.

  Definition cfg_wf cfg : Prop :=
    ∀ i ag, pc_ags cfg !! i = Some ag →
      ws_bounded (pa_ws ag) (length (pc_log cfg)) ∧
      prom_wf (pc_log cfg) i ag.

  Lemma cfg_wf_init img d0 ps : cfg_wf (wp_init img d0 ps).
  Proof.
    intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
    destruct (ps !! i) as [p|]; simplify_eq/=.
    split; [apply ws_bounded_init|]. intros ts Hts. set_solver.
  Qed.

  (** Every read timestamp a [read_ok] admits is a real log position —
      the [Forall] shape [load_post_run_bounded] wants. *)
  Lemma read_ok_d_ts_bounded img log ws aq lat base tvs va :
    read_ok_d img log ws aq lat base tvs va →
    Forall (λ t, (t ≤ length log)%nat) (tvs.*1).
  Proof.
    intros Hr. apply Forall_lookup_2. intros j t Hj.
    rewrite list_lookup_fmap in Hj.
    destruct (tvs !! j) as [[t' v]|] eqn:Htv; simplify_eq/=.
    destruct (Hr j t v Htv) as (Hb & _ & _).
    eapply log_byte_bounded. by eexists.
  Qed.

  Lemma read_ok_ts_bounded img log ws aq lat base tvs :
    read_ok img log ws aq lat base tvs →
    Forall (λ t, (t ≤ length log)%nat) (tvs.*1).
  Proof. apply read_ok_d_ts_bounded. Qed.

  Lemma cfg_wf_step cfg cfg' : cfg_wf cfg → wpstep cfg cfg' → cfg_wf cfg'.
  Proof.
    intros Hwf Hstep. destruct Hstep.
    - (* promise: log grows by one; the new promise names the new top *)
      intros i' ag' Hlk'. simpl in *.
      rewrite length_app /=.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|]. split.
        { eapply ws_bounded_mono; [done|lia]. }
        intros ts Hts. simpl in Hts.
        apply elem_of_union in Hts as [->%elem_of_singleton|Hts].
        * rewrite length_app /=. split_and!; [lia|lia|].
          eexists. split; [apply list_lookup_middle; lia|done].
        * destruct (Hp ts Hts) as (?&?&m&Hm&?).
          rewrite length_app /=. split_and!; [done|lia|].
          exists m. split; [|done].
          rewrite lookup_app_l //. apply lookup_lt_Some in Hm. lia.
      + rewrite list_lookup_insert_ne // in Hlk'.
        destruct (Hwf i' ag') as [Hb Hp]; [done|]. split.
        { eapply ws_bounded_mono; [done|lia]. }
        intros ts Hts. destruct (Hp ts Hts) as (?&?&m&Hm&?).
        rewrite length_app /=. split_and!; [done|lia|].
        exists m. split; [|done].
        rewrite lookup_app_l //. apply lookup_lt_Some in Hm. lia.
    - (* silent *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        by destruct (Hwf i ag).
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* load *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|]. split; [|done].
        apply load_post_run_d_bounded;
          [done|by apply srcs_view_bounded|by eapply read_ok_d_ts_bounded].
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* fulfil *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|].
        destruct (Hp ts) as (?&?&_); [done|]. split.
        { eapply store_post_run_d_bounded; [done|lia|lia| |];
            by apply srcs_view_bounded. }
        intros ts' Hts'. simpl in Hts'. apply Hp. set_solver.
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* rmw *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|].
        destruct (Hp ts) as (?&?&_); [done|].
        have Hva : (srcs_view (pa_ws ag) asrc ≤ length (pc_log cfg))%nat
          by apply srcs_view_bounded.
        have Hvd : (srcs_view (pa_ws ag) vsrc ≤ length (pc_log cfg))%nat
          by apply srcs_view_bounded.
        split.
        { eapply store_post_run_d_bounded;
            [apply load_post_run_d_bounded;
               [done|exact Hva|by eapply read_ok_d_ts_bounded]
            |lia|lia|lia|lia]. }
        intros ts' Hts'. simpl in Hts'. apply Hp. set_solver.
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* fence *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|]. split; [|done].
        by apply fence_post_bounded.
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* dev: [WPSilent]'s twin *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        by destruct (Hwf i ag).
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* regw *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|]. split; [|done].
        apply regw_post_bounded; [done|by apply srcs_view_bounded].
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* ctrl *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|]. split; [|done].
        apply ctrl_post_bounded; [done|by apply srcs_view_bounded].
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* instr *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|]. split; [|done].
        by apply instr_post_bounded.
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* THE RMW SPLIT (S2): exclusive load — [WPLoad]'s arm through
         [exload_post_run_d_bounded], whose extra obligation is the
         reservation's own boundedness (the same [Forall] on [tvs.*1]). *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|]. split; [|done].
        apply exload_post_run_d_bounded;
          [done|by apply srcs_view_bounded|by eapply read_ok_d_ts_bounded].
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
    - (* THE RMW SPLIT (S2): conditional write — [WPFulfil]'s arm verbatim *)
      intros i' ag' Hlk'. simpl in *.
      destruct (decide (i' = i)) as [->|Hne].
      + rewrite list_lookup_insert in Hlk';
          [by eapply lookup_lt_Some|simplify_eq/=].
        destruct (Hwf i ag) as [Hb Hp]; [done|].
        destruct (Hp ts) as (?&?&_); [done|]. split.
        { eapply store_post_run_d_bounded; [done|lia|lia| |];
            by apply srcs_view_bounded. }
        intros ts' Hts'. simpl in Hts'. apply Hp. set_solver.
      + rewrite list_lookup_insert_ne // in Hlk'. by apply Hwf.
  Qed.

  Lemma cfg_wf_reach cfg cfg' :
    cfg_wf cfg → rtc wpstep cfg cfg' → cfg_wf cfg'.
  Proof.
    intros H0 Hr. induction Hr as [|??? Hs ? IH]; [done|].
    apply IH. by eapply cfg_wf_step.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** The fused promise+fulfil derivations

      The promise-free machine's store IS these two steps back to back:
      append at the fresh top, fulfil immediately.  [EXT] and [COH] hold
      by construction there — every view is bounded by the log the store
      tops — which is exactly why the promise-free store rule has no
      side condition ([WeakMem]'s "the store rule has no admissibility
      condition to check").  These lemmas are the promise-free ⊆ full
      inclusion, stated one rule at a time; slice 2's bridge composes
      them into a machine-level embedding. *)

  Lemma wpstep_store_now cfg i ag rl base data asrc vsrc k st' d' :
    pc_ags cfg !! i = Some ag →
    pstep (pa_st ag) (pc_dev cfg) (LStore rl base data asrc vsrc) st' d' →
    data ≠ [] →
    ws_bounded (pa_ws ag) (length (pc_log cfg)) →
    S (length (pc_log cfg)) ∉ pa_prom ag →
    rtc wpstep cfg
      (WPCfg (pc_img cfg)
             (pc_log cfg ++ [WMsg base data (Some i) k])
             d'
             (<[i := WPAgent st'
                       (store_post_run_d (pa_ws ag) rl
                          (srcs_view (pa_ws ag) asrc)
                          (srcs_view (pa_ws ag) vsrc)
                          base (length data)
                          (S (length (pc_log cfg))))
                       (pa_prom ag)]> (pc_ags cfg))).
  Proof.
    intros Hlk Hp Hnn Hb Hfresh.
    pose proof (lookup_lt_Some _ _ _ Hlk) as Hlen.
    set ts := S (length (pc_log cfg)).
    (* step 1: promise the message at the fresh top *)
    eapply rtc_l.
    { by eapply (WPPromise cfg i ag base data k). }
    (* step 2: fulfil it immediately *)
    set mid := WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i) k])
                 (pc_dev cfg)
                 (<[i := WPAgent (pa_st ag) (pa_ws ag)
                           ({[ts]} ∪ pa_prom ag)]> (pc_ags cfg)).
    eapply rtc_l; [|apply rtc_refl].
    have Hmidlk : pc_ags mid !! i
                  = Some (WPAgent (pa_st ag) (pa_ws ag) ({[ts]} ∪ pa_prom ag)).
    { rewrite /mid /= list_lookup_insert //. }
    have Hmsg : pc_log mid !! (ts - 1)%nat = Some (WMsg base data (Some i) k).
    { rewrite /mid /=. apply list_lookup_middle. rewrite /ts. lia. }
    have Hpd : pstep (pa_st ag) (pc_dev mid) (LStore rl base data asrc vsrc)
                 st' d' by rewrite /mid /=.
    pose proof (WPFulfil mid i _ rl base data asrc vsrc k ts st' d' Hmidlk Hpd
                  ltac:(set_solver) Hmsg) as Hful.
    have Hok : fulfil_ok_d (pa_ws ag) rl base (length data) ts
                 (Nat.max (srcs_view (pa_ws ag) asrc)
                          (srcs_view (pa_ws ag) vsrc)).
    { split.
      - intros j Hj. destruct Hb as (_&_&_&_&_&_&Hcoh&_).
        pose proof (Hcoh (base + Z.of_nat j)). rewrite /ts. lia.
      - have Hvdb : (Nat.max (srcs_view (pa_ws ag) asrc)
                              (srcs_view (pa_ws ag) vsrc)
                     ≤ length (pc_log cfg))%nat.
        { pose proof (srcs_view_bounded (pa_ws ag) _ asrc Hb).
          pose proof (srcs_view_bounded (pa_ws ag) _ vsrc Hb). lia. }
        pose proof (fulfil_vpre_d_bounded _ rl _ _ Hb Hvdb).
        rewrite /ts. lia. }
    specialize (Hful Hok).
    (* the two agent-list inserts collapse; the promise set returns *)
    rewrite /mid /= in Hful.
    have Hprom : ({[ts]} ∪ pa_prom ag) ∖ {[ts]} = pa_prom ag by set_solver.
    rewrite Hprom list_insert_insert in Hful.
    exact Hful.
  Qed.

  (** The rmw sibling of [wpstep_store_now] (lifted from
      [WeakPromiseBridge] by the W4 batch), proved the same way: the read
      half and the exclusivity window survive the append because the read is
      plain and the window ends at the old top. *)
  Lemma wpstep_rmw_now cfg i ag aq rl base tvs data asrc vsrc k st' d' :
    pc_ags cfg !! i = Some ag →
    pstep (pa_st ag) (pc_dev cfg) (LRmw aq rl base tvs data asrc vsrc)
          st' d' →
    data ≠ [] →
    length tvs = length data →
    ws_bounded (pa_ws ag) (length (pc_log cfg)) →
    S (length (pc_log cfg)) ∉ pa_prom ag →
    read_ok_d (pc_img cfg) (pc_log cfg) (pa_ws ag) aq false base tvs
              (srcs_view (pa_ws ag) asrc) →
    excl_ok (pc_log cfg) i base tvs (S (length (pc_log cfg))) →
    rtc wpstep cfg
      (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i) k])
             d'
             (<[i := WPAgent st'
                       (store_post_run_d
                          (load_post_run_d (pa_ws ag) aq
                             (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                          rl (srcs_view (pa_ws ag) asrc)
                          (srcs_view (pa_ws ag) vsrc)
                          base (length data) (S (length (pc_log cfg))))
                       (pa_prom ag)]> (pc_ags cfg))).
  Proof.
    intros Hlk Hps Hnn Hlen Hb Hfresh Hr He.
    have Hva : (srcs_view (pa_ws ag) asrc ≤ length (pc_log cfg))%nat
      by apply srcs_view_bounded.
    have Hvd : (srcs_view (pa_ws ag) vsrc ≤ length (pc_log cfg))%nat
      by apply srcs_view_bounded.
    pose proof (lookup_lt_Some _ _ _ Hlk) as Hlt.
    set ts := S (length (pc_log cfg)).
    (* step 1: promise the message at the fresh top *)
    eapply rtc_l.
    { by eapply (WPPromise cfg i ag base data k). }
    set mid := WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i) k])
                 (pc_dev cfg)
                 (<[i := WPAgent (pa_st ag) (pa_ws ag)
                           ({[ts]} ∪ pa_prom ag)]> (pc_ags cfg)).
    eapply rtc_l; [|apply rtc_refl].
    have Hmidlk : pc_ags mid !! i
                  = Some (WPAgent (pa_st ag) (pa_ws ag) ({[ts]} ∪ pa_prom ag)).
    { rewrite /mid /= list_lookup_insert //. }
    have Hmsg : pc_log mid !! (ts - 1)%nat
                = Some (WMsg base data (Some i) k).
    { rewrite /mid /=. apply list_lookup_middle. rewrite /ts. lia. }
    (* the read half survives the append: it is a plain (lat-free) read *)
    have Hr' : read_ok_d (pc_img mid) (pc_log mid) (pa_ws ag) aq false base tvs
                 (srcs_view (pa_ws ag) asrc).
    { rewrite /mid /=. by eapply read_ok_d_app. }
    have He' : excl_ok (pc_log mid) i base tvs ts.
    { rewrite /mid /=. eapply excl_ok_app; [rewrite /ts; lia|done]. }
    (* the fulfil conditions, by construction at the fresh top *)
    have Hbl : ws_bounded (load_post_run_d (pa_ws ag) aq
                             (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                 (length (pc_log cfg)).
    { apply load_post_run_d_bounded;
        [done|exact Hva|by eapply read_ok_d_ts_bounded]. }
    have Hldv : (ldv_of (pa_ws ag) aq (srcs_view (pa_ws ag) asrc) base (tvs.*1)
                 ≤ length (pc_log cfg))%nat.
    { apply ldv_of_bounded;
        [done|exact Hva|by eapply read_ok_d_ts_bounded]. }
    have Hok : fulfil_ok_d (load_post_run_d (pa_ws ag) aq
                              (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                 rl base (length data) ts
                 (Nat.max (Nat.max (srcs_view (pa_ws ag) asrc)
                                   (srcs_view (pa_ws ag) vsrc))
                          (ldv_of (pa_ws ag) aq (srcs_view (pa_ws ag) asrc)
                             base (tvs.*1))).
    { split.
      - intros j Hj. destruct Hbl as (_&_&_&_&_&_&Hcoh&_).
        pose proof (Hcoh (base + Z.of_nat j)). rewrite /ts. lia.
      - have Hvdb : (Nat.max (Nat.max (srcs_view (pa_ws ag) asrc)
                                      (srcs_view (pa_ws ag) vsrc))
                             (ldv_of (pa_ws ag) aq
                                (srcs_view (pa_ws ag) asrc) base (tvs.*1))
                     ≤ length (pc_log cfg))%nat by lia.
        pose proof (fulfil_vpre_d_bounded _ rl _ _ Hbl Hvdb).
        rewrite /ts. lia. }
    have Hpd : pstep (pa_st ag) (pc_dev mid)
                 (LRmw aq rl base tvs data asrc vsrc) st' d'
      by rewrite /mid /=.
    pose proof (WPRmw mid i _ aq rl base tvs data asrc vsrc k ts st' d'
                  Hmidlk Hpd Hlen ltac:(set_solver) Hmsg Hr' He' Hok) as Hrmw.
    rewrite /mid /= in Hrmw.
    have Hprom : ({[ts]} ∪ pa_prom ag) ∖ {[ts]} = pa_prom ag by set_solver.
    rewrite Hprom list_insert_insert in Hrmw.
    exact Hrmw.
  Qed.

  (** THE RMW SPLIT (S2): [wpstep_rmw_now]'s successor.  The conditional
      write's fused form — promise at the fresh top, fulfil immediately.
      Where the rmw lemma carried the read half's [read_ok]/[excl_ok] as
      premises (the fused label had both halves), this one carries the
      RESERVATION the earlier [WPExLoad] left, and its window premise is
      already in the reservation's vocabulary. *)
  Lemma wpstep_exstore_now cfg i ag rl base data asrc vsrc k R st' d' :
    pc_ags cfg !! i = Some ag →
    pstep (pa_st ag) (pc_dev cfg) (LExStore rl base data asrc vsrc) st' d' →
    data ≠ [] →
    ws_bounded (pa_ws ag) (length (pc_log cfg)) →
    S (length (pc_log cfg)) ∉ pa_prom ag →
    w_res (pa_ws ag) = Some R →
    rv_base R = base →
    length (rv_ts R) = length data →
    excl_ok_ts (pc_log cfg) i base (rv_ts R) (S (length (pc_log cfg))) →
    rtc wpstep cfg
      (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i) k])
             d'
             (<[i := WPAgent st'
                       (store_post_run_d (pa_ws ag) rl
                          (srcs_view (pa_ws ag) asrc)
                          (srcs_view (pa_ws ag) vsrc)
                          base (length data)
                          (S (length (pc_log cfg))))
                       (pa_prom ag)]> (pc_ags cfg))).
  Proof.
    intros Hlk Hps Hnn Hb Hfresh Hres Hrb Hrlen He.
    have Hva : (srcs_view (pa_ws ag) asrc ≤ length (pc_log cfg))%nat
      by apply srcs_view_bounded.
    have Hvd : (srcs_view (pa_ws ag) vsrc ≤ length (pc_log cfg))%nat
      by apply srcs_view_bounded.
    have Hrv : (rv_view R ≤ length (pc_log cfg))%nat.
    { destruct (ws_bounded_res _ _ Hb R Hres) as [_ ?]. done. }
    pose proof (lookup_lt_Some _ _ _ Hlk) as Hlt.
    set ts := S (length (pc_log cfg)).
    eapply rtc_l.
    { by eapply (WPPromise cfg i ag base data k). }
    set mid := WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg base data (Some i) k])
                 (pc_dev cfg)
                 (<[i := WPAgent (pa_st ag) (pa_ws ag)
                           ({[ts]} ∪ pa_prom ag)]> (pc_ags cfg)).
    eapply rtc_l; [|apply rtc_refl].
    have Hmidlk : pc_ags mid !! i
                  = Some (WPAgent (pa_st ag) (pa_ws ag) ({[ts]} ∪ pa_prom ag)).
    { rewrite /mid /= list_lookup_insert //. }
    have Hmsg : pc_log mid !! (ts - 1)%nat
                = Some (WMsg base data (Some i) k).
    { rewrite /mid /=. apply list_lookup_middle. rewrite /ts. lia. }
    (* the window survives the append: it ends at the OLD top *)
    have He' : excl_ok_ts (pc_log mid) i base (rv_ts R) ts.
    { rewrite /mid /=. eapply excl_ok_ts_app; [rewrite /ts; lia|done]. }
    have Hok : fulfil_ok_d (pa_ws ag) rl base (length data) ts
                 (Nat.max (Nat.max (srcs_view (pa_ws ag) asrc)
                                   (srcs_view (pa_ws ag) vsrc))
                          (rv_view R)).
    { split.
      - intros j Hj. destruct Hb as (_&_&_&_&_&_&Hcoh&_).
        pose proof (Hcoh (base + Z.of_nat j)). rewrite /ts. lia.
      - have Hvdb : (Nat.max (Nat.max (srcs_view (pa_ws ag) asrc)
                                      (srcs_view (pa_ws ag) vsrc))
                             (rv_view R)
                     ≤ length (pc_log cfg))%nat by lia.
        pose proof (fulfil_vpre_d_bounded _ rl _ _ Hb Hvdb).
        rewrite /ts. lia. }
    have Hpd : pstep (pa_st ag) (pc_dev mid)
                 (LExStore rl base data asrc vsrc) st' d'
      by rewrite /mid /=.
    pose proof (WPExStore mid i _ rl base data asrc vsrc k ts R st' d'
                  Hmidlk Hpd ltac:(set_solver) Hmsg Hres Hrb Hrlen He' Hok)
      as Hex.
    rewrite /mid /= in Hex.
    have Hprom : ({[ts]} ∪ pa_prom ag) ∖ {[ts]} = pa_prom ag by set_solver.
    rewrite Hprom list_insert_insert in Hex.
    exact Hex.
  Qed.

  (** A promise-free step never leaves promises behind: [wpstep_store_now]
      starts and ends [no_promises]-clean when the config was clean. *)
  Lemma no_promises_store_now cfg i ag k st' ws' d' :
    no_promises cfg →
    pc_ags cfg !! i = Some ag →
    no_promises
      (WPCfg (pc_img cfg) (pc_log cfg ++ [WMsg (0%Z) [] (Some i) k]) d'
             (<[i := WPAgent st' ws' (pa_prom ag)]> (pc_ags cfg))).
  Proof.
    intros Hnp Hlk i' ag' Hlk'. simpl in *.
    destruct (decide (i' = i)) as [->|Hne].
    - rewrite list_lookup_insert in Hlk';
        [by eapply lookup_lt_Some|simplify_eq/=].
      by eapply Hnp.
    - rewrite list_lookup_insert_ne // in Hlk'. by eapply Hnp.
  Qed.

End machine.

Global Arguments wpstep {P D} _ _ _.
Global Arguments wp_init {P D} _ _ _.
Global Arguments no_promises {P D} _.
Global Arguments wp_behavior {P D} _ _ _ _ _.
Global Arguments cfg_wf {P D} _.
Global Arguments prom_wf {P} _ _ _.

(* ------------------------------------------------------------------ *)
(** ** THE COMPATIBILITY SHIM: the old machine is the constant-fabric
       instance

    Before the fabric generalization the program step was
    [P → wlabel → P → Prop] and a configuration had two shared components.
    That machine is EXACTLY this one at a fabric that never moves:
    [pstep_of_pure ps] lifts an old-style program LTS by pinning the
    fabric, and every instantiation may then take [D := unit], [d0 := tt].

    Two facts make the correspondence usable: the lift never moves the
    fabric ([pstep_of_pure_dev]) and it is available at EVERY fabric
    ([pstep_of_pure_any]) — which is precisely [WeakPromiseFact]'s
    dev-freeness, so under the shim no step is ever fabric-touching and
    the device-order witness of a run is EMPTY. *)

Definition pstep_of_pure {P D : Type} (ps : P → wlabel → P → Prop)
    : P → D → wlabel → P → D → Prop :=
  λ p d l p' d', ps p l p' ∧ d' = d.

Lemma pstep_of_pure_dev {P D} (ps : P → wlabel → P → Prop) p (d : D) l p' d' :
  pstep_of_pure ps p d l p' d' → d' = d.
Proof. by intros [_ ->]. Qed.

Lemma pstep_of_pure_any {P D} (ps : P → wlabel → P → Prop) p (d : D) l p' d' :
  pstep_of_pure ps p d l p' d' → ∀ d0 : D, pstep_of_pure ps p d0 l p' d0.
Proof. intros [? _] d0. by split. Qed.

Lemma pstep_of_pure_intro {P D} (ps : P → wlabel → P → Prop) p (d : D) l p' :
  ps p l p' → pstep_of_pure ps p d l p' d.
Proof. by split. Qed.

Lemma pstep_of_pure_elim {P D} (ps : P → wlabel → P → Prop) p (d : D) l p' d' :
  pstep_of_pure ps p d l p' d' → ps p l p'.
Proof. by intros [? _]. Qed.

(** AT [D := unit] THE FABRIC EQUATION IS AUTOMATIC, so the lift is the old
    program step VERBATIM — no conjunct, no equation to discharge.  That is
    what makes the archived per-hart-stream files ([WeakSailLTS] and the
    lift tree above it) port by a signature change alone: every
    [pstep p l p'] obligation of the old machine is LITERALLY the [pstep_unit]
    obligation of the new one.  [WPCfgU] is the matching configuration
    abbreviation.  Use [pstep_of_pure] when [D] must stay abstract. *)
Definition pstep_unit {P : Type} (ps : P → wlabel → P → Prop)
    : P → unit → wlabel → P → unit → Prop :=
  λ p _ l p' _, ps p l p'.

Notation WPCfgU img log ags := (WPCfg img log tt ags).

Lemma pstep_unit_of_pure {P} (ps : P → wlabel → P → Prop) p d l p' d' :
  pstep_unit ps p d l p' d' ↔ pstep_of_pure ps p d l p' d'.
Proof.
  split; [intros ?; split; [done|by destruct d, d']|by intros [? _]].
Qed.

(** The fabric of a constant-fabric run never moves. *)
Lemma wpstep_pure_dev {P D} (ps : P → wlabel → P → Prop) (c c' : wpcfg P D) :
  wpstep (pstep_of_pure ps) c c' → pc_dev c' = pc_dev c.
Proof.
  destruct 1; simpl; try done;
    match goal with
    | H : pstep_of_pure _ _ _ _ _ _ |- _ => by destruct H as [_ ->]
    end.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Slice-2 goals (stated here as comments so the file is honest
       about where it is going; see projects/weak-memory-m6.md W1)

    1. FACTORIZATION (PARM Thm 7.1's analog, PtoPF.v): every
       [wp_behavior] is matched by a run that makes ALL its promise
       steps first, then only non-promise steps against the frozen log —
       and the non-promise phase decomposes per agent (PARM
       [Machine.state_exec] is per-thread rtc against the same memory).
    2. THE ERASURE BRIDGE: instantiated at the [WeakLitmus]/[WeakLang]
       program LTS, runs of THIS machine whose stores are all fused
       promise+fulfil at the top ([wpstep_store_now]'s shape) are
       exactly the promise-free machine's runs; in particular the RMW
       rule's [read_ok] + [excl_ok] at a top-of-log write collapses to
       [WeakMem.latest] (own writes excluded by the coherence window,
       other agents' by [excl_ok]) — the [amo_latest_unique] dovetail.
    3. LB LITMUS SANITY: the LB weak outcome is reachable here (promise
       H0's store of y, read it from H1, fulfil late) and provably
       unreachable promise-free ([WeakLitmus.lb_inv]). *)
