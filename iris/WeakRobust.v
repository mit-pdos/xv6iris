(** * WeakRobust.v — the violation pattern and the Layer-1 robustness goal
      (M6 W2, slice 1)

    The vocabulary of the robustness theorem
    ([claude-notes/projects/weak-memory-m6.md], stage W2): the store
    classification, the violation predicate (decision D-M6-2: a STATE
    predicate), and the Layer-1 goal statement over the W1 artifacts
    ([WeakPromise] behaviors on one side, [wp_pf_run] runs on the other).

    PARAMETERS, NOT PLUMBING (see the W2 design block in the worklist):
    Layer 1 takes the classification [cls : wmsg → store_class] and the
    publication predicate [pub] as parameters with stated properties.  The
    Iris side (W3, decision D-M6-6) will instantiate [cls] from the
    message's access kind and [pub] from the storing agent's inert
    watermark; nothing here may depend on that representation.

    THE OBSERVATION FLOOR IS [coh].  A foreign agent that reads byte [a]
    at timestamp [t] raises its [coh] floor for [a] to at least [t]
    ([WeakMem.load_post_at] joins the RAW timestamp into [coh], forwarding
    notwithstanding), and a foreign write raises it likewise — while a
    plain (non-acquire) read raises neither [w_vrNew] nor [w_vwNew].  So
    "some foreign [coh] floor reached the message" is the tightest
    per-byte state witness of "some foreign agent observed the message",
    which is what the violation predicate needs (D-M6-2).

    THE VIOLATION IS HART-RESTRICTED where it is CONSUMED.  [violation]
    quantifies its author and observer over all agents; φ speaks only about
    harts, and with the DMA-tid unification the disk is an ordinary agent,
    so the unrestricted form is refutable for xv6 (see [violation_hart]
    below for the two concrete DMA witnesses).  [violation_hart nh] /
    [pf_violation_free_hart nh] are the forms [WeakRobustMain]'s exhibit
    produces and [WeakCompose]'s premise bundle declares.

    Slice 1 (this file): definitions + the goal statement + the cheap
    sanity lemmas.  W2a (the dependency graph and its acyclicity from
    violation-freedom) and W2b (the π-permuted simulation) build on top;
    they are stated in the worklist, not here. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** The classification *)

(** The three store classes of the Layer-2 enumeration (design doc §4 +
    the third arm): [SCowned] — the storing agent exclusively owns the
    bytes until publication; [SCfenced] — an enumerated release-fenced
    sync site; [SCexcl] — the exclusive-conditional (walker A/D CAS)
    class, pinned by the rmw exclusivity window rather than by ownership
    or fences. *)
Inductive store_class := SCowned | SCfenced | SCexcl.

Global Instance store_class_eq_dec : EqDecision store_class.
Proof. solve_decision. Defined.

(* ------------------------------------------------------------------ *)
(** ** The violation predicate *)

Section violation.
  Context {P D : Type}.

  (** The per-byte observation floor of agent [j] in configuration [c]:
      its coherence floor.  See the header for why [coh] and not a
      view component. *)
  Definition obs_flr (c : wpcfg P D) (j : agent) (a : Z) : nat :=
    match pc_ags c !! j with
    | Some ag => coh (pa_ws ag) a
    | None => 0%nat
    end.

  Context (cls : wmsg → store_class).
  (** Publication: [pub c ts] — the message at timestamp [ts] has been
      published (its owner's release fence covered it).  Layer 1 needs
      only MONOTONICITY along runs, required where used (W2a); the Iris
      side derives it from the [w_pub] watermark (D-M6-6). *)
  Context (pub : wpcfg P D → nat → Prop).

  (** The violation (D-M6-2): an owned, unpublished message some FOREIGN
      agent's floor has reached.  [ts = S p] for log position [p], as
      everywhere in [WeakMem]. *)
  Definition violation (c : wpcfg P D) : Prop :=
    ∃ (p : nat) (m : wmsg) (i j : agent) (a : Z),
      pc_log c !! p = Some m ∧ wm_tid m = Some i ∧
      cls m = SCowned ∧ ¬ pub c (S p) ∧
      j ≠ i ∧ is_Some (msg_byte m a) ∧
      (S p ≤ obs_flr c j a)%nat.

  (** THE HART-RESTRICTED VIOLATION, and the one every CONSUMER of this
      file takes.  [nh] is the number of HART agents: both the AUTHOR
      [i] and the OBSERVER [j] are required to be harts
      ([WeakMem.tid_hart nh]).

      WHY THE RESTRICTION IS NOT OPTIONAL.  [violation] above quantifies
      both agents over ALL agents, while the Iris-side predicate that
      refutes it ([WeakGhost.no_violation], and the C/D/S invariants
      behind it) speaks only about HARTS — a device never publishes and
      is exempt by construction ([WeakGhost.wcds_clean],
      [WeakLang.n_disk_not_hart]).  With the DMA-tid unification (seam
      1a) the disk is an ORDINARY agent with an ordinary index, so for
      xv6 the unrestricted [pf_violation_free] is not merely
      undischarged but REFUTABLE: a hart that reads a byte the virtio
      DMA wrote raises its [coh] to that message's timestamp, and the
      message is [WCplain] (hence [SCowned]) and never published, so
      [violation] holds with [i = WeakLang.n_disk]; symmetrically the
      disk's own DMA over a plainly-written hart byte gives [violation]
      with [j = n_disk].  Both witnesses are outside φ's domain of
      discourse, and both disappear under the hart restriction.
      [WeakRobustMain.bad] already carries the author's bound, and its
      [bad]/[edges_split] pair carries the reader's, so the exhibit
      produces exactly this form. *)
  Definition violation_hart (nh : nat) (c : wpcfg P D) : Prop :=
    ∃ (p : nat) (m : wmsg) (i j : agent) (a : Z),
      pc_log c !! p = Some m ∧ wm_tid m = Some i ∧ tid_hart nh (wm_tid m) ∧
      cls m = SCowned ∧ ¬ pub c (S p) ∧
      j ≠ i ∧ tid_hart nh (Some j) ∧ is_Some (msg_byte m a) ∧
      (S p ≤ obs_flr c j a)%nat.

  Lemma violation_hart_violation nh c : violation_hart nh c → violation c.
  Proof.
    intros (p & m & i & j & a & ? & ? & _ & ? & ? & ? & _ & ? & ?).
    by exists p, m, i, j, a.
  Qed.

  (** The Layer-2 premise, as Layer 1 consumes it: no promise-free run of
      the program reaches a violating configuration.  Stated over
      [wp_pf_run] ([WeakPromiseBridge]'s fused promise-free fragment), the
      object the Iris proof talks about through the bridge.

      [pf_violation_free] is the UNRESTRICTED form, kept for the goal
      statements below and in [WeakRobustGraph]; [pf_violation_free_hart]
      is what [WeakRobustMain] and [WeakCompose] actually consume. *)
  Definition pf_violation_free (pstep : P → D → wlabel → P → D → Prop)
      (img : image) (d0 : D) (ps : list P) : Prop :=
    ∀ c, rtc (wp_pf_run pstep) (wp_init img d0 ps) c → ¬ violation c.

  Definition pf_violation_free_hart (nh : nat)
      (pstep : P → D → wlabel → P → D → Prop) (img : image) (d0 : D)
      (ps : list P) : Prop :=
    ∀ c, rtc (wp_pf_run pstep) (wp_init img d0 ps) c → ¬ violation_hart nh c.

  Lemma pf_violation_free_hart_weaken nh pstep img d0 ps :
    pf_violation_free pstep img d0 ps →
    pf_violation_free_hart nh pstep img d0 ps.
  Proof. intros H c Hrun Hv. by eapply H, violation_hart_violation. Qed.

  (** Sanity: the initial configuration violates nothing (empty log). *)
  Lemma violation_init img d0 ps :
    ¬ violation (wp_init (P := P) (D := D) img d0 ps).
  Proof. intros (p & m & _ & _ & _ & Hm & _). by rewrite lookup_nil in Hm. Qed.

End violation.

(* ------------------------------------------------------------------ *)
(** ** Observables *)

(** The flat memory a configuration's log denotes: byte [a] is the value
    of the LATEST write to [a] (timestamp 0 = the era-initial image).
    This is the observable the robustness conclusion preserves — the
    promise-free witness run ends with the SAME memory, at possibly
    different (π-permuted) timestamps. *)
Definition mem_of {P D : Type} (c : wpcfg P D) (a : Z) : option (bv 8) :=
  log_byte (pc_img c) (pc_log c) (latest_ts (pc_log c) a) a.

(** The per-agent program observables. *)
Definition prog_of {P D : Type} (c : wpcfg P D) : list P := pa_st <$> pc_ags c.

(* ------------------------------------------------------------------ *)
(** ** The Layer-1 goal *)

Section goal.
  Context {P D : Type} (pstep : P → D → wlabel → P → D → Prop).
  Context (cls : wmsg → store_class).
  Context (pub : wpcfg P D → nat → Prop).

  (** THE ROBUSTNESS GOAL (the theorem W2a+W2b prove; stated here so the
      target is fixed and compiling from day one):

      for a lat-free program whose promise-free runs never violate, every
      full-machine BEHAVIOR (completed run, all promises drained —
      [wp_behavior]) is matched by a promise-free run with the same
      per-agent program states and the same flat memory.

      What "matched" deliberately does NOT say: equal logs (the
      promise-free log is the FULFILMENT order, a permutation π of the
      behavior's gmo), equal per-agent views (they differ by π), or
      anything about incomplete prefixes (doomed runs are model
      artifacts — design doc §2 consequence (a)). *)
  Definition robust : Prop :=
    ∀ img d0 ps c,
      lat_free_prog pstep →
      pf_violation_free cls pub pstep img d0 ps →
      wp_behavior pstep img d0 ps c →
      ∃ c', rtc (wp_pf_run pstep) (wp_init img d0 ps) c' ∧
            prog_of c' = prog_of c ∧
            (∀ a : Z, mem_of c' a = mem_of c a).

End goal.

(* ------------------------------------------------------------------ *)
(** ** Slice-2 pointers (comments only)

    W2a builds the dependency graph over [wp_behavior_factor]'s
    factorized form (promise phase + [wp_phases] per-agent state runs)
    and derives its acyclicity from [pf_violation_free]; W2b
    topologically sorts it and constructs the [wp_pf_run] witness with a
    timestamp permutation, value-exact reads, and a per-agent view
    relation whose direction the proof will determine.  Both live in
    follow-up files; the worklist's W2 block is the authoritative plan. *)
