(** * WeakRvwmoKill.v — THE ARITHMETIC SUB-KILLS (route B, stage B2e-1)

    Design: [claude-notes/design/weak-memory-route-b.md] §4c, first bullet.

    THE POINT.  [WeakRvwmoNorm.normalize] is parameterized by three kill
    obligations [kill_K1]/[kill_K2]/[kill_K3] — the three configurations the
    po-minimal-witness descent cannot exchange away.  Each of them is a
    statement about a VIOLATION [gviol G e w] ([e] po-before the write [w],
    but [w] gmo-before [e]) plus a witness-kind-specific blocker.  This file
    peels off everything about such a configuration that is PURE ORDER
    THEORY, so that B2e-3's export argument (φ, the lock protocol) only ever
    has to face the genuinely RACY residual.

    THE ONE IDEA, in two lines: every named ppo⁻ arm and every dep edge
    running [e → w] gives [gmo_lt G e w] (by [gppo_gmo] / [gdeps_gmo]),
    which contradicts the violation's own [gmo_lt G w e].  So the arm
    cannot be present — WHATEVER the witness kind is.  §2's five
    [gviol_no_*] lemmas are exactly the four ppo⁻ arms plus the dep
    fragment, in that shape; §1 states the shared engine once.

    THE DELIVERABLE for B2e-3 is §4: for each landed kill, a RACY form
    — the kill's statement verbatim, PLUS the §2 exclusions as extra
    hypotheses on the configuration — and a REDUCTION
    [kill_K1_of_racy : kill_K1_racy GD → kill_K1 GD] (and K2/K3).  Note
    that no case split and no decidability is needed anywhere: the
    exclusions are NEGATIONS, and §2 proves each of them outright from the
    violation.  The racy forms are the contract B2e-3 implements.

    THE ORBIT.  The landed kills quantify over an arbitrary [GD'] with
    [gd_equiv GD GD'] (see [WeakRvwmoNorm]'s header for why); the racy
    forms do too, and the reductions work POINTWISE at each [GD'] — whose
    consistency is [gd_equiv]'s fourth conjunct, which is where §2's
    hypotheses come from.

    BEYOND THE THREE SPEC'D EXCLUSIONS (flagged; see the report):
      - the racy forms carry ALL FOUR ppo⁻ arms, not just rules 4/5:
        [grel_acq] (rule 7) and same-byte-ness (rules 1–3, [gviol_no_poloc])
        are refuted by the very same argument and are free;
      - [kill_K2_racy] additionally gets [z.1 ≠ e.1] — the MP-stale-reader
        is NECESSARILY CROSS-HART ([gviol_K2_cross_hart], §3), which the
        landed [kill_K2] does not say (unlike [kill_K3], which hypothesizes
        its cross-hart-ness).  A same-hart stale reader is refuted either by
        po-minimality (below [e]) or by poloc (above [e]).
      - CHECKED AND EMPTY (the spec's K1 candidate): [e] reads [w0]'s byte
        by construction, but [w0] is CROSS-HART from [e] and every ppo⁻ arm
        as well as [gdeps_wf] pins the agent, so the [e]/[w0] same-byte
        facts yield no ordering and no contradiction.  K1's residual is
        genuinely the racy read.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2
                            WeakRvwmoGraph WeakRvwmoXchg WeakRvwmoNorm.

(* ====================================================================== *)
(** * 1. THE ENGINE: a violation admits NO ppo⁻ edge in its own direction

    [gviol G e w] carries [gmo_lt G w e]; [gppo_gmo] turns a ppo⁻ edge
    [e → w] into [gmo_lt G e w]; gmo is a strict order.  Everything below
    is this lemma with one arm plugged in. *)

Lemma gviol_no_gppo (G : gexec) (e w : geid) :
  gppo_gmo G → gviol G e w → ¬ gppo G e w.
Proof.
  intros Hppo (_ & _ & _ & Hmo_we) Hp.
  eapply gmo_lt_irrefl, gmo_lt_trans; [exact (Hppo e w Hp)|exact Hmo_we].
Qed.

(* ====================================================================== *)
(** * 2. THE [gviol_no_*] FAMILY — witness-kind-INDEPENDENT

    Each named edge from the violation's witness [e] to the violating write
    [w] is refuted.  None of them looks at whether [e] is a read or a write,
    which is why the same five exclusions serve all three kills. *)

(** RULE 5 — an ACQUIRING READ (including an acquiring RMW: the fused
    alphabet lets one event be both) is gppo-before every po-later event. *)
Lemma gviol_no_aq (G : gexec) (e w : geid) :
  rvwmo_minus_consistent G → gviol G e w →
  ¬ (glbl_is G e lb_is_r ∧ glbl_is G e lb_aq).
Proof.
  intros (_ & Hppo & _ & _) Hv [Hr Haq].
  apply (gviol_no_gppo G e w Hppo Hv). right. right. left.
  pose proof Hv as (Hpo & _ & _ & _). by split_and!.
Qed.

(** RULE 4 — a covering fence between them. *)
Lemma gviol_no_fence (G : gexec) (e w : geid) :
  rvwmo_minus_consistent G → gviol G e w → ¬ gfence_covers G e w.
Proof.
  intros (_ & Hppo & _ & _) Hv Hf.
  apply (gviol_no_gppo G e w Hppo Hv). by right; left.
Qed.

(** RULE 7 — the RCsc pair.  Vacuous unless [w] is an acquiring-read RMW;
    stated anyway, so the exclusion set covers every ppo⁻ arm. *)
Lemma gviol_no_relacq (G : gexec) (e w : geid) :
  rvwmo_minus_consistent G → gviol G e w → ¬ grel_acq G e w.
Proof.
  intros (_ & Hppo & _ & _) Hv Hra.
  apply (gviol_no_gppo G e w Hppo Hv). by right; right; right.
Qed.

(** RULES 1–3 — same-byte program order.  So the violation's witness and
    the violating write are BYTE-DISJOINT.  ([WeakRvwmoNorm]'s descent
    proves this inline twice, at the final swap; here it is, exported.) *)
Lemma gviol_no_poloc (G : gexec) (e w : geid) (a : Z) :
  rvwmo_minus_consistent G → gviol G e w →
  gaccesses G e a → gaccesses G w a → False.
Proof.
  intros (_ & Hppo & _ & _) Hv Hae Haw.
  apply (gviol_no_gppo G e w Hppo Hv). left.
  pose proof Hv as (Hpo & _ & _ & _). split; [exact Hpo|]. by exists a.
Qed.

(** THE DEP FRAGMENT — [gdeps_gmo] is the ppo 9–13 store fragment, so a dep
    edge into the violating write is refuted the same way. *)
Lemma gviol_no_dep (GD : gdexec) (e w : geid) :
  rvwmo_minus_deps_consistent GD → gviol (gd_g GD) e w →
  (e, w) ∉ gd_deps GD.
Proof.
  intros (_ & _ & Hdgmo) (_ & _ & _ & Hmo_we) Hin.
  eapply gmo_lt_irrefl, gmo_lt_trans; [exact (Hdgmo (e, w) Hin)|exact Hmo_we].
Qed.

(* ====================================================================== *)
(** * 3. K2's EXTRA: THE STALE READER IS CROSS-HART

    Beyond the spec's three exclusions.  In [kill_K2] the blocker [z] reads
    a byte of the descending write [e] at an older index; [z] cannot be
    same-hart as [e]:

      - [z.2 < e.2] — then [z] is a memory event sitting gmo-above [w] and
        po-BEFORE [e], i.e. an earlier witness of [w], contradicting [e]'s
        po-minimality ([po_min_no_blocker]);
      - [z.2 = e.2] — then [z = e], and [gmo_lt G z e] is irreflexive;
      - [z.2 > e.2] — then [gpo G e z], and they share the byte [a], so
        rules 1–3 give [gmo_lt G e z], again contradicting [gmo_lt G z e].

    Note this needs NEITHER [e]'s write-ness nor the [t < gwix e]
    staleness — it holds for any interval reader of one of [e]'s bytes. *)

Lemma gviol_K2_cross_hart (G : gexec) (w e z : geid) (a : Z) (t : nat)
    (v v' : bv 8) :
  rvwmo_minus_consistent G →
  gviol G e w →
  (∀ e', gviol G e' w → ¬ (e'.2 < e.2)%nat) →
  gmo_lt G w z → gmo_lt G z e →
  greads_byte G z a t v →
  gwrites_byte G e a v' →
  z.1 ≠ e.1.
Proof.
  intros Hcons Hv Hpmin Hmo_wz Hmo_ze Hrd Hwb Hag.
  pose proof Hcons as (Hwf & Hppo & _ & _).
  pose proof Hv as (_ & Hmem_e & _ & _).
  assert (Hzs : ∃ l, gx_lbl G z = Some l ∧ lb_is_r l = true).
  { destruct Hrd as (l & base & ts & vs & j & Hl & Hrd' & _).
    exists l. split; [exact Hl|by eapply lb_rd_is_r]. }
  assert (Hzmem : gmem G z).
  { destruct Hzs as (l & Hl & Hr). exists l. split; [exact Hl|].
    by rewrite /lb_is_mem Hr. }
  destruct (decide (z.2 < e.2)%nat) as [Hlt|Hge].
  { exact (po_min_no_blocker G w e z Hv Hpmin Hzmem Hmo_wz Hag Hlt). }
  destruct (decide (z.2 = e.2)) as [Heq2|Hne2].
  { assert (z = e) by (by apply injective_projections). subst z.
    by eapply gmo_lt_irrefl. }
  (* [z] is po-AFTER [e] on the same hart, and reads a byte [e] writes. *)
  assert (Hpl : gppo G e z).
  { left. split.
    - split_and!; [by rewrite Hag|lia| |].
      + destruct Hmem_e as (l & Hl & _). by exists l.
      + destruct Hzs as (l & Hl & _). by exists l.
    - exists a. split; [left; by exists v'|right; by exists t, v]. }
  eapply gmo_lt_irrefl, gmo_lt_trans; [exact (Hppo e z Hpl)|exact Hmo_ze].
Qed.

(* ====================================================================== *)
(** * 4. THE RACY RESIDUALS, AND THE REDUCTIONS

    Each [kill_K*_racy] repeats [kill_K*]'s quantification and premises
    verbatim and then adds the §2 exclusions (and, for K2, §3's
    cross-hart-ness) as further hypotheses.  Adding hypotheses WEAKENS the
    obligation, and the reduction pays for the weakening once and for all
    — so B2e-3 implements the racy forms and gets the landed kills. *)

(** ** 4.1 K1 — the witness is a READ blocked at its cross-hart rf-source *)

Definition kill_K1_racy (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e a t v w0,
    gviol (gd_g GD') e w →
    (∀ e' w', gviol (gd_g GD') e' w' → ¬ gmo_lt (gd_g GD') w' w) →
    (∀ e', gviol (gd_g GD') e' w → ¬ (e'.2 < e.2)%nat) →
    gis_w (gd_g GD') e = false →
    greads_byte (gd_g GD') e a t v →
    gwrite_at (gd_g GD') t = Some w0 →
    w0.1 ≠ e.1 →
    gmo_lt (gd_g GD') w w0 → gmo_lt (gd_g GD') w0 e →
    (* ---- the arithmetic exclusions (§2): no ppo⁻ arm, no dep edge ---- *)
    ¬ (glbl_is (gd_g GD') e lb_is_r ∧ glbl_is (gd_g GD') e lb_aq) →
    ¬ gfence_covers (gd_g GD') e w →
    ¬ grel_acq (gd_g GD') e w →
    (∀ b, gaccesses (gd_g GD') e b → gaccesses (gd_g GD') w b → False) →
    (e, w) ∉ gd_deps GD' →
    False.

Lemma kill_K1_of_racy (GD : gdexec) : kill_K1_racy GD → kill_K1 GD.
Proof.
  intros HR GD' Heq w e a t v w0 Hv Hmin Hpmin Hew Hrd Hsrc Hag Hmo1 Hmo2.
  pose proof Heq as (π & _ & _ & _ & Hcons).
  pose proof Hcons as (Hc & _ & _).
  eapply (HR GD' Heq w e a t v w0); [done..| | | | |].
  - exact (gviol_no_aq _ e w Hc Hv).
  - exact (gviol_no_fence _ e w Hc Hv).
  - exact (gviol_no_relacq _ e w Hc Hv).
  - intros b. exact (gviol_no_poloc _ e w b Hc Hv).
  - exact (gviol_no_dep GD' e w Hcons Hv).
Qed.

(** ** 4.2 K2 — the witness is a WRITE with an interval STALE reader *)

Definition kill_K2_racy (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e z a t v v',
    gviol (gd_g GD') e w →
    (∀ e' w', gviol (gd_g GD') e' w' → ¬ gmo_lt (gd_g GD') w' w) →
    (∀ e', gviol (gd_g GD') e' w → ¬ (e'.2 < e.2)%nat) →
    gis_w (gd_g GD') e = true →
    gmo_lt (gd_g GD') w z → gmo_lt (gd_g GD') z e →
    greads_byte (gd_g GD') z a t v →
    gwrites_byte (gd_g GD') e a v' →
    (t < gwix (gd_g GD') e)%nat →
    (* ---- the arithmetic exclusions (§2), plus §3's cross-hart-ness ---- *)
    z.1 ≠ e.1 →
    ¬ (glbl_is (gd_g GD') e lb_is_r ∧ glbl_is (gd_g GD') e lb_aq) →
    ¬ gfence_covers (gd_g GD') e w →
    ¬ grel_acq (gd_g GD') e w →
    (∀ b, gaccesses (gd_g GD') e b → gaccesses (gd_g GD') w b → False) →
    (e, w) ∉ gd_deps GD' →
    False.

Lemma kill_K2_of_racy (GD : gdexec) : kill_K2_racy GD → kill_K2 GD.
Proof.
  intros HR GD' Heq w e z a t v v' Hv Hmin Hpmin Hew Hmo1 Hmo2 Hrd Hwb Hlt.
  pose proof Heq as (π & _ & _ & _ & Hcons).
  pose proof Hcons as (Hc & _ & _).
  eapply (HR GD' Heq w e z a t v v'); [done..| | | | | |].
  - exact (gviol_K2_cross_hart _ w e z a t v v' Hc Hv Hpmin Hmo1 Hmo2 Hrd Hwb).
  - exact (gviol_no_aq _ e w Hc Hv).
  - exact (gviol_no_fence _ e w Hc Hv).
  - exact (gviol_no_relacq _ e w Hc Hv).
  - intros b. exact (gviol_no_poloc _ e w b Hc Hv).
  - exact (gviol_no_dep GD' e w Hcons Hv).
Qed.

(** ** 4.3 K3 — the witness is a WRITE racing a cross-hart same-byte write *)

Definition kill_K3_racy (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e z a v v',
    gviol (gd_g GD') e w →
    (∀ e' w', gviol (gd_g GD') e' w' → ¬ gmo_lt (gd_g GD') w' w) →
    (∀ e', gviol (gd_g GD') e' w → ¬ (e'.2 < e.2)%nat) →
    gis_w (gd_g GD') e = true →
    gis_w (gd_g GD') z = true → z.1 ≠ e.1 →
    gmo_lt (gd_g GD') w z → gmo_lt (gd_g GD') z e →
    gwrites_byte (gd_g GD') z a v → gwrites_byte (gd_g GD') e a v' →
    (* ---- the arithmetic exclusions (§2) ---- *)
    ¬ (glbl_is (gd_g GD') e lb_is_r ∧ glbl_is (gd_g GD') e lb_aq) →
    ¬ gfence_covers (gd_g GD') e w →
    ¬ grel_acq (gd_g GD') e w →
    (∀ b, gaccesses (gd_g GD') e b → gaccesses (gd_g GD') w b → False) →
    (e, w) ∉ gd_deps GD' →
    False.

Lemma kill_K3_of_racy (GD : gdexec) : kill_K3_racy GD → kill_K3 GD.
Proof.
  intros HR GD' Heq w e z a v v' Hv Hmin Hpmin Hew Hzw Hag Hmo1 Hmo2 Hzb Heb.
  pose proof Heq as (π & _ & _ & _ & Hcons).
  pose proof Hcons as (Hc & _ & _).
  eapply (HR GD' Heq w e z a v v'); [done..| | | | |].
  - exact (gviol_no_aq _ e w Hc Hv).
  - exact (gviol_no_fence _ e w Hc Hv).
  - exact (gviol_no_relacq _ e w Hc Hv).
  - intros b. exact (gviol_no_poloc _ e w b Hc Hv).
  - exact (gviol_no_dep GD' e w Hcons Hv).
Qed.

(** ** 4.4 STATEMENT FIDELITY, MACHINE-CHECKED

    The reductions alone would still compile if a racy form had DROPPED one
    of the landed kill's premises, so here is the trivial converse — the
    racy form holds of any graph whose landed kill holds, by forgetting the
    exclusions.  It typechecks only if the shared premise blocks match
    exactly, which is the property B2e-3 is entitled to rely on.  (Together
    with §4.1–4.3 the two forms are of course EQUIVALENT; the racy one is
    merely the one with the easier proof obligation.) *)

Lemma kill_K1_to_racy (GD : gdexec) : kill_K1 GD → kill_K1_racy GD.
Proof. intros HK GD' Heq w e a t v w0; intros. by eapply HK. Qed.

Lemma kill_K2_to_racy (GD : gdexec) : kill_K2 GD → kill_K2_racy GD.
Proof. intros HK GD' Heq w e z a t v v'; intros. by eapply HK. Qed.

Lemma kill_K3_to_racy (GD : gdexec) : kill_K3 GD → kill_K3_racy GD.
Proof. intros HK GD' Heq w e z a v v'; intros. by eapply HK. Qed.

(** ** 4.5 THE RACY FORMS ARE STILL REAL OBLIGATIONS

    The reduction direction that matters is [_of_racy]; but the exclusions
    must not have made the racy forms vacuous.  They have not: the LB
    non-collapse witness refutes [kill_K1_racy] too — its K1 configuration
    satisfies all five exclusions (the load is plain, there is no fence and
    no dep, and the load's byte [0] is not the store's byte [8]).  This is
    [lbgd_kill_K1_false] transported along the reduction, so it costs one
    line. *)

Lemma lbgd_kill_K1_racy_false : ¬ kill_K1_racy lbgd.
Proof. intros HR. exact (lbgd_kill_K1_false (kill_K1_of_racy lbgd HR)). Qed.
