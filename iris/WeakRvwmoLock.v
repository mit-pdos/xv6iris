(** * WeakRvwmoLock.v — THE GRAPH-SIDE LOCK-PROTOCOL KIT (route B, stage B2e-2)

    Design: [claude-notes/design/weak-memory-route-b.md] §4c, second bullet
    (the "B2e-2's DERIVATION CHAIN" block).

    THE POINT.  [WeakRvwmoKill]'s racy residuals hand B2e-3 a configuration
    that pure order theory cannot refute: a violation [gviol G e w] whose
    witness [e] reads a write [w0] sitting gmo-between [w] and [e].  The
    xv6 answer is that [e]/[w] and [w0] live in DIFFERENT critical sections
    of one lock byte, and critical sections do not overlap.  This file makes
    that argument PURE ORDER THEORY over one lock byte [b], parameterized by
    two hypotheses whose discharge is B2e-3's:

      - [lock_pattern G b] — the VALUE protocol: every [b]-write either
        writes zero (a RELEASE) or is an RMW writing nonzero whose own read
        entry at [b] names a ZERO value (an ACQUIRE);
      - [lock_paired G b] — the CS PAIRING: every release is the closing
        write of a critical section of ITS OWN hart (same hart, co-later
        than its acquire, with no [b]-write of that hart in between).

    §2 is the window theory the pattern buys on its own: ATOMICITY says no
    [b]-write is co-strictly-between an acquire's read source and the
    acquire ([acq_src]), and LOAD-VALUE + rules 1–3 say the source is
    co-BELOW the acquire ([acq_ts_lt]) — so an acquire's co-predecessor on
    [b] is exactly the zero write it read ([acq_src_rel]).

    WHY [lock_paired] IS NOT OPTIONAL (flagged; see the report).  The
    pattern alone does NOT give mutual exclusion, and the design block's
    sketch is one step short here.  The pattern constrains the [b]-write
    sequence only by "no two acquires are co-adjacent", which admits

        ACQ_h · REL_x · ACQ_j · REL_h · REL_j

    — overlapping critical sections separated by a THIRD hart's release
    (nothing in the pattern says a hart releases only what it holds, or
    that its releases alternate with its acquires).  [lock_paired] is
    exactly the missing "only the holder releases", in the SYNTACTIC form
    B2e-3's site classification can supply — per hart, the [b]-writes of a
    lock client alternate acquire/release, and [lock_cs_intro] builds the
    pairing from that program-order fact alone.  With it, §3's induction
    (over [gwix], three cases, minimal-overlap descent) closes exclusion:
    [win_excl_of_pattern].

    §4 assembles [cs_kill].  Both case directions of the window order close
    by the SAME four-step gmo cycle, mirrored:

        j's CS first :  w  <  w0 <  REL_j < ACQ_h <  w
        h's CS first :  w0 <  e  <  REL_h < ACQ_j <  w0

    where the outer steps are the configuration's own [gmo_lt], the fence
    steps are ppo rule 4 and the acquire steps are ppo rule 5.  The mirror
    is why the [h]-first direction needs [e]'s OWN release [REL_h] and the
    aq bit on [ACQ_j] — both flagged as B2e-3 obligations.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakRvwmoGraph WeakRvwmoXchg.

(* ====================================================================== *)
(** * 0. BOOKKEEPING — byte footprints, write indices, and gmo

    Small bridges between [gwrites_byte] and the [gwrites]/[gwix] sub-order.
    Nothing here is lock-specific. *)

(** A write event's byte value is FUNCTIONAL: [acc_addr] is injective in the
    offset, so one event writes one value per address.  This is the entire
    reason an acquire (nonzero) can never BE a release (zero). *)
Lemma gwrites_byte_det (G : gexec) (e : geid) (a : Z) (v1 v2 : bv 8) :
  gwrites_byte G e a v1 → gwrites_byte G e a v2 → v1 = v2.
Proof.
  intros (l1 & b1 & vs1 & j1 & Hl1 & Hwr1 & Hv1 & Ha1)
         (l2 & b2 & vs2 & j2 & Hl2 & Hwr2 & Hv2 & Ha2).
  assert (l1 = l2) as -> by (rewrite Hl1 in Hl2; by simplify_eq).
  assert (b1 = b2 ∧ vs1 = vs2) as [-> ->]
    by (rewrite Hwr1 in Hwr2; by simplify_eq).
  assert (j1 = j2) as ->.
  { apply (acc_addr_inj b2). by rewrite Ha1 Ha2. }
  rewrite Hv1 in Hv2. by simplify_eq.
Qed.

Lemma gwrites_byte_lbl (G : gexec) (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte G e a v → is_Some (gx_lbl G e).
Proof. intros (l & ? & ? & ? & Hl & _). by exists l. Qed.

Lemma gwrites_byte_glbl_w (G : gexec) (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte G e a v → glbl_is G e lb_is_w.
Proof.
  intros (l & base & vs & j & Hl & Hwr & _ & _).
  exists l. split; [done|]. by eapply lb_wr_is_w.
Qed.

Lemma gwrites_byte_gwrites (G : gexec) (e : geid) (a : Z) (v : bv 8) :
  gwf G → gwrites_byte G e a v → e ∈ gwrites G.
Proof.
  intros Hwf Hw. eapply gis_w_gwrites;
    [done|by eapply gwrites_byte_lbl|by eapply gwrites_byte_gis_w].
Qed.

(** [gwix] and [gmo_lt] agree on the writes, in both directions. *)
Lemma gwix_lt_gmo (G : gexec) (w1 w2 : geid) :
  gwf G → w1 ∈ gwrites G → w2 ∈ gwrites G →
  (gwix G w1 < gwix G w2)%nat → gmo_lt G w1 w2.
Proof.
  intros Hwf H1 H2 Hlt. pose proof Hwf as (Hnd & _ & _).
  split_and!.
  - by apply gwrites_elem_of in H1 as [? _].
  - by apply gwrites_elem_of in H2 as [? _].
  - by apply (gwix_gpos_lt G w1 w2 Hnd H1 H2).
Qed.

Lemma gmo_gwix_lt (G : gexec) (w1 w2 : geid) :
  gwf G → w1 ∈ gwrites G → w2 ∈ gwrites G →
  gmo_lt G w1 w2 → (gwix G w1 < gwix G w2)%nat.
Proof.
  intros Hwf H1 H2 (_ & _ & Hlt). pose proof Hwf as (Hnd & _ & _).
  by apply (gwix_gpos_lt G w1 w2 Hnd H1 H2).
Qed.

(** Program order from a same-hart offset comparison. *)
Lemma gpo_of_lt (G : gexec) (x y : geid) :
  x.1 = y.1 → (x.2 < y.2)%nat →
  is_Some (gx_lbl G x) → is_Some (gx_lbl G y) → gpo G x y.
Proof. intros. by split_and!. Qed.

(** THE PPO ARMS, as one-liners.

    RULE 5 — an acquiring read is gmo-before every po-later event. *)
Lemma acq_gmo_after (G : gexec) (a x : geid) :
  gppo_gmo G → gpo G a x → glbl_is G a lb_is_r → glbl_is G a lb_aq →
  gmo_lt G a x.
Proof. intros Hppo Hpo Hr Haq. apply Hppo. right; right; left. by split_and!. Qed.

(** RULE 4 — a covering fence orders. *)
Lemma fence_gmo_after (G : gexec) (x y : geid) :
  gppo_gmo G → gfence_covers G x y → gmo_lt G x y.
Proof. intros Hppo Hf. apply Hppo. by right; left. Qed.

(* ====================================================================== *)
(** * 1. THE VALUE PATTERN

    One lock byte [b].  [lock_free] is the byte the lock word holds when the
    lock is free; an ACQUIRE writes something else, a RELEASE writes it. *)

Definition lock_free : bv 8 := Z_to_bv 8 0.

(** An ACQUIRE on [b]: a [b]-write of a NONZERO byte.  (That it is an RMW
    reading zero is the PATTERN's business, not the definition's — so the
    CS-coverage hypotheses stay as small as possible.) *)
Definition lock_acq (G : gexec) (b : Z) (w : geid) : Prop :=
  ∃ v, gwrites_byte G w b v ∧ v ≠ lock_free.

(** A RELEASE on [b]: a [b]-write of the free byte. *)
Definition lock_rel (G : gexec) (b : Z) (w : geid) : Prop :=
  gwrites_byte G w b lock_free.

(** THE PATTERN.  The image starts the byte free, and every [b]-write is an
    acquire — an RMW whose READ ENTRY AT [b] names a zero value — or a
    release. *)
Definition lock_pattern (G : gexec) (b : Z) : Prop :=
  (∀ v0, gx_img G b = Some v0 → v0 = lock_free) ∧
  (∀ w v, gwrites_byte G w b v →
     (glbl_is G w lb_is_r ∧ v ≠ lock_free ∧
      (∃ t, greads_byte G w b t lock_free)) ∨
     v = lock_free).

(** An event is never both. *)
Lemma lock_acq_not_rel (G : gexec) (b : Z) (w : geid) :
  lock_acq G b w → lock_rel G b w → False.
Proof.
  intros (v & Hw & Hne) Hr. apply Hne. by eapply gwrites_byte_det.
Qed.

Lemma lock_acq_gwrites (G : gexec) (b : Z) (w : geid) :
  gwf G → lock_acq G b w → w ∈ gwrites G.
Proof. intros Hwf (v & Hw & _). by eapply gwrites_byte_gwrites. Qed.

Lemma lock_rel_gwrites (G : gexec) (b : Z) (w : geid) :
  gwf G → lock_rel G b w → w ∈ gwrites G.
Proof. intros Hwf Hw. by eapply gwrites_byte_gwrites. Qed.

(** THE PATTERN AT AN ACQUIRE: it is a read, and it read zero at [b]. *)
Lemma lock_acq_read (G : gexec) (b : Z) (w : geid) :
  lock_pattern G b → lock_acq G b w →
  glbl_is G w lb_is_r ∧ ∃ t, greads_byte G w b t lock_free.
Proof.
  intros [_ Hpat] (v & Hw & Hne).
  destruct (Hpat w v Hw) as [(Hr & _ & Ht)|Hz]; [by split|done].
Qed.

(* ====================================================================== *)
(** * 2. THE WINDOW: an acquire's co-predecessor is the zero write it read

    Three facts, all from [rvwmo_minus_consistent] + the pattern. *)

(** ATOMICITY, in window form: no [b]-write is co-strictly-between the
    acquire's read index [t] and the acquire itself.  ([gatomicity]'s
    negated conjunction, turned into the dichotomy every consumer wants.) *)
Lemma acq_src (G : gexec) (b : Z) (A : geid) (t : nat) :
  rvwmo_minus_consistent G → lock_acq G b A →
  greads_byte G A b t lock_free →
  ∀ w' v', gwrites_byte G w' b v' →
    (gwix G w' ≤ t)%nat ∨ (gwix G A ≤ gwix G w')%nat.
Proof.
  intros (_ & _ & _ & Hat) (v & Hwb & _) Hrd w' v' Hw'.
  pose proof (Hat A b t lock_free Hrd (gwrites_byte_glbl_w _ _ _ _ Hwb)
                w' v' Hw') as Hna.
  lia.
Qed.

(** LOAD VALUE + rules 1–3: the acquire's read index is BELOW its own write
    index.  The [gvisible] disjunction's forwarding half is not a hole —
    a same-hart same-byte write po-before the acquire is [gpoloc]-ordered,
    hence gmo-ordered, hence co-below. *)
Lemma acq_ts_lt (G : gexec) (b : Z) (A : geid) (t : nat) :
  rvwmo_minus_consistent G → lock_acq G b A →
  greads_byte G A b t lock_free → (t < gwix G A)%nat.
Proof.
  intros Hcons Hacq Hrd. pose proof Hcons as (Hwf & Hppo & Hlv & _).
  pose proof Hwf as (Hnd & _ & _).
  pose proof (lock_acq_gwrites G b A Hwf Hacq) as HA.
  destruct t as [|t]; [by apply gwix_pos|].
  destruct (Hlv A b (S t) lock_free Hrd) as [(r & Hat & Hrb & Hvis) _].
  destruct (gwrite_at_inv G (S t) r Hnd Hat) as [Hr Hrix].
  rewrite -Hrix. apply (gmo_gwix_lt G r A Hwf Hr HA).
  destruct Hvis as [Hmo|Hpo]; [exact Hmo|].
  apply Hppo. left. split; [exact Hpo|].
  destruct Hacq as (v & Hwb & _).
  exists b. split; [left; by exists lock_free|left; by exists v].
Qed.

(** THE DERIVATION CHAIN'S CONCLUSION: for a nonzero read index the named
    source IS a release, sitting at index [t] — so with [acq_src] it is the
    acquire's immediate co-predecessor among the [b]-writes. *)
Lemma acq_src_rel (G : gexec) (b : Z) (A : geid) (t : nat) :
  rvwmo_minus_consistent G → greads_byte G A b t lock_free → (0 < t)%nat →
  ∃ r, lock_rel G b r ∧ r ∈ gwrites G ∧ gwix G r = t.
Proof.
  intros Hcons Hrd Hpos. pose proof Hcons as (Hwf & _ & Hlv & _).
  pose proof Hwf as (Hnd & _ & _).
  destruct t as [|t]; [lia|].
  destruct (Hlv A b (S t) lock_free Hrd) as [(r & Hat & Hrb & _) _].
  destruct (gwrite_at_inv G (S t) r Hnd Hat) as [Hr Hrix].
  by exists r.
Qed.

(* ====================================================================== *)
(** * 3. CRITICAL SECTIONS AND THEIR EXCLUSION

    A CRITICAL SECTION is an acquire/release pair of ONE hart with no
    [b]-write of that hart co-between them.  [lock_paired] says every
    release closes one — this is the "only the holder releases" fact the
    value pattern cannot see (see the header), and it is B2e-3's
    site-classification obligation, buildable from program order alone
    through [lock_cs_intro]. *)

Definition lock_cs (G : gexec) (b : Z) (A R : geid) : Prop :=
  lock_acq G b A ∧ lock_rel G b R ∧ A.1 = R.1 ∧
  (gwix G A < gwix G R)%nat ∧
  (∀ x v, gwrites_byte G x b v → x.1 = A.1 →
     ¬ ((gwix G A < gwix G x)%nat ∧ (gwix G x < gwix G R)%nat)).

Definition lock_paired (G : gexec) (b : Z) : Prop :=
  ∀ R, lock_rel G b R → ∃ A, lock_cs G b A R.

(** Same-hart [b]-writes are co-ordered as they are po-ordered (rules 1–3).
    This is what makes [lock_cs]'s co-order clauses a PROGRAM-ORDER fact. *)
Lemma lock_po_gwix (G : gexec) (b : Z) (x y : geid) (v v' : bv 8) :
  rvwmo_minus_consistent G → gwrites_byte G x b v → gwrites_byte G y b v' →
  gpo G x y → (gwix G x < gwix G y)%nat.
Proof.
  intros Hcons Hx Hy Hpo. pose proof Hcons as (Hwf & Hppo & _ & _).
  apply gmo_gwix_lt;
    [done|by eapply gwrites_byte_gwrites|by eapply gwrites_byte_gwrites|].
  apply Hppo. left. split; [exact Hpo|].
  exists b. split; [left; by exists v|left; by exists v'].
Qed.

(** B2e-3's CONSTRUCTOR: a critical section from program order.  The
    no-[b]-write-in-between clause is asked for in PO form (the shape a
    per-site reading of the lock client's row gives) and converted here. *)
Lemma lock_cs_intro (G : gexec) (b : Z) (A R : geid) :
  rvwmo_minus_consistent G → gpo G A R →
  lock_acq G b A → lock_rel G b R →
  (∀ x v, gwrites_byte G x b v → x.1 = A.1 →
     (A.2 < x.2)%nat → (x.2 < R.2)%nat → False) →
  lock_cs G b A R.
Proof.
  intros Hcons Hpo Hacq Hrel Hno.
  pose proof Hacq as (va & Hwa & _).
  assert (Hlt : (gwix G A < gwix G R)%nat)
    by (by eapply (lock_po_gwix G b A R va lock_free)).
  destruct Hpo as (Hag & Hoff & HsA & HsR).
  split_and!; [done|done|done|done|].
  intros x v Hx Hxag [Hlo Hhi].
  assert (Hsx : is_Some (gx_lbl G x)) by (by eapply gwrites_byte_lbl).
  (* place [x] po-after [A] *)
  assert (HxA : (A.2 < x.2)%nat).
  { destruct (decide (x.2 < A.2)%nat) as [Hc|Hc].
    { assert (gpo G x A) as Hpo' by (by apply gpo_of_lt).
      pose proof (lock_po_gwix G b x A v va Hcons Hx Hwa Hpo'). lia. }
    destruct (decide (x.2 = A.2)) as [Hc'|Hc']; [|lia].
    assert (x = A) as -> by (by apply injective_projections). lia. }
  (* ... and po-before [R] *)
  assert (HxR : (x.2 < R.2)%nat).
  { destruct (decide (R.2 < x.2)%nat) as [Hc|Hc].
    { assert (gpo G R x) as Hpo'.
      { apply gpo_of_lt; [by rewrite Hxag -Hag|done|done|done]. }
      pose proof (lock_po_gwix G b R x lock_free v Hcons Hrel Hx Hpo'). lia. }
    destruct (decide (x.2 = R.2)) as [Hc'|Hc']; [|lia].
    assert (x = R) as ->; [|lia].
    apply injective_projections; [by rewrite Hxag Hag|done]. }
  by eapply Hno.
Qed.

(** The pairing is FUNCTIONAL — a free consequence of [lock_cs]'s own
    no-write-in-between clause, so [lock_paired] needs only existence. *)
Lemma lock_cs_functional (G : gexec) (b : Z) (A R1 R2 : geid) :
  gwf G → lock_cs G b A R1 → lock_cs G b A R2 → R1 = R2.
Proof.
  intros Hwf (Hacq & Hr1 & Hag1 & Hlt1 & Hno1) (_ & Hr2 & Hag2 & Hlt2 & Hno2).
  destruct (decide (R1 = R2)) as [->|Hne]; [done|]. exfalso.
  pose proof Hwf as (Hnd & _ & _).
  assert (Hix : gwix G R1 ≠ gwix G R2).
  { intros Heq. apply Hne. eapply gwix_inj;
      [done|by eapply lock_rel_gwrites|by eapply lock_rel_gwrites|done]. }
  destruct (decide (gwix G R1 < gwix G R2)%nat) as [Hlt|Hge].
  - apply (Hno2 R1 lock_free Hr1); [by rewrite -Hag1|]. split; lia.
  - apply (Hno1 R2 lock_free Hr2); [by rewrite -Hag2|]. lia.
Qed.

(** ** 3.1 THE EXCLUSION INDUCTION

    NO ACQUIRE SITS STRICTLY INSIDE ANOTHER CRITICAL SECTION.  By strong
    induction on the intruding acquire's write index: its co-predecessor
    [r] (the zero write it read, §2) is a release, hence closes SOME
    critical section [(A_k, r)]; either [A_k] is the host acquire [A1] —
    then [r = R1] by functionality, but [r] is co-below [A2] which is
    co-below [R1] — or [A_k ≠ A1], and one of the two overlaps
    [(A_k, r, A1)] / [(A1, R1, A_k)] is an intrusion by a co-EARLIER
    acquire, which the induction hypothesis refutes. *)
Lemma acq_no_overlap (G : gexec) (b : Z) :
  rvwmo_minus_consistent G → lock_pattern G b → lock_paired G b →
  ∀ n A2, (gwix G A2 ≤ n)%nat → lock_acq G b A2 →
  ∀ A1 R1, lock_cs G b A1 R1 →
    (gwix G A1 < gwix G A2)%nat → (gwix G A2 < gwix G R1)%nat → False.
Proof.
  intros Hcons Hpat Hpair. pose proof Hcons as (Hwf & _ & _ & _).
  induction n as [|n IH];
    intros A2 Hle HA2 A1 R1 Hcs1 Hlt1 Hlt2.
  { pose proof (gwix_pos G A2 (lock_acq_gwrites G b A2 Hwf HA2)). lia. }
  pose proof Hcs1 as (HA1 & HR1 & Hag1 & Hlt1' & Hno1).
  (* the intruder read zero at [b], at some index [t] *)
  destruct (lock_acq_read G b A2 Hpat HA2) as [_ (t & Hrd2)].
  pose proof (acq_ts_lt G b A2 t Hcons HA2 Hrd2) as Htlt.
  (* the host acquire is not inside the intruder's window *)
  pose proof HA1 as (v1 & Hwb1 & Hnz1).
  destruct (acq_src G b A2 t Hcons HA2 Hrd2 A1 v1 Hwb1) as [Hle1|Hbad];
    [|lia].
  pose proof (gwix_pos G A1 (lock_acq_gwrites G b A1 Hwf HA1)) as Hpos1.
  (* so the window bottom names a real write: the intruder's co-predecessor *)
  destruct (acq_src_rel G b A2 t Hcons Hrd2 ltac:(lia)) as (r & Hr & Hrw & Hrix).
  assert (Hne_r1 : A1 ≠ r).
  { intros ->. by eapply lock_acq_not_rel. }
  assert (Hlt_1r : (gwix G A1 < gwix G r)%nat).
  { destruct (decide (gwix G A1 = gwix G r)) as [Heq|Hne]; [|lia].
    destruct Hne_r1. eapply gwix_inj;
      [by destruct Hwf as (?&?&?)|by eapply lock_acq_gwrites|done|done]. }
  (* the co-predecessor closes SOME critical section *)
  destruct (Hpair r Hr) as (Ak & Hcsk).
  destruct (decide (Ak = A1)) as [->|Hnek].
  { (* it is the host's own release, but it is co-below the intruder *)
    assert (r = R1) as -> by (by eapply lock_cs_functional). lia. }
  pose proof Hcsk as (HAk & _ & _ & Hltk & _).
  assert (Hixk : gwix G Ak ≠ gwix G A1).
  { intros Heq. apply Hnek. eapply gwix_inj;
      [by destruct Hwf as (?&?&?)|by eapply lock_acq_gwrites
      |by eapply lock_acq_gwrites|done]. }
  destruct (decide (gwix G Ak < gwix G A1)%nat) as [Hkl|Hkg].
  - (* [A1] intrudes into [(Ak, r)], and [A1] is co-earlier than [A2] *)
    apply (IH A1 ltac:(lia) HA1 Ak r Hcsk); lia.
  - (* [Ak] intrudes into [(A1, R1)], and [Ak] is co-earlier than [A2] *)
    apply (IH Ak ltac:(lia) HAk A1 R1 Hcs1); lia.
Qed.

(** ** 3.2 THE EXPORT: two distinct critical sections are DISJOINT and
    TOTALLY ORDERED — one closes before the other opens. *)
Theorem win_excl_of_pattern (G : gexec) (b : Z) :
  rvwmo_minus_consistent G → lock_pattern G b → lock_paired G b →
  ∀ A1 R1 A2 R2, lock_cs G b A1 R1 → lock_cs G b A2 R2 → A1 ≠ A2 →
    (gwix G R1 < gwix G A2)%nat ∨ (gwix G R2 < gwix G A1)%nat.
Proof.
  intros Hcons Hpat Hpair A1 R1 A2 R2 Hcs1 Hcs2 Hne.
  pose proof Hcons as (Hwf & _ & _ & _). pose proof Hwf as (Hnd & _ & _).
  pose proof Hcs1 as (HA1 & HR1 & _ & Hlt1 & _).
  pose proof Hcs2 as (HA2 & HR2 & _ & Hlt2 & _).
  assert (Hix : gwix G A1 ≠ gwix G A2).
  { intros Heq. apply Hne. eapply gwix_inj;
      [done|by eapply lock_acq_gwrites|by eapply lock_acq_gwrites|done]. }
  (* a release is never an acquire, so the boundaries never coincide *)
  assert (Hb1 : gwix G R1 ≠ gwix G A2).
  { intros Heq. eapply (lock_acq_not_rel G b A2); [done|].
    assert (R1 = A2) as <-; [|done]. eapply gwix_inj;
      [done|by eapply lock_rel_gwrites|by eapply lock_acq_gwrites|done]. }
  assert (Hb2 : gwix G R2 ≠ gwix G A1).
  { intros Heq. eapply (lock_acq_not_rel G b A1); [done|].
    assert (R2 = A1) as <-; [|done]. eapply gwix_inj;
      [done|by eapply lock_rel_gwrites|by eapply lock_acq_gwrites|done]. }
  destruct (decide (gwix G A1 < gwix G A2)%nat) as [Hlt|Hge].
  - left.
    destruct (decide (gwix G A2 < gwix G R1)%nat) as [Hin|Hout]; [|lia].
    exfalso. eapply (acq_no_overlap G b Hcons Hpat Hpair (gwix G A2) A2);
      [lia|exact HA2|exact Hcs1|exact Hlt|exact Hin].
  - right.
    assert (Hlt' : (gwix G A2 < gwix G A1)%nat) by lia.
    destruct (decide (gwix G A1 < gwix G R2)%nat) as [Hin|Hout]; [|lia].
    exfalso. eapply (acq_no_overlap G b Hcons Hpat Hpair (gwix G A1) A1);
      [lia|exact HA1|exact Hcs2|exact Hlt'|exact Hin].
Qed.

(* ====================================================================== *)
(** * 4. [cs_kill] — THE ASSEMBLED CONTRADICTION

    The K1-CS configuration: a violation [gviol G e w] whose witness [e]
    reads a write [w0] lying gmo-between [w] and [e], with [e]/[w] covered
    by hart [e.1]'s critical section and [w0] by hart [w0.1]'s.  Every
    coverage fact is an EXPLICIT hypothesis; discharging them is B2e-3's.

    THE FOUR-STEP CYCLE, mirrored across the window order:

      [ACQ_j] first :  w  gmo< w0 gmo< REL_j gmo< ACQ_h gmo< w
      [ACQ_h] first :  w0 gmo< e  gmo< REL_h gmo< ACQ_j gmo< w0

    with the release steps by ppo rule 4 (the covering fence) and the
    acquire steps by ppo rule 5. *)

Theorem cs_kill (G : gexec) (b : Z) (e w w0 ACQh RELh ACQj RELj : geid) :
  (* the declared model *)
  rvwmo_minus_consistent G →
  (* the lock-word protocol on byte [b] *)
  lock_pattern G b → lock_paired G b →
  (* the configuration ([kill_K1_racy]'s core) *)
  gviol G e w → gmo_lt G w w0 → gmo_lt G w0 e →
  (* CS coverage on hart [e.1]: [e] (hence [w]) is inside [ACQh]'s section,
     and a release fence covers [e] to that section's release *)
  lock_cs G b ACQh RELh →
  gpo G ACQh e → glbl_is G ACQh lb_aq → gfence_covers G e RELh →
  (* CS coverage on hart [w0.1]: [w0] is inside [ACQj]'s section, and a
     release fence covers [w0] to that section's release *)
  lock_cs G b ACQj RELj →
  gpo G ACQj w0 → glbl_is G ACQj lb_aq → gfence_covers G w0 RELj →
  (* the two sections are distinct — [kill_K1_racy]'s own cross-hart premise *)
  e.1 ≠ w0.1 →
  False.
Proof.
  intros Hcons Hpat Hpair Hv Hmo_ww0 Hmo_w0e
         Hcsh Hpoh Haqh Hfh Hcsj Hpoj Haqj Hfj Hhart.
  pose proof Hcons as (Hwf & Hppo & _ & _).
  (* the acquires sit on the two harts, so they are distinct events *)
  assert (Hne : ACQh ≠ ACQj).
  { intros Heq. apply Hhart.
    destruct Hpoh as (Hh & _). destruct Hpoj as (Hj & _).
    by rewrite -Hh Heq Hj. }
  pose proof Hcsh as (HAh & HRh & _ & _ & _).
  pose proof Hcsj as (HAj & HRj & _ & _ & _).
  (* the pattern makes both acquires READS, which is rule 5's other half *)
  destruct (lock_acq_read G b ACQh Hpat HAh) as [Hrh _].
  destruct (lock_acq_read G b ACQj Hpat HAj) as [Hrj _].
  (* rule 5, twice *)
  pose proof Hv as (Hpo_ew & _ & _ & _).
  assert (Hpo_hw : gpo G ACQh w).
  { destruct Hpoh as (Ha1 & Ho1 & Hs1 & _).
    destruct Hpo_ew as (Ha2 & Ho2 & _ & Hs2).
    split_and!; [congruence|lia|done|done]. }
  assert (Hmo_hw : gmo_lt G ACQh w)
    by (by eapply acq_gmo_after).
  assert (Hmo_jw0 : gmo_lt G ACQj w0)
    by (by eapply acq_gmo_after).
  (* rule 4, twice *)
  assert (Hmo_erh : gmo_lt G e RELh) by (by eapply fence_gmo_after).
  assert (Hmo_w0rj : gmo_lt G w0 RELj) by (by eapply fence_gmo_after).
  (* the window order *)
  destruct (win_excl_of_pattern G b Hcons Hpat Hpair ACQh RELh ACQj RELj
              Hcsh Hcsj Hne) as [Hwin|Hwin].
  - (* [ACQh]'s section closes first: w0 < e < RELh < ACQj < w0 *)
    assert (Hmo_rhj : gmo_lt G RELh ACQj).
    { eapply gwix_lt_gmo;
        [done|by eapply lock_rel_gwrites|by eapply lock_acq_gwrites|done]. }
    eapply (gmo_lt_irrefl G w0), (gmo_lt_trans G w0 e w0); [exact Hmo_w0e|].
    eapply gmo_lt_trans; [exact Hmo_erh|].
    eapply gmo_lt_trans; [exact Hmo_rhj|exact Hmo_jw0].
  - (* [ACQj]'s section closes first: w < w0 < RELj < ACQh < w *)
    assert (Hmo_rjh : gmo_lt G RELj ACQh).
    { eapply gwix_lt_gmo;
        [done|by eapply lock_rel_gwrites|by eapply lock_acq_gwrites|done]. }
    eapply (gmo_lt_irrefl G w), (gmo_lt_trans G w w0 w); [exact Hmo_ww0|].
    eapply gmo_lt_trans; [exact Hmo_w0rj|].
    eapply gmo_lt_trans; [exact Hmo_rjh|exact Hmo_hw].
Qed.
