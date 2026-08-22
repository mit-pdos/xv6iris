(** * WeakRvwmoDec.v — [RacyD] IS DECIDABLE, so the topological sort needs
      no side condition

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.1 (F2(ii)),
    and [WeakRvwmoTopo.v]'s header note (D): the minimal-element search of a
    finite topological sort cannot pick a minimum constructively without
    deciding the relation, so [WeakRvwmoTopo.topo_exists] and
    [normalize_of_acyclic] were stated with an explicit hypothesis
    [∀ x y, Decision (RacyD GD x y)].

    THIS FILE DISCHARGES IT — CONSTRUCTIVELY, with no [Classical] import and
    no excluded middle.  Every existential inside [WeakRvwmoAcyc]'s relation
    is pinned by a row lookup or a list position, so each arm is a BOUNDED
    search:

      - [gwr_bytes] / [grd_bytes] enumerate an event's write/read byte
        entries off its label ([gwrites_byte] / [greads_byte] become list
        membership — [gwrites_byte_bytes] / [greads_byte_bytes]);
      - [gacc_addrs] enumerates the addresses an event touches, so
        [gaccesses]' address existential (and [gpoloc]'s "∃ a") is a search
        over a list rather than over [Z];
      - [gfence_covers]' "∃ pr pw sr sw" is NOT searched over the sixteen
        bit patterns: the fence's position [kf] DETERMINES the label and
        hence the four bits, so [gfcov_at] reads them off [gx_lbl] and the
        only search left is over [kf ∈ seq (S e1.2) (e2.2 - S e1.2)];
      - [gwrite_at], [gwix], [gpos] are functions; [gmo_lt] and the dep set
        are list membership.

    The reformulations are stated as [↔]s ([gpoloc_alt], [gfence_covers_alt],
    [grf_alt], [gco_alt], [gfr_alt]) and turned into instances by [dec_iff],
    so nothing here changes the model.

    Delivered: [racyD_dec], and [topo_exists'] / [normalize_of_acyclic'] —
    [WeakRvwmoTopo]'s two theorems with the [Decision] hypothesis removed.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2
                            WeakRvwmoGraph WeakRvwmoXchg WeakRvwmoNorm
                            WeakRvwmoAcyc WeakRvwmoTopo.

(* ====================================================================== *)
(** * 1. Two generic tools *)

(** Transport a decision along an equivalence.  (Written by hand: the
    [Decision] plumbing lemma stdpp exports goes the other way round.) *)
Definition dec_iff {P Q : Prop} (H : P ↔ Q) (d : Decision Q) : Decision P :=
  match d with
  | left h => left (proj2 H h)
  | right h => right (λ p, h (proj1 H p))
  end.

(** Bounded search over a list — [WeakRvwmoTopo.list_ex_dec] in [Decision]
    clothing. *)
Lemma list_exists_dec {A} (P : A → Prop) (Pdec : ∀ x, Decision (P x))
    (l : list A) : Decision (∃ x, x ∈ l ∧ P x).
Proof.
  destruct (list_ex_dec P Pdec l) as [[x [Hx Hp]]|Hno].
  - left. by exists x.
  - right. intros (x & Hx & Hp). by eapply Hno.
Defined.

(** [zip]'s lookup, in the shape the read-byte enumeration wants. *)
Lemma lookup_zip {A B} (l : list A) (k : list B) j x y :
  zip l k !! j = Some (x, y) ↔ l !! j = Some x ∧ k !! j = Some y.
Proof.
  rewrite /zip lookup_zip_with.
  destruct (l !! j) as [x0|]; destruct (k !! j) as [y0|]; simpl;
    (split; [intros H; simplify_eq; done
            |intros [H1 H2]; simplify_eq; done]).
Qed.

(* ====================================================================== *)
(** * 2. THE BYTE ENUMERATIONS

    An event's byte footprint is a function of its label, so both
    [gwrites_byte] and [greads_byte] are list membership. *)

Definition gwr_bytes (G : gexec) (e : geid) : list (Z * bv 8) :=
  match gx_lbl G e ≫= lb_wr with
  | Some (base, vs) => imap (λ j v, (acc_addr base j, v)) vs
  | None => []
  end.

Definition grd_bytes (G : gexec) (e : geid) : list (Z * nat * bv 8) :=
  match gx_lbl G e ≫= lb_rd with
  | Some (base, ts, vs) =>
      imap (λ j tv, (acc_addr base j, tv.1, tv.2)) (zip ts vs)
  | None => []
  end.

Lemma gwrites_byte_bytes G e a v :
  gwrites_byte G e a v ↔ (a, v) ∈ gwr_bytes G e.
Proof.
  rewrite /gwrites_byte /gwr_bytes.
  destruct (gx_lbl G e) as [l|] eqn:Hl; simpl.
  - destruct (lb_wr l) as [[base vs]|] eqn:Hw; simpl.
    + rewrite elem_of_list_lookup. split.
      * intros (l0 & base0 & vs0 & j & Hl0 & Hw0 & Hv & Ha).
        assert (l0 = l) as -> by congruence.
        rewrite Hw in Hw0. simplify_eq.
        exists j. by rewrite list_lookup_imap Hv /=.
      * intros (j & Hj). rewrite list_lookup_imap in Hj.
        destruct (vs !! j) as [v0|] eqn:Hv; simpl in Hj; [|done].
        simplify_eq. by exists l, base, vs, j.
    + split.
      * intros (l0 & base0 & vs0 & j & Hl0 & Hw0 & _).
        assert (l0 = l) as -> by congruence.
        rewrite Hw in Hw0. simplify_eq.
      * by intros ?%elem_of_nil.
  - split.
    + intros (l0 & base0 & vs0 & j & Hl0 & _). simplify_eq.
    + by intros ?%elem_of_nil.
Qed.

Lemma greads_byte_bytes G e a t v :
  greads_byte G e a t v ↔ (a, t, v) ∈ grd_bytes G e.
Proof.
  rewrite /greads_byte /grd_bytes.
  destruct (gx_lbl G e) as [l|] eqn:Hl; simpl.
  - destruct (lb_rd l) as [[[base ts] vs]|] eqn:Hr; simpl.
    + rewrite elem_of_list_lookup. split.
      * intros (l0 & base0 & ts0 & vs0 & j & Hl0 & Hr0 & Ht & Hv & Ha).
        assert (l0 = l) as -> by congruence.
        rewrite Hr in Hr0. simplify_eq.
        exists j. rewrite list_lookup_imap.
        by rewrite (proj2 (lookup_zip _ _ j _ _) (conj Ht Hv)) /=.
      * intros (j & Hj). rewrite list_lookup_imap in Hj.
        destruct (zip ts vs !! j) as [[t0 v0]|] eqn:Hz; simpl in Hj; [|done].
        simplify_eq. apply lookup_zip in Hz as [Ht Hv].
        by exists l, base, ts, vs, j.
    + split.
      * intros (l0 & base0 & ts0 & vs0 & j & Hl0 & Hr0 & _).
        assert (l0 = l) as -> by congruence.
        rewrite Hr in Hr0. simplify_eq.
      * by intros ?%elem_of_nil.
  - split.
    + intros (l0 & base0 & ts0 & vs0 & j & Hl0 & _). simplify_eq.
    + by intros ?%elem_of_nil.
Qed.

(** The addresses an event touches. *)
Definition gacc_addrs (G : gexec) (e : geid) : list Z :=
  ((λ x : Z * bv 8, x.1) <$> gwr_bytes G e) ++
  ((λ x : Z * nat * bv 8, x.1.1) <$> grd_bytes G e).

Lemma gaccesses_addrs G e a : gaccesses G e a ↔ a ∈ gacc_addrs G e.
Proof.
  rewrite /gaccesses /gacc_addrs elem_of_app !elem_of_list_fmap. split.
  - intros [(v & Hw)|(t & v & Hr)].
    + left. exists (a, v). split; [done|]. by apply gwrites_byte_bytes.
    + right. exists (a, t, v). split; [done|]. by apply greads_byte_bytes.
  - intros [(x & Ha & Hx)|(x & Ha & Hx)].
    + destruct x as [a0 v]. simpl in Ha. subst a.
      left. exists v. by apply gwrites_byte_bytes.
    + destruct x as [[a0 t] v]. simpl in Ha. subst a.
      right. exists t, v. by apply greads_byte_bytes.
Qed.

(* ====================================================================== *)
(** * 3. THE ELEMENTARY DECISIONS *)

Global Instance gwrites_byte_dec G e a v : Decision (gwrites_byte G e a v) :=
  dec_iff (gwrites_byte_bytes G e a v) _.

Global Instance greads_byte_dec G e a t v : Decision (greads_byte G e a t v) :=
  dec_iff (greads_byte_bytes G e a t v) _.

Global Instance gaccesses_dec G e a : Decision (gaccesses G e a) :=
  dec_iff (gaccesses_addrs G e a) _.

Global Instance glbl_is_dec G e P : Decision (glbl_is G e P).
Proof.
  rewrite /glbl_is. destruct (gx_lbl G e) as [l|] eqn:Hl.
  - destruct (decide (P l = true)) as [HP|HP].
    + left. by exists l.
    + right. intros (l0 & Hl0 & HP0). simplify_eq.
  - right. intros (l0 & Hl0 & _). simplify_eq.
Qed.

(** [gmem] IS [glbl_is _ _ lb_is_mem], definitionally. *)
Global Instance gmem_dec G e : Decision (gmem G e) := glbl_is_dec G e lb_is_mem.

Global Instance gpo_dec G x y : Decision (gpo G x y).
Proof. rewrite /gpo. apply _. Qed.

Global Instance gmo_lt_dec G x y : Decision (gmo_lt G x y).
Proof. rewrite /gmo_lt. apply _. Qed.

Global Instance gpow_dec G e w : Decision (gpow G e w).
Proof. rewrite /gpow. apply _. Qed.

Global Instance gacq_po_dec G e1 e2 : Decision (gacq_po G e1 e2).
Proof. rewrite /gacq_po. apply _. Qed.

Global Instance grel_acq_dec G e1 e2 : Decision (grel_acq G e1 e2).
Proof. rewrite /grel_acq. apply _. Qed.

(* ====================================================================== *)
(** * 4. THE ARMS THAT NEEDED A REFORMULATION *)

(** ** 4.1 [gpoloc]: the "∃ a" is a search over [Z] as written. *)

Lemma gpoloc_alt G e1 e2 :
  gpoloc G e1 e2 ↔
  gpo G e1 e2 ∧ ∃ a, a ∈ gacc_addrs G e1 ∧ gaccesses G e2 a.
Proof.
  rewrite /gpoloc. split.
  - intros (Hpo & a & H1 & H2). split; [done|].
    exists a. split; [by apply gaccesses_addrs|done].
  - intros (Hpo & a & H1 & H2). split; [done|].
    exists a. split; [by apply gaccesses_addrs|done].
Qed.

Global Instance gpoloc_dec G e1 e2 : Decision (gpoloc G e1 e2).
Proof.
  apply (dec_iff (gpoloc_alt G e1 e2)), and_dec; [apply _|].
  apply list_exists_dec. intros a. apply _.
Qed.

(** ** 4.2 [gfence_covers]: the four bits are DETERMINED by the fence's
       position, so only the position is searched. *)

Definition gfcov_at (G : gexec) (e1 e2 : geid) (kf : nat) : Prop :=
  match gx_lbl G (e1.1, kf) with
  | Some (LFence pr pw sr sw) =>
      ((glbl_is G e1 lb_is_r ∧ pr = true) ∨
       (glbl_is G e1 lb_is_w ∧ pw = true)) ∧
      ((glbl_is G e2 lb_is_r ∧ sr = true) ∨
       (glbl_is G e2 lb_is_w ∧ sw = true))
  | _ => False
  end.

Global Instance gfcov_at_dec G e1 e2 kf : Decision (gfcov_at G e1 e2 kf).
Proof.
  rewrite /gfcov_at.
  destruct (gx_lbl G (e1.1, kf)) as [l|]; [destruct l|];
    try (right; by intros []).
  apply _.
Qed.

Lemma gfence_covers_alt G e1 e2 :
  gfence_covers G e1 e2 ↔
  e1.1 = e2.1 ∧ (e1.2 < e2.2)%nat ∧
  ∃ kf, kf ∈ seq (S e1.2) (e2.2 - S e1.2) ∧ gfcov_at G e1 e2 kf.
Proof.
  rewrite /gfence_covers /gfence_between /gfcov_at. split.
  - intros (pr & pw & sr & sw & (Hag & Hlt & kf & Hk1 & Hk2 & Hlf) & C1 & C2).
    split_and!; [done|done|]. exists kf. split.
    + apply elem_of_seq. lia.
    + rewrite Hlf. by split.
  - intros (Hag & Hlt & kf & Hkf & Hcov).
    apply elem_of_seq in Hkf.
    destruct (gx_lbl G (e1.1, kf)) as [l|] eqn:Hl; [|done].
    destruct l as [| |pr pw sr sw|]; try done.
    destruct Hcov as [C1 C2].
    exists pr, pw, sr, sw. split_and!; [done|done| |done|done].
    exists kf. split_and!; [lia|lia|done].
Qed.

Global Instance gfence_covers_dec G e1 e2 : Decision (gfence_covers G e1 e2).
Proof.
  apply (dec_iff (gfence_covers_alt G e1 e2)), and_dec; [apply _|].
  apply and_dec; [apply _|]. apply list_exists_dec. intros kf. apply _.
Qed.

Global Instance gppo_dec G e1 e2 : Decision (gppo G e1 e2).
Proof. rewrite /gppo. apply _. Qed.

(** ** 4.3 [grf] / [gco] / [gfr]: the byte existentials *)

Lemma grf_alt G w r :
  grf G w r ↔ ∃ x, x ∈ grd_bytes G r ∧ gwrite_at G x.1.2 = Some w.
Proof.
  rewrite /grf. split.
  - intros (a & t & v & Hrd & Hat). exists (a, t, v).
    split; [by apply greads_byte_bytes|done].
  - intros ([[a t] v] & Hx & Hat). simpl in Hat.
    exists a, t, v. split; [by apply greads_byte_bytes|done].
Qed.

Global Instance grf_dec G w r : Decision (grf G w r).
Proof.
  apply (dec_iff (grf_alt G w r)), list_exists_dec. intros x. apply _.
Qed.

Lemma gco_alt G w w' :
  gco G w w' ↔
  (gwix G w < gwix G w')%nat ∧
  ∃ x, x ∈ gwr_bytes G w ∧ ∃ y, y ∈ gwr_bytes G w' ∧ y.1 = x.1.
Proof.
  rewrite /gco. split.
  - intros (a & v & v' & H1 & H2 & Hlt). split; [done|].
    exists (a, v). split; [by apply gwrites_byte_bytes|].
    exists (a, v'). split; [by apply gwrites_byte_bytes|done].
  - intros (Hlt & [a v] & Hx & [a' v'] & Hy & Heq). simpl in Heq. subst a'.
    exists a, v, v'. split_and!; [by apply gwrites_byte_bytes
                                 |by apply gwrites_byte_bytes|done].
Qed.

Global Instance gco_dec G w w' : Decision (gco G w w').
Proof.
  apply (dec_iff (gco_alt G w w')), and_dec; [apply _|].
  apply list_exists_dec. intros x. apply list_exists_dec. intros y. apply _.
Qed.

Lemma gfr_alt G r w' :
  gfr G r w' ↔
  r ≠ w' ∧ ∃ x, x ∈ grd_bytes G r ∧ (x.1.2 < gwix G w')%nat ∧
                ∃ y, y ∈ gwr_bytes G w' ∧ y.1 = x.1.1.
Proof.
  rewrite /gfr. split.
  - intros (Hne & a & t & v & v' & Hrd & Hwb & Hlt). split; [done|].
    exists (a, t, v). split; [by apply greads_byte_bytes|].
    split; [done|]. exists (a, v'). split; [by apply gwrites_byte_bytes|done].
  - intros (Hne & [[a t] v] & Hx & Hlt & [a' v'] & Hy & Heq).
    simpl in Hlt, Heq. subst a'. split; [done|].
    exists a, t, v, v'. split_and!; [by apply greads_byte_bytes
                                     |by apply gwrites_byte_bytes|done].
Qed.

Global Instance gfr_dec G r w' : Decision (gfr G r w').
Proof.
  apply (dec_iff (gfr_alt G r w')), and_dec; [apply _|].
  apply list_exists_dec. intros x. apply and_dec; [apply _|].
  apply list_exists_dec. intros y. apply _.
Qed.

(* ====================================================================== *)
(** * 5. THE THEOREM *)

Global Instance racy_dec G x y : Decision (Racy G x y).
Proof. rewrite /Racy. apply _. Qed.

Global Instance racyD_dec GD x y : Decision (RacyD GD x y).
Proof. rewrite /RacyD. apply _. Qed.

(* ====================================================================== *)
(** * 6. [WeakRvwmoTopo]'s theorems, hypothesis-free *)

Theorem topo_exists' (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x, ¬ tc (RacyD GD) x x) →
  ∃ L, lin_extD GD L.
Proof.
  intros Hcons Hacy. eapply topo_exists; [done|intros x y; apply _|done].
Qed.

Corollary normalize_of_acyclic' (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x, ¬ tc (RacyD GD) x x) →
  ∃ (GD' : gdexec) (pi : nat → nat),
    rvwmo_minus_deps_consistent GD' ∧
    grule14 (gd_g GD') ∧
    rows_rel pi (gd_g GD) (gd_g GD') ∧
    gd_deps GD' = gd_deps GD ∧
    wperm pi (gd_g GD) (gd_g GD').
Proof.
  intros Hcons Hacy.
  eapply normalize_of_acyclic; [done|intros x y; apply _|done].
Qed.

Print Assumptions racyD_dec.
Print Assumptions topo_exists'.
Print Assumptions normalize_of_acyclic'.
