(* Tests for FastLia.v's override.  EVERY lemma uses [lia_fast], i.e. THE
   FALLBACK IS DELETED: if the filter drops a hypothesis the solve needs, these
   fail rather than silently passing through to upstream.  That is the only
   check that means anything -- with the fallback in place [lia] cannot fail,
   it can only get slow (FastSetSolver.v records the same discipline). *)
Require Import FastLia.
From Stdlib Require Import ZArith List.
Open Scope Z_scope.

Section Probe.
  Variable T : Type.
  Variable P : T -> Prop.
  Variables x y z : T.
  Variable U : Type.
  (* a data family and a function indexed by a proof, for the two
     dependent-survivor probes below *)
  Variable R : P x -> Type.
  Variable f : P x -> Z.

  (* Every lemma below uses lia_fast, i.e. THE FALLBACK IS DELETED: if the
     filter drops something needed, these fail rather than silently pass. *)

  Lemma probe_noise (a b : Z)
    (H1 : P x) (H2 : P y) (H3 : P z) (H4 : x = y) (H5 : y = z)
    (H6 : list T = list T) (H7 : forall t, P t -> P t)
    (Ha : a = b + 1) (Hb : 0 <= b) : 0 <= a.
  Proof. lia_fast. Qed.

  Lemma probe_transitive (a b c : Z) (H1 : P x)
    (H2 : a <= b) (H3 : b <= c) : a <= c.
  Proof. lia_fast. Qed.

  (* a bare equation between two Z variables: arithmetic by its TYPE only *)
  Lemma probe_bare_eq (a b : Z) (H1 : P x) (H2 : P y) (Heq : a = b) (Hb : 0 <= b) :
    0 <= a.
  Proof. lia_fast. Qed.

  (* mixed nat/Z through Z.of_nat *)
  Lemma probe_ofnat (n : nat) (a : Z) (H1 : P x)
    (Ha : a = Z.of_nat n) : 0 <= a.
  Proof. lia_fast. Qed.

  (* bool through Z.leb, which zify does read *)
  Lemma probe_bool (a b : Z) (H1 : P x) (H2 : P y) (Hb : Z.leb a b = true) : a <= b.
  Proof. lia_fast. Qed.

  (* ex falso: a False hypothesis shares nothing with the goal *)
  Lemma probe_false (a : Z) (H1 : P x) (Hf : False) : a = 42.
  Proof. lia_fast. Qed.

  (* ARGUMENT POSITION -- the case a hand-written [clear -] cannot reach *)
  Definition needs (a : Z) (_ : 0 <= a) : Z := a.
  Lemma probe_argpos (a b : Z) (H1 : P x) (H2 : P y) (H3 : P z)
    (Ha : a = b + 1) (Hb : 0 <= b) : Z.
  Proof. exact (needs a ltac:(lia_fast)). Qed.

  (* REGRESSION, ProofCreateMkdir.v:1750.  ONE INEQUALITY PER NUMERIC TYPE,
     each provable ONLY from the inequality hypothesis, so a vocabulary entry
     whose head does not match what the notation actually elaborates to drops
     that hypothesis and fails the test here rather than hanging a proof in the
     tree.  [(0 <= 0)%nat] is [Peano.le], NOT [Nat.le]; naming the latter dropped
     every nat inequality and the fallback hid it. *)
  Lemma probe_ineq_nat (m n : nat) (H1 : P x) (Hmn : (m <= n)%nat) : (m <= n)%nat.
  Proof. lia_fast. Qed.
  Lemma probe_ineq_nat_lt (m n : nat) (H1 : P x) (Hmn : (m < n)%nat) : (m < n)%nat.
  Proof. lia_fast. Qed.
  Lemma probe_ineq_nat_absurd (H1 : P x) (H2 : P y) (Hbad : (1 <= 0)%nat) : False.
  Proof. lia_fast. Qed.
  Lemma probe_ineq_Z (m n : Z) (H1 : P x) (Hmn : m <= n) : m <= n.
  Proof. lia_fast. Qed.
  Lemma probe_ineq_N (m n : N) (H1 : P x) (Hmn : N.le m n) : N.le m n.
  Proof. lia_fast. Qed.
  Lemma probe_ineq_pos (m n : positive) (H1 : P x) (Hmn : Pos.le m n) : Pos.le m n.
  Proof. lia_fast. Qed.

  (* REGRESSION, ProofInitlog.v:2293.  A hypothesis that is not a [Prop] must
     SURVIVE the shrink even when nothing in the goal names it: clearing one
     restricts the context of every undefined evar, so a sibling goal sharing an
     evar with this one stops unifying -- silently, and far from here.  Noise
     that IS a Prop still goes. *)
  Lemma probe_keeps_data (a b : Z) (u : U) (Hnoise : P x)
    (Ha : a = b + 1) (Hb : 0 <= b) : 0 <= a.
  Proof.
    lia_shrink.
    lazymatch goal with _ : U |- _ => idtac end.
    Fail lazymatch goal with _ : P x |- _ => idtac end.
    lia_slow.
  Qed.

  (* THE [clear] MUST STAY WELL-FORMED WITHOUT A PER-HYPOTHESIS LIVE SCAN.
     [lia_shrink] scans only the GOAL for names it must not drop; a SURVIVING
     hypothesis whose type names a dropped one is not predicted, it is left to
     [SetShrink.clear_greedily] to discover from the failure Coq raises and to
     bisect around.  Here [Hnoise : P x] is a non-arithmetic Prop, so it is
     doomed -- but [r : R Hnoise] is not a Prop, so it stays and still names it.
     A [clear] that took the whole doomed list at once fails; what must happen
     is that the rest still goes and the solve still closes. *)
  Lemma probe_dependent_survivor (a b : Z) (Hnoise : P x) (r : R Hnoise)
    (Ha : a = b + 1) (Hb : 0 <= b) : 0 <= a.
  Proof. lia_fast. Qed.

  (* ... and the same shape where the survivor is an ARITHMETIC Prop, so the
     bisection runs with the hypothesis [lia] actually needs on the far side
     of the failing [clear]. *)
  Lemma probe_dependent_arith (a : Z) (Hnoise : P x) (Hb : 0 <= f Hnoise)
    (Ha : a = f Hnoise) : 0 <= a.
  Proof. lia_fast. Qed.

  (* a hypothesis under a binder.  lia does not instantiate a universally
     quantified hypothesis, so NEITHER arm proves this -- the check is that
     the filter behaves the same as upstream, not that it is stronger. *)
  Lemma probe_forall (a : Z) (H1 : P x) (Hf : forall k : Z, 0 <= k -> k <= a)
    : 0 <= a.
  Proof. Fail lia_fast. Fail lia_slow. exact (Hf 0 (Z.le_refl 0)). Qed.
End Probe.
