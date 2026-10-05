/-
MachCSL: the stdpp `relations` layer the weak-memory port stands on (Rocq
stdpp `relations.v`: `rtc`, `tc`, `nsteps`, `sc` and the lemmas the Rocq
weak files -- `iris/Weak*.v`, `iris/Ax*.v` -- actually cite; gap G1 of
`notes/weak-port-iris-gaps.md`).

THE CLOSURES ARE THE LIBRARY'S, NOT NEW INDUCTIVES.  `rtc R` is iris-lean's
`FromMathlib.Relation.ReflTransGen R`, `tc R` is core's
`Relation.TransGen R`, and `nsteps R` is iris-lean's `Relation.Iterate R`,
each through an `abbrev`, so every library lemma and instance about those
types (`Trans`, `head_induction_on`, `ReflTrans_iff_exists_iterate`, ...)
applies to the stdpp spelling unchanged, and the stdpp names below apply to
anything the library produced.

Name mapping.  The stdpp names are kept, in namespace `MachCSL`: each
component of an stdpp relation-lemma name is one lowercase word, which is
already Lean's theorem spelling (`rtc_transitive`, `tc_rtc_l`,
`rtc_nsteps_2`, ...), so no name changes.  The weak files cite, by count:
`rtc_l` 182, `nsteps_l` 153, `rtc_refl` 98, `tc_once` 95, `tc_l` 58,
`rtc_transitive` 57, `rtc_r` 37, `rtc_once` 36, `tc_rtc` 31, `rtc_inv` 22,
`nsteps_trans` 12, `tc_rtc_r` 9, `tc_transitive` 8, `nsteps_once` 7,
`nsteps_O` 7, `rtc_ind_r` 6, `tc_rtc_l` 6, `rtc_nsteps_2` 4, `rtc_tc` 3,
`rtc_nsteps_1` 3, `tc_r` 3, `rtc_nsteps` 2, `rtc_subrel` 2.  Added beside
them because they are their direct duals and cost a line: `rtc_ind_l`,
`rtc_inv_r`, `nsteps_r`, `nsteps_once_inv`, and `sc` with `sc_lr`/`sc_rl`/
`sc_symm` (stdpp's `sc`; the weak files' 46 `sc` hits are all RISC-V
store-conditional, never the symmetric closure).

Deviations from Rocq.
1. THE CONSTRUCTORS ARE LEMMAS.  stdpp's `rtc`/`tc`/`nsteps` are their own
   inductives with HEAD-style constructors (`rtc_l : R x y → rtc y z →
   rtc x z`); the library types are TAIL-style (`ReflTransGen.tail`,
   `TransGen.tail`, `Iterate.tail`).  `rtc_refl`/`rtc_l`, `tc_once`/`tc_l`
   and `nsteps_O`/`nsteps_l` are therefore theorems, not constructors, and a
   bare `induction h` on an `rtc`/`tc`/`nsteps` hypothesis splits at the
   LAST step (stdpp: the first).  A Rocq `induction H` that needs the first
   step is ported as `induction h using FromMathlib.Relation.ReflTransGen.
   head_induction_on` (rtc), `Relation.Iterate.head_induction_on` (nsteps),
   or `rtc_ind_l`; a Rocq `rtc_ind_r` is the bare `induction`.
2. `nsteps R (S n)` IS `nsteps R (n + 1)`.
3. `rtc_subrel` takes the sub-relation hypothesis first and leaves `R1 R2
   x y` implicit (stdpp makes `R1 R2` section-explicit; every weak use is
   `eapply rtc_subrel`).
4. `sc` is a `def` (stdpp's is a notation-like `Definition` over `relation`).
5. NOT PORTED (no weak use): `rtcS`, `bsteps` and its lemmas, `nf`/`red`/
   `sn`/`wn`/confluence, `nsteps_add_inv`/`nsteps_inv_r`, `tc_nsteps`,
   `rtc_congruence`, and the setoid/`Proper` instances.  `tc_subrel`/
   `tc_mono` are LOCAL to `WeakRobustOrd.v`/`WeakRvwmoAcyc.v`, not stdpp, and
   port with those files.
-/
import Iris.Std.Relation

namespace MachCSL

/-- stdpp `rtc`: the reflexive-transitive closure (iris-lean's
`FromMathlib.Relation.ReflTransGen`). -/
abbrev rtc {A : Type _} (R : A → A → Prop) : A → A → Prop :=
  FromMathlib.Relation.ReflTransGen R

/-- stdpp `tc`: the transitive closure (core `Relation.TransGen`). -/
abbrev tc {A : Type _} (R : A → A → Prop) : A → A → Prop :=
  _root_.Relation.TransGen R

/-- stdpp `nsteps`: exactly `n` steps (iris-lean `Relation.Iterate`). -/
abbrev nsteps {A : Type _} (R : A → A → Prop) : Nat → A → A → Prop :=
  _root_.Relation.Iterate R

/-- stdpp `sc`: the symmetric closure. -/
def sc {A : Type _} (R : A → A → Prop) (x y : A) : Prop := R x y ∨ R y x

section
variable {A : Type _} {R : A → A → Prop}

/-! ## `rtc` -/

/-- stdpp constructor `rtc_refl`. -/
theorem rtc_refl (x : A) : rtc R x x := FromMathlib.Relation.ReflTransGen.refl

/-- stdpp constructor `rtc_l` (a first step, then the rest). -/
theorem rtc_l {x y z : A} (h1 : R x y) (h2 : rtc R y z) : rtc R x z :=
  FromMathlib.Relation.ReflTransGen.head h1 h2

theorem rtc_transitive {x y z : A} (h1 : rtc R x y) (h2 : rtc R y z) : rtc R x z :=
  FromMathlib.Relation.ReflTransGen.trans h1 h2

theorem rtc_once {x y : A} (h : R x y) : rtc R x y :=
  FromMathlib.Relation.ReflTransGen.single h

theorem rtc_r {x y z : A} (h1 : rtc R x y) (h2 : R y z) : rtc R x z :=
  FromMathlib.Relation.ReflTransGen.tail h1 h2

theorem rtc_inv {x z : A} (h : rtc R x z) : x = z ∨ ∃ y, R x y ∧ rtc R y z :=
  FromMathlib.Relation.ReflTransGen.cases_head h

theorem rtc_inv_r {x z : A} (h : rtc R x z) : x = z ∨ ∃ y, rtc R x y ∧ R y z := by
  cases h with
  | refl => exact .inl rfl
  | tail h1 h2 => exact .inr ⟨_, h1, h2⟩

/-- stdpp `rtc_ind_l`: induction from the FIRST step, toward a fixed end. -/
theorem rtc_ind_l (P : A → Prop) (z : A) (Prefl : P z)
    (Pstep : ∀ x y, R x y → rtc R y z → P y → P x) : ∀ x, rtc R x z → P x := by
  intro x h
  exact FromMathlib.Relation.ReflTransGen.head_induction_on (motive := fun x _ => P x) h Prefl
    (fun h' h ih => Pstep _ _ h' h ih)

/-- stdpp `rtc_ind_r`: induction from the LAST step, from a fixed start. -/
theorem rtc_ind_r (P : A → Prop) (x : A) (Prefl : P x)
    (Pstep : ∀ y z, rtc R x y → R y z → P y → P z) : ∀ z, rtc R x z → P z := by
  intro z h
  induction h with
  | refl => exact Prefl
  | tail h1 h2 ih => exact Pstep _ _ h1 h2 ih

/-! ## `tc` -/

/-- stdpp constructor `tc_once`. -/
theorem tc_once {x y : A} (h : R x y) : tc R x y := _root_.Relation.TransGen.single h

/-- stdpp constructor `tc_l`. -/
theorem tc_l {x y z : A} (h1 : R x y) (h2 : tc R y z) : tc R x z :=
  FromMathlib.Relation.TransGen.head h1 h2

theorem tc_transitive {x y z : A} (h1 : tc R x y) (h2 : tc R y z) : tc R x z :=
  _root_.Relation.TransGen.trans h1 h2

theorem tc_r {x y z : A} (h1 : tc R x y) (h2 : R y z) : tc R x z := _root_.Relation.TransGen.tail h1 h2

theorem tc_rtc {x y : A} (h : tc R x y) : rtc R x y :=
  FromMathlib.Relation.TransGen.to_reflTransGen h

theorem tc_rtc_r {x y z : A} (h1 : tc R x y) (h2 : rtc R y z) : tc R x z :=
  FromMathlib.Relation.TransGen.trans_left h1 h2

theorem tc_rtc_l {x y z : A} (h1 : rtc R x y) (h2 : tc R y z) : tc R x z := by
  revert h2
  induction h1 with
  | refl => exact id
  | tail _ hb ih => exact fun h2 => ih (tc_l hb h2)

theorem rtc_tc {x y : A} : rtc R x y ↔ x = y ∨ tc R x y := by
  constructor
  · intro h
    cases h with
    | refl => exact .inl rfl
    | tail h1 h2 => exact .inr (tc_rtc_l h1 (tc_once h2))
  · rintro (rfl | h)
    · exact rtc_refl _
    · exact tc_rtc h

instance : Trans (tc R) (tc R) (tc R) := ⟨tc_transitive⟩
instance : Trans (rtc R) (tc R) (tc R) := ⟨tc_rtc_l⟩
instance : Trans (tc R) (rtc R) (tc R) := ⟨tc_rtc_r⟩

/-! ## `nsteps` -/

/-- stdpp constructor `nsteps_O`. -/
theorem nsteps_O (x : A) : nsteps R 0 x x := _root_.Relation.Iterate.rfl x

/-- stdpp constructor `nsteps_l`. -/
theorem nsteps_l {n : Nat} {x y z : A} (h1 : R x y) (h2 : nsteps R n y z) :
    nsteps R (n + 1) x z :=
  _root_.Relation.Iterate.head h1 h2

theorem nsteps_once {x y : A} (h : R x y) : nsteps R 1 x y :=
  _root_.Relation.Iterate.once h

theorem nsteps_r {n : Nat} {x y z : A} (h1 : nsteps R n x y) (h2 : R y z) :
    nsteps R (n + 1) x z :=
  _root_.Relation.Iterate.tail y h1 h2

theorem nsteps_once_inv {x y : A} (h : nsteps R 1 x y) : R x y := by
  cases h with
  | tail _ h1 h2 =>
    cases h1 with
    | rfl => exact h2

theorem nsteps_trans {n m : Nat} {x y z : A} (h1 : nsteps R n x y) (h2 : nsteps R m y z) :
    nsteps R (n + m) x z := by
  revert h1
  induction h2 with
  | rfl => exact id
  | tail w _ h ih => exact fun h1 => _root_.Relation.Iterate.tail w (ih h1) h

theorem rtc_nsteps {x y : A} : rtc R x y ↔ ∃ n, nsteps R n x y :=
  _root_.Relation.ReflTrans_iff_exists_iterate

theorem rtc_nsteps_1 {x y : A} (h : rtc R x y) : ∃ n, nsteps R n x y := rtc_nsteps.1 h

theorem rtc_nsteps_2 {n : Nat} {x y : A} (h : nsteps R n x y) : rtc R x y :=
  rtc_nsteps.2 ⟨n, h⟩

/-! ## `sc` -/

theorem sc_lr {x y : A} (h : R x y) : sc R x y := Or.inl h

theorem sc_rl {x y : A} (h : R y x) : sc R x y := Or.inr h

theorem sc_symm {x y : A} (h : sc R x y) : sc R y x := Or.symm h

end

/-! ## Sub-relations -/

/-- stdpp `rtc_subrel` (deviation 3: the inclusion first, `R1 R2` implicit). -/
theorem rtc_subrel {A : Type _} {R1 R2 : A → A → Prop} {x y : A}
    (H : ∀ x y, R1 x y → R2 x y) (h : rtc R1 x y) : rtc R2 x y := by
  induction h with
  | refl => exact rtc_refl _
  | tail _ h2 ih => exact rtc_r ih (H _ _ h2)

end MachCSL
