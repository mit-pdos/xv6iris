/-
MachCSL: the `Qp` (positive rationals) lemmas the weak-memory port uses, on
top of iris-lean's thin `Iris.Algebra.Frac` API (Rocq stdpp `numbers.v`,
section `Qp`; gap G6 of `notes/weak-port-iris-gaps.md`).

iris-lean's `Qp` is `{q : Rat // 0 < q}` with `+`, `half`, `quarter`,
`div`, `≤`/`<` through `.val` (`Qp.le_iff`/`Qp.lt_iff` are `Iff.rfl`), and
`half_add_half`/`add_left_comm`/`lt_iff_exists_add`.  It has no
associativity, commutativity, order or subtraction lemma set; this file is
that set, under the stdpp names, in `Iris.Qp` beside iris-lean's own.

What the weak files cite: `1%Qp` (190 literals, iris-lean's `1`),
`Qp.half_half` (20, every one a `rewrite -Qp.half_half` splitting a full
fraction), `Qp.not_add_le_l` (2, refuting `1 + 1 ≤ 1`), and `q1 + q2 ≤ 1`
side conditions of the `*_agree` lemmas (stated as `≤` on `Qp`, so
`Qp.le_iff`).  The rest of the stdpp `Qp` order/sum lemmas are here because
the SC port already needed several of them as local copies
(`Xv6/FileFrac.qp_add_assoc`, `Xv6/FilePay.qp_half_add`,
`Xv6/IcacheInvRef.qpSub`/`qpSub_some`/`qp_one_add_not_le`) and the weak
port's fraction algebra (`WeakLog*`, `WeakHist*`) is the same shape.

Name mapping: stdpp `Qp.foo` is `Iris.Qp.foo` (stdpp's names are already
Lean's theorem spelling).  stdpp's `Assoc`/`Comm` instances are
`Qp.add_assoc`/`Qp.add_comm`; `Qp.div_add_distr` at `2` is `Qp.half_add`.

Deviations from Rocq.
1. `p / 2` IS `p.half`, `1 / 4` IS `Qp.quarter` (iris-lean has no
   numeral `OfNat Qp n` beyond `1`, and adding one would give `1` two
   instances).  So stdpp `half_half : 1/2 + 1/2 = 1` is
   `(1 : Qp).half + (1 : Qp).half = 1` and `div_2 p` is `half_add_half p`.
2. stdpp's `p - q : option Qp` is `Qp.sub p q : Option Qp` (a function,
   no `-` notation: an `Option`-valued `HSub` would surprise every reader).
3. NOT PORTED (no weak use): `Qp.mul`/`inv`/`max`/`min` lemma families,
   `Qp.le_dec`/`lt_dec` (`decide` on `Qp` order is not used; the weak files'
   fraction facts are all closed by these lemmas), `pos_to_Qp`.  The SC
   local copies listed above are left where they are (moving them touches
   built Xv6 files for no proof change); new code uses these names.
-/
import Iris.Algebra.Frac

namespace Iris

/-! ## Equalities -/

theorem Qp.add_assoc (x y z : Qp) : x + y + z = x + (y + z) := Subtype.ext (Rat.add_assoc ..)

theorem Qp.add_comm (x y : Qp) : x + y = y + x := Subtype.ext (Rat.add_comm ..)

/-- stdpp `Qp.half_half : 1/2 + 1/2 = 1` (deviation 1). -/
theorem Qp.half_half : (1 : Qp).half + (1 : Qp).half = 1 := Qp.half_add_half 1

/-- stdpp `Qp.div_2 p : p/2 + p/2 = p` (deviation 1). -/
theorem Qp.div_2 (p : Qp) : p.half + p.half = p := Qp.half_add_half p

/-- stdpp `Qp.div_add_distr` at `2`. -/
theorem Qp.half_add (p q : Qp) : (p + q).half = p.half + q.half :=
  Subtype.ext (by show (p.val + q.val) / 2 = p.val / 2 + q.val / 2; grind)

/-- `1/4 + 1/4 = 1/2` (stdpp: `compute_done` on literals). -/
theorem Qp.quarter_add_quarter : Qp.quarter + Qp.quarter = (1 : Qp).half :=
  Subtype.ext (by show (1 / 4 : Rat) + 1 / 4 = 1 / 2; grind)

/-- `(1/2)/2 = 1/4`. -/
theorem Qp.half_half_eq_quarter : (1 : Qp).half.half = Qp.quarter :=
  Subtype.ext (by show ((1 : Rat) / 2) / 2 = 1 / 4; grind)

theorem Qp.add_id_free (q p : Qp) : q + p ≠ q := by
  intro h
  have h' := congrArg Subtype.val h
  rw [Qp.val_add] at h'
  have := p.2
  grind

/-! ## Order -/

theorem Qp.le_refl (p : Qp) : p ≤ p := by
  rw [Qp.le_iff]; grind

theorem Qp.le_trans {p q r : Qp} (h1 : p ≤ q) (h2 : q ≤ r) : p ≤ r := by
  rw [Qp.le_iff] at *; grind

theorem Qp.le_antisymm {p q : Qp} (h1 : p ≤ q) (h2 : q ≤ p) : p = q := by
  rw [Qp.le_iff] at *; apply Subtype.ext; grind

theorem Qp.lt_irrefl (p : Qp) : ¬ p < p := by
  rw [Qp.lt_iff]; grind

theorem Qp.lt_le_incl {p q : Qp} (h : p < q) : p ≤ q := by
  rw [Qp.lt_iff] at h; rw [Qp.le_iff]; grind

theorem Qp.le_lt_trans {p q r : Qp} (h1 : p ≤ q) (h2 : q < r) : p < r := by
  rw [Qp.le_iff] at h1; rw [Qp.lt_iff] at *; grind

theorem Qp.lt_le_trans {p q r : Qp} (h1 : p < q) (h2 : q ≤ r) : p < r := by
  rw [Qp.le_iff] at h2; rw [Qp.lt_iff] at *; grind

theorem Qp.lt_add_l (p q : Qp) : p < p + q := by
  have := q.2; rw [Qp.lt_iff, Qp.val_add]; grind

theorem Qp.lt_add_r (p q : Qp) : q < p + q := by
  have := p.2; rw [Qp.lt_iff, Qp.val_add]; grind

theorem Qp.le_add_l (p q : Qp) : p ≤ p + q := Qp.lt_le_incl (Qp.lt_add_l p q)

theorem Qp.le_add_r (p q : Qp) : q ≤ p + q := Qp.lt_le_incl (Qp.lt_add_r p q)

/-- stdpp `Qp.not_add_le_l` (the weak files: `Qp.not_add_le_l 1 1` refutes
`1 + 1 ≤ 1`). -/
theorem Qp.not_add_le_l (p q : Qp) : ¬ (p + q ≤ p) := by
  have := q.2; rw [Qp.le_iff, Qp.val_add]; grind

theorem Qp.not_add_le_r (p q : Qp) : ¬ (p + q ≤ q) := by
  have := p.2; rw [Qp.le_iff, Qp.val_add]; grind

theorem Qp.add_le_mono_l (p q r : Qp) : p ≤ q ↔ r + p ≤ r + q := by
  rw [Qp.le_iff, Qp.le_iff, Qp.val_add, Qp.val_add]; grind

theorem Qp.add_le_mono_r (p q r : Qp) : p ≤ q ↔ p + r ≤ q + r := by
  rw [Qp.le_iff, Qp.le_iff, Qp.val_add, Qp.val_add]; grind

theorem Qp.add_le_mono {q p n m : Qp} (h1 : q ≤ n) (h2 : p ≤ m) : q + p ≤ n + m := by
  rw [Qp.le_iff] at *; rw [Qp.val_add, Qp.val_add]; grind

theorem Qp.add_lt_mono_l (p q r : Qp) : p < q ↔ r + p < r + q := by
  rw [Qp.lt_iff, Qp.lt_iff, Qp.val_add, Qp.val_add]; grind

theorem Qp.add_lt_mono_r (p q r : Qp) : p < q ↔ p + r < q + r := by
  rw [Qp.lt_iff, Qp.lt_iff, Qp.val_add, Qp.val_add]; grind

theorem Qp.add_lt_mono {q p n m : Qp} (h1 : q < n) (h2 : p < m) : q + p < n + m := by
  rw [Qp.lt_iff] at *; rw [Qp.val_add, Qp.val_add]; grind

theorem Qp.half_lt (p : Qp) : p.half < p := by
  have := p.2; rw [Qp.lt_iff, Qp.val_half]; grind

/-- stdpp `Qp.lt_sum` (iris-lean's `lt_iff_exists_add`, equation flipped). -/
theorem Qp.lt_sum (p q : Qp) : p < q ↔ ∃ r, q = p + r :=
  Qp.lt_iff_exists_add.trans ⟨fun ⟨c, h⟩ => ⟨c, h.symm⟩, fun ⟨c, h⟩ => ⟨c, h.symm⟩⟩

/-! ## Subtraction (deviation 2) -/

/-- stdpp `p - q : option Qp`: the difference when it is positive. -/
def Qp.sub (p q : Qp) : Option Qp := Qp.ofRat? (p.val - q.val)

theorem Qp.sub_Some {p q r : Qp} : Qp.sub p q = some r ↔ p = q + r := by
  unfold Qp.sub Qp.ofRat?
  constructor
  · intro h
    split at h
    · cases h
      apply Subtype.ext
      show p.val = q.val + (p.val - q.val)
      grind
    · cases h
  · intro h
    subst h
    have hr := r.2
    have hpos : 0 < (q + r).val - q.val := by
      show 0 < (q.val + r.val) - q.val
      grind
    rw [dif_pos hpos]
    congr 1
    apply Subtype.ext
    show (q.val + r.val) - q.val = r.val
    grind

theorem Qp.sub_None {p q : Qp} : Qp.sub p q = none ↔ p ≤ q := by
  unfold Qp.sub Qp.ofRat?
  rw [Qp.le_iff]
  constructor
  · intro h
    split at h
    · cases h
    · grind
  · intro h
    rw [dif_neg (by grind)]

end Iris
