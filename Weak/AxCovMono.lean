/-
Weak: **A PROVED GHOST COMBINATOR toward `AxCov.class_epoch_gmo_mono`** (AxSL tier, LB/AxSL
rev 7, C6 coverage).

Rocq: `iris/AxCovMono.v` @ xxvzwolszwmp.

Rocq header (in substance).  `AxCov.v`'s single remaining premise `class_epoch_gmo_mono` ("two
different writes to the same owned byte, each with its own `Φ_own`/`hist_snap` deposit, are
prefix-ordered the way their writes are gmo-ordered") needs a per-event induction over `s_proc`
invoking `AxProt.prot_inv_write_step` in real commit order (`AxSched.Inv.inv_ord_fresh`: writes
are never deferred, so commit order already equals gmo order for writes); that induction does
not exist yet.

WHAT THIS FILE ADDS: `histChainSnoc`/`histChainMono` — the exact per-step ghost invariant that
induction will carry, in full generality (an arbitrary replay list `xs`, no graph/scheduler
dependency).  Replaying `xs` onto a byte's ghost log one `histAppend` at a time, in list order,
produces for every index `i` a persistent `histSnap γ a (H0 ++ xs.take (i+1))`
(`histChainSnoc`); that these snapshots NEST in list order (`histChainMono`) is a pure fact
about `take`.  `class_epoch_gmo_mono` ITSELF is NOT discharged here.

THE FINDING (Rocq header, kept): `class_epoch_gmo_mono` quantifies over arbitrary
externally-supplied snapshots; relating such an `H_w` back to its position in the real commit
order needs the per-event induction: (a) mono-list algebra alone does not tie an appended entry
to `gmo_lt` (a caller could append in gmo-reverse order); (b) a fresh, disconnected replay proves
the fact only for a private `γ`; (c) wrapping `hist_auth` in an invariant conflicts with the
write rule's exclusive `tok_tie` of the auth fraction, and a separate commit counter just
repackages `inv_ord_fresh` along the same missing walk.  The combinator is additive preparation;
`AxCov.v`'s reduction is unchanged.

**Deviations from Rocq.**

1. NAMES: camelCase (map below).  The section's `axlogG Σ hent` is `[AxlogG GF Hent]`.
2. VOCABULARY (`AxGhost` deviation 2): `take (S i) xs` ↦ `xs.take (i + 1)`; `prefix_of` ↦ `<+:`;
   `[∗ list] i ↦ _ ∈ xs, …` ↦ iris-lean's `[∗list] i ↦ _x ∈ xs, …`.
3. STATEMENT SHAPES (`AxGhost` deviation 4): `P -∗ |==> Q` is `P ⊢ |==> Q`; the leading `∀ H0`
   of `hist_chain_snoc` stays a Lean `∀` outside the entailment; pure premises stay `→`.

**Rocq → Lean name map.**  `take_prefix_take`→`takePrefixTake`, `app_cons_assoc`→
`appConsAssoc`, `hist_chain_snoc`→`histChainSnoc`, `hist_chain_mono`→`histChainMono`.  (None of
these names is in `notes/weak-port-dupnames.json`.)

**Not ported:** the `Print Assumptions` audit (the lint bans `sorry`/`axiom`).
-/
import Weak.AxGhost

namespace Weak

open Iris Iris.BI Iris.Std MachCSL MachCSL.Stdpp

/-- PURE HELPER: `take` is monotone in its bound, under prefix. -/
theorem takePrefixTake {A : Type} (l : List A) (n m : Nat) (h : n ≤ m) :
    l.take n <+: l.take m := by
  have hp := List.take_prefix n (l.take m)
  rwa [List.take_take, Nat.min_eq_left h] at hp

/-- PURE HELPER: re-associate a `cons` in the middle of an `++`. -/
theorem appConsAssoc {A : Type} (l1 : List A) (x : A) (l2 : List A) :
    l1 ++ x :: l2 = (l1 ++ [x]) ++ l2 := by
  simp

section chain

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- THE GHOST STEP LEMMA: replaying `xs` onto byte `a`'s history from base `H0`, one entry at a
time in list order, ends with the full history `H0 ++ xs` plus, for every index `i` into `xs`,
a persistent snapshot of the history up to and including `xs`'s `i`-th entry. -/
theorem histChainSnoc (γ : GName) (a : Int) (xs : List Hent) :
    ∀ H0, histAuth (GF := GF) γ a 1 H0 ⊢ |==>
      (histAuth γ a 1 (H0 ++ xs) ∗
        [∗list] i ↦ _x ∈ xs, histSnap γ a (H0 ++ xs.take (i + 1))) := by
  induction xs with
  | nil =>
    intro H0
    rw [List.append_nil]
    iintro H
    imodintro
    isplitl [H]
    · iexact H
    · iapply BigSepL.bigSepL_nil_intro (P := (emp : IProp GF))
      iempintro
  | cons x xs ih =>
    intro H0
    iintro H
    imod histAppend γ a H0 x $$ H with H
    ihave #Hs0 := histSnapGet γ a 1 (H0 ++ [x]) $$ H
    imod ih (H0 ++ [x]) $$ H with ⟨H, Hrest⟩
    imodintro
    rw [appConsAssoc H0 x xs]
    isplitl [H]
    · iexact H
    · iapply BigSepL.bigSepL_cons.2
      isplitr [Hrest]
      · simp only [Nat.zero_add, List.take_succ_cons, List.take_zero]
        iexact Hs0
      · iapply BigSepL.bigSepL_mono _ $$ Hrest
        iintro %k %y %_ Hk
        rw [List.take_succ_cons, appConsAssoc H0 x (xs.take (k + 1))]
        iexact Hk

/-- THE NESTING COROLLARY: any two positions `i ≤ j` into the replayed `xs` carry snapshots
ordered the same way — purely from `take`'s monotonicity. -/
theorem histChainMono (γ : GName) (a : Int) (H0 : List Hent) (xs : List Hent) (i j : Nat)
    (hij : i ≤ j) (hj : j < xs.length) :
    histAuth (GF := GF) γ a 1 H0 ⊢ |==>
      (histAuth γ a 1 (H0 ++ xs) ∗
        histSnap γ a (H0 ++ xs.take (i + 1)) ∗
        histSnap γ a (H0 ++ xs.take (j + 1)) ∗
        ⌜(H0 ++ xs.take (i + 1)) <+: (H0 ++ xs.take (j + 1))⌝) := by
  have hxi : xs[i]? = some xs[i] := List.getElem?_eq_getElem (by omega)
  have hxj : xs[j]? = some xs[j] := List.getElem?_eq_getElem hj
  iintro H
  imod histChainSnoc γ a xs H0 $$ H with ⟨H, #Hall⟩
  ihave #Hi := BigSepL.bigSepL_lookup
    (Φ := fun k _ => histSnap (GF := GF) γ a (H0 ++ xs.take (k + 1))) hxi $$ Hall
  ihave #Hj := BigSepL.bigSepL_lookup
    (Φ := fun k _ => histSnap (GF := GF) γ a (H0 ++ xs.take (k + 1))) hxj $$ Hall
  imodintro
  isplitl [H]
  · iexact H
  isplitr
  · iexact Hi
  isplitr
  · iexact Hj
  · ipureintro
    exact List.prefix_append_right_inj H0 |>.mpr (takePrefixTake xs (i + 1) (j + 1) (by omega))

end chain

end Weak
