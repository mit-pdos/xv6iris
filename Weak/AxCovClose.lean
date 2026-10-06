/-
Weak: **CLOSING THE C6 GAP** (AxSL tier, LB/AxSL rev 7, C6 coverage): how far `AxCovMono`'s
combinator can go, tied to WRITE IDENTITY, and why `AxCov.class_epoch_gmo_mono` itself cannot be
discharged this way for ANY `γ`.

Rocq: `iris/AxCovClose.v` @ xxvzwolszwmp.

Rocq header (in substance).  WHAT THIS FILE ADDS (§1): `classEpochGmoMonoOfWrites` is
`AxCovMono.histChainMono`'s `(i, j)`-indexed comparability RE-INDEXED by the two writes' own
identities: given `xs[i]? = some (w, v)`, `xs[j]? = some (w', v')` and `gmoLt GD.gdG w w'` (not a
bare `i ≤ j`), it derives `i < j` internally from ONE further pure premise, `hxsOrder` (`xs`'s
tags are gmo-sorted), via nat trichotomy plus `gmoLt`'s antisymmetry (`indexOrderOfGmoLt`).

THE SHARPENED FINDING (Rocq header, kept): `AxCov.class_epoch_gmo_mono γ GD a` is a NATIVE
Rocq Pi-type (no `: iProp Σ` ascription), so a value of it is a closed term built in the EMPTY
ambient context: no leftover `hist_auth` fraction, and no invariant (its wand ends in a bare,
unmoded `⌜_⌝`, so no mask-changing update can open one).  From two externally supplied
`hist_snap`s alone, mono-list comparability gives a prefix in SOME direction, and nothing ties
the direction to `gmo_lt` — for the real shared `γ` and for a fresh one alike; the replay's
canonical snapshots carry that information only because they are OUTPUTS of the same `|==>`.
CONCLUSION: the gap is the SHAPE of the obligation, not "which γ".  The open route is to prove
`deferred_read_cov`/`deferred_snap_avail` directly inside the concrete instance's per-event
adequacy induction (a twin of `AxAdequacyL.adequacy_ord_aux_L` specialised to `AxProt`'s
`Φ_own`), with a concrete `axpol` routing each write's `Φ_own` token via its gmo-previous write;
both are separate increments, left to follow-up.

**Deviations from Rocq.**

1. NAMES: camelCase (map below).  The section's `axlogG Σ hent` is `[AxlogG GF Hent]`.
2. VOCABULARY (`AxGhost` deviation 2): `l !! i` ↦ `l[i]?`; `xs.*1` ↦ `xs.map Prod.fst`;
   `take (S i) xs` ↦ `xs.take (i + 1)`; `prefix_of` ↦ `<+:`; `gd_g GD` ↦ `GD.gdG`; `bv 8` ↦
   `BitVec 8`; `Z` ↦ `Int`.
3. STATEMENT SHAPES (`AxGhost` deviation 4): `P -∗ |==> Q` is `P ⊢ |==> Q`; pure premises stay
   `→` (as named binders).

**Rocq → Lean name map.**  `index_order_of_gmo_lt`→`indexOrderOfGmoLt`,
`class_epoch_gmo_mono_of_writes`→`classEpochGmoMonoOfWrites`.  (Neither name is in
`notes/weak-port-dupnames.json`.)

**Not ported:** the §2 `Print Assumptions` audit (the lint bans `sorry`/`axiom`).
-/
import Weak.AxCovMono

namespace Weak

open Iris Iris.BI Iris.Std MachCSL MachCSL.Stdpp

/-! ## 1. `classEpochGmoMonoOfWrites` — `histChainMono`, indexed by write identity -/

/-- PURE HELPER: two positions into a `gmo`-sorted (by `horder`) list are ordered by `gmoLt`
exactly as their positions are — the converse of `horder` itself, from trichotomy plus `gmoLt`'s
antisymmetry (`gmoLtIrrefl` + `gmoLtTrans`). -/
theorem indexOrderOfGmoLt (GD : Gdexec) (ws : List Geid) (i j : Nat) (w w' : Geid)
    (hi : ws[i]? = some w) (hj : ws[j]? = some w')
    (hgmo : gmoLt GD.gdG w w')
    (horder : ∀ (i0 j0 : Nat) (w0 w0' : Geid), ws[i0]? = some w0 → ws[j0]? = some w0' →
                i0 < j0 → gmoLt GD.gdG w0 w0') :
    i < j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact hlt
  · exfalso
    subst heq
    rw [hi] at hj
    cases hj
    exact gmoLtIrrefl GD.gdG w hgmo
  · exfalso
    have hgmo' := horder j i w' w hj hi hgt
    exact gmoLtIrrefl GD.gdG w (gmoLtTrans GD.gdG w w' w hgmo hgmo')

section chain2

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- `AxCovMono.histChainMono`, with its `i ≤ j` hypothesis replaced by the two writes' OWN
`gmoLt` fact plus a witness of WHICH write each replayed position deposits (`hi`/`hj`) —
exactly `AxCov.class_epoch_gmo_mono`'s premise shape, for the replay's self-produced snapshots.
`hxsOrder` (`xs`'s tags sorted by `gmoLt`) turns "which write" into "which index" via
`indexOrderOfGmoLt`; everything else is `histChainMono`, reused unchanged. -/
theorem classEpochGmoMonoOfWrites (γ : GName) (a : Int)
    (H0 xs : List Hent) (i j : Nat) (w w' : Geid) (v v' : BitVec 8) (GD : Gdexec)
    (hi : xs[i]? = some (w, v)) (hj : xs[j]? = some (w', v'))
    (hgmo : gmoLt GD.gdG w w')
    (hjlt : j < xs.length)
    (hxsOrder : ∀ (i0 j0 : Nat) (w0 w0' : Geid), (xs.map Prod.fst)[i0]? = some w0 →
                  (xs.map Prod.fst)[j0]? = some w0' → i0 < j0 → gmoLt GD.gdG w0 w0') :
    histAuth (GF := GF) γ a 1 H0 ⊢ |==>
      (histAuth γ a 1 (H0 ++ xs) ∗
        histSnap γ a (H0 ++ xs.take (i + 1)) ∗
        histSnap γ a (H0 ++ xs.take (j + 1)) ∗
        ⌜(H0 ++ xs.take (i + 1)) <+: (H0 ++ xs.take (j + 1))⌝) := by
  have hi' : (xs.map Prod.fst)[i]? = some w := by simp [List.getElem?_map, hi]
  have hj' : (xs.map Prod.fst)[j]? = some w' := by simp [List.getElem?_map, hj]
  have hij := indexOrderOfGmoLt GD (xs.map Prod.fst) i j w w' hi' hj' hgmo hxsOrder
  exact histChainMono γ a H0 xs i j (Nat.le_of_lt hij) hjlt

end chain2

end Weak
