/-
Weak: **the arithmetic sub-kills** (route B, stage B2e-1).

Rocq: `iris/WeakRvwmoKill.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§4c, first bullet).

THE POINT.  `WeakRvwmoNorm.normalize` is parameterized by three kill
obligations `killK1`/`killK2`/`killK3`.  Each is a statement about a VIOLATION
`gviol G e w` (`e` po-before the write `w`, but `w` gmo-before `e`) plus a
witness-kind-specific blocker.  This file peels off everything about such a
configuration that is PURE ORDER THEORY, so B2e-3's export argument only has to
face the genuinely RACY residual.

THE ONE IDEA: every named ppo⁻ arm and every dep edge running `e → w` gives
`gmoLt G e w` (by `gppoGmo` / `gdepsGmo`), contradicting the violation's own
`gmoLt G w e`.  §1 states the engine once; §2's five `gviolNo*` lemmas are the
four ppo⁻ arms plus the dep fragment; §3 is K2's extra (the stale reader is
CROSS-HART); §4 gives for each kill a RACY form (the kill verbatim plus the
exclusions as extra hypotheses) and a REDUCTION `killK1OfRacy : killK1Racy GD →
killK1 GD` (and K2/K3), the converse (statement fidelity, machine-checked), and
`lbgdKillK1RacyFalse` (the racy forms are not vacuous).

A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  No name of this
   file is in `notes/weak-port-dupnames.json`; the `WeakRvwmoGraph` duplicates
   used are referred to qualified (`WeakRvwmoGraph.gpo`,
   `WeakRvwmoGraph.glblIsWGmem`).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`Z` ↦ `Int`, `bv 8` ↦
   `BitVec 8`).
3. `gviolK2CrossHart`'s three-way split on `z.2` vs `e.2` is
   `Nat.lt_trichotomy` (Rocq: two `decide`s).
4. D35-fix ([OWN.54]; `WeakRvwmoGraph` deviation 7): rule 7's exclusion is `¬ grcsc`
   (riscv.cat's RCsc; Rocq: `¬ grel_acq`), so `gviol_no_relacq` is `gviolNoRcsc` and the
   racy forms `killK1Racy`/`killK2Racy`/`killK3Racy` carry `¬ grcsc GD'.gdG e w`.

**Name map** (Rocq → Lean): `gviol_no_gppo` ↦ `gviolNoGppo`; `gviol_no_aq` ↦
`gviolNoAq`; `gviol_no_fence` ↦ `gviolNoFence`; `gviol_no_relacq` ↦
`gviolNoRcsc` (D35-fix, `¬ grcsc`); `gviol_no_poloc` ↦ `gviolNoPoloc`; `gviol_no_dep` ↦
`gviolNoDep`; `gviol_K2_cross_hart` ↦ `gviolK2CrossHart`; `kill_K1_racy`/
`_K2_racy`/`_K3_racy` ↦ `killK1Racy`/`killK2Racy`/`killK3Racy`;
`kill_K1_of_racy`/`_K2_`/`_K3_` ↦ `killK1OfRacy`/`killK2OfRacy`/`killK3OfRacy`;
`kill_K1_to_racy`/`_K2_`/`_K3_` ↦ `killK1ToRacy`/`killK2ToRacy`/`killK3ToRacy`;
`lbgd_kill_K1_racy_false` ↦ `lbgdKillK1RacyFalse`.

**Not ported:** nothing.
-/
import Weak.WeakMem
import Weak.WeakAxiomatic
import Weak.WeakAxiomatic2
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg
import Weak.WeakRvwmoNorm

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. THE ENGINE: a violation admits NO ppo⁻ edge in its own direction -/

theorem gviolNoGppo (G : Gexec) (e w : Geid) :
    gppoGmo G → gviol G e w → ¬ gppo G e w := by
  rintro hppo ⟨_, _, _, hmo⟩ hp
  exact gmoLtIrrefl G e (gmoLtTrans G e w e (hppo e w hp) hmo)

/-! # 2. THE `gviolNo*` FAMILY — witness-kind-INDEPENDENT -/

/-- RULE 5 — an ACQUIRING READ is gppo-before every po-later memory event. -/
theorem gviolNoAq (G : Gexec) (e w : Geid) :
    rvwmoMinusConsistent G → gviol G e w →
    ¬ (glblIs G e lbIsR ∧ glblIs G e lbAq) := by
  rintro ⟨_, hppo, _, _⟩ hv ⟨hr, haq⟩
  apply gviolNoGppo G e w hppo hv
  obtain ⟨hpo, _, hw, _⟩ := hv
  exact Or.inr (Or.inr (Or.inl ⟨hpo, hr, haq, WeakRvwmoGraph.glblIsWGmem G w hw⟩))

/-- RULE 4 — a covering fence between them. -/
theorem gviolNoFence (G : Gexec) (e w : Geid) :
    rvwmoMinusConsistent G → gviol G e w → ¬ gfenceCovers G e w := by
  rintro ⟨_, hppo, _, _⟩ hv hf
  exact gviolNoGppo G e w hppo hv (Or.inr (Or.inl hf))

/-- RULE 7 — the RCsc pair (D35-fix [OWN.54]: riscv.cat's RCsc, `grcsc`; Rocq: `grelAcq`). -/
theorem gviolNoRcsc (G : Gexec) (e w : Geid) :
    rvwmoMinusConsistent G → gviol G e w → ¬ grcsc G e w := by
  rintro ⟨_, hppo, _, _⟩ hv hra
  exact gviolNoGppo G e w hppo hv (Or.inr (Or.inr (Or.inr hra)))

/-- RULES 1–3 — the witness and the violating write are BYTE-DISJOINT. -/
theorem gviolNoPoloc (G : Gexec) (e w : Geid) (a : Int) :
    rvwmoMinusConsistent G → gviol G e w →
    gaccesses G e a → gaccesses G w a → False := by
  rintro ⟨_, hppo, _, _⟩ hv hae haw
  exact gviolNoGppo G e w hppo hv (Or.inl ⟨hv.1, a, hae, haw⟩)

/-- THE DEP FRAGMENT — a dep edge into the violating write is refuted the same
way. -/
theorem gviolNoDep (GD : Gdexec) (e w : Geid) :
    rvwmoMinusDepsConsistent GD → gviol GD.gdG e w →
    (e, w) ∉ GD.gdDeps := by
  rintro ⟨_, _, hdgmo⟩ ⟨_, _, _, hmo⟩ hin
  exact gmoLtIrrefl _ e (gmoLtTrans _ e w e (hdgmo (e, w) hin) hmo)

/-! # 3. K2's EXTRA: THE STALE READER IS CROSS-HART

`z.2 < e.2`: an earlier witness of `w` (`poMinNoBlocker`); `z.2 = e.2`: `z = e`
and `gmoLt G z e` is irreflexive; `z.2 > e.2`: `gpoloc G e z` on the byte `a`,
so `gmoLt G e z`, contradicting `gmoLt G z e`. -/

theorem gviolK2CrossHart (G : Gexec) (w e z : Geid) (a : Int) (t : Nat)
    (v v' : BitVec 8) :
    rvwmoMinusConsistent G →
    gviol G e w →
    (∀ e', gviol G e' w → ¬ e'.2 < e.2) →
    gmoLt G w z → gmoLt G z e →
    greadsByte G z a t v →
    gwritesByte G e a v' →
    z.1 ≠ e.1 := by
  intro hcons hv hpmin hmowz hmoze hrd hwb hag
  obtain ⟨_, hppo, _, _⟩ := id hcons
  obtain ⟨_, hmeme, _, _⟩ := id hv
  have hzs : ∃ l, gxLbl G z = some l ∧ lbIsR l = true := by
    obtain ⟨l, base, ts, vs, j, hl, hrd', _⟩ := hrd
    exact ⟨l, hl, lbRdIsR l _ hrd'⟩
  have hzmem : gmem G z := by
    obtain ⟨l, hl, hr⟩ := hzs
    exact ⟨l, hl, by simp [lbIsMem, hr]⟩
  rcases Nat.lt_trichotomy z.2 e.2 with hlt | heq2 | hgt
  · exact poMinNoBlocker G w e z hv hpmin hzmem hmowz hag hlt
  · have : z = e := Prod.ext hag heq2
    subst this
    exact gmoLtIrrefl G z hmoze
  · -- `z` is po-AFTER `e` on the same hart, and reads a byte `e` writes
    have hpl : gppo G e z := by
      refine Or.inl ⟨⟨hag.symm, hgt, ?_, ?_⟩, a, Or.inl ⟨v', hwb⟩, Or.inr ⟨t, v, hrd⟩⟩
      · obtain ⟨l, hl, _⟩ := hmeme
        simp [hl]
      · obtain ⟨l, hl, _⟩ := hzs
        simp [hl]
    exact gmoLtIrrefl G e (gmoLtTrans G e z e (hppo e z hpl) hmoze)

/-! # 4. THE RACY RESIDUALS, AND THE REDUCTIONS -/

/-! ## 4.1 K1 — the witness is a READ blocked at its cross-hart rf-source -/

def killK1Racy (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e : Geid) (a : Int) (t : Nat) (v : BitVec 8) (w0 : Geid),
    gviol GD'.gdG e w →
    (∀ e' w', gviol GD'.gdG e' w' → ¬ gmoLt GD'.gdG w' w) →
    (∀ e', gviol GD'.gdG e' w → ¬ e'.2 < e.2) →
    gisW GD'.gdG e = false →
    greadsByte GD'.gdG e a t v →
    gwriteAt GD'.gdG t = some w0 →
    w0.1 ≠ e.1 →
    gmoLt GD'.gdG w w0 → gmoLt GD'.gdG w0 e →
    -- ---- the arithmetic exclusions (§2): no ppo⁻ arm, no dep edge ----
    ¬ (glblIs GD'.gdG e lbIsR ∧ glblIs GD'.gdG e lbAq) →
    ¬ gfenceCovers GD'.gdG e w →
    ¬ grcsc GD'.gdG e w →
    (∀ b, gaccesses GD'.gdG e b → gaccesses GD'.gdG w b → False) →
    (e, w) ∉ GD'.gdDeps →
    False

theorem killK1OfRacy (GD : Gdexec) : killK1Racy GD → killK1 GD := by
  intro hR GD' heq w e a t v w0 hv hmin hpmin hew hrd hsrc hag hmo1 hmo2
  obtain ⟨_, _, _, _, hcons⟩ := id heq
  have hc := hcons.1
  exact hR GD' heq w e a t v w0 hv hmin hpmin hew hrd hsrc hag hmo1 hmo2
    (gviolNoAq _ e w hc hv) (gviolNoFence _ e w hc hv) (gviolNoRcsc _ e w hc hv)
    (fun b => gviolNoPoloc _ e w b hc hv) (gviolNoDep GD' e w hcons hv)

/-! ## 4.2 K2 — the witness is a WRITE with an interval STALE reader -/

def killK2Racy (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e z : Geid) (a : Int) (t : Nat) (v v' : BitVec 8),
    gviol GD'.gdG e w →
    (∀ e' w', gviol GD'.gdG e' w' → ¬ gmoLt GD'.gdG w' w) →
    (∀ e', gviol GD'.gdG e' w → ¬ e'.2 < e.2) →
    gisW GD'.gdG e = true →
    gmoLt GD'.gdG w z → gmoLt GD'.gdG z e →
    greadsByte GD'.gdG z a t v →
    gwritesByte GD'.gdG e a v' →
    t < gwix GD'.gdG e →
    -- ---- the arithmetic exclusions (§2), plus §3's cross-hart-ness ----
    z.1 ≠ e.1 →
    ¬ (glblIs GD'.gdG e lbIsR ∧ glblIs GD'.gdG e lbAq) →
    ¬ gfenceCovers GD'.gdG e w →
    ¬ grcsc GD'.gdG e w →
    (∀ b, gaccesses GD'.gdG e b → gaccesses GD'.gdG w b → False) →
    (e, w) ∉ GD'.gdDeps →
    False

theorem killK2OfRacy (GD : Gdexec) : killK2Racy GD → killK2 GD := by
  intro hR GD' heq w e z a t v v' hv hmin hpmin hew hmo1 hmo2 hrd hwb hlt
  obtain ⟨_, _, _, _, hcons⟩ := id heq
  have hc := hcons.1
  exact hR GD' heq w e z a t v v' hv hmin hpmin hew hmo1 hmo2 hrd hwb hlt
    (gviolK2CrossHart _ w e z a t v v' hc hv hpmin hmo1 hmo2 hrd hwb)
    (gviolNoAq _ e w hc hv) (gviolNoFence _ e w hc hv) (gviolNoRcsc _ e w hc hv)
    (fun b => gviolNoPoloc _ e w b hc hv) (gviolNoDep GD' e w hcons hv)

/-! ## 4.3 K3 — the witness is a WRITE racing a cross-hart same-byte write -/

def killK3Racy (GD : Gdexec) : Prop :=
  ∀ GD', gdEquiv GD GD' →
  ∀ (w e z : Geid) (a : Int) (v v' : BitVec 8),
    gviol GD'.gdG e w →
    (∀ e' w', gviol GD'.gdG e' w' → ¬ gmoLt GD'.gdG w' w) →
    (∀ e', gviol GD'.gdG e' w → ¬ e'.2 < e.2) →
    gisW GD'.gdG e = true →
    gisW GD'.gdG z = true → z.1 ≠ e.1 →
    gmoLt GD'.gdG w z → gmoLt GD'.gdG z e →
    gwritesByte GD'.gdG z a v → gwritesByte GD'.gdG e a v' →
    -- ---- the arithmetic exclusions (§2) ----
    ¬ (glblIs GD'.gdG e lbIsR ∧ glblIs GD'.gdG e lbAq) →
    ¬ gfenceCovers GD'.gdG e w →
    ¬ grcsc GD'.gdG e w →
    (∀ b, gaccesses GD'.gdG e b → gaccesses GD'.gdG w b → False) →
    (e, w) ∉ GD'.gdDeps →
    False

theorem killK3OfRacy (GD : Gdexec) : killK3Racy GD → killK3 GD := by
  intro hR GD' heq w e z a v v' hv hmin hpmin hew hzw hag hmo1 hmo2 hzb heb
  obtain ⟨_, _, _, _, hcons⟩ := id heq
  have hc := hcons.1
  exact hR GD' heq w e z a v v' hv hmin hpmin hew hzw hag hmo1 hmo2 hzb heb
    (gviolNoAq _ e w hc hv) (gviolNoFence _ e w hc hv) (gviolNoRcsc _ e w hc hv)
    (fun b => gviolNoPoloc _ e w b hc hv) (gviolNoDep GD' e w hcons hv)

/-! ## 4.4 STATEMENT FIDELITY, MACHINE-CHECKED

The trivial converse — it typechecks only if the shared premise blocks match
exactly. -/

theorem killK1ToRacy (GD : Gdexec) : killK1 GD → killK1Racy GD :=
  fun hK GD' heq w e a t v w0 h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ _ _ =>
    hK GD' heq w e a t v w0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem killK2ToRacy (GD : Gdexec) : killK2 GD → killK2Racy GD :=
  fun hK GD' heq w e z a t v v' h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ _ _ _ =>
    hK GD' heq w e z a t v v' h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem killK3ToRacy (GD : Gdexec) : killK3 GD → killK3Racy GD :=
  fun hK GD' heq w e z a v v' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ _ _ =>
    hK GD' heq w e z a v v' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-! ## 4.5 THE RACY FORMS ARE STILL REAL OBLIGATIONS

The LB non-collapse witness refutes `killK1Racy` too: `lbgdKillK1False`
transported along the reduction. -/

theorem lbgdKillK1RacyFalse : ¬ killK1Racy lbgd :=
  fun hR => lbgdKillK1False (killK1OfRacy lbgd hR)

end Weak
