/-
Weak: **additive generalisation of `AxGateAdeq`'s purity half** — the purity obligation of a gate
scoped to an EXPLICIT, caller-chosen index set `D` instead of the whole `dom na`.

Rocq: `iris/AxGateAdeq2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`annotPure R φ := R ⊢ ⌜φ⌝` (`AxGateWp`) is already an entailment, so a mixed slot
`R := ⌜φ⌝ ∗ tok_tie` satisfies it; §1 (`annotPureFrame`) makes this the IProp-level fact: the pure
readout is a persistent consequence, `R` survives it.  `naPureGlobal na φ` quantifies over the whole
growing `dom na` with `φ` fixed once (not vacuous — the caller may pick `φ e := True` elsewhere — but
it forces that workaround).  §2's `naPureGlobalEnt na D φ` states purity only over `D` (typically
the gate's sources); §3 shows the old form is the `D := dom na` instance; §4 is `AxGateAdeq.wpGateAdeq`
scoped to `D`, with the carried premises `Hna_dom`/`Hpure` (as in Rocq, and as in `AxGateAdeq`).
Nothing here touches a slot's stored value, nor fetches / the WP step clause (only `wpGate`).

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  No name of this file is in
   `notes/weak-port-dupnames.json`.
2. Typeclass context: Rocq's section takes `invGS_gen HasNoLc Σ`, `axirisG Σ`, `axpol`.  Lean takes
   only what is used (as `AxGateAdeq` deviation 2): §1–§3 just `GF`; §4 `[AxirisG GF]`.
3. Set/map forms as `AxGateAdeq` deviation 3: `list_to_set l` ↦ `(LawfulSet.ofList l : GSet Geid)`,
   `dom na` ↦ `FiniteMap.dom_set na`, `na !! e` ↦ `get? na e`.

**Name map.**  `annot_pure_frame` `annotPureFrame`, `na_pure_global_ent` `naPureGlobalEnt`,
`gate_facts_of_dom_ent` `gateFactsOfDomEnt`, `na_pure_global_ent_of_global`
`naPureGlobalEntOfGlobal`, `gate_facts_of_dom_pure_via_ent` `gateFactsOfDomPureViaEnt`,
`wp_gate_ent` `wpGateEnt`.

**Not ported:** the §5 `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxGateAdeq

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

section ent
variable {GF : BundledGFunctors}

/-! # 1. An `annotPure` extraction is a persistent consequence, never a consuming one -/

/-- `R` survives its own pure readout. -/
theorem annotPureFrame (R : IProp GF) (φ : Prop) :
    annotPure R φ → R ⊢ iprop(⌜φ⌝ ∗ R) := by
  intro Hae
  exact (and_intro Hae .rfl).trans persistent_and_sep_mp

/-! # 2. `naPureGlobal` with `dom na` replaced by an explicit index set `D` -/

/-- Purity of `na`'s slots, stated only over the caller-chosen positions `D`. -/
def naPureGlobalEnt (na : Mea GF) (D : GSet Geid) (φ : Geid → Prop) : Prop :=
  ∀ e, e ∈ D → ∃ R, get? na e = some R ∧ annotPure R (φ e)

/-- `gateFactsOfDomPure` with `D` in place of `dom na`. -/
theorem gateFactsOfDomEnt (na : Mea GF) (gsrcs : List Geid) (D : GSet Geid)
    (φ : Geid → Prop) (Hpure : naPureGlobalEnt na D φ)
    (Hdom : (LawfulSet.ofList gsrcs : GSet Geid) ⊆ D) :
    gateFacts na gsrcs φ := by
  intro e He
  exact Hpure e (Hdom e (elemOfListToSet.2 He))

/-! # 3. The old pure form is the `D := dom na` instance -/

theorem naPureGlobalEntOfGlobal (na : Mea GF) (φ : Geid → Prop) :
    naPureGlobal na φ → naPureGlobalEnt na (FiniteMap.dom_set na) φ :=
  fun Hg e He => Hg e He

theorem gateFactsOfDomPureViaEnt (na : Mea GF) (gsrcs : List Geid) (φ : Geid → Prop)
    (Hpure : naPureGlobal na φ)
    (Hdom : (LawfulSet.ofList gsrcs : GSet Geid) ⊆ FiniteMap.dom_set na) :
    gateFacts na gsrcs φ :=
  gateFactsOfDomEnt na gsrcs (FiniteMap.dom_set na) φ (naPureGlobalEntOfGlobal na φ Hpure) Hdom

end ent

/-! # 4. The `wpGate` composition, scoped to `D` -/

section adeq
variable {GF : BundledGFunctors} [AxirisG GF]

/-- `AxGateAdeq.wpGateAdeq` with the domain/purity premises over `D` rather than `dom na`. -/
theorem wpGateEnt (GD : Gdexec) (i : Agent) (k' : Nat) (gsrcs : List Geid)
    (D : GSet Geid) (φ : Geid → Prop) (Ψ : IProp GF)
    (Hna_dom : ⊢ ∀ na : Mea GF, AxirisG.annotInterp na -∗
       AxirisG.annotInterp na ∗ ⌜(LawfulSet.ofList gsrcs : GSet Geid) ⊆ D⌝)
    (Hpure : ∀ na : Mea GF,
       (LawfulSet.ofList gsrcs : GSet Geid) ⊆ D → naPureGlobalEnt na D φ) :
    wpSkipStepGate GD i k' gsrcs φ Ψ ⊢ wpSkipStep GD i k' Ψ := by
  apply wpGate GD i k' gsrcs φ Ψ
  iintro %na Hn
  ihave Hd := Hna_dom
  icases Hd $$ %na Hn with ⟨Hn, %Hdom⟩
  isplitl [Hn]
  · iexact Hn
  · ipureintro
    exact gateFactsOfDomEnt na gsrcs D φ (Hpure na Hdom) Hdom

end adeq

end Weak
