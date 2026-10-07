/-
Weak: **supplying `AxGateWp.wpGate`'s `Hna` premise from scheduler adequacy** — what closes, and
the precise remaining gap.

Rocq: `iris/AxGateAdeq.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`gateFacts na gsrcs φ` unfolds to "for every source `e`, SOME resource is on record at `e` in
`na` (the DOMAIN half) AND that resource already entails `φ e` (the PURITY half)".  The halves
come from different places and are kept separate:

- DOMAIN — from the scheduler.  §1 (`gateSrcsDomOfSched`): at a fully-processed scheduler run
  (`schedCorrect`'s `Hfull`/`Hdone`), every graph memory event sits in `st.sProc`, hence — GIVEN
  the same `Hdom` hypothesis `AxSchedGD.schedProcAdequate` itself requires — inside `dom na`.
- PURITY — NOT from adequacy.  `adequacyOrdL`/`schedProcAdequate` are `Axpol`-generic and treat
  `na`'s entries as opaque resources.  §2 packages purity as the named invariant `naPureGlobal`
  and shows domain + purity is exactly `gateFacts` (`gateFactsOfDomPure`).

THE STRUCTURAL GAP.  `wpEvStep` carries the LOCAL `naAtProgress GD i k na`; `wpSkipStep` /
`wpSkipStepGate` carry only `annotInterp na`, which never pins `dom na` to the graph.  So `Hna`
cannot be discharged for an ARBITRARY `na` from adequacy alone; §3 threads the GLOBAL domain fact
in EXPLICITLY, as a hypothesis of `Hna`'s own shape (`Hna_dom` / `Hna_dom_run`).  These are the
file's carried, undischargeable-here premises (as in Rocq).

**Fetches / WP step clause.**  Nothing here mentions fetches or the WP step clause: the file only
uses `wpGate`/`wpGateRow` (skip-step level) and `schedCorrect` as black boxes, so the pending Q8
fetch-pin rework of the step clause does not touch it.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  No name of this file is in
   `notes/weak-port-dupnames.json`.
2. Typeclass context: Rocq's sections take `invGS_gen HasNoLc Σ`, `axirisG Σ`, `axpol`.  Lean takes
   only what is used (as `AxGateWp` deviation 2): `naPureGlobal`/`gateFactsOfDomPure` need just
   `GF`; the §3 lemmas just `[AxirisG GF]`.
3. `list_to_set l ⊆ dom na` ↦ `(LawfulSet.ofList l : GSet Geid) ⊆ FiniteMap.dom_set na` (the form
   of `AxSchedGD.schedProcAdequate`'s `Hdom`); `na !! e` ↦ `get? na e`; `e ∈ dom na` ↦
   `e ∈ (FiniteMap.dom_set na : GSet Geid)`.
4. `gateSrcsDomOfSched` is over an arbitrary value type `A` with `na : GMapF Geid A`
   (Rocq `gmap geid A`), as in Rocq.

**Name map.**  `gate_srcs_dom_of_sched` `gateSrcsDomOfSched`, `na_pure_global` `naPureGlobal`,
`gate_facts_of_dom_pure` `gateFactsOfDomPure`, `wp_gate_adeq` `wpGateAdeq`, `wp_gate_row_adeq`
`wpGateRowAdeq`, `wp_gate_row_adeq_of_sched` `wpGateRowAdeqOfSched`.

**Not ported:** the §4 `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxGateWp
import Weak.AxSchedGD

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The domain half: scheduler adequacy places every gate source inside `dom na` -/

/-- GIVEN `na`'s own `Hdom` (never derived from `annotInterp` alone), a completed scheduler run
puts every graph memory event among `gsrcs` inside `dom na`. -/
theorem gateSrcsDomOfSched {A : Type} (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (na : GMapF Geid A) (Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆ FiniteMap.dom_set na)
    (gsrcs : List Geid) (Hmem : ∀ r, r ∈ gsrcs → r ∈ GD.gdG.gxGmo) :
    (LawfulSet.ofList gsrcs : GSet Geid) ⊆ FiniteMap.dom_set na := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  intro e He
  rw [elemOfListToSet] at He
  exact Hdom e (elemOfListToSet.2 ((Hmemiff e).2 (Hmem e He)))

/-! # 2. The purity half: a NAMED invariant on `na`, and its composition with §1 -/

section purity
variable {GF : BundledGFunctors}

/-- For every position `na` covers, its resource already entails the claimed pure fact. -/
def naPureGlobal (na : Mea GF) (φ : Geid → Prop) : Prop :=
  ∀ e, e ∈ (FiniteMap.dom_set na : GSet Geid) → ∃ R, get? na e = some R ∧ annotPure R (φ e)

/-- Domain (§1) + purity is exactly `gateFacts`. -/
theorem gateFactsOfDomPure (na : Mea GF) (gsrcs : List Geid) (φ : Geid → Prop)
    (Hpure : naPureGlobal na φ)
    (Hdom : (LawfulSet.ofList gsrcs : GSet Geid) ⊆ FiniteMap.dom_set na) :
    gateFacts na gsrcs φ := by
  intro e He
  exact Hpure e (Hdom e (elemOfListToSet.2 He))

end purity

/-! # 3. Discharging `wpGate`/`wpGateRow`'s `Hna`, the domain premise threaded in explicitly -/

section adeq
variable {GF : BundledGFunctors} [AxirisG GF]

/-- `wpGate`'s `Hna`, split into the domain half `Hna_dom` (of `Hna`'s own shape — NOT free) and
the purity invariant `Hpure`. -/
theorem wpGateAdeq (GD : Gdexec) (i : Agent) (k' : Nat) (gsrcs : List Geid) (φ : Geid → Prop)
    (Ψ : IProp GF)
    (Hna_dom : ⊢ ∀ na : Mea GF, AxirisG.annotInterp na -∗
       AxirisG.annotInterp na ∗ ⌜(LawfulSet.ofList gsrcs : GSet Geid) ⊆ FiniteMap.dom_set na⌝)
    (Hpure : ∀ na : Mea GF,
       (LawfulSet.ofList gsrcs : GSet Geid) ⊆ FiniteMap.dom_set na → naPureGlobal na φ) :
    wpSkipStepGate GD i k' gsrcs φ Ψ ⊢ wpSkipStep GD i k' Ψ := by
  apply wpGate GD i k' gsrcs φ Ψ
  iintro %na Hn
  ihave Hd := Hna_dom
  icases Hd $$ %na Hn with ⟨Hn, %Hdom⟩
  isplitl [Hn]
  · iexact Hn
  · ipureintro
    exact gateFactsOfDomPure na gsrcs φ (Hpure na Hdom) Hdom

/-- Same, at `AxGate.gateSrcs`'s concrete instantiation (per `wpGateRow`). -/
theorem wpGateRowAdeq (GD : Gdexec) (i : Agent) (k' : Nat) (s0 : DstateT) (srcs : List Dsrc)
    (φ : Geid → Prop) (Ψ : IProp GF)
    (Hna_dom : ⊢ ∀ na : Mea GF, AxirisG.annotInterp na -∗
       AxirisG.annotInterp na ∗
         ⌜(LawfulSet.ofList (gateSrcs i s0 srcs) : GSet Geid) ⊆ FiniteMap.dom_set na⌝)
    (Hpure : ∀ na : Mea GF,
       (LawfulSet.ofList (gateSrcs i s0 srcs) : GSet Geid) ⊆ FiniteMap.dom_set na →
         naPureGlobal na φ) :
    wpSkipStepGate GD i k' (gateSrcs i s0 srcs) φ Ψ ⊢ wpSkipStep GD i k' Ψ := by
  apply wpGateRow GD i k' s0 srcs φ Ψ
  iintro %na Hn
  ihave Hd := Hna_dom
  icases Hd $$ %na Hn with ⟨Hn, %Hdom⟩
  isplitl [Hn]
  · iexact Hn
  · ipureintro
    exact gateFactsOfDomPure na (gateSrcs i s0 srcs) φ (Hpure na Hdom) Hdom

/-- §1's scheduler fact lifted to `Hna_dom`'s shape: given that `na`'s domain covers a completed
scheduler's `sProc` (`Hna_dom_run`, the same `Hdom` `schedProcAdequate` takes), the scheduler's
domain contribution plus the named purity invariant supply `wpGateRow`'s `Hna`. -/
theorem wpGateRowAdeqOfSched (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (i : Agent) (k' : Nat) (s0 : DstateT) (srcs : List Dsrc)
    (Hmem : ∀ r, r ∈ gateSrcs i s0 srcs → r ∈ GD.gdG.gxGmo)
    (φ : Geid → Prop) (Ψ : IProp GF)
    (Hna_dom_run : ⊢ ∀ na : Mea GF, AxirisG.annotInterp na -∗
       AxirisG.annotInterp na ∗
         ⌜(LawfulSet.ofList st.sProc : GSet Geid) ⊆ FiniteMap.dom_set na⌝)
    (Hpure : ∀ na : Mea GF,
       (LawfulSet.ofList (gateSrcs i s0 srcs) : GSet Geid) ⊆ FiniteMap.dom_set na →
         naPureGlobal na φ) :
    wpSkipStepGate GD i k' (gateSrcs i s0 srcs) φ Ψ ⊢ wpSkipStep GD i k' Ψ := by
  refine wpGateRowAdeq GD i k' s0 srcs φ Ψ ?_ Hpure
  iintro %na Hn
  ihave Hd := Hna_dom_run
  icases Hd $$ %na Hn with ⟨Hn, %Hdom⟩
  isplitl [Hn]
  · iexact Hn
  · ipureintro
    exact gateSrcsDomOfSched GD Hcons st Hrun Hfull Hdone na Hdom (gateSrcs i s0 srcs) Hmem

end adeq

end Weak
