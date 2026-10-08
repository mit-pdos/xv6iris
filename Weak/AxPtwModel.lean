/-
Weak: **the walker-aware graph model as an `AxWpD.GModel` instance**, and the model-generic
tier-A adequacy and walker bridge at it.

Rocq: `iris/AxPtwModel.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxWpD.wpdM M` takes the graph-consistency model as a parameter; the only interface the
model-generic proofs use is `GModel M` = `gmWf` (`gwf GD.gdG`).  Here `ptwModelRow i kd ws sf`
(AxWalk5 §2) and the per-graph-tagged `ptwModelAt` both provide it (the `gwf` conjunct of
`ptwExplicitConsistent`), so `wpdM (ptwModelRow …)` and the model-generic adequacy
`AxDefer5.tierAAdequacyAnnLM` / `tierAAdequacyAnnGmoM` apply verbatim.

NOT AVAILABLE at the ptw model (riscv.cat-only phase-2 routes, consuming
`rvwmoCatConsistent` beyond `gwf`): `AxTierA2.tierAAdequacyAnn`, `AxTierA4.*Run` (scheduler
hypothesis `gppoCat6Gmo`, `AxSchedGD.Inv2`) — `ptwExplicitConsistent` orders ppo edges only
between NON-walker events; and the dev-2 / `gobCatFlow` handouts (`AxTierA3.flowDev2Gmo`,
`AxDefer5.tierAAdequacyAnnGate`), which need `obCat ⊆ gmo` over ALL events.  The gmo-bounded
route needs neither: `tierAAdequacyAnnGmoM`.

THE WALKER BRIDGE at the walker-aware model: `AxWalk2.wpdOfCertWPM` is model-generic (every node
lemma on the way uses the model premise only by handing it to the caller's premises
`HG`/`Htext`/`Hflow`/`Hloc`/`Hpos`/`Hpin` and the flows `FldM`/`FstM`), so the caller discharges
those — in particular the walker flow `WFrM` — against `ptwModel`, not `rvwmoCatConsistent`.
CAVEAT: `ptwModelRow i kd ws sf` fixes the walker list `ws` BEFORE the WPd while the bridge
REPORTS `ws'` in its continuation; the caller must pick `ws` up front (or use the per-graph
`ptwModelAt fr sfr` form).

## Deviations from Rocq

1. O2 STAGE C: the adequacy theorems have no oracle parameter `T : Int → Prop` (AxDefer5 has
   none), so `tierAAdequacyPtwGmo`/`tierAAdequacyPtwL` drop it.
2. Rocq `Definition X := lemma args` (partially applied lemmas) ↦ Lean
   `theorem X : type_of% (lemma args) := lemma args` (as AxWalk2's `bridgeWCat`).
3. `GPtw GD f sf` ↦ `Gptw.mk GD f sf`; `gd_g` ↦ `.gdG`; `gp_gd` ↦ `.gpGd`; `agent` ↦ `Agent`.

**Rocq → Lean name map.**  `ptw_model_at` `ptwModelAt`, `ptw_model_gwf` `ptwModelGwf`,
`ptw_model_at_gmodel` `ptwModelAtGmodel`, `ptw_model_row_gmodel` `ptwModelRowGmodel`,
`tierA_adequacy_ptw_gmo` `tierAAdequacyPtwGmo`, `tierA_adequacy_ptw_L` `tierAAdequacyPtwL`,
`wpd_of_CertWP_ptw` `wpdOfCertWPPtw`, `wpd_instr_of_CertWP_ptw` `wpdInstrOfCertWPPtw`,
`wpd_of_CertWP_ptw_at` `wpdOfCertWPPtwAt`, `wpd_instr_of_CertWP_ptw_at`
`wpdInstrOfCertWPPtwAt`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 10 definitions/lemmas/instances; Lean 10).  **Not ported:** the
`Check` / `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxWalk5
import Weak.AxDefer5
import Weak.AxDataX9
import Weak.AxWalk2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

/-- The tagging read off the graph (bridge-reported walker positions / sfence markers, per
graph). -/
def ptwModelAt (fr : Gdexec → Geid → Option Geid) (sfr : Gdexec → Geid → Bool)
    (GD : Gdexec) : Prop :=
  ptwModel (Gptw.mk GD (fr GD) (sfr GD))

theorem ptwModelGwf (GP : Gptw) : ptwModel GP → gwf GP.gpGd.gdG :=
  fun H => H.2.1.1

instance ptwModelAtGmodel (fr : Gdexec → Geid → Option Geid) (sfr : Gdexec → Geid → Bool) :
    GModel (ptwModelAt fr sfr) :=
  ⟨fun GD H => ptwModelGwf _ H⟩

instance ptwModelRowGmodel (i kd : Nat) (ws : List (Nat × Wev)) (sf : Geid → Bool) :
    GModel (ptwModelRow i kd ws sf) :=
  ⟨fun GD H => ptwModelGwf _ H⟩

section adequacy
variable {GF : BundledGFunctors.{0,0,0}}

/-- The gmo-bounded tier-A adequacy, at the walker-aware model. -/
theorem tierAAdequacyPtwGmo [InvGpreS GF] [AxannotG GF] [Axpol] (GD : Gdexec)
    (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF) (i kd : Nat) (ws : List (Nat × Wev)) (sf : Geid → Bool) :
    type_of% (tierAAdequacyAnnGmoM GD N obSt0 obStInterp0 init (ptwModelRow i kd ws sf)) :=
  tierAAdequacyAnnGmoM GD N obSt0 obStInterp0 init (ptwModelRow i kd ws sf)

/-- The any-order tier-A adequacy, at the per-graph-tagged walker-aware model. -/
theorem tierAAdequacyPtwL [InvGpreS GF] [AxannotG GF] [Axpol] (GD : Gdexec)
    (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (init : N → Agent → IProp GF)
    (fr : Gdexec → Geid → Option Geid) (sfr : Gdexec → Geid → Bool) :
    type_of% (tierAAdequacyAnnLM GD N obSt0 obStInterp0 init (ptwModelAt fr sfr)) :=
  tierAAdequacyAnnLM GD N obSt0 obStInterp0 init (ptwModelAt fr sfr)

end adequacy

/-! The walker bridge under the walker-aware model. -/
section walkerBridgePtw
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdOfCertWPPtw (iw : Agent) (kd : Nat) (ws : List (Nat × Wev)) (sf : Geid → Bool) :
    type_of% (wpdOfCertWPM (hlc := hlc) (GF := GF) (ptwModelRow iw kd ws sf)) :=
  wpdOfCertWPM (ptwModelRow iw kd ws sf)

theorem wpdInstrOfCertWPPtw (iw : Agent) (kd : Nat) (ws : List (Nat × Wev)) (sf : Geid → Bool) :
    type_of% (wpdInstrOfCertWPM (hlc := hlc) (GF := GF) (ptwModelRow iw kd ws sf)) :=
  wpdInstrOfCertWPM (ptwModelRow iw kd ws sf)

theorem wpdOfCertWPPtwAt (fr : Gdexec → Geid → Option Geid) (sfr : Gdexec → Geid → Bool) :
    type_of% (wpdOfCertWPM (hlc := hlc) (GF := GF) (ptwModelAt fr sfr)) :=
  wpdOfCertWPM (ptwModelAt fr sfr)

theorem wpdInstrOfCertWPPtwAt (fr : Gdexec → Geid → Option Geid) (sfr : Gdexec → Geid → Bool) :
    type_of% (wpdInstrOfCertWPM (hlc := hlc) (GF := GF) (ptwModelAt fr sfr)) :=
  wpdInstrOfCertWPM (ptwModelAt fr sfr)

end walkerBridgePtw

end Weak
