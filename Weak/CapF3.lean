/-
Weak: **W11-F [OWN.102] increment 3 — `cycRun` FROM `hartConf` AND THE REALIZATION INTERFACES ONLY**.
Lean-only, no Rocq twin.

`CapF3.cycRunOfHartConfR`: `PinCycRun.cycRunOfHartConfW` with its cycle obligations `fetchOkRF` /
`dataOkRF` discharged by `CapF2.cycFactsAt` from the three run interfaces (`PinFetchPa.fetchRealized`,
`PinDataOk.fetchOkRealized`, `PinDataOk.dataRealized`) at every reached NON-pin walk state, the admin
fetch items from `hartConf` (`PinCycRun.hemitFeNone`).  What is left for W11-F's composition: those
three interfaces, `walkStartRealized`, and `excRetR` (header, [OWN.96]).  Uses the guarded premises
of `cycWalk` / `cycRunOfHartConf*` (inventory A15, approved pass-through edit: the obligations are
needed, and now stated, only at non-pin states).

Spec: FAITHFUL (proof organisation).  Every name is file-qualified (`CapF3.*`).
-/
import Weak.CapF2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Wlabel KernelPinsDef
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinWalkTab
open SailCycleOrderK PinCycRun PinDataflow

/-- **`cycRun` FROM `hartConf`, ALL CYCLE OBLIGATIONS FROM THE INTERFACES** (header). -/
theorem CapF3.cycRunOfHartConfR (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConf i row p0 dv em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em)
    (hreal : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      PinFetchPa.fetchRealized p0 (dv 0) em s.psPc ∧ PinDataOk.fetchOkRealized p0 (dv 0) em s.psPc ∧
        PinDataOk.dataRealized p0 (dv 0) em s.psPc)
    (hexc : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      excRetR G i p0 (dv 0) em s.psPc)
    (base rest : List Eitem) (hes : em.emItems = base ++ rest)
    (hstart : walkStartRealized p0 (dv 0) base (pinStart pcL).psPc) :
    ∃ (mid rest' : List Eitem) (s : PState) (n : Nat) (p' : Pexv6) (d' : Efab),
      rest = mid ++ rest' ∧ cycRun G i em own base (pinStart pcL) mid s ∧
      preach own (pinStart pcL) s n ∧ walkBd p0 (dv 0) em (base ++ mid) s.psPc p' d' ∧
      cycStop G i p0 (dv 0) em own (base ++ mid) s rest' := by
  have hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none :=
    hemitFeNone dv 0 wsInit row p0 em.emItems em.emFin hcf
  have hfacts : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      fetchOkRF p0 (dv 0) em s.psPc ∧ dataOkRF p0 (dv 0) em s.psPc := by
    intro s n l hx hp hne
    obtain ⟨h1, h2, h3⟩ := hreal s n l hx hp hne
    exact CapF2.cycFactsAt pcL w own s n l hm hw hx hp hne p0 (dv 0) em hft hfeN h1 h2 h3
  exact cycRunOfHartConfW G i row p0 dv em pcL w own hcf hm hw hft
    (fun s n l hx hp hne => (hfacts s n l hx hp hne).1)
    (fun s n l hx hp hne => (hfacts s n l hx hp hne).2) hexc base rest hes hstart

end Weak
