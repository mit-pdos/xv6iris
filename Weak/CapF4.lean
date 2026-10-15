/-
Weak: **W11-F [OWN.102] increment 4 — the fabric premise `gfDevWIoCZ` (inventory B4)**.  Lean-only,
no Rocq twin.

* `CapF4.bootHarts` — the boot list `(List.range' 0 N).map boot = epsInit σ0` has `N = NCPU + 1`
  entries, the first `NCPU` of them harts.
* `CapF4.gfDevWIoCZOf` — `CatLin.gfDevWIoCZ` over the class from `gfDevWIoOfXv6`: the boot's harts,
  the row-count bound the kill's `hpre` already gives (`≤ N`), and the NAMED device-model premise
  `usedElemGateOk` ([OWN.93]: permanent) at every class member.
* `CapF4.gfDevWIoCZOfBoot` — the same at the pf boot list.

Spec: FAITHFUL (proof organisation); `usedElemGateOk` stays the header's device-model premise.
Every name is file-qualified (`CapF4.*`).
-/
import Weak.CertZ17

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

theorem CapF4.bootHarts (σ0 : WGState) (boot : Nat → Pexv6) (N : Nat)
    (hb : (List.range' 0 N).map boot = epsInit σ0) :
    N = NCPU + 1 ∧ ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true := by
  have hlen := congrArg List.length hb
  simp only [List.length_map, List.length_range', epsInit, List.length_append, List.length_singleton,
    enumCPULength] at hlen
  refine ⟨hlen, fun i hi => ?_⟩
  have h1 : ((List.range' 0 N).map boot)[i]? = some (boot i) := by
    rw [List.getElem?_map, List.getElem?_range' (by omega)]
    simp
  rw [hb] at h1
  have hc : i < cpus.length := by rw [enumCPULength]; exact hi
  unfold epsInit at h1
  rw [List.getElem?_append_left (by simpa using hc), List.getElem?_map,
    List.getElem?_eq_getElem hc] at h1
  simp only [Option.map_some, Option.some.injEq] at h1
  rw [← h1]
  rfl

/-- **`gfDevWIoCZ` from the device-model premise** (header). -/
theorem CapF4.gfDevWIoCZOf (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (hbt : ∀ i, i < NCPU → GraphFabConf.isHart (boot i) = true)
    (hlen : ∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im →
      CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ NCPU + 1)
    (hgate : ∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im →
      CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      usedElemGateOk GF) :
    CatLin.gfDevWIoCZ boot d0 fab im :=
  fun GF ad him hc hconf =>
    gfDevWIoOfXv6 boot d0 fab GF (GraphFabConf.gfexecConfZFZ boot d0 fab GF hconf) hbt
      (hlen GF ad him hc hconf) (hgate GF ad him hc hconf)

/-- **At the pf boot list** (the kill's `(List.range' 0 N).map boot = epsInit σ0` and its row bound). -/
theorem CapF4.gfDevWIoCZOfBoot (σ0 : WGState) (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (im : Image) (N : Nat) (hb : (List.range' 0 N).map boot = epsInit σ0)
    (hlen : ∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im →
      CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N)
    (hgate : ∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = im →
      CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      usedElemGateOk GF) :
    CatLin.gfDevWIoCZ boot d0 fab im := by
  obtain ⟨hN, hbt⟩ := CapF4.bootHarts σ0 boot N hb
  subst hN
  exact CapF4.gfDevWIoCZOf boot d0 fab im hbt hlen hgate

end Weak
