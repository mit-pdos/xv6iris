/-
Weak: **W11-F [OWN.102] increment 1 — THE REALIZATION BASE**: every configuration of M2's realized pf
run (each recorded step's pre-configuration, and the last one) is matched by a MachCSL configuration
reachable from power-on, related to it by W4's `SimRel` (pool, EQUAL register files, `rmem`,
`viewRel cohSrc`), at which W8's export `xv6AccessDisc` holds.  Lean-only, no Rocq twin.

This is the common source of W11-F's run interfaces (`syncRealized`, `segRealized`/`readAt`,
`fetchReplayOk`, `FrameWin`, …): each of them asks for a MachCSL state `σ` with `rmem c st σ` and
`xv6AccessDisc σ` at a configuration `c` of the realized run (plus interface-specific facts).

* `CapF1.recRealizedH` — the generic form, at any W4 parameter set `HypsC fok fcutT g0 c0` with
  `c0` the pf boot configuration: from `RelSiteProvPc.simRunAt` (every recorded step simulated from
  a reachable related configuration) and `Xv6.xv6DiscAdequacy_closed` (the export at every
  reachable powered-on configuration; `SimRel.pow`).
* `CapF1.recRealized` — at M2: from `srvwmoXv6M2Premises` (the pf run `srvwmoXv6M2PfRun`, W4's
  parameters `PfRunUnpinned.m2Hyps` with `sailCycleOrder_holds`).
* `CapF1.pcLock` — at a realized configuration each pf hart's issuing pc is the MachCSL hart's `PC`
  (`RelSiteProvPc.simRelPc`), and `CapF1.rmemOf` — `rmem` from `SimRel`.

Spec: FAITHFUL (proof organisation over the registered M2 run; no new trusted text).
Every name is file-qualified (`CapF1.*`).
-/
import Weak.RelSiteProvPc
import Weak.SailCycleOrderCycle
import Xv6.LinkDiscAdequacy

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open MachOfPf

/-- **A REALIZED CONFIGURATION**: a MachCSL configuration reachable from `([power], g0)`, related to
the pf configuration `c` (step-list prefix `st`) by `SimRel`, obeying the export. -/
def CapF1.realAt (g0 : GState) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (t : List Expr)
    (g : GState) : Prop :=
  (∃ (n : Nat) (κ : List Obs), MRun n ([Expr.power], g0) κ (t, g)) ∧ SimRel c st t g ∧
    Xv6.AccessDiscipline.xv6AccessDisc g.m

/-- The export at a reachable related configuration. -/
theorem CapF1.discOf (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)}
    {t : List Expr} {g : GState} {n : Nat} {κ : List Obs}
    (hm : MRun n ([Expr.power], g0) κ (t, g)) (hR : SimRel c st t g) : CapF1.realAt g0 c st t g :=
  ⟨⟨n, κ, hm⟩, hR, (Xv6.xv6DiscAdequacy_closed (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κ t g hm).2
    hR.pow⟩

/-- **THE REALIZATION, GENERIC** (any W4 parameter set at the pf boot configuration): along a run
record from the boot configuration, every recorded step's pre-configuration and the last
configuration are realized. -/
theorem CapF1.recRealizedH (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (σ0 : WGState) (g0 : GState) (hb : wbootFacts σ0) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hgd : σ0.wgdev = g0.m.devs.reset) (hfs : diskOf g0.m.devs = Xv6.fsImgDisk)
    (hH : HypsC fok fcutT g0 (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)))
    (st : List (Nat × Wlabel)) (cN : Wpcfg Pexv6 Efab)
    (hrun : pfRunSTC pstepEv pclsEv fok TsoShadow.cohSrc fcutT
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cN)
    (hadj : pairAdjacent st) :
    ∃ r : List PfRec,
      contRC fok fcutT (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cN ∧
      recLabels r = st ∧
      (∃ (t : List Expr) (g : GState), CapF1.realAt g0 cN st t g) ∧
      ∀ x, x ∈ r → ∃ (st' : List (Nat × Wlabel)) (t' : List Expr) (g' : GState),
        CapF1.realAt g0 x.pre st' t' g' := by
  obtain ⟨r, hr, hl, n, t, g, hm, hR⟩ :=
    machRunOfPfRun fok σ0 g0.m.devs g0 hb hgd hg0 hp0 rfl hH st cN hrun hadj
  refine ⟨r, hr, hl, ⟨t, g, CapF1.discOf g0 hg0 hp0 hfs hm hR⟩, fun x hx => ?_⟩
  have hboot := powerOnRun g0 σ0 g0.m.devs hb hg0 hp0 rfl
  have hR0 := simRelBoot σ0 g0.m.devs hb hgd
  obtain ⟨st', n', κ', t', g', hm', hR'⟩ :=
    RelSiteProvPc.simRunAt hH hr hR0 hboot pfRunST.nil (by simpa [hl] using hadj) x hx
  exact ⟨st', t', g', CapF1.discOf g0 hg0 hp0 hfs hm' hR'⟩

/-- **THE REALIZATION AT M2** (`srvwmoXv6M2`'s run): the unpinned, cut-carrying pf run of an M2
candidate, its run record, and every configuration of it realized. -/
theorem CapF1.recRealized (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
    (hP : srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (r : List PfRec),
      pfRunSTC pstepEv pclsEv PfRunUnpinned.fokTriv TsoShadow.cohSrc PfRunUnpinned.fcutM2
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf ∧
      pairAdjacent st ∧
      cf.pcAgs.map Wpagent.paSt = pst c.cdTr.length ∧ cf.pcDev = dv c.cdTr.length ∧
      contRC PfRunUnpinned.fokTriv PfRunUnpinned.fcutM2
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cf ∧
      recLabels r = st ∧
      (∃ (t : List Expr) (g : GState), CapF1.realAt g0 cf st t g) ∧
      ∀ x, x ∈ r → ∃ (st' : List (Nat × Wlabel)) (t' : List Expr) (g' : GState),
        CapF1.realAt g0 x.pre st' t' g' := by
  have hb : wbootFacts σ0 := hP.1
  obtain ⟨cf, st, hrun, hadj, h1, h2, -⟩ := srvwmoXv6M2PfRun σ0 c pst dv itvOf fiOf hP
  have hH := PfRunUnpinned.m2Hyps σ0 hb g0 hg0 hp0 hfs sailCycleOrder_holds
  obtain ⟨r, hr, hl, hend, hall⟩ :=
    CapF1.recRealizedH _ σ0 g0 hb hg0 hp0 hgd hfs hH st cf hrun hadj
  exact ⟨cf, st, r, hrun, hadj, h1, h2, hr, hl, hend, hall⟩

/-- At a realized configuration, `R`'s memory half. -/
theorem CapF1.rmemOf {g0 : GState} {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)}
    {t : List Expr} {g : GState} (h : CapF1.realAt g0 c st t g) : PfStepTsoMem.rmem c st g.m :=
  h.2.1.mem

/-- At a realized configuration, each pf hart's issuing pc is the MachCSL hart's `PC`. -/
theorem CapF1.pcLock {g0 : GState} {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)}
    {t : List Expr} {g : GState} (h : CapF1.realAt g0 c st t g) (cpu : CPU) :
    ∃ ag, c.pcAgs[cpu.val]? = some ag ∧
      RelSiteProvPc.pcOfSt ag.paSt = (((g.m.regs cpu) .PC).toNat : Int) :=
  RelSiteProvPc.simRelPc h.2.1 cpu

end Weak
