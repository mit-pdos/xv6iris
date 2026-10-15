/-
Weak: **W11-F [OWN.102] increment 10 — A2's FLOOR EQUATION AT A REALIZED MachCSL STATE**.  Lean-only,
no Rocq twin.

`CapF7.loadFloorRealized`: for an M2 candidate and its `k`-th step, a plain load of hart `cpu` reading
byte `j` (physical `pa`) from a FOREIGN timestamp `t`, there is a MachCSL configuration reachable from
power-on, `SimRel`-related to a pf configuration `cf` whose log IS the candidate's log after the load
(`elog (candExec c) (k + 1)`), obeying the export (`CapF1.realAt`), at which hart `cpu`'s coherence
floor at `pa` IS `t` — `readAt`'s floor clause (`Weak/RvwmoXv6Adequacy.lean:272`) at that state.

Route (per-prefix, no record bookkeeping): M2's replay at the prefix `k + 1`
(`execPrefixPfRunProgF`: a cut-carrying pf run from boot whose step-list shadow is the candidate's
shadow of `take (k + 1)`, log matched), W4 on THAT run (`machRunOfPfRun` with `PfRunUnpinned.m2Hyps`),
the export (`CapF1.discOf`), `SimRel.view`'s `hartRel.cohEq`, and the candidate floor equation
`CapF6.cohAfterLoad`.

Spec: FAITHFUL (proof organisation over the registered M2 run).  Names: `CapF7.*`.
-/
import Weak.CapF1
import Weak.CapF6

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow PfStepTsoView
open MachOfPf

/-- **THE FLOOR EQUATION, REALIZED** (header). -/
theorem CapF7.loadFloorRealized (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
    (hP : srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk)
    (k : Nat) (s : Estep) (hs : (candExec c).exTr[k]? = some s) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : s.esLb = .LLoad aq base ts vs) (j t au' : Nat)
    (hj : ts[j]? = some t)
    (hsrc : shSrc (shadowRun cohSrc s.esAg ((candExec c).exTr.take k)).1 t = some (au', t))
    (hne : au' ≠ s.esAg) (cpu : CPU) (hcpu : hartAgent cpu = s.esAg) (pa : PAddr)
    (hpa : paZ pa = accAddr base j) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (t' : List Expr) (g : GState),
      CapF1.realAt g0 cf st t' g ∧ cf.pcLog = elog (candExec c) (k + 1) ∧
      (g.m.hr cpu).coh pa = t := by
  obtain ⟨hb, -, -, hcons, himg, hpst, hdv, hprog, hscaT, -, hi0, hf0⟩ := hP
  obtain ⟨hwf, -, heximg⟩ := srvwmoRealizable c hcons
  have hk : k + 1 ≤ (candExec c).exTr.length := lookup_lt_Some hs
  obtain ⟨cf, st, hrun, hadj, -, -, hm, hsh, -⟩ :=
    execPrefixPfRunProgF pstepEv pclsEv _ cohSrc pst dv (candExec c) itvOf fiOf (k + 1)
      pclsEvEqr hwf hprog hi0 hf0 hk
  rw [heximg, himg, hpst, hdv] at hrun
  have hH := PfRunUnpinned.m2Hyps σ0 hb g0 hg0 hp0 hfs sailCycleOrder_holds
  obtain ⟨r, -, -, n, t', g, hmr, hR⟩ :=
    machRunOfPfRun _ σ0 g0.m.devs g0 hb hgd hg0 hp0 rfl hH st cf hrun hadj
  refine ⟨cf, st, t', g, CapF1.discOf g0 hg0 hp0 hfs hmr hR, hm.2.1.symm, ?_⟩
  have hcoh := (hR.view cpu).cohEq pa
  rw [hcoh, hpa]
  have hmem : (tsoShadow cohSrc st (hartAgent cpu)).mem =
      shadowOf cohSrc ((candExec c).exTr.take (k + 1)) (hartAgent cpu) := by
    have := congrArg Prod.snd (hsh (hartAgent cpu))
    simpa only [tsoShadow, shadowOf, TsoShadow.memOf] using this
  rw [hmem, hcpu]
  exact CapF6.cohAfterLoad (candExec c) hwf hscaT k s hs aq base ts vs hl j t au' hj hsrc hne

end Weak
