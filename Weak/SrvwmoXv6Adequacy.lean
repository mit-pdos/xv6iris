/-
Weak: **W5 CORE — M1's composition** (allocproc plan `notes/weak-allocproc-plan.md` §C W5 /
"W5 CORE", rev 29; [R21.4]; F9's disk rows discharged by W4 F9, `MachOfPf.simDisk`).  Lean-only
(no Rocq source).

INTERNAL MILESTONE M1 (NOT published, [OWN.2]); kernel-only BY PREMISE (D21: M1's fetch clause
`candKfetch bcRoLo bcRoHi`); loads single-copy atomic at or above the TsoMem floor BY PREMISE
(`candScaT cohSrc`).  `srvwmoXv6M1Core` is registered in `roots-weak.txt` (with its
`baseline-weak.json` entry, audited by `tools/ci/audit.sh --weak`; W5 CLOSE-OUT).  Since W4 F9 the theorem is NO LONGER conditional on the disk
rows (the former `diskRows` / `DR` hypotheses are gone; [OWN.40] made the pf disk program stall
on an OUT buffer wrapping past `2^64`, so no disk side condition remains either).

## Status (D21)

M1 — composition milestone, INTERNAL (not published [OWN.2]): kernel-only by premise
`candKfetch`, loads single-copy-atomic at or above the TsoMem floor by premise `candScaT`,
disk-row loads latest by premise `candDiskLat`, under the named ISA-model premise
`sailCycleOrder` [OWN.35] (W-SCO demotes it for kernel text); the disk rows PROVED (W4 F9), no
side condition; the realizing MachCSL run satisfies `xv6FsAdequacy_closed`'s conclusions,
`xv6NiPhi`, `unionPhiSync`, `textPristine` and the allocproc shadow; axioms = the SC roots'
(`propext`, `Classical.choice`, `Quot.sound`; opaques the two `resv` predicates +
`MachCSL.bootImageSealed`) + the `bv_decide` certificates the audit counts (`audit.json`);
non-vacuity: `srvwmoXv6M1Satisfiable` (QUIESCENT, D22/D44).

## The composition

`srvwmoXv6M1Core`: from M1's premise set `srvwmoXv6M1Premises σ0 c pst dv` (W5-pre, stated
THROUGH the definition, never re-listed) and a MachCSL machine off `g0` (generation 0, power off,
`fs.img` on the disk, `σ0`'s devices its reset; `SrvwmoXv6Adequacy.bootStateOf` builds one from
the premises' `ds`):
1. `srvwmoXv6M1PfRun` (W5-pre) gives the shaped, shadow-threaded pf run `pfRunST … cohSrc` with
   `pairAdjacent` and the projection lemma;
2. `MachOfPf.machRunOfPfRun` (W4 F1–F8) turns it into ONE `PowerOn` step and a MachCSL run
   `MRun n ([power], g0) (powerOn :: pfObsOf r) (t, g)` related to the run's end by `SimRel`,
   at `MachOfPf.Hyps` discharged here (`SrvwmoXv6Adequacy.m1Hyps`):
   * `tso`  = `pfStepTsoProposed` (W2 CLOSE, `Weak/PfStepTso.lean`);
   * `safe` = HSafe, `(Xv6.xv6FsAdequacy_closed g0 …).1` (E-S1);
   * `cut`  = `MachOfPf.cutOfPristine bcRoLo bcRoHi` with `bcRoLo = ramBase`, `bcRoHi = _data ≤
     ramEnd`, its `winPristine` hypothesis at every reachable powered state from
     `(Xv6.xv6TextAdequacy_closed …).2` (W3's sibling root, through `powerInterp_textPristine`)
     read through `Xv6.textWin_get` (`SrvwmoXv6Adequacy.winOfText`);
   * `fi`   = from the NAMED premise `sailCycleOrder` [OWN.35] by the one-fold lemma
     `SrvwmoXv6Adequacy.fiArmLastCyc` over `shStepF` (`SrvwmoXv6Adequacy.fiOfSco`);
   * the disk rows are no longer a parameter: W4 F9 proves them (`MachOfPf.simDisk`);
3. the closed xv6 theorems conclude at the realized run: `Reducible` and `xv6TracePure`
   (`xv6FsAdequacy_closed`), `xv6NiPhi` (`xv6NiAdequacy`), `unionPhiSync`
   (`unionAdequacyClosed`), the pristine window (`xv6TextAdequacy_closed`, at `SimRel.pow`), and
   W1b's allocproc shadow on the trace (`allocprocTraceAns`, restated as
   `SrvwmoXv6Adequacy.allocprocAns`).  `Xv6.Allocproc` (T-alloc, `Xv6/LinkAllocproc.lean`) is in
   these theorems' cone through `userProof` (`LinkMain`/`LinkSyscall`).

`SimRel` is used ONLY through `machRunOfPfRun`'s `MRun`/`pfObsOf`, through `cutOfPristine` (its
`pow`/`mem`/`auth` fields, inside W4's file) and `SimRel.pow` (the pristine-window conjunct);
its device clause (F9's `R-dev`) is never unfolded.  `SimRel` appears in the conclusion as an
opaque relation.

## `sailCycleOrder` [OWN.35] — the named ISA-model premise, LABEL-LIST form [R21.s1]

Along every `pfRunST` run from `wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)` (any
`fok`, any `σ0`), at each own `.barrier Barrier_RISCV_i` node the LATEST own `LInstr`/`LIFetch`
step of the step list is `LInstr`, and at each own `sfence.vma` announce node it is an `LIFetch`
— Sail's cycle fetch → announce → execute, no instruction fetch during execute
(`model/Lean_RV64D/LeanRV64D/Step.lean:331-404`).  Stated on the label list
(`SrvwmoXv6Adequacy.lastCyc`), NOT through `tsoShadow`'s `fiArm` bit.  FAITHFUL (true of the
Sail model by inspection; RVWMO / riscv.cat / Zifencei / PMAs are silent on in-cycle order).
W-SCO (after M1) proves it for xv6's kernel text and removes it from M1.

## Remaining hypotheses of `srvwmoXv6M1Core`

* M1's premise set `srvwmoXv6M1Premises σ0 c pst dv` (satisfiable: `srvwmoXv6M1Satisfiable`);
* the MachCSL boot state `g0`: `g0.gen = 0`, `g0.pow = false`, `σ0.wgdev = g0.m.devs.reset`,
  `diskOf g0.m.devs = fsImgDisk` (always constructible: `SrvwmoXv6Adequacy.bootStateOf`);
* `sailCycleOrder` [OWN.35].

## Deviations from the plan text

1. The plan's §C W5 says W5 CORE also corrects `MachOfPf.lean`'s header deviation 3 ("its owner
   is OPEN") to [OWN.35]; W4 F9 made that correction in `MachOfPf.lean`'s header
   (`PfStepTsoView.lean`'s deviation (4) is corrected by the W5 CLOSE-OUT, naming
   `sailCycleOrder` and W-SCO's `sailCycleOrderK_holds`).
2. (W4 F9) The former `diskRows` (a copy of `MachOfPf.Hyps.disk`'s type) and its `DR`
   parameter are DELETED with that field.
3. `allocprocAns` is a COPY of `Xv6.allocprocTraceAns`'s conclusion (proved by `exact`).

Every helper is `Weak.SrvwmoXv6Adequacy.*`; `Weak.sailCycleOrder` and `Weak.srvwmoXv6M1Core` are
top-level.  Axioms: those of `Xv6.xv6FsAdequacy_closed` (`propext`, `Classical.choice`,
`Quot.sound`, …; printed at the end).
-/
import Weak.MachOfPf
import Weak.PfStepTso
import Weak.SrvwmoXv6Witness
import Xv6.LinkSystemAdequacyClosed
import Xv6.LinkTextAdequacy
import Xv6.LinkUInitUnion
import Xv6.AllocprocTrace

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Sail.ArchSem (FreeM)
open TsoShadow PfStepTsoMem PfStepTsoView
open Iris.ProgramLogic

/-! ## (1) `sailCycleOrder`, in label-list form -/

/-- The labels of Sail's cycle skeleton: the instruction boundary / announce `LInstr` and an
instruction fetch `LIFetch`. -/
def SrvwmoXv6Adequacy.lbCyc (l : Wlabel) : Bool :=
  match l with
  | .LInstr => true
  | .LIFetch .. => true
  | _ => false

/-- The LATEST own `LInstr`/`LIFetch` step of agent `i` in the step list `st` (`none` if there is
none). -/
def SrvwmoXv6Adequacy.lastCyc (i : Nat) (st : List (Nat × Wlabel)) : Option Wlabel :=
  ((st.filter (fun y => y.1 == i && SrvwmoXv6Adequacy.lbCyc y.2)).getLast?).map Prod.snd

/-- **THE NAMED ISA-MODEL PREMISE `sailCycleOrder`** [OWN.35][R20.s4][R21.s1]: along every
`pfRunST` run from the pf boot configuration (any fetch clause `fok`, any boot state `σ0`), at an
own `fence.i` BARRIER node the latest own `LInstr`/`LIFetch` step is `LInstr` (the announce), and
at an own `sfence.vma` ANNOUNCE node it is an `LIFetch` (the instruction's fetch) — "the Sail
cycle fetches, then announces, then executes, and fetches nothing while executing"
(`Step.lean:331-404`).  A closed proposition (the shape `bootImageSealed` has); FAITHFUL. -/
def sailCycleOrder : Prop :=
  ∀ (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (σ0 : WGState)
    (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab),
    pfRunST pstepEv pclsEv fok TsoShadow.cohSrc
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st c →
    ∀ (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
      (ib : Ibch) (ws : Wstate) (pr : GSet Nat),
      c.pcAgs[cpu.val]? = some ⟨.PHart cpu (.impure (.ok o) k) rs none ib, ws, pr⟩ →
      (o = .barrier .Barrier_RISCV_i →
         SrvwmoXv6Adequacy.lastCyc (hartAgent cpu) st = some .LInstr) ∧
      (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
         ∃ base tvs, SrvwmoXv6Adequacy.lastCyc (hartAgent cpu) st = some (.LIFetch base tvs))

/-- The `fiArm` bit a latest cycle label stands for. -/
def SrvwmoXv6Adequacy.fiOf (x : Option Wlabel) : Bool :=
  match x with
  | some .LInstr => true
  | _ => false

/-- **The one-fold lemma** [R20.s4]: the shadow's `fiArm` (set by `LInstr`, cleared by
`LIFetch`, `shStepF`) IS "the latest own `LInstr`/`LIFetch` step is `LInstr`", under every
stamp. -/
theorem SrvwmoXv6Adequacy.fiArmLastCyc (stamp : CohStamp) (i : Nat) :
    ∀ st : List (Nat × Wlabel),
      (tsoShadow stamp st i).fiArm = SrvwmoXv6Adequacy.fiOf (SrvwmoXv6Adequacy.lastCyc i st) := by
  intro st0
  obtain ⟨rs, rfl⟩ : ∃ rs : List (Nat × Wlabel), st0 = rs.reverse := ⟨st0.reverse, by simp⟩
  induction rs with
  | nil => rfl
  | cons y rs ih =>
    rw [List.reverse_cons]
    generalize rs.reverse = st at ih ⊢
    obtain ⟨j, l⟩ := y
    rw [tsoShadowSnoc]
    unfold SrvwmoXv6Adequacy.lastCyc
    rw [List.filter_append]
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      unfold SrvwmoXv6Adequacy.lastCyc at ih
      cases l <;>
        simp [shStepF, SrvwmoXv6Adequacy.lbCyc, SrvwmoXv6Adequacy.fiOf, ih]
    · rw [if_neg hj]
      have hf : List.filter (fun y : Nat × Wlabel => y.1 == i && SrvwmoXv6Adequacy.lbCyc y.2)
          [(j, l)] = [] := by
        simp [hj]
      rw [hf, List.append_nil]
      exact ih

/-- `MachOfPf.Hyps.fi` from `sailCycleOrder`. -/
theorem SrvwmoXv6Adequacy.fiOfSco (hsco : sailCycleOrder)
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (σ0 : WGState) :
    ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab),
      pfRunST pstepEv pclsEv fok TsoShadow.cohSrc
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st c →
      ∀ (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
        (ib : Ibch) (ws : Wstate) (pr : GSet Nat),
        c.pcAgs[cpu.val]? = some ⟨.PHart cpu (.impure (.ok o) k) rs none ib, ws, pr⟩ →
        (o = .barrier .Barrier_RISCV_i →
           (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) ∧
        (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
           (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false) := by
  intro st c hrun cpu o k rs ib ws pr hag
  obtain ⟨hb, ha⟩ := hsco fok σ0 st c hrun cpu o k rs ib ws pr hag
  rw [SrvwmoXv6Adequacy.fiArmLastCyc]
  refine ⟨fun h => by rw [hb h]; rfl, fun n w h hs => ?_⟩
  obtain ⟨base, tvs, e⟩ := ha n w h hs
  rw [e]
  rfl

/-! ## (2) The fetch cut, the boot state -/

/-- `cutOfPristine`'s window hypothesis, from W3's sibling root: whenever the power is on, every
byte of `[bcRoLo, bcRoHi)` holds the fresh era's history. -/
theorem SrvwmoXv6Adequacy.winOfText (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) :
    ∀ (n : Nat) (κs : List Obs) (t : List Expr) (g : GState),
      MachOfPf.MRun n ([Expr.power], g0) κs (t, g) → g.pow = true →
      MachOfPf.winPristine Xv6.bcRoLo Xv6.bcRoHi g := by
  intro n κs t g hm hpow pa hlo hhi
  obtain ⟨v, -, hw⟩ := Xv6.textWin_get pa hlo hhi
  exact ⟨v, (Xv6.xv6TextAdequacy_closed (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm).2
    hpow pa _ hw⟩

/-- The pristine window lies in DRAM: `bcRoHi = _data ≤ ramEnd`. -/
theorem SrvwmoXv6Adequacy.bcRoHiLe : Xv6.bcRoHi ≤ ramEnd := by decide

/-- **`MachOfPf.Hyps` at M1** (`fok = candKfetch bcRoLo bcRoHi`, the pf boot configuration):
`tso`, `safe`, `cut`, `fi` discharged (the disk rows are W4 F9's `MachOfPf.simDisk`, no longer a
field). -/
theorem SrvwmoXv6Adequacy.m1Hyps (σ0 : WGState) (g0 : GState) (hg0 : g0.gen = 0)
    (hp0 : g0.pow = false) (hfs : diskOf g0.m.devs = Xv6.fsImgDisk)
    (hsco : sailCycleOrder) :
    MachOfPf.Hyps (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) g0
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) where
  tso := pfStepTsoProposed _
  safe := fun n κs t g hm =>
    (Xv6.xv6FsAdequacy_closed (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm).1
  cut := MachOfPf.cutOfPristine Xv6.bcRoLo Xv6.bcRoHi (Nat.le_refl _) SrvwmoXv6Adequacy.bcRoHiLe
    g0 _ (SrvwmoXv6Adequacy.winOfText g0 hg0 hp0 hfs)
  fi := SrvwmoXv6Adequacy.fiOfSco hsco _ σ0

/-- The MachCSL machine-off state `srvwmoXv6M1Core` starts from exists for every M1 premise set
(from the premises' `ds`): the extra boot hypotheses are never vacuous. -/
theorem SrvwmoXv6Adequacy.bootStateOf (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) (hP : srvwmoXv6M1Premises σ0 c pst dv) :
    ∃ g0 : GState, g0.gen = 0 ∧ g0.pow = false ∧ σ0.wgdev = g0.m.devs.reset ∧
      diskOf g0.m.devs = Xv6.fsImgDisk := by
  obtain ⟨-, -, ⟨ds, hds, hdisk⟩, -⟩ := hP
  exact ⟨⟨{ (MachOfPf.bootG1 σ0 ds).m with devs := ds }, 0, false⟩, rfl, rfl, hds, hdisk⟩

/-! ## (3) The conclusion's allocproc shadow (`allocprocTraceAns`, verbatim) -/

section
open Xv6

/-- `Xv6.allocprocTraceAns`'s conclusion on the trace `κs` (W1b; `Xv6/AllocprocTrace.lean`). -/
def SrvwmoXv6Adequacy.allocprocAns (κs : List Obs) : Prop :=
  ∃ F, niOk κs F ∧ niOneShot κs F ∧ niChain F (niHist F) ∧
    (∀ k, AllocprocTrace.forkHist F k <+: (niHist F k).pev ∧
      pidHistWf PIDMAX (AllocprocTrace.forkHist F k) ∧
      (AllocprocTrace.liveList (AllocprocTrace.forkHist F k)).Nodup ∧
      (∀ z : Nat, z ∈ AllocprocTrace.liveList (AllocprocTrace.forkHist F k) ↔
        liveOf (AllocprocTrace.forkHist F k) (z : Int))) ∧
    ∀ q : NiInc, ∀ s ∈ utrace q κs F, AllocprocTrace.isFork s →
    ∃ k ι, s.cite = some (k, ι) ∧ niBelow ι (niHist F k) ∧ ι.pev <+: AllocprocTrace.forkHist F k ∧
      AllocprocTrace.ans s = usysForkAns ι ∧
      AllocprocTrace.forkRet (usysForkAns ι) ∧
      (1 ≤ pidPick PIDMAX ι.pev ∧ pidPick PIDMAX ι.pev ≤ PIDMAX) ∧ nextOf PIDMAX ι.pev ≤ PIDMAX ∧
      (forkOk ι → ¬ liveOf ι.pev (pidPick PIDMAX ι.pev : Int)) ∧
      pidHistWf PIDMAX ι.pev ∧ (AllocprocTrace.liveList ι.pev).Nodup ∧
      (∀ z : Nat, z ∈ AllocprocTrace.liveList ι.pev ↔ liveOf ι.pev (z : Int)) ∧
      (ι.kNull → poolEmpty ι.kev.dropLast) ∧ (ι.kOk → ¬ poolEmpty ι.kev.dropLast)

end

/-- **Every closed xv6 conclusion at one MachCSL run** from the machine off: reducibility, trace
purity, the NI conclusion, the union conclusion, the pristine window when powered, and the
allocproc shadow. -/
theorem SrvwmoXv6Adequacy.xv6Concl (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) (n : Nat) (κs : List Obs) (t : List Expr)
    (g : GState) (hm : MachOfPf.MRun n ([Expr.power], g0) κs (t, g)) :
    (∀ e, e ∈ t → PrimStep.Reducible (e, g)) ∧
    Xv6.xv6TracePure Xv6.fsimgCov Xv6.fsimgSb.sbLogstart g ∧
    Xv6.xv6NiPhi g κs ∧ Xv6.unionPhiSync κs ∧ (g.pow = true → Xv6.textPristine g) ∧
    SrvwmoXv6Adequacy.allocprocAns κs := by
  obtain ⟨hred, hpure⟩ := Xv6.xv6FsAdequacy_closed (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm
  exact ⟨hred, hpure,
    (Xv6.xv6NiAdequacy (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm).2,
    (Xv6.unionAdequacyClosed (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm).2,
    (Xv6.xv6TextAdequacy_closed (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm).2,
    Xv6.allocprocTraceAns (hlc := Iris.HasLC.hasLC) g0 hg0 hp0 hfs n κs t g hm⟩

/-! ## (4) THE COMPOSITION -/

/-- **W5 CORE — M1's composition** (plan §C W5, [R21.4]; the disk rows by W4 F9).  From M1's
premise set (W5-pre), a MachCSL machine off `g0` matching the pf boot (generation 0, power off,
`fs.img`, `σ0`'s devices its reset) and the named premise `sailCycleOrder` [OWN.35]:
the shaped pf run `srvwmoXv6M1PfRun` gives (with its projections), its run record `r`, and a
MachCSL run of `([power], g0)` observing `powerOn :: pfObsOf r` to `(t, g)`, related to the pf
run's end by `SimRel`, at which every thread is reducible (panics and the two spin arms not
excluded), the trace is pure (`xv6TracePure`), the NI and union conclusions hold, the kernel's
read-only window is pristine, and the allocproc shadow (`allocprocTraceAns`) holds of the trace. -/
theorem srvwmoXv6M1Core (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (hP : srvwmoXv6M1Premises σ0 c pst dv)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk)
    (hsco : sailCycleOrder) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (r : List MachOfPf.PfRec) (n : Nat)
      (t : List Expr) (g : GState),
      -- the shaped pf run (W5-pre)
      pfRunST pstepEv pclsEv (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int)) TsoShadow.cohSrc
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf ∧
      pairAdjacent st ∧
      cf.pcAgs.map Wpagent.paSt = pst c.cdTr.length ∧ cf.pcDev = dv c.cdTr.length ∧
      cfgMatchd cf (stt (candExec c) c.cdTr.length) ∧
      (∀ i, (tsoShadow TsoShadow.cohSrc st i).mem = shadowOf TsoShadow.cohSrc c.cdTr i) ∧
      -- its run record and the realizing MachCSL run (W4)
      MachOfPf.contR (candKfetch (Xv6.bcRoLo : Int) (Xv6.bcRoHi : Int))
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cf ∧
      MachOfPf.recLabels r = st ∧
      MachOfPf.MRun n ([Expr.power], g0) (Obs.powerOn :: MachOfPf.pfObsOf r) (t, g) ∧
      MachOfPf.SimRel cf st t g ∧
      -- the closed xv6 theorems at that run
      (∀ e, e ∈ t → PrimStep.Reducible (e, g)) ∧
      Xv6.xv6TracePure Xv6.fsimgCov Xv6.fsimgSb.sbLogstart g ∧
      Xv6.xv6NiPhi g (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.unionPhiSync (Obs.powerOn :: MachOfPf.pfObsOf r) ∧
      Xv6.textPristine g ∧
      SrvwmoXv6Adequacy.allocprocAns (Obs.powerOn :: MachOfPf.pfObsOf r) := by
  have hb : wbootFacts σ0 := hP.1
  obtain ⟨cf, st, hrun, hadj, h1, h2, h3, h4⟩ := srvwmoXv6M1PfRun σ0 c pst dv hP
  have hH := SrvwmoXv6Adequacy.m1Hyps σ0 g0 hg0 hp0 hfs hsco
  obtain ⟨r, hr, hl, n, t, g, hm, hR⟩ :=
    MachOfPf.machRunOfPfRun _ σ0 g0.m.devs g0 hb hgd hg0 hp0 rfl hH st cf hrun hadj
  obtain ⟨hred, hpure, hni, hun, htext, hap⟩ :=
    SrvwmoXv6Adequacy.xv6Concl g0 hg0 hp0 hfs n _ t g hm
  exact ⟨cf, st, r, n, t, g, hrun, hadj, h1, h2, h3, h4, hr, hl, hm, hR, hred, hpure, hni, hun,
    htext hR.pow, hap⟩

end Weak

#print axioms Weak.SrvwmoXv6Adequacy.fiArmLastCyc
#print axioms Weak.SrvwmoXv6Adequacy.m1Hyps
#print axioms Weak.srvwmoXv6M1Core
#print axioms Xv6.xv6FsAdequacy_closed
