/-
Weak: **W4 — a shaped pf run IS a MachCSL run** (allocproc plan §C W4, the STRUCTURAL half
F1–F8; census `notes/W4-structural-census.md` §F).  Lean-only (no Rocq source).

**Main theorem** `MachOfPf.machRunOfPfRun`: from the machine off (`g0`: generation 0, power off,
devices `ds`) and a pf boot `σ0` (`wbootFacts`, devices `ds.reset`), every `pfRunST` run (any
`fok`, stamp `cohSrc`) from `wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)` — exactly
`srvwmoXv6M1PfRun`'s configuration — with `pairAdjacent` steps has a RUN RECORD `r` (`contR`: the
run's configurations and step kinds, `recLabels r = st`) such that `([power], g0)` makes ONE
`PowerOn` step and then runs, `MRun n` (= iris `NSteps`, no bound `n ≤ |st|`, E-S6), observing
`.powerOn :: pfObsOf r` — a FUNCTION of the record (E-S3) — to a MachCSL configuration related to
the run's last configuration by `SimRel` (`poolRel ∧ R_mem`).

**The relation** `SimRel DR c st t g` (F1): generation 0, power on (the power thread is never
stepped again); the pool is `poolOf H F vs` — thread `0` power, `c + 1` hart `c` running the pf
hart's residual monad `H c`, `NCPU + 1`/`+ 2` the UART programs and `NCPU + 3` the PLIC program
of the fabric, then the virtio threads `vs`, related to the disk agent's program by the F9
parameter `DR` (E-S2: the thread map is per step KIND, `thrOf`); register files and device states
EQUAL; and `R_mem` = W2's `rmem ∧ viewRel cohSrc`, with the `R-log` link to the step list
(`pfStepTso`'s hypothesis (2)) and `ownCoh` (part of (4)); every parked fence is `fence.tso`'s
parked half (`fnOk`).

**Rows** (census table B6, `simStep`: 0 or 1 MachCSL step per pf step off the disk program):
* F3 boot (`powerOnRun`, `simRelBoot`): `bootG1` from `wbootFacts` (its register clause IS
  `bootFacts`'), `bootShape`, `primStep_power_on`; `R_mem` by `rmemBoot`/`viewRelNil`.
* F4/F5 hart node (`simNode`): parked-fence fire and lost-SC retry = 0 steps (frame: the shadow
  of the parked `LFence true true false true` is the identity, `viewRelPark`); the boundary, the
  silent nodes, register reads and writes (`LSilent`/`LRegW`/`LCtrl`, all `lbInert`) = 1
  `primStep` with `σ' = σ` / `setReg`, `R_mem` by `memFrame` (W2a `pfFrameRowMem`, W2b
  `viewRelInert`); MMIO = 1 step (`devRead`/`devWrite`, the whole-footprint `devBytes` from HSafe,
  `devOfSafe`); RAM read/write, barrier, announce/marker = 1 step through `pfStepTso`, its
  hypotheses discharged here: `ramBytes` from HSafe (`ramOfSafe`, `notOthers` from `R-resv` and
  the adjacency), (1) from the full run's `pairAdjacent`, (2) from `SimRel`, (3) from `Hyps.cut`,
  (4) `ownCoh` from `SimRel` and `exclOkTs` from the pair's own exclusive store
  (`exclAhead`/`walkToStore`: only the agent's administrative steps lie between), the `fiArm`
  facts from `Hyps.fi`; the MachCSL post-state's registers/devices by `evStepShape`.
* F6 devices (`simDev`, `simWire`): the disk agent's UART/PLIC-gateway `fdevStep` = 1 `devStep`
  of the device's own thread (`devStepOfFdev`, observed `fdevObs`); the hart's PLIC wire = 1
  `devOpStep .setPin` of the PLIC thread (`pinM`).
* F7 `pfStepObs`/`pfObsOf`: a hart node emits `hartObsM` read off the pf register file
  (`hartObsMEq`), a UART step its guard's events, everything else nothing.
* F8 `simRun`: forward induction over the record (`contROfRun` turns the snoc-built `pfRunST` into
  it; the look-ahead (4) needs the record's tail).
* M1 (`cutOfPristine`): `Hyps.cut` at `fok = candKfetch lo hi` from a MachCSL-side pristine window
  (`winPristine`, W3's `textPristine` read through `textWin_get`).

**Parameters** (`Hyps`): `tso` = W2 CLOSE's `pfStepTso` in the ADOPTED shape (`pfStepTsoStmt`, a
verbatim copy of `PfStepTso.proposedStmt`); `safe` = HSafe (E-S1); `cut` = the fetch cut at every
fetch; `fi` = plan item (3) (`fiArm` at `fence.i` / the `sfence.vma` marker); `disk` = F9's
disk-program rows over `DR`.

**Deviations from the plan / census text.**
1. `pfStepTso` is the coordinator-adopted `proposedStmt` (2026-10-11), not the pinned §C W2 CLOSE
   text (false at the fetch and log-length rows, unusable inside exclusive pairs:
   `PROGRESS-W2CLOSE.md`, `PROGRESS-W4s.md`).
2. The companions `pfStepTsoStutter`/`pfStepTsoSame` are NOT parameters: W4 proves those rows
   itself from the landed W2a/W2b frame lemmas (`memFrame`, `viewRelPark`) — including the rows
   their prose missed (the boundary `LInstr`, a register write labelled `LSilent`, the PLIC wire
   at a parked fence or at the boundary, the disk agent's UART/PLIC moves).
3. Item (3) (`fiArm`) is a PARAMETER (`Hyps.fi`, stated over every `pfRunST` run from the boot
   configuration): W2 CLOSE disowned it (a fact of Sail's event order inside `try_step`, not of
   the step list); its owner is OPEN.
4. The fetch cut is a PARAMETER over related, boot-reachable states (`Hyps.cut`), discharged at
   M1 by `cutOfPristine` from a SECOND MachCSL-side hypothesis (the pristine window at every
   reachable powered state; W5: `powerInterp_textPristine`) — `candKfetch` alone does not give it.
5. `κs` is a function of the run RECORD (configurations + step kinds): the disk agent's
   `LDev .dev 0 []` does not say which device moved, and `pfRunST` is a `Prop`.
6. Disk rows (F9) are the parameter `Hyps.disk`; `SimRel` keeps `efDev = σ.devs` EQUAL — after
   W-DISK, `R-dev` is equality only up to `pre₁` on the OUT capture segment [R18.3], so F9 will
   generalize the device clause (and re-check the hart MMIO row against it).

Every name is in `Weak.MachOfPf` (file-qualified).  Axioms: `propext`, `Classical.choice`,
`Quot.sound`.
-/
import Weak.PfStepTsoMem
import Weak.PfStepTsoView
import Weak.PfRunShape
import Weak.WeakEvCapstone

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Sail.ArchSem (FreeM)
open TsoShadow PfStepTsoMem PfStepTsoView

namespace MachOfPf

/-! ## (0) The parameter: W2 CLOSE's `pfStepTso`, in the ADOPTED shape

`pfStepTsoStmt` is a verbatim copy of `PfStepTso.proposedStmt` (W2 CLOSE, `Weak/PfStepTso.lean`;
adopted by the coordinator 2026-10-11 over the plan's pinned text, `PROGRESS-W2CLOSE.md`), so
`pfStepTsoProposed : PfStepTso.proposedStmt fok` instantiates it by `exact`. -/

def pfStepTsoStmt (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) : Prop :=
  ∀ (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (cpu : CPU)
    (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (rest : List (Nat × Wlabel)),
    pstepEv (.PHart cpu (.impure (.ok o) k) rs fn ib) c.pcDev l p' d' →
    wpPfStep pstepEv pclsEv (hartAgent cpu) l c c' →
    pairAdjacent (st ++ (hartAgent cpu, l) :: rest) →                              -- (1)
    pfStepFactsT fok TsoShadow.cohSrc st c (hartAgent cpu) l →
    (∀ n va req, o = .memRead n va req → ramBytes req.pa n) →
    (∀ n va req, o = .memWrite n va req → ramBytes req.pa n) →
    rmem c st σ → viewRel TsoShadow.cohSrc σ st →
    c.pcLog.map Wmsg.wmTid = (stAuthors st).map some →                             -- (2)
    (∀ base tvs, l = .LIFetch base tvs →                                           -- (3)
       ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
         ifetchOk c.pcImg c.pcLog q base tvs ∧
         ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q) →
    (∀ aq base tvs asrc, l = .LExLoad aq base tvs asrc →                           -- (4)
       ownCoh c ∧ exclOkTs c.pcLog (hartAgent cpu) base (tvs.map Prod.fst) (c.pcLog.length + 1)) →
    fn = none →
    l ≠ .LSilent → (∀ kd ba bs, l ≠ .LDev kd ba bs) →
    (o = .barrier .Barrier_RISCV_i →
       (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) →
    (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
       (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false) →
    ∃ (v : o.ret) (σ' : MState),
      evStep cpu o σ v σ' ∧
      (∃ rs' fn' ib', p' = .PHart cpu (k v) rs' fn' ib') ∧
      rmem c' (st ++ [(hartAgent cpu, l)]) σ' ∧
      viewRel TsoShadow.cohSrc σ' (st ++ [(hartAgent cpu, l)])

/-! ## (F2) `NSteps` helpers (iris `Language.lean` has no transitivity lemma) -/

open Iris.ProgramLogic

/-- A MachCSL run of `n` thread-pool steps. -/
abbrev MRun (n : Nat) (ρ : List Expr × GState) (κ : List Obs) (ρ' : List Expr × GState) : Prop :=
  Language.NSteps n ρ κ ρ'

theorem mrunTrans {n m : Nat} {ρ1 ρ2 ρ3 : List Expr × GState} {κ1 κ2 : List Obs}
    (h1 : MRun n ρ1 κ1 ρ2) (h2 : MRun m ρ2 κ2 ρ3) : MRun (n + m) ρ1 (κ1 ++ κ2) ρ3 := by
  revert h2
  induction h1 with
  | refl ρ => intro h2; simpa using h2
  | cons hs _ ih =>
    intro h2
    have := Language.NSteps.cons hs (ih h2)
    rw [List.append_assoc, Nat.add_right_comm]
    exact this

theorem mrunRefl (ρ : List Expr × GState) : MRun 0 ρ [] ρ := .refl ρ

/-- One primitive step of thread `j` is a one-step run. -/
theorem mrunOne {t : List Expr} {j : Nat} {e e' : Expr} {g g' : GState} {obs : List Obs}
    {efs : List Expr} (hj : t[j]? = some e) (hs : PrimStep.primStep (e, g) obs (e', g', efs)) :
    MRun 1 (t, g) obs (t.set j e' ++ efs, g') := by
  have := Language.NSteps.cons (Language.step_update_of_getElem? g g' hj hs) (.refl _)
  simpa using this

/-! ## (F1) The thread pool by step KIND (E-S2), `thrOf`, and the relation -/

/-- The hart part of the pool: hart `c` at thread `1 + c`. -/
def hartsOf (H : CPU → SailM Unit) : List Expr := cpus.map (fun c => Expr.hart 0 c (H c))

/-- THE POOL AFTER `PowerOn` (iris `Step.atomic` appends forks at the END): thread `0` the power
thread (stepped once, never again), `1 + c` hart `c`, `NCPU + 1`/`+ 2` the UARTs, `NCPU + 3` the
PLIC, then the virtio threads (root, then its forked tasks — F9). -/
def poolOf (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) : List Expr :=
  .power :: (hartsOf H ++ (Expr.dev 0 (.uart .uart0) rootTask F.efU0 ::
    Expr.dev 0 (.uart .uart1) rootTask F.efU1 :: Expr.dev 0 .plic rootTask F.efPlic :: vs))

/-- Update one hart's residual monad. -/
def updH (H : CPU → SailM Unit) (c : CPU) (m : SailM Unit) : CPU → SailM Unit :=
  fun c' => if c' = c then m else H c'

/-- The thread of a UART. -/
def uartThr : UartId → Nat
  | .uart0 => NCPU + 1
  | .uart1 => NCPU + 2

/-- The PLIC's thread. -/
def plicThr : Nat := NCPU + 3

/-- The KIND of a pf step (E-S2): which `pstepEv` disjunct it takes, hence which MachCSL thread
runs it. -/
inductive SKind where
  /-- a hart's own node (`pstepNode`) — thread `1 + c` -/
  | node
  /-- a hart taking the PLIC wire (`pstepPlic`) — the PLIC thread -/
  | wire
  /-- the disk agent stepping UART `u` (`pdiskUart`, UART arm) — the UART's thread -/
  | uart (u : UartId)
  /-- the disk agent stepping the PLIC program (`pdiskUart`, PLIC arm) — the PLIC thread -/
  | gate
  /-- the disk agent's own program (`pdiskProg`) — the virtio threads (F9) -/
  | disk

/-- **`thrOf`**: the MachCSL thread a pf step of agent `i` and kind `k` runs on (the disk
program's threads are F9's: the virtio root at `NCPU + 4`, its tasks after). -/
def thrOf (k : SKind) (i : Nat) : Nat :=
  match k with
  | .node => i + 1
  | .wire => plicThr
  | .uart u => uartThr u
  | .gate => plicThr
  | .disk => NCPU + 4

theorem hartsOfLength (H : CPU → SailM Unit) : (hartsOf H).length = NCPU := by
  simp [hartsOf, enumCPULength]

theorem hartsOfGet (H : CPU → SailM Unit) (c : CPU) :
    (hartsOf H)[c.val]? = some (Expr.hart 0 c (H c)) := by
  simp only [hartsOf, List.getElem?_map, enumCPULookup, Option.map_some]

theorem cpusGetLt (j : Nat) (hj : j < NCPU) : cpus[j]? = some ⟨j, hj⟩ :=
  enumCPULookup ⟨j, hj⟩

theorem hartsOfSet (H : CPU → SailM Unit) (c : CPU) (m : SailM Unit) :
    (hartsOf H).set c.val (Expr.hart 0 c m) = hartsOf (updH H c m) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  by_cases hj : j < NCPU
  · simp only [hartsOf, List.getElem?_map, cpusGetLt j hj, Option.map_some, List.length_map,
      enumCPULength, updH]
    by_cases hcj : c.val = j
    · subst hcj
      simp [c.isLt]
    · have hne : (⟨j, hj⟩ : CPU) ≠ c := fun h => hcj (by rw [← h])
      simp [hcj, hne]
  · have hl : (hartsOf H).length ≤ j := by rw [hartsOfLength]; omega
    have hl' : (hartsOf (updH H c m)).length ≤ j := by rw [hartsOfLength]; omega
    have hcj : c.val ≠ j := by have := c.isLt; omega
    rw [if_neg hcj, List.getElem?_eq_none hl, List.getElem?_eq_none hl']

theorem poolHart (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (c : CPU) :
    (poolOf H F vs)[c.val + 1]? = some (Expr.hart 0 c (H c)) := by
  simp only [poolOf, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by rw [hartsOfLength]; exact c.isLt), hartsOfGet]

theorem poolHartSet (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (c : CPU) (m : SailM Unit) :
    (poolOf H F vs).set (c.val + 1) (Expr.hart 0 c m) = poolOf (updH H c m) F vs := by
  simp only [poolOf, List.set_cons_succ]
  rw [List.set_append_left _ _ (by rw [hartsOfLength]; exact c.isLt), hartsOfSet]

theorem poolTail (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (j : Nat) :
    (poolOf H F vs)[NCPU + 1 + j]? =
      (Expr.dev 0 (.uart .uart0) rootTask F.efU0 :: Expr.dev 0 (.uart .uart1) rootTask F.efU1 ::
        Expr.dev 0 .plic rootTask F.efPlic :: vs)[j]? := by
  rw [show NCPU + 1 + j = (NCPU + j) + 1 by omega]
  simp only [poolOf, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [hartsOfLength]; omega), hartsOfLength,
    show NCPU + j - NCPU = j by omega]

theorem poolTailSet (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (j : Nat) (e : Expr) :
    (poolOf H F vs).set (NCPU + 1 + j) e =
      .power :: (hartsOf H ++ (Expr.dev 0 (.uart .uart0) rootTask F.efU0 ::
        Expr.dev 0 (.uart .uart1) rootTask F.efU1 :: Expr.dev 0 .plic rootTask F.efPlic :: vs).set j e) := by
  rw [show NCPU + 1 + j = (NCPU + j) + 1 by omega]
  simp only [poolOf, List.set_cons_succ]
  rw [List.set_append_right _ _ (by rw [hartsOfLength]; omega), hartsOfLength,
    show NCPU + j - NCPU = j by omega]

theorem poolUart (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (u : UartId) :
    (poolOf H F vs)[uartThr u]? = some (Expr.dev 0 (.uart u) rootTask (efU F u)) := by
  cases u
  · rw [show uartThr .uart0 = NCPU + 1 + 0 from rfl, poolTail]; rfl
  · rw [show uartThr .uart1 = NCPU + 1 + 1 from rfl, poolTail]; rfl

theorem poolUartSet (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (u : UartId)
    (m : DevProg (.uart u)) (ds : DevStates) :
    (poolOf H F vs).set (uartThr u) (Expr.dev 0 (.uart u) rootTask m) =
      poolOf H (efUset { F with efDev := ds } u m) vs := by
  cases u
  · rw [show uartThr .uart0 = NCPU + 1 + 0 from rfl, poolTailSet]; rfl
  · rw [show uartThr .uart1 = NCPU + 1 + 1 from rfl, poolTailSet]; rfl

theorem poolPlic (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) :
    (poolOf H F vs)[plicThr]? = some (Expr.dev 0 .plic rootTask F.efPlic) := by
  rw [show plicThr = NCPU + 1 + 2 from rfl, poolTail]; rfl

theorem poolPlicSet (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (m : DevProg .plic)
    (ds : DevStates) :
    (poolOf H F vs).set plicThr (Expr.dev 0 .plic rootTask m) =
      poolOf H { F with efDev := ds, efPlic := m } vs := by
  rw [show plicThr = NCPU + 1 + 2 from rfl, poolTailSet]; rfl

/-- `thrOf` names the thread each kind runs on (E-S2). -/
theorem thrOfPool (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (cpu : CPU) (u : UartId) :
    (poolOf H F vs)[thrOf .node cpu.val]? = some (Expr.hart 0 cpu (H cpu)) ∧
    (poolOf H F vs)[thrOf (.uart u) NCPU]? = some (Expr.dev 0 (.uart u) rootTask (efU F u)) ∧
    (poolOf H F vs)[thrOf .wire cpu.val]? = some (Expr.dev 0 .plic rootTask F.efPlic) ∧
    (poolOf H F vs)[thrOf .gate NCPU]? = some (Expr.dev 0 .plic rootTask F.efPlic) :=
  ⟨poolHart H F vs cpu, poolUart H F vs u, poolPlic H F vs, poolPlic H F vs⟩

/-- The pool's shape depends on the fabric only through the residual UART/PLIC programs. -/
theorem poolOfDev (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (ds : DevStates) :
    poolOf H { F with efDev := ds } vs = poolOf H F vs := rfl

/-- A parked fence is `fence.tso`'s parked half (`ebarPark`), the only one the program half
parks. -/
def fnOk (fn : Option (Bool × Bool × Bool × Bool)) : Prop :=
  ∀ x, fn = some x → x = (true, true, false, true)

/-- **THE SIMULATION RELATION** `poolRel ∧ R_mem` at a pf configuration `c` with step-list
prefix `st` and a MachCSL configuration `(t, g)`: generation 0, power on; the pool is `poolOf`
with the harts' residual monads those of the pf harts, the UART/PLIC programs the fabric's, and
the virtio threads related to the disk agent's program by the F9 parameter `DR`; the register
files and device states equal; and `R_mem` = W2's `rmem ∧ viewRel cohSrc`, with the `R-log` link
to the step list and `ownCoh` (the hypotheses (2)/(4) of `pfStepTso`). -/
structure SimRel (DR : Option (DM Dres) → List Expr → Prop) (c : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (t : List Expr) (g : GState) : Prop where
  gen : g.gen = 0
  pow : g.pow = true
  pool : ∃ (H : CPU → SailM Unit) (vs : List Expr) (dp : Option (DM Dres)) (dws : Wstate)
      (dpr : GSet Nat),
    t = poolOf H c.pcDev vs ∧ c.pcAgs.length = NCPU + 1 ∧
    (∀ cpu : CPU, ∃ fn ib ws pr,
       c.pcAgs[cpu.val]? = some ⟨.PHart cpu (H cpu) (g.m.regs cpu) fn ib, ws, pr⟩ ∧ fnOk fn) ∧
    c.pcAgs[NCPU]? = some ⟨.PDisk dp, dws, dpr⟩ ∧ DR dp vs
  dev : c.pcDev.efDev = g.m.devs
  mem : rmem c st g.m
  view : viewRel TsoShadow.cohSrc g.m st
  auth : c.pcLog.map Wmsg.wmTid = (stAuthors st).map some
  coh : ownCoh c

/-! ## (F3) The boot bridge: `wbootFacts` → `bootShape`, the one `PowerOn` step -/

/-- The booted MachCSL state: the pf boot's register files (`wbootFacts`' register clause IS
`bootFacts`'), the boot image, an empty log, zero views, the reset devices. -/
def bootG1 (σ0 : WGState) (ds : DevStates) : GState :=
  { m := ⟨σ0.wgregs, imgFlat bootImage, [], fun _ => 0, fun _ => 0, fun _ => HRead.zero,
          fun _ => none, ds.reset, fun _ => DevRt.init⟩,
    gen := 0, pow := true }

theorem bootShapeG1 (g0 : GState) (σ0 : WGState) (ds : DevStates) (hb : wbootFacts σ0)
    (hg : g0.gen = 0) (hd : g0.m.devs = ds) : bootShape g0 (bootG1 σ0 ds) := by
  obtain ⟨-, -, -, -, -, hregs, -, -⟩ := hb
  refine ⟨hg.symm, rfl, ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, hregs, fun _ => rfl⟩, ?_⟩
  show ds.reset = g0.m.devs.reset
  rw [hd]

/-- The pool `PowerOn` forks IS `poolOf` at the boundary. -/
theorem powerForkPool (ds : DevStates) :
    Expr.power :: powerFork 0 = poolOf (fun _ => FreeM.pure ()) (efInit ds) [DevLoop 0 .virtio] := rfl

/-- **The PowerOn step** (`primStep_power_on`, `Lang.lean`). -/
theorem powerOnRun (g0 : GState) (σ0 : WGState) (ds : DevStates) (hb : wbootFacts σ0)
    (hg : g0.gen = 0) (hp : g0.pow = false) (hd : g0.m.devs = ds) :
    MRun 1 ([Expr.power], g0) [Obs.powerOn]
      (poolOf (fun _ => FreeM.pure ()) (efInit ds.reset) [DevLoop 0 .virtio], bootG1 σ0 ds) := by
  have hs := primStep_power_on hp (bootShapeG1 g0 σ0 ds hb hg hd)
  have := mrunOne (t := [Expr.power]) (j := 0) rfl hs
  rw [hg] at this
  simpa [← powerForkPool] using this

/-- The initial pf configuration's agents. -/
theorem epsInitAgs (σ0 : WGState) (img : Image) (d0 : Efab) :
    ((wpInit img d0 (epsInit σ0)) : Wpcfg Pexv6 Efab).pcAgs.length = NCPU + 1 ∧
    (∀ cpu : CPU, (wpInit img d0 (epsInit σ0) : Wpcfg Pexv6 Efab).pcAgs[cpu.val]? =
       some ⟨.PHart cpu (FreeM.pure ()) (σ0.wgregs cpu) none (σ0.wgib cpu), wsInit, ∅⟩) ∧
    (wpInit img d0 (epsInit σ0) : Wpcfg Pexv6 Efab).pcAgs[NCPU]? = some ⟨.PDisk none, wsInit, ∅⟩ := by
  refine ⟨by simp [wpInit, epsInit, enumCPULength], fun cpu => ?_, ?_⟩
  · simp only [wpInit, epsInit, List.getElem?_map]
    rw [List.getElem?_append_left (by simp [enumCPULength, cpu.isLt]), List.getElem?_map,
      enumCPULookup]
    rfl
  · simp only [wpInit, epsInit, List.getElem?_map]
    rw [List.getElem?_append_right (by simp [enumCPULength])]
    simp [enumCPULength]

/-- **The relation at boot** (census §D3): `R-regs` by `epsInit`, `R-expr` the boundary, `R-fab`
the reset devices and `.pure ()` programs, `R_mem` by `rmemBoot` and `viewRelNil`. -/
theorem simRelBoot (DR : Option (DM Dres) → List Expr → Prop) (hDR : DR none [DevLoop 0 .virtio])
    (σ0 : WGState) (ds : DevStates) (hb : wbootFacts σ0) (hds : σ0.wgdev = ds.reset) :
    SimRel DR (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) []
      (poolOf (fun _ => FreeM.pure ()) (efInit ds.reset) [DevLoop 0 .virtio]) (bootG1 σ0 ds) := by
  have himg : σ0.wgimg = bootImage := hb.2.1
  obtain ⟨hlen, hcpu, hdisk⟩ := epsInitAgs σ0 (imgZ σ0.wgimg) (efInit σ0.wgdev)
  refine ⟨rfl, rfl, ⟨fun _ => FreeM.pure (), [DevLoop 0 .virtio], none, wsInit, ∅,
    by rw [hds]; rfl, hlen, fun cpu => ⟨none, σ0.wgib cpu, wsInit, ∅, hcpu cpu,
      fun _ h => by cases h⟩, hdisk, hDR⟩, by rw [hds]; rfl, ?_, ?_, by simp [wpInit, stAuthors],
    ownCohInit _ _ _⟩
  · rw [himg]
    exact rmemBoot _ _ _ ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, hb.2.2.2.2.2.1, fun _ => rfl⟩
  · exact viewRelNil _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-! ## (F1, cont.) Step kinds, inversion, the run record -/

/-- The pf program step of KIND `k` (one disjunct of `pstepEv`, E-S2). -/
def kindStep (k : SKind) (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) : Prop :=
  match k, p, p' with
  | .node, .PHart cpu m rs fn ib, .PHart cpu' m' rs' fn' ib' =>
      cpu' = cpu ∧ ∃ (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind),
        rs' = ors.getD rs ∧ ib' = oib.getD ib ∧
        pstepNode cpu m rs fn ib d.efDev l m' ors fn' d'.efDev oib obar ∧
        d' = { d with efDev := d'.efDev }
  | .wire, .PHart cpu m rs fn ib, .PHart cpu' m' rs' fn' ib' =>
      cpu' = cpu ∧ ∃ (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind),
        rs' = ors.getD rs ∧ ib' = oib.getD ib ∧
        pstepPlic cpu m rs fn ib d l m' ors fn' d' oib obar
  | .uart u, .PDisk dp, .PDisk dp' =>
      dp' = dp ∧ l = .LDev .dev 0 [] ∧
      ∃ (m' : DevProg (.uart u)) (ds' : DevStates),
        fdevStep (.uart u) (efU d u) d.efDev m' ds' ∧ d' = efUset { d with efDev := ds' } u m'
  | .gate, .PDisk dp, .PDisk dp' =>
      dp' = dp ∧ l = .LDev .dev 0 [] ∧
      ∃ (m' : DevProg .plic) (ds' : DevStates),
        fdevStep .plic d.efPlic d.efDev m' ds' ∧ d' = { d with efDev := ds', efPlic := m' }
  | .disk, .PDisk dp, .PDisk dp' =>
      pdiskProg dp d.efDev l dp' d'.efDev ∧ d' = { d with efDev := d'.efDev }
  | _, _, _ => False

/-- Every program step has a kind. -/
theorem pstepEvKind (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab)
    (h : pstepEv p d l p' d') : ∃ k, kindStep k p d l p' d' := by
  match p, p', h with
  | .PHart cpu m rs fn ib, .PHart cpu' m' rs' fn' ib', h =>
    obtain ⟨hc, ors, oib, obar, hrs, hib, hh⟩ := h
    rcases hh with ⟨hn, hd⟩ | hp
    · exact ⟨.node, hc, ors, oib, obar, hrs, hib, hn, hd⟩
    · exact ⟨.wire, hc, ors, oib, obar, hrs, hib, hp⟩
  | .PDisk dp, .PDisk dp', h =>
    rcases h with ⟨hp, hd⟩ | ⟨hdp, hl, hu⟩
    · exact ⟨.disk, hp, hd⟩
    · rcases hu with ⟨u, m', ds', hf, hd⟩ | ⟨m', ds', hf, hd⟩
      · exact ⟨.uart u, hdp, hl, m', ds', hf, hd⟩
      · exact ⟨.gate, hdp, hl, m', ds', hf, hd⟩
  | .PHart .., .PDisk _, h => nomatch h
  | .PDisk _, .PHart .., h => nomatch h

/-- **Inversion of a promise-free step**: the agent's program moves by `pstep`, the fabric is
the program step's, the agent's entry is replaced. -/
theorem wpPfStepInv {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (i : Nat) (l : Wlabel) (c c' : Wpcfg P D)
    (h : wpPfStep pstep pcls i l c c') :
    ∃ (ag : Wpagent P) (p' : P) (d' : D) (ws' : Wstate),
      c.pcAgs[i]? = some ag ∧ pstep ag.paSt c.pcDev l p' d' ∧
      c'.pcImg = c.pcImg ∧ c'.pcDev = d' ∧ c'.pcAgs = c.pcAgs.set i ⟨p', ws', ag.paProm⟩ := by
  cases h with
  | PFSilent _ ag st' d' hlk hps => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFLoad _ ag _ _ _ _ _ st' d' hlk hps _ => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFStore _ ag _ _ _ _ _ _ st' d' hlk hps _ _ => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFRmw _ ag _ _ _ _ _ _ _ _ st' d' hlk hps _ _ _ _ _ =>
    exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFFence _ ag _ _ _ _ st' d' hlk hps => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFDev _ ag st' d' hlk hps => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFRegW _ ag _ _ st' d' hlk hps => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFCtrl _ ag _ st' d' hlk hps => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFInstr _ ag st' d' hlk hps => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFExLoad _ ag _ _ _ _ st' d' hlk hps _ => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFExStore _ ag _ _ _ _ _ _ _ st' d' hlk hps _ _ _ _ _ _ =>
    exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩
  | PFIFetch _ ag _ _ st' d' hlk hps _ => exact ⟨ag, st', d', _, hlk, hps, rfl, rfl, rfl⟩

/-- The step of agent `i` from `c` to `c'` takes kind `k`. -/
def kindOk (c : Wpcfg Pexv6 Efab) (i : Nat) (l : Wlabel) (c' : Wpcfg Pexv6 Efab) (k : SKind) :
    Prop :=
  ∃ (ag : Wpagent Pexv6) (p' : Pexv6) (ws' : Wstate),
    c.pcAgs[i]? = some ag ∧ kindStep k ag.paSt c.pcDev l p' c'.pcDev ∧
    c'.pcImg = c.pcImg ∧ c'.pcAgs = c.pcAgs.set i ⟨p', ws', ag.paProm⟩

theorem kindOfStep (i : Nat) (l : Wlabel) (c c' : Wpcfg Pexv6 Efab)
    (h : wpPfStep pstepEv pclsEv i l c c') : ∃ k, kindOk c i l c' k := by
  obtain ⟨ag, p', d', ws', hlk, hps, himg, hdev, hags⟩ := wpPfStepInv _ _ i l c c' h
  obtain ⟨k, hk⟩ := pstepEvKind _ _ _ _ _ hps
  exact ⟨k, ag, p', ws', hlk, by rw [hdev]; exact hk, himg, hags⟩

/-- One entry of the RUN RECORD: the pre-configuration, the agent, the label, the kind. -/
structure PfRec where
  pre : Wpcfg Pexv6 Efab
  ag : Nat
  lb : Wlabel
  kind : SKind

/-- The step list of a record. -/
def recLabels (r : List PfRec) : List (Nat × Wlabel) := r.map (fun x => (x.ag, x.lb))

/-- **The run record, forward**: from `c` with step-list prefix `st`, the steps of `r` (each a
`pfRunST` step with its facts at ITS prefix, and its kind) lead to `cN`. -/
inductive contR (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) :
    Wpcfg Pexv6 Efab → List (Nat × Wlabel) → List PfRec → Wpcfg Pexv6 Efab → Prop where
  | nil (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) : contR fok c st [] c
  | cons (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) (k : SKind)
      (r : List PfRec) (cN : Wpcfg Pexv6 Efab) :
      wpPfStep pstepEv pclsEv i l c c' → pfStepFacts fok c i l →
      pfLoadFactsT TsoShadow.cohSrc st c i l → kindOk c i l c' k →
      contR fok c' (st ++ [(i, l)]) r cN → contR fok c st (⟨c, i, l, k⟩ :: r) cN

theorem contRSnoc (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {c c1 c2 : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {i : Nat}
    {l : Wlabel} {k : SKind} (h : contR fok c st r c1) (hs : wpPfStep pstepEv pclsEv i l c1 c2)
    (hf : pfStepFacts fok c1 i l) (hfT : pfLoadFactsT TsoShadow.cohSrc (st ++ recLabels r) c1 i l)
    (hk : kindOk c1 i l c2 k) : contR fok c st (r ++ [⟨c1, i, l, k⟩]) c2 := by
  revert hfT
  induction h with
  | nil c st =>
    intro hfT
    exact .cons _ _ _ i l k [] c2 hs hf (by simpa [recLabels] using hfT) hk (.nil _ _)
  | cons c c' st i' l' k' r cN hs' hf' hfT' hk' _ ih =>
    intro hfT
    exact .cons _ _ _ i' l' k' _ _ hs' hf' hfT' hk'
      (ih hs hf hk (by simpa [recLabels, List.append_assoc] using hfT))

/-- A shaped run IS a run record. -/
theorem contROfRun (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {c0 cN : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)}
    (h : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st cN) :
    ∃ r, contR fok c0 [] r cN ∧ recLabels r = st := by
  induction h with
  | nil => exact ⟨[], .nil _ _, rfl⟩
  | snoc c1 c2 st i l _ hs hf hfT ih =>
    obtain ⟨r, hr, hl⟩ := ih
    obtain ⟨k, hk⟩ := kindOfStep i l c1 c2 hs
    exact ⟨r ++ [⟨c1, i, l, k⟩], contRSnoc fok hr hs hf (by simpa [hl] using hfT) hk,
      by simp [recLabels, ← hl]⟩

/-! ## (F7) Observations: `κs` as a FUNCTION of the run record (E-S3) -/

/-- What hart `cpu`'s step at `m` with register file `rs` emits (MachCSL's `hartObsM`, read off
the pf register file). -/
def pfHartObs (cpu : CPU) (m : SailM Unit) (rs : RegFile) : List Obs :=
  match m with
  | .impure (.ok (.regWrite r v)) _ => hartObsW cpu rs r v
  | _ => []

theorem hartObsMEq (cpu : CPU) (m : SailM Unit) (σ : MState) :
    hartObsM cpu m σ = pfHartObs cpu m (σ.regs cpu) := by
  rcases m with _ | ⟨e, k⟩
  · rfl
  · cases e with
    | error _ => rfl
    | ok o => cases o <;> rfl

open Classical in
/-- What a device program's next root-task step emits: its guard's events when the guard answers
faithfully, nothing otherwise (MachCSL `devOpStep .step`/`devBlocked`; every other node is
silent). -/
noncomputable def fdevObs (dv : DevId) (m : DevProg dv) (ds : DevStates) : List Obs :=
  match m with
  | .op (.step f) _ =>
      match f (ds.st dv) with
      | some (s', os) => if devObsOk dv (ds.st dv) s' os then os.map Obs.dev else []
      | none => []
  | _ => []

/-- What UART `u`'s next step emits. -/
noncomputable def uartObs (u : UartId) (F : Efab) : List Obs := fdevObs (.uart u) (efU F u) F.efDev

/-- **The observations of one recorded pf step**, from its pre-configuration and kind: a hart's
own node emits `hartObsM` (the `cur_privilege` crossing; nothing at a parked fence), a UART step
its wire events; the PLIC (wire and gateway) and the disk are silent. -/
noncomputable def pfStepObs (c : Wpcfg Pexv6 Efab) (i : Nat) (k : SKind) : List Obs :=
  match k with
  | .node =>
      match c.pcAgs[i]? with
      | some ⟨.PHart cpu m rs none _, _, _⟩ => pfHartObs cpu m rs
      | _ => []
  | .uart u => uartObs u c.pcDev
  | _ => []

/-- **`pfObsOf`**: the run's observations, a function of its record. -/
noncomputable def pfObsOf (r : List PfRec) : List Obs := r.flatMap (fun x => pfStepObs x.pre x.ag x.kind)

theorem pfObsOfCons (x : PfRec) (r : List PfRec) :
    pfObsOf (x :: r) = pfStepObs x.pre x.ag x.kind ++ pfObsOf r := by
  simp [pfObsOf]

/-! ## (R_mem frame) The memory relation across steps that move no memory field -/

theorem authStep {c c' : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {i : Nat} {l : Wlabel}
    (hs : wpPfStep pstepEv pclsEv i l c c')
    (ha : c.pcLog.map Wmsg.wmTid = (stAuthors st).map some) :
    c'.pcLog.map Wmsg.wmTid = (stAuthors (st ++ [(i, l)])).map some := by
  rw [wpPfStepAuthors _ _ i l c c' hs, ha, stAuthorsSnoc]
  cases lbWrites l <;> simp

theorem viewRelSame {σ σ' : MState} {st : List (Nat × Wlabel)}
    (h : viewRel TsoShadow.cohSrc σ st) (hs : sameRead σ σ') : viewRel TsoShadow.cohSrc σ' st :=
  fun c => hartRelOther σ σ' c _ (h c) (by rw [hs.1]) (by rw [hs.2.1]) (by rw [hs.2.2])

/-- The parked half of `fence.tso` moves no shadow (`ShSt.fenceNoSucc`; not `lbFenceZero`). -/
theorem viewRelPark {σ : MState} {st : List (Nat × Wlabel)} (j : Nat)
    (h : viewRel TsoShadow.cohSrc σ st) :
    viewRel TsoShadow.cohSrc σ (st ++ [(j, .LFence true true false true)]) := by
  intro cpu
  rw [tsoShadowSnoc]
  split
  · refine hartRelCongr (h cpu) ?_ ?_
    · simp [shStepF, shStep, ShSt.fenceNoSucc]
    · simp [shStepF, lbFenceZero]
  · exact h cpu

/-- **The frame row**: a step whose label moves no memory field (and no `itv`) relates any
TsoMem state with the same memory fields and read side. -/
theorem memFrame {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {i : Nat}
    {l : Wlabel} {σ σ' : MState} (hs : wpPfStep pstepEv pclsEv i l c c') (hl : frameLbl l)
    (hin : lbInert l = true ∨ l = .LFence true true false true)
    (hadj : pairAdjacent (st ++ (i, l) :: rest)) (hR : rmem c st σ)
    (hV : viewRel TsoShadow.cohSrc σ st) (hA : c.pcLog.map Wmsg.wmTid = (stAuthors st).map some)
    (hC : ownCoh c) (hmem : σ'.mem = σ.mem) (hlog : σ'.log = σ.log) (hres : σ'.resv = σ.resv)
    (hsr : sameRead σ σ') :
    rmem c' (st ++ [(i, l)]) σ' ∧ viewRel TsoShadow.cohSrc σ' (st ++ [(i, l)]) ∧
      c'.pcLog.map Wmsg.wmTid = (stAuthors (st ++ [(i, l)])).map some ∧ ownCoh c' := by
  refine ⟨(pfFrameRowMem pstepEv pclsEv c c' st rest σ i l hR hs hl hadj).2.2 σ' hmem hlog hres,
    ?_, authStep hs hA, ownCohStep pstepEv pclsEv i l c c' hC hs⟩
  rcases hin with hin | rfl
  · exact viewRelInert _ σ σ' st i l hin hV hsr
  · exact viewRelSame (viewRelPark i hV) hsr

/-! ## The hypotheses W4 is parametric in -/

/-- **W4's parameters** (all but `tso`/`disk` MachCSL-side or run-level facts):
* `tso` — W2 CLOSE's `pfStepTso` (the adopted statement);
* `safe` — **HSafe** (E-S1): every thread of every MachCSL run from `([power], g0)` is
  reducible (W5: `xv6FsAdequacy_closed`'s first conjunct).  It supplies the BUS DECODE the pf
  machine lacks (`devBytes`/`ramBytes` over the whole footprint);
* `cut` — the fetch cut of `pfStepTso`'s hypothesis (3) at every fetch of the run, at a related
  MachCSL state reachable from boot (M1: from `candKfetch` and the pristine kernel text; M2:
  W5d's cut form);
* `fi` — plan item (3): `fiArm` at `fence.i` / the `sfence.vma` marker, along every run from
  `c0` (a fact of the Sail model's event order, owner of the proof OPEN);
* `disk` — **F9's interface**: every disk-PROGRAM step (kind `.disk`) from a related state is
  simulated by MachCSL steps (silent: the disk observes nothing) re-establishing the relation,
  whose virtio part is `DR`. -/
structure Hyps (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (DR : Option (DM Dres) → List Expr → Prop) (g0 : GState) (c0 : Wpcfg Pexv6 Efab) : Prop where
  tso : pfStepTsoStmt fok
  safe : ∀ (n : Nat) (κs : List Obs) (t : List Expr) (g : GState),
    MRun n ([Expr.power], g0) κs (t, g) → ∀ e, e ∈ t → PrimStep.Reducible (e, g)
  cut : ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
    pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → MRun n ([Expr.power], g0) κ (t, g) →
    SimRel DR c st t g →
    ∀ (cpu : CPU) (base : Int) (tvs : List (Nat × BitVec 8)) (c' : Wpcfg Pexv6 Efab),
      wpPfStep pstepEv pclsEv (hartAgent cpu) (.LIFetch base tvs) c c' →
      pfStepFacts fok c (hartAgent cpu) (.LIFetch base tvs) →
      ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
        ifetchOk c.pcImg c.pcLog q base tvs ∧
        ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q
  fi : ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab),
    pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c →
    ∀ (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
      (ib : Ibch) (ws : Wstate) (pr : GSet Nat),
      c.pcAgs[cpu.val]? = some ⟨.PHart cpu (.impure (.ok o) k) rs none ib, ws, pr⟩ →
      (o = .barrier .Barrier_RISCV_i →
         (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) ∧
      (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
         (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false)
  disk : ∀ (st rest : List (Nat × Wlabel)) (c c' : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState)
      (n : Nat) (κ : List Obs) (l : Wlabel),
    pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → MRun n ([Expr.power], g0) κ (t, g) →
    SimRel DR c st t g → wpPfStep pstepEv pclsEv NCPU l c c' → pfStepFacts fok c NCPU l →
    pfLoadFactsT TsoShadow.cohSrc st c NCPU l → kindOk c NCPU l c' .disk →
    pairAdjacent (st ++ (NCPU, l) :: rest) →
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      MRun m (t, g) [] (t', g') ∧ SimRel DR c' (st ++ [(NCPU, l)]) t' g'

/-! ## (F5) The bus decode from HSafe, and what `evStep` moves -/

/-- No device window lies at or above the DRAM bank. -/
theorem devDecodeNone (pa : PAddr) (h : devAddr pa = false) : devDecode pa = none := by
  simp only [devAddr, devBound, decide_eq_false_iff_not, Nat.not_lt] at h
  simp only [devDecode, uartBase, uartSize, plicBase, plicSize, Virtio.base, Virtio.windowSize]
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · omega
  rfl

theorem devReadNone (ds : DevStates) (pa : PAddr) (n : Nat) (h : devAddr pa = false) :
    devRead ds pa n = none := by
  simp only [devRead, devDecodeNone pa h]

theorem devWriteNone (ds : DevStates) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (h : devAddr pa = false) : devWrite ds pa n w = none := by
  simp only [devWrite, devDecodeNone pa h]

/-- The register files after hart `cpu`'s event `o`. -/
def oRegs (cpu : CPU) (o : Outcome Register RegisterType) (σ : MState) : CPU → RegFile :=
  match o with
  | .regWrite r v => (σ.setReg cpu r v).regs
  | _ => σ.regs

theorem oRegsOther (cpu c : CPU) (o : Outcome Register RegisterType) (σ : MState) (h : c ≠ cpu) :
    oRegs cpu o σ c = σ.regs c := by
  cases o <;> simp [oRegs, h]

/-- **What an `evStep` off the device windows moves**: devices and task bookkeeping never; the
register files only at a register write. -/
theorem evStepShape (cpu : CPU) (o : Outcome Register RegisterType) (σ σ' : MState) (v : o.ret)
    (h : evStep cpu o σ v σ')
    (hR : ∀ n va req, o = .memRead n va req → devAddr req.pa = false)
    (hW : ∀ n va req, o = .memWrite n va req → devAddr req.pa = false) :
    σ'.devs = σ.devs ∧ σ'.regs = oRegs cpu o σ ∧ σ'.devrt = σ.devrt := by
  cases o with
  | memRead n va req =>
    have hda := hR n va req rfl
    rcases h with ⟨-, w, ds', hdr, -, -⟩ | ⟨-, -, -, -, -, -, -, -, rfl⟩ |
        ⟨-, -, -, -, -, -, -, -, -, rfl⟩ | ⟨-, -, -, -, -, -, rfl⟩
    · rw [devReadNone _ _ _ hda] at hdr; cases hdr
    all_goals exact ⟨rfl, rfl, rfl⟩
  | memWrite n va req =>
    have hda := hW n va req rfl
    rcases h with ⟨-, w, ds', -, hdw, -, -⟩ | ⟨-, w, -, -, -, rfl⟩
    · rw [devWriteNone _ _ _ _ hda] at hdw; cases hdw
    · exact ⟨rfl, rfl, rfl⟩
  | regRead r => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | regWrite r v => subst h; exact ⟨rfl, rfl, rfl⟩
  | readRam => exact h.elim
  | writeRam => exact h.elim
  | getCycleCount => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | _ => subst h; exact ⟨rfl, rfl, rfl⟩

/-- Under `rmem` and the adjacency of the step being taken, no other hart reserves anything. -/
theorem notOthers {c : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {σ : MState} {cpu : CPU}
    {l : Wlabel} (hR : rmem c st σ) (hadj : pairAdjacent (st ++ (hartAgent cpu, l) :: rest)) :
    ∀ pa n, ¬ othersReserve σ.resv cpu pa n := by
  rintro pa n ⟨c', hne, r, hr, -⟩
  have hn := resvOthersNone c st rest σ (hartAgent cpu) l hR hadj c'
    (fun h => hne (Fin.ext h))
  rw [hn] at hr
  cases hr

/-- **HSafe's bus decode, RAM side** (E-S1/E-M4): a reducible hart at a memory node off the
device windows, with no foreign reservation, has a DRAM footprint. -/
theorem ramOfSafe {g : GState} {cpu : CPU} {o : Outcome Register RegisterType}
    {k : o.ret → SailM Unit} (hred : PrimStep.Reducible (Expr.hart 0 cpu (.impure (.ok o) k), g))
    (hlive : threadLive g 0) (hno : ∀ pa n, ¬ othersReserve g.m.resv cpu pa n) :
    (∀ n va req, o = .memRead n va req → devAddr req.pa = false → ramBytes req.pa n) ∧
    (∀ n va req, o = .memWrite n va req → devAddr req.pa = false → ramBytes req.pa n) := by
  obtain ⟨obs, e', g', efs, hs⟩ := hred
  rcases (primStep_hart_inv hs).2 with ⟨-, -, m', σ', -, hh, -⟩ | ⟨hd, -⟩
  · refine ⟨fun n va req ho hda => ?_, fun n va req ho hda => ?_⟩
    · subst ho
      rcases hh with ⟨v, -, hev⟩ | ⟨⟨-, hor, -⟩, -⟩
      · rcases hev with ⟨-, w, ds', hdr, -, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
        · rw [devReadNone _ _ _ hda] at hdr; cases hdr
        all_goals exact hb
      · exact absurd hor (hno _ _)
    · subst ho
      rcases hh with ⟨v, -, hev⟩ | ⟨⟨hor, -⟩, -⟩
      · rcases hev with ⟨-, w, ds', -, hdw, -, -⟩ | ⟨hb, -⟩
        · rw [devWriteNone _ _ _ _ hda] at hdw; cases hdw
        · exact hb
      · exact absurd hor (hno _ _)
  · exact absurd hlive hd

/-- A DRAM byte is no device address. -/
theorem ramNotDev {pa : PAddr} {n : Nat} (h : ramBytes pa n) (hda : devAddr pa = true) :
    devBytes pa n := by
  intro j hj
  have := ramBytes_head h (by omega)
  simp only [inRam, ramBase] at this
  simp only [devAddr, devBound, decide_eq_true_eq] at hda
  omega

/-- **HSafe's bus decode, device side**: a reducible hart at a memory node whose start address
is a device address, with no foreign reservation, has a device footprint. -/
theorem devOfSafe {g : GState} {cpu : CPU} {o : Outcome Register RegisterType}
    {k : o.ret → SailM Unit} (hred : PrimStep.Reducible (Expr.hart 0 cpu (.impure (.ok o) k), g))
    (hlive : threadLive g 0) (hno : ∀ pa n, ¬ othersReserve g.m.resv cpu pa n) :
    (∀ n va req, o = .memRead n va req → devAddr req.pa = true → devBytes req.pa n) ∧
    (∀ n va req, o = .memWrite n va req → devAddr req.pa = true → devBytes req.pa n) := by
  obtain ⟨obs, e', g', efs, hs⟩ := hred
  rcases (primStep_hart_inv hs).2 with ⟨-, -, m', σ', -, hh, -⟩ | ⟨hd, -⟩
  · refine ⟨fun n va req ho hda => ?_, fun n va req ho hda => ?_⟩
    · subst ho
      rcases hh with ⟨v, -, hev⟩ | ⟨⟨-, hor, -⟩, -⟩
      · rcases hev with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
        · exact hb
        all_goals exact ramNotDev hb hda
      · exact absurd hor (hno _ _)
    · subst ho
      rcases hh with ⟨v, -, hev⟩ | ⟨⟨hor, -⟩, -⟩
      · rcases hev with ⟨hb, -⟩ | ⟨hb, -⟩
        · exact hb
        · exact ramNotDev hb hda
      · exact absurd hor (hno _ _)
  · exact absurd hlive hd

/-! ## (F4/F5) The hart rows -/

theorem obsNode {c : Wpcfg Pexv6 Efab} {cpu : CPU} {m : SailM Unit} {rs : RegFile} {ib : Ibch}
    {ws : Wstate} {pr : GSet Nat}
    (h : c.pcAgs[cpu.val]? = some ⟨.PHart cpu m rs none ib, ws, pr⟩) :
    pfStepObs c cpu.val .node = pfHartObs cpu m rs := by
  simp [pfStepObs, h]

/-- One step of hart `cpu`'s thread, observed as the record says. -/
theorem hartRun {c : Wpcfg Pexv6 Efab} {t : List Expr} {g : GState} {H : CPU → SailM Unit}
    {vs : List Expr} (ht : t = poolOf H c.pcDev vs) (hgen : g.gen = 0) (hpow : g.pow = true)
    (cpu : CPU) {ib : Ibch} {ws : Wstate} {pr : GSet Nat}
    (hlk : c.pcAgs[cpu.val]? = some ⟨.PHart cpu (H cpu) (g.m.regs cpu) none ib, ws, pr⟩)
    {m' : SailM Unit} {σ' : MState} (hh : hartStep cpu (H cpu) g.m m' σ') :
    MRun 1 (t, g) (pfStepObs c cpu.val .node)
      (t.set (cpu.val + 1) (.hart 0 cpu m'), { g with m := σ' }) := by
  have hs := primStep_hart_live (gen := 0) (⟨hpow, hgen⟩ : threadLive g 0) hh
  have := mrunOne (t := t) (j := cpu.val + 1) (by rw [ht]; exact poolHart H c.pcDev vs cpu) hs
  rw [hartObsMEq, ← obsNode hlk] at this
  simpa using this

theorem poolOfProg (H : CPU → SailM Unit) (F F' : Efab) (vs : List Expr) (h0 : F'.efU0 = F.efU0)
    (h1 : F'.efU1 = F.efU1) (hp : F'.efPlic = F.efPlic) : poolOf H F' vs = poolOf H F vs := by
  simp only [poolOf, h0, h1, hp]

theorem updHSelf (H : CPU → SailM Unit) (cpu : CPU) : updH H cpu (H cpu) = H := by
  funext c
  simp only [updH]
  split
  · subst c; rfl
  · rfl

theorem lbInertErw (w : ErwKind) : lbInert (erwLabel w) = true ∧ frameLbl (erwLabel w) := by
  rcases erwLabelCases w with h | ⟨rd, srcs, h⟩ | ⟨srcs, h⟩ <;> rw [h] <;> exact ⟨rfl, trivial⟩

/-- **THE HART ROWS** (F4 + F5; census table B6): a hart's own node step is 0 MachCSL steps (the
parked-fence fire, the lost-SC retry) or exactly 1 `primStep` of thread `cpu + 1`: the boundary
(`hartStep .pure`), the silent nodes and register reads/writes (`σ' = σ` / `setReg`), MMIO
(`devRead`/`devWrite`, the footprint from HSafe), and the RAM/fence/announce nodes through
`pfStepTso`. -/
theorem simNode {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {DR : Option (DM Dres) → List Expr → Prop} {g0 : GState} {c0 : Wpcfg Pexv6 Efab}
    (hH : Hyps fok DR g0 c0) {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)}
    {t : List Expr} {g : GState} {n : Nat} {κ : List Obs} {i : Nat} {l : Wlabel}
    (hR : SimRel DR c st t g) (hreach : MRun n ([Expr.power], g0) κ (t, g))
    (hrun : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c)
    (hs : wpPfStep pstepEv pclsEv i l c c') (hf : pfStepFacts fok c i l)
    (hfT : pfLoadFactsT TsoShadow.cohSrc st c i l) (hk : kindOk c i l c' .node)
    (hadj : pairAdjacent (st ++ (i, l) :: rest))
    (hex : ∀ aq base tvs asrc, l = .LExLoad aq base tvs asrc →
      exclOkTs c.pcLog i base (tvs.map Prod.fst) (c.pcLog.length + 1)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      m ≤ 1 ∧ MRun m (t, g) (pfStepObs c i .node) (t', g') ∧ SimRel DR c' (st ++ [(i, l)]) t' g' := by
  have hR0 := hR
  obtain ⟨hgen, hpow, ⟨H, vs, dp, dws, dpr, ht, hlen, hharts, hdisk, hDR⟩, hdev, hmem, hview,
    hauth, hcoh⟩ := hR
  obtain ⟨ag, p', ws', hlk, hks, himg, hags⟩ := hk
  -- the agent is a hart
  have hi : i < NCPU := by
    rcases Nat.lt_or_ge i NCPU with h | h
    · exact h
    · exfalso
      rcases Nat.eq_or_lt_of_le h with h | h
      · subst h
        rw [hdisk] at hlk
        simp only [Option.some.injEq] at hlk
        subst hlk
        cases p' <;> exact hks.elim
      · rw [List.getElem?_eq_none (by omega)] at hlk
        cases hlk
  obtain ⟨cpu, rfl⟩ : ∃ cpu : CPU, cpu.val = i := ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨fn, ib, ws, pr, hlkc, hfn⟩ := hharts cpu
  rw [hlkc] at hlk
  simp only [Option.some.injEq] at hlk
  subst hlk
  cases p' with
  | PDisk _ => exact hks.elim
  | PHart cpu' m' rs' fn' ib' =>
  obtain ⟨hcc, ors, oib, obar, hrs, hib, hn, hd⟩ := hks
  subst cpu' hrs hib
  have hlive : threadLive g 0 := ⟨hpow, hgen⟩
  have hprog : c'.pcDev.efU0 = c.pcDev.efU0 ∧ c'.pcDev.efU1 = c.pcDev.efU1 ∧
      c'.pcDev.efPlic = c.pcDev.efPlic :=
    ⟨by rw [hd], by rw [hd], by rw [hd]⟩
  -- THE POST-STATE: any hart step that re-establishes the hart's entry, registers, devices and
  -- `R_mem` re-establishes the relation
  have post : ∀ (m1 : SailM Unit) (fn1 : Option (Bool × Bool × Bool × Bool)) (σ' : MState)
      (nn : Nat),
      m' = m1 → nn ≤ 1 → fnOk fn' → σ'.regs cpu = ors.getD (g.m.regs cpu) →
      (∀ c'', c'' ≠ cpu → σ'.regs c'' = g.m.regs c'') → c'.pcDev.efDev = σ'.devs →
      rmem c' (st ++ [(cpu.val, l)]) σ' → viewRel TsoShadow.cohSrc σ' (st ++ [(cpu.val, l)]) →
      MRun nn (t, g) (pfStepObs c cpu.val .node)
        (t.set (cpu.val + 1) (.hart 0 cpu m1), { g with m := σ' }) →
      ∃ (m : Nat) (t' : List Expr) (g' : GState),
        m ≤ 1 ∧ MRun m (t, g) (pfStepObs c cpu.val .node) (t', g') ∧
        SimRel DR c' (st ++ [(cpu.val, l)]) t' g' := by
    intro m1 _ σ' nn hm1 hnn hfn' hrc hro hdv hmem' hview' hrun'
    subst hm1
    refine ⟨nn, _, _, hnn, hrun', hgen, hpow, ⟨updH H cpu m', vs, dp, dws, dpr, ?_, ?_, ?_, ?_, hDR⟩,
      hdv, hmem', hview', authStep hs hauth, ownCohStep pstepEv pclsEv _ _ c c' hcoh hs⟩
    · rw [ht, poolHartSet]
      exact (poolOfProg _ _ _ _ hprog.1 hprog.2.1 hprog.2.2).symm
    · rw [hags, List.length_set, hlen]
    · intro c''
      by_cases hc : c'' = cpu
      · subst hc
        refine ⟨fn', oib.getD ib, ws', pr, ?_, hfn'⟩
        rw [hags, List.getElem?_set_self (by rw [hlen]; omega)]
        simp [updH, hrc]
      · obtain ⟨fn2, ib2, ws2, pr2, hl2, hf2⟩ := hharts c''
        refine ⟨fn2, ib2, ws2, pr2, ?_, hf2⟩
        have hne : cpu.val ≠ c''.val := fun h => hc (Fin.ext h).symm
        rw [hags, List.getElem?_set_ne hne, hl2]
        simp [updH, hc, hro c'' hc]
    · rw [hags, List.getElem?_set_ne (by omega)]
      exact hdisk
  cases fn with
  | some x =>
    -- THE PARKED-FENCE FIRE: 0 MachCSL steps
    have hx := hfn x rfl
    subst hx
    obtain ⟨rfl, rfl, rfl, rfl, hd'', -, -⟩ := hn
    have hobs : pfStepObs c cpu.val .node = [] := by simp [pfStepObs, hlkc]
    obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := g.m) hs trivial (Or.inr rfl) hadj hmem hview hauth
      hcoh rfl rfl rfl (sameReadRefl _)
    refine post (H cpu) none g.m 0 rfl (by omega) (fun _ h => by cases h) rfl (fun _ _ => rfl)
      (by rw [hd'', hdev]) hm1 hv1 ?_
    rw [hobs, ht, poolHartSet, updHSelf]
    exact mrunRefl _
  | none =>
  -- the hart's own node
  generalize hm : H cpu = mm at hn hlkc
  cases mm with
  | pure a =>
    -- THE BOUNDARY
    obtain ⟨tick, rfl, rfl, rfl, rfl, hd'', -, -⟩ := hn
    obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := g.m) hs trivial (Or.inl rfl) hadj hmem hview hauth
      hcoh rfl rfl rfl (sameReadRefl _)
    exact post _ none g.m 1 rfl (by omega) (fun _ h => by cases h) rfl (fun _ _ => rfl) (by rw [hd'', hdev])
      hm1 hv1 (hartRun ht hgen hpow cpu (by rw [hm]; exact hlkc)
        (by rw [hm]; exact ⟨tick, rfl, rfl⟩))
  | impure e k =>
  cases e with
  | error _ => exact hn.elim
  | ok o =>
  -- the four row shapes
  have silent : ∀ (v : o.ret), evStep cpu o g.m v g.m → l = .LSilent → m' = k v → ors = none →
      fn' = none → c'.pcDev.efDev = c.pcDev.efDev →
      ∃ (m : Nat) (t' : List Expr) (g' : GState),
        m ≤ 1 ∧ MRun m (t, g) (pfStepObs c cpu.val .node) (t', g') ∧
        SimRel DR c' (st ++ [(cpu.val, l)]) t' g' := by
    intro v hev hl hm' hors hfn' hd''
    subst hl hm' hors hfn'
    obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := g.m) hs trivial (Or.inl rfl) hadj hmem hview hauth
      hcoh rfl rfl rfl (sameReadRefl _)
    exact post _ none g.m 1 rfl (by omega) (fun _ h => by cases h) rfl (fun _ _ => rfl) (by rw [hd'', hdev])
      hm1 hv1 (hartRun ht hgen hpow cpu (by rw [hm]; exact hlkc)
        (by rw [hm]; exact Or.inl ⟨v, rfl, hev⟩))
  have mmio : ∀ (v : o.ret),
      (∀ n va req, o = .memRead n va req → devAddr req.pa = true) →
      (∀ n va req, o = .memWrite n va req → devAddr req.pa = true) →
      ((∀ n va req, o = .memRead n va req → devBytes req.pa n) →
        (∀ n va req, o = .memWrite n va req → devBytes req.pa n) →
        evStep cpu o g.m v { g.m with devs := c'.pcDev.efDev }) →
      lbInert l = true → frameLbl l → m' = k v → ors = none → fn' = none →
      ∃ (m : Nat) (t' : List Expr) (g' : GState),
        m ≤ 1 ∧ MRun m (t, g) (pfStepObs c cpu.val .node) (t', g') ∧
        SimRel DR c' (st ++ [(cpu.val, l)]) t' g' := by
    intro v hdaR hdaW hev hin hfr hm' hors hfn'
    subst hm' hors hfn'
    have hred := hH.safe n κ t g hreach _
      (List.mem_of_getElem? (by rw [ht]; exact poolHart H c.pcDev vs cpu))
    rw [hm] at hred
    obtain ⟨hdbR, hdbW⟩ := devOfSafe hred hlive (notOthers hmem hadj)
    have hev' := hev (fun n va req ho => hdbR n va req ho (hdaR n va req ho))
      (fun n va req ho => hdbW n va req ho (hdaW n va req ho))
    obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := { g.m with devs := c'.pcDev.efDev }) hs hfr
      (Or.inl hin) hadj hmem hview hauth hcoh rfl rfl rfl (sameReadDevs _ _)
    exact post _ none { g.m with devs := c'.pcDev.efDev } 1 rfl (by omega) (fun _ h => by cases h) rfl
      (fun _ _ => rfl) rfl hm1 hv1
      (hartRun ht hgen hpow cpu (by rw [hm]; exact hlkc)
        (by rw [hm]; exact Or.inl ⟨v, rfl, hev'⟩))
  have tso : l ≠ .LSilent → (∀ kd ba bs, l ≠ .LDev kd ba bs) →
      c'.pcDev.efDev = c.pcDev.efDev → fnOk fn' →
      (∀ n va req, o = .memRead n va req → devAddr req.pa = false) →
      (∀ n va req, o = .memWrite n va req → devAddr req.pa = false) →
      ors.getD (g.m.regs cpu) = oRegs cpu o g.m cpu →
      ∃ (m : Nat) (t' : List Expr) (g' : GState),
        m ≤ 1 ∧ MRun m (t, g) (pfStepObs c cpu.val .node) (t', g') ∧
        SimRel DR c' (st ++ [(cpu.val, l)]) t' g' := by
    intro hl1 hl2 hd'' hfn' hdaR hdaW hors
    have hred := hH.safe n κ t g hreach _
      (List.mem_of_getElem? (by rw [ht]; exact poolHart H c.pcDev vs cpu))
    rw [hm] at hred
    obtain ⟨hrbR, hrbW⟩ := ramOfSafe hred hlive (notOthers hmem hadj)
    obtain ⟨hfi1, hfi2⟩ := hH.fi st c hrun cpu o k (g.m.regs cpu) ib ws pr hlkc
    have hps : pstepEv (.PHart cpu (.impure (.ok o) k) (g.m.regs cpu) none ib) c.pcDev l
        (.PHart cpu m' (ors.getD (g.m.regs cpu)) fn' (oib.getD ib)) c'.pcDev :=
      ⟨rfl, ors, oib, obar, rfl, rfl, Or.inl ⟨hn, hd⟩⟩
    obtain ⟨v, σ', hev, ⟨rs'', fn'', ib'', hp'⟩, hmem', hview'⟩ :=
      hH.tso c c' st g.m cpu o k (g.m.regs cpu) none ib l _ c'.pcDev rest hps hs hadj ⟨hf, hfT⟩
        (fun n va req ho => hrbR n va req ho (hdaR n va req ho))
        (fun n va req ho => hrbW n va req ho (hdaW n va req ho)) hmem hview hauth
        (fun base tvs hl => by subst hl; exact hH.cut st c t g n κ hrun hreach hR0 cpu base tvs c' hs hf)
        (fun aq base tvs asrc hl => ⟨hcoh, hex aq base tvs asrc hl⟩) rfl hl1 hl2 hfi1 hfi2
    simp only [Pexv6.PHart.injEq] at hp'
    obtain ⟨-, hmk, -, -, -⟩ := hp'
    obtain ⟨hdv, hrg, -⟩ := evStepShape cpu o g.m σ' v hev hdaR hdaW
    exact post (k v) fn' σ' 1 hmk (by omega) hfn' (by rw [hrg, hors]) (fun c'' hc => by rw [hrg, oRegsOther _ _ _ _ hc])
      (by rw [hd'', hdev, hdv]) hmem' hview'
      (hartRun ht hgen hpow cpu (by rw [hm]; exact hlkc) (by rw [hm]; exact Or.inl ⟨v, rfl, hev⟩))
  -- the per-event dispatch
  cases o with
  | regRead r =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent (g.m.regs cpu r) ⟨rfl, rfl⟩ hl hm' hors hfn' (by rw [hd''])
  | regWrite r v =>
    obtain ⟨hl, rfl, rfl, rfl, hd'', -, -⟩ := hn
    obtain ⟨hin, hfr⟩ := lbInertErw (erwOf (depsOfIb ib.ibBits) ib.ibRds r)
    rw [← hl] at hin hfr
    obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := g.m.setReg cpu r v) hs hfr (Or.inl hin) hadj hmem
      hview hauth hcoh rfl rfl rfl (sameReadSetReg _ _ _ _)
    exact post _ none _ 1 rfl (by omega) (fun _ h => by cases h) (by simp)
      (fun c'' hc => by simp [hc]) (by rw [hd'', hdev]) hm1 hv1
      (hartRun ht hgen hpow cpu (by rw [hm]; exact hlkc)
        (by rw [hm]; exact Or.inl ⟨(), rfl, rfl⟩))
  | memRead nb va req =>
    have hn' : pnodeStep (.impure (.ok (.memRead nb va req)) k) (g.m.regs cpu) ib c.pcDev.efDev l m'
      ors fn' c'.pcDev.efDev oib obar := hn
    clear hn
    simp only [pnodeStep] at hn'
    split at hn'
    · rename_i hda
      obtain ⟨w, hdr, hl, hm', hors, hfn', -, -⟩ := hn'
      refine mmio (.Ok (w, none)) (fun _ _ _ ho => by cases ho; exact hda)
        (fun _ _ _ ho => by cases ho) (fun hdb _ => Or.inl ⟨hdb nb va req rfl, w, c'.pcDev.efDev,
          by rw [← hdev]; exact hdr, rfl, rfl⟩) (by rw [hl]; rfl) (by rw [hl]; trivial) hm' hors hfn'
    · rename_i hda
      have hda' : devAddr req.pa = false := by simpa using hda
      rcases hn' with ⟨-, w, tvs, -, -, hl, -, hors, hfn', hd'', -, -⟩ |
          ⟨-, ⟨-, w, tvs, -, -, hl, -, hors, hfn', hd'', -, -⟩ |
              ⟨-, w, tvs, -, -, hl, -, hors, hfn', hd'', -, -⟩⟩ <;>
        exact tso (by rw [hl]; nofun) (fun _ _ _ => by rw [hl]; nofun) hd''
          (by rw [hfn']; exact fun _ h => by cases h) (fun _ _ _ ho => by cases ho; exact hda')
          (fun _ _ _ ho => by cases ho)
          (by rw [hors]; rfl)
  | memWrite nb va req =>
    have hn' : pnodeStep (.impure (.ok (.memWrite nb va req)) k) (g.m.regs cpu) ib c.pcDev.efDev l m'
      ors fn' c'.pcDev.efDev oib obar := hn
    clear hn
    simp only [pnodeStep] at hn'
    split at hn'
    · rename_i hda
      split at hn'
      · rename_i v hv
        obtain ⟨hdw, hl, hm', hors, hfn', -, -⟩ := hn'
        exact mmio (.Ok (some true)) (fun _ _ _ ho => by cases ho) (fun _ _ _ ho => by cases ho; exact hda)
          (fun _ hdb => Or.inl ⟨hdb nb va req rfl, v, c'.pcDev.efDev, hv,
            by rw [← hdev]; exact hdw, rfl, rfl⟩) (by rw [hl]; rfl) (by rw [hl]; trivial) hm' hors hfn'
      · exact hn'.elim
    · rename_i hda
      have hda' : devAddr req.pa = false := by simpa using hda
      split at hn'
      · rename_i v hv
        obtain ⟨-, hn'⟩ := hn'
        rcases hn' with ⟨-, hl, -, hors, hfn', hd'', -, -⟩ |
            ⟨-, ⟨hl, -, hors, hfn', hd'', -, -⟩ | ⟨hl, hm', hors, hfn', hd'', -, -⟩⟩
        · exact tso (by rw [hl]; nofun) (fun _ _ _ => by rw [hl]; nofun) hd''
            (by rw [hfn']; exact fun _ h => by cases h) (fun _ _ _ ho => by cases ho)
            (fun _ _ _ ho => by cases ho; exact hda')
            (by rw [hors]; rfl)
        · exact tso (by rw [hl]; nofun) (fun _ _ _ => by rw [hl]; nofun) hd''
            (by rw [hfn']; exact fun _ h => by cases h) (fun _ _ _ ho => by cases ho)
            (fun _ _ _ ho => by cases ho; exact hda')
            (by rw [hors]; rfl)
        · -- THE LOST-SC RETRY: 0 MachCSL steps
          subst hl hm' hors hfn'
          have hobs : pfStepObs c cpu.val .node = [] := by rw [obsNode hlkc]; rfl
          obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := g.m) hs trivial (Or.inl rfl) hadj hmem hview
            hauth hcoh rfl rfl rfl (sameReadRefl _)
          refine post (H cpu) none g.m 0 hm.symm (by omega) (fun _ h => by cases h) rfl (fun _ _ => rfl)
            (by rw [hd'', hdev]) hm1 hv1 ?_
          rw [hobs, ht, poolHartSet, updHSelf]
          exact mrunRefl _
      · exact hn'.elim
  | readRam => exact hn.elim
  | writeRam => exact hn.elim
  | barrier b =>
    obtain ⟨hl, -, hors, hfn', hd'', -, -⟩ := hn
    obtain ⟨pr', pw', sr', sw', hb⟩ := ebarLabelFence b
    exact tso (by rw [hl, hb]; nofun) (fun _ _ _ => by rw [hl, hb]; nofun) hd''
      (by rw [hfn']; cases b <;> simp [fnOk, ebarPark]) (fun _ _ _ ho => by cases ho)
      (fun _ _ _ ho => by cases ho) (by rw [hors]; rfl)
  | instrAnnounce nb w =>
    obtain ⟨hl, -, hors, hfn', hd'', -, -⟩ := hn
    have hl1 : l ≠ .LSilent ∧ ∀ kd ba bs, l ≠ .LDev kd ba bs := by
      rcases annLabelCases nb w with h | h <;> rw [hl, h]
      · exact ⟨nofun, fun _ _ _ => nofun⟩
      · obtain ⟨pr', pw', sr', sw', hb⟩ := ebarLabelFence .Barrier_RISCV_i
        rw [hb]; exact ⟨nofun, fun _ _ _ => nofun⟩
    exact tso hl1.1 hl1.2 hd'' (by rw [hfn']; exact fun _ h => by cases h)
      (fun _ _ _ ho => by cases ho) (fun _ _ _ ho => by cases ho) (by rw [hors]; rfl)
  | branchAnnounce _ _ =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | cacheOp _ =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | tlbi _ =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | translationStart _ =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | translationEnd _ =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | takeException _ =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | returnException _ =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | cycleCount =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | message _ =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent () rfl hl hm' hors hfn' (by rw [hd''])
  | getCycleCount =>
    obtain ⟨hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent (0 : Nat) ⟨rfl, rfl⟩ hl hm' hors hfn' (by rw [hd''])
  | choose _ =>
    obtain ⟨ch, hl, hm', hors, hfn', hd'', -, -⟩ := hn
    exact silent ch rfl hl hm' hors hfn' (by rw [hd''])

/-! ## (F6) The device rows: `fdevStep` ↔ `devStep`, `pstepPlic` ↔ `setPin` -/

/-- **One root-task device step** (`WeakEvInst.fdevStep`, "`wdevStep` at the root task,
verbatim") IS MachCSL's `devStep` at the root task, observed by `fdevObs`, forking nothing. -/
theorem devStepOfFdev (gen : Nat) (dv : DevId) (m m' : DevProg dv) (ds ds' : DevStates)
    (σ : MState) (hds : σ.devs = ds) (h : fdevStep dv m ds m' ds') :
    devStep gen dv rootTask m σ (fdevObs dv m ds) m' { σ with devs := ds' } [] := by
  subst hds
  cases m with
  | pure a =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | op o k =>
    cases o with
    | step f =>
      rcases h with ⟨s', os, hf, hok, rfl, rfl⟩ | ⟨hbl, rfl, rfl⟩
      · have hobs : fdevObs dv (.op (.step f) k) σ.devs = os.map Obs.dev := by
          simp [fdevObs, hf, hok]
        rw [hobs]
        exact Or.inl ⟨(), rfl, s', os, hf, hok, rfl, rfl, rfl⟩
      · have hobs : fdevObs dv (.op (.step f) k) σ.devs = [] := by
          cases hf : f (σ.devs.st dv) with
          | none => simp [fdevObs, hf]
          | some p =>
            obtain ⟨s', os⟩ := p
            simp [fdevObs, hf, hbl s' os hf]
        rw [hobs]
        exact Or.inr ⟨hbl, rfl, rfl, rfl, rfl⟩
    | get =>
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨σ.devs.st dv, rfl, rfl, rfl, rfl, rfl⟩
    | choose =>
      obtain ⟨n, rfl, rfl⟩ := h
      exact Or.inl ⟨n, rfl, rfl, rfl, rfl⟩
    | sample src =>
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨devLevel σ.devs src, rfl, rfl, rfl, rfl, rfl⟩
    | dmaRead _ _ => exact h.elim
    | dmaWrite _ _ _ _ => exact h.elim
    | setPin _ _ _ => exact h.elim
    | fork _ => exact h.elim
    | join _ => exact h.elim

/-- The PLIC observes nothing (`devSilent_plic`). -/
theorem fdevObsPlic (m : DevProg .plic) (ds : DevStates) : fdevObs .plic m ds = [] := by
  unfold fdevObs
  split
  · split
    · rename_i os _
      split
      · rename_i hok
        have : os = [] := hok
        simp [this]
      · rfl
    · rfl
  · rfl

/-- The disk agent is agent `NCPU`. -/
theorem diskAgentIdx {DR : Option (DM Dres) → List Expr → Prop} {c : Wpcfg Pexv6 Efab}
    {st : List (Nat × Wlabel)} {t : List Expr} {g : GState} (hR : SimRel DR c st t g) {i : Nat}
    {ag : Wpagent Pexv6} (hlk : c.pcAgs[i]? = some ag) {dp : Option (DM Dres)}
    (hp : ag.paSt = .PDisk dp) : i = NCPU := by
  obtain ⟨-, -, ⟨H, vs, dp', dws, dpr, -, hlen, hharts, -, -⟩, -⟩ := hR
  rcases Nat.lt_or_ge i NCPU with h | h
  · obtain ⟨fn, ib, ws, pr, hl, -⟩ := hharts ⟨i, h⟩
    have hl' : c.pcAgs[i]? = _ := hl
    rw [hl'] at hlk
    simp only [Option.some.injEq] at hlk
    subst hlk
    cases hp
  · rcases Nat.eq_or_lt_of_le h with h | h
    · exact h.symm
    · rw [List.getElem?_eq_none (by omega)] at hlk
      cases hlk

/-- **The UART/PLIC-gateway rows** (census C1/C2): the disk agent's `pdiskUart` step is ONE
`devStep` of the device's own thread (D51's one-row coupling only removes interleavings). -/
theorem simDev {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {DR : Option (DM Dres) → List Expr → Prop} {c c' : Wpcfg Pexv6 Efab}
    {st rest : List (Nat × Wlabel)} {t : List Expr} {g : GState} {i : Nat} {l : Wlabel}
    {k : SKind} (hR : SimRel DR c st t g) (hs : wpPfStep pstepEv pclsEv i l c c')
    (hk : kindOk c i l c' k) (hkd : k ≠ .node ∧ k ≠ .wire ∧ k ≠ .disk)
    (hadj : pairAdjacent (st ++ (i, l) :: rest)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      m ≤ 1 ∧ MRun m (t, g) (pfStepObs c i k) (t', g') ∧ SimRel DR c' (st ++ [(i, l)]) t' g' := by
  have hR0 := hR
  obtain ⟨hgen, hpow, ⟨H, vs, dp, dws, dpr, ht, hlen, hharts, hdisk, hDR⟩, hdev, hmem, hview,
    hauth, hcoh⟩ := hR
  obtain ⟨ag, p', ws', hlk, hks, himg, hags⟩ := hk
  obtain ⟨hk1, hk2, hk3⟩ := hkd
  -- the stepping agent is the disk agent
  obtain ⟨st0, ws0, pr0⟩ := ag
  cases st0 with
  | PHart _ _ _ _ _ => cases k <;> first | exact absurd rfl hk1 | exact absurd rfl hk2 | (cases p' <;> exact hks.elim)
  | PDisk dp0 =>
  have hi := diskAgentIdx hR0 hlk rfl
  subst hi
  rw [hdisk] at hlk
  simp only [Option.some.injEq, Wpagent.mk.injEq, Pexv6.PDisk.injEq] at hlk
  obtain ⟨rfl, rfl, rfl⟩ := hlk
  cases p' with
  | PHart _ _ _ _ _ => cases k <;> exact hks.elim
  | PDisk dp' =>
  have hlive : threadLive g 0 := ⟨hpow, hgen⟩
  -- the frame part, for any device move
  have frame : ∀ ds' : DevStates,
      rmem c' (st ++ [(NCPU, l)]) { g.m with devs := ds' } ∧
      viewRel TsoShadow.cohSrc { g.m with devs := ds' } (st ++ [(NCPU, l)]) ∧
      c'.pcLog.map Wmsg.wmTid = (stAuthors (st ++ [(NCPU, l)])).map some ∧ ownCoh c' := by
    intro ds'
    have hl : l = .LDev .dev 0 [] := by
      cases k
      · exact absurd rfl hk1
      · exact absurd rfl hk2
      · exact hks.2.1
      · exact hks.2.1
      · exact absurd rfl hk3
    subst hl
    exact memFrame hs trivial (Or.inl rfl) hadj hmem hview hauth hcoh rfl rfl rfl (sameReadDevs _ _)
  have hags' : c'.pcAgs[NCPU]? = some ⟨.PDisk dp, ws', dpr⟩ ∧
      ∀ cpu : CPU, c'.pcAgs[cpu.val]? = c.pcAgs[cpu.val]? := by
    refine ⟨?_, fun cpu => ?_⟩
    · have : dp' = dp := by
        cases k
        · exact absurd rfl hk1
        · exact absurd rfl hk2
        · exact hks.1
        · exact hks.1
        · exact absurd rfl hk3
      rw [hags, List.getElem?_set_self (by rw [hlen]; omega), this]
    · rw [hags, List.getElem?_set_ne (by have := cpu.isLt; omega)]
  cases k with
  | node => exact absurd rfl hk1
  | wire => exact absurd rfl hk2
  | disk => exact absurd rfl hk3
  | uart u =>
    obtain ⟨-, -, m', ds', hfd, hd'⟩ := hks
    have hds := devStepOfFdev 0 (.uart u) (efU c.pcDev u) m' c.pcDev.efDev ds' g.m hdev.symm hfd
    have hst := primStep_dev_live (gen := 0) hlive hds
    have hrun := mrunOne (t := t) (j := uartThr u) (by rw [ht]; exact poolUart H c.pcDev vs u) hst
    obtain ⟨hm1, hv1, ha1, hc1⟩ := frame ds'
    refine ⟨1, t.set (uartThr u) (.dev 0 (.uart u) rootTask m'), { g with m := { g.m with devs := ds' } },
      Nat.le_refl _, by simpa [pfStepObs, uartObs] using hrun, hgen, hpow,
      ⟨H, vs, dp, ws', dpr, ?_, by rw [hags, List.length_set, hlen], fun cpu => ?_, hags'.1, hDR⟩,
      ?_, hm1, hv1, ha1, hc1⟩
    · rw [ht, poolUartSet H c.pcDev vs u m' ds', hd']
    · rw [hags'.2 cpu]; exact hharts cpu
    · rw [hd']; cases u <;> rfl
  | gate =>
    obtain ⟨-, -, m', ds', hfd, hd'⟩ := hks
    have hds := devStepOfFdev 0 .plic c.pcDev.efPlic m' c.pcDev.efDev ds' g.m hdev.symm hfd
    rw [fdevObsPlic] at hds
    have hst := primStep_dev_live (gen := 0) hlive hds
    have hrun := mrunOne (t := t) (j := plicThr) (by rw [ht]; exact poolPlic H c.pcDev vs) hst
    obtain ⟨hm1, hv1, ha1, hc1⟩ := frame ds'
    refine ⟨1, t.set plicThr (.dev 0 .plic rootTask m'), { g with m := { g.m with devs := ds' } },
      Nat.le_refl _, by simpa [pfStepObs] using hrun, hgen, hpow,
      ⟨H, vs, dp, ws', dpr, ?_, by rw [hags, List.length_set, hlen], fun cpu => ?_, hags'.1, hDR⟩,
      ?_, hm1, hv1, ha1, hc1⟩
    · rw [ht, poolPlicSet H c.pcDev vs m' ds', hd']
    · rw [hags'.2 cpu]; exact hharts cpu
    · rw [hd']

/-- The register files after the PLIC wire's `setPin`. -/
def pinM (σ : MState) (cpu : CPU) (mm b : Bool) : MState :=
  if mm then σ.setReg cpu .sig_meip (if b then 1#1 else 0#1)
  else σ.setReg cpu .sig_seip (if b then 1#1 else 0#1)

theorem pinMFields (σ : MState) (cpu : CPU) (mm b : Bool) :
    (pinM σ cpu mm b).mem = σ.mem ∧ (pinM σ cpu mm b).log = σ.log ∧
    (pinM σ cpu mm b).resv = σ.resv ∧ sameRead σ (pinM σ cpu mm b) ∧
    (pinM σ cpu mm b).devs = σ.devs ∧ (pinM σ cpu mm b).regs cpu = pinSet (σ.regs cpu) mm b ∧
    ∀ c, c ≠ cpu → (pinM σ cpu mm b).regs c = σ.regs c := by
  refine ⟨by cases mm <;> rfl, by cases mm <;> rfl, by cases mm <;> rfl, by cases mm <;> exact ⟨rfl, rfl, rfl⟩,
    by cases mm <;> rfl, by cases mm <;> simp [pinM, pinSet], fun c hc => ?_⟩
  cases mm <;> simp [pinM, hc]

/-- **The PLIC wire** (census C2): a hart taking the PLIC program's `setPin` is ONE step of the
PLIC thread (`devOpStep .setPin`); the hart's own thread does not move. -/
theorem simWire {DR : Option (DM Dres) → List Expr → Prop} {c c' : Wpcfg Pexv6 Efab}
    {st rest : List (Nat × Wlabel)} {t : List Expr} {g : GState} {i : Nat} {l : Wlabel}
    (hR : SimRel DR c st t g) (hs : wpPfStep pstepEv pclsEv i l c c') (hk : kindOk c i l c' .wire)
    (hadj : pairAdjacent (st ++ (i, l) :: rest)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      m ≤ 1 ∧ MRun m (t, g) (pfStepObs c i .wire) (t', g') ∧ SimRel DR c' (st ++ [(i, l)]) t' g' := by
  obtain ⟨hgen, hpow, ⟨H, vs, dp, dws, dpr, ht, hlen, hharts, hdisk, hDR⟩, hdev, hmem, hview,
    hauth, hcoh⟩ := hR
  obtain ⟨ag, p', ws', hlk, hks, himg, hags⟩ := hk
  have hi : i < NCPU := by
    rcases Nat.lt_or_ge i NCPU with h | h
    · exact h
    · exfalso
      rcases Nat.eq_or_lt_of_le h with h | h
      · subst h
        rw [hdisk] at hlk
        simp only [Option.some.injEq] at hlk
        subst hlk
        cases p' <;> exact hks.elim
      · rw [List.getElem?_eq_none (by omega)] at hlk
        cases hlk
  obtain ⟨cpu, rfl⟩ : ∃ cpu : CPU, cpu.val = i := ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨fn, ib, ws, pr, hlkc, hfn⟩ := hharts cpu
  rw [hlkc] at hlk
  simp only [Option.some.injEq] at hlk
  subst hlk
  cases p' with
  | PDisk _ => exact hks.elim
  | PHart cpu' m' rs' fn' ib' =>
  obtain ⟨hcc, ors, oib, obar, hrs, hib, mm, b, kp, hpl, hl, hm', hfn', hd', hoib, -, hors⟩ := hks
  subst cpu' rs' ib' l m' fn' oib ors
  have hlive : threadLive g 0 := ⟨hpow, hgen⟩
  have hds : devStep 0 .plic rootTask c.pcDev.efPlic g.m [] (kp ()) (pinM g.m cpu mm b) [] := by
    rw [hpl]
    exact Or.inl ⟨(), rfl, rfl, rfl, rfl⟩
  have hst := primStep_dev_live (gen := 0) hlive hds
  have hrun := mrunOne (t := t) (j := plicThr) (by rw [ht]; exact poolPlic H c.pcDev vs) hst
  obtain ⟨hpm, hpl', hpr, hpsr, hpd, hpc, hpo⟩ := pinMFields g.m cpu mm b
  obtain ⟨hm1, hv1, ha1, hc1⟩ := memFrame (σ' := pinM g.m cpu mm b) hs trivial (Or.inl rfl) hadj
    hmem hview hauth hcoh hpm hpl' hpr hpsr
  refine ⟨1, t.set plicThr (.dev 0 .plic rootTask (kp ())), { g with m := pinM g.m cpu mm b },
    Nat.le_refl _, by simpa [pfStepObs] using hrun, hgen, hpow,
    ⟨H, vs, dp, dws, dpr, ?_, by rw [hags, List.length_set, hlen], fun c'' => ?_, ?_, hDR⟩,
    ?_, hm1, hv1, ha1, hc1⟩
  · rw [ht, poolPlicSet H c.pcDev vs (kp ()) c.pcDev.efDev, hd']
  · by_cases hc : c'' = cpu
    · subst hc
      refine ⟨fn, ib, ws', pr, ?_, hfn⟩
      rw [hags, List.getElem?_set_self (by rw [hlen]; omega)]
      simp [hpc]
    · obtain ⟨fn2, ib2, ws2, pr2, hl2, hf2⟩ := hharts c''
      refine ⟨fn2, ib2, ws2, pr2, ?_, hf2⟩
      have hne : cpu.val ≠ c''.val := fun h => hc (Fin.ext h).symm
      rw [hags, List.getElem?_set_ne hne, hl2]
      simp [hpo c'' hc]
  · rw [hags, List.getElem?_set_ne (by omega)]
    exact hdisk
  · rw [hd', hpd]
    exact hdev

/-! ## (F8) The exclusive look-ahead, one step, the main induction -/

/-- An administrative step of agent `i` leaves the log and `i`'s reservation. -/
theorem adminStep {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (i : Nat) (l : Wlabel) (c c' : Wpcfg P D)
    (h : wpPfStep pstep pcls i l c c') (hl : lbAdmin false l) (ag : Wpagent P)
    (hlk : c.pcAgs[i]? = some ag) :
    c'.pcLog = c.pcLog ∧ ∃ ag', c'.pcAgs[i]? = some ag' ∧ ag'.paWs.wRes = ag.paWs.wRes := by
  have hlt : i < c.pcAgs.length := lookup_lt_Some hlk
  cases h with
  | PFSilent _ ag0 st' d' hlk0 _ =>
    rw [hlk] at hlk0; cases hlk0
    exact ⟨rfl, _, List.getElem?_set_self hlt, rfl⟩
  | PFDev _ ag0 st' d' hlk0 _ =>
    rw [hlk] at hlk0; cases hlk0
    exact ⟨rfl, _, List.getElem?_set_self hlt, rfl⟩
  | PFRegW _ ag0 rd srcs st' d' hlk0 _ =>
    rw [hlk] at hlk0; cases hlk0
    exact ⟨rfl, _, List.getElem?_set_self hlt, rfl⟩
  | PFCtrl _ ag0 srcs st' d' hlk0 _ =>
    rw [hlk] at hlk0; cases hlk0
    exact ⟨rfl, _, List.getElem?_set_self hlt, rfl⟩
  | PFInstr => simp [lbAdmin] at hl
  | PFLoad => simp [lbAdmin] at hl
  | PFStore => simp [lbAdmin] at hl
  | PFRmw => simp [lbAdmin] at hl
  | PFFence => simp [lbAdmin] at hl
  | PFExLoad => simp [lbAdmin] at hl
  | PFExStore => simp [lbAdmin] at hl
  | PFIFetch => simp [lbAdmin] at hl

/-- Walking a record forward over agent `i`'s administrative steps to its exclusive store: the
store's `exclOkTs` holds at the walk's start (log and `i`'s reservation unchanged). -/
theorem walkToStore (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (i : Nat) (rl : Bool) (b : Int) (data : List (BitVec 8)) (a2 v2 : List Dsrc) :
    ∀ {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab},
      contR fok c st r cN → ∀ (m : Nat),
      (∀ w, w < m → ∃ l', (recLabels r)[w]? = some (i, l') ∧ lbAdmin false l') →
      (recLabels r)[m]? = some (i, .LExStore rl b data a2 v2) →
      ∀ (ag : Wpagent Pexv6) (R : Wresv), c.pcAgs[i]? = some ag → ag.paWs.wRes = some R →
        exclOkTs c.pcLog i b R.rvTs (c.pcLog.length + 1) := by
  intro c st r cN h
  induction h with
  | nil c st =>
    intro m _ hm
    simp [recLabels] at hm
  | cons c c' st j l k r cN hs _ _ _ _ ih =>
    intro m hadm hm ag R hlk hres
    cases m with
    | zero =>
      simp only [recLabels, List.map_cons, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      cases hs with
      | PFExStore _ ag0 _ _ _ _ _ _ R0 _ _ hlk0 _ _ hres0 hb0 _ hex0 _ =>
        rw [hlk] at hlk0; cases hlk0
        rw [hres] at hres0; cases hres0
        exact hex0
    | succ m =>
      obtain ⟨l', h0, hadm0⟩ := hadm 0 (by omega)
      simp only [recLabels, List.map_cons, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨hlog, ag', hlk', hres'⟩ := adminStep _ _ j l c c' hs hadm0 ag hlk
      have := ih m (fun w hw => by
          obtain ⟨l'', h1, h2⟩ := hadm (w + 1) (by omega)
          exact ⟨l'', by simpa [recLabels] using h1, h2⟩)
        (by simpa [recLabels] using hm) ag' R hlk' (by rw [hres', hres])
      rw [hlog] at this
      exact this

/-- **The exclusive look-ahead** (hypothesis (4) of `pfStepTso`): at an exclusive read, the
pair's own exclusive store — reached through the agent's administrative steps only — checked
`exclOkTs` on the reservation's timestamps, which ARE the read's. -/
theorem exclAhead (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {c c1 cN : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {i : Nat} {aq : Bool} {base : Int}
    {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} {r : List PfRec}
    (hs : wpPfStep pstepEv pclsEv i (.LExLoad aq base tvs asrc) c c1)
    (hr : contR fok c1 (st ++ [(i, .LExLoad aq base tvs asrc)]) r cN)
    (hadj : pairAdjacent (st ++ (i, .LExLoad aq base tvs asrc) :: recLabels r)) :
    exclOkTs c.pcLog i base (tvs.map Prod.fst) (c.pcLog.length + 1) := by
  obtain ⟨u, hvu, hbt, rl, data, a2, v2, hu, -, -⟩ :=
    hadj.1 st.length i aq base tvs asrc (by simp)
  have hpos : ∀ w, (st ++ (i, Wlabel.LExLoad aq base tvs asrc) :: recLabels r)[st.length + 1 + w]? =
      (recLabels r)[w]? := by
    intro w
    rw [List.getElem?_append_right (by omega), show st.length + 1 + w - st.length = w + 1 by omega]
    rfl
  have hm : (recLabels r)[u - st.length - 1]? = some (i, .LExStore rl base data a2 v2) := by
    rw [← hpos, show st.length + 1 + (u - st.length - 1) = u by omega]; exact hu
  cases hs with
  | PFExLoad _ ag _ _ _ _ st' d' hlk _ _ =>
    have hlt : i < c.pcAgs.length := lookup_lt_Some hlk
    exact walkToStore fok i rl base data a2 v2 hr (u - st.length - 1)
      (fun w hw => by
        obtain ⟨l', h1, h2⟩ := hbt (st.length + 1 + w) (by omega) (by omega)
        exact ⟨l', by rw [← hpos]; exact h1, h2⟩)
      hm _ _ (List.getElem?_set_self hlt) rfl

/-- **ONE pf step** is 0, 1 (or, for the disk program, F9's) MachCSL steps, observed by the
record, re-establishing the relation. -/
theorem simStep {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {DR : Option (DM Dres) → List Expr → Prop} {g0 : GState} {c0 : Wpcfg Pexv6 Efab}
    (hH : Hyps fok DR g0 c0) {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)}
    {t : List Expr} {g : GState} {n : Nat} {κ : List Obs} {i : Nat} {l : Wlabel} {k : SKind}
    (hR : SimRel DR c st t g) (hreach : MRun n ([Expr.power], g0) κ (t, g))
    (hrun : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c)
    (hs : wpPfStep pstepEv pclsEv i l c c') (hf : pfStepFacts fok c i l)
    (hfT : pfLoadFactsT TsoShadow.cohSrc st c i l) (hk : kindOk c i l c' k)
    (hadj : pairAdjacent (st ++ (i, l) :: rest))
    (hex : ∀ aq base tvs asrc, l = .LExLoad aq base tvs asrc →
      exclOkTs c.pcLog i base (tvs.map Prod.fst) (c.pcLog.length + 1)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      (k ≠ .disk → m ≤ 1) ∧ MRun m (t, g) (pfStepObs c i k) (t', g') ∧ SimRel DR c' (st ++ [(i, l)]) t' g' := by
  cases k with
  | node =>
    obtain ⟨m, t', g', hle, hm, hR'⟩ := simNode hH hR hreach hrun hs hf hfT hk hadj hex
    exact ⟨m, t', g', fun _ => hle, hm, hR'⟩
  | wire =>
    obtain ⟨m, t', g', hle, hm, hR'⟩ := simWire hR hs hk hadj
    exact ⟨m, t', g', fun _ => hle, hm, hR'⟩
  | uart u =>
    obtain ⟨m, t', g', hle, hm, hR'⟩ := simDev (fok := fok) hR hs hk ⟨nofun, nofun, nofun⟩ hadj
    exact ⟨m, t', g', fun _ => hle, hm, hR'⟩
  | gate =>
    obtain ⟨m, t', g', hle, hm, hR'⟩ := simDev (fok := fok) hR hs hk ⟨nofun, nofun, nofun⟩ hadj
    exact ⟨m, t', g', fun _ => hle, hm, hR'⟩
  | disk =>
    obtain ⟨ag, p', ws', hlk, hks, himg, hags⟩ := hk
    obtain ⟨st0, ws0, pr0⟩ := ag
    cases st0 with
    | PHart _ _ _ _ _ => cases p' <;> exact hks.elim
    | PDisk dp0 =>
    have hi := diskAgentIdx hR hlk rfl
    subst hi
    obtain ⟨m, t', g', hm, hR'⟩ :=
      hH.disk st rest c c' t g n κ l hrun hreach hR hs hf hfT ⟨_, p', ws', hlk, hks, himg, hags⟩ hadj
    exact ⟨m, t', g', fun h => absurd rfl h, by simpa [pfStepObs] using hm, hR'⟩

/-- **THE MAIN INDUCTION** (F8), forward over the run record: from a related, boot-reachable
MachCSL configuration, the rest of the run is a MachCSL run observed by `pfObsOf`, ending
related to the pf run's last configuration. -/
theorem simRun {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {DR : Option (DM Dres) → List Expr → Prop} {g0 : GState} {c0 : Wpcfg Pexv6 Efab}
    (hH : Hyps fok DR g0 c0) :
    ∀ {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab},
      contR fok c st r cN →
      ∀ {t : List Expr} {g : GState} {n : Nat} {κ : List Obs},
        SimRel DR c st t g → MRun n ([Expr.power], g0) κ (t, g) →
        pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → pairAdjacent (st ++ recLabels r) →
        ∃ (m : Nat) (t' : List Expr) (g' : GState),
          MRun m ([Expr.power], g0) (κ ++ pfObsOf r) (t', g') ∧
          SimRel DR cN (st ++ recLabels r) t' g' := by
  intro c st r cN h
  induction h with
  | nil c st =>
    intro t g n κ hR hreach _ _
    exact ⟨n, t, g, by simpa [pfObsOf] using hreach, by simpa [recLabels] using hR⟩
  | cons c c' st i l k r cN hs hf hfT hk hr ih =>
    intro t g n κ hR hreach hrun hadj
    have hadj' : pairAdjacent (st ++ (i, l) :: recLabels r) := by
      simpa [recLabels] using hadj
    obtain ⟨m1, t1, g1, -, hm1, hR1⟩ := simStep hH hR hreach hrun hs hf hfT hk hadj'
      (fun aq base tvs asrc hl => by subst hl; exact exclAhead fok hs hr hadj')
    obtain ⟨m2, t2, g2, hm2, hR2⟩ := ih hR1 (mrunTrans hreach hm1) (.snoc c c' st i l hrun hs hf hfT)
      (by simpa using hadj')
    refine ⟨m2, t2, g2, ?_, by simpa [recLabels] using hR2⟩
    rw [pfObsOfCons, ← List.append_assoc]
    exact hm2

/-- **W4's STRUCTURAL THEOREM (F1–F8): a shaped pf run, PREFIXED by ONE `PowerOn` step, is a
MachCSL run** (plan §C W4; census §F).  From the machine off (`g0`: generation 0, power off,
devices `ds`) and the pf boot `σ0` (`wbootFacts`, devices `ds.reset`), every `pfRunST` run from
`wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)` — `srvwmoXv6M1PfRun`'s configuration —
with `pairAdjacent` steps has a RUN RECORD `r` (its configurations and step kinds; its step list
is the run's) such that `([power], g0)` runs, in `n` thread-pool steps (no bound `n ≤ |st|`,
E-S6), observing `.powerOn :: pfObsOf r` (E-S3: a function of the record), to a configuration
related to the run's last one by `SimRel` (the pool by step kind, registers, devices, and
`R_mem` = `rmem ∧ viewRel cohSrc`).  Parametric in `Hyps` (W2 CLOSE's `pfStepTso`, HSafe, the
fetch cut, item (3)'s `fiArm` facts, and F9's disk rows over `DR`). -/
theorem machRunOfPfRun (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (DR : Option (DM Dres) → List Expr → Prop) (σ0 : WGState) (ds : DevStates) (g0 : GState)
    (hb : wbootFacts σ0) (hds : σ0.wgdev = ds.reset) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hgd : g0.m.devs = ds) (hDR : DR none [DevLoop 0 .virtio])
    (hH : Hyps fok DR g0 (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)))
    (st : List (Nat × Wlabel)) (cN : Wpcfg Pexv6 Efab)
    (hrun : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cN)
    (hadj : pairAdjacent st) :
    ∃ r : List PfRec,
      contR fok (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cN ∧
      recLabels r = st ∧
      ∃ (n : Nat) (t : List Expr) (g : GState),
        MRun n ([Expr.power], g0) (Obs.powerOn :: pfObsOf r) (t, g) ∧ SimRel DR cN st t g := by
  obtain ⟨r, hr, hl⟩ := contROfRun fok hrun
  have hboot := powerOnRun g0 σ0 ds hb hg0 hp0 hgd
  have hR0 := simRelBoot DR hDR σ0 ds hb hds
  obtain ⟨m, t, g, hm, hR⟩ := simRun hH hr hR0 hboot .nil (by simpa [hl] using hadj)
  refine ⟨r, hr, hl, m, t, g, by simpa using hm, by simpa [hl] using hR⟩

/-! ## (M1) The fetch cut from the pristine kernel text -/

/-- The pristine-window fact W3 exports (`Xv6.textPristine` at `[bcRoLo, bcRoHi)`, read through
`Xv6.textWin_get`): every window byte's history is a single timestamp-0 entry. -/
def winPristine (lo hi : Nat) (g : GState) : Prop :=
  ∀ pa : PAddr, lo ≤ pa.toNat → pa.toNat < hi → ∃ v, g.m.mem[pa]? = some [⟨0, 0, v⟩]

/-- A byte whose `R-hist` history is the image entry alone has no write in the log. -/
theorem histNoWrite (img : Image) (log : List Wmsg) (a : Int) (v : BitVec 8)
    (h : TsoOfPf.histOf img log a = [⟨0, 0, v⟩]) :
    ∀ i : Nat, log[i]?.bind (fun m => msgByte m a) = none := by
  intro i
  cases hb : log[i]?.bind (fun m => msgByte m a) with
  | none => rfl
  | some w =>
    exfalso
    have hi : i < log.length := by
      cases hl : log[i]? with
      | none => rw [hl] at hb; cases hb
      | some _ => exact lookup_lt_Some hl
    have hmem : (⟨i + 1, (log[i]?.bind Wmsg.wmTid).getD 0, w⟩ : HEnt) ∈
        TsoOfPf.histOf img log a := by
      unfold TsoOfPf.histOf
      apply List.mem_append_left
      rw [List.mem_reverse, List.mem_filterMap]
      exact ⟨i, List.mem_range.2 hi, by rw [hb]; rfl⟩
    rw [h] at hmem
    simp at hmem

/-- **M1's fetch cut** (`Hyps.cut` at `fok = candKfetch lo hi`): when every MachCSL state reachable
from boot keeps the window `[lo, hi) ⊆ DRAM` pristine (W5: `Xv6.powerInterp_textPristine`), a
fetch inside the window reads image bytes no log message ever wrote, so ANY cut works — take the
shadow's `itv` (TsoMem's own instruction view). -/
theorem cutOfPristine (lo hi : Nat) (hlo : ramBase ≤ lo) (hhi : hi ≤ ramEnd)
    (DR : Option (DM Dres) → List Expr → Prop) (g0 : GState) (c0 : Wpcfg Pexv6 Efab)
    (htext : ∀ (n : Nat) (κs : List Obs) (t : List Expr) (g : GState),
      MRun n ([Expr.power], g0) κs (t, g) → g.pow = true → winPristine lo hi g) :
    ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
      pfRunST pstepEv pclsEv (candKfetch (lo : Int) (hi : Int)) TsoShadow.cohSrc c0 st c →
      MRun n ([Expr.power], g0) κ (t, g) → SimRel DR c st t g →
      ∀ (cpu : CPU) (base : Int) (tvs : List (Nat × BitVec 8)) (c' : Wpcfg Pexv6 Efab),
        wpPfStep pstepEv pclsEv (hartAgent cpu) (.LIFetch base tvs) c c' →
        pfStepFacts (candKfetch (lo : Int) (hi : Int)) c (hartAgent cpu) (.LIFetch base tvs) →
        ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
          ifetchOk c.pcImg c.pcLog q base tvs ∧
          ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q := by
  intro st c t g n κ _ hreach hR cpu base tvs c' hs hf
  have hwin := htext n κ t g hreach hR.pow
  have hif : ifetchOk c.pcImg c.pcLog 0 base tvs := by
    cases hs with
    | PFIFetch _ _ _ _ _ _ _ _ h => exact h
  -- no log message writes a fetched byte
  have hnw : ∀ j, j < tvs.length →
      ∀ i : Nat, c.pcLog[i]?.bind (fun m => msgByte m (base + (j : Int))) = none := by
    intro j hj
    obtain ⟨h1, h2⟩ := hf j hj
    simp only [ramBase] at hlo
    simp only [ramEnd] at hhi
    have hpa : (BitVec.ofNat 64 (base + (j : Int)).toNat).toNat = (base + (j : Int)).toNat := by
      rw [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      omega
    have hram : inRam (BitVec.ofNat 64 (base + (j : Int)).toNat) 1 := by
      simp only [inRam, hpa, ramBase, ramEnd]
      omega
    obtain ⟨v, hv⟩ := hwin (BitVec.ofNat 64 (base + (j : Int)).toNat) (by omega) (by omega)
    have hh := hR.mem.2.2.1.1 _ hram
    rw [hv] at hh
    have hz : paZ (BitVec.ofNat 64 (base + (j : Int)).toNat) = base + (j : Int) := by
      simp only [paZ, hpa]
      omega
    rw [hz] at hh
    exact histNoWrite _ _ _ _ (Option.some.inj hh).symm
  have ht0 : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t = 0 := by
    intro j t v hj
    obtain ⟨hlb, -⟩ := hif j t v hj
    cases t with
    | zero => rfl
    | succ i =>
      exfalso
      rw [logByteS, hnw j (lookup_lt_Some hj) i] at hlb
      cases hlb
  have hbound : (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ c.pcLog.length := by
    have h1 := (tsoShadowBound TsoShadow.cohSrc cohSrcOk (hartAgent cpu) st).2
    have h2 := congrArg List.length hR.auth
    simp only [List.length_map] at h2
    omega
  refine ⟨_, Nat.le_refl _, hbound, fun j t v hj => ?_,
    fun j t v hj => by rw [ht0 j t v hj]; exact Nat.zero_le _⟩
  obtain ⟨hlb, -⟩ := hif j t v hj
  refine ⟨hlb, ?_⟩
  rintro ⟨t', -, -, m, hm, hs'⟩
  have := hnw j (lookup_lt_Some hj) (t' - 1)
  rw [hm] at this
  simp only [Option.bind_some] at this
  rw [this] at hs'
  cases hs'

end MachOfPf

end Weak

#print axioms Weak.MachOfPf.machRunOfPfRun
#print axioms Weak.MachOfPf.cutOfPristine
