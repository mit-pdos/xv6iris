/-
Weak: **W4 — a shaped pf run IS a MachCSL run** (allocproc plan §C W4: the STRUCTURAL half
F1–F8, census `notes/W4-structural-census.md` §F; and the DISK ROWS F9, plan §C W4 F9 / §C W-DISK
"LANDED — the record", with the virtio half in `Weak/MachOfPfDisk.lean`).  Lean-only (no Rocq
source).

**Main theorem** `MachOfPf.machRunOfPfRun`: from the machine off (`g0`: generation 0, power off,
devices `ds`) and a pf boot `σ0` (`wbootFacts`, devices `ds.reset`), every `pfRunST` run (any
`fok`, stamp `cohSrc`) from `wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)` — exactly
`srvwmoXv6M1PfRun`'s configuration — with `pairAdjacent` steps has a RUN RECORD `r` (`contR`: the
run's configurations and step kinds, `recLabels r = st`) such that `([power], g0)` makes ONE
`PowerOn` step and then runs, `MRun n` (= iris `NSteps`, no bound `n ≤ |st|`, E-S6), observing
`.powerOn :: pfObsOf r` — a FUNCTION of the record (E-S3) — to a MachCSL configuration related to
the run's last configuration by `SimRel` (`poolRel ∧ R_mem`).

**The relation** `SimRel c st t g` (F1): generation 0, power on (the power thread is never
stepped again); the pool is `poolOf H F vs` — thread `0` power, `c + 1` hart `c` running the pf
hart's residual monad `H c`, `NCPU + 1`/`+ 2` the UART programs and `NCPU + 3` the PLIC program
of the fabric, then the virtio threads `vs` — the root `Virtio.body` at `NCPU + 4`, the forked
`serve` tasks after it (`13 + k`) — related to the disk agent's program by `diskSide` (F9: the
position relation `PosRel` and **`R-dev`**, `devAgree`; E-S2: the thread map is per step KIND,
`thrOf`); register files EQUAL; and `R_mem` = W2's `rmem ∧ viewRel cohSrc`, with the `R-log` link to the step list
(`pfStepTso`'s hypothesis (2)) and `ownCoh` (part of (4)); every parked fence is `fence.tso`'s
parked half (`fnOk`).

**Rows** (census table B6, `simStep`: 0 or 1 MachCSL step per pf step off the disk program):
* F3 boot (`powerOnRun`, `simRelBoot`): `bootG1` from `wbootFacts` (its register clause IS
  `bootFacts`'), `bootShape`, `primStep_power_on`; `R_mem` by `rmemBoot`/`viewRelNil`.
* F4/F5 hart node (`simNode`): parked-fence fire and lost-SC retry = 0 steps (frame: the shadow
  of the parked `LFence true true false true` is the identity, `viewRelPark`); the boundary, the
  silent nodes, register reads and writes (`LSilent`/`LRegW`/`LCtrl`, all `lbInert`) = 1
  `primStep` with `σ' = σ` / `setReg`, `R_mem` by `memFrame` (W2a `pfFrameRowMem`, W2b
  `viewRelInert`) -- at the boundary `σ' = σ.dropResv cpu` (W-RSV: the reservation is cleared,
  `rmemDropResv`); MMIO = 1 step (`devRead`/`devWrite`, the whole-footprint `devBytes` from HSafe,
  `devOfSafe`); RAM read/write, barrier, announce/marker = 1 step through `pfStepTso`, its
  hypotheses discharged here: `ramBytes` from HSafe (`ramOfSafe`, `notOthers` from `R-resv` and
  the adjacency), (1) from the full run's `pairAdjacent`, (2) from `SimRel`, (3) from `Hyps.cut`,
  (4) `ownCoh` from `SimRel` and `exclOkTs` from the pair's own exclusive store
  (`exclAhead`/`walkToStore`: only the agent's administrative steps lie between), the `fiArm`
  facts from `Hyps.fi`; the MachCSL post-state's registers/devices by `evStepShape`.
* F6 devices (`simDev`, `simWire`): the disk agent's UART/PLIC-gateway `fdevStep` = 1 `devStep`
  of the device's own thread (`devStepOfFdev`, observed `fdevObs`, transported across `R-dev` by
  `diskSideFdev`); the hart's PLIC wire = 1 `devOpStep .setPin` of the PLIC thread (`pinM`).
* F9 disk rows (`simDisk`): the disk agent's own program against MachCSL's virtio threads, one
  row per `PosRel` position (`caseIdle` … `caseFin`, the plan's step counts in the section
  header), built from one-step lemmas of the virtio threads (`VRun`, `vGet` … `vFork`) and the
  drain loop (`drainLoop`: the root drains every cached sector, 5 steps each, reaching pf's
  `drainAll`); every consumer of the device clause re-proved against `R-dev` [R21.3 (c)] — the
  hart MMIO arms (`diskSideRead`/`diskSideWrite`), `simDev`, `simWire`, every `simNode` post.
* F7 `pfStepObs`/`pfObsOf`: a hart node emits `hartObsM` read off the pf register file
  (`hartObsMEq`), a UART step its guard's events, everything else nothing.
* F8 `simRun`: forward induction over the record (`contROfRun` turns the snoc-built `pfRunST` into
  it; the look-ahead (4) needs the record's tail).
* M1 (`cutOfPristine`): `Hyps.cut` at `fok = candKfetch lo hi` from a MachCSL-side pristine window
  (`winPristine`, W3's `textPristine` read through `textWin_get`), through the two factored steps
  `noWriteOfPristine` (no log message writes a window byte) and `fetchIsImage` (an admissible
  fetch of unwritten bytes reads the image at timestamp 0) — W-SCO [R28.2] reuses both.

**Parameters** (`Hyps`): `tso` = W2 CLOSE's `pfStepTso` in the ADOPTED shape (`pfStepTsoStmt`, a
verbatim copy of `PfStepTso.proposedStmt`); `safe` = HSafe (E-S1); `cut` = the fetch cut at every
fetch; `fi` = plan item (3) (`fiArm` at `fence.i` / the `sfence.vma` marker) — F9's former `disk`
parameter is DISCHARGED (`simDisk`).

**Deviations from the plan / census text.**
1. `pfStepTso` is the coordinator-adopted `proposedStmt` (2026-10-11), not the pinned §C W2 CLOSE
   text (false at the fetch and log-length rows, unusable inside exclusive pairs:
   `PROGRESS-W2CLOSE.md`, `PROGRESS-W4s.md`).
2. The companions `pfStepTsoStutter`/`pfStepTsoSame` are NOT parameters: W4 proves those rows
   itself from the landed W2a/W2b frame lemmas (`memFrame`, `viewRelPark`) — including the rows
   their prose missed (the boundary `LInstr`, a register write labelled `LSilent`, the PLIC wire
   at a parked fence or at the boundary, the disk agent's UART/PLIC moves).
3. Item (3) (`fiArm`) is a PARAMETER (`Hyps.fi`, stated over every `pfRunST` run from the boot
   configuration, at a related boot-reachable MachCSL state — `cut`'s shape, W-SCO [R28.2]): W2 CLOSE disowned it (a fact of Sail's event order inside `try_step`, not of
   the step list); Q-FIARM RULED [OWN.35]: it is the named premise `sailCycleOrder`
   (`Weak/SrvwmoXv6Adequacy.lean`, `fiOfSco`) — TRUE of the model from this platform's reset (the
   boot PMA table forbids instruction fetch from I/O regions and the HTIF window is disabled);
   FALSE over arbitrary register files; stated under `wbootFacts σ0` [R32.1][R33.1][OWN.45];
   proved: `sailCycleOrder_holds`, `SailCycleOrderCycle.lean:137`.
4. The fetch cut is a PARAMETER over related, boot-reachable states (`Hyps.cut`), discharged at
   M1 by `cutOfPristine` from a SECOND MachCSL-side hypothesis (the pristine window at every
   reachable powered state; W5: `powerInterp_textPristine`) — `candKfetch` alone does not give it.
5. `κs` is a function of the run RECORD (configurations + step kinds): the disk agent's
   `LDev .dev 0 [] [] []` does not say which device moved, and `pfRunST` is a `Prop`.
6. (F9) `SimRel`'s device clause is `R-dev` (`diskSide`/`devAgree`), no longer `efDev = σ.devs`:
   every device but the disk EQUAL, the disk EQUAL (all fields, `disk` and `cache` included) off
   the OUT capture segment and `(pre₁ pf).1` on it [R18.3][R20.1]; the plan's `cache = []`
   outside a capture → gate window is replaced by the weaker `cacheWf` (`MachOfPfDisk` deviation
   1); the task bookkeeping `devrt` is not tracked (`MachOfPfDisk` deviation 2).  The parameter
   `DR` of `SimRel` is gone (instantiated by `diskSide`).
7. (F9) A disk load wrapping past `2^64` would make the rows FALSE (MachCSL's DMA read wraps its
   `PAddr` and reads the top of the wrapped DRAM bytes; the pf load reads Int addresses where
   `imgZ` aliases the boot image).  Every load of at most 16 bytes is safe (`smallNoWrap`:
   descriptor / header / ring reads); the OUT capture read is made safe by the pf program itself,
   which STALLS on a wrapping capture buffer (`VirtioProg.outWraps`, owner ruling (a′) [OWN.40];
   `caseStall`), so no hypothesis remains.
8. (W5d [R29.1], the cut clause's carrier) The parameter set is `HypsC fok fcutT`, the run record
   `contRC fok fcutT`: `contRC.cons` carries the step's `pfCutFactsT fcutT` (`TsoShadow.lean`) and
   `HypsC.cut` RECEIVES it — M2's cut is that clause verbatim (`Weak/PfRunUnpinned.lean`).  The
   plan's names are the M1 (trivial-cut `fcutTTriv`) instances, as reducible abbreviations:
   `Hyps fok := HypsC fok fcutTTriv`, `contR fok := contRC fok fcutTTriv`, so M1's statement text
   is unchanged; M1's `cutOfPristine` enters `HypsC.cut` through `cutIgnore`.  `HypsC.cut`/`.fi`
   quantify the trivial-cut `pfRunST` runs (`pfRunSTForgetCut`), so `simRun` threads that run and
   `machRunOfPfRun` takes any `pfRunSTC` run.

Every name is in `Weak.MachOfPf` (file-qualified).  Axioms: `propext`, `Classical.choice`,
`Quot.sound`.
-/
import Weak.PfStepTsoMem
import Weak.PfStepTsoView
import Weak.PfRunShape
import Weak.WeakEvCapstone
import Weak.MachOfPfDisk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Sail.ArchSem (FreeM)
open TsoShadow PfStepTsoMem PfStepTsoView MachOfPfDisk

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
    l ≠ .LSilent → (∀ kd ba bs sa sv, l ≠ .LDev kd ba bs sa sv) →
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
program's steps run the virtio root at `NCPU + 4` and the live task after it, F9 `simDisk`). -/
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

/-- **The virtio part of the pool** (F9): the virtio threads are the ROOT (running `mr`) followed
by the forked tasks, one of which (if `ot` names one) is the LIVE serving task; the forked tasks
are appended at the END of the pool (iris `Step.atomic`), so a task's thread is `NCPU + 4` + its
position in `vs` (the plan's `13 + k`). -/
def vsOk (vs : List Expr) (mr : Virtio.VM Unit) (ot : Option (Virtio.VM Unit)) : Prop :=
  ∃ ts : List Expr, vs = Expr.dev 0 .virtio rootTask mr :: ts ∧
    ∀ mt, ot = some mt → ∃ (j : Nat) (tid : TaskId), ts[j]? = some (Expr.dev 0 .virtio tid mt)

/-- **The disk side of the relation** (F9): the pf disk program `dp` and MachCSL's virtio threads
`vs` at corresponding positions (`MachOfPfDisk.PosRel`), and **`R-dev`** between the pf device
states `dsP` and MachCSL's `dsM` (`MachOfPfDisk.devAgree`: every device but the disk EQUAL, the
disk EQUAL off the OUT capture segment and `(pre₁ pf).1` on it, the pf cache well-formed). -/
def diskSide (dp : Option (DM Dres)) (vs : List Expr) (dsP dsM : DevStates) : Prop :=
  ∃ (mr : Virtio.VM Unit) (ot : Option (Virtio.VM Unit)) (κ : VRel),
    vsOk vs mr ot ∧ PosRel dp mr ot κ ∧ devAgree κ dsP dsM

/-- **THE SIMULATION RELATION** `poolRel ∧ R_mem` at a pf configuration `c` with step-list
prefix `st` and a MachCSL configuration `(t, g)`: generation 0, power on; the pool is `poolOf`
with the harts' residual monads those of the pf harts, the UART/PLIC programs the fabric's, and
the virtio threads related to the disk agent's program by `diskSide` (which carries `R-dev`,
F9 — the device states are no longer EQUAL, header deviation 6); the register files equal; and
`R_mem` = W2's `rmem ∧ viewRel cohSrc`, with the `R-log` link to the step list and `ownCoh`
(the hypotheses (2)/(4) of `pfStepTso`). -/
structure SimRel (c : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (t : List Expr) (g : GState) : Prop where
  gen : g.gen = 0
  pow : g.pow = true
  pool : ∃ (H : CPU → SailM Unit) (vs : List Expr) (dp : Option (DM Dres)) (dws : Wstate)
      (dpr : GSet Nat),
    t = poolOf H c.pcDev vs ∧ c.pcAgs.length = NCPU + 1 ∧
    (∀ cpu : CPU, ∃ fn ib ws pr,
       c.pcAgs[cpu.val]? = some ⟨.PHart cpu (H cpu) (g.m.regs cpu) fn ib, ws, pr⟩ ∧ fnOk fn) ∧
    c.pcAgs[NCPU]? = some ⟨.PDisk dp, dws, dpr⟩ ∧ diskSide dp vs c.pcDev.efDev g.m.devs
  mem : rmem c st g.m
  view : viewRel TsoShadow.cohSrc g.m st
  auth : c.pcLog.map Wmsg.wmTid = (stAuthors st).map some
  coh : ownCoh c

/-! ## (F3) The boot bridge: `wbootFacts` → `bootShape`, the one `PowerOn` step -/

/-- The booted MachCSL state: the pf boot's register files (`wbootFacts`' register clause IS
`bootFacts`'), the boot image, an empty log, zero views, the reset devices. -/
def bootG1 (σ0 : WGState) (ds : DevStates) : GState :=
  { m := ⟨σ0.wgregs, imgFlat bootImage, [], fun _ => 0, fun _ => 0, fun _ => HRead.zero,
          fun _ => none, ds.reset, fun _ => DevRt.init, fun _ => -1, [], fun _ => [], fun _ => 0⟩,
    gen := 0, pow := true }

theorem bootShapeG1 (g0 : GState) (σ0 : WGState) (ds : DevStates) (hb : wbootFacts σ0)
    (hg : g0.gen = 0) (hd : g0.m.devs = ds) : bootShape g0 (bootG1 σ0 ds) := by
  obtain ⟨-, -, -, -, -, hregs, -, -⟩ := hb
  refine ⟨hg.symm, rfl, ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, hregs, fun _ => rfl, rfl,
    fun _ => ⟨rfl, rfl⟩⟩, ?_⟩
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
theorem simRelBoot (σ0 : WGState) (ds : DevStates) (hb : wbootFacts σ0) (hds : σ0.wgdev = ds.reset) :
    SimRel (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) []
      (poolOf (fun _ => FreeM.pure ()) (efInit ds.reset) [DevLoop 0 .virtio]) (bootG1 σ0 ds) := by
  have himg : σ0.wgimg = bootImage := hb.2.1
  obtain ⟨hlen, hcpu, hdisk⟩ := epsInitAgs σ0 (imgZ σ0.wgimg) (efInit σ0.wgdev)
  have hDS : diskSide none [DevLoop 0 .virtio] (efInit σ0.wgdev).efDev (bootG1 σ0 ds).m.devs := by
    refine ⟨.pure (), none, .eq, ⟨[], rfl, fun _ h => by cases h⟩, .idle, ?_⟩
    show devAgree .eq σ0.wgdev ds.reset
    rw [hds]
    exact devAgreeEq _ cacheWfNil
  refine ⟨rfl, rfl, ⟨fun _ => FreeM.pure (), [DevLoop 0 .virtio], none, wsInit, ∅,
    by rw [hds]; rfl, hlen, fun cpu => ⟨none, σ0.wgib cpu, wsInit, ∅, hcpu cpu,
      fun _ h => by cases h⟩, hdisk, hDS⟩, ?_, ?_, by simp [wpInit, stAuthors],
    ownCohInit _ _ _⟩
  · rw [himg]
    exact rmemBoot _ _ _ ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, hb.2.2.2.2.2.1, fun _ => rfl, rfl,
      fun _ => ⟨rfl, rfl⟩⟩
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
      dp' = dp ∧ l = .LDev .dev 0 [] [] [] ∧
      ∃ (m' : DevProg (.uart u)) (ds' : DevStates),
        fdevStep (.uart u) (efU d u) d.efDev m' ds' ∧ d' = efUset { d with efDev := ds' } u m'
  | .gate, .PDisk dp, .PDisk dp' =>
      dp' = dp ∧ l = .LDev .dev 0 [] [] [] ∧
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
`pfRunSTC` step with its facts — the cut clause `fcutT` included, W5d [R29.1] — at ITS prefix, and
its kind) lead to `cN`. -/
inductive contRC (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) :
    Wpcfg Pexv6 Efab → List (Nat × Wlabel) → List PfRec → Wpcfg Pexv6 Efab → Prop where
  | nil (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) : contRC fok fcutT c st [] c
  | cons (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) (k : SKind)
      (r : List PfRec) (cN : Wpcfg Pexv6 Efab) :
      wpPfStep pstepEv pclsEv i l c c' → pfStepFacts fok c i l →
      pfLoadFactsT TsoShadow.cohSrc st c i l → pfCutFactsT fcutT TsoShadow.cohSrc st c i l →
      kindOk c i l c' k →
      contRC fok fcutT c' (st ++ [(i, l)]) r cN → contRC fok fcutT c st (⟨c, i, l, k⟩ :: r) cN

/-- The run record of M1 (`contRC` at the trivial cut clause). -/
abbrev contR (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) :
    Wpcfg Pexv6 Efab → List (Nat × Wlabel) → List PfRec → Wpcfg Pexv6 Efab → Prop :=
  contRC fok fcutTTriv

theorem contRSnoc (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c c1 c2 : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {i : Nat}
    {l : Wlabel} {k : SKind} (h : contRC fok fcutT c st r c1)
    (hs : wpPfStep pstepEv pclsEv i l c1 c2)
    (hf : pfStepFacts fok c1 i l) (hfT : pfLoadFactsT TsoShadow.cohSrc (st ++ recLabels r) c1 i l)
    (hcf : pfCutFactsT fcutT TsoShadow.cohSrc (st ++ recLabels r) c1 i l)
    (hk : kindOk c1 i l c2 k) : contRC fok fcutT c st (r ++ [⟨c1, i, l, k⟩]) c2 := by
  revert hfT hcf
  induction h with
  | nil c st =>
    intro hfT hcf
    exact .cons _ _ _ i l k [] c2 hs hf (by simpa [recLabels] using hfT)
      (by simpa [recLabels] using hcf) hk (.nil _ _)
  | cons c c' st i' l' k' r cN hs' hf' hfT' hcf' hk' _ ih =>
    intro hfT hcf
    exact .cons _ _ _ i' l' k' _ _ hs' hf' hfT' hcf' hk'
      (ih hs hf hk (by simpa [recLabels, List.append_assoc] using hfT)
        (by simpa [recLabels, List.append_assoc] using hcf))

/-- A shaped run IS a run record. -/
theorem contROfRun (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c0 cN : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)}
    (h : pfRunSTC pstepEv pclsEv fok TsoShadow.cohSrc fcutT c0 st cN) :
    ∃ r, contRC fok fcutT c0 [] r cN ∧ recLabels r = st := by
  induction h with
  | nil => exact ⟨[], .nil _ _, rfl⟩
  | snoc c1 c2 st i l _ hs hf hfT hcf ih =>
    obtain ⟨r, hr, hl⟩ := ih
    obtain ⟨k, hk⟩ := kindOfStep i l c1 c2 hs
    exact ⟨r ++ [⟨c1, i, l, k⟩], contRSnoc fok hr hs hf (by simpa [hl] using hfT)
      (by simpa [hl] using hcf) hk, by simp [recLabels, ← hl]⟩

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
    (hsr : sameRead σ σ') (hxs : σ'.sb = σ.sb := by rfl) :
    rmem c' (st ++ [(i, l)]) σ' ∧ viewRel TsoShadow.cohSrc σ' (st ++ [(i, l)]) ∧
      c'.pcLog.map Wmsg.wmTid = (stAuthors (st ++ [(i, l)])).map some ∧ ownCoh c' := by
  refine ⟨(pfFrameRowMem pstepEv pclsEv c c' st rest σ i l hR hs hl hadj).2.2 σ' hmem hlog hres hxs,
    ?_, authStep hs hA, ownCohStep pstepEv pclsEv i l c c' hC hs⟩
  rcases hin with hin | rfl
  · exact viewRelInert _ σ σ' st i l hin hV hsr
  · exact viewRelSame (viewRelPark i hV) hsr

/-- `R-resv` survives the instruction boundary's reservation clearing (W-RSV: `hartStep`'s `.pure`
arm is `σ.dropResv cpu`, the pf twin's `instrPost` clears `wRes` alike). -/
theorem rmemDropResv {P D : Type} {c : Wpcfg P D} {st : List (Nat × Wlabel)} {σ : MState} (cpu : CPU)
    (h : rmem c st σ) : rmem c st (σ.dropResv cpu) := by
  obtain ⟨hl, hi, hh, hr, hx⟩ := h
  refine ⟨hl, hi, hh, fun c' => ?_, fun c' => ?_⟩
  · by_cases hc : c' = cpu
    · subst hc
      left
      simp [updCpu]
    · have := hr c'
      simpa [updCpu, hc] using this
  · exact hx c'

/-! ## The hypotheses W4 is parametric in -/

/-- **W4's parameters** (all but `tso` MachCSL-side or run-level facts):
* `tso` — W2 CLOSE's `pfStepTso` (the adopted statement);
* `safe` — **HSafe** (E-S1): every thread of every MachCSL run from `([power], g0)` is
  reducible (W5: `xv6FsAdequacy_closed`'s first conjunct).  It supplies the BUS DECODE the pf
  machine lacks (`devBytes`/`ramBytes` over the whole footprint);
* `cut` — the fetch cut of `pfStepTso`'s hypothesis (3) at every fetch of the run, at a related
  MachCSL state reachable from boot, given the step's cut clause `pfCutFactsT fcutT` (W5d
  [R29.1]; M1: `fcutTTriv`, the cut from `candKfetch` and the pristine kernel text, `cutIgnore`;
  M2: the clause IS the cut form, `Weak/PfRunUnpinned.lean`);
* `fi` — plan item (3): `fiArm` at `fence.i` / the `sfence.vma` marker, along every run from
  `c0` (a fact of the Sail model's event order; [OWN.35]: the named premise `sailCycleOrder` —
  TRUE of the model from this platform's reset (the boot PMA table forbids instruction fetch from
  I/O regions and the HTIF window is disabled); FALSE over arbitrary register files; stated under
  `wbootFacts σ0` [R32.1][R33.1]),
  at a related MachCSL state reachable from boot — the `cut` shape [R28.2], so that a
  kernel-text discharge (W-SCO) can pin the fetched words to the image through `SimRel`.
The disk rows are `simDisk`, no longer a parameter.  The runs `cut` and `fi` quantify are the
trivial-cut `pfRunST` ones (every `pfRunSTC` run forgets to one, `pfRunSTForgetCut`). -/
structure HypsC (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (g0 : GState) (c0 : Wpcfg Pexv6 Efab) : Prop where
  tso : pfStepTsoStmt fok
  safe : ∀ (n : Nat) (κs : List Obs) (t : List Expr) (g : GState),
    MRun n ([Expr.power], g0) κs (t, g) → ∀ e, e ∈ t → PrimStep.Reducible (e, g)
  cut : ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
    pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → MRun n ([Expr.power], g0) κ (t, g) →
    SimRel c st t g →
    ∀ (cpu : CPU) (base : Int) (tvs : List (Nat × BitVec 8)) (c' : Wpcfg Pexv6 Efab),
      wpPfStep pstepEv pclsEv (hartAgent cpu) (.LIFetch base tvs) c c' →
      pfStepFacts fok c (hartAgent cpu) (.LIFetch base tvs) →
      pfCutFactsT fcutT TsoShadow.cohSrc st c (hartAgent cpu) (.LIFetch base tvs) →
      ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
        ifetchOk c.pcImg c.pcLog q base tvs ∧
        ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q
  fi : ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
    pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → MRun n ([Expr.power], g0) κ (t, g) →
    SimRel c st t g →
    ∀ (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
      (ib : Ibch) (ws : Wstate) (pr : GSet Nat),
      c.pcAgs[cpu.val]? = some ⟨.PHart cpu (.impure (.ok o) k) rs none ib, ws, pr⟩ →
      (o = .barrier .Barrier_RISCV_i →
         (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) ∧
      (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →
         (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false)

/-- **W4's parameters at M1** (`HypsC` at the trivial cut clause). -/
abbrev Hyps (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (g0 : GState) (c0 : Wpcfg Pexv6 Efab) : Prop :=
  HypsC fok fcutTTriv g0 c0

/-- A cut that does not read the step's cut clause serves at every `fcutT` (M1's `cutOfPristine`
into `HypsC.cut`). -/
theorem cutIgnore {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {g0 : GState} {c0 : Wpcfg Pexv6 Efab}
    (h : ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
      pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → MRun n ([Expr.power], g0) κ (t, g) →
      SimRel c st t g →
      ∀ (cpu : CPU) (base : Int) (tvs : List (Nat × BitVec 8)) (c' : Wpcfg Pexv6 Efab),
        wpPfStep pstepEv pclsEv (hartAgent cpu) (.LIFetch base tvs) c c' →
        pfStepFacts fok c (hartAgent cpu) (.LIFetch base tvs) →
        ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
          ifetchOk c.pcImg c.pcLog q base tvs ∧
          ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q) :
    ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
      pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → MRun n ([Expr.power], g0) κ (t, g) →
      SimRel c st t g →
      ∀ (cpu : CPU) (base : Int) (tvs : List (Nat × BitVec 8)) (c' : Wpcfg Pexv6 Efab),
        wpPfStep pstepEv pclsEv (hartAgent cpu) (.LIFetch base tvs) c c' →
        pfStepFacts fok c (hartAgent cpu) (.LIFetch base tvs) →
        pfCutFactsT fcutT TsoShadow.cohSrc st c (hartAgent cpu) (.LIFetch base tvs) →
        ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
          ifetchOk c.pcImg c.pcLog q base tvs ∧
          ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q :=
  fun st c t g n κ hr hm hR cpu base tvs c' hs hf _ => h st c t g n κ hr hm hR cpu base tvs c' hs hf

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
        ⟨-, -, -, -, -, -, -, -, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
    · rw [devReadNone _ _ _ hda] at hdr; cases hdr
    all_goals exact ⟨rfl, rfl, rfl⟩
  | memWrite n va req =>
    have hda := hW n va req rfl
    rcases h with ⟨-, w, ds', -, hdw, -, -⟩ | ⟨-, w, -, -, -, -, rfl⟩
    · rw [devWriteNone _ _ _ _ hda] at hdw; cases hdw
    all_goals exact ⟨rfl, rfl, rfl⟩
  | regRead r => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | regWrite r v => subst h; exact ⟨rfl, rfl, rfl⟩
  | readRam => exact h.elim
  | writeRam => exact h.elim
  | getCycleCount => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | barrier b => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
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
    (hlive : threadLive g 0) (hno : ∀ pa n, ¬ othersReserve g.m.resv cpu pa n)
    (hsb : g.m.sb cpu = []) :
    (∀ n va req, o = .memRead n va req → devAddr req.pa = false → ramBytes req.pa n) ∧
    (∀ n va req, o = .memWrite n va req → devAddr req.pa = false → ramBytes req.pa n) := by
  obtain ⟨obs, e', g', efs, hs⟩ := hred
  rcases (primStep_hart_inv hs).2 with ⟨-, -, m', σ', -, hh, -⟩ | ⟨hd, -⟩ | ⟨-, -, -, t, hland, -⟩
  · refine ⟨fun n va req ho hda => ?_, fun n va req ho hda => ?_⟩
    · subst ho
      rcases hh with ⟨v, -, hev⟩ | ⟨⟨-, hor | hsb', -⟩, -⟩
      · rcases hev with ⟨-, w, ds', hdr, -, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
        · rw [devReadNone _ _ _ hda] at hdr; cases hdr
        all_goals exact hb
      · exact absurd hor (hno _ _)
      · exact absurd hsb' (MState.not_sbOverlaps_of_nil _ _ _ _ hsb)
    · subst ho
      rcases hh with ⟨v, -, hev⟩ | ⟨⟨hor | hsb, -⟩, -⟩
      · rcases hev with ⟨-, w, ds', -, hdw, -, -⟩ | ⟨hb, -⟩
        · rw [devWriteNone _ _ _ _ hda] at hdw; cases hdw
        all_goals exact hb
      · exact absurd hor (hno _ _)
      · exact hsb.1
  · exact absurd hlive hd
  · -- the land arm (route P): no store is buffered (`rmem`)
    exact absurd hland (MState.not_landOk_of_nil _ _ _ hsb)

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
    (hlive : threadLive g 0) (hno : ∀ pa n, ¬ othersReserve g.m.resv cpu pa n)
    (hsb : g.m.sb cpu = []) :
    (∀ n va req, o = .memRead n va req → devAddr req.pa = true → devBytes req.pa n) ∧
    (∀ n va req, o = .memWrite n va req → devAddr req.pa = true → devBytes req.pa n) := by
  obtain ⟨obs, e', g', efs, hs⟩ := hred
  rcases (primStep_hart_inv hs).2 with ⟨-, -, m', σ', -, hh, -⟩ | ⟨hd, -⟩ | ⟨-, -, -, t, hland, -⟩
  · refine ⟨fun n va req ho hda => ?_, fun n va req ho hda => ?_⟩
    · subst ho
      rcases hh with ⟨v, -, hev⟩ | ⟨⟨-, hor | hsb', -⟩, -⟩
      · rcases hev with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
        · exact hb
        all_goals exact ramNotDev hb hda
      · exact absurd hor (hno _ _)
      · exact absurd hsb' (MState.not_sbOverlaps_of_nil _ _ _ _ hsb)
    · subst ho
      rcases hh with ⟨v, -, hev⟩ | ⟨⟨hor | hsb, -⟩, -⟩
      · rcases hev with ⟨hb, -⟩ | ⟨hb, -⟩
        · exact hb
        all_goals exact ramNotDev hb hda
      · exact absurd hor (hno _ _)
      · exact ramNotDev hsb.1 hda
  · exact absurd hlive hd
  · -- the land arm (route P): no store is buffered (`rmem`)
    exact absurd hland (MState.not_landOk_of_nil _ _ _ hsb)

/-! ## `R-dev` through the hart MMIO transactions and the UART / PLIC programs (F9) -/

theorem diskSideRead {dp : Option (DM Dres)} {vs : List Expr} {dsP dsM : DevStates}
    (h : diskSide dp vs dsP dsM) (pa : PAddr) (n : Nat) (x : BitVec (8 * n)) (dsP' : DevStates)
    (hr : devRead dsP pa n = some (x, dsP')) :
    ∃ dsM', devRead dsM pa n = some (x, dsM') ∧ diskSide dp vs dsP' dsM' := by
  obtain ⟨mr, ot, κ, hvs, hpos, hag⟩ := h
  obtain ⟨dsM', h1, h2⟩ := devAgreeRead hag pa n x dsP' hr
  exact ⟨dsM', h1, mr, ot, κ, hvs, hpos, h2⟩

theorem diskSideWrite {dp : Option (DM Dres)} {vs : List Expr} {dsP dsM : DevStates}
    (h : diskSide dp vs dsP dsM) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (dsP' : DevStates)
    (hw : devWrite dsP pa n w = some dsP') :
    ∃ dsM', devWrite dsM pa n w = some dsM' ∧ diskSide dp vs dsP' dsM' := by
  obtain ⟨mr, ot, κ, hvs, hpos, hag⟩ := h
  obtain ⟨dsM', h1, h2⟩ := devAgreeWrite hag pa n w dsP' hw
  exact ⟨dsM', h1, mr, ot, κ, hvs, hpos, h2⟩

theorem diskSideFdev {dp : Option (DM Dres)} {vs : List Expr} {dsP dsM : DevStates}
    (h : diskSide dp vs dsP dsM) (dv : DevId) (hd : dv ≠ .virtio) (m m' : DevProg dv)
    (dsP' : DevStates) (hf : fdevStep dv m dsP m' dsP') :
    ∃ dsM', fdevStep dv m dsM m' dsM' ∧ diskSide dp vs dsP' dsM' ∧
      fdevObs dv m dsM = fdevObs dv m dsP := by
  obtain ⟨mr, ot, κ, hvs, hpos, hag⟩ := h
  obtain ⟨dsM', h1, h2⟩ := devAgreeFdev hag dv hd m m' dsP' hf
  refine ⟨dsM', h1, ⟨mr, ot, κ, hvs, hpos, h2⟩, ?_⟩
  unfold fdevObs
  rw [devAgreeOther hag hd]

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
(`hartStep .pure`, `σ' = σ.dropResv cpu`), the silent nodes and register reads/writes (`σ' = σ` /
`setReg`), MMIO
(`devRead`/`devWrite`, the footprint from HSafe), and the RAM/fence/announce nodes through
`pfStepTso`. -/
theorem simNode {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {g0 : GState} {c0 : Wpcfg Pexv6 Efab}
    (hH : HypsC fok fcutT g0 c0) {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)}
    {t : List Expr} {g : GState} {n : Nat} {κ : List Obs} {i : Nat} {l : Wlabel}
    (hR : SimRel c st t g) (hreach : MRun n ([Expr.power], g0) κ (t, g))
    (hrun : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c)
    (hs : wpPfStep pstepEv pclsEv i l c c') (hf : pfStepFacts fok c i l)
    (hfT : pfLoadFactsT TsoShadow.cohSrc st c i l)
    (hcf : pfCutFactsT fcutT TsoShadow.cohSrc st c i l) (hk : kindOk c i l c' .node)
    (hadj : pairAdjacent (st ++ (i, l) :: rest))
    (hex : ∀ aq base tvs asrc, l = .LExLoad aq base tvs asrc →
      exclOkTs c.pcLog i base (tvs.map Prod.fst) (c.pcLog.length + 1)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      m ≤ 1 ∧ MRun m (t, g) (pfStepObs c i .node) (t', g') ∧ SimRel c' (st ++ [(i, l)]) t' g' := by
  have hR0 := hR
  obtain ⟨hgen, hpow, ⟨H, vs, dp, dws, dpr, ht, hlen, hharts, hdisk, hDS⟩, hmem, hview,
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
      (∀ c'', c'' ≠ cpu → σ'.regs c'' = g.m.regs c'') → diskSide dp vs c'.pcDev.efDev σ'.devs →
      rmem c' (st ++ [(cpu.val, l)]) σ' → viewRel TsoShadow.cohSrc σ' (st ++ [(cpu.val, l)]) →
      MRun nn (t, g) (pfStepObs c cpu.val .node)
        (t.set (cpu.val + 1) (.hart 0 cpu m1), { g with m := σ' }) →
      ∃ (m : Nat) (t' : List Expr) (g' : GState),
        m ≤ 1 ∧ MRun m (t, g) (pfStepObs c cpu.val .node) (t', g') ∧
        SimRel c' (st ++ [(cpu.val, l)]) t' g' := by
    intro m1 _ σ' nn hm1 hnn hfn' hrc hro hdv hmem' hview' hrun'
    subst hm1
    refine ⟨nn, _, _, hnn, hrun', hgen, hpow, ⟨updH H cpu m', vs, dp, dws, dpr, ?_, ?_, ?_, ?_, hdv⟩,
      hmem', hview', authStep hs hauth, ownCohStep pstepEv pclsEv _ _ c c' hcoh hs⟩
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
      (by rw [hd'']; exact hDS) hm1 hv1 ?_
    rw [hobs, ht, poolHartSet, updHSelf]
    exact mrunRefl _
  | none =>
  -- the hart's own node
  generalize hm : H cpu = mm at hn hlkc
  cases mm with
  | pure a =>
    -- THE BOUNDARY: the hart's reservation is cleared (W-RSV)
    obtain ⟨tick, rfl, rfl, rfl, rfl, hd'', -, -⟩ := hn
    obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := g.m) hs trivial (Or.inl rfl) hadj hmem hview hauth
      hcoh rfl rfl rfl (sameReadRefl _)
    exact post _ none (g.m.dropResv cpu) 1 rfl (by omega) (fun _ h => by cases h) rfl (fun _ _ => rfl)
      (by rw [hd'']; exact hDS) (rmemDropResv cpu hm1) (viewRelSame hv1 (sameReadDropResv g.m cpu))
      (hartRun ht hgen hpow cpu (by rw [hm]; exact hlkc)
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
        SimRel c' (st ++ [(cpu.val, l)]) t' g' := by
    intro v hev hl hm' hors hfn' hd''
    subst hl hm' hors hfn'
    obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := g.m) hs trivial (Or.inl rfl) hadj hmem hview hauth
      hcoh rfl rfl rfl (sameReadRefl _)
    exact post _ none g.m 1 rfl (by omega) (fun _ h => by cases h) rfl (fun _ _ => rfl) (by rw [hd'']; exact hDS)
      hm1 hv1 (hartRun ht hgen hpow cpu (by rw [hm]; exact hlkc)
        (by rw [hm]; exact Or.inl ⟨v, rfl, hev⟩))
  have mmio : ∀ (v : o.ret) (dsM' : DevStates),
      (∀ n va req, o = .memRead n va req → devAddr req.pa = true) →
      (∀ n va req, o = .memWrite n va req → devAddr req.pa = true) →
      ((∀ n va req, o = .memRead n va req → devBytes req.pa n) →
        (∀ n va req, o = .memWrite n va req → devBytes req.pa n) →
        evStep cpu o g.m v { g.m with devs := dsM' }) →
      diskSide dp vs c'.pcDev.efDev dsM' →
      lbInert l = true → frameLbl l → m' = k v → ors = none → fn' = none →
      ∃ (m : Nat) (t' : List Expr) (g' : GState),
        m ≤ 1 ∧ MRun m (t, g) (pfStepObs c cpu.val .node) (t', g') ∧
        SimRel c' (st ++ [(cpu.val, l)]) t' g' := by
    intro v dsM' hdaR hdaW hev hdsM hin hfr hm' hors hfn'
    subst hm' hors hfn'
    have hred := hH.safe n κ t g hreach _
      (List.mem_of_getElem? (by rw [ht]; exact poolHart H c.pcDev vs cpu))
    rw [hm] at hred
    obtain ⟨hdbR, hdbW⟩ := devOfSafe hred hlive (notOthers hmem hadj) (hmem.2.2.2.2 cpu)
    have hev' := hev (fun n va req ho => hdbR n va req ho (hdaR n va req ho))
      (fun n va req ho => hdbW n va req ho (hdaW n va req ho))
    obtain ⟨hm1, hv1, -, -⟩ := memFrame (σ' := { g.m with devs := dsM' }) hs hfr
      (Or.inl hin) hadj hmem hview hauth hcoh rfl rfl rfl (sameReadDevs _ _)
    exact post _ none { g.m with devs := dsM' } 1 rfl (by omega) (fun _ h => by cases h) rfl
      (fun _ _ => rfl) hdsM hm1 hv1
      (hartRun ht hgen hpow cpu (by rw [hm]; exact hlkc)
        (by rw [hm]; exact Or.inl ⟨v, rfl, hev'⟩))
  have tso : l ≠ .LSilent → (∀ kd ba bs sa sv, l ≠ .LDev kd ba bs sa sv) →
      c'.pcDev.efDev = c.pcDev.efDev → fnOk fn' →
      (∀ n va req, o = .memRead n va req → devAddr req.pa = false) →
      (∀ n va req, o = .memWrite n va req → devAddr req.pa = false) →
      ors.getD (g.m.regs cpu) = oRegs cpu o g.m cpu →
      ∃ (m : Nat) (t' : List Expr) (g' : GState),
        m ≤ 1 ∧ MRun m (t, g) (pfStepObs c cpu.val .node) (t', g') ∧
        SimRel c' (st ++ [(cpu.val, l)]) t' g' := by
    intro hl1 hl2 hd'' hfn' hdaR hdaW hors
    have hred := hH.safe n κ t g hreach _
      (List.mem_of_getElem? (by rw [ht]; exact poolHart H c.pcDev vs cpu))
    rw [hm] at hred
    obtain ⟨hrbR, hrbW⟩ := ramOfSafe hred hlive (notOthers hmem hadj) (hmem.2.2.2.2 cpu)
    obtain ⟨hfi1, hfi2⟩ := hH.fi st c t g n κ hrun hreach hR0 cpu o k (g.m.regs cpu) ib ws pr hlkc
    have hps : pstepEv (.PHart cpu (.impure (.ok o) k) (g.m.regs cpu) none ib) c.pcDev l
        (.PHart cpu m' (ors.getD (g.m.regs cpu)) fn' (oib.getD ib)) c'.pcDev :=
      ⟨rfl, ors, oib, obar, rfl, rfl, Or.inl ⟨hn, hd⟩⟩
    obtain ⟨v, σ', hev, ⟨rs'', fn'', ib'', hp'⟩, hmem', hview'⟩ :=
      hH.tso c c' st g.m cpu o k (g.m.regs cpu) none ib l _ c'.pcDev rest hps hs hadj ⟨hf, hfT⟩
        (fun n va req ho => hrbR n va req ho (hdaR n va req ho))
        (fun n va req ho => hrbW n va req ho (hdaW n va req ho)) hmem hview hauth
        (fun base tvs hl => by
          subst hl; exact hH.cut st c t g n κ hrun hreach hR0 cpu base tvs c' hs hf hcf)
        (fun aq base tvs asrc hl => ⟨hcoh, hex aq base tvs asrc hl⟩) rfl hl1 hl2 hfi1 hfi2
    simp only [Pexv6.PHart.injEq] at hp'
    obtain ⟨-, hmk, -, -, -⟩ := hp'
    obtain ⟨hdv, hrg, -⟩ := evStepShape cpu o g.m σ' v hev hdaR hdaW
    exact post (k v) fn' σ' 1 hmk (by omega) hfn' (by rw [hrg, hors]) (fun c'' hc => by rw [hrg, oRegsOther _ _ _ _ hc])
      (by rw [hd'', hdv]; exact hDS) hmem' hview'
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
      (fun c'' hc => by simp [hc]) (by rw [hd'']; exact hDS) hm1 hv1
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
      obtain ⟨dsM', hdrM, hdsM⟩ := diskSideRead hDS req.pa nb w _ hdr
      refine mmio (.Ok (w, none)) dsM' (fun _ _ _ ho => by cases ho; exact hda)
        (fun _ _ _ ho => by cases ho) (fun hdb _ => Or.inl ⟨hdb nb va req rfl, w, dsM',
          hdrM, rfl, rfl⟩) hdsM (by rw [hl]; rfl) (by rw [hl]; trivial) hm' hors hfn'
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
        obtain ⟨dsM', hdwM, hdsM⟩ := diskSideWrite hDS req.pa nb v _ hdw
        exact mmio (.Ok (some true)) dsM' (fun _ _ _ ho => by cases ho)
          (fun _ _ _ ho => by cases ho; exact hda)
          (fun _ hdb => Or.inl ⟨hdb nb va req rfl, v, dsM', hv, hdwM, rfl, rfl⟩) hdsM
          (by rw [hl]; rfl) (by rw [hl]; trivial) hm' hors hfn'
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
            (by rw [hd'']; exact hDS) hm1 hv1 ?_
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
    have hl1 : l ≠ .LSilent ∧ ∀ kd ba bs sa sv, l ≠ .LDev kd ba bs sa sv := by
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
theorem diskAgentIdx {c : Wpcfg Pexv6 Efab}
    {st : List (Nat × Wlabel)} {t : List Expr} {g : GState} (hR : SimRel c st t g) {i : Nat}
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
    {c c' : Wpcfg Pexv6 Efab}
    {st rest : List (Nat × Wlabel)} {t : List Expr} {g : GState} {i : Nat} {l : Wlabel}
    {k : SKind} (hR : SimRel c st t g) (hs : wpPfStep pstepEv pclsEv i l c c')
    (hk : kindOk c i l c' k) (hkd : k ≠ .node ∧ k ≠ .wire ∧ k ≠ .disk)
    (hadj : pairAdjacent (st ++ (i, l) :: rest)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      m ≤ 1 ∧ MRun m (t, g) (pfStepObs c i k) (t', g') ∧ SimRel c' (st ++ [(i, l)]) t' g' := by
  have hR0 := hR
  obtain ⟨hgen, hpow, ⟨H, vs, dp, dws, dpr, ht, hlen, hharts, hdisk, hDS⟩, hmem, hview,
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
    have hl : l = .LDev .dev 0 [] [] [] := by
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
    obtain ⟨dsM', hfdM, hDS', hobs⟩ := diskSideFdev hDS (.uart u) nofun _ _ _ hfd
    have hds := devStepOfFdev 0 (.uart u) (efU c.pcDev u) m' g.m.devs dsM' g.m rfl hfdM
    have hst := primStep_dev_live (gen := 0) hlive hds
    have hrun := mrunOne (t := t) (j := uartThr u) (by rw [ht]; exact poolUart H c.pcDev vs u) hst
    obtain ⟨hm1, hv1, ha1, hc1⟩ := frame dsM'
    have hdev' : c'.pcDev.efDev = ds' := by rw [hd']; cases u <;> rfl
    refine ⟨1, t.set (uartThr u) (.dev 0 (.uart u) rootTask m'), { g with m := { g.m with devs := dsM' } },
      Nat.le_refl _, by rw [hobs] at hrun; simpa [pfStepObs, uartObs] using hrun, hgen, hpow,
      ⟨H, vs, dp, ws', dpr, ?_, by rw [hags, List.length_set, hlen], fun cpu => ?_, hags'.1,
        by rw [hdev']; exact hDS'⟩, hm1, hv1, ha1, hc1⟩
    · rw [ht, poolUartSet H c.pcDev vs u m' ds', hd']
    · rw [hags'.2 cpu]; exact hharts cpu
  | gate =>
    obtain ⟨-, -, m', ds', hfd, hd'⟩ := hks
    obtain ⟨dsM', hfdM, hDS', -⟩ := diskSideFdev hDS .plic nofun _ _ _ hfd
    have hds := devStepOfFdev 0 .plic c.pcDev.efPlic m' g.m.devs dsM' g.m rfl hfdM
    rw [fdevObsPlic] at hds
    have hst := primStep_dev_live (gen := 0) hlive hds
    have hrun := mrunOne (t := t) (j := plicThr) (by rw [ht]; exact poolPlic H c.pcDev vs) hst
    obtain ⟨hm1, hv1, ha1, hc1⟩ := frame dsM'
    have hdev' : c'.pcDev.efDev = ds' := by rw [hd']
    refine ⟨1, t.set plicThr (.dev 0 .plic rootTask m'), { g with m := { g.m with devs := dsM' } },
      Nat.le_refl _, by simpa [pfStepObs] using hrun, hgen, hpow,
      ⟨H, vs, dp, ws', dpr, ?_, by rw [hags, List.length_set, hlen], fun cpu => ?_, hags'.1,
        by rw [hdev']; exact hDS'⟩, hm1, hv1, ha1, hc1⟩
    · rw [ht, poolPlicSet H c.pcDev vs m' ds', hd']
    · rw [hags'.2 cpu]; exact hharts cpu

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
theorem simWire {c c' : Wpcfg Pexv6 Efab}
    {st rest : List (Nat × Wlabel)} {t : List Expr} {g : GState} {i : Nat} {l : Wlabel}
    (hR : SimRel c st t g) (hs : wpPfStep pstepEv pclsEv i l c c') (hk : kindOk c i l c' .wire)
    (hadj : pairAdjacent (st ++ (i, l) :: rest)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      m ≤ 1 ∧ MRun m (t, g) (pfStepObs c i .wire) (t', g') ∧ SimRel c' (st ++ [(i, l)]) t' g' := by
  obtain ⟨hgen, hpow, ⟨H, vs, dp, dws, dpr, ht, hlen, hharts, hdisk, hDS⟩, hmem, hview,
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
    hmem hview hauth hcoh hpm hpl' hpr hpsr (by unfold pinM; split <;> rfl)
  refine ⟨1, t.set plicThr (.dev 0 .plic rootTask (kp ())), { g with m := pinM g.m cpu mm b },
    Nat.le_refl _, by simpa [pfStepObs] using hrun, hgen, hpow,
    ⟨H, vs, dp, dws, dpr, ?_, by rw [hags, List.length_set, hlen], fun c'' => ?_, ?_, ?_⟩,
    hm1, hv1, ha1, hc1⟩
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
    exact hDS

/-! ## (F9) THE DISK ROWS

The disk agent's own program (`pdiskProg`, kind `.disk`) against MachCSL's virtio threads
(`Virtio.body` on the root thread `NCPU + 4`, `Virtio.serve h` on the forked tasks after it):
`diskSide`'s position relation `PosRel` names, for every stopping point of a pf burst, where the
MachCSL root and the live serving task are; each pf step is a block of MachCSL steps of those
threads (`VRun`), with the plan's counts (§C W4 F9 "Bookkeeping"): START 1 → 3 (the root's
restart folded in), the avail/ring reads 1 → 1, the POP 1 → 4 (`get`, guard-pop, `fork`, the
task's first `get`) or 1 → 1 refused, a descriptor/header read 1 → 1, the OUT capture read 1 → 3
(free) / 1 → 1 (held) / 1 → 0 (no longer in flight), the IN fill 1 → 3, the status byte 1 → 2 /
3 / 5, the used element 1 → 3 + 5k (the `k` cached sectors drained by the root loop, 5 steps
each, before the gate), the used index 1 → 1, an ABORT 1 → 0 (+ the folded moves MachCSL
performs before its blocking guard), `DFence` / `DRet` / the stall 1 → 0. -/

/-! ### The virtio threads in the pool -/

theorem poolVirtio (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (j : Nat) :
    (poolOf H F vs)[NCPU + 4 + j]? = vs[j]? := by
  rw [show NCPU + 4 + j = NCPU + 1 + (j + 1 + 1 + 1) by omega, poolTail]
  simp only [List.getElem?_cons_succ]

theorem poolVirtioSet (H : CPU → SailM Unit) (F : Efab) (vs : List Expr) (j : Nat) (e : Expr) :
    (poolOf H F vs).set (NCPU + 4 + j) e = poolOf H F (vs.set j e) := by
  rw [show NCPU + 4 + j = NCPU + 1 + (j + 1 + 1 + 1) by omega, poolTailSet]
  simp only [List.set_cons_succ]
  rfl

theorem poolAppend (H : CPU → SailM Unit) (F : Efab) (vs es : List Expr) :
    poolOf H F vs ++ es = poolOf H F (vs ++ es) := by
  simp [poolOf]

/-- **A run of the virtio threads alone** (F9): from any configuration over `vs` at `σ` (power
on, generation 0, any harts and fabric programs), `n` silent steps to `vs'` at `σ'`. -/
def VRun (n : Nat) (vs : List Expr) (σ : MState) (vs' : List Expr) (σ' : MState) : Prop :=
  ∀ (H : CPU → SailM Unit) (F : Efab) (g : GState), g.m = σ → threadLive g 0 →
    MRun n (poolOf H F vs, g) [] (poolOf H F vs', { g with m := σ' })

theorem vrunRefl (vs : List Expr) (σ : MState) : VRun 0 vs σ vs σ := by
  intro H F g hg _
  subst hg
  exact mrunRefl _

theorem vrunTrans {a b : Nat} {vs1 vs2 vs3 : List Expr} {σ1 σ2 σ3 : MState}
    (h1 : VRun a vs1 σ1 vs2 σ2) (h2 : VRun b vs2 σ2 vs3 σ3) : VRun (a + b) vs1 σ1 vs3 σ3 := by
  intro H F g hg hl
  have r1 := h1 H F g hg hl
  have r2 := h2 H F { g with m := σ2 } rfl hl
  exact mrunTrans r1 r2

/-- One step of the virtio thread at position `j` of `vs`. -/
theorem vGen {vs : List Expr} {σ σ' : MState} {j : Nat} {tid : TaskId} {m m' : DevProg .virtio}
    {efs : List Expr} (hj : vs[j]? = some (.dev 0 .virtio tid m))
    (hd : devStep 0 .virtio tid m σ [] m' σ' efs) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio tid m') ++ efs) σ' := by
  intro H F g hg hl
  subst hg
  have hs := primStep_dev_live (gen := 0) hl hd
  have := mrunOne (t := poolOf H F vs) (j := NCPU + 4 + j) (by rw [poolVirtio]; exact hj) hs
  rw [poolVirtioSet, poolAppend] at this
  exact this

theorem vGet {vs : List Expr} {σ : MState} {j : Nat} {tid : TaskId}
    {k : DevSt .virtio → DevProg .virtio} (hj : vs[j]? = some (.dev 0 .virtio tid (.op .get k))) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio tid (k (σ.devs.st .virtio)))) σ := by
  have := vGen (σ := σ) (σ' := σ) (efs := []) hj (Or.inl ⟨σ.devs.st .virtio, rfl, rfl, rfl, rfl, rfl⟩)
  simpa using this

theorem vChoose {vs : List Expr} {σ : MState} {j : Nat} {tid : TaskId}
    {k : Nat → DevProg .virtio} (n : Nat) (hj : vs[j]? = some (.dev 0 .virtio tid (.op .choose k))) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio tid (k n))) σ := by
  have := vGen (σ := σ) (σ' := σ) (efs := []) hj (Or.inl ⟨n, rfl, rfl, rfl, rfl⟩)
  simpa using this

theorem vStep {vs : List Expr} {σ : MState} {j : Nat} {tid : TaskId}
    {f : DevSt .virtio → Option (DevSt .virtio × List DevObs)} {k : Unit → DevProg .virtio}
    {s' : VirtioState} (hj : vs[j]? = some (.dev 0 .virtio tid (.op (.step f) k)))
    (hf : f (σ.devs.st .virtio) = some (s', [])) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio tid (k ()))) (σ.setDev .virtio s') := by
  have := vGen (σ := σ) (σ' := σ.setDev .virtio s') (efs := []) hj
    (Or.inl ⟨(), rfl, s', [], hf, rfl, rfl, rfl, rfl⟩)
  simpa using this

theorem vRead {vs : List Expr} {σ : MState} {j : Nat} {tid : TaskId} {pa : PAddr} {n : Nat}
    {k : BitVec (8 * n) → DevProg .virtio} (w : BitVec (8 * n))
    (hj : vs[j]? = some (.dev 0 .virtio tid (.op (.dmaRead pa n) k))) (hv : dmaView σ pa n w) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio tid (k w))) σ := by
  have := vGen (σ := σ) (σ' := σ) (efs := []) hj (Or.inl ⟨w, rfl, hv, rfl, rfl, rfl⟩)
  simpa using this

theorem vWrite {vs : List Expr} {σ : MState} {j : Nat} {tid : TaskId}
    {G : DevSt .virtio → Option (DevSt .virtio)} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    {k : Unit → DevProg .virtio} {s' : VirtioState}
    (hj : vs[j]? = some (.dev 0 .virtio tid (.op (.dmaWrite G pa n w) k)))
    (hg : G (σ.devs.st .virtio) = some s') (hram : ramBytes pa n) (hres : ¬ anyReserve σ.resv pa n) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio tid (k ()))) ((σ.storeDma pa n w).setDev .virtio s') := by
  have := vGen (σ := σ) (σ' := (σ.storeDma pa n w).setDev .virtio s') (efs := []) hj
    (Or.inl ⟨(), rfl, rfl, rfl, Or.inl ⟨s', hg, rfl, hram, hres, rfl⟩⟩)
  simpa using this

theorem vSkip {vs : List Expr} {σ : MState} {j : Nat} {tid : TaskId}
    {G : DevSt .virtio → Option (DevSt .virtio)} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    {k : Unit → DevProg .virtio}
    (hj : vs[j]? = some (.dev 0 .virtio tid (.op (.dmaWrite G pa n w) k)))
    (hg : G (σ.devs.st .virtio) = none ∨ ¬ ramBytes pa n) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio tid (k ()))) σ := by
  have := vGen (σ := σ) (σ' := σ) (efs := []) hj (Or.inl ⟨(), rfl, rfl, rfl, Or.inr ⟨hg, rfl⟩⟩)
  simpa using this

theorem vFork {vs : List Expr} {σ : MState} {j : Nat} {tid : TaskId} {tk : DevTask .virtio}
    {k : TaskId → DevProg .virtio} (hj : vs[j]? = some (.dev 0 .virtio tid (.op (.fork tk) k))) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio tid (k (σ.devrt .virtio).next)) ++
        [.dev 0 .virtio (σ.devrt .virtio).next ((devSig .virtio).task tk)])
      (σ.setRt .virtio { σ.devrt .virtio with next := (σ.devrt .virtio).next + 1 }) :=
  vGen hj (Or.inl ⟨_, rfl, rfl, rfl, rfl, rfl⟩)

theorem vRestart {vs : List Expr} {σ : MState} {j : Nat}
    (hj : vs[j]? = some (.dev 0 .virtio rootTask (.pure ()))) :
    VRun 1 vs σ (vs.set j (.dev 0 .virtio rootTask (devSig .virtio).body)) σ := by
  have := vGen (σ := σ) (σ' := σ) (efs := []) hj ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  simpa using this

/-! ### What the virtio threads move: the device state and the task bookkeeping only -/

/-- `σ'` differs from `σ` at most in the device states, the task bookkeeping. -/
structure DevOnly (σ σ' : MState) : Prop where
  regs : σ'.regs = σ.regs
  mem : σ'.mem = σ.mem
  log : σ'.log = σ.log
  resv : σ'.resv = σ.resv
  read : sameRead σ σ'
  xs : σ'.sb = σ.sb

theorem devOnlyRefl (σ : MState) : DevOnly σ σ := ⟨rfl, rfl, rfl, rfl, sameReadRefl σ, rfl⟩

theorem devOnlyTrans {σ1 σ2 σ3 : MState} (h1 : DevOnly σ1 σ2) (h2 : DevOnly σ2 σ3) :
    DevOnly σ1 σ3 :=
  ⟨h2.regs.trans h1.regs, h2.mem.trans h1.mem, h2.log.trans h1.log, h2.resv.trans h1.resv,
    sameReadTrans h1.read h2.read, h2.xs.trans h1.xs⟩

theorem devOnlySetDev (σ : MState) (d : DevId) (s : DevSt d) : DevOnly σ (σ.setDev d s) :=
  ⟨rfl, rfl, rfl, rfl, sameReadSetDev σ d s, rfl⟩

theorem devOnlySetRt (σ : MState) (d : DevId) (rt : DevRt) : DevOnly σ (σ.setRt d rt) :=
  ⟨rfl, rfl, rfl, rfl, sameReadSetRt σ d rt, rfl⟩

theorem rmemCongr {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {σ σ' : MState}
    (h : rmem c st σ) (hd : DevOnly σ σ') : rmem c st σ' := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩ := h
  refine ⟨⟨by rw [hd.log]; exact h1, by rw [hd.log]; exact h2⟩, h3, by rw [hd.mem]; exact h4,
    fun cpu => by rw [hd.resv]; exact h5 cpu, fun cpu => by rw [hd.xs]; exact h6 cpu⟩

/-- **The disk's frame rows** (`DRead`, `DFence`, `LDev`, `LSilent`): the MachCSL state with the
same memory fields is related (W2a `pfFrameRowMem`, W2b `viewRelForeign`). -/
theorem diskFrame {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ σ' : MState} (hs : wpPfStep pstepEv pclsEv NCPU l c c') (hl : frameLbl l)
    (hadj : pairAdjacent (st ++ (NCPU, l) :: rest)) (hR : rmem c st σ)
    (hV : viewRel TsoShadow.cohSrc σ st) (hd : DevOnly σ σ') :
    rmem c' (st ++ [(NCPU, l)]) σ' ∧ viewRel TsoShadow.cohSrc σ' (st ++ [(NCPU, l)]) :=
  ⟨(pfFrameRowMem pstepEv pclsEv c c' st rest σ NCPU l hR hs hl hadj).2.2 σ' hd.mem hd.log hd.resv hd.xs,
    viewRelForeign _ σ σ' st NCPU l (fun c => diskNotHart c) hV hd.read⟩

/-- **The disk's store row** (a `DWriteDev` STORE): the DMA store with the device's move, at a
MachCSL state that moved only the devices since the pf step's pre-state (W2a
`pfDWriteDevRowMem`, W2b `rowDiskWrite`). -/
theorem diskStore {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {σ σ1 : MState}
    {pa : PAddr} {n : Nat} {w : BitVec (8 * n)} {data : List (BitVec 8)} (s' : VirtioState)
    (hs : wpPfStep pstepEv pclsEv NCPU (.LStore false (paZ pa) data [] []) c c')
    (hadj : pairAdjacent (st ++ (NCPU, .LStore false (paZ pa) data [] []) :: rest))
    (hR : rmem c st σ) (hV : viewRel TsoShadow.cohSrc σ st) (hd : DevOnly σ σ1)
    (hram : ramBytes pa n) (hdl : data.length = n) (hn : n ≠ 0)
    (hb : ∀ j, j < n → data[j]? = some (nthByte w j)) :
    ¬ anyReserve σ1.resv pa n ∧
      rmem c' (st ++ [(NCPU, .LStore false (paZ pa) data [] [])]) ((σ1.storeDma pa n w).setDev .virtio s') ∧
      viewRel TsoShadow.cohSrc ((σ1.storeDma pa n w).setDev .virtio s')
        (st ++ [(NCPU, .LStore false (paZ pa) data [] [])]) := by
  obtain ⟨h1, h2⟩ := pfDWriteDevRowMem pstepEv pclsEv c c' st rest σ1 false (paZ pa) data [] [] pa n w
    .virtio s' (rmemCongr hR hd) hs hadj rfl hram hdl hn hb
  exact ⟨h1, h2, rowDiskWrite _ σ1 st pa n w .virtio s' (paZ pa) data (viewRelSame hV hd.read)⟩

theorem bytesOfGet {n : Nat} (w : BitVec (8 * n)) (j : Nat) (hj : j < n) :
    (bytesOf w)[j]? = some (nthByte w j) := by
  simp [bytesOf, List.getElem?_map, List.getElem?_range hj]

theorem bvOfBytesGet (n : Nat) (data : List (BitVec 8)) (hd : data.length = n) (j : Nat)
    (hj : j < n) : data[j]? = some (nthByte (bvOfBytes n data) j) := by
  rw [nthByte_bvOfBytes n data j hj, List.getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- The pf disk read reads the top (`diskLatOk`), so it is a `dmaView` of MachCSL — byte by
byte, a wrapped byte (past `2^64`) included when it misses DRAM (`hwrap`). -/
theorem dmaViewOf {c c' : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {σ : MState} {aq : Bool}
    {pa : PAddr} {n : Nat} {tvs : List (Nat × BitVec 8)} (hR : rmem c st σ)
    (hs : wpPfStep pstepEv pclsEv NCPU (.LLoad aq false (paZ pa) tvs []) c c')
    (hfT : pfLoadFactsT TsoShadow.cohSrc st c NCPU (.LLoad aq false (paZ pa) tvs []))
    (htl : tvs.length = n) (hwrap : paZ pa + (n : Int) ≤ 2 ^ 64 + (ramBase : Int)) :
    dmaView σ pa n (bvOfBytes n (tvs.map Prod.snd)) := by
  intro j hj b hbt
  have hlb : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
      logByte c.pcImg c.pcLog t (paZ pa + (j : Int)) = some v := by
    cases hs with
    | PFLoad _ _ _ _ _ _ _ _ _ _ _ hrd => exact fun j t v hj => (hrd j t v hj).1
  have hlat := hfT.2 rfl
  by_cases hin : inRam (pa + BitVec.ofNat 64 j) 1
  · have hlt : pa.toNat + j < 2 ^ 64 := by
      refine Classical.byContradiction fun hge => ?_
      have hnat := BitVec.toNat_add pa (BitVec.ofNat 64 j)
      rw [BitVec.toNat_ofNat] at hnat
      simp only [inRam, ramBase, ramEnd] at hin
      simp only [paZ, ramBase] at hwrap
      have := pa.isLt
      omega
    obtain ⟨tv, htj⟩ : ∃ tv, tvs[j]? = some tv := by
      cases h : tvs[j]? with
      | none => rw [List.getElem?_eq_none_iff] at h; omega
      | some tv => exact ⟨tv, rfl⟩
    obtain ⟨t, v⟩ := tv
    have hlj := hlat j t (by simp [htj])
    have hv := hlb j t v htj
    have htop := (histOfTop c.pcImg c.pcLog (accAddr (paZ pa) j) v).2 ⟨t, hlj, hv⟩
    have hpz : paZ (pa + BitVec.ofNat 64 j) = accAddr (paZ pa) j := by
      simp only [paZ, accAddr]
      rw [toNatAdd pa j hlt]
      omega
    rw [hR.2.2.1.1 _ hin, hpz] at hbt
    simp only [Option.bind_some] at hbt
    rw [htop] at hbt
    have hb : nthByte (bvOfBytes n (tvs.map Prod.snd)) j = v := by
      rw [nthByte_bvOfBytes n _ j hj]
      simp [List.getD, htj]
    rw [hb]
    exact Option.some.inj hbt
  · rw [hR.2.2.1.2 _ hin] at hbt; cases hbt

/-- A read of at most 16 bytes never wraps into DRAM. -/
theorem smallNoWrap (pa : PAddr) (n : Nat) (hn : n ≤ 16) :
    paZ pa + (n : Int) ≤ 2 ^ 64 + (ramBase : Int) := by
  have := pa.isLt
  simp only [paZ, ramBase]
  omega

/-! ### The root thread (position 0) and the live task (position `j + 1`) -/

theorem setSelfOf {ts : List Expr} {j : Nat} {e : Expr} (h : ts[j]? = some e) : ts.set j e = ts := by
  have hlt : j < ts.length := by
    rcases Nat.lt_or_ge j ts.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at h; cases h
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_set]
  split
  · next hij => subst hij; first | rw [if_pos hlt, h] | exact h.symm
  · rfl

theorem rGet {ts : List Expr} {σ : MState} {k : DevSt .virtio → DevProg .virtio} {m : DevProg .virtio}
    (hm : m = .op .get k) :
    VRun 1 (Expr.dev 0 .virtio rootTask m :: ts) σ
      (Expr.dev 0 .virtio rootTask (k (σ.devs.st .virtio)) :: ts) σ :=
  vGet (j := 0) (by rw [hm]; rfl)

theorem rChoose {ts : List Expr} {σ : MState} {k : Nat → DevProg .virtio} {m : DevProg .virtio}
    (n : Nat) (hm : m = .op .choose k) :
    VRun 1 (Expr.dev 0 .virtio rootTask m :: ts) σ (Expr.dev 0 .virtio rootTask (k n) :: ts) σ :=
  vChoose (j := 0) n (by rw [hm]; rfl)

theorem rStep {ts : List Expr} {σ : MState} {f : DevSt .virtio → Option (DevSt .virtio × List DevObs)}
    {k : Unit → DevProg .virtio} {m : DevProg .virtio} {s' : VirtioState} (hm : m = .op (.step f) k)
    (hf : f (σ.devs.st .virtio) = some (s', [])) :
    VRun 1 (Expr.dev 0 .virtio rootTask m :: ts) σ (Expr.dev 0 .virtio rootTask (k ()) :: ts)
      (σ.setDev .virtio s') :=
  vStep (j := 0) (by rw [hm]; rfl) hf

theorem rRead {ts : List Expr} {σ : MState} {pa : PAddr} {n : Nat} {k : BitVec (8 * n) → DevProg .virtio}
    {m : DevProg .virtio} (w : BitVec (8 * n)) (hm : m = .op (.dmaRead pa n) k)
    (hv : dmaView σ pa n w) :
    VRun 1 (Expr.dev 0 .virtio rootTask m :: ts) σ (Expr.dev 0 .virtio rootTask (k w) :: ts) σ :=
  vRead (j := 0) w (by rw [hm]; rfl) hv

theorem rRestart {ts : List Expr} {σ : MState} :
    VRun 1 (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ
      (Expr.dev 0 .virtio rootTask Virtio.body :: ts) σ :=
  vRestart (j := 0) rfl

theorem tSetSet {x : Expr} {ts : List Expr} {j : Nat} (e e' : Expr) :
    (x :: ts.set j e).set (j + 1) e' = x :: ts.set j e' := by
  simp [List.set_set]

theorem tAt {x : Expr} {ts : List Expr} {j : Nat} (hj : j < ts.length) (e : Expr) :
    (x :: ts.set j e)[j + 1]? = some e := by
  simp [List.getElem?_set_self hj]

theorem tGet {x : Expr} {ts : List Expr} {j : Nat} {tid : TaskId} {σ : MState}
    {k : DevSt .virtio → DevProg .virtio} {m : DevProg .virtio} (hj : j < ts.length)
    (hm : m = .op .get k) :
    VRun 1 (x :: ts.set j (.dev 0 .virtio tid m)) σ
      (x :: ts.set j (.dev 0 .virtio tid (k (σ.devs.st .virtio)))) σ := by
  have := vGet (vs := x :: ts.set j (.dev 0 .virtio tid m)) (j := j + 1) (tid := tid) (σ := σ) (k := k)
    (by rw [tAt hj, hm])
  rwa [tSetSet] at this

theorem tStep {x : Expr} {ts : List Expr} {j : Nat} {tid : TaskId} {σ : MState}
    {f : DevSt .virtio → Option (DevSt .virtio × List DevObs)} {k : Unit → DevProg .virtio}
    {m : DevProg .virtio} {s' : VirtioState} (hj : j < ts.length) (hm : m = .op (.step f) k)
    (hf : f (σ.devs.st .virtio) = some (s', [])) :
    VRun 1 (x :: ts.set j (.dev 0 .virtio tid m)) σ
      (x :: ts.set j (.dev 0 .virtio tid (k ()))) (σ.setDev .virtio s') := by
  have := vStep (vs := x :: ts.set j (.dev 0 .virtio tid m)) (j := j + 1) (tid := tid) (σ := σ) (f := f) (k := k)
    (by rw [tAt hj, hm]) hf
  rwa [tSetSet] at this

theorem tRead {x : Expr} {ts : List Expr} {j : Nat} {tid : TaskId} {σ : MState} {pa : PAddr}
    {n : Nat} {k : BitVec (8 * n) → DevProg .virtio} {m : DevProg .virtio} (hj : j < ts.length)
    (w : BitVec (8 * n)) (hm : m = .op (.dmaRead pa n) k) (hv : dmaView σ pa n w) :
    VRun 1 (x :: ts.set j (.dev 0 .virtio tid m)) σ (x :: ts.set j (.dev 0 .virtio tid (k w))) σ := by
  have := vRead (vs := x :: ts.set j (.dev 0 .virtio tid m)) (j := j + 1) (tid := tid) (σ := σ) (k := k) w
    (by rw [tAt hj, hm]) hv
  rwa [tSetSet] at this

theorem tWrite {x : Expr} {ts : List Expr} {j : Nat} {tid : TaskId} {σ : MState}
    {G : DevSt .virtio → Option (DevSt .virtio)} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    {k : Unit → DevProg .virtio} {m : DevProg .virtio} {s' : VirtioState} (hj : j < ts.length)
    (hm : m = .op (.dmaWrite G pa n w) k) (hg : G (σ.devs.st .virtio) = some s')
    (hram : ramBytes pa n) (hres : ¬ anyReserve σ.resv pa n) :
    VRun 1 (x :: ts.set j (.dev 0 .virtio tid m)) σ (x :: ts.set j (.dev 0 .virtio tid (k ())))
      ((σ.storeDma pa n w).setDev .virtio s') := by
  have := vWrite (vs := x :: ts.set j (.dev 0 .virtio tid m)) (j := j + 1) (tid := tid) (σ := σ) (G := G) (k := k)
    (by rw [tAt hj, hm]) hg hram hres
  rwa [tSetSet] at this

theorem tSkip {x : Expr} {ts : List Expr} {j : Nat} {tid : TaskId} {σ : MState}
    {G : DevSt .virtio → Option (DevSt .virtio)} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    {k : Unit → DevProg .virtio} {m : DevProg .virtio} (hj : j < ts.length)
    (hm : m = .op (.dmaWrite G pa n w) k) (hg : G (σ.devs.st .virtio) = none ∨ ¬ ramBytes pa n) :
    VRun 1 (x :: ts.set j (.dev 0 .virtio tid m)) σ (x :: ts.set j (.dev 0 .virtio tid (k ()))) σ := by
  have := vSkip (vs := x :: ts.set j (.dev 0 .virtio tid m)) (j := j + 1) (tid := tid) (σ := σ) (G := G) (k := k)
    (by rw [tAt hj, hm]) hg
  rwa [tSetSet] at this

/-! ### The drain loop: the root loop drains every cached sector, 5 steps each -/

theorem devsSetDev (σ : MState) (s : VirtioState) :
    (σ.setDev .virtio s).devs = setDvirtio σ.devs s := rfl

theorem dvirtioSetDev (σ : MState) (s : VirtioState) :
    (σ.setDev .virtio s).devs.st .virtio = s := dvirtioSet σ.devs s

/-- **The drains** [R19.1 (a)]: from the root at its boundary, MachCSL drains the cache one
sector per root iteration (`choose`(1), `get`, `choose` 0, `modify`, restart) and reaches pf's
`VirtioProg.drainAll`. -/
theorem drainLoop (ts : List Expr) :
    ∀ (L : List (Nat × List (BitVec 8))) (σ : MState), (σ.devs.st .virtio).cache = L →
      cacheWf (σ.devs.st .virtio) →
      ∃ (n : Nat) (σ' : MState), VRun n (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ
          (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ' ∧ DevOnly σ σ' ∧
        σ'.devs = setDvirtio σ.devs (VirtioProg.drainAll (σ.devs.st .virtio))
  | [], σ, hL, _ => by
    refine ⟨0, σ, vrunRefl _ _, devOnlyRefl σ, ?_⟩
    have hd : VirtioProg.drainAll (σ.devs.st .virtio) = σ.devs.st .virtio := by
      have hcv : Virtio.cacheView (σ.devs.st .virtio) = (σ.devs.st .virtio).disk := by
        funext a; unfold Virtio.cacheView; rw [hL]; rfl
      show ({ (σ.devs.st .virtio) with disk := Virtio.cacheView (σ.devs.st .virtio), cache := [] } : VirtioState) = _
      rw [hcv, ← hL]
      rfl
    rw [hd]
    exact (setDvirtioSelf σ.devs).symm
  | (s0, bs) :: rest, σ, hL, hw => by
    obtain ⟨kb, hb, -, hk1⟩ := bodyShape
    have hne : (σ.devs.st .virtio).cache ≠ [] := by rw [hL]; exact List.cons_ne_nil _ _
    obtain ⟨kc, hkc, f, kz, hkz, hf, hkz0⟩ := drainGShape (σ.devs.st .virtio) hne
    have hdrain := drainHead (σ.devs.st .virtio) s0 bs rest hL hw
    have r1 := rRestart (ts := ts) (σ := σ)
    have r2 := rChoose (ts := ts) (σ := σ) (k := kb) 1 hb
    have r3 := rGet (ts := ts) (σ := σ) (k := drainG) hk1
    have r4 := rChoose (ts := ts) (σ := σ) (k := kc) 0 hkc
    let v1 : VirtioState := { (σ.devs.st .virtio) with
      disk := Virtio.diskWrite (σ.devs.st .virtio).disk (Virtio.sectorSize * s0) bs, cache := rest }
    have hf1 : f (σ.devs.st .virtio) = some (v1, []) := by
      rw [hf, hL]
      simp only [List.length_cons, Nat.zero_mod, List.getD, List.getElem?_cons_zero, Option.getD_some]
      show some (Virtio.drain (σ.devs.st .virtio) s0, []) = _
      rw [hdrain]
    have r5 := rStep (ts := ts) (σ := σ) (f := f) (k := kz) (s' := v1) hkz hf1
    rw [hkz0] at r5
    have hwf1 : cacheWf v1 := by
      obtain ⟨hn, hlen⟩ := hw
      rw [hL] at hn hlen
      exact ⟨(List.nodup_cons.1 hn).2, fun e he => hlen e (List.mem_cons_of_mem _ he)⟩
    obtain ⟨n, σ', r6, hd6, hdv6⟩ := drainLoop ts rest (σ.setDev .virtio v1)
      (by rw [dvirtioSetDev]) (by rw [dvirtioSetDev]; exact hwf1)
    refine ⟨5 + n, σ', vrunTrans (vrunTrans (vrunTrans (vrunTrans (vrunTrans r1 r2) r3) r4) r5) r6,
      devOnlyTrans (devOnlySetDev σ .virtio v1) hd6, ?_⟩
    rw [hdv6, devsSetDev, setDvirtioTwice, setDvirtioSt]
    congr 1
    show ({ v1 with disk := Virtio.cacheView v1, cache := [] } : VirtioState) =
      { (σ.devs.st .virtio) with disk := Virtio.cacheView (σ.devs.st .virtio), cache := [] }
    rw [show Virtio.cacheView v1 = Virtio.cacheView (σ.devs.st .virtio) from
      cacheViewDrainHead (σ.devs.st .virtio) s0 bs rest hL hw]

/-! ### The disk rows proper -/

/-- What one disk-program step yields (F9): a run of the virtio threads to a MachCSL state that
moved only the devices / task bookkeeping (and, at a store, the memory), related again. -/
def DiskGoal (c' : Wpcfg Pexv6 Efab) (st' : List (Nat × Wlabel)) (dp' : Option (DM Dres))
    (vs : List Expr) (σ : MState) : Prop :=
  ∃ (n : Nat) (vs' : List Expr) (σ' : MState), VRun n vs σ vs' σ' ∧ σ'.regs = σ.regs ∧
    rmem c' st' σ' ∧ viewRel TsoShadow.cohSrc σ' st' ∧ diskSide dp' vs' c'.pcDev.efDev σ'.devs

/-- The context of a disk-program step (F9). -/
structure DCtx (c c' : Wpcfg Pexv6 Efab) (st rest : List (Nat × Wlabel)) (l : Wlabel)
    (σ : MState) : Prop where
  step : wpPfStep pstepEv pclsEv NCPU l c c'
  adj : pairAdjacent (st ++ (NCPU, l) :: rest)
  mem : rmem c st σ
  view : viewRel TsoShadow.cohSrc σ st
  lf : pfLoadFactsT TsoShadow.cohSrc st c NCPU l

theorem goalFrame {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) (hl : frameLbl l) {dp' : Option (DM Dres)} {n : Nat}
    {vs vs' : List Expr} {σ' : MState} (hr : VRun n vs σ vs' σ') (hd : DevOnly σ σ')
    (hds : diskSide dp' vs' c'.pcDev.efDev σ'.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' vs σ :=
  ⟨n, vs', σ', hr, hd.regs, (diskFrame X.step hl X.adj X.mem X.view hd).1,
    (diskFrame X.step hl X.adj X.mem X.view hd).2, hds⟩

theorem goalStore {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    {data : List (BitVec 8)} (hl : l = .LStore false (paZ pa) data [] []) {dp' : Option (DM Dres)}
    {m1 : Nat} {vs vs1 vs' : List Expr} {σ1 : MState} (s' : VirtioState)
    (hr1 : VRun m1 vs σ vs1 σ1) (hd1 : DevOnly σ σ1)
    (hwr : ¬ anyReserve σ1.resv pa n → VRun 1 vs1 σ1 vs' ((σ1.storeDma pa n w).setDev .virtio s'))
    (hram : ramBytes pa n) (hdl : data.length = n) (hn : n ≠ 0)
    (hb : ∀ j, j < n → data[j]? = some (nthByte w j))
    (hds : diskSide dp' vs' c'.pcDev.efDev (setDvirtio σ1.devs s')) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' vs σ := by
  subst hl
  obtain ⟨hres, hm, hv⟩ := diskStore s' X.step X.adj X.mem X.view hd1 hram hdl hn hb
  exact ⟨m1 + 1, vs', _, vrunTrans hr1 (hwr hres), hd1.regs, hm, hv, hds⟩

theorem vsOkTask (ts : List Expr) (j : Nat) (tid : TaskId) (hj : j < ts.length) (m : Virtio.VM Unit) :
    vsOk (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid m)) (.pure ())
      (some m) :=
  ⟨_, rfl, fun mt hmt => ⟨j, tid, by cases hmt; exact List.getElem?_set_self hj⟩⟩

theorem vsOkIdle (ts : List Expr) : vsOk (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) (.pure ()) none :=
  ⟨ts, rfl, fun _ h => by cases h⟩

/-- **The status byte** (`dtail h r pre`, any folded part `pre`): STORE / own-guard SKIP 1 → 1
after the MachCSL block `hgo` that performs `pre`'s moves (the task then at `restR`, `:536`);
ABORT after the block `hab` (MachCSL's task left at its blocking guard, or not moved). -/
theorem statusTail {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {h : BitVec 16} {r : VioReq}
    {pre : VirtioState → VirtioState × Bool} {dp' : Option (DM Dres)} {κ0 : VRel}
    (hpd : pdiskProg (some (dtail h r pre)) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree κ0 c.pcDev.efDev σ.devs) {ts : List Expr} {j : Nat} {tid : TaskId}
    (hj : j < ts.length) (hcw : ∀ s b, pre (dvirtio c.pcDev.efDev) = (s, b) → cacheWf s)
    (hgo : ∀ s, pre (dvirtio c.pcDev.efDev) = (s, true) → ∃ (m1 : Nat) (σ1 : MState),
      VRun m1 (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ
        (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (restR h r))) σ1 ∧
      DevOnly σ σ1 ∧ σ1.devs = setDvirtio σ.devs s)
    (hab : ∀ s, pre (dvirtio c.pcDev.efDev) = (s, false) → ∃ (m1 : Nat) (σ1 : MState) (ts1 : List Expr),
      VRun m1 (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ
        (Expr.dev 0 .virtio rootTask (.pure ()) :: ts1) σ1 ∧
      DevOnly σ σ1 ∧ σ1.devs = setDvirtio σ.devs s) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ := by
  obtain ⟨G, k, hrest, hG, hk⟩ := restShape h r
  rcases pdpWrite hpd with ⟨s, s', hp, hg, hram, hl, hdp, hd'⟩ | ⟨s, hp, hg, hl, hdp, hd'⟩ |
    ⟨s, hp, hl, hdp, hd'⟩
  · -- THE STORE
    have hs' : s' = s := reqGuardSome hg
    rw [hs'] at hg hd'
    obtain ⟨m1, σ1, r1, hd1, hdv1⟩ := hgo s hp
    have hram1 : ramBytes r.status 1 := by simpa [bytesOf_length] using hram
    refine goalStore X hl (vs' := Expr.dev 0 .virtio rootTask (.pure ()) ::
        ts.set j (.dev 0 .virtio tid (statusR h r))) s r1 hd1 (fun hres => ?_) hram1
      (bytesOf_length _) (by decide) (bytesOfGet _) ?_
    · have := tWrite (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (σ := σ1) hj hrest
        (by rw [hG, hdv1, setDvirtioSt]; exact hg) hram1 hres
      rw [hk] at this
      exact this
    · refine ⟨.pure (), some (statusR h r), .eq, vsOkTask ts j tid hj _, ?_, ?_⟩
      · rw [hdp]; exact .status h r
      · rw [hd', hdv1, setDvirtioTwice]; exact agMove .eq hag s s rfl (hcw s true hp)
  · -- THE OWN-GUARD SKIP
    obtain ⟨m1, σ1, r1, hd1, hdv1⟩ := hgo s hp
    have r2 := tSkip (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (σ := σ1) hj hrest
      (by rw [hG, hdv1, setDvirtioSt]; rw [bytesOf_length] at hg; exact hg)
    rw [hk] at r2
    subst hl
    refine goalFrame X trivial (vrunTrans r1 r2) hd1
      ⟨.pure (), some (statusR h r), .eq, vsOkTask ts j tid hj _, by rw [hdp]; exact .status h r, ?_⟩
    rw [hd', hdv1]; exact agMove .eq hag s s rfl (hcw s true hp)
  · -- THE ABORT
    obtain ⟨m1, σ1, ts1, r1, hd1, hdv1⟩ := hab s hp
    subst hl
    refine goalFrame X trivial r1 hd1 ⟨.pure (), none, .eq, vsOkIdle ts1, by rw [hdp]; exact .idle, ?_⟩
    rw [hd', hdv1]; exact agMove .eq hag s s rfl (hcw s false hp)

/-- No burst: START, 1 → 3 (the root's restart, `chooseLt 3` = 0, `get :561`). -/
theorem caseIdle {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr}
    (hpd : pdiskProg none c.pcDev.efDev l dp' c'.pcDev.efDev) (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ := by
  obtain ⟨hl, hdp, hd'⟩ := pdpNone hpd
  obtain ⟨hσ, hc⟩ := agEqOf hag
  obtain ⟨kb, hb, hk0, -⟩ := bodyShape
  have r1 := rRestart (ts := ts) (σ := σ)
  have r2 := rChoose (ts := ts) (σ := σ) (k := kb) 0 hb
  have r3 := rGet (ts := ts) (σ := σ) (k := rootAG) hk0
  have hv : σ.devs.st .virtio = dvirtio c.pcDev.efDev := by rw [hσ]; rfl
  rw [hv] at r3
  subst hl
  refine goalFrame X trivial (vrunTrans (vrunTrans r1 r2) r3) (devOnlyRefl σ)
    ⟨rootAG (dvirtio c.pcDev.efDev), none, .eq, ⟨ts, rfl, fun _ h => by cases h⟩,
      by rw [hdp]; exact .start _, ?_⟩
  rw [hd', hσ]; exact devAgreeEq _ hc

/-- After START: the avail-index read 1 → 1 (or, the queue not live, the burst's end 1 → 0). -/
theorem caseStart {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr}
    (v0 : VirtioState) (hpd : pdiskProg (some (virtioProg v0)) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' (Expr.dev 0 .virtio rootTask (rootAG v0) :: ts) σ := by
  obtain ⟨hσ, hc⟩ := agEqOf hag
  by_cases hl : Virtio.live v0.cfg = true
  · rw [vpLive v0 hl] at hpd
    obtain ⟨tvs, htl, hl', hdp, hd'⟩ := pdpRead hpd
    subst hl'
    obtain ⟨k, hk, hkw⟩ := rootAGLive v0 hl
    have r := rRead (ts := ts) (σ := σ) (k := k) (bvOfBytes 2 (tvs.map Prod.snd)) hk
      (dmaViewOf X.mem X.step X.lf htl (smallNoWrap _ _ (by decide)))
    rw [hkw] at r
    refine goalFrame X trivial r (devOnlyRefl σ)
      ⟨_, none, .eq, ⟨ts, rfl, fun _ h => by cases h⟩, by rw [hdp]; exact .ai _ _, ?_⟩
    rw [hd', hσ]; exact devAgreeEq _ hc
  · rw [vpDead v0 hl] at hpd
    obtain ⟨hl', hd', hst | hid⟩ := pdpRet hpd
    · cases hst.1
    · obtain ⟨-, hdp⟩ := hid
      subst hl'
      refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
        ⟨.pure (), none, .eq, ⟨ts, by rw [rootAGDead v0 hl], fun _ h => by cases h⟩,
          by rw [hdp]; exact .idle, ?_⟩
      rw [hd', hσ]; exact devAgreeEq _ hc

/-- After the avail-index read: the ring read 1 → 1 (or nothing pending, 1 → 0). -/
theorem caseAi {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr}
    (v0 : VirtioState) (ai : BitVec 16)
    (hpd : pdiskProg (some (kAi v0 ai)) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' (Expr.dev 0 .virtio rootTask (rootAI v0 ai) :: ts) σ := by
  obtain ⟨hσ, hc⟩ := agEqOf hag
  by_cases hne : v0.seen ≠ ai
  · rw [kAiNe v0 ai hne] at hpd
    obtain ⟨tvs, htl, hl', hdp, hd'⟩ := pdpRead hpd
    subst hl'
    obtain ⟨k, hk, hkw⟩ := rootAINe v0 ai hne
    have r := rRead (ts := ts) (σ := σ) (k := k) (bvOfBytes 2 (tvs.map Prod.snd)) hk
      (dmaViewOf X.mem X.step X.lf htl (smallNoWrap _ _ (by decide)))
    rw [hkw] at r
    refine goalFrame X trivial r (devOnlyRefl σ)
      ⟨_, none, .eq, ⟨ts, rfl, fun _ h => by cases h⟩, by rw [hdp]; exact .ring _, ?_⟩
    rw [hd', hσ]; exact devAgreeEq _ hc
  · have heq : v0.seen = ai := by simpa using hne
    rw [kAiEq v0 ai heq] at hpd
    obtain ⟨hl', hd', hst | hid⟩ := pdpRet hpd
    · cases hst.1
    · obtain ⟨-, hdp⟩ := hid
      subst hl'
      refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
        ⟨.pure (), none, .eq, ⟨ts, by rw [rootAIEq v0 ai heq], fun _ h => by cases h⟩,
          by rw [hdp]; exact .idle, ?_⟩
      rw [hd', hσ]; exact devAgreeEq _ hc

/-- A stalled pf request (`DRet DStall`): the silent self-loop, 1 → 0. -/
theorem caseStall {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr}
    (hpd : pdiskProg (some (DRet DStall)) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ := by
  obtain ⟨hl, hd', hst | hid⟩ := pdpRet hpd
  · obtain ⟨-, hdp⟩ := hst
    subst hl
    refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
      ⟨.pure (), none, .eq, vsOkIdle _, by rw [hdp]; exact .stall, ?_⟩
    rw [hd']; exact hag
  · cases hid.1

/-- At THE POP: refused 1 → 1 (`get :567`), or the pop 1 → 4 (`get :567`, guard-pop `:576`,
`fork :579`, the forked task's `get :522`). -/
theorem caseRing {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr}
    (h : BitVec 16)
    (hpd : pdiskProg (some (DPop h (fun s => VirtioProg.fetchProg s.cfg h))) c.pcDev.efDev l dp'
      c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' (Expr.dev 0 .virtio rootTask (rootRing h) :: ts) σ := by
  obtain ⟨hσ, hc⟩ := agEqOf hag
  have hv : σ.devs.st .virtio = dvirtio c.pcDev.efDev := by rw [hσ]; rfl
  obtain ⟨hl, hcase⟩ := pdpPop hpd
  subst hl
  obtain ⟨k, hk, hkr, hkp⟩ := rootRingShape h
  have r1 := rGet (ts := ts) (σ := σ) (k := k) hk
  rw [hv] at r1
  rcases hcase with ⟨hph, hdp, hd'⟩ | ⟨hph, hdp, hd'⟩
  · rw [hkr _ hph] at r1
    refine goalFrame X trivial r1 (devOnlyRefl σ)
      ⟨.pure (), none, .eq, vsOkIdle ts, by rw [hdp]; exact .idle, ?_⟩
    rw [hd', hσ]; exact devAgreeEq _ hc
  · obtain ⟨f, k2, hk2, hf, k3, hk3, hk3t⟩ := hkp _ hph
    have r2 := rStep (ts := ts) (σ := σ) (f := f) (k := k2)
      (s' := VirtioProg.popState (dvirtio c.pcDev.efDev) h) hk2
      (by rw [hf, hv]; simp [popG, hph])
    have r3 := vFork (vs := Expr.dev 0 .virtio rootTask (k2 ()) :: ts)
      (σ := σ.setDev .virtio (VirtioProg.popState (dvirtio c.pcDev.efDev) h)) (j := 0)
      (tid := rootTask) (tk := .serve h) (k := k3) (by rw [hk3]; rfl)
    rw [hk3t] at r3
    obtain ⟨ks, hks, hksv⟩ := serveShape h
    have hlt : ts.length < (ts ++ [Expr.dev 0 .virtio (σ.devrt .virtio).next (Virtio.serve h)]).length := by
      simp
    have r4 := tGet (x := Expr.dev 0 .virtio rootTask (.pure ()))
      (ts := ts ++ [Expr.dev 0 .virtio (σ.devrt .virtio).next (Virtio.serve h)]) (j := ts.length)
      (tid := (σ.devrt .virtio).next)
      (σ := (σ.setDev .virtio (VirtioProg.popState (dvirtio c.pcDev.efDev) h)).setRt .virtio
        { σ.devrt .virtio with next := (σ.devrt .virtio).next + 1 }) (k := ks) hlt hks
    rw [setSelfOf (by simp), dvirtioSetDev, hksv] at r4
    refine goalFrame X trivial (vrunTrans (vrunTrans (vrunTrans r1 r2) r3) r4)
      (devOnlyTrans (devOnlySetDev _ _ _) (devOnlySetRt _ _ _))
      ⟨.pure (), some (DevM.bind (Virtio.fetch (VirtioProg.popState (dvirtio c.pcDev.efDev) h).cfg h)
          (serveMatch h)), .eq, vsOkTask _ _ _ hlt _, by rw [hdp]; exact .fetch _ _ _ (fcFetch _ _), ?_⟩
    rw [hd']
    exact agMove .eq hag _ _ rfl (cacheWfOf rfl hc)

/-- **The serving task's request** (the fetch answered `some r`, the task at `:526`): the data
phase by the request's kind (plan §C W4 F9, [R20.2] [R21.3 (a)] [R23.s2]). -/
theorem caseSvc {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (r : VioReq)
    (hpd : pdiskProg (some (dcomplete h r)) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (svcR h r))) σ := by
  obtain ⟨hσ, hc⟩ := agEqOf hag
  have hv : σ.devs.st .virtio = dvirtio c.pcDev.efDev := by rw [hσ]; rfl
  obtain ⟨f0, k0, hsvc, hf0, hkOut, hkIn, hkElse⟩ := svcShape h r
  -- the move `:526`, from the task at `svcR`
  have step526 : (Virtio.phase (dvirtio c.pcDev.efDev) h).isSome = true →
      VRun 1 (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (svcR h r))) σ
        (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (k0 ())))
        (σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) := fun _ =>
    tStep hj hsvc (by rw [hf0, hv])
  by_cases hout : r.type.toNat = Virtio.blkTOut
  · rw [hkOut hout] at step526
    by_cases hn : r.len.toNat = 0
    · -- OUT, zero-length: the status byte absorbs the capture (1 → 5)
      rw [dcompleteOut0 h r hout hn] at hpd
      refine statusTail X hpd hag (tid := tid) (by rw [List.length_set]; exact hj) (fun s b hp => ?_)
        (fun s hp => ?_) (fun s hp => ?_)
      · obtain ⟨-, h1, h2⟩ := preCaptureInv h r [] _ s b hp
        cases b
        · rw [h2 rfl]; exact cacheWfOf (pre1Cache h r _) hc
        · rw [h1 rfl]; exact captureMoveWf h r [] _ (cacheWfOf (pre1Cache h r _) hc)
      · simp only [List.set_set]
        obtain ⟨hb, h1, -⟩ := preCaptureInv h r [] _ s true hp
        obtain ⟨hph, htk, hpe⟩ := pre1True h r _ hb
        have r1 := step526 hph
        obtain ⟨fl, kl, hlatch, hfl, k2, hk2, hk2w⟩ := latchShape h r
        have r2 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid)
          (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) (f := fl) (k := kl)
          (s' := { Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r) with taken := some h }) hj hlatch
          (by rw [hfl, dvirtioSetDev]; simp [latchG, Virtio.setPhase, htk])
        rw [hk2] at r2
        have r3 := tRead (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (pa := r.buf) (k := k2) hj
          (σ := (σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))).setDev .virtio
            { Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r) with taken := some h })
          0 rfl (fun i hi => absurd hi (by omega))
        rw [hk2w] at r3
        obtain ⟨fc, kc, hcap, hfc, hkc⟩ := capShape h r 0
        have r4 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (f := fc) (k := kc)
          (σ := (σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))).setDev .virtio
            { Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r) with taken := some h })
          (s' := s) hj hcap (by
            rw [hfc, dvirtioSetDev, h1 rfl, hpe]
            have hb0 : bytesOf (n := r.len.toNat) 0 = [] := by simp [bytesOf, hn]
            rw [hb0]
            rfl)
        rw [hkc] at r4
        refine ⟨_, _, vrunTrans (vrunTrans (vrunTrans r1 r2) r3) r4,
          devOnlyTrans (devOnlyTrans (devOnlySetDev _ _ _) (devOnlySetDev _ _ _)) (devOnlySetDev _ _ _), ?_⟩
        rw [devsSetDev, devsSetDev, devsSetDev, setDvirtioTwice, setDvirtioTwice]
      · obtain ⟨hb, -, h2⟩ := preCaptureInv h r [] _ s false hp
        rcases pre1False h r _ hb with ⟨hph, hpe⟩ | ⟨hph, htk, hpe⟩
        · refine ⟨0, σ, ts.set j (.dev 0 .virtio tid (svcR h r)), vrunRefl _ _, devOnlyRefl σ, ?_⟩
          rw [h2 rfl, hpe, ← hv]
          exact (setDvirtioSelf σ.devs).symm
        · exact ⟨1, _, _, step526 hph, devOnlySetDev _ _ _, by rw [h2 rfl, hpe]; rfl⟩
    · by_cases hwr : VirtioProg.outWraps r = true
      · -- OUT, the buffer wrapping past `2^64`: the pf program STALLS ([OWN.40]), 1 → 0
        rw [dcompleteWrap h r hout hwr] at hpd
        exact caseStall X hpd hag
      have hwr' : VirtioProg.outWraps r = false := by simpa using hwr
      -- OUT: THE CAPTURE READ
      rw [dcompleteOut h r hout hwr' hn] at hpd
      obtain ⟨tvs, htl, hl, hdp, hd'⟩ := pdpRead hpd
      subst hl
      have hbs : (tvs.map Prod.snd).length = r.len.toNat := by simp [htl]
      by_cases hph : (Virtio.phase (dvirtio c.pcDev.efDev) h).isSome = true
      · have r1 := step526 hph
        by_cases htk : (dvirtio c.pcDev.efDev).taken = none
        · -- the latch FREE: `:526`, `:529`, `:516` (1 → 3)
          obtain ⟨fl, kl, hlatch, hfl, k2, hk2, hk2w⟩ := latchShape h r
          have r2 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid)
            (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) (f := fl) (k := kl)
            (s' := { Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r) with taken := some h }) hj hlatch
            (by rw [hfl, dvirtioSetDev]; simp [latchG, Virtio.setPhase, htk])
          rw [hk2] at r2
          have hd2 : DevOnly σ ((σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))).setDev
              .virtio { Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r) with taken := some h }) :=
            devOnlyTrans (devOnlySetDev _ _ _) (devOnlySetDev _ _ _)
          have r3 := tRead (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (pa := r.buf) (k := k2) hj
            (bvOfBytes r.len.toNat (tvs.map Prod.snd)) rfl
            (dmaViewOf (rmemCongr X.mem hd2) X.step X.lf htl
              (by
                have h1 : ¬ (2 ^ 64 < r.buf.toNat + r.len.toNat) := by
                  simpa [VirtioProg.outWraps] using hwr'
                simp only [paZ, ramBase]
                omega))
          rw [hk2w] at r3
          refine goalFrame X trivial (vrunTrans (vrunTrans r1 r2) r3) hd2
            ⟨.pure (), some (capR h r (bvOfBytes r.len.toNat (tvs.map Prod.snd))), .capF h r,
              vsOkTask _ _ _ hj _, by rw [hdp]; exact .capF h r _ hout hbs, ?_⟩
          rw [hd', devsSetDev, devsSetDev, setDvirtioTwice]
          refine agMoveM _ hag _ ⟨?_, Or.inl ?_⟩ hc
          · rw [pre1Free h r _ hph htk]
          · rw [pre1Free h r _ hph htk]
        · -- the latch HELD: `:526` only (1 → 1)
          refine goalFrame X trivial r1 (devOnlySetDev _ _ _)
            ⟨.pure (), some (latchR h r), .capB h r, vsOkTask _ _ _ hj _,
              by rw [hdp]; exact .capB h r _ hout hbs, ?_⟩
          rw [hd', devsSetDev]
          refine agMoveM _ hag _ ⟨?_, ?_⟩ hc
          · rw [pre1Held h r _ hph htk]
          · rw [pre1Held h r _ hph htk]
      · -- no longer in flight: 1 → 0, the task a zombie at `:526`
        have hn' : Virtio.phase (dvirtio c.pcDev.efDev) h = none := by simpa using hph
        refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
          ⟨.pure (), some (svcR h r), .capZ h, vsOkTask _ _ _ hj _,
            by rw [hdp]; exact .capZ h r _ hout hbs, ?_⟩
        rw [hd']
        exact agRe hag (fun vm hk => ⟨hk, hn'⟩)
  · by_cases hfill : r.type.toNat = Virtio.blkTIn ∧ r.len.toNat ≠ 0
    · -- IN: THE FILL (1 → 3)
      rw [dcompleteIn h r hout hfill.1 hfill.2] at hpd
      have hstep := step526
      rw [hkIn hout hfill.1] at hstep
      obtain ⟨kf, hfk, hkf⟩ := fillShape h r
      rcases pdpWrite hpd with ⟨s, s', hp, hg, hram, hl, hdp, hd'⟩ | ⟨s, hp, hg, hl, hdp, hd'⟩ |
        ⟨s, hp, hl, hdp, hd'⟩
      · rcases preSimpleInv (preFillEq h r) _ s true hp with ⟨-, hph, hs⟩ | ⟨h0, -⟩
        · subst hs
          have r1 := hstep hph
          have r2 := tGet (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (k := kf)
            (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) hj hfk
          rw [dvirtioSetDev] at r2
          obtain ⟨G, k2, hk2, hG, hk2s⟩ := hkf (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))
          have hs' : s' = Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r) := reqGuardSome hg
          have hdl := diskReadLength (Virtio.cacheView (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r)))
            (Virtio.reqOff r) r.len.toNat
          rw [hdl] at hram
          refine goalStore X hl (vs' := Expr.dev 0 .virtio rootTask (.pure ()) ::
              ts.set j (.dev 0 .virtio tid (servedR h r))) s' (vrunTrans r1 r2)
            (devOnlySetDev _ _ _) (fun hres => ?_) hram hdl hfill.2
            (bvOfBytesGet _ _ hdl) ?_
          · have := tWrite (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid)
              (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) hj hk2
              (by rw [hG, dvirtioSetDev]; exact hg) hram hres
            rw [hk2s] at this
            exact this
          · refine ⟨.pure (), some (servedR h r), .eq, vsOkTask _ _ _ hj _,
              by rw [hdp]; exact .served h r, ?_⟩
            rw [hd', devsSetDev, setDvirtioTwice]
            exact agMove .eq hag s' s' rfl (by rw [hs']; exact cacheWfOf rfl hc)
        · cases h0
      · rcases preSimpleInv (preFillEq h r) _ s true hp with ⟨-, hph, hs⟩ | ⟨h0, -⟩
        · subst hs
          have r1 := hstep hph
          have r2 := tGet (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (k := kf)
            (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) hj hfk
          rw [dvirtioSetDev] at r2
          obtain ⟨G, k2, hk2, hG, hk2s⟩ := hkf (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))
          have hdl := diskReadLength (Virtio.cacheView (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r)))
            (Virtio.reqOff r) r.len.toNat
          rw [hdl] at hg
          have r3 := tSkip (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid)
            (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) hj hk2
            (by rw [hG, dvirtioSetDev]; exact hg)
          rw [hk2s] at r3
          subst hl
          refine goalFrame X trivial (vrunTrans (vrunTrans r1 r2) r3) (devOnlySetDev _ _ _)
            ⟨.pure (), some (servedR h r), .eq, vsOkTask _ _ _ hj _, by rw [hdp]; exact .served h r, ?_⟩
          rw [hd', devsSetDev]
          exact agMove .eq hag _ _ rfl (cacheWfOf rfl hc)
        · cases h0
      · rcases preSimpleInv (preFillEq h r) _ s false hp with ⟨h0, -⟩ | ⟨-, -, hs⟩
        · cases h0
        · subst hs hl
          refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
            ⟨.pure (), none, .eq, vsOkIdle _, by rw [hdp]; exact .idle, ?_⟩
          rw [hd', setDvirtioSelf, hσ]; exact devAgreeEq _ hc
    · -- no data node (IN of length 0 1 → 5, FLUSH / unknown 1 → 3)
      rw [dcompleteElse h r hout hfill] at hpd
      refine statusTail X hpd hag (tid := tid) (by rw [List.length_set]; exact hj) (fun s b hp => ?_)
        (fun s hp => ?_) (fun s hp => ?_)
      · rcases preSimpleInv (preNoDataEq h r) _ s b hp with ⟨-, -, hs⟩ | ⟨-, -, hs⟩
        · rw [hs]; exact cacheWfOf rfl hc
        · rw [hs]; exact hc
      · simp only [List.set_set]
        rcases preSimpleInv (preNoDataEq h r) _ s true hp with ⟨-, hph, hs⟩ | ⟨h0, -⟩
        · subst hs
          have r1 := step526 hph
          obtain ⟨fs, ks, hserv, hfs, hks⟩ := servedShape h r
          by_cases hin : r.type.toNat = Virtio.blkTIn
          · have hn : r.len.toNat = 0 := by
              by_cases h0 : r.len.toNat = 0
              · exact h0
              · exact absurd ⟨hin, h0⟩ hfill
            rw [hkIn hout hin] at r1
            obtain ⟨kf, hfk, hkf⟩ := fillShape h r
            have r2 := tGet (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (k := kf)
              (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) hj hfk
            rw [dvirtioSetDev] at r2
            obtain ⟨G, k2, hk2, hG, hk2s⟩ := hkf (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))
            have r3 := tWrite (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid)
              (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))) hj hk2
              (by rw [hG, dvirtioSetDev]; exact reqGuardFetched _ _ _)
              (fun i hi => absurd hi (by omega)) (fun ⟨_, _, _, i, hi, _⟩ => absurd hi (by omega))
            rw [hk2s, MState.storeDma_zero _ _ _ _ hn] at r3
            have r4 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (f := fs) (k := ks)
              (σ := (σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r))).setDev .virtio
                (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r)))
              (s' := Virtio.setPhase (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r)) h (.served r)) hj hserv
              (by rw [hfs, dvirtioSetDev])
            rw [hks] at r4
            refine ⟨_, _, vrunTrans (vrunTrans (vrunTrans r1 r2) r3) r4,
              devOnlyTrans (devOnlyTrans (devOnlySetDev _ _ _) (devOnlySetDev _ _ _)) (devOnlySetDev _ _ _), ?_⟩
            rw [devsSetDev, devsSetDev, devsSetDev, setDvirtioTwice, setDvirtioTwice]
          · rw [hkElse hout hin] at r1
            have r2 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (f := fs) (k := ks)
              (σ := σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r)))
              (s' := Virtio.setPhase (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.fetched r)) h (.served r)) hj hserv
              (by rw [hfs, dvirtioSetDev])
            rw [hks] at r2
            refine ⟨_, _, vrunTrans r1 r2, devOnlyTrans (devOnlySetDev _ _ _) (devOnlySetDev _ _ _), ?_⟩
            rw [devsSetDev, devsSetDev, setDvirtioTwice]
        · cases h0
      · rcases preSimpleInv (preNoDataEq h r) _ s false hp with ⟨h0, -⟩ | ⟨-, -, hs⟩
        · cases h0
        · refine ⟨0, σ, ts.set j (.dev 0 .virtio tid (svcR h r)), vrunRefl _ _, devOnlyRefl σ, ?_⟩
          rw [hs, ← hv]
          exact (setDvirtioSelf σ.devs).symm

/-- The task in its FETCH: a descriptor / header read 1 → 1, the stall 1 → 0, the decoded
request (`caseSvc`). -/
theorem caseFetch {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (P : DM Dres) (M : Virtio.VM (Option VioReq))
    (hfc : FC h P M) (hpd : pdiskProg (some P) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (DevM.bind M (serveMatch h)))) σ := by
  cases hfc with
  | stall =>
    obtain ⟨hl, hd', hst | hid⟩ := pdpRet hpd
    · obtain ⟨-, hdp⟩ := hst
      subst hl
      refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
        ⟨.pure (), some _, .eq, vsOkTask _ _ _ hj _, by rw [hdp]; exact .fetch h _ _ .stall, ?_⟩
      rw [hd']; exact hag
    · cases hid.1
  | done r => exact caseSvc X hj h r hpd hag
  | read pa n kP kM hn hk =>
    obtain ⟨tvs, htl, hl, hdp, hd'⟩ := pdpRead hpd
    subst hl
    have r := tRead (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (σ := σ)
      (m := DevM.bind (.op (.dmaRead pa n) kM) (serveMatch h))
      (k := fun x => DevM.bind (kM x) (serveMatch h)) hj
      (bvOfBytes n (tvs.map Prod.snd)) rfl
      (dmaViewOf X.mem X.step X.lf htl (smallNoWrap _ _ hn))
    refine goalFrame X trivial r (devOnlyRefl σ)
      ⟨.pure (), some _, .eq, vsOkTask _ _ _ hj _,
        by rw [hdp]; exact .fetch h _ _ (hk _ (by simp [htl])), ?_⟩
    rw [hd']; exact hag

/-- The OUT capture segment, the task a ZOMBIE (`capZ`): the status byte ABORTS, 1 → 0. -/
theorem caseCapZ {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8))
    (hpd : pdiskProg (some (dtail h r (VirtioProg.preCapture h r bs))) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree (.capZ h) c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (svcR h r))) σ := by
  obtain ⟨hσ, hk⟩ := agSt hag
  obtain ⟨hvm, hph⟩ := hk
  have hc := agCache hag
  have hpre : VirtioProg.preCapture h r bs (dvirtio c.pcDev.efDev) = (dvirtio c.pcDev.efDev, false) :=
    preCaptureOut h r bs _ hph
  refine statusTail X hpd hag (tid := tid) (by rw [List.length_set]; exact hj) (fun s b hp => ?_)
    (fun s hp => ?_) (fun s hp => ?_)
  · rw [hpre] at hp; cases hp; exact hc
  · rw [hpre] at hp; cases hp
  · rw [hpre] at hp
    cases hp
    refine ⟨0, σ, _, vrunRefl _ _, devOnlyRefl σ, ?_⟩
    rw [← hvm]
    exact (setDvirtioSelf σ.devs).symm

/-- The OUT capture segment, the latch FREE (`capF`, the task at `:517`): the capture's move and
the status byte, 1 → 2; ABORT 1 → 0 once no longer in flight. -/
theorem caseCapF {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8))
    (hbs : bs.length = r.len.toNat)
    (hpd : pdiskProg (some (dtail h r (VirtioProg.preCapture h r bs))) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree (.capF h r) c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) ::
        ts.set j (.dev 0 .virtio tid (capR h r (bvOfBytes r.len.toNat bs)))) σ := by
  obtain ⟨hσ, hk⟩ := agSt hag
  obtain ⟨hvm, hcase⟩ := hk
  have hc := agCache hag
  refine statusTail X hpd hag (tid := tid) (by rw [List.length_set]; exact hj) (fun s b hp => ?_)
    (fun s hp => ?_) (fun s hp => ?_)
  · obtain ⟨-, h1, h2⟩ := preCaptureInv h r bs _ s b hp
    cases b
    · rw [h2 rfl]; exact cacheWfOf (pre1Cache h r _) hc
    · rw [h1 rfl]; exact captureMoveWf h r bs _ (cacheWfOf (pre1Cache h r _) hc)
  · simp only [List.set_set]
    obtain ⟨-, h1, -⟩ := preCaptureInv h r bs _ s true hp
    obtain ⟨fc, kc, hcap, hfc, hkc⟩ := capShape h r (bvOfBytes r.len.toNat bs)
    have r1 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (f := fc) (k := kc)
      (σ := σ) (s' := s) hj hcap (by
        rw [hfc, hvm, h1 rfl, bytesOf_bvOfBytes _ _ hbs]
        rfl)
    rw [hkc] at r1
    exact ⟨1, _, r1, devOnlySetDev _ _ _, rfl⟩
  · obtain ⟨hb, -, h2⟩ := preCaptureInv h r bs _ s false hp
    rcases hcase with ht | hn
    · rw [hb] at ht; cases ht
    · rw [preCaptureHeadOut h r _ hn] at h2 hvm
      refine ⟨0, σ, _, vrunRefl _ _, devOnlyRefl σ, ?_⟩
      rw [h2 rfl, ← hvm]
      exact (setDvirtioSelf σ.devs).symm

/-- The OUT capture segment, the latch HELD (`capB`, MachCSL blocked at `:529`): ABORT, 1 → 0. -/
theorem caseCapB {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8))
    (hpd : pdiskProg (some (dtail h r (VirtioProg.preCapture h r bs))) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree (.capB h r) c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (latchR h r))) σ := by
  obtain ⟨hσ, hk⟩ := agSt hag
  obtain ⟨hvm, hfalse⟩ := hk
  have hc := agCache hag
  refine statusTail X hpd hag (tid := tid) (by rw [List.length_set]; exact hj) (fun s b hp => ?_)
    (fun s hp => ?_) (fun s hp => ?_)
  · obtain ⟨-, h1, h2⟩ := preCaptureInv h r bs _ s b hp
    cases b
    · rw [h2 rfl]; exact cacheWfOf (pre1Cache h r _) hc
    · rw [h1 rfl]; exact captureMoveWf h r bs _ (cacheWfOf (pre1Cache h r _) hc)
  · obtain ⟨hb, -, -⟩ := preCaptureInv h r bs _ s true hp
    rw [hfalse] at hb; cases hb
  · obtain ⟨-, -, h2⟩ := preCaptureInv h r bs _ s false hp
    refine ⟨0, σ, _, vrunRefl _ _, devOnlyRefl σ, ?_⟩
    rw [h2 rfl, ← hvm]
    exact (setDvirtioSelf σ.devs).symm

/-- After an IN fill (the task at `:534`): `setPhase .served` and the status byte, 1 → 2. -/
theorem caseServed {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (r : VioReq)
    (hpd : pdiskProg (some (dtail h r (VirtioProg.preServed h r))) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (servedR h r))) σ := by
  obtain ⟨hσ, hc⟩ := agEqOf hag
  have hv : σ.devs.st .virtio = dvirtio c.pcDev.efDev := by rw [hσ]; rfl
  refine statusTail X hpd hag (tid := tid) (by rw [List.length_set]; exact hj) (fun s b hp => ?_)
    (fun s hp => ?_) (fun s hp => ?_)
  · rcases preSimpleInv (preServedEq h r) _ s b hp with ⟨-, -, hs⟩ | ⟨-, -, hs⟩
    · rw [hs]; exact cacheWfOf rfl hc
    · rw [hs]; exact hc
  · simp only [List.set_set]
    rcases preSimpleInv (preServedEq h r) _ s true hp with ⟨-, -, hs⟩ | ⟨h0, -⟩
    · subst hs
      obtain ⟨fs, ks, hserv, hfs, hks⟩ := servedShape h r
      have r1 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (f := fs) (k := ks)
        (σ := σ) (s' := Virtio.setPhase (dvirtio c.pcDev.efDev) h (.served r)) hj hserv
        (by rw [hfs, hv])
      rw [hks] at r1
      exact ⟨1, _, r1, devOnlySetDev _ _ _, rfl⟩
    · cases h0
  · rcases preSimpleInv (preServedEq h r) _ s false hp with ⟨h0, -⟩ | ⟨-, -, hs⟩
    · cases h0
    · refine ⟨0, σ, _, vrunRefl _ _, devOnlyRefl σ, ?_⟩
      rw [hs, ← hv]
      exact (setDvirtioSelf σ.devs).symm

/-- After the status byte (the task at `:537`): THE USED ELEMENT — `setPhase .status`, the root
loop's drains (5 per cached sector), the gate, `get :542`, the element write: 1 → 3 + 5k; a gate
ABORT 1 → 1 + 5k; a pre-check ABORT 1 → 0. -/
theorem caseStatus {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (r : VioReq)
    (hpd : pdiskProg (some (dusedTail h r)) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (statusR h r))) σ := by
  obtain ⟨hσ, hc⟩ := agEqOf hag
  have hv : σ.devs.st .virtio = dvirtio c.pcDev.efDev := by rw [hσ]; rfl
  obtain ⟨fs, ks, hstat, hfs, hks⟩ := statusShape h r
  -- `:537` then the drains, whenever the request is still in flight
  have pre : (Virtio.phase (dvirtio c.pcDev.efDev) h).isSome = true →
      ∃ (n : Nat) (σ2 : MState),
        VRun n (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (statusR h r))) σ
          (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (gateR h r))) σ2 ∧
        DevOnly σ σ2 ∧
        σ2.devs = setDvirtio σ.devs
          (VirtioProg.drainAll (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.status r))) := fun _ => by
    have r1 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (f := fs) (k := ks)
      (σ := σ) (s' := Virtio.setPhase (dvirtio c.pcDev.efDev) h (.status r)) hj hstat (by rw [hfs, hv])
    rw [hks] at r1
    obtain ⟨n, σ2, r2, hd2, hdv2⟩ := drainLoop (ts.set j (.dev 0 .virtio tid (gateR h r)))
      _ (σ.setDev .virtio (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.status r))) rfl
      (by rw [dvirtioSetDev]; exact cacheWfOf rfl hc)
    refine ⟨1 + n, σ2, vrunTrans r1 r2, devOnlyTrans (devOnlySetDev _ _ _) hd2, ?_⟩
    rw [hdv2, devsSetDev, setDvirtioTwice]
    exact congrArg (fun v => setDvirtio σ.devs (VirtioProg.drainAll v)) (setDvirtioSt σ.devs _)
  obtain ⟨fg, kg, hgate, hfg, kg2, hkg, hkg2⟩ := gateShape h r
  rcases pdpWrite hpd with ⟨s, s', hp, hg, hram, hl, hdp, hd'⟩ | ⟨s, hp, hg, hl, hdp, hd'⟩ |
    ⟨s, hp, hl, hdp, hd'⟩
  · rcases preGateInv h r _ s true hp with ⟨-, h0, -⟩ | ⟨hph, hgs, -⟩
    · cases h0
    · simp only [if_true] at hgs
      obtain ⟨n, σ2, r12, hd2, hdv2⟩ := pre hph
      have r3 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (f := fg) (k := kg)
        (σ := σ2) (s' := s) hj hgate (by rw [hfg, hdv2, setDvirtioSt, hgs]; rfl)
      rw [hkg] at r3
      have r4 := tGet (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (k := kg2)
        (σ := σ2.setDev .virtio s) hj rfl
      rw [dvirtioSetDev, hkg2] at r4
      obtain ⟨G, ku, hused, hG, hku⟩ := usedShape h r s.usedIdx s.cfg
      have hs' : s' = s := reqGuardSome hg
      have hram8 : ramBytes (Virtio.usedElemAddr s.cfg s.usedIdx) 8 := by
        simpa [bytesOf_length] using hram
      refine goalStore X hl (vs' := Expr.dev 0 .virtio rootTask (.pure ()) ::
          ts.set j (.dev 0 .virtio tid (idxR h r s.usedIdx s.cfg))) s'
        (vrunTrans (vrunTrans r12 r3) r4)
        (devOnlyTrans hd2 (devOnlySetDev σ2 .virtio s)) (fun hres => ?_) hram8 (bytesOf_length _)
        (by decide) (bytesOfGet _) ?_
      · have := tWrite (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid)
          (σ := σ2.setDev .virtio s) hj hused
          (by rw [hG, dvirtioSetDev, usedGSelf]; exact hg) hram8 hres
        rw [hku] at this
        exact this
      · refine ⟨.pure (), some (idxR h r s.usedIdx s.cfg), .eq, vsOkTask _ _ _ hj _,
          by rw [hdp]; exact .fence h r _ _, ?_⟩
        rw [hd', devsSetDev, hdv2, setDvirtioTwice, setDvirtioTwice]
        refine agMove .eq hag s' s' rfl ?_
        rw [hs', gateGSome hgs]
        exact cacheWfOf (v := VirtioProg.drainAll (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.status r)))
          rfl (drainAllWf _)
  · rcases preGateInv h r _ s true hp with ⟨-, h0, -⟩ | ⟨hph, hgs, -⟩
    · cases h0
    · simp only [if_true] at hgs
      obtain ⟨n, σ2, r12, hd2, hdv2⟩ := pre hph
      have r3 := tStep (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (f := fg) (k := kg)
        (σ := σ2) (s' := s) hj hgate (by rw [hfg, hdv2, setDvirtioSt, hgs]; rfl)
      rw [hkg] at r3
      have r4 := tGet (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (k := kg2)
        (σ := σ2.setDev .virtio s) hj rfl
      rw [dvirtioSetDev, hkg2] at r4
      obtain ⟨G, ku, hused, hG, hku⟩ := usedShape h r s.usedIdx s.cfg
      have r5 := tSkip (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid)
        (σ := σ2.setDev .virtio s) hj hused
        (by rw [hG, dvirtioSetDev, usedGSelf]; rw [bytesOf_length] at hg; exact hg)
      rw [hku] at r5
      subst hl
      refine goalFrame X trivial (vrunTrans (vrunTrans (vrunTrans r12 r3) r4) r5)
        (devOnlyTrans hd2 (devOnlySetDev σ2 .virtio s))
        ⟨.pure (), some (idxR h r s.usedIdx s.cfg), .eq, vsOkTask _ _ _ hj _,
          by rw [hdp]; exact .fence h r _ _, ?_⟩
      rw [hd', devsSetDev, hdv2, setDvirtioTwice]
      refine agMove .eq hag s s rfl ?_
      rw [gateGSome hgs]
      exact cacheWfOf (v := VirtioProg.drainAll (Virtio.setPhase (dvirtio c.pcDev.efDev) h (.status r)))
          rfl (drainAllWf _)
  · subst hl
    rcases preGateInv h r _ s false hp with ⟨hn, -, hs⟩ | ⟨hph, -, hs⟩
    · refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
        ⟨.pure (), none, .eq, vsOkIdle _, by rw [hdp]; exact .idle, ?_⟩
      rw [hd', hs, setDvirtioSelf, hσ]; exact devAgreeEq _ hc
    · obtain ⟨n, σ2, r12, hd2, hdv2⟩ := pre hph
      refine goalFrame X trivial r12 hd2
        ⟨.pure (), none, .eq, vsOkIdle _, by rw [hdp]; exact .idle, ?_⟩
      rw [hd', hdv2, hs rfl]
      exact agMove .eq hag _ _ rfl (drainAllWf _)

/-- The pf-only `DFence` before the used index: 1 → 0. -/
theorem caseFence {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (cf : VirtioCfg)
    (hpd : pdiskProg (some (DFence (VirtioProg.idxNode h r ui cf))) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (idxR h r ui cf))) σ := by
  obtain ⟨hl, hdp, hd'⟩ := pdpFence hpd
  subst hl
  refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
    ⟨.pure (), some (idxR h r ui cf), .eq, vsOkTask _ _ _ hj _, by rw [hdp]; exact .idx h r ui cf, ?_⟩
  rw [hd']; exact hag

/-- THE USED INDEX and the completion, in one step: STORE / own-guard SKIP 1 → 1. -/
theorem caseIdx {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr} {j : Nat}
    {tid : TaskId} (hj : j < ts.length) (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (cf : VirtioCfg)
    (hpd : pdiskProg (some (VirtioProg.idxNode h r ui cf)) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp'
      (Expr.dev 0 .virtio rootTask (.pure ()) :: ts.set j (.dev 0 .virtio tid (idxR h r ui cf))) σ := by
  obtain ⟨hσ, hc⟩ := agEqOf hag
  have hv : σ.devs.st .virtio = dvirtio c.pcDev.efDev := by rw [hσ]; rfl
  obtain ⟨G, k, hidx, hG, hk⟩ := idxShape h r ui cf
  rcases pdpWrite hpd with ⟨s, s', hp, hg, hram, hl, hdp, hd'⟩ | ⟨s, hp, hg, hl, hdp, hd'⟩ |
    ⟨s, hp, hl, hdp, hd'⟩
  · have hs : s = dvirtio c.pcDev.efDev := (Prod.mk.inj hp).1.symm
    subst hs
    have hram2 : ramBytes (Virtio.usedIdxAddr cf) 2 := by simpa [bytesOf_length] using hram
    refine goalStore X hl (vs' := Expr.dev 0 .virtio rootTask (.pure ()) ::
        ts.set j (.dev 0 .virtio tid (.pure ()))) s' (vrunRefl _ σ) (devOnlyRefl σ)
      (fun hres => ?_) hram2 (bytesOf_length _) (by decide) (bytesOfGet _) ?_
    · have := tWrite (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (σ := σ) hj hidx
        (by rw [hG, hv]; exact hg) hram2 hres
      rw [hk] at this
      exact this
    · refine ⟨.pure (), none, .eq, vsOkIdle _, by rw [hdp]; exact .fin, ?_⟩
      rw [hd']
      refine agMove .eq hag s' s' rfl ?_
      rw [idxGuardSome hg]
      exact cacheWfOf rfl hc
  · have hs : s = dvirtio c.pcDev.efDev := (Prod.mk.inj hp).1.symm
    subst hs
    have r1 := tSkip (x := Expr.dev 0 .virtio rootTask (.pure ())) (tid := tid) (σ := σ) hj hidx
      (by rw [hG, hv]; rw [bytesOf_length] at hg; exact hg)
    rw [hk] at r1
    subst hl
    refine goalFrame X trivial r1 (devOnlyRefl σ)
      ⟨.pure (), none, .eq, vsOkIdle _, by rw [hdp]; exact .fin, ?_⟩
    rw [hd', setDvirtioSelf]; exact hag
  · cases (Prod.mk.inj hp).2

/-- The burst's end `DRet DIdle`: 1 → 0. -/
theorem caseFin {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {l : Wlabel}
    {σ : MState} (X : DCtx c c' st rest l σ) {dp' : Option (DM Dres)} {ts : List Expr}
    (hpd : pdiskProg (some (DRet DIdle)) c.pcDev.efDev l dp' c'.pcDev.efDev)
    (hag : devAgree .eq c.pcDev.efDev σ.devs) :
    DiskGoal c' (st ++ [(NCPU, l)]) dp' (Expr.dev 0 .virtio rootTask (.pure ()) :: ts) σ := by
  obtain ⟨hl, hd', hst | hid⟩ := pdpRet hpd
  · cases hst.1
  · obtain ⟨-, hdp⟩ := hid
    subst hl
    refine goalFrame X trivial (vrunRefl _ σ) (devOnlyRefl σ)
      ⟨.pure (), none, .eq, vsOkIdle _, by rw [hdp]; exact .idle, ?_⟩
    rw [hd']; exact hag

theorem lenOf {ts : List Expr} {j : Nat} {e : Expr} (h : ts[j]? = some e) : j < ts.length := by
  rcases Nat.lt_or_ge j ts.length with hlt | hge
  · exact hlt
  · rw [List.getElem?_eq_none hge] at h; cases h

/-- **THE DISK ROWS** (F9, discharging W4's former `Hyps.disk`): a step of the disk agent's own
program (kind `.disk`) from a related configuration is a silent run of MachCSL's virtio threads
(the root `Virtio.body` at `NCPU + 4`, the live `serve` task after it) that re-establishes the
relation — `R-dev` included.  One row per `PosRel` position (`caseIdle` … `caseFin`). -/
theorem simDisk {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)} {t : List Expr}
    {g : GState} {l : Wlabel} (hR : SimRel c st t g) (hs : wpPfStep pstepEv pclsEv NCPU l c c')
    (hfT : pfLoadFactsT TsoShadow.cohSrc st c NCPU l) (hk : kindOk c NCPU l c' .disk)
    (hadj : pairAdjacent (st ++ (NCPU, l) :: rest)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      MRun m (t, g) [] (t', g') ∧ SimRel c' (st ++ [(NCPU, l)]) t' g' := by
  obtain ⟨hgen, hpow, ⟨H, vs, dp, dws, dpr, ht, hlen, hharts, hdisk, mr, ot, κ, ⟨ts, hvs, hot⟩,
    hpos, hag⟩, hmem, hview, hauth, hcoh⟩ := hR
  obtain ⟨ag, p', ws', hlk, hks, himg, hags⟩ := hk
  rw [hdisk] at hlk
  cases hlk
  cases p' with
  | PHart _ _ _ _ _ => exact hks.elim
  | PDisk dp' =>
  obtain ⟨hpd, hdev⟩ := hks
  have X : DCtx c c' st rest l g.m := ⟨hs, hadj, hmem, hview, hfT⟩
  have hgoal : DiskGoal c' (st ++ [(NCPU, l)]) dp' vs g.m := by
    subst hvs
    cases hpos with
    | idle => exact caseIdle X hpd hag
    | start v0 => exact caseStart X v0 hpd hag
    | ai v0 a => exact caseAi X v0 a hpd hag
    | ring h => exact caseRing X h hpd hag
    | fetch h P M hfc =>
      obtain ⟨j, tid, htk⟩ := hot _ rfl
      rw [← setSelfOf htk]
      exact caseFetch X (lenOf htk) h P M hfc hpd hag
    | capZ h r bs hout hbs =>
      obtain ⟨j, tid, htk⟩ := hot _ rfl
      rw [← setSelfOf htk]
      exact caseCapZ X (lenOf htk) h r bs hpd hag
    | capF h r bs hout hbs =>
      obtain ⟨j, tid, htk⟩ := hot _ rfl
      rw [← setSelfOf htk]
      exact caseCapF X (lenOf htk) h r bs hbs hpd hag
    | capB h r bs hout hbs =>
      obtain ⟨j, tid, htk⟩ := hot _ rfl
      rw [← setSelfOf htk]
      exact caseCapB X (lenOf htk) h r bs hpd hag
    | served h r =>
      obtain ⟨j, tid, htk⟩ := hot _ rfl
      rw [← setSelfOf htk]
      exact caseServed X (lenOf htk) h r hpd hag
    | status h r =>
      obtain ⟨j, tid, htk⟩ := hot _ rfl
      rw [← setSelfOf htk]
      exact caseStatus X (lenOf htk) h r hpd hag
    | fence h r ui cf =>
      obtain ⟨j, tid, htk⟩ := hot _ rfl
      rw [← setSelfOf htk]
      exact caseFence X (lenOf htk) h r ui cf hpd hag
    | idx h r ui cf =>
      obtain ⟨j, tid, htk⟩ := hot _ rfl
      rw [← setSelfOf htk]
      exact caseIdx X (lenOf htk) h r ui cf hpd hag
    | fin => exact caseFin X hpd hag
    | stall => exact caseStall X hpd hag
  obtain ⟨n, vs', σ', hr, hregs, hm', hv', hds⟩ := hgoal
  refine ⟨n, poolOf H c.pcDev vs', { g with m := σ' }, ?_, hgen, hpow,
    ⟨H, vs', dp', ws', dpr, ?_, ?_, fun cpu => ?_, ?_, hds⟩, hm', hv', authStep hs hauth,
    ownCohStep pstepEv pclsEv _ _ c c' hcoh hs⟩
  · rw [ht]; exact hr H c.pcDev g rfl ⟨hpow, hgen⟩
  · rw [hdev]; rfl
  · rw [hags, List.length_set, hlen]
  · obtain ⟨fn, ib, ws, pr, hl, hf⟩ := hharts cpu
    refine ⟨fn, ib, ws, pr, ?_, hf⟩
    have hregs' : ({ g with m := σ' } : GState).m.regs = g.m.regs := hregs
    rw [hags, List.getElem?_set_ne (by have := cpu.isLt; omega), hl, hregs']
  · rw [hags, List.getElem?_set_self (by rw [hlen]; omega)]

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
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (i : Nat) (rl : Bool) (b : Int) (data : List (BitVec 8)) (a2 v2 : List Dsrc) :
    ∀ {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab},
      contRC fok fcutT c st r cN → ∀ (m : Nat),
      (∀ w, w < m → ∃ l', (recLabels r)[w]? = some (i, l') ∧ lbAdmin false l') →
      (recLabels r)[m]? = some (i, .LExStore rl b data a2 v2) →
      ∀ (ag : Wpagent Pexv6) (R : Wresv), c.pcAgs[i]? = some ag → ag.paWs.wRes = some R →
        exclOkTs c.pcLog i b R.rvTs (c.pcLog.length + 1) := by
  intro c st r cN h
  induction h with
  | nil c st =>
    intro m _ hm
    simp [recLabels] at hm
  | cons c c' st j l k r cN hs _ _ _ _ _ ih =>
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
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c c1 cN : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {i : Nat} {aq : Bool} {base : Int}
    {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} {r : List PfRec}
    (hs : wpPfStep pstepEv pclsEv i (.LExLoad aq base tvs asrc) c c1)
    (hr : contRC fok fcutT c1 (st ++ [(i, .LExLoad aq base tvs asrc)]) r cN)
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

/-- **ONE pf step** is 0, 1 (or, for the disk program, `simDisk`'s block of) MachCSL steps,
observed by the record, re-establishing the relation. -/
theorem simStep {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {g0 : GState} {c0 : Wpcfg Pexv6 Efab}
    (hH : HypsC fok fcutT g0 c0) {c c' : Wpcfg Pexv6 Efab} {st rest : List (Nat × Wlabel)}
    {t : List Expr} {g : GState} {n : Nat} {κ : List Obs} {i : Nat} {l : Wlabel} {k : SKind}
    (hR : SimRel c st t g) (hreach : MRun n ([Expr.power], g0) κ (t, g))
    (hrun : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c)
    (hs : wpPfStep pstepEv pclsEv i l c c') (hf : pfStepFacts fok c i l)
    (hfT : pfLoadFactsT TsoShadow.cohSrc st c i l)
    (hcf : pfCutFactsT fcutT TsoShadow.cohSrc st c i l) (hk : kindOk c i l c' k)
    (hadj : pairAdjacent (st ++ (i, l) :: rest))
    (hex : ∀ aq base tvs asrc, l = .LExLoad aq base tvs asrc →
      exclOkTs c.pcLog i base (tvs.map Prod.fst) (c.pcLog.length + 1)) :
    ∃ (m : Nat) (t' : List Expr) (g' : GState),
      (k ≠ .disk → m ≤ 1) ∧ MRun m (t, g) (pfStepObs c i k) (t', g') ∧ SimRel c' (st ++ [(i, l)]) t' g' := by
  cases k with
  | node =>
    obtain ⟨m, t', g', hle, hm, hR'⟩ := simNode hH hR hreach hrun hs hf hfT hcf hk hadj hex
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
      simDisk hR hs hfT ⟨_, p', ws', hlk, hks, himg, hags⟩ hadj
    exact ⟨m, t', g', fun h => absurd rfl h, by simpa [pfStepObs] using hm, hR'⟩

/-- **THE MAIN INDUCTION** (F8), forward over the run record: from a related, boot-reachable
MachCSL configuration, the rest of the run is a MachCSL run observed by `pfObsOf`, ending
related to the pf run's last configuration. -/
theorem simRun {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {g0 : GState} {c0 : Wpcfg Pexv6 Efab}
    (hH : HypsC fok fcutT g0 c0) :
    ∀ {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab},
      contRC fok fcutT c st r cN →
      ∀ {t : List Expr} {g : GState} {n : Nat} {κ : List Obs},
        SimRel c st t g → MRun n ([Expr.power], g0) κ (t, g) →
        pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → pairAdjacent (st ++ recLabels r) →
        ∃ (m : Nat) (t' : List Expr) (g' : GState),
          MRun m ([Expr.power], g0) (κ ++ pfObsOf r) (t', g') ∧
          SimRel cN (st ++ recLabels r) t' g' := by
  intro c st r cN h
  induction h with
  | nil c st =>
    intro t g n κ hR hreach _ _
    exact ⟨n, t, g, by simpa [pfObsOf] using hreach, by simpa [recLabels] using hR⟩
  | cons c c' st i l k r cN hs hf hfT hcf hk hr ih =>
    intro t g n κ hR hreach hrun hadj
    have hadj' : pairAdjacent (st ++ (i, l) :: recLabels r) := by
      simpa [recLabels] using hadj
    obtain ⟨m1, t1, g1, -, hm1, hR1⟩ := simStep hH hR hreach hrun hs hf hfT hcf hk hadj'
      (fun aq base tvs asrc hl => by subst hl; exact exclAhead fok hs hr hadj')
    obtain ⟨m2, t2, g2, hm2, hR2⟩ :=
      ih hR1 (mrunTrans hreach hm1) (pfRunST.snoc c c' st i l hrun hs hf hfT)
      (by simpa using hadj')
    refine ⟨m2, t2, g2, ?_, by simpa [recLabels] using hR2⟩
    rw [pfObsOfCons, ← List.append_assoc]
    exact hm2

/-- **W4's THEOREM (F1–F9): a shaped pf run, PREFIXED by ONE `PowerOn` step, is a MachCSL run**
(plan §C W4; census §F; the disk rows F9 `simDisk`).  From the machine off (`g0`: generation 0, power off,
devices `ds`) and the pf boot `σ0` (`wbootFacts`, devices `ds.reset`), every `pfRunST` run from
`wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)` — `srvwmoXv6M1PfRun`'s configuration —
with `pairAdjacent` steps has a RUN RECORD `r` (its configurations and step kinds; its step list
is the run's) such that `([power], g0)` runs, in `n` thread-pool steps (no bound `n ≤ |st|`,
E-S6), observing `.powerOn :: pfObsOf r` (E-S3: a function of the record), to a configuration
related to the run's last one by `SimRel` (the pool by step kind, registers, `R-dev`, and
`R_mem` = `rmem ∧ viewRel cohSrc`).  Parametric in `Hyps` (W2 CLOSE's `pfStepTso`, HSafe, the
fetch cut and item (3)'s `fiArm` facts) — NOT in the disk rows, which F9 proves
(`simDisk`). -/
theorem machRunOfPfRun (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (σ0 : WGState) (ds : DevStates) (g0 : GState)
    (hb : wbootFacts σ0) (hds : σ0.wgdev = ds.reset) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hgd : g0.m.devs = ds)
    (hH : HypsC fok fcutT g0 (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)))
    (st : List (Nat × Wlabel)) (cN : Wpcfg Pexv6 Efab)
    (hrun : pfRunSTC pstepEv pclsEv fok TsoShadow.cohSrc fcutT
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cN)
    (hadj : pairAdjacent st) :
    ∃ r : List PfRec,
      contRC fok fcutT (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cN ∧
      recLabels r = st ∧
      ∃ (n : Nat) (t : List Expr) (g : GState),
        MRun n ([Expr.power], g0) (Obs.powerOn :: pfObsOf r) (t, g) ∧ SimRel cN st t g := by
  obtain ⟨r, hr, hl⟩ := contROfRun fok hrun
  have hboot := powerOnRun g0 σ0 ds hb hg0 hp0 hgd
  have hR0 := simRelBoot σ0 ds hb hds
  obtain ⟨m, t, g, hm, hR⟩ := simRun hH hr hR0 hboot pfRunST.nil (by simpa [hl] using hadj)
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

/-- **No log message writes a pristine-window byte** (factored out of `cutOfPristine`,
W-SCO [R28.2]): when the MachCSL state related to `c` keeps `[lo, hi) ⊆ DRAM` pristine, the
`R-hist` link of `SimRel` makes every window byte's history the image entry alone, so no message
of `c.pcLog` writes it. -/
theorem noWriteOfPristine (lo hi : Nat) (hlo : ramBase ≤ lo) (hhi : hi ≤ ramEnd)
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {t : List Expr} {g : GState}
    (hR : SimRel c st t g) (hwin : winPristine lo hi g) :
    ∀ a : Int, (lo : Int) ≤ a → a < (hi : Int) →
      ∀ i : Nat, c.pcLog[i]?.bind (fun m => msgByte m a) = none := by
  intro a h1 h2
  simp only [ramBase] at hlo
  simp only [ramEnd] at hhi
  have hpa : (BitVec.ofNat 64 a.toNat).toNat = a.toNat := by
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  have hram : inRam (BitVec.ofNat 64 a.toNat) 1 := by
    simp only [inRam, hpa, ramBase, ramEnd]
    omega
  obtain ⟨v, hv⟩ := hwin (BitVec.ofNat 64 a.toNat) (by omega) (by omega)
  have hh := hR.mem.2.2.1.1 _ hram
  rw [hv] at hh
  have hz : paZ (BitVec.ofNat 64 a.toNat) = a := by
    simp only [paZ, hpa]
    omega
  rw [hz] at hh
  exact histNoWrite _ _ _ _ (Option.some.inj hh).symm

/-- **`fetchIsImage`** (factored out of `cutOfPristine`, W-SCO [R28.2]): an admissible fetch
(`ifetchOk`, at any instruction view) of bytes no message of the log writes reads every byte at
timestamp `0`, i.e. the IMAGE's byte. -/
theorem fetchIsImage (img : Image) (log : List Wmsg) (itv : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (hif : ifetchOk img log itv base tvs)
    (hnw : ∀ j, j < tvs.length →
      ∀ i : Nat, log[i]?.bind (fun m => msgByte m (base + (j : Int))) = none) :
    ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
      t = 0 ∧ logByte img log 0 (base + (j : Int)) = some v := by
  intro j t v hj
  obtain ⟨hlb, -⟩ := hif j t v hj
  cases t with
  | zero => exact ⟨rfl, hlb⟩
  | succ i =>
    exfalso
    rw [logByteS, hnw j (lookup_lt_Some hj) i] at hlb
    cases hlb

/-- **M1's fetch cut** (`Hyps.cut` at `fok = candKfetch lo hi`): when every MachCSL state reachable
from boot keeps the window `[lo, hi) ⊆ DRAM` pristine (W5: `Xv6.powerInterp_textPristine`), a
fetch inside the window reads image bytes no log message ever wrote (`noWriteOfPristine`,
`fetchIsImage`), so ANY cut works — take the shadow's `itv` (TsoMem's own instruction view). -/
theorem cutOfPristine (lo hi : Nat) (hlo : ramBase ≤ lo) (hhi : hi ≤ ramEnd)
    (g0 : GState) (c0 : Wpcfg Pexv6 Efab)
    (htext : ∀ (n : Nat) (κs : List Obs) (t : List Expr) (g : GState),
      MRun n ([Expr.power], g0) κs (t, g) → g.pow = true → winPristine lo hi g) :
    ∀ (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab) (t : List Expr) (g : GState) (n : Nat)
      (κ : List Obs),
      pfRunST pstepEv pclsEv (candKfetch (lo : Int) (hi : Int)) TsoShadow.cohSrc c0 st c →
      MRun n ([Expr.power], g0) κ (t, g) → SimRel c st t g →
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
    exact noWriteOfPristine lo hi hlo hhi hR hwin _ h1 h2
  have ht0 : ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t = 0 :=
    fun j t v hj => (fetchIsImage _ _ _ _ _ hif hnw j t v hj).1
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
#print axioms Weak.MachOfPf.fetchIsImage
#print axioms Weak.MachOfPf.simDisk
