/-
Weak: **the definitional correspondence** between the event language and the promise-free
machine (spike S2, revised).

Rocq: `iris/WeakEvPf.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header, in substance

THE ROUTE.  The event language's configuration has a THIRD shared component besides the image
and the write log: the device fabric `wgdev`.  Since the G-series generalization
`WeakPromise.Wpcfg P D` carries it (`pcDev : D`), so the projection `ecfgOf` forgets nothing that
Layer 1 can hold.  The FABRIC-SHARED promise-free machine `epfStep i l ρ ρ'` (§3) is stated over
the language's own configuration (a pool record `Epool` and σ): each arm LITERALLY CONTAINS the
language's own step, decorated with the label its memory effect determines.  So ⇐ (every pf step
is an erased step, `epfStepErased`, §4) is a PROJECTION — naming the pool position and
re-assembling the pool — and ⇒ (every language event carries a label, `ecycleStepLabel` /
`ediskStepLabel`, §5) is a LABEL EXHIBITION — one case analysis, no invariant, no simulation.
The agents' PROGRAM state comes from the POOL (`Pexv6.PHart` carries the residual monad and the
parked fence, `Pexv6.PDisk` the residual device program), field for field (`eags`, §1).
RECORDED DEVIATION (Rocq budget): ⇒ is delivered at the STEP level only (the run-level form needs
a pool-shape inversion; ⇐ is the direction S3 consumes).  §6: the observation floor of a hart
agent IS its coherence floor, and `WeakGhost.noViolation` refutes Layer 1's `violationHart` at the
projected configuration (`noViolationViolationHart`), term for term.

LAYOUT.  Hart `c` at pool position and agent index `c.val`; the disk is agent `nDisk = NCPU`.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  `epool` ↦ the structure `Epool` (fields `epGen`,
   `epH`, `epDp`, `epDws` + deviation 2); `pexv6` ↦ `Pexv6`; `epf_step` ↦ the Prop-valued
   inductive `epfStep` (arms `EPFBoundary` … `EPFPlic` kept).  `fin_to_nat c` ↦ `c.val`;
   `enum CPU` ↦ `MachCSL.cpus` (`List.finRange NCPU`); `fin_enum n` ↦ `List.finRange n`;
   `l !! i` ↦ `l[i]?`; `<[i := x]> l` ↦ `l.set i x`; `tvs.*1` ↦ `tvs.map Prod.fst`;
   `S (length lg)` ↦ `lg.length + 1`; `oib32` ↦ `Ibch`; `regstate` ↦ `RegFile`;
   `dev_state` ↦ `DevStates`; `img_z` ↦ `imgZ`; `erased_step` ↦ iris-lean's
   `Language.ErasedStep` (at the instance `weakEvLang`); `rtc` ↦ `MachCSL.rtc`.
2. DEVICES (forced by Lean's device model, `Weak/WeakEvLang.lean` deviation 2).  Lean's UARTs and
   PLIC are device PROGRAMS (`EExpr.EDev gen d rootTask m`, stepped by `wdevStep`), not the
   stateless `EUart g`/`EPlic g` of Rocq, and `epowerFork` forks TWO UARTs.  So:
   - `Epool` gains the three residual device programs `epU0`, `epU1`, `epPlic` (Lean-only;
     accessor `epU`, updates `epUset`/`epPset`), and `epInit` starts them at `.pure ()`.
   - THE POOL LAYOUT is `epowerFork`'s: harts at `0 .. NCPU-1`, then `epoolTail` =
     `[uart0, uart1, disk, plic]` at `NCPU`, `NCPU+1`, `NCPU+2`, `NCPU+3` (Rocq: uart `NCPU`,
     disk `S NCPU`, plic `S (S NCPU)`).  `epoolList` = harts `++ epoolTail`.
   - `EPFUart` carries a `UartId`; its step is `wdevStep … (epU P i) σ m' σ' []` (Rocq
     `euart_step σ σ'`).  `EPFPlic` is ANY step of the PLIC program (Rocq: only the wire write);
     its agent is `plicAgent m` — the TARGET hart `cpu.val` when the program sits at a
     `setPin cpu …` node (the wire write, which moves that hart's register file, Rocq's
     `EPFPlic` at `fin_to_nat c`), and `nDisk` otherwise (the gateway's `choose`/`sample`/latch:
     fabric-only moves; Rocq attributed the latch, an `edisk_step` arm, to the disk agent).
   - Both device arms gain two premises Rocq's stateless steps satisfied by construction: the
     step FORKS NOTHING (`efs = []`: a fork would leave the pool shape; the board's UART/PLIC
     have task type `Empty` and never fork) and LEAVES THE LOG (`σ'.wglog = σ.wglog`: a residual
     `DevProg` may syntactically hold a `dmaWrite`; the board's UART/PLIC bodies never do).
     These are the `LDev` label's log clause, made explicit.  `epfStepErased` is unaffected
     (the language step is the same one).
   - `edisk_step`'s PLIC-latch arm does not exist (WeakEvLang deviation 2), so `ediskStepLabel`
     has seven arms; the latch is an `EPFPlic` step at agent `nDisk`.
   - `epool_list_uart_lookup` ↦ `epoolListUartLookup` (per `UartId`); Lean-only
     `epoolListPlicLookup`, `epoolListUset`, `epoolListPset`, `epoolListTailGet`,
     `epoolListTailSet` (the shared index arithmetic).  Rocq's `epf_step_erased` PLIC case
     inlines the lookup; Lean names it.
3. O2 — THE INSTRUCTION FETCH (`Weak/WeakEvLang.lean` deviation 5; owner decision D4).  The
   language's RAM-read arm has a third, i-cache branch, so `elabelOk` gains the clause
   `LIFetch base tvs ↦ ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base tvs ∧ log ∧ view
   unchanged` (at the hart's own instruction view, Stage B), and `ecycleStepLabel` exhibits it.
   `edlabelOk (LIFetch ..)` is `False` (the disk never fetches).  The FETCH → PLAIN LOAD
   premise of the bridge (`WeakPromiseBridge.pfFetchLoadOk`, its deviation 6) is NOT folded into
   `elabelOk`: a stale pre-`fence.i` fetch is a legal language event whose bytes need not be
   readable, so folding it in would falsify ⇒.  Lean-only bridges for the consumer:
   `elabelOkIFetch0` (the language's check implies `PFIFetch`'s view-0 check, `ifetchOkAnti`)
   and `pfFetchLoadOkHart` (the premise at a hart agent of `ecfgOf` is a statement about
   `σ.wgws c`).
4. O2 STAGE B — the barrier arm also moves `wgitv` (`ewgBar`); `elabelOk`'s clauses speak only of
   the log and the data view, so `fence.i` (`ebarNow = none`) is `LSilent` as in Rocq and the
   other ten barriers `LFence`.  The label is read off `ebarNow b` (Rocq: an eleven-way
   `destruct b`).
5. THE OPERAND LISTS.  The Lean language's store and exclusive-read arms carry the DECODED
   operand lists (`depsAsrc`/`depsVsrc (edeps σ c)`), so `ecycleStepLabel` exhibits those (Rocq's
   comment about empty lists predates D3; Rocq's proof also exhibits the arm's own lists).
   `elabelOk`'s clauses are Rocq's verbatim.
6. `wbytes_ne` is `WeakInterpProj.wbytesNonnil` (already in the tree); `wbytesNe` is kept as a
   name for it.  `epool_list_id` ↦ `epoolListId` stated over `List.set`.
7. `fin_enum_lookup` & co. are about `List.finRange` (Rocq `fin_enum`); `fmap_enum_hset` uses
   `if c' = c` (Rocq `decide`).
8. PROOFS: `epfRunLive` / `epfRtcErased` by tail induction on `rtc` (Rocq: head induction).
9. THE FABRIC TYPE (owner decision Q1, `notes/weak-port-architecture.md`).  `ecfgOf` carries
   `Efab` (Lean-only: `DevStates` plus the residual programs `efU0`/`efU1`/`efPlic` of the
   UARTs and the PLIC, read off the pool), not `DevStates` (Rocq `dev_state`): Rocq's UART and
   PLIC were stateless, Lean's are programs, and Layer 1's program half must step them exactly
   (`WeakEvInst` deviation 5).  So `ecfgOf : Epool → WGState → Wpcfg Pexv6 Efab`, with
   `pcDev = efabOf P σ`.  Lean-only: `Efab`, `efU`, `efUset`, `efabOf`, `efInit`, `efabOfInit`,
   `efUOf`.

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Rocq → Lean name map.**  `fin_enum_lookup` `finEnumLookup`, `fin_enum_lookup_nat`
`finEnumLookupNat`, `fin_enum_length` `finEnumLength`, `enum_CPU_lookup` `enumCPULookup`,
`enum_CPU_length` `enumCPULength`, `ehst` `ehst`, `ehexp` `ehexp`, `epool`/`EPool` `Epool`/
`Epool.mk`, `ep_gen`/`ep_h`/`ep_dp`/`ep_dws` `Epool.epGen`/`epH`/`epDp`/`epDws`, `ehexpr`
`ehexpr`, `epool_list` `epoolList`, `ep_hset` `epHset`, `ep_dset` `epDset`, `ep_init` `epInit`,
`epool_list_init` `epoolListInit`, `pexv6` `Pexv6` (`PHart`, `PDisk`), `ehart_m` `ehartM`,
`ehart_fn` `ehartFn`, `ehexp_sail` `ehexpSail`, `ehart_ag` `ehartAg`, `edisk_ag` `ediskAg`,
`eags` `eags`, `ecfg_of` `ecfgOf`, `eags_hart` `eagsHart`, `eags_disk` `eagsDisk`, `eags_length`
`eagsLength`, `elabel_ok` `elabelOk`, `edlabel_ok` `edlabelOk`, `wbytes_ne` `wbytesNe`,
`epf_step` `epfStep` (`EPFBoundary`, `EPFCycle`, `EPFDisk`, `EPFUart`, `EPFPlic`), `epf_run`
`epfRun`, `epf_step_era` `epfStepEra`, `epf_step_live` `epfStepLive`, `epf_run_live`
`epfRunLive`, `erased_step_of_lookup` `erasedStepOfLookup`, `fmap_enum_hset` `fmapEnumHset`,
`epool_list_hart_lookup` `epoolListHartLookup`, `epool_list_hset` `epoolListHset`,
`epool_list_disk_lookup` `epoolListDiskLookup`, `epool_list_dset` `epoolListDset`,
`epool_list_uart_lookup` `epoolListUartLookup`, `epool_list_id` `epoolListId`,
`epf_step_erased` `epfStepErased`, `epf_rtc_erased` `epfRtcErased`, `ecycle_step_label`
`ecycleStepLabel`, `edisk_step_label` `ediskStepLabel`, `obs_flr_hart` `obsFlrHart`,
`ecfg_of_log` `ecfgOfLog`, `no_violation_violation_hart` `noViolationViolationHart`.
Lean-only: `Epool.epU0`/`epU1`/`epPlic`, `epU`, `epUset`, `epPset`, `epUsetGen`, `uartOff`,
`plicAgent`, `epoolTail`, `epoolListTailGet`, `epoolListTailSet`, `epoolListUset`,
`epoolListPlicLookup`, `epoolListPset`, `ediskStepEra`, `elabelOkIFetch0`, `pfFetchLoadOkHart`,
`Efab` & co. (deviation 9).

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all; the changed ones are listed above
(`Epool`, `epoolList`, `epInit`, `epfStep`'s device arms, `elabelOk`/`edlabelOk`'s `LIFetch`
clause, `epoolListUartLookup`).
-/
import Weak.WeakEvLang
import Weak.WeakRobustMain
import Weak.WeakGhost

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Iris.ProgramLogic
open Wlabel

/-! ## 0. `Fin`-indexed lookup, once -/

theorem finEnumLookup (n : Nat) (i : Fin n) : (List.finRange n)[i.val]? = some i := by
  rw [List.getElem?_eq_some_iff]
  exact ⟨by simp, by simp⟩

theorem finEnumLookupNat (n : Nat) :
    ∀ (j : Nat) (x : Fin n), (List.finRange n)[j]? = some x → x.val = j := by
  intro j x h
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 h
  rw [← heq]
  simp

theorem finEnumLength (n : Nat) : (List.finRange n).length = n := List.length_finRange

theorem enumCPULookup (c : CPU) : cpus[c.val]? = some c := finEnumLookup NCPU c

theorem enumCPULength : cpus.length = NCPU := finEnumLength NCPU

/-! ## 1. The pool, the program type and the agent layout -/

/-- A hart's whole thread state: `none` at the boundary, `some (m, fn)` mid instruction. -/
abbrev ehst : Type := Option (SailM Unit × Option (Bool × Bool × Bool × Bool))

def ehexp (gen : Nat) (c : CPU) (h : ehst) : EExpr :=
  match h with
  | none => ELoop gen c
  | some (m, fn) => ECycle gen c m fn

/-- The canonical pool of one era (deviation 2: plus the three residual device programs). -/
structure Epool where
  epGen : Nat
  epH : CPU → ehst
  /-- M5: the RESIDUAL DEVICE PROGRAM -/
  epDp : Option (DM Dres)
  epDws : Wstate
  /-- Lean-only: the residual programs of the two UARTs and the PLIC -/
  epU0 : DevProg (.uart .uart0)
  epU1 : DevProg (.uart .uart1)
  epPlic : DevProg .plic

def ehexpr (P : Epool) (c : CPU) : EExpr := ehexp P.epGen c (P.epH c)

/-- The device tail of the pool, `epowerFork`'s order (Lean-only). -/
def epoolTail (P : Epool) : List EExpr :=
  [.EDev P.epGen (.uart .uart0) rootTask P.epU0, .EDev P.epGen (.uart .uart1) rootTask P.epU1,
   .EDisk P.epGen P.epDp P.epDws, .EDev P.epGen .plic rootTask P.epPlic]

def epoolList (P : Epool) : List EExpr := cpus.map (ehexpr P) ++ epoolTail P

def epHset (P : Epool) (c : CPU) (h : ehst) : Epool :=
  { P with epH := fun c' => if c' = c then h else P.epH c' }

def epDset (P : Epool) (dp : Option (DM Dres)) (dws : Wstate) : Epool :=
  { P with epDp := dp, epDws := dws }

/-- A UART's residual program (Lean-only). -/
def epU (P : Epool) : (i : UartId) → DevProg (.uart i)
  | .uart0 => P.epU0
  | .uart1 => P.epU1

def epUset (P : Epool) : (i : UartId) → DevProg (.uart i) → Epool
  | .uart0, m => { P with epU0 := m }
  | .uart1, m => { P with epU1 := m }

def epPset (P : Epool) (m : DevProg .plic) : Epool := { P with epPlic := m }

theorem epUsetGen (P : Epool) (i : UartId) (m : DevProg (.uart i)) : (epUset P i m).epGen = P.epGen := by
  cases i <;> rfl

/-- A UART's offset in the device tail (Lean-only). -/
def uartOff : UartId → Nat
  | .uart0 => 0
  | .uart1 => 1

/-- The initial pool of a fresh era IS `epowerFork`. -/
def epInit (gen : Nat) : Epool := ⟨gen, fun _ => none, none, wsInit, .pure (), .pure (), .pure ()⟩

theorem epoolListInit (gen : Nat) : epoolList (epInit gen) = epowerFork gen := rfl

/-- A hart's PROGRAM state: the CPU, the residual monad, the register file, the parked fence and
(D3) the announced instruction bits; the disk's: its residual device program. -/
inductive Pexv6 where
  | PHart (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
      (ib : Ibch)
  | PDisk (dp : Option (DM Dres))

def ehartM (h : ehst) : SailM Unit :=
  match h with
  | some (m, _) => m
  | none => FreeM.pure ()

def ehartFn (h : ehst) : Option (Bool × Bool × Bool × Bool) :=
  match h with
  | some (_, fn) => fn
  | none => none

/-- ... and the expression IS that program state. -/
theorem ehexpSail (gen : Nat) (c : CPU) (h : ehst) :
    ehexp gen c h = .Sail gen c (ehartM h) (ehartFn h) := by
  rcases h with _ | ⟨m, fn⟩ <;> rfl

def ehartAg (P : Epool) (σ : WGState) (c : CPU) : Wpagent Pexv6 :=
  ⟨.PHart c (ehartM (P.epH c)) (σ.wgregs c) (ehartFn (P.epH c)) (σ.wgib c), σ.wgws c, ∅⟩

def ediskAg (P : Epool) : Wpagent Pexv6 := ⟨.PDisk P.epDp, P.epDws, ∅⟩

def eags (P : Epool) (σ : WGState) : List (Wpagent Pexv6) := cpus.map (ehartAg P σ) ++ [ediskAg P]

/-- THE FABRIC of the event instance (Lean-only, deviation 9; owner decision Q1): the device
states AND the residual programs of the two UARTs and the PLIC, so that Layer 1's program half
can step those programs exactly (`WeakEvInst.pstepPlic` / `pdiskUart`). -/
structure Efab where
  efDev : DevStates
  efU0 : DevProg (.uart .uart0)
  efU1 : DevProg (.uart .uart1)
  efPlic : DevProg .plic

/-- A UART's residual program in the fabric (Lean-only). -/
def efU (F : Efab) : (i : UartId) → DevProg (.uart i)
  | .uart0 => F.efU0
  | .uart1 => F.efU1

def efUset (F : Efab) : (i : UartId) → DevProg (.uart i) → Efab
  | .uart0, m => { F with efU0 := m }
  | .uart1, m => { F with efU1 := m }

/-- The fabric of a pool and a state (Lean-only). -/
def efabOf (P : Epool) (σ : WGState) : Efab := ⟨σ.wgdev, P.epU0, P.epU1, P.epPlic⟩

/-- The fabric of a fresh era: every residual device program at `.pure ()` (Lean-only). -/
def efInit (ds : DevStates) : Efab := ⟨ds, .pure (), .pure (), .pure ()⟩

theorem efabOfInit (gen : Nat) (σ : WGState) : efabOf (epInit gen) σ = efInit σ.wgdev := rfl

theorem efUOf (P : Epool) (σ : WGState) (i : UartId) : efU (efabOf P σ) i = epU P i := by
  cases i <;> rfl

/-- THE PROJECTION to a `WeakPromise` configuration; the fabric is carried (deviation 9: with
the residual UART/PLIC programs). -/
def ecfgOf (P : Epool) (σ : WGState) : Wpcfg Pexv6 Efab :=
  ⟨imgZ σ.wgimg, σ.wglog, efabOf P σ, eags P σ⟩

theorem eagsHart (P : Epool) (σ : WGState) (c : CPU) : (eags P σ)[c.val]? = some (ehartAg P σ c) := by
  unfold eags
  rw [List.getElem?_append_left (by simp [enumCPULength, c.isLt]), List.getElem?_map,
    enumCPULookup]
  rfl

theorem eagsDisk (P : Epool) (σ : WGState) : (eags P σ)[nDisk]? = some (ediskAg P) := by
  unfold eags
  rw [List.getElem?_append_right (by simp [enumCPULength, nDisk])]
  simp [enumCPULength, nDisk]

theorem eagsLength (P : Epool) (σ : WGState) : (eags P σ).length = NCPU + 1 := by
  simp [eags, enumCPULength]

/-! ## 2. The labels: reading a `Wlabel` off a transition -/

/-- "The memory effect of hart `c`'s transition IS the label `l`", with exactly the side
conditions and view updates of `WeakPromiseBridge.wpPfStep`'s arms (deviation 3: the `LIFetch`
clause, at the hart's own instruction view). -/
def elabelOk (σ : WGState) (c : CPU) (l : Wlabel) (σ' : WGState) : Prop :=
  match l with
  | LSilent => σ'.wglog = σ.wglog ∧ σ'.wgws c = σ.wgws c
  | LLoad aq lat base tvs asrc =>
      lat = false ∧ asrc = [] ∧
      readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) aq lat base tvs ∧
      σ'.wglog = σ.wglog ∧
      σ'.wgws c = loadPostRun (σ.wgws c) aq base (tvs.map Prod.fst)
  | LStore rl base data asrc vsrc =>
      (∃ k, σ'.wglog = σ.wglog ++ [⟨base, data, some c.val, k⟩]) ∧
      data ≠ [] ∧
      σ'.wgws c = storePostRunD (σ.wgws c) rl (srcsView (σ.wgws c) asrc)
                    (srcsView (σ.wgws c) vsrc) base data.length (σ.wglog.length + 1)
  | LRmw aq rl base tvs data asrc vsrc =>
      data ≠ [] ∧ tvs.length = data.length ∧
      readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) aq false base tvs ∧
      exclOk σ.wglog c.val base tvs (σ.wglog.length + 1) ∧
      (∃ k, σ'.wglog = σ.wglog ++ [⟨base, data, some c.val, k⟩]) ∧
      σ'.wgws c = storePostRunD
                    (loadPostRunD (σ.wgws c) aq (srcsView (σ.wgws c) asrc) base
                       (tvs.map Prod.fst))
                    rl (srcsView (σ.wgws c) asrc) (srcsView (σ.wgws c) vsrc)
                    base data.length (σ.wglog.length + 1)
  | LFence pr pw sr sw =>
      σ'.wglog = σ.wglog ∧ σ'.wgws c = fencePost (σ.wgws c) pr pw sr sw
  -- THE FABRIC MARKER (M5): `LSilent`'s twin
  | LDev => σ'.wglog = σ.wglog ∧ σ'.wgws c = σ.wgws c
  -- D3-2: the three dependency-only labels
  | LRegW rd srcs =>
      σ'.wglog = σ.wglog ∧ σ'.wgws c = regwPost (σ.wgws c) rd (srcsView (σ.wgws c) srcs)
  | LCtrl srcs =>
      σ'.wglog = σ.wglog ∧ σ'.wgws c = ctrlPost (σ.wgws c) (srcsView (σ.wgws c) srcs)
  | LInstr => σ'.wglog = σ.wglog ∧ σ'.wgws c = instrPost (σ.wgws c)
  -- THE RMW SPLIT (S3): the two halves
  | LExLoad aq base tvs asrc =>
      readOk (imgZ σ.wgimg) σ.wglog (σ.wgws c) aq false base tvs ∧
      σ'.wglog = σ.wglog ∧
      σ'.wgws c = exloadPostRunD (σ.wgws c) aq (srcsView (σ.wgws c) asrc) base (tvs.map Prod.fst)
  | LExStore rl base data asrc vsrc =>
      (∃ k, σ'.wglog = σ.wglog ++ [⟨base, data, some c.val, k⟩]) ∧
      data ≠ [] ∧
      exwinOk σ.wglog c.val (σ.wgws c) base data.length (σ.wglog.length + 1) ∧
      σ'.wgws c = storePostRunD (σ.wgws c) rl (srcsView (σ.wgws c) asrc)
                    (srcsView (σ.wgws c) vsrc) base data.length (σ.wglog.length + 1)
  -- O2 (deviation 3): THE I-CACHE READ, view-silent, at the hart's instruction view
  | LIFetch base tvs =>
      ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base tvs ∧
      σ'.wglog = σ.wglog ∧ σ'.wgws c = σ.wgws c

/-- The disk agent's version (its own view lives in the pool). -/
def edlabelOk (P : Epool) (σ : WGState) (l : Wlabel) (dws' : Wstate) (σ' : WGState) : Prop :=
  match l with
  | LSilent => σ'.wglog = σ.wglog ∧ dws' = P.epDws
  | LLoad aq lat base tvs asrc =>
      lat = false ∧ asrc = [] ∧
      readOk (imgZ σ.wgimg) σ.wglog P.epDws aq lat base tvs ∧
      σ'.wglog = σ.wglog ∧
      dws' = loadPostRun P.epDws aq base (tvs.map Prod.fst)
  | LStore rl base data asrc vsrc =>
      asrc = [] ∧ vsrc = [] ∧
      (∃ k, σ'.wglog = σ.wglog ++ [⟨base, data, some nDisk, k⟩]) ∧
      data ≠ [] ∧
      dws' = storePostRun P.epDws rl base data.length (σ.wglog.length + 1)
  | LFence pr pw sr sw => σ'.wglog = σ.wglog ∧ dws' = fencePost P.epDws pr pw sr sw
  | LDev => σ'.wglog = σ.wglog ∧ dws' = P.epDws
  | LRmw .. => False
  | LRegW .. | LCtrl _ | LInstr => False
  | LExLoad .. | LExStore .. => False
  -- O2: the disk never fetches
  | LIFetch .. => False

/-- Rocq `wbytes_ne` (deviation 6). -/
theorem wbytesNe (n : Nat) {w : Nat} (v : BitVec w) : n ≠ 0 → WeakInterpProj.wbytes n v ≠ [] :=
  wbytesNonnil n v

/-- O2 (Lean-only): the language's fetch check implies the pf machine's view-0 check. -/
theorem elabelOkIFetch0 (σ : WGState) (c : CPU) (base : Int) (tvs : List (Nat × BitVec 8))
    (σ' : WGState) :
    elabelOk σ c (.LIFetch base tvs) σ' → ifetchOk (imgZ σ.wgimg) σ.wglog 0 base tvs :=
  fun h => ifetchOkAnti _ _ _ _ _ _ (Nat.zero_le _) h.1

/-- O2 (Lean-only): the bridge's fetch premise at a hart agent of the projection. -/
theorem pfFetchLoadOkHart (P : Epool) (σ : WGState) (c : CPU) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    pfFetchLoadOk (ecfgOf P σ) c.val (.LIFetch base tvs) ↔
      ((∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
          readable (imgZ σ.wgimg) σ.wglog (σ.wgws c) (loadVpre (σ.wgws c) false)
            (base + (j : Int)) t) ∧
        wsEqr (loadPostRun (σ.wgws c) false base (tvs.map Prod.fst)) (σ.wgws c)) := by
  constructor
  · intro h
    exact h _ (eagsHart P σ c)
  · intro h ag hag
    have hag' : (eags P σ)[c.val]? = some ag := hag
    rw [eagsHart] at hag'
    cases hag'
    exact h

/-! ## 3. THE FABRIC-SHARED PROMISE-FREE MACHINE -/

/-- The PLIC step's agent (deviation 2, Lean-only): the target hart at a wire write, the
fabric owner (the disk) otherwise. -/
def plicAgent : DevProg .plic → Nat
  | .op (.setPin cpu _ _) _ => cpu.val
  | _ => nDisk

inductive epfStep : Nat → Wlabel → (Epool × WGState) → (Epool × WGState) → Prop where
  /-- THE RESTART: clears the announced bits and is the reset point (`LInstr`). -/
  | EPFBoundary (c : CPU) (P : Epool) (σ : WGState) (tick : Bool) :
      ethreadLive σ P.epGen → P.epH c = none →
      epfStep c.val .LInstr (P, σ)
        (epHset P c (some (riscvStep tick, none)), ewgIbws σ c ibNone (instrPost (σ.wgws c)))
  | EPFCycle (c : CPU) (l : Wlabel) (P : Epool) (σ : WGState) (m : SailM Unit)
      (fn : Option (Bool × Bool × Bool × Bool)) (h' : ehst) (σ' : WGState) :
      ethreadLive σ P.epGen → P.epH c = some (m, fn) →
      ecycleStep P.epGen σ c m fn (ehexp P.epGen c h') σ' →
      elabelOk σ c l σ' →
      epfStep c.val l (P, σ) (epHset P c h', σ')
  | EPFDisk (l : Wlabel) (P : Epool) (σ : WGState) (dp' : Option (DM Dres)) (dws' : Wstate)
      (σ' : WGState) :
      ethreadLive σ P.epGen →
      ediskStep P.epGen P.epDp P.epDws σ (.EDisk P.epGen dp' dws') σ' →
      edlabelOk P σ l dws' σ' →
      epfStep nDisk l (P, σ) (epDset P dp' dws', σ')
  /-- A UART step: a fabric-touching silent step of the disk agent (deviation 2). -/
  | EPFUart (i : UartId) (P : Epool) (σ σ' : WGState) (m' : DevProg (.uart i)) :
      ethreadLive σ P.epGen →
      wdevStep P.epGen (.uart i) rootTask (epU P i) σ m' σ' [] →
      σ'.wglog = σ.wglog →
      epfStep nDisk .LDev (P, σ) (epUset P i m', σ')
  /-- A PLIC step: the wire write at its target hart, the gateway at the disk (deviation 2). -/
  | EPFPlic (P : Epool) (σ σ' : WGState) (m' : DevProg .plic) :
      ethreadLive σ P.epGen →
      wdevStep P.epGen .plic rootTask P.epPlic σ m' σ' [] →
      σ'.wglog = σ.wglog →
      epfStep (plicAgent P.epPlic) .LDev (P, σ) (epPset P m', σ')

def epfRun (ρ ρ' : Epool × WGState) : Prop := ∃ i l, epfStep i l ρ ρ'

/-- The disk's step keeps the era (Lean-only). -/
theorem ediskStepEra (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState) (e' : EExpr)
    (σ' : WGState) : ediskStep gen dp dws σ e' σ' → σ'.wgpow = σ.wgpow ∧ σ'.wggen = σ.wggen := by
  rintro (⟨-, -, rfl⟩ | ⟨pa, n, aq, k, tvs, -, -, -, -, rfl⟩ | ⟨pa, bs, k, -, -, -, rfl⟩ |
    ⟨k, -, -, rfl⟩ | ⟨delta, -, -, rfl⟩ | ⟨prog', -, -, -, rfl⟩ | ⟨-, -, rfl⟩) <;>
    exact ⟨rfl, rfl⟩

/-- THE ERA IS FIXED across the pf machine. -/
theorem epfStepEra (i : Nat) (l : Wlabel) (ρ ρ' : Epool × WGState) :
    epfStep i l ρ ρ' →
    ρ'.2.wgpow = ρ.2.wgpow ∧ ρ'.2.wggen = ρ.2.wggen ∧ ρ'.1.epGen = ρ.1.epGen := by
  intro h
  cases h with
  | EPFBoundary c P σ tick _ _ => exact ⟨rfl, rfl, rfl⟩
  | EPFCycle c l P σ m fn h' σ' _ _ hcy _ =>
    obtain ⟨h1, h2⟩ := ecycleStepEra _ _ _ _ _ _ _ hcy
    exact ⟨h1, h2, rfl⟩
  | EPFDisk l P σ dp' dws' σ' _ hs _ =>
    obtain ⟨h1, h2⟩ := ediskStepEra _ _ _ _ _ _ hs
    exact ⟨h1, h2, rfl⟩
  | EPFUart i P σ σ' m' _ hs _ =>
    have hf := wdevStepFrame hs
    exact ⟨hf.2.2.2.2.1, hf.2.2.2.1, epUsetGen P i m'⟩
  | EPFPlic P σ σ' m' _ hs _ =>
    have hf := wdevStepFrame hs
    exact ⟨hf.2.2.2.2.1, hf.2.2.2.1, rfl⟩

theorem epfStepLive (gen i : Nat) (l : Wlabel) (ρ ρ' : Epool × WGState) :
    ethreadLive ρ.2 gen → ρ.1.epGen = gen → epfStep i l ρ ρ' →
    ethreadLive ρ'.2 gen ∧ ρ'.1.epGen = gen := by
  intro hl hP hs
  obtain ⟨h1, h2, h3⟩ := epfStepEra i l ρ ρ' hs
  exact ⟨⟨h1.trans hl.1, h2.trans hl.2⟩, h3.trans hP⟩

theorem epfRunLive (gen : Nat) (ρ ρ' : Epool × WGState) :
    ethreadLive ρ.2 gen → ρ.1.epGen = gen → rtc epfRun ρ ρ' →
    ethreadLive ρ'.2 gen ∧ ρ'.1.epGen = gen := by
  intro hl hP hr
  induction hr with
  | refl => exact ⟨hl, hP⟩
  | tail _ hs ih =>
    obtain ⟨i, l, hs⟩ := hs
    exact epfStepLive gen i l _ _ ih.1 ih.2 hs

/-! ## 4. ⇐ : EVERY PF STEP IS AN ERASED STEP -/

/-- A thread at a known position steps the whole pool. -/
theorem erasedStepOfLookup (t : List EExpr) (i : Nat) (e e' : EExpr) (σ σ' : WGState) :
    t[i]? = some e → eprimStep e σ [] e' σ' [] →
    Language.ErasedStep (t, σ) (t.set i e', σ') := by
  intro hi hs
  refine ⟨[], ?_⟩
  have := Language.step_update_of_getElem? (Λ := weakEvLang) (obs := []) (efs := []) σ σ' hi hs
  rw [List.append_nil] at this
  exact this

theorem fmapEnumHset (gen : Nat) (f : CPU → ehst) (c : CPU) (h : ehst) :
    cpus.map (fun c' => ehexp gen c' (if c' = c then h else f c'))
      = (cpus.map (fun c' => ehexp gen c' (f c'))).set c.val (ehexp gen c h) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set, List.getElem?_map, List.getElem?_map]
  by_cases hj : c.val = j
  · subst hj
    rw [enumCPULookup]
    simp [enumCPULength, c.isLt]
  · rw [if_neg hj]
    cases hc : cpus[j]? with
    | none => rfl
    | some c0 =>
      have hne : c0 ≠ c := by
        intro he
        exact hj (by rw [← he]; exact finEnumLookupNat NCPU j c0 hc)
      simp [hne]

theorem epoolListHartLookup (P : Epool) (c : CPU) : (epoolList P)[c.val]? = some (ehexpr P c) := by
  unfold epoolList
  rw [List.getElem?_append_left (by simp [enumCPULength, c.isLt]), List.getElem?_map,
    enumCPULookup]
  rfl

theorem epoolListHset (P : Epool) (c : CPU) (h : ehst) :
    (epoolList P).set c.val (ehexp P.epGen c h) = epoolList (epHset P c h) := by
  unfold epoolList
  rw [List.set_append_left _ _ (by simp [enumCPULength, c.isLt])]
  exact congrArg (· ++ epoolTail P) (fmapEnumHset P.epGen P.epH c h).symm

/-- The device tail's index arithmetic (Lean-only). -/
theorem epoolListTailGet (P : Epool) (k : Nat) : (epoolList P)[NCPU + k]? = (epoolTail P)[k]? := by
  unfold epoolList
  rw [List.getElem?_append_right (by simp [enumCPULength])]
  simp [enumCPULength]

theorem epoolListTailSet (P : Epool) (k : Nat) (x : EExpr) :
    (epoolList P).set (NCPU + k) x = cpus.map (ehexpr P) ++ (epoolTail P).set k x := by
  unfold epoolList
  rw [List.set_append_right _ _ (by simp [enumCPULength])]
  simp [enumCPULength]

theorem epoolListDiskLookup (P : Epool) :
    (epoolList P)[NCPU + 2]? = some (.EDisk P.epGen P.epDp P.epDws) := by
  rw [epoolListTailGet]
  rfl

theorem epoolListDset (P : Epool) (dp : Option (DM Dres)) (dws : Wstate) :
    (epoolList P).set (NCPU + 2) (.EDisk P.epGen dp dws) = epoolList (epDset P dp dws) := by
  rw [epoolListTailSet]
  rfl

theorem epoolListUartLookup (P : Epool) (i : UartId) :
    (epoolList P)[NCPU + uartOff i]? = some (.EDev P.epGen (.uart i) rootTask (epU P i)) := by
  rw [epoolListTailGet]
  cases i <;> rfl

theorem epoolListUset (P : Epool) (i : UartId) (m : DevProg (.uart i)) :
    (epoolList P).set (NCPU + uartOff i) (.EDev P.epGen (.uart i) rootTask m)
      = epoolList (epUset P i m) := by
  rw [epoolListTailSet]
  cases i <;> rfl

theorem epoolListPlicLookup (P : Epool) :
    (epoolList P)[NCPU + 3]? = some (.EDev P.epGen .plic rootTask P.epPlic) := by
  rw [epoolListTailGet]
  rfl

theorem epoolListPset (P : Epool) (m : DevProg .plic) :
    (epoolList P).set (NCPU + 3) (.EDev P.epGen .plic rootTask m) = epoolList (epPset P m) := by
  rw [epoolListTailSet]
  rfl

theorem epoolListId (t : List EExpr) (i : Nat) (e : EExpr) : t[i]? = some e → t.set i e = t := by
  intro h
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 h
  subst heq
  exact List.set_getElem_self hlt

theorem epfStepErased (i : Nat) (l : Wlabel) (ρ ρ' : Epool × WGState) :
    epfStep i l ρ ρ' → Language.ErasedStep (epoolList ρ.1, ρ.2) (epoolList ρ'.1, ρ'.2) := by
  intro h
  cases h with
  | EPFBoundary c P σ tick hl hh =>
    dsimp only
    -- the boundary: fetch a fresh instruction
    rw [← epoolListHset P c (some (riscvStep tick, none))]
    refine erasedStepOfLookup _ _ _ _ _ _ (epoolListHartLookup P c) ?_
    have he : ehexpr P c = ELoop P.epGen c := by simp [ehexpr, hh, ehexp]
    rw [he]
    exact eprimStepLoopLive P.epGen c σ tick hl
  | EPFCycle c l P σ m fn h' σ' hl hh hcy _ =>
    dsimp only
    -- one event of the cycle
    rw [← epoolListHset P c h']
    refine erasedStepOfLookup _ _ _ _ _ _ (epoolListHartLookup P c) ?_
    have he : ehexpr P c = ECycle P.epGen c m fn := by simp [ehexpr, hh, ehexp]
    rw [he]
    exact ⟨rfl, rfl, Or.inl ⟨hl, hcy⟩⟩
  | EPFDisk l P σ dp' dws' σ' hl hs _ =>
    dsimp only
    rw [← epoolListDset P dp' dws']
    exact erasedStepOfLookup _ _ _ _ _ _ (epoolListDiskLookup P) ⟨rfl, rfl, Or.inl ⟨hl, hs⟩⟩
  | EPFUart i P σ σ' m' hl hs _ =>
    dsimp only
    rw [← epoolListUset P i m']
    exact erasedStepOfLookup _ _ _ _ _ _ (epoolListUartLookup P i)
      ⟨rfl, Or.inl ⟨hl, m', [], rfl, hs, rfl⟩⟩
  | EPFPlic P σ σ' m' hl hs _ =>
    dsimp only
    rw [← epoolListPset P m']
    exact erasedStepOfLookup _ _ _ _ _ _ (epoolListPlicLookup P)
      ⟨rfl, Or.inl ⟨hl, m', [], rfl, hs, rfl⟩⟩

theorem epfRtcErased (ρ ρ' : Epool × WGState) :
    rtc epfRun ρ ρ' →
    rtc (fun a b : List EExpr × WGState => Language.ErasedStep a b)
      (epoolList ρ.1, ρ.2) (epoolList ρ'.1, ρ'.2) := by
  intro h
  induction h with
  | refl => exact rtc_refl _
  | tail _ hs ih =>
    obtain ⟨i, l, hs⟩ := hs
    exact rtc_r ih (epfStepErased i l _ _ hs)

/-! ## 5. ⇒ : EVERY LANGUAGE EVENT CARRIES A LABEL -/

theorem ecycleStepLabel (gen : Nat) (σ : WGState) (c : CPU) (m : SailM Unit)
    (fn : Option (Bool × Bool × Bool × Bool)) (e' : EExpr) (σ' : WGState) :
    ecycleStep gen σ c m fn e' σ' → ∃ l, elabelOk σ c l σ' := by
  intro h
  match fn, h with
  | some (pr, pw, sr, sw), h =>
    obtain ⟨-, rfl⟩ := h
    exact ⟨.LFence pr pw sr sw, rfl, gwsInsertEq _ _ _⟩
  | none, h =>
    match m, h with
    | .pure _, h =>
      -- THE BOUNDARY: `LInstr`, the reset point
      obtain ⟨tick, -, rfl⟩ := h
      exact ⟨.LInstr, rfl, gwsInsertEq _ _ _⟩
    | .impure (.error _) _, h => exact h.elim
    | .impure (.ok o) k, h =>
      cases o with
      | regRead r =>
        obtain ⟨-, rfl⟩ := h
        exact ⟨.LSilent, rfl, rfl⟩
      | regWrite r v =>
        -- D3-2: the register write's label is its classification's
        obtain ⟨-, rfl⟩ := h
        generalize erwOf (edeps σ c) (erds σ c) r = kk
        refine ⟨erwLabel kk, ?_⟩
        cases kk with
        | ERWnone => exact ⟨ewgRwLog _ _ _ _, ewgRwWs _ _ _ _⟩
        | ERWreg rd srcs => exact ⟨ewgRwLog _ _ _ _, ewgRwWs _ _ _ _⟩
        | ERWctrl srcs => exact ⟨ewgRwLog _ _ _ _, ewgRwWs _ _ _ _⟩
      | memRead n va req =>
        simp only [emonadStep, ecycleStep] at h
        split at h
        · obtain ⟨w, d', -, -, rfl⟩ := h
          exact ⟨.LDev, rfl, rfl⟩
        · rcases h with ⟨-, w, tvs, -, -, hif, -, rfl⟩ |
            ⟨-, ⟨-, w, tvs, -, -, hrd, -, rfl⟩ | ⟨-, w, tvs, -, -, hrd, -, rfl⟩⟩
          · -- O2: THE I-CACHE READ
            exact ⟨.LIFetch (paZ req.pa) tvs, hif, rfl, rfl⟩
          · exact ⟨.LLoad _ false (paZ req.pa) tvs [], rfl, rfl, hrd, rfl, gwsInsertEq _ _ _⟩
          · -- THE EXCLUSIVE READ (RMW split S3)
            exact ⟨.LExLoad _ (paZ req.pa) tvs (depsAsrc (edeps σ c)), hrd, rfl, gwsInsertEq _ _ _⟩
      | memWrite n va req =>
        simp only [emonadStep, ecycleStep] at h
        split at h
        · split at h
          · obtain ⟨d', -, -, rfl⟩ := h
            exact ⟨.LDev, rfl, rfl⟩
          · exact h.elim
        · split at h
          · rename_i v _
            rcases h with ⟨hn, ⟨-, -, rfl⟩ | ⟨-, ⟨hex, -, rfl⟩ | ⟨-, rfl⟩⟩⟩
            · refine ⟨.LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
                (depsAsrc (edeps σ c)) (depsVsrc (edeps σ c)), ⟨_, rfl⟩,
                wbytesNonnil n v hn, ?_⟩
              rw [wbytesLength]
              exact gwsInsertEq _ _ _
            · -- THE CONDITIONAL WRITE (RMW split S3)
              refine ⟨.LExStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
                (depsAsrc (edeps σ c)) (depsVsrc (edeps σ c)), ⟨_, rfl⟩,
                wbytesNonnil n v hn, ?_, ?_⟩
              · rw [wbytesLength]
                exact hex
              · rw [wbytesLength]
                exact gwsInsertEq _ _ _
            · -- THE RETRY SELF-LOOP: a silent, σ-preserving step
              exact ⟨.LSilent, rfl, rfl⟩
          · exact h.elim
      | barrier b =>
        obtain ⟨-, rfl⟩ := h
        cases hb : ebarNow b with
        | none =>
          refine ⟨.LSilent, rfl, ?_⟩
          rw [ewgBarWs]
          simp [efenceApply]
        | some q =>
          obtain ⟨pr, pw, sr, sw⟩ := q
          refine ⟨.LFence pr pw sr sw, rfl, ?_⟩
          rw [ewgBarWs]
          simp [efenceApply]
      | instrAnnounce n w =>
        -- D3-2: THE ANNOUNCE, `LInstr`
        obtain ⟨-, rfl⟩ := h
        exact ⟨.LInstr, rfl, gwsInsertEq _ _ _⟩
      | branchAnnounce _ _ => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | cacheOp _ => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | tlbi _ => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | takeException _ => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | returnException _ => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | translationStart _ => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | translationEnd _ => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | cycleCount => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | message _ => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | getCycleCount => obtain ⟨-, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | choose p => obtain ⟨ch, -, rfl⟩ := h; exact ⟨.LSilent, rfl, rfl⟩
      | readRam _ _ _ => exact h.elim
      | writeRam _ _ _ _ => exact h.elim

/-- THE DISK'S LABEL, one per arm of the M5 device program (seven arms, deviation 2). -/
theorem ediskStepLabel (P : Epool) (σ : WGState) (e' : EExpr) (σ' : WGState) :
    ediskStep P.epGen P.epDp P.epDws σ e' σ' →
    ∃ l dp' dws', e' = .EDisk P.epGen dp' dws' ∧ edlabelOk P σ l dws' σ' := by
  rintro (⟨-, rfl, rfl⟩ | ⟨pa, n, aq, k, tvs, -, -, hrd, rfl, rfl⟩ | ⟨pa, bs, k, -, hne, rfl, rfl⟩ |
    ⟨k, -, rfl, rfl⟩ | ⟨delta, -, rfl, rfl⟩ | ⟨prog', -, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩)
  · exact ⟨.LDev, _, _, rfl, rfl, rfl⟩
  · exact ⟨.LLoad aq false (paZ pa) tvs [], _, _, rfl, rfl, rfl, hrd, rfl, rfl⟩
  · exact ⟨.LStore false (paZ pa) bs [] [], _, _, rfl, rfl, rfl, ⟨_, rfl⟩, hne, rfl⟩
  · exact ⟨.LFence true true true true, _, _, rfl, rfl, rfl⟩
  · exact ⟨.LDev, _, _, rfl, rfl, rfl⟩
  · exact ⟨.LSilent, _, _, rfl, rfl, rfl⟩
  · exact ⟨.LSilent, _, _, rfl, rfl, rfl⟩

/-! ## 6. THE PROJECTION TO `Wpcfg` -/

theorem obsFlrHart (P : Epool) (σ : WGState) (c : CPU) (a : Int) :
    obsFlr (ecfgOf P σ) c.val a = coh (σ.wgws c) a := by
  unfold obsFlr
  rw [show (ecfgOf P σ).pcAgs = eags P σ from rfl, eagsHart]
  rfl

theorem ecfgOfLog (P : Epool) (σ : WGState) : (ecfgOf P σ).pcLog = σ.wglog := rfl

/-- THE φ TRANSPORT: `WeakGhost.noViolation` over σ REFUTES Layer 1's `violationHart` at the
projected configuration, at the hart bound `nDisk = NCPU`. -/
theorem noViolationViolationHart (P : Epool) (σ : WGState) :
    noViolation σ.wglog σ.wgws → ¬ violationHart clsOf pubOf nDisk (ecfgOf P σ) := by
  rintro hnv ⟨p, m, i, j, a, hp, ht, ⟨i', hti, hilt⟩, hcls, hpub, hne, ⟨j', hj, hjlt⟩, hb, hfl⟩
  have hii : i' = i := Option.some.inj (hti.symm.trans ht)
  rw [hii] at hilt
  rw [← Option.some.inj hj] at hjlt
  have hak : m.wmAk = .WCplain := by
    revert hcls
    unfold clsOf
    cases m.wmAk <;> simp
  have hnpub : ¬ wpublished σ.wglog m.wmTid p := fun hw => hpub ⟨p, m, rfl, hp, hw⟩
  have hlt := hnv p m ⟨i, hilt⟩ a hp ht hak hnpub hb ⟨j, hjlt⟩
    (fun h => hne (congrArg Fin.val h))
  have hfl' : obsFlr (ecfgOf P σ) j a = coh (σ.wgws ⟨j, hjlt⟩) a := obsFlrHart P σ ⟨j, hjlt⟩ a
  omega

end Weak
