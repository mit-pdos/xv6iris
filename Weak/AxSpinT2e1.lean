/-
Weak: **THEOREM 2 / certificate (b), NON-VACUITY, COMPUTATION HALF** — the CONCRETE 3-hart RACE
graph on which `allocpidRaceUnprovable` (AxSpinT2d) fires: hart A (0) runs xv6's real
inlined-allocpid segment (nextpid 1 → 2, pid 1, proc[0]); hart B (1) runs the same segment on
proc[1] up to and including its lock claim (`amoswap.w.aq`, row item `t2KA q0` = 26); THEN the
unlocked racer C (2) (`AxSpinT2d.rcM0`: `lw; addiw; sw nextpid`) reads A's 2 and stores 3; THEN
B finishes: its nextpid read (`t2KBd q0` = 35) reads C's 3, the scan sees proc[0].pid = 1 and
zeros (no collision), B stores nextpid 4 and `p->pid` 3.  This file: the literal rows, the
`graphOfSc` graph, its generic consistency / ctrl closure, the run read-back over a VARIABLE
drive result, the row premises of A / B and THE RACE FACTS.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §A.4, §C.6 (b) (in
../xv6iris-lbthm2); AxSpinT2d's header lists what this certificate must supply.  Modules:
`AxSpinT2e1` (this), `AxSpinT2e2` (B's drive), `AxSpinT2e3` (entry state + the capstone
`allocpidRaceCert`).

## The schedule is SC

The race needs no weak behaviour: `il` is a sequential interleaving (A's 134 memory events, B's
first 27, C's two, B's remaining 107), so `graphOfSc` (consistency by the GENERIC
`graphOfScCatT`) covers it.  The race is a LOCKING violation, not a memory-model one.

## What this file proves

§1 THE LITERAL.  `rowA` = (a′)'s hart A row (`AxSpinT2c1.rowA`, unchanged: A runs first in both
schedules); `encB` / `rowB` = B's row in the race schedule (generated offline by a Python replica
of `sim` — it reproduces (a′)'s literal from `il3` — and checked here by `rowsFixed`): versus
(a′) it differs in the nextpid read (3 from write 52 = C's store), the nextpid / `p->pid` store
values (4 / 3) and the later timestamps (shifted by C's one write); `rowC = AxSpinT2d.rcRow tsC
wC` (reads A's nextpid store = write 19, value 2; stores 3).  `il`; `rowsFixed` (the graph's rows
ARE the literal: ONE `decide +kernel`).
§2 THE GRAPH.  `gT E = graphOfSc img rows il E` for any emission `E`; `growR`, `gtGEq`;
`hartOkRow` (a hart's `hartOkB` share depends only on its own row, so A's (a′) drive
check transfers); `emsC` (C's emission, written by hand: load, the `addiw` register write with
its data source, store — the racer's data dependency); `cat`, `ctrl`; `runOfDrive` (generic
read-back of an unfolded drive + `finish2` equation to the `tierAAstep` RUN premise at every
`gT E`); `runAR` — A's run, read back from (a′)'s ALREADY-EVALUATED `AxSpinT2c2.chkA` (no
re-drive); `drvB`/`chkOfB`/`runOfChkB` for B's drive (evaluated in `AxSpinT2e2`).
§3 ROW PREMISES of A / B: `fullA`/`fullB` (`allocFull` at `q0`), `pinsA`/`pinsB` (`AllocPins`:
on B's race row the nextpid value is 3 — `≠ 1000`, no wrap, ≠ every scanned pid 1 / 0 — so the
race is INSIDE the theorem's Q18b scope), `readsOff` (no row read hits `σX`'s domain).
§4 THE RACE: `hartsIn` (gmo harts ⊆ [0, 1, 2]), `rowCEq` (`HrowC`), `rfRace` (`HrfB`: B's nextpid
read sources C's store `(2, 1)`), `ltRace` (`HltB`: C's store is gmo-after B's claim).

## Pins / honesty
* C is a HAND NODE (`hp cpu0 rcM0 zeroRegs`, as in AxSpinT2d / the AxSpinJ2 templates): its row
  is consumed by `AxSpinT2d.rcRun` (2 model steps), not by `drive2`; its emission is the
  hand-written `emsC` (it only fixes the graph's dependency edges; the racer's real data edge
  load → store is included).
* Every proof mentioning `AxSpinT2c2.drvA` / `AxSpinT2e2.drvB` goes through a read-back stated
  for a VARIABLE drive result (a `match` on the drive would make the kernel re-run it).

Reused: `AxSpinT2c1.img`/`dec`/`rowA`/`hartOkB`/`finish2`/`finish2Sound`/`emsOf`/`chkOf`/
`fullB`/`fullOfB`/`pinsB`/`pinsOfB`/`q0`/`sZ`/`fullLit`/`pinsLit`, `AxSpinT2c2.chkA`/`drvA`,
`AxSpinT2c5.readsOffB`, `AxSpinT2d.rcRow`/`nppaX`, `graphOfSc`/`graphOfScCatT`/
`graphOfScCtrlClosed`/`scProg`/`sim` (AxScRun), `drive2`/`drive2Sound` (AxScRun2),
`grfAtBSpec`/`gmoLtBSpec` (AxGraphDec).
Names: Lean-only, in the namespace `Weak.AxSpinT2e1` (file-qualified).
-/
import Weak.AxSpinT2c2
import Weak.AxSpinT2c5
import Weak.AxSpinT2d

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt
open AxSpinT2c1 (img dec rowA hartOkB finish2 finish2Sound emsOf chkOf fullB fullOfB pinsB pinsOfB q0 sZ fullLit pinsLit fuel pureB rows3)

namespace AxSpinT2e1

/-! # 1. The literal -/

/-- Hart B's row in the race schedule (encoded; `AxSpinT2c1.dec`). -/
def encB : List (Nat × Int × Nat × Nat × Nat) := [
  (1, 0x8000c3d8, 8, 0x80001bb6, 0), (1, 0x8000c3d0, 8, 0x8000c400, 0), (1, 0x8000c3c8, 8, 0x80012aa8, 0),
  (1, 0x8000c3b8, 8, 0x80000c68, 0), (1, 0x8000c3b0, 8, 0x8000c3e0, 0), (1, 0x8000c3a8, 8, 0x80012500, 0),
  (1, 0x8000c398, 8, 0x80000c32, 0), (1, 0x8000c390, 8, 0x8000c3c0, 0), (0, 0x8000c398, 8, 0x80000c32, 43),
  (0, 0x8000c390, 8, 0x8000c3c0, 44), (0, 0x80012628, 4, 0x0, 0), (1, 0x8000c398, 8, 0x80000c4e, 0),
  (1, 0x8000c390, 8, 0x8000c3c0, 0), (0, 0x8000c398, 8, 0x80000c4e, 45), (0, 0x8000c390, 8, 0x8000c3c0, 46),
  (1, 0x8001262c, 4, 0x0, 0), (1, 0x8000c398, 8, 0x80000c3a, 0), (1, 0x8000c390, 8, 0x8000c3c0, 0),
  (0, 0x8000c398, 8, 0x80000c3a, 48), (0, 0x8000c390, 8, 0x8000c3c0, 49), (0, 0x80012628, 4, 0x0, 0),
  (1, 0x80012628, 4, 0x1, 0), (0, 0x8000c3b8, 8, 0x80000c68, 40), (0, 0x8000c3b0, 8, 0x8000c3e0, 41),
  (0, 0x8000c3a8, 8, 0x80012500, 42), (0, 0x80012500, 4, 0x0, 30), (3, 0x80012500, 4, 0x0, 30),
  (1, 0x8000c3b8, 8, 0x80000c80, 0), (1, 0x8000c3b0, 8, 0x8000c3e0, 0), (0, 0x8000c3b8, 8, 0x80000c80, 53),
  (0, 0x8000c3b0, 8, 0x8000c3e0, 54), (1, 0x80012510, 8, 0x800125b0, 0), (0, 0x8000c3d8, 8, 0x80001bb6, 37),
  (0, 0x8000c3d0, 8, 0x8000c400, 38), (0, 0x8000c3c8, 8, 0x80012aa8, 39), (0, 0x8000a384, 4, 0x3, 52),
  (0, 0x80012960, 4, 0x1, 20), (0, 0x80012ad8, 4, 0x0, 0), (0, 0x80012c50, 4, 0x0, 0),
  (0, 0x80012dc8, 4, 0x0, 0), (0, 0x80012f40, 4, 0x0, 0), (0, 0x800130b8, 4, 0x0, 0),
  (0, 0x80013230, 4, 0x0, 0), (0, 0x800133a8, 4, 0x0, 0), (0, 0x80013520, 4, 0x0, 0),
  (0, 0x80013698, 4, 0x0, 0), (0, 0x80013810, 4, 0x0, 0), (0, 0x80013988, 4, 0x0, 0),
  (0, 0x80013b00, 4, 0x0, 0), (0, 0x80013c78, 4, 0x0, 0), (0, 0x80013df0, 4, 0x0, 0),
  (0, 0x80013f68, 4, 0x0, 0), (0, 0x800140e0, 4, 0x0, 0), (0, 0x80014258, 4, 0x0, 0),
  (0, 0x800143d0, 4, 0x0, 0), (0, 0x80014548, 4, 0x0, 0), (0, 0x800146c0, 4, 0x0, 0),
  (0, 0x80014838, 4, 0x0, 0), (0, 0x800149b0, 4, 0x0, 0), (0, 0x80014b28, 4, 0x0, 0),
  (0, 0x80014ca0, 4, 0x0, 0), (0, 0x80014e18, 4, 0x0, 0), (0, 0x80014f90, 4, 0x0, 0),
  (0, 0x80015108, 4, 0x0, 0), (0, 0x80015280, 4, 0x0, 0), (0, 0x800153f8, 4, 0x0, 0),
  (0, 0x80015570, 4, 0x0, 0), (0, 0x800156e8, 4, 0x0, 0), (0, 0x80015860, 4, 0x0, 0),
  (0, 0x800159d8, 4, 0x0, 0), (0, 0x80015b50, 4, 0x0, 0), (0, 0x80015cc8, 4, 0x0, 0),
  (0, 0x80015e40, 4, 0x0, 0), (0, 0x80015fb8, 4, 0x0, 0), (0, 0x80016130, 4, 0x0, 0),
  (0, 0x800162a8, 4, 0x0, 0), (0, 0x80016420, 4, 0x0, 0), (0, 0x80016598, 4, 0x0, 0),
  (0, 0x80016710, 4, 0x0, 0), (0, 0x80016888, 4, 0x0, 0), (0, 0x80016a00, 4, 0x0, 0),
  (0, 0x80016b78, 4, 0x0, 0), (0, 0x80016cf0, 4, 0x0, 0), (0, 0x80016e68, 4, 0x0, 0),
  (0, 0x80016fe0, 4, 0x0, 0), (0, 0x80017158, 4, 0x0, 0), (0, 0x800172d0, 4, 0x0, 0),
  (0, 0x80017448, 4, 0x0, 0), (0, 0x800175c0, 4, 0x0, 0), (0, 0x80017738, 4, 0x0, 0),
  (0, 0x800178b0, 4, 0x0, 0), (0, 0x80017a28, 4, 0x0, 0), (0, 0x80017ba0, 4, 0x0, 0),
  (0, 0x80017d18, 4, 0x0, 0), (0, 0x80017e90, 4, 0x0, 0), (0, 0x80018008, 4, 0x0, 0),
  (0, 0x80018180, 4, 0x0, 0), (0, 0x800182f8, 4, 0x0, 0), (0, 0x80018470, 4, 0x0, 0),
  (0, 0x800185e8, 4, 0x0, 0), (1, 0x8000a384, 4, 0x4, 0), (1, 0x80012ad8, 4, 0x3, 0),
  (1, 0x8000c3d8, 8, 0x80001c0a, 0), (1, 0x8000c3d0, 8, 0x8000c400, 0), (1, 0x8000c3c8, 8, 0x80012aa8, 0),
  (0, 0x80012500, 4, 0x1, 51), (1, 0x8000c3b8, 8, 0x80000cf0, 0), (1, 0x8000c3b0, 8, 0x8000c3e0, 0),
  (1, 0x8000c3a8, 8, 0x80012500, 0), (0, 0x80012510, 8, 0x800125b0, 55), (1, 0x8000c398, 8, 0x80000c0c, 0),
  (1, 0x8000c390, 8, 0x8000c3c0, 0), (0, 0x8000c398, 8, 0x80000c0c, 64), (0, 0x8000c390, 8, 0x8000c3c0, 65),
  (0, 0x8000c3b8, 8, 0x80000cf0, 61), (0, 0x8000c3b0, 8, 0x8000c3e0, 62), (0, 0x8000c3a8, 8, 0x80012500, 63),
  (1, 0x80012510, 8, 0x0, 0), (4, 0, 0, 0x0, 0), (2, 0x80012500, 4, 0x0, 0),
  (1, 0x8000c3b8, 8, 0x80000d02, 0), (1, 0x8000c3b0, 8, 0x8000c3e0, 0), (1, 0x8000c3a8, 8, 0x80000ca4, 0),
  (1, 0x8000c3a0, 8, 0x8000c3c0, 0), (0, 0x8000c3a8, 8, 0x80000ca4, 70), (0, 0x8000c3a0, 8, 0x8000c3c0, 71),
  (0, 0x80012628, 4, 0x1, 50), (1, 0x80012628, 4, 0x0, 0), (0, 0x8001262c, 4, 0x0, 47),
  (0, 0x8000c3b8, 8, 0x80000d02, 68), (0, 0x8000c3b0, 8, 0x8000c3e0, 69), (0, 0x8000c3d8, 8, 0x80001c0a, 58),
  (0, 0x8000c3d0, 8, 0x8000c400, 59), (0, 0x8000c3c8, 8, 0x80012aa8, 60), (1, 0x80012ac0, 4, 0x1, 0)]

def rowB : List Lbl := encB.map dec

/-- C's nextpid read: every byte from write 19 (A's nextpid store). -/
def tsC : List Nat := [19, 19, 19, 19]
/-- The value C reads (A's nextpid store). -/
def wC : BitVec 32 := 2#32
/-- C's row: the racer's. -/
def rowC : List Lbl := AxSpinT2d.rcRow tsC wC

/-- THE ROWS (harts 0, 1, 2 = A, B, C). -/
def rows : List (List Lbl) := [rowA, rowB, rowC]

/-- THE INTERLEAVING: A's memory events, B's first 27 (through its claim), C's two, B's rest. -/
def il : List Geid :=
  ((List.range 135).filter (fun k => k != 118)).map (fun k => (0, k)) ++
  (List.range 27).map (fun k => (1, k)) ++ [(2, 0), (2, 1)] ++
  ((List.range' 27 108).filter (fun k => k != 118)).map (fun k => (1, k))

/-- Hart `h`'s literal row. -/
def rowL (h : Nat) : List Lbl := (rows[h]?).getD []

theorem sizes : rowB.length = 135 ∧ rowC.length = 2 ∧ il.length = 270 := by decide +kernel

/-! # 2. The graph -/

/-- THE RACE GRAPH, for any emission. -/
def gT (E : List (List Eitem)) : GdexecT := graphOfSc img rows il E

/-- The literal carries the SC values and timestamps: the graph's rows ARE the literal. -/
theorem rowsFixed : scProg rows (sim img rows il).sOut = rows := by decide +kernel

/-- The untagged graph. -/
def gR0 : Gexec := ⟨fun a => some (img a), rows, il⟩

theorem gtGEq (E : List (List Eitem)) : (gT E).gtG = gR0 := by
  show (⟨fun a => some (img a), scProg rows (sim img rows il).sOut, il⟩ : Gexec) = gR0
  rw [rowsFixed]; rfl

theorem growR (E : List (List Eitem)) (h : Nat) : AxOpsem.grow (gtAdGd (gT E)) h = rowL h := by
  show ((scProg rows (sim img rows il).sOut)[h]?).getD [] = _
  rw [rowsFixed]; rfl

theorem shil : (shapesOkB rows && ilOkB rows il) = true := by decide +kernel

/-- A hart's share of `emsOkB` / `ctrlOkB` reads only its own row. -/
theorem hartOkRow (r r' : List (List Lbl)) (i : Nat) (es : List Eitem)
    (h : r[i]? = r'[i]?) : hartOkB r i es = hartOkB r' i es := by
  have hl : ∀ k, lblAt r (i, k) = lblAt r' (i, k) := fun k => by
    show (r[i]?).bind _ = (r'[i]?).bind _
    rw [h]
  have hi : ∀ (P : Lbl → Bool) k, isAt r P i k = isAt r' P i k := fun P k => by
    unfold isAt; rw [hl]
  have hn : rowLen r i = rowLen r' i := by unfold rowLen; rw [h]
  have hit : itemOkB r i = itemOkB r' i := by
    funext it; unfold itemOkB; simp only [hi]
  simp only [hartOkB, AxScRun.coverB, hit, hi, hn]

/-- C's emission (by hand): the load, `addiw a5` (data source: the load result), the store of
`a5` (value source `a5`). -/
def emsC : List Eitem :=
  [(.LLoad false false (paZ AxSpinT2d.nppaX) [] [], some 0),
   (.LRegW 15 [.DLdRes], none),
   (.LStore false (paZ AxSpinT2d.nppaX) [] [] [.DReg 15], some 1)]

theorem okC : hartOkB rows 2 emsC = true := by decide +kernel

theorem emsCtrlOf (a b : List Eitem) (ha : hartOkB rows 0 a = true)
    (hb : hartOkB rows 1 b = true) :
    emsOkB rows [a, b, emsC] = true ∧ ctrlOkB rows [a, b, emsC] = true := by
  have hc := okC
  simp only [hartOkB, Bool.and_eq_true] at ha hb hc
  simp only [emsOkB, ctrlOkB, List.mapIdx_cons, List.mapIdx_nil, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  exact ⟨⟨ha.1, hb.1, hc.1⟩, ⟨ha.2, hb.2, hc.2⟩⟩

/-- Consistency of the race graph, by the GENERIC SC lemma. -/
theorem catR (a b : List Eitem) (ha : hartOkB rows 0 a = true) (hb : hartOkB rows 1 b = true) :
    rvwmoCatConsistentT (gT [a, b, emsC]) := by
  refine graphOfScCatT _ _ _ _ ?_
  unfold scInputsOkB
  rw [shil, (emsCtrlOf a b ha hb).1]

/-- Ctrl closure of the race graph, by the generic lemma. -/
theorem ctrlR (a b : List Eitem) (ha : hartOkB rows 0 a = true) (hb : hartOkB rows 1 b = true) :
    ctrlClosed (gT [a, b, emsC]) :=
  graphOfScCtrlClosed _ _ _ _ (emsCtrlOf a b ha hb).2

/-- (Generic) an unfolded successful drive + `finish2` on hart `h`'s row gives the RUN premise
at every `gT E`. -/
theorem runOfDrive (h : Nat) (rs0 : RegFile) (m1 : SailM Unit) (rs1 : RegFile) (ib1 : Ibch)
    (k1 : Nat) (es : List Eitem) (u : Unit) (rs2 : RegFile) (ib2 : Ibch) (k2 : Nat)
    (Hd1 : drive2 (fun a => some (img a)) (rowL h) (rowL h).length fuel (.pure ()) rs0 ibNone 0 =
      some (m1, rs1, ib1, k1, es))
    (Hf : finish2 (fun a => some (img a)) (rowL h) 1000 m1 rs1 ib1 k1 =
      some (.pure u, rs2, ib2, k2))
    (Hk2 : k2 = (rowL h).length) (E : List (List Eitem)) :
    ∃ n, ∀ (cpu : CPU) (N : Type) (nm : N),
      nsteps (tierAAstep (gtAdGd (gT E)) nm h) n (AxEpiRun.st cpu (.pure ()) rs0 ibNone 0)
        (AxEpiRun.st cpu (.pure u) rs2 ib2 (AxOpsem.grow (gtAdGd (gT E)) h).length) := by
  have Hd' : drive2 (gtAdGd (gT E)).gdG.gxImg (AxOpsem.grow (gtAdGd (gT E)) h)
      (rowL h).length fuel (.pure ()) rs0 ibNone 0 = some (m1, rs1, ib1, k1, es) := by
    rw [growR]; exact Hd1
  have Hf' : finish2 (gtAdGd (gT E)).gdG.gxImg (AxOpsem.grow (gtAdGd (gT E)) h) 1000
      m1 rs1 ib1 k1 = some (.pure u, rs2, ib2, k2) := by
    rw [growR]; exact Hf
  obtain ⟨-, n1, Hr1⟩ := drive2Sound _ h _ fuel _ _ _ _ _ _ _ _ _ Hd'
  obtain ⟨-, n2, Hr2⟩ := finish2Sound _ h 1000 _ _ _ _ _ _ _ _ Hf'
  refine ⟨n1 + n2, fun cpu N nm => ?_⟩
  rw [growR, ← Hk2]
  exact nsteps_trans (Hr1 cpu) (Hr2 cpu)

/-- The run statement of a hart (to an instruction boundary at the row end). -/
def RunOk (h : Nat) (rs0 : RegFile) (es : List Eitem) : Prop :=
  ∃ (u : Unit) (rs : RegFile) (ib : Ibch), hartOkB rows h es = true ∧
    ∀ E, ∃ n, ∀ (cpu : CPU) (N : Type) (nm : N),
      nsteps (tierAAstep (gtAdGd (gT E)) nm h) n (AxEpiRun.st cpu (.pure ()) rs0 ibNone 0)
        (AxEpiRun.st cpu (.pure u) rs ib (AxOpsem.grow (gtAdGd (gT E)) h).length)

theorem rowL0 : rowL 0 = AxSpinT2c1.rowL 0 := rfl

/-- **A's run**, read back from (a′)'s evaluated drive check `AxSpinT2c2.chkA` (A's row is the
same; nothing is re-driven). -/
theorem runAR : RunOk 0 (regsE 0) AxSpinT2c2.emsA := by
  have Hc := AxSpinT2c2.chkA
  have Hd : AxSpinT2c1.drvOf 0 = AxSpinT2c2.drvA := rfl
  revert Hc Hd
  unfold AxSpinT2c2.emsA
  generalize AxSpinT2c2.drvA = o
  intro Hc Hd
  unfold AxSpinT2c1.drvOf at Hd
  cases Hd1 : drive2 (fun a => some (img a)) (AxSpinT2c1.rowL 0) (AxSpinT2c1.rowL 0).length fuel
      (.pure ()) (regsE 0) ibNone 0 with
  | none => simp only [Hd1] at Hd; subst Hd; cases Hc
  | some r =>
    obtain ⟨m1, rs1, ib1, k1, es⟩ := r
    simp only [Hd1] at Hd
    cases Hf : finish2 (fun a => some (img a)) (AxSpinT2c1.rowL 0) 1000 m1 rs1 ib1 k1 with
    | none => simp only [Hf, Option.map_none] at Hd; subst Hd; cases Hc
    | some r2 =>
      obtain ⟨m2, rs2, ib2, k2⟩ := r2
      simp only [Hf, Option.map_some] at Hd
      subst Hd
      simp only [chkOf, Bool.and_eq_true, decide_eq_true_eq] at Hc
      obtain ⟨Hok, Hpure, Hk2, -⟩ := Hc
      cases m2 with
      | impure c kk => cases Hpure
      | pure u =>
        refine ⟨u, rs2, ib2, ?_, fun E => ?_⟩
        · rw [hartOkRow rows rows3 0 _ rfl]; exact Hok
        · rw [← rowL0] at Hd1 Hf Hk2
          exact runOfDrive 0 (regsE 0) m1 rs1 ib1 k1 es u rs2 ib2 k2 Hd1 Hf Hk2 E

/-- B's drive on its race row, from the warm entry state. -/
noncomputable def drvOfB : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) :=
  match drive2 (fun a => some (img a)) (rowL 1) (rowL 1).length fuel (.pure ()) (regsE 1)
      ibNone 0 with
  | some (m, rs, ib, k, es) =>
    (finish2 (fun a => some (img a)) (rowL 1) 1000 m rs ib k).map fun r =>
      (r.1, r.2.1, r.2.2.1, r.2.2.2, es)
  | none => none

/-- B's check on a drive result: `hartOkB`, row end, instruction boundary. -/
def chkOfB (o : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem)) : Bool :=
  match o with
  | some r => hartOkB rows 1 r.2.2.2.2 && (pureB r.1 && decide (r.2.2.2.1 = (rowL 1).length))
  | none => false

/-- **READ-BACK of B's drive check** (for a VARIABLE drive result). -/
theorem runOfChkB (o : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem))
    (Hd : drvOfB = o) (Hc : chkOfB o = true) : RunOk 1 (regsE 1) (emsOf o) := by
  unfold drvOfB at Hd
  cases Hd1 : drive2 (fun a => some (img a)) (rowL 1) (rowL 1).length fuel (.pure ()) (regsE 1)
      ibNone 0 with
  | none => simp only [Hd1] at Hd; subst Hd; cases Hc
  | some r =>
    obtain ⟨m1, rs1, ib1, k1, es⟩ := r
    simp only [Hd1] at Hd
    cases Hf : finish2 (fun a => some (img a)) (rowL 1) 1000 m1 rs1 ib1 k1 with
    | none => simp only [Hf, Option.map_none] at Hd; subst Hd; cases Hc
    | some r2 =>
      obtain ⟨m2, rs2, ib2, k2⟩ := r2
      simp only [Hf, Option.map_some] at Hd
      subst Hd
      simp only [chkOfB, Bool.and_eq_true, decide_eq_true_eq] at Hc
      obtain ⟨Hok, Hpure, Hk2⟩ := Hc
      cases m2 with
      | impure c kk => cases Hpure
      | pure u =>
        exact ⟨u, rs2, ib2, Hok, runOfDrive 1 (regsE 1) m1 rs1 ib1 k1 es u rs2 ib2 k2 Hd1 Hf Hk2⟩

/-! # 3. Row premises of A and B -/

theorem fullLitB : fullB rowB q0 1 (sZ 1) (AxSpinT2a.pEx 1) = true := by decide +kernel

theorem pinsLitB : pinsB rowB q0 1 = true := by decide +kernel

/-- **`allocFull`** for A (from (a′)'s literal check: same row). -/
theorem fullA (E : List (List Eitem)) :
    allocFull (AxOpsem.grow (gtAdGd (gT E)) 0) q0 0 (sZ 0) (AxSpinT2a.pEx 0) := by
  rw [growR, rowL0]
  exact fullOfB _ _ _ _ _ (List.all_eq_true.1 fullLit 0 (List.mem_range.2 (by decide)))

/-- **`allocFull`** for B on its race row. -/
theorem fullBG (E : List (List Eitem)) :
    allocFull (AxOpsem.grow (gtAdGd (gT E)) 1) q0 1 (sZ 1) (AxSpinT2a.pEx 1) := by
  rw [growR]
  exact fullOfB _ _ _ _ _ fullLitB

/-- **`AllocPins`** for A. -/
theorem pinsA (E : List (List Eitem)) : AllocPins (gtAdGd (gT E)) 0 q0 := by
  apply pinsOfB
  rw [growR, rowL0]
  exact List.all_eq_true.1 pinsLit 0 (List.mem_range.2 (by decide))

/-- **`AllocPins`** for B on its race row (nextpid value 3: `≠ 1000`, no wrap, no collision). -/
theorem pinsBG (E : List (List Eitem)) : AllocPins (gtAdGd (gT E)) 1 q0 := by
  apply pinsOfB
  rw [growR]
  exact pinsLitB

/-- No read of a row touches `σX`'s domain. -/
theorem readsOff : (List.range 3).all (fun h => AxSpinT2c5.readsOffB (rowL h)) = true := by
  decide +kernel

/-! # 4. The race -/

/-- Only harts 0, 1, 2 emit memory events. -/
theorem hartsIn (E : List (List Eitem)) : ∀ e, e ∈ (gT E).gtG.gxGmo → e.1 ∈ [0, 1, 2] := by
  intro e he
  have H : il.all (fun e : Geid => decide (e.1 ∈ [0, 1, 2])) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 H e he)

/-- `HrowC`: C's row is the racer's. -/
theorem rowCEq (E : List (List Eitem)) :
    AxOpsem.grow (gtAdGd (gT E)) 2 = AxSpinT2d.rcRow tsC wC := by
  rw [growR]; rfl

theorem rfLit : grfAtB gR0 (paZ AxSpinT2d.nppaX) (2, 1) (1, t2KBd q0) = true := by decide +kernel

theorem ltLit : gmoLtB gR0 (1, t2KA q0) (2, 1) = true := by decide +kernel

/-- `HrfB`: B's nextpid read sources C's store. -/
theorem rfRace (E : List (List Eitem)) :
    grfAt (gtAdGd (gT E)).gdG (paZ AxSpinT2d.nppaX) (2, 1) (1, t2KBd q0) := by
  show grfAt (gT E).gtG _ _ _
  rw [gtGEq]
  exact (grfAtBSpec _ _ _ _).1 rfLit

/-- `HltB`: C's store is gmo-after B's claim. -/
theorem ltRace (E : List (List Eitem)) : gmoLt (gtAdGd (gT E)).gdG (1, t2KA q0) (2, 1) := by
  show gmoLt (gT E).gtG _ _
  rw [gtGEq]
  exact (gmoLtBSpec _ _ _).1 ltLit

end AxSpinT2e1

end Weak
