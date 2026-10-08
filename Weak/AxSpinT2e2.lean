/-
Weak: **THEOREM 2 / certificate (b), NON-VACUITY: THE DRIVE OF HART B ON THE RACE ROW** (hart 1,
slot proc[1]; its nextpid read returns the racer's 3) — ONE `decide +kernel` running `drive2`
(the proved-sound driver, AxScRun2: it re-runs the REAL `riscvStep` against the graph's row) on
`AxSpinT2e1.rowL 1` from the warm entry state `(.pure (), AxSpinT2pt.regsE 1)`, checking on its
emission B's share of `emsOkB` / `ctrlOkB` (`AxSpinT2c1.hartOkB` at `AxSpinT2e1.rows`) and that
the run (finished by `AxSpinT2c1.finish2`) ends at the row end at an instruction boundary.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §C.6 (in ../xv6iris-lbthm2);
the race-schedule twin of `AxSpinT2c3`.  (A's row is (a′)'s, so its drive is NOT repeated: the
capstone reuses `AxSpinT2c2.chkA` through `AxSpinT2e1.runAR`; C is a hand node, run by
`AxSpinT2d.rcRun`.)

## What this file proves

`chkB`: `AxSpinT2e1.chkOfB drvB = true` (THE evaluation).  `emsB` = the recorded emission.
`runB` — read back by `AxSpinT2e1.runOfChkB` (stated for a VARIABLE drive result: nothing
downstream re-evaluates the drive): `AxSpinT2e1.RunOk 1 (regsE 1) emsB`.

## Pins / honesty
* Every proof that mentions `drvB` / `emsB` goes through `runB`.

Reused: `drive2` (AxScRun2), `AxSpinT2e1.drvOfB`/`chkOfB`/`runOfChkB`, `AxSpinT2c1.emsOf`.
Names: Lean-only, in the namespace `Weak.AxSpinT2e2` (file-qualified).
-/
import Weak.AxSpinT2e1

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt

namespace AxSpinT2e2

/-- Hart B's drive on the race row. -/
noncomputable def drvB : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) :=
  AxSpinT2e1.drvOfB

/-- **THE DRIVE CHECK** (one kernel evaluation of `drive2`). -/
theorem chkB : AxSpinT2e1.chkOfB drvB = true := by decide +kernel

/-- Hart B's emission. -/
noncomputable def emsB : List Eitem := AxSpinT2c1.emsOf drvB

/-- Hart B's run premise (no re-evaluation). -/
theorem runB : AxSpinT2e1.RunOk 1 (regsE 1) emsB :=
  AxSpinT2e1.runOfChkB drvB rfl chkB

end AxSpinT2e2

end Weak
