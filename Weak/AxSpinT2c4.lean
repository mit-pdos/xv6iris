/-
Weak: **THEOREM 2 / certificate (a′): THE DRIVE OF HART C** (hart 2, slot proc[2], pid 3) —
ONE `decide +kernel` running `drive2` (the proved-sound driver, AxScRun2: it re-runs the REAL
`riscvStep` against the graph's row) on hart C's literal row of `AxSpinT2c1.rows3` from the warm
entry state `(.pure (), AxSpinT2pt.regsE 2)`, checking on its emission (≈ 31 000 items) the
per-hart share of `emsOkB` and `ctrlOkB` (`AxSpinT2c1.hartOkB`), that the run (finished to
the end of the terminal store's instruction, `AxSpinT2c1.finish2`) ends at the row end at an
instruction boundary, and `a3 = 3` at the row end.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §C.6 (in ../xv6iris-lbthm2);
one of the three per-hart modules `AxSpinT2c2/3/4` (they import only `AxSpinT2c1`, so they build
in parallel).

## What this file proves

`chkC`: `AxSpinT2c1.chkOf 2 drvC = true` (THE evaluation, ≈ 2 min).  `emsC` = the recorded
emission.  `runC` — read back by `AxSpinT2c1.runOfChk` (stated for a VARIABLE drive result:
nothing downstream re-evaluates the drive): ∃ final `rs ib` (program `.pure`, so
`AxSpinT2c1.finNotMid`), `(rs .x13).toNat = 3`,
`hartOkB rows3 2 emsC = true`, and for EVERY emission `E` the `tierAAstep` RUN premise of hart 2
at `gtAdGd (gT3 E)` from `AxEpiRun.st cpu (.pure ()) (regsE 2) ibNone 0` to the row end.
Downstream: `AxSpinT2c1.cat3` / `ctrl3` at `E = [emsA, emsB, emsC]`.

## Pins / honesty
* Every proof that mentions `drvC` / `emsC` goes through `runC` (a `match` / `cases` on
  `drvC` would make the kernel re-run the drive).

Reused: `drive2` (AxScRun2), `AxSpinT2c1.drvOf`/`chkOf`/`emsOf`/`runOfChk`.
Names: Lean-only, in the namespace `Weak.AxSpinT2c4` (file-qualified).
-/
import Weak.AxSpinT2c1

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2c1

namespace AxSpinT2c4

/-- Hart C's drive. -/
noncomputable def drvC : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) := drvOf 2

/-- **THE DRIVE CHECK** (one kernel evaluation of `drive2`). -/
theorem chkC : chkOf 2 drvC = true := by decide +kernel

/-- Hart C's emission. -/
noncomputable def emsC : List Eitem := emsOf drvC

/-- Hart C's run premise (to an instruction boundary), emission check and final `a3`
(no re-evaluation). -/
theorem runC : ∃ (u : Unit) (rs : RegFile) (ib : Ibch), (rs .x13).toNat = 2 + 1 ∧
    hartOkB rows3 2 emsC = true ∧
    ∀ E, ∃ n, ∀ (cpu : CPU) (N : Type) (nm : N),
      nsteps (tierAAstep (gtAdGd (gT3 E)) nm 2) n
        (AxEpiRun.st cpu (.pure ()) (regsE 2) ibNone 0)
        (AxEpiRun.st cpu (.pure u) rs ib (AxOpsem.grow (gtAdGd (gT3 E)) 2).length) :=
  runOfChk 2 drvC rfl chkC

end AxSpinT2c4

end Weak
