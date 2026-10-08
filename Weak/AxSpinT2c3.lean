/-
Weak: **THEOREM 2 / certificate (a′): THE DRIVE OF HART B** (hart 1, slot proc[1], pid 2) —
ONE `decide +kernel` running `drive2` (the proved-sound driver, AxScRun2: it re-runs the REAL
`riscvStep` against the graph's row) on hart B's literal row of `AxSpinT2c1.rows3` from the warm
entry state `(.pure (), AxSpinT2pt.regsE 1)`, checking on its emission (≈ 31 000 items) the
per-hart share of `emsOkB` and `ctrlOkB` (`AxSpinT2c1.hartOkB`), that the run (finished to
the end of the terminal store's instruction, `AxSpinT2c1.finish2`) ends at the row end at an
instruction boundary, and `a3 = 2` at the row end.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §C.6 (in ../xv6iris-lbthm2);
one of the three per-hart modules `AxSpinT2c2/3/4` (they import only `AxSpinT2c1`, so they build
in parallel).

## What this file proves

`chkB`: `AxSpinT2c1.chkOf 1 drvB = true` (THE evaluation, ≈ 2 min).  `emsB` = the recorded
emission.  `runB` — read back by `AxSpinT2c1.runOfChk` (stated for a VARIABLE drive result:
nothing downstream re-evaluates the drive): ∃ final `rs ib` (program `.pure`, so
`AxSpinT2c1.finNotMid`), `(rs .x13).toNat = 2`,
`hartOkB rows3 1 emsB = true`, and for EVERY emission `E` the `tierAAstep` RUN premise of hart 1
at `gtAdGd (gT3 E)` from `AxEpiRun.st cpu (.pure ()) (regsE 1) ibNone 0` to the row end.
Downstream: `AxSpinT2c1.cat3` / `ctrl3` at `E = [emsA, emsB, emsC]`.

## Pins / honesty
* Every proof that mentions `drvB` / `emsB` goes through `runB` (a `match` / `cases` on
  `drvB` would make the kernel re-run the drive).

Reused: `drive2` (AxScRun2), `AxSpinT2c1.drvOf`/`chkOf`/`emsOf`/`runOfChk`.
Names: Lean-only, in the namespace `Weak.AxSpinT2c3` (file-qualified).
-/
import Weak.AxSpinT2c1

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2c1

namespace AxSpinT2c3

/-- Hart B's drive. -/
noncomputable def drvB : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) := drvOf 1

/-- **THE DRIVE CHECK** (one kernel evaluation of `drive2`). -/
theorem chkB : chkOf 1 drvB = true := by decide +kernel

/-- Hart B's emission. -/
noncomputable def emsB : List Eitem := emsOf drvB

/-- Hart B's run premise (to an instruction boundary), emission check and final `a3`
(no re-evaluation). -/
theorem runB : ∃ (u : Unit) (rs : RegFile) (ib : Ibch), (rs .x13).toNat = 1 + 1 ∧
    hartOkB rows3 1 emsB = true ∧
    ∀ E, ∃ n, ∀ (cpu : CPU) (N : Type) (nm : N),
      nsteps (tierAAstep (gtAdGd (gT3 E)) nm 1) n
        (AxEpiRun.st cpu (.pure ()) (regsE 1) ibNone 0)
        (AxEpiRun.st cpu (.pure u) rs ib (AxOpsem.grow (gtAdGd (gT3 E)) 1).length) :=
  runOfChk 1 drvB rfl chkB

end AxSpinT2c3

end Weak
