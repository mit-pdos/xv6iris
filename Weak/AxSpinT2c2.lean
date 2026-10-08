/-
Weak: **THEOREM 2 / certificate (a′): THE DRIVE OF HART A** (hart 0, slot proc[0], pid 1) —
ONE `decide +kernel` running `drive2` (the proved-sound driver, AxScRun2: it re-runs the REAL
`riscvStep` against the graph's row) on hart A's literal row of `AxSpinT2c1.rows3` from the warm
entry state `(.pure (), AxSpinT2pt.regsE 0)`, checking on its emission (≈ 31 000 items) the
per-hart share of `emsOkB` and `ctrlOkB` (`AxSpinT2c1.hartOkB`), that the run (finished to
the end of the terminal store's instruction, `AxSpinT2c1.finish2`) ends at the row end at an
instruction boundary, and `a3 = 1` at the row end.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §C.6 (in ../xv6iris-lbthm2);
one of the three per-hart modules `AxSpinT2c2/3/4` (they import only `AxSpinT2c1`, so they build
in parallel).

## What this file proves

`chkA`: `AxSpinT2c1.chkOf 0 drvA = true` (THE evaluation, ≈ 2 min).  `emsA` = the recorded
emission.  `runA` — read back by `AxSpinT2c1.runOfChk` (stated for a VARIABLE drive result:
nothing downstream re-evaluates the drive): ∃ final `rs ib` (program `.pure`, so
`AxSpinT2c1.finNotMid`), `(rs .x13).toNat = 1`,
`hartOkB rows3 0 emsA = true`, and for EVERY emission `E` the `tierAAstep` RUN premise of hart 0
at `gtAdGd (gT3 E)` from `AxEpiRun.st cpu (.pure ()) (regsE 0) ibNone 0` to the row end.
Downstream: `AxSpinT2c1.cat3` / `ctrl3` at `E = [emsA, emsB, emsC]`.

## Pins / honesty
* Every proof that mentions `drvA` / `emsA` goes through `runA` (a `match` / `cases` on
  `drvA` would make the kernel re-run the drive).

Reused: `drive2` (AxScRun2), `AxSpinT2c1.drvOf`/`chkOf`/`emsOf`/`runOfChk`.
Names: Lean-only, in the namespace `Weak.AxSpinT2c2` (file-qualified).
-/
import Weak.AxSpinT2c1

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2c1

namespace AxSpinT2c2

/-- Hart A's drive. -/
noncomputable def drvA : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) := drvOf 0

/-- **THE DRIVE CHECK** (one kernel evaluation of `drive2`). -/
theorem chkA : chkOf 0 drvA = true := by decide +kernel

/-- Hart A's emission. -/
noncomputable def emsA : List Eitem := emsOf drvA

/-- Hart A's run premise (to an instruction boundary), emission check and final `a3`
(no re-evaluation). -/
theorem runA : ∃ (u : Unit) (rs : RegFile) (ib : Ibch), (rs .x13).toNat = 0 + 1 ∧
    hartOkB rows3 0 emsA = true ∧
    ∀ E, ∃ n, ∀ (cpu : CPU) (N : Type) (nm : N),
      nsteps (tierAAstep (gtAdGd (gT3 E)) nm 0) n
        (AxEpiRun.st cpu (.pure ()) (regsE 0) ibNone 0)
        (AxEpiRun.st cpu (.pure u) rs ib (AxOpsem.grow (gtAdGd (gT3 E)) 0).length) :=
  runOfChk 0 drvA rfl chkA

end AxSpinT2c2

end Weak
