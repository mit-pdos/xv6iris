/-
Weak: **THEOREM 2, STAGE 2 / certificate (a-): THE DRIVE OF HART B** — hart B (1, slot proc[1]) on its PREFIX row `AxSpinT2p1.rowB1` (38 items: through holding's long arm and ONE failed `amoswap.w.aq`): ONE
`decide +kernel` running `drive2` (the proved-sound driver, AxScRun2: it re-runs the REAL
`riscvStep` against the graph's row) from the warm entry state `(.pure (), AxSpinT2pt.regsE 1)`,
checking on its emission the hart's share of `emsOkB` / `ctrlOkB` (`AxSpinT2c1.hartOkB` at
`AxSpinT2p1.rows1`) and that the run (finished by `AxSpinT2c1.finish2`) ends at the row end at
an instruction boundary.

Lean-only (no Rocq source).  Stage-2 design `notes/weak-lb-thm2-stage2.md` §C (certificate (a-),
row `AxSpinT2e1`, here `AxSpinT2p1*`); one of the two per-hart modules `AxSpinT2p1a/b` (each
imports only `AxSpinT2p1`, so they build in parallel).

## What this file proves

`chkB`: `AxSpinT2p1.chkG rows1 1 rowB drvB = true` (THE evaluation).  `emsB` = the recorded
emission.  `runB` — read back by `AxSpinT2p1.runOfChkG` (stated for a VARIABLE drive result):
`AxSpinT2p1.RunOk rows1 il1 1 (regsE 1) emsB` (∃ final `.pure` state at the row end, the hart's
`hartOkB`, and for EVERY emission the `tierAAstep` RUN premise from the entry state).

## Pins / honesty
* Every proof that mentions `drvB` / `emsB` goes through `runB` (a `match` on the drive would
  make the kernel re-run it).

Reused: `drive2` (AxScRun2), `AxSpinT2p1.drvG`/`chkG`/`runOfChkG`, `AxSpinT2c1.emsOf`.
Names: Lean-only, in the namespace `Weak.AxSpinT2p1b` (file-qualified).
-/
import Weak.AxSpinT2p1

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2p1

namespace AxSpinT2p1b

/-- Hart B's drive on its prefix row. -/
noncomputable def drvB : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) :=
  AxSpinT2p1.drvG rowB1 (regsE 1)

/-- **THE DRIVE CHECK** (one kernel evaluation of `drive2`). -/
theorem chkB : AxSpinT2p1.chkG rows1 1 rowB1 drvB = true := by decide +kernel

/-- Hart B's emission. -/
noncomputable def emsB : List Eitem := AxSpinT2c1.emsOf drvB

/-- Hart B's run premise (no re-evaluation). -/
theorem runB : AxSpinT2p1.RunOk rows1 il1 1 (regsE 1) emsB :=
  AxSpinT2p1.runOfChkG rows1 il1 1 rowB1 (regsE 1) drvB growB1 rfl chkB

end AxSpinT2p1b

end Weak
