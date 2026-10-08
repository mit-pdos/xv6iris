/-
Weak: **THEOREM 2 / certificate (a′), COMPUTATION HALF (rows, graph, row premises)** — the
3-hart SERIAL run A, B, C of xv6's REAL inlined-allocpid segment (allocproc + 0x38 .. the
terminal `sw a5,24(s1)` at + 0x9a) on the slots proc[0], proc[1], proc[2] (nextpid 1 → 2 → 3 → 4;
every scan sees only the earlier pids, so no collision), frozen into LITERAL rows, the
`graphOfSc` graph over them with its generic consistency / ctrl-closure / RUN facts, and the
concrete row-level premises of Theorem 2 (AxSpinT2a's `allocFull`, `AllocPins`, AxSpinRl1's
`rowClsHonest`) discharged on the literal rows by sound Bool checkers.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §C.6, §D row `AxSpinT2c`
(in ../xv6iris-lbthm2); measurements `PROGRESS-AxSpinT2Spike.md` (the spike module itself is deleted: its content
moved here and to AxSpinT2pt; its only unique piece, the 1-hart tie theorem `obs1Lit`, is
recorded there).  The per-hart drives are
`AxSpinT2c2` (A), `AxSpinT2c3` (B), `AxSpinT2c4` (C): each imports only this file and proves
ONE `drive2` check, read back by `AxSpinT2c1.runOfChk` (stated for a VARIABLE drive result).

## What this file proves

§1 THE IMAGE.  `imgByte`/`img`: the real kernel text (`AxScRun3.textByte`), the words of the
table `AxSpinT2pt.tX`, `nextpid = 1`, every other RAM byte 0 (pid_lock free, cpus[] / proc[]
zero).  `mem0`, `st3`, `jres3` = the tracer input / run that GENERATED the literal (provenance
only — see "No tie theorem").
§2 THE LITERAL.  `encA/B/C` (one `(tag, addr, width, value, timestamp)` tuple per row item,
decoded by `dec`), `rows3 = [rowA, rowB, rowC]` (135 items each: 98 loads, 35 stores, the
`amoswap.w.aq` claim, release's `fence rw,w`), `il3` (the serial interleaving: A's 134 memory
events, then B's, then C's).  The literal carries the SC timestamps, so `rowsFixed`: the graph's
rows ARE the literal (`scProg` of the simulation = `rows3`, ONE `decide +kernel`).
§3 THE GRAPH.  `gT3 E = graphOfSc img rows3 il3 E` for ANY emission `E`; `growG3` / `rowOfG3`
(its rows are the literal, independent of `E`), `gvRow` (`graphValue` = the row label's value),
`shil3`, `hartOkB` (one hart's share of `emsOkB` + `ctrlOkB`), `emsCtrlOf` (three per-hart
checks give both), `cat3 : rvwmoCatConsistentT (gT3 [a, b, c])` (GENERIC `graphOfScCatT`),
`ctrl3 : ctrlClosed (gT3 [a, b, c])` (`graphOfScCtrlClosed`); `drvOf h` = `drive2` to the row
end, then `finish2` (the rest of the terminal store's instruction, admin steps only;
`finish2Sound`); `chkOf`/`emsOf`/`runOfChk`: a successful per-hart drive check gives the
`tierAAstep` RUN premise from the entry state `⟨PHart cpu (.pure ()) (regsE h) none ibNone, 0⟩`
to the row end AT AN INSTRUCTION BOUNDARY (`.pure`, so `finNotMid`: AxSpinT2b's `HfinA`/`HfinB`)
at every `gT3 E`, the hart's `hartOkB`, and `a3 = h + 1` at the end — all stated over a
variable drive result.
§4 SOUND CHECKERS (generic, reusable by certificate (b)): `shGo` (→ `RowShX`), `lkB`
(→ `lkBranch`), `spinValsB`, `bodyB`, `spinRmwB` (→ `AxSpinAq1.spinRmw`), `cpuValsB`
(→ `t2CpuVals`), `relValsB` (→ `t2RelVals`), `fullB` → `allocFull` (`fullOfB`); `pinsB` →
`AllocPins` (`pinsOfB`).
§5 THE PREMISES ON (a′).  `q0` (push_off's intena arm, lock free at holding, no failed spin,
pop_off's `noff − 1 = 0` arm), frame bases `sZ h = stack0 + 4096 (h + 1) − 64`, slots
`AxSpinT2a.pEx h = &proc[h]`.  For h ∈ {0, 1, 2} and EVERY emission `E`: `fullG`
(`allocFull`: shape, length, both `lkBranch`es, `spinVals`, the body's reads, `spinRmw` at
`.WCexcl`, `t2CpuVals`, `t2RelVals`), `completeG` (`t2Complete`), `honestG` (`rowClsHonest`,
by `rowClsOkB`), `pinsG` (`AllocPins`: every Option V return / arm pin and the Q18b pins
`≠ 1000`, no wrap, no collision).  `layHyp3`: `T2LayHyp 0 1 2 sZ pEx ptpX` (so `xlayOk` by
`xlayXv6Ok`).
§6 TLB NON-COLLISION (real layout).  `touchPage`: for ANY hart `i < NCPU`, frame base inside
`stack0` and slot in `proc[]` (T2LayHyp's bounds), every page `t2Touch` names lies in
KERNBASE .. `end` — 36 consecutive pages, hence pairwise different slots of the 64-entry
direct-mapped TLB (`AxSpinT2pt.tlbSlotInj`); `hitOfPage` + `touchHit`: a register file whose
TLB is `tlbW` HITS every touched page (`hitW`), in particular `regsE h` (`entryHit`).
DECISION: the non-collision holds for the whole layout family (not only (a′)'s instance).

## Pins / honesty

* The tracer (`AxScRun3.jrun`, untrusted) only GENERATED the literal (Nat-dump recipe,
  `PROGRESS-AxSpinT2Spike.md`); soundness of the RUN premise comes from `drive2` (proved sound,
  AxScRun2), which re-runs the real `riscvStep` on the graph's rows in `AxSpinT2c2/3/4`.
* **No tie theorem** (literal = tracer output; 6–11 min of kernel time): SKIPPED on the owner /
  orchestrator ruling — nothing downstream mentions `jrun`.  It would also have to be modulo
  the write classes: the tracer stamps every store / RMW `WCplain`, while the literal carries
  the classes the language stamps (`wmClassOf`: the claim RMW `WCexcl`, release's `sw zero`
  after `fence rw,w` `WCrel`, all other stores `WCplain`) — checked by `rowClsOkB` (`honestG`).
  `drive2` and `graphOfSc`'s consistency lemmas are class-agnostic.
* The literal carries SC timestamps (computed offline); `rowsFixed` re-derives them.
* Image: only text, the table and `nextpid` are non-zero; the real `.data`/`.bss` of other
  objects is not modelled (nothing in the segment reads them).
* Entry: `ctrlOkSW` of `regsE h` (part of AxSpinT2a's `entryOk`) is not proved here; it is proved in `AxSpinT2c` (`ctrlOkSWE`, `entryOkE`).

Reused: `graphOfSc`/`graphOfScCatT`/`graphOfScCtrlClosed`/`emsOkB`/`ctrlOkB`/`itemOkB`/`monoB`/
`AxScRun.coverB`/`shapesOkB`/`ilOkB`/`scProg`/`sim`/`rowOf` (AxScRun), `drive2`/`drive2Sound`/
`nodeStep2Sound`/`runGraphOfSc` (AxScRun2), `AxScRun3.jrun`/`textByte`, `allocFull`/`allocSeg`/`AllocPins`/`t2Complete`/
`t2CpuVals`/`t2RelVals`/`T2LayHyp`/`t2Touch`/`AxSpinT2a.segParts`/`AxSpinT2a.pEx`/`AxSpinT2a.symV`
(AxSpinT2a), `rowClsOkB`/`rowClsHonestOfB`/`xshape`/`RowShX` (AxSpinRl1), `AxSpinAq1.spinRmw`,
`lkBranch` (AxSpinHd8), `spinVals` (AxSpinAqr), `hitW` (AxSpinE), `WeakKpt.svpnOf`,
`AxSpinT2pt.*`.  Names: Lean-only, in the namespace `Weak.AxSpinT2c1` (file-qualified).
-/
import Weak.AxSpinT2pt
import Weak.AxScRun3
import Weak.AxSpinT2a

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt

namespace AxSpinT2c1

/-! # 1. The image -/

/-- The table word at PA `a`, if `a` is in a table page (read off the tree). -/
def ptWord (a : Nat) : Option (BitVec 64) :=
  if a / 4096 = ptRoot then some (tX.ents (BitVec.ofNat 9 ((a % 4096) / 8)))
  else if a / 4096 = ptL1 then some (tX1.ents (BitVec.ofNat 9 ((a % 4096) / 8)))
  else if a / 4096 = ptL0 then some (tX0.ents (BitVec.ofNat 9 ((a % 4096) / 8)))
  else none

/-- The initial `nextpid`. -/
def n0 : Nat := 1

/-- The image byte at PA `a`: table words, kernel text, `nextpid`, else 0. -/
def imgByte (a : Nat) : Nat :=
  match ptWord a with
  | some w => (w.toNat >>> (8 * (a % 8))) % 256
  | none =>
    if KernelSyms.«_entry» ≤ a ∧ a < KernelSyms.«etext» then AxScRun3.textByte a
    else if KernelSyms.«nextpid» ≤ a ∧ a < KernelSyms.«nextpid» + 4 then
      (n0 >>> (8 * (a - KernelSyms.«nextpid»))) % 256
    else 0

/-- The graph image. -/
def img (a : Int) : BitVec 8 := BitVec.ofNat 8 (imgByte a.toNat)

/-- (Provenance) the tracer's memory: all of RAM. -/
def mem0 : AxSpinSpikeRun.TMem := fun pa =>
  if ramBase ≤ pa.toNat ∧ pa.toNat < ramEnd then some (BitVec.ofNat 8 (imgByte pa.toNat)) else none

/-- (Provenance) the tracer's input: three warm harts, empty rows. -/
def st3 : AxScRun3.Jstate := ([regsE 0, regsE 1, regsE 2], mem0, [[], [], []], [])

/-- (Provenance) THE RUN THAT GENERATED THE LITERAL: 466 instruction steps of A, then of B,
then of C (`#kernel_eval` of a one-`Nat` dump of it, decoded offline; not evaluated here). -/
noncomputable def jres3 : Option AxScRun3.Jstate :=
  AxScRun3.jrun (List.replicate 466 0 ++ List.replicate 466 1 ++ List.replicate 466 2) st3

/-! # 2. The literal -/

/-- `n` little-endian bytes of `v`. -/
def le (n v : Nat) : List (BitVec 8) := (List.range n).map fun j => BitVec.ofNat 8 (v >>> (8 * j))

/-- The decoder: tag 0 = plain load (timestamp `t` on every byte), 1 = plain store, 2 = `WCrel`
store, 3 = the `amoswap.w.aq` RMW (writes 1, class `WCexcl`), else release's `fence rw,w`. -/
def dec (x : Nat × Int × Nat × Nat × Nat) : Lbl :=
  match x with
  | (0, a, n, v, t) => .LLoad false a (List.replicate n t) (le n v)
  | (1, a, n, v, _) => .LStore false a (le n v) .WCplain
  | (2, a, n, v, _) => .LStore false a (le n v) .WCrel
  | (3, a, n, v, t) => .LRmw true false a (List.replicate n t) (le n v) (le n 1) .WCexcl
  | _ => .LFence true true false true

/-- Hart A's row (encoded; `AxSpinT2c1.dec`). -/
def encA : List (Nat × Int × Nat × Nat × Nat) := [
  (1, 0x8000b3d8, 8, 0x80001bb6, 0), (1, 0x8000b3d0, 8, 0x8000b400, 0), (1, 0x8000b3c8, 8, 0x80012930, 0),
  (1, 0x8000b3b8, 8, 0x80000c68, 0), (1, 0x8000b3b0, 8, 0x8000b3e0, 0), (1, 0x8000b3a8, 8, 0x80012500, 0),
  (1, 0x8000b398, 8, 0x80000c32, 0), (1, 0x8000b390, 8, 0x8000b3c0, 0), (0, 0x8000b398, 8, 0x80000c32, 7),
  (0, 0x8000b390, 8, 0x8000b3c0, 8), (0, 0x800125a8, 4, 0x0, 0), (1, 0x8000b398, 8, 0x80000c4e, 0),
  (1, 0x8000b390, 8, 0x8000b3c0, 0), (0, 0x8000b398, 8, 0x80000c4e, 9), (0, 0x8000b390, 8, 0x8000b3c0, 10),
  (1, 0x800125ac, 4, 0x0, 0), (1, 0x8000b398, 8, 0x80000c3a, 0), (1, 0x8000b390, 8, 0x8000b3c0, 0),
  (0, 0x8000b398, 8, 0x80000c3a, 12), (0, 0x8000b390, 8, 0x8000b3c0, 13), (0, 0x800125a8, 4, 0x0, 0),
  (1, 0x800125a8, 4, 0x1, 0), (0, 0x8000b3b8, 8, 0x80000c68, 4), (0, 0x8000b3b0, 8, 0x8000b3e0, 5),
  (0, 0x8000b3a8, 8, 0x80012500, 6), (0, 0x80012500, 4, 0x0, 0), (3, 0x80012500, 4, 0x0, 0),
  (1, 0x8000b3b8, 8, 0x80000c80, 0), (1, 0x8000b3b0, 8, 0x8000b3e0, 0), (0, 0x8000b3b8, 8, 0x80000c80, 16),
  (0, 0x8000b3b0, 8, 0x8000b3e0, 17), (1, 0x80012510, 8, 0x80012530, 0), (0, 0x8000b3d8, 8, 0x80001bb6, 1),
  (0, 0x8000b3d0, 8, 0x8000b400, 2), (0, 0x8000b3c8, 8, 0x80012930, 3), (0, 0x8000a384, 4, 0x1, 0),
  (0, 0x80012960, 4, 0x0, 0), (0, 0x80012ad8, 4, 0x0, 0), (0, 0x80012c50, 4, 0x0, 0),
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
  (0, 0x800185e8, 4, 0x0, 0), (1, 0x8000a384, 4, 0x2, 0), (1, 0x80012960, 4, 0x1, 0),
  (1, 0x8000b3d8, 8, 0x80001c0a, 0), (1, 0x8000b3d0, 8, 0x8000b400, 0), (1, 0x8000b3c8, 8, 0x80012930, 0),
  (0, 0x80012500, 4, 0x1, 15), (1, 0x8000b3b8, 8, 0x80000cf0, 0), (1, 0x8000b3b0, 8, 0x8000b3e0, 0),
  (1, 0x8000b3a8, 8, 0x80012500, 0), (0, 0x80012510, 8, 0x80012530, 18), (1, 0x8000b398, 8, 0x80000c0c, 0),
  (1, 0x8000b390, 8, 0x8000b3c0, 0), (0, 0x8000b398, 8, 0x80000c0c, 27), (0, 0x8000b390, 8, 0x8000b3c0, 28),
  (0, 0x8000b3b8, 8, 0x80000cf0, 24), (0, 0x8000b3b0, 8, 0x8000b3e0, 25), (0, 0x8000b3a8, 8, 0x80012500, 26),
  (1, 0x80012510, 8, 0x0, 0), (4, 0, 0, 0, 0), (2, 0x80012500, 4, 0x0, 0),
  (1, 0x8000b3b8, 8, 0x80000d02, 0), (1, 0x8000b3b0, 8, 0x8000b3e0, 0), (1, 0x8000b3a8, 8, 0x80000ca4, 0),
  (1, 0x8000b3a0, 8, 0x8000b3c0, 0), (0, 0x8000b3a8, 8, 0x80000ca4, 33), (0, 0x8000b3a0, 8, 0x8000b3c0, 34),
  (0, 0x800125a8, 4, 0x1, 14), (1, 0x800125a8, 4, 0x0, 0), (0, 0x800125ac, 4, 0x0, 11),
  (0, 0x8000b3b8, 8, 0x80000d02, 31), (0, 0x8000b3b0, 8, 0x8000b3e0, 32), (0, 0x8000b3d8, 8, 0x80001c0a, 21),
  (0, 0x8000b3d0, 8, 0x8000b400, 22), (0, 0x8000b3c8, 8, 0x80012930, 23), (1, 0x80012948, 4, 0x1, 0)]

/-- Hart B's row (encoded; `AxSpinT2c1.dec`). -/
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
  (1, 0x8000c3b8, 8, 0x80000c80, 0), (1, 0x8000c3b0, 8, 0x8000c3e0, 0), (0, 0x8000c3b8, 8, 0x80000c80, 52),
  (0, 0x8000c3b0, 8, 0x8000c3e0, 53), (1, 0x80012510, 8, 0x800125b0, 0), (0, 0x8000c3d8, 8, 0x80001bb6, 37),
  (0, 0x8000c3d0, 8, 0x8000c400, 38), (0, 0x8000c3c8, 8, 0x80012aa8, 39), (0, 0x8000a384, 4, 0x2, 19),
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
  (0, 0x800185e8, 4, 0x0, 0), (1, 0x8000a384, 4, 0x3, 0), (1, 0x80012ad8, 4, 0x2, 0),
  (1, 0x8000c3d8, 8, 0x80001c0a, 0), (1, 0x8000c3d0, 8, 0x8000c400, 0), (1, 0x8000c3c8, 8, 0x80012aa8, 0),
  (0, 0x80012500, 4, 0x1, 51), (1, 0x8000c3b8, 8, 0x80000cf0, 0), (1, 0x8000c3b0, 8, 0x8000c3e0, 0),
  (1, 0x8000c3a8, 8, 0x80012500, 0), (0, 0x80012510, 8, 0x800125b0, 54), (1, 0x8000c398, 8, 0x80000c0c, 0),
  (1, 0x8000c390, 8, 0x8000c3c0, 0), (0, 0x8000c398, 8, 0x80000c0c, 63), (0, 0x8000c390, 8, 0x8000c3c0, 64),
  (0, 0x8000c3b8, 8, 0x80000cf0, 60), (0, 0x8000c3b0, 8, 0x8000c3e0, 61), (0, 0x8000c3a8, 8, 0x80012500, 62),
  (1, 0x80012510, 8, 0x0, 0), (4, 0, 0, 0, 0), (2, 0x80012500, 4, 0x0, 0),
  (1, 0x8000c3b8, 8, 0x80000d02, 0), (1, 0x8000c3b0, 8, 0x8000c3e0, 0), (1, 0x8000c3a8, 8, 0x80000ca4, 0),
  (1, 0x8000c3a0, 8, 0x8000c3c0, 0), (0, 0x8000c3a8, 8, 0x80000ca4, 69), (0, 0x8000c3a0, 8, 0x8000c3c0, 70),
  (0, 0x80012628, 4, 0x1, 50), (1, 0x80012628, 4, 0x0, 0), (0, 0x8001262c, 4, 0x0, 47),
  (0, 0x8000c3b8, 8, 0x80000d02, 67), (0, 0x8000c3b0, 8, 0x8000c3e0, 68), (0, 0x8000c3d8, 8, 0x80001c0a, 57),
  (0, 0x8000c3d0, 8, 0x8000c400, 58), (0, 0x8000c3c8, 8, 0x80012aa8, 59), (1, 0x80012ac0, 4, 0x1, 0)]

/-- Hart C's row (encoded; `AxSpinT2c1.dec`). -/
def encC : List (Nat × Int × Nat × Nat × Nat) := [
  (1, 0x8000d3d8, 8, 0x80001bb6, 0), (1, 0x8000d3d0, 8, 0x8000d400, 0), (1, 0x8000d3c8, 8, 0x80012c20, 0),
  (1, 0x8000d3b8, 8, 0x80000c68, 0), (1, 0x8000d3b0, 8, 0x8000d3e0, 0), (1, 0x8000d3a8, 8, 0x80012500, 0),
  (1, 0x8000d398, 8, 0x80000c32, 0), (1, 0x8000d390, 8, 0x8000d3c0, 0), (0, 0x8000d398, 8, 0x80000c32, 79),
  (0, 0x8000d390, 8, 0x8000d3c0, 80), (0, 0x800126a8, 4, 0x0, 0), (1, 0x8000d398, 8, 0x80000c4e, 0),
  (1, 0x8000d390, 8, 0x8000d3c0, 0), (0, 0x8000d398, 8, 0x80000c4e, 81), (0, 0x8000d390, 8, 0x8000d3c0, 82),
  (1, 0x800126ac, 4, 0x0, 0), (1, 0x8000d398, 8, 0x80000c3a, 0), (1, 0x8000d390, 8, 0x8000d3c0, 0),
  (0, 0x8000d398, 8, 0x80000c3a, 84), (0, 0x8000d390, 8, 0x8000d3c0, 85), (0, 0x800126a8, 4, 0x0, 0),
  (1, 0x800126a8, 4, 0x1, 0), (0, 0x8000d3b8, 8, 0x80000c68, 76), (0, 0x8000d3b0, 8, 0x8000d3e0, 77),
  (0, 0x8000d3a8, 8, 0x80012500, 78), (0, 0x80012500, 4, 0x0, 66), (3, 0x80012500, 4, 0x0, 66),
  (1, 0x8000d3b8, 8, 0x80000c80, 0), (1, 0x8000d3b0, 8, 0x8000d3e0, 0), (0, 0x8000d3b8, 8, 0x80000c80, 88),
  (0, 0x8000d3b0, 8, 0x8000d3e0, 89), (1, 0x80012510, 8, 0x80012630, 0), (0, 0x8000d3d8, 8, 0x80001bb6, 73),
  (0, 0x8000d3d0, 8, 0x8000d400, 74), (0, 0x8000d3c8, 8, 0x80012c20, 75), (0, 0x8000a384, 4, 0x3, 55),
  (0, 0x80012960, 4, 0x1, 20), (0, 0x80012ad8, 4, 0x2, 56), (0, 0x80012c50, 4, 0x0, 0),
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
  (0, 0x800185e8, 4, 0x0, 0), (1, 0x8000a384, 4, 0x4, 0), (1, 0x80012c50, 4, 0x3, 0),
  (1, 0x8000d3d8, 8, 0x80001c0a, 0), (1, 0x8000d3d0, 8, 0x8000d400, 0), (1, 0x8000d3c8, 8, 0x80012c20, 0),
  (0, 0x80012500, 4, 0x1, 87), (1, 0x8000d3b8, 8, 0x80000cf0, 0), (1, 0x8000d3b0, 8, 0x8000d3e0, 0),
  (1, 0x8000d3a8, 8, 0x80012500, 0), (0, 0x80012510, 8, 0x80012630, 90), (1, 0x8000d398, 8, 0x80000c0c, 0),
  (1, 0x8000d390, 8, 0x8000d3c0, 0), (0, 0x8000d398, 8, 0x80000c0c, 99), (0, 0x8000d390, 8, 0x8000d3c0, 100),
  (0, 0x8000d3b8, 8, 0x80000cf0, 96), (0, 0x8000d3b0, 8, 0x8000d3e0, 97), (0, 0x8000d3a8, 8, 0x80012500, 98),
  (1, 0x80012510, 8, 0x0, 0), (4, 0, 0, 0, 0), (2, 0x80012500, 4, 0x0, 0),
  (1, 0x8000d3b8, 8, 0x80000d02, 0), (1, 0x8000d3b0, 8, 0x8000d3e0, 0), (1, 0x8000d3a8, 8, 0x80000ca4, 0),
  (1, 0x8000d3a0, 8, 0x8000d3c0, 0), (0, 0x8000d3a8, 8, 0x80000ca4, 105), (0, 0x8000d3a0, 8, 0x8000d3c0, 106),
  (0, 0x800126a8, 4, 0x1, 86), (1, 0x800126a8, 4, 0x0, 0), (0, 0x800126ac, 4, 0x0, 83),
  (0, 0x8000d3b8, 8, 0x80000d02, 103), (0, 0x8000d3b0, 8, 0x8000d3e0, 104), (0, 0x8000d3d8, 8, 0x80001c0a, 93),
  (0, 0x8000d3d0, 8, 0x8000d400, 94), (0, 0x8000d3c8, 8, 0x80012c20, 95), (1, 0x80012c38, 4, 0x1, 0)]

def rowA : List Lbl := encA.map dec
def rowB : List Lbl := encB.map dec
def rowC : List Lbl := encC.map dec

/-- THE ROWS (harts 0, 1, 2 = A, B, C). -/
def rows3 : List (List Lbl) := [rowA, rowB, rowC]

/-- THE INTERLEAVING: serial, every memory event of A, then of B, then of C (item 118 is
release's fence, not a memory event). -/
def il3 : List Geid :=
  (List.range 3).flatMap fun h => ((List.range 135).filter fun k => k != 118).map fun k => (h, k)

/-- Hart `h`'s literal row. -/
def rowL (h : Nat) : List Lbl := (rows3[h]?).getD []

theorem sizes3 : rowA.length = 135 ∧ rowB.length = 135 ∧ rowC.length = 135 ∧ il3.length = 402 := by
  decide +kernel

/-! # 3. The graph -/

/-- THE CERTIFICATE GRAPH, for any emission. -/
def gT3 (E : List (List Eitem)) : GdexecT := graphOfSc img rows3 il3 E

/-- The literal carries the SC values and timestamps: the graph's rows ARE the literal. -/
theorem rowsFixed : scProg rows3 (sim img rows3 il3).sOut = rows3 := by decide +kernel

theorem rowOfG3 (E : List (List Eitem)) (h : Nat) :
    rowOf (graphOfSc img rows3 il3 E).gtG h = rowL h := by
  show ((scProg rows3 (sim img rows3 il3).sOut)[h]?).getD [] = _
  rw [rowsFixed]; rfl

theorem growG3 (E : List (List Eitem)) (h : Nat) : AxOpsem.grow (gtAdGd (gT3 E)) h = rowL h :=
  rowOfG3 E h

/-- The value a row label carries. -/
def valAt (row : List Lbl) (k : Nat) : Option (List (BitVec 8)) := (row[k]?).bind lblValue

theorem gvRow (GD : Gdexec) (i k : Nat) : graphValue GD (i, k) = valAt (AxOpsem.grow GD i) k := by
  unfold graphValue gxLbl valAt AxOpsem.grow growG
  rcases GD.gdG.gxProg[i]? with _ | p <;> simp

theorem gdRow (GD : Gdexec) (i k : Nat) :
    graphData GD (i, k) = ((AxOpsem.grow GD i)[k]?).bind lblData := by
  unfold graphData gxLbl AxOpsem.grow growG
  rcases GD.gdG.gxProg[i]? with _ | p <;> simp

theorem shil3 : (shapesOkB rows3 && ilOkB rows3 il3) = true := by decide +kernel

/-- One hart's share of `emsOkB` and `ctrlOkB`. -/
def hartOkB (rows : List (List Lbl)) (i : Nat) (es : List Eitem) : Bool :=
  es.all (itemOkB rows i) && (monoB 0 es && AxScRun.coverB rows i es)

theorem emsCtrlOf (a b c : List Eitem) (ha : hartOkB rows3 0 a = true)
    (hb : hartOkB rows3 1 b = true) (hc : hartOkB rows3 2 c = true) :
    emsOkB rows3 [a, b, c] = true ∧ ctrlOkB rows3 [a, b, c] = true := by
  simp only [hartOkB, Bool.and_eq_true] at ha hb hc
  simp only [emsOkB, ctrlOkB, List.mapIdx_cons, List.mapIdx_nil, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  exact ⟨⟨ha.1, hb.1, hc.1⟩, ⟨ha.2, hb.2, hc.2⟩⟩

/-- Consistency of the certificate graph, by the GENERIC SC lemma (nothing decided on it). -/
theorem cat3 (a b c : List Eitem) (ha : hartOkB rows3 0 a = true)
    (hb : hartOkB rows3 1 b = true) (hc : hartOkB rows3 2 c = true) :
    rvwmoCatConsistentT (gT3 [a, b, c]) := by
  refine graphOfScCatT _ _ _ _ ?_
  unfold scInputsOkB
  rw [shil3, (emsCtrlOf a b c ha hb hc).1]

/-- Ctrl closure of the certificate graph, by the generic lemma. -/
theorem ctrl3 (a b c : List Eitem) (ha : hartOkB rows3 0 a = true)
    (hb : hartOkB rows3 1 b = true) (hc : hartOkB rows3 2 c = true) :
    ctrlClosed (gT3 [a, b, c]) :=
  graphOfScCtrlClosed _ _ _ _ (emsCtrlOf a b c ha hb hc).2

/-- Driver fuel (one hart's drive takes ≈ 31 000 nodes). -/
def fuel : Nat := 1000000

/-- (Generic) after `drive2` reached the row end, finish the current instruction: step the
driver's node while the program is not `.pure` (admin steps only; a memory event past the row
end makes it fail). -/
noncomputable def finish2 (img : Image) (row : List Lbl) :
    Nat → SailM Unit → RegFile → Ibch → Nat → Option (SailM Unit × RegFile × Ibch × Nat)
  | fuel, m, rs, ib, k =>
    match m with
    | .pure _ => some (m, rs, ib, k)
    | m => match fuel with
      | 0 => none
      | f + 1 =>
        match nodeStep2 img row m rs ib k with
        | some (m1, rs1, ib1, k1, _) => finish2 img row f m1 rs1 ib1 k1
        | none => none

/-- `finish2` is sound: it ends at a `.pure` program, by model steps. -/
theorem finish2Sound (GD : Gdexec) (i : Agent) :
    ∀ (fuel : Nat) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) (m' : SailM Unit)
      (rs' : RegFile) (ib' : Ibch) (k' : Nat),
      finish2 GD.gdG.gxImg (AxOpsem.grow GD i) fuel m rs ib k = some (m', rs', ib', k') →
      (∃ u, m' = .pure u) ∧
      ∃ n, ∀ cpu : CPU, nsteps (astepAnyNfGv GD i) n (AxEpiRun.st cpu m rs ib k)
        (AxEpiRun.st cpu m' rs' ib' k') := by
  intro fuel
  induction fuel with
  | zero =>
    intro m rs ib k m' rs' ib' k' Hd
    cases m with
    | pure u =>
      simp only [finish2, Option.some.injEq, Prod.mk.injEq] at Hd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Hd
      exact ⟨⟨u, rfl⟩, 0, fun _ => nsteps_O _⟩
    | impure c kk => simp [finish2] at Hd
  | succ f ih =>
    intro m rs ib k m' rs' ib' k' Hd
    cases m with
    | pure u =>
      simp only [finish2, Option.some.injEq, Prod.mk.injEq] at Hd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Hd
      exact ⟨⟨u, rfl⟩, 0, fun _ => nsteps_O _⟩
    | impure c kk =>
      simp only [finish2] at Hd
      cases Hn : nodeStep2 GD.gdG.gxImg (AxOpsem.grow GD i) (.impure c kk) rs ib k with
      | none => rw [Hn] at Hd; cases Hd
      | some r =>
        obtain ⟨m1, rs1, ib1, k1, it⟩ := r
        rw [Hn] at Hd
        obtain ⟨Hp, n, Hr⟩ := ih m1 rs1 ib1 k1 m' rs' ib' k' Hd
        exact ⟨Hp, n + 1, fun cpu =>
          nsteps_l (nodeStep2Sound GD i cpu _ rs ib k m1 rs1 ib1 k1 it Hn) (Hr cpu)⟩

/-- The drive of hart `h` on its literal row, from the entry state (`.pure ()`, `regsE h`),
then to the end of the terminal store's instruction. -/
noncomputable def drvOf (h : Nat) : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) :=
  match drive2 (fun a => some (img a)) (rowL h) (rowL h).length fuel (.pure ()) (regsE h)
      ibNone 0 with
  | some (m, rs, ib, k, es) =>
    (finish2 (fun a => some (img a)) (rowL h) 1000 m rs ib k).map fun r =>
      (r.1, r.2.1, r.2.2.1, r.2.2.2, es)
  | none => none

/-- (Generic) the emission a drive result recorded. -/
def emsOf (o : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem)) : List Eitem :=
  (o.map fun r => r.2.2.2.2).getD []

/-- (Generic) the final program is `.pure` (an instruction boundary). -/
def pureB (m : SailM Unit) : Bool :=
  match m with
  | .pure _ => true
  | _ => false

/-- (Generic) the per-hart check on a drive result: `hartOkB`, the run ends at the row end at
an instruction boundary, `a3 = h + 1`. -/
def chkOf (h : Nat) (o : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem)) : Bool :=
  match o with
  | some r => hartOkB rows3 h r.2.2.2.2 && (pureB r.1 && (decide (r.2.2.2.1 = (rowL h).length) &&
      decide ((r.2.1 .x13).toNat = h + 1)))
  | none => false

/-- **READ-BACK of a per-hart drive check** (stated for a VARIABLE drive result `o`, so no
proof using it re-evaluates the drive): the run premise from the entry state to the row end,
at an instruction boundary (`.pure`), at EVERY `gT3 E`; the hart's `hartOkB`; the final `a3`. -/
theorem runOfChk (h : Nat) (o : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem))
    (Hd : drvOf h = o) (Hc : chkOf h o = true) :
    ∃ (u : Unit) (rs : RegFile) (ib : Ibch), (rs .x13).toNat = h + 1 ∧
      hartOkB rows3 h (emsOf o) = true ∧
      ∀ E, ∃ n, ∀ (cpu : CPU) (N : Type) (nm : N),
        nsteps (tierAAstep (gtAdGd (gT3 E)) nm h) n
          (AxEpiRun.st cpu (.pure ()) (regsE h) ibNone 0)
          (AxEpiRun.st cpu (.pure u) rs ib (AxOpsem.grow (gtAdGd (gT3 E)) h).length) := by
  unfold drvOf at Hd
  cases Hd1 : drive2 (fun a => some (img a)) (rowL h) (rowL h).length fuel (.pure ()) (regsE h)
      ibNone 0 with
  | none => simp only [Hd1] at Hd; subst Hd; cases Hc
  | some r =>
    obtain ⟨m1, rs1, ib1, k1, es⟩ := r
    simp only [Hd1] at Hd
    cases Hf : finish2 (fun a => some (img a)) (rowL h) 1000 m1 rs1 ib1 k1 with
    | none => simp only [Hf, Option.map_none] at Hd; subst Hd; cases Hc
    | some r2 =>
      obtain ⟨m2, rs2, ib2, k2⟩ := r2
      simp only [Hf, Option.map_some] at Hd
      subst Hd
      simp only [chkOf, Bool.and_eq_true, decide_eq_true_eq] at Hc
      obtain ⟨Hok, Hpure, Hk2, Hx⟩ := Hc
      cases m2 with
      | impure c kk => cases Hpure
      | pure u =>
        refine ⟨u, rs2, ib2, Hx, Hok, fun E => ?_⟩
        have Hd' : drive2 (gtAdGd (gT3 E)).gdG.gxImg (AxOpsem.grow (gtAdGd (gT3 E)) h)
            (rowL h).length fuel (.pure ()) (regsE h) ibNone 0 = some (m1, rs1, ib1, k1, es) := by
          rw [growG3]; exact Hd1
        have Hf' : finish2 (gtAdGd (gT3 E)).gdG.gxImg (AxOpsem.grow (gtAdGd (gT3 E)) h) 1000
            m1 rs1 ib1 k1 = some (.pure u, rs2, ib2, k2) := by
          rw [growG3]; exact Hf
        obtain ⟨-, n1, Hr1⟩ := drive2Sound _ h _ fuel _ _ _ _ _ _ _ _ _ Hd'
        obtain ⟨-, n2, Hr2⟩ := finish2Sound _ h 1000 _ _ _ _ _ _ _ _ Hf'
        refine ⟨n1 + n2, fun cpu N nm => ?_⟩
        rw [growG3, ← Hk2]
        exact nsteps_trans (Hr1 cpu) (Hr2 cpu)

/-- The final state of a `runOfChk` run is not mid-instruction (AxSpinT2b's `HfinA`/`HfinB`). -/
theorem finNotMid (cpu : CPU) (u : Unit) (rs : RegFile) (ib : Ibch) (k : Nat) :
    ¬ midState (AxEpiRun.st cpu (.pure u) rs ib k) := by
  simp [midState, isNext, AxEpiRun.st]

/-! # 4. Sound checkers for the row premises (generic) -/

/-- `xshape` as a Bool. -/
def xshapeB (x : Rxitem) (lb : Lbl) : Bool :=
  match x with
  | .it (.RF n) => match aident lb with
    | .IRead _ _ n' => decide (n' = n)
    | _ => false
  | .it (.RP pa n) => match aident lb with
    | .IRead _ b n' => decide (b = pa) && decide (n' = n)
    | _ => false
  | .it (.RL pa n) => match aident lb with
    | .IRead _ b n' => decide (b = pa) && decide (n' = n)
    | _ => false
  | .it (.RS pa n) => match lb with
    | .LStore false b vw _ => decide (b = pa) && decide (vw.length = n)
    | _ => false
  | .RB pr pw sr sw => decide (aident lb = .IFence pr pw sr sw)
  | .RSc pa n cls => match lb with
    | .LStore false b vw c => decide (b = pa) && decide (vw.length = n) && decide (c = cls)
    | _ => false
  | .RM aq rl pa n => decide (aident lb = .IRmw aq rl pa n)

theorem xshapeOfB (x : Rxitem) (lb : Lbl) : xshapeB x lb = true → xshape x lb := by
  intro h
  cases x with
  | it i =>
    cases i with
    | RF n =>
      show ∃ aq b, aident lb = .IRead aq b n
      revert h; simp only [xshapeB]; generalize aident lb = a
      cases a <;> simp
    | RP pa n =>
      show ∃ aq, aident lb = .IRead aq pa n
      revert h; simp only [xshapeB]; generalize aident lb = a
      cases a <;> simp
    | RL pa n =>
      show ∃ aq, aident lb = .IRead aq pa n
      revert h; simp only [xshapeB]; generalize aident lb = a
      cases a <;> simp
    | RS pa n =>
      show ∃ vw cls, lb = .LStore false pa vw cls ∧ vw.length = n
      cases lb with
      | LStore rl b vw c =>
        cases rl with
        | false =>
          simp only [xshapeB, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨rfl, h2⟩ := h
          exact ⟨vw, c, rfl, h2⟩
        | true => simp [xshapeB] at h
      | _ => simp [xshapeB] at h
  | RB pr pw sr sw =>
    show aident lb = _
    exact of_decide_eq_true h
  | RSc pa n cls =>
    show ∃ vw, lb = .LStore false pa vw cls ∧ vw.length = n
    cases lb with
    | LStore rl b vw c =>
      cases rl with
      | false =>
        simp only [xshapeB, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, h2⟩, rfl⟩ := h
        exact ⟨vw, rfl, h2⟩
      | true => simp [xshapeB] at h
    | _ => simp [xshapeB] at h
  | RM aq rl pa n =>
    show aident lb = _
    exact of_decide_eq_true h

/-- `RowShX 0` as a Bool (item by item). -/
def shGo : List Lbl → List Rxitem → Bool
  | _, [] => true
  | lb :: r, x :: s => xshapeB x lb && shGo r s
  | [], _ :: _ => false

theorem shGoSound : ∀ (row : List Lbl) (sh : List Rxitem), shGo row sh = true → RowShX 0 row sh
  | _, [], _ => fun j x hx => by simp at hx
  | lb :: r, x :: s, h => by
    simp only [shGo, Bool.and_eq_true] at h
    intro j y hy
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      exact ⟨lb, rfl, xshapeOfB _ _ h.1⟩
    | succ j =>
      obtain ⟨lb', h1, h2⟩ := shGoSound r s h.2 j y (by simpa using hy)
      exact ⟨lb', by simpa using h1, h2⟩
  | [], _ :: _, h => by simp [shGo] at h

/-- `Option`-guarded Bool (`true` on `none`). -/
def optAll {α : Type} (o : Option α) (f : α → Bool) : Bool :=
  match o with
  | some v => f v
  | none => true

theorem optAllOf {α : Type} {o : Option α} {f : α → Bool} :
    optAll o f = true → ∀ v, o = some v → f v = true := by
  intro h v hv; subst hv; exact h

/-- `lkBranch` as a Bool. -/
def lkB (row : List Lbl) (k : Nat) (hb : Bool) : Bool :=
  match row[k]? with
  | some lb => match lblValue lb with
    | some vs => decide (hb = (ldRes false 4 vs != 0#64))
    | none => false
  | none => false

theorem lkOfB {row : List Lbl} {k : Nat} {hb : Bool} : lkB row k hb = true → lkBranch row k hb := by
  intro h
  unfold lkB at h
  cases hr : row[k]? with
  | none => simp [hr] at h
  | some lb =>
    cases hv : lblValue lb with
    | none => simp [hr, hv] at h
    | some vs =>
      simp only [hr, hv, decide_eq_true_eq] at h
      exact ⟨lb, vs, hr, hv, h⟩

/-- `spinVals` as a Bool. -/
def spinValsB (row : List Lbl) (u n : Nat) : Bool :=
  (List.range (n + 1)).all fun j =>
    match row[u + j]? with
    | some lb => match lblValue lb with
      | some vs => decide (aqFail vs = decide (j < n))
      | none => false
    | none => false

theorem spinValsOfB {row : List Lbl} {u n : Nat} : spinValsB row u n = true → spinVals row u n := by
  intro h j hj
  have h1 := List.all_eq_true.1 h j (List.mem_range.2 (by omega))
  cases hr : row[u + j]? with
  | none => simp [hr] at h1
  | some lb =>
    cases hv : lblValue lb with
    | none => simp [hr, hv] at h1
    | some vs =>
      simp only [hr, hv, decide_eq_true_eq] at h1
      exact ⟨lb, vs, rfl, hv, h1⟩

/-- The body's read conditions (`RowAllocpidBody`'s 2nd / 3rd conjuncts) as a Bool. -/
def bodyB (row : List Lbl) (k : Nat) (pnp : Int) : Bool :=
  optAll (row[k]?) (fun lb => decide (aident lb = .IRead false pnp 4)) &&
  (List.range 64).all fun j =>
    optAll (row[k + 1 + j]?) (fun lb => decide (aident lb = .IRead false (AxSpinAp7.scanAddr j) 4))

theorem bodyOfB {row : List Lbl} {k : Nat} {pnp : Int} : bodyB row k pnp = true →
    (∀ lb, row[k]? = some lb → aident lb = .IRead false pnp 4) ∧
    (∀ j, j < 64 → ∀ lb, row[k + 1 + j]? = some lb →
      aident lb = .IRead false (AxSpinAp7.scanAddr j) 4) := by
  intro h
  simp only [bodyB, Bool.and_eq_true] at h
  refine ⟨fun lb hl => of_decide_eq_true (optAllOf h.1 lb hl), fun j hj lb hl => ?_⟩
  exact of_decide_eq_true (optAllOf (List.all_eq_true.1 h.2 j (List.mem_range.2 hj)) lb hl)

/-- `AxSpinAq1.spinRmw` as a Bool. -/
def spinRmwB (row : List Lbl) (u n : Nat) (lk : Int) : Bool :=
  (List.range (n + 1)).all fun j =>
    match row[u + j]? with
    | some (.LRmw _ _ _ ts rvs _ _) =>
      decide (row[u + j]? = some (.LRmw true false lk [ts.headD 0, ts.headD 0, ts.headD 0,
        ts.headD 0] rvs AxSpinX4.o4 .WCexcl)) &&
      (decide (rvs = AxSpinX4.z4) || optAll (rvs[0]?) (fun b => !decide (b = b0)) &&
        !rvs.isEmpty)
    | _ => false

theorem spinRmwOfB {row : List Lbl} {u n : Nat} {lk : Int} :
    spinRmwB row u n lk = true → AxSpinAq1.spinRmw row u n lk := by
  intro h j hj
  have h1 := List.all_eq_true.1 h j (List.mem_range.2 (by omega))
  cases hr : row[u + j]? with
  | none => rw [hr] at h1; cases h1
  | some lb =>
    cases lb with
    | LRmw aq rl pa ts rvs wvs cls =>
      rw [hr] at h1
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
      refine ⟨ts.headD 0, rvs, h1.1, ?_⟩
      rcases h1.2 with h2 | ⟨h2, h3⟩
      · exact .inl h2
      · right
        cases hv : rvs[0]? with
        | none =>
          cases rvs with
          | nil => simp at h3
          | cons x l => simp at hv
        | some b =>
          rw [hv] at h2
          exact ⟨b, rfl, by simpa [optAll] using h2⟩
    | _ => rw [hr] at h1; cases h1

/-- `t2CpuVals` as a Bool. -/
def cpuValsB (row : List Lbl) (i : Agent) : Bool :=
  row.all fun lb =>
    match lb with
    | .LStore false a vw _ =>
      !decide (a = AxSpinT2a.zLk + 16) || decide (vw = cvx i) || decide (vw = List.replicate 8 b0)
    | .LStore true a _ _ => !decide (a = AxSpinT2a.zLk + 16)
    | .LRmw _ _ a _ _ _ _ => !decide (a = AxSpinT2a.zLk + 16)
    | _ => true

theorem cpuValsOfB {row : List Lbl} {i : Agent} : cpuValsB row i = true → t2CpuVals row i := by
  intro h k lb rl m hk hw
  have h1 := List.all_eq_true.1 h lb (List.mem_of_getElem? hk)
  cases lb with
  | LLoad aq a ts vs => simp [aident, aidentWr] at hw
  | LFence pr pw sr sw => simp [aident, aidentWr] at hw
  | LStore rl' a vw cls =>
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨-, rfl, -⟩ := hw
    cases rl' with
    | false =>
      simp only [decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq] at h1
      exact ⟨vw, cls, rfl, h1⟩
    | true => simp at h1
  | LRmw aq rl' a ts rvs wvs cls =>
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨-, rfl, -⟩ := hw
    simp at h1

/-- `t2RelVals` as a Bool. -/
def relValsB (row : List Lbl) (q : T2Prm) : Bool :=
  optAll (row[relKw (t2KRl q)]?) fun lb =>
    match lb with
    | .LStore false a vw _ => !decide (a = AxSpinT2a.zLk) || decide (vw = AxSpinX4.z4)
    | _ => true

theorem relValsOfB {row : List Lbl} {q : T2Prm} : relValsB row q = true → t2RelVals row q := by
  intro h vw cls hl
  have h1 := optAllOf h _ hl
  simpa using h1

/-- `allocFull` as a Bool. -/
def fullB (row : List Lbl) (q : T2Prm) (i : Agent) (S p : Int) : Bool :=
  shGo row (allocSeg q i S p) && (decide (row.length = t2Len q) &&
  (lkB row (t2KHd q) q.hb && (spinValsB row (t2KSp q) q.n && (lkB row (t2KRh q) true &&
  (bodyB row (t2KBd q) AxSpinT2a.zNp && (spinRmwB row (t2KSp q) q.n AxSpinT2a.zLk &&
  (cpuValsB row i && relValsB row q)))))))

/-- **Soundness of `fullB`.** -/
theorem fullOfB (row : List Lbl) (q : T2Prm) (i : Agent) (S p : Int) :
    fullB row q i S p = true → allocFull row q i S p := by
  intro h
  simp only [fullB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have H1 : RowShX 0 row (allocSeg q i S p) := shGoSound _ _ h1
  exact ⟨H1, h2, lkOfB h3, spinValsOfB h4, lkOfB h5,
    ⟨(AxSpinT2a.segParts H1).2.2.2.2.2.1, (bodyOfB h6).1, (bodyOfB h6).2⟩,
    spinRmwOfB h7, cpuValsOfB h8, relValsOfB h9⟩

/-- `AllocPins` as a Bool, on the row (`gvRow`, `gdRow`), including AxSpinApA's six extra pins
(`poS1`, `hdS1`, `aqS1`, `rhCpu`, `rhS1`, `rlS1`). -/
def pinsB (row : List Lbl) (q : T2Prm) (i : Agent) : Bool :=
  decide (valAt row (t2KPo + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14))) &&
  (optAll (valAt row (t2KPo + 7)) (fun vn => decide ((ldRes false 4 vn == zero_reg) = q.b)) &&
  ((!q.b || decide (valAt row (t2KPo + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30)))) &&
  (decide (valAt row (t2KPoT q + 2) = some (stBytes 8 (AxSpinPO.ppo 0x1c))) &&
  (decide (valAt row (t2KPoT q + 6) = some (stBytes 8 (AxSpinHdB.pac 0x10))) &&
  ((!q.hb || (decide (valAt row (t2KHd q + 7) = some (stBytes 8 (pch 0x1a))) &&
    decide (valAt row (t2KHd q + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16))))) &&
  ((!q.hb || optAll (valAt row (t2KHd q + 4))
    (fun vcpu => !decide (ldRes false 8 vcpu = cpuAddr (cpuOf i)))) &&
  (decide (valAt row (t2KMy q + 2) = some (stBytes 8 (AxSpinHdB.pac 0x28))) &&
  (decide (valAt row (t2KMy q + 5) = some (stBytes 8 (pca 0x44))) &&
  (optAll (valAt row (t2KBd q)) (fun vs => !decide ((wordOfBytes 4 vs : BitVec 32) = 1000#32) &&
    decide ((wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32)) &&
  (optAll (valAt row (t2KBd q)) (fun vs => (List.range 64).all fun j =>
    optAll (valAt row (t2KBd q + 1 + j))
      (fun v => !decide ((wordOfBytes 4 v : BitVec 32) = wordOfBytes 4 vs))) &&
  ((decide (valAt row (t2KRh q + 7) = some (stBytes 8 (pch 0x1a))) &&
    decide (valAt row (t2KRh q + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10)))) &&
  (optAll (valAt row (t2KRh q + 4)) (fun vcpu => decide (ldRes false 8 vcpu = cpuAddr (cpuOf i))) &&
  (decide (valAt row (t2KPp q + 4) = some (stBytes 8 (ppp 0x0c))) &&
  (optAll (valAt row (t2KPp q + 6)) (fun vn => decide (zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false)) &&
  (optAll (valAt row (t2KPp q + 6)) (fun vn => decide ((addiwm1 (ldRes false 4 vn) != zero_reg) = q.c)) &&
  ((q.c || optAll (valAt row (t2KPp q + 8)) (fun vi => decide ((ldRes false 4 vi == zero_reg) = true))) &&
  (decide (valAt row (t2KPp q + 8 + (if q.c then 0 else 1)) = some (stBytes 8 (AxSpinHdB.prl 0x22))) &&
  (decide (valAt row (t2KRr q) = some (stBytes 8 (pca 0x98))) &&
  (decide (valAt row (t2KPoT q + 8) = some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))) &&
  ((!q.hb || decide (valAt row (t2KHd q + 11) =
    some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»)))) &&
  (decide (valAt row (t2KMy q + 7) = (row[2]?).bind lblData) &&
  (decide (valAt row (t2KRh q + 4) = some (stBytes 8 (cpuAddr (cpuOf i)))) &&
  (decide (valAt row (t2KRh q + 11) = some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))) &&
  decide (valAt row (t2KRr q + 2) = (row[t2KRl q + 2]?).bind lblData))))))))))))))))))))))))

/-- **Soundness of `pinsB`.** -/
theorem pinsOfB (GD : Gdexec) (i : Agent) (q : T2Prm) :
    pinsB (AxOpsem.grow GD i) q i = true → AllocPins GD i q := by
  intro h
  simp only [pinsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ⟨h12a, h12b⟩, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩ := h
  have gv := gvRow GD i
  have gd := gdRow GD i
  refine
    { poMy1 := by rw [gv]; exact h1
      poArm := fun vn hv => of_decide_eq_true (optAllOf h2 vn (by rw [← gv]; exact hv))
      poMy2 := fun hb => by
        rw [hb] at h3; rw [gv]; simpa using h3
      poMy3 := by rw [gv]; exact h4
      poRet := by rw [gv]; exact h5
      hdRets := fun hb => by
        rw [hb] at h6
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h6
        exact ⟨by rw [gv]; exact h6.1, by rw [gv]; exact h6.2⟩
      hdArm := fun hb vcpu hv => by
        rw [hb] at h7
        simp only [Bool.not_true, Bool.false_or] at h7
        have := optAllOf h7 vcpu (by rw [← gv]; exact hv)
        simpa using this
      aqMy := by rw [gv]; exact h8
      aqRet := by rw [gv]; exact h9
      npNowrap := fun vs hv => by
        have := optAllOf h10 vs (by rw [← gv]; exact hv)
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          decide_eq_true_eq] at this
        exact this
      npNcoll := fun vs hv j hj v hv' => by
        have h1' := optAllOf h11 vs (by rw [← gv]; exact hv)
        have h2' := optAllOf (List.all_eq_true.1 h1' j (List.mem_range.2 hj)) v
          (by rw [← gv]; exact hv')
        simpa using h2'
      rhRets := ⟨by rw [gv]; exact h12a, by rw [gv]; exact h12b⟩
      rhArm := fun vcpu hv => of_decide_eq_true (optAllOf h13 vcpu (by rw [← gv]; exact hv))
      ppMy := by rw [gv]; exact h14
      ppGe := fun vn hv => of_decide_eq_true (optAllOf h15 vn (by rw [← gv]; exact hv))
      ppArm := fun vn hv => of_decide_eq_true (optAllOf h16 vn (by rw [← gv]; exact hv))
      ppInt := fun hc vi hv => by
        rw [hc] at h17
        simp only [Bool.false_or] at h17
        exact of_decide_eq_true (optAllOf h17 vi (by rw [← gv]; exact hv))
      ppRet := by rw [gv]; exact h18
      rlRet := by rw [gv]; exact h19
      poS1 := by rw [gv]; exact h20
      hdS1 := fun hb => by
        rw [hb] at h21; rw [gv]; simpa using h21
      aqS1 := by rw [gv, gd]; exact h22
      rhCpu := by rw [gv]; exact h23
      rhS1 := by rw [gv]; exact h24
      rlS1 := by rw [gv, gd]; exact h25 }

/-! # 5. The premises on certificate (a′) -/

/-- The control parameters of every hart of (a′): push_off's `noff == 0` arm, the lock free at
holding, no failed spin, pop_off's `noff − 1 = 0` arm. -/
def q0 : T2Prm := ⟨true, false, 0, false⟩

/-- Hart `j`'s frame base (sp at allocproc + 0x38). -/
def sZ (j : Agent) : Int := (KernelSyms.«stack0» : Int) + 4096 * ((j : Int) + 1) - 64

theorem sZSp (j : Agent) : sZ j = (spOf j : Int) := by
  unfold sZ spOf
  have h : KernelSyms.«stack0» = 0x8000a420 := rfl
  rw [h]; omega

/-- allocproc's frame is 16-aligned (AxSpinApA's `Lay.sAl`). -/
theorem sZAl (j : Agent) : sZ j % 16 = 0 := by
  unfold sZ
  have h : (KernelSyms.«stack0» : Int) = 0x8000a420 := rfl
  rw [h]; omega

theorem procAtZ (j : Agent) : AxSpinT2a.pEx j = (procAt j : Int) := by
  unfold AxSpinT2a.pEx procAt
  have h : KernelSyms.«proc» = 0x80012930 := rfl
  rw [h]; omega

theorem fullLit : (List.range 3).all (fun h =>
    fullB (rowL h) q0 h (sZ h) (AxSpinT2a.pEx h)) = true := by
  decide +kernel

theorem pinsLit : (List.range 3).all (fun h => pinsB (rowL h) q0 h) = true := by
  decide +kernel

theorem clsLit : (List.range 3).all (fun h => rowClsOkB (rowL h)) = true := by
  decide +kernel

section prem
variable (E : List (List Eitem)) (h : Agent) (hh : h < 3)
include hh

/-- **`allocFull`** for hart `h` of (a′), at every emission. -/
theorem fullG : allocFull (AxOpsem.grow (gtAdGd (gT3 E)) h) q0 h (sZ h) (AxSpinT2a.pEx h) := by
  rw [growG3]
  exact fullOfB _ _ _ _ _ (List.all_eq_true.1 fullLit h (List.mem_range.2 hh))

/-- **`t2Complete`** for hart `h` of (a′). -/
theorem completeG : t2Complete (gtAdGd (gT3 E)) h (sZ h) (AxSpinT2a.pEx h) :=
  ⟨q0, fullG E h hh⟩

/-- **`AllocPins`** (Option V + Q18b) for hart `h` of (a′). -/
theorem pinsG : AllocPins (gtAdGd (gT3 E)) h q0 := by
  apply pinsOfB
  rw [growG3]
  exact List.all_eq_true.1 pinsLit h (List.mem_range.2 hh)

/-- **`rowClsHonest`** (ID-6) for hart `h` of (a′). -/
theorem honestG : rowClsHonest (AxOpsem.grow (gtAdGd (gT3 E)) h) := by
  rw [growG3]
  exact rowClsHonestOfB _ (List.all_eq_true.1 clsLit h (List.mem_range.2 hh))

end prem

/-- The page-table pages of `tX` (root, L1, L0). -/
def ptpX (a : Int) : Prop := (ptL0 * 4096 : Int) ≤ a ∧ a < ((ptRoot + 1) * 4096 : Int)

/-- The layout hypotheses of (a′): harts 0 / 1 / 2, slots proc[0..2], frames in stack0. -/
theorem layHyp3 : T2LayHyp 0 1 2 sZ AxSpinT2a.pEx ptpX := by
  obtain ⟨-, -, v3, -, v5, v6, -, -⟩ := AxSpinT2a.symV
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases hj with rfl | rfl | rfl
    · exact ⟨0, by decide, by simp [AxSpinT2a.pEx]⟩
    · exact ⟨1, by decide, by simp [AxSpinT2a.pEx]⟩
    · exact ⟨2, by decide, by simp [AxSpinT2a.pEx]⟩
  · intro j1 j2 h1 h2 hne
    unfold AxSpinT2a.pEx
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | omega
  · intro j hj
    unfold sZ
    rw [v5]
    rcases hj with rfl | rfl | rfl <;> omega
  · intro j1 j2 h1 h2 hne
    unfold sZ
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | omega
  · intro a ha
    unfold ptpX ptL0 ptRoot at ha
    rw [v6]; omega

/-! # 6. TLB non-collision on the real layout -/

theorem svpnToNat (va : BitVec 64) (h : va.toNat < 2 ^ 39) :
    (WeakKpt.svpnOf va).toNat = va.toNat / 4096 := by
  unfold WeakKpt.svpnOf Sail.BitVec.extractLsb
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow,
    Functions.pagesize_bits]
  omega

/-- A register file whose TLB is `tlbW` hits every page of KERNBASE .. `end`. -/
theorem hitOfPage (rs : RegFile) (hT : rs .tlb = tlbW) (va : BitVec 64)
    (h1 : kbase * 4096 ≤ va.toNat) (h2 : va.toNat < (kbase + nPages) * 4096) : hitW rs va := by
  unfold hitW
  rw [hT]
  have e1 : kbase = 0x80000 := rfl
  have e2 : nPages = 0x24 := rfl
  rw [e1] at h1
  rw [e1, e2] at h2
  have hj : va.toNat / 4096 - kbase < nPages := by rw [e1, e2]; omega
  have hv : WeakKpt.svpnOf va = AxSpinT2pt.vpnOf (va.toNat / 4096 - kbase) := by
    apply BitVec.eq_of_toNat_eq
    rw [svpnToNat va (by omega)]
    unfold AxSpinT2pt.vpnOf
    rw [BitVec.toNat_ofNat, e1]
    show _ = (0x80000 + (va.toNat / 4096 - 0x80000)) % 134217728
    omega
  rw [hv]
  exact tlbWHit _ hj

/-- **The touched pages of ANY layout instance lie in KERNBASE .. `end`** (36 consecutive pages,
so they hash to pairwise different TLB slots, `tlbSlotInj`). -/
theorem touchPage (i : Agent) (hi : i < NCPU) (S p : Int)
    (hS : (KernelSyms.«stack0» : Int) + 80 ≤ S ∧ S ≤ (KernelSyms.«stack0» : Int) + 0x8000)
    (hp : ∃ m : Nat, m < 64 ∧ p = (KernelSyms.«proc» : Int) + 376 * (m : Int))
    (va : BitVec 64) :
    t2Touch i S p va → kbase * 4096 ≤ va.toNat ∧ va.toNat < (kbase + nPages) * 4096 := by
  obtain ⟨v1, v2, v3, v4, v5, -, -, -⟩ := AxSpinT2a.symV
  obtain ⟨m, hm, rfl⟩ := hp
  have hc : ((cpuOf i).val : Int) = (i : Int) := by rw [cpuOfNat i hi]
  have hi8 : (i : Int) < 8 := by have := Int.ofNat_lt.2 hi; exact this
  intro ht
  unfold t2Touch cpuZ at ht
  simp only [AxSpinT2a.zNp, AxSpinT2a.zLk] at ht
  rw [v1, v2, v3, v4, hc] at ht
  rw [v5] at hS
  have e1 : kbase = 0x80000 := rfl
  have e2 : nPages = 0x24 := rfl
  rw [e1, e2]
  omega

/-- The warm TLB hits every page a hart of the layout touches. -/
theorem touchHit (rs : RegFile) (hT : rs .tlb = tlbW) (i : Agent) (hi : i < NCPU) (S p : Int)
    (hS : (KernelSyms.«stack0» : Int) + 80 ≤ S ∧ S ≤ (KernelSyms.«stack0» : Int) + 0x8000)
    (hp : ∃ m : Nat, m < 64 ∧ p = (KernelSyms.«proc» : Int) + 376 * (m : Int)) :
    ∀ va, t2Touch i S p va → hitW rs va := by
  intro va ht
  obtain ⟨h1, h2⟩ := touchPage i hi S p hS hp va ht
  exact hitOfPage rs hT va h1 h2

/-- **Warm entry of (a′)**: `regsE h` hits every page hart `h` touches (`entryOk`'s TLB part). -/
theorem entryHit (h : Agent) (hh : h < 3) :
    ∀ va, t2Touch h (sZ h) (AxSpinT2a.pEx h) va → hitW (regsE h) va := by
  have hL := layHyp3
  match h, hh with
  | 0, _ => exact touchHit (regsE 0) rfl 0 (by decide) _ _ (hL.stk 0 (.inl rfl)) (hL.slot 0 (.inl rfl))
  | 1, _ =>
    exact touchHit (regsE 1) rfl 1 (by decide) _ _ (hL.stk 1 (.inr (.inl rfl)))
      (hL.slot 1 (.inr (.inl rfl)))
  | 2, _ =>
    exact touchHit (regsE 2) rfl 2 (by decide) _ _ (hL.stk 2 (.inr (.inr rfl)))
      (hL.slot 2 (.inr (.inr rfl)))
  | n + 3, hh => exact absurd hh (Nat.not_lt.2 (Nat.le_add_left 3 n))

end AxSpinT2c1

end Weak
