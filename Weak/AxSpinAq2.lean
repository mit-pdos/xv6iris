/-
Weak: **THE WHOLE POSITIONAL `acquire` WPd** — xv6's REAL `acquire(lk)` (the 22 non-panic
instructions of `AxSpinAq.acquireText` at `KernelSyms.acquire` = 0x80000c58, calling the real
`push_off`, `holding`, the spin loop and `mycpu`) as a POSITIONAL CPS WPd at the joint instance
Ixv6 (`AxSpinX2.xG L GT nm` / `xv6Pol GT`), interrupts off (`ctrlOkSW`), WARM TLB.

Lean-only (Theorem 2 design `notes/weak-lb-thm2-design.md` §C.1 "Composition", §D row
`AxSpinAq2`; no Rocq source: Rocq stopped before a positional `wpd_acquire`).

## The composition (row positions, AxSpinAqr; `k` = acquire's first memory event)

```
  + 0x00 c.addi sp,-32       XxReg  @ k
  + 0x02/04/06 c.sdsp ra/s0/s1  XxSt @ k, k+1, k+2          (aqHead)
  + 0x08 c.addi4spn; + 0x0a c.mv s1,a0; + 0x0c jal push_off   XxReg @ k+3
  push_off                   wpdPushOff @ k+3 (poSh b), continuation aqKp k b
  + 0x10 c.mv a0,s1; + 0x12 jal holding                       XxReg @ aqKp
  holding                    holdingFromAcquire' @ aqKp (hb; ORacy at aqKp+4), cont. aqKh
  + 0x16 c.li a4,1; + 0x18 c.bnez a0,panic (NOT taken)        XxReg @ aqKh
  + 0x1a … + 0x22 the spin   AxSpinAq1.wpdSpinAq @ aqKh, claim at aqKA, cont. aqKm
  + 0x24 jal mycpu           XxReg @ aqKm
  mycpu                      wpdMycpu @ aqKm, cont. aqKm+4
  + 0x28 c.sd a0,16(s1)      AxSpinRl2.XxSdCpuAcq @ aqKm+4 (the claim's RCpu handle)
  + 0x2a/2c/2e c.ldsp ra/s0/s1  XxLd @ aqKm+5, +6, +7
  + 0x30 c.addi16sp; + 0x32 c.ret                             XxReg / XxRet @ aqKm+8
```
KERNEL CROSS-CHECK (against `Xv6/KernelImage.lean`, acquire = 0x80000c58): the three jal
targets are decided at the literals — `pac 0x0c + (−70) = push_off` (0x80000c1e),
`pac 0x12 + (−120) = holding` (0x80000bf2), `pac 0x24 + 3296 = mycpu` (0x8000195c); the panic
branch target `pac 0x18 + 28 = pac 0x34`; the words are `AxSpinAq.aqCode` (tied to the image by
`AxSpinAq.aqCodeImg`), the text premise `acquireText` is satisfiable (`AxSpinTextCerts.acquireTextOf`).
All pcs but mycpu's lie on page 0x80000 (`hitWSvpn … (by decide)` from `hitW (pac 0)`); mycpu's
page needs its own `hitW (pcm 0)`.

## Files / theorems

§1 row facts: `AxSpinAq2.shWr` (writes of a `RowSh` window), `AxSpinAq2.djOut` (acquire's slot
   misses every other write of the window), `AxSpinAq2.nowrBody` / `AxSpinAq2.nowrSpill`: NO WRITE
   to an acquire spill slot between its spill and the reloads — DERIVED from `RowAcquire` (push_off's
   `poSh`, holding's `RowHolding` both arms, the spin RMWs, mycpu, the lk->cpu store).
§2 `AxSpinAq2.head`: entry → push_off → `jal holding` (boundary `aqKp`).
   `AxSpinAq2.liBnez`: `c.li a4,1; c.bnez a0` with `a0 = 0` (falls through to + 0x1a).
   `AxSpinAq2.mid`: holding (both arms) → `liBnez` (boundary `aqKh`).
   `AxSpinAq2.tail`: the spin → mycpu → the lk->cpu store → reloads → `c.ret` (boundary `aqKm+8`).
§3 `AxSpinAq2.wpdAcquire` (THE THEOREM): from the boundary `k` with `PC = acquire`,
       isLock … RPid -∗ notheld i -∗ AxSpinAq2.KAcq … -∗ WPd ⟨rs0, k⟩
   `AxSpinAq2.KAcq` (the caller's continuation, at the boundary `aqKm k b hb n + 8`, `PC = ret`):
   regime, TLB kept, `sp = sp0`, `a0 = mycpuRet tp`, ra / s0 / s1 = the reloaded words, every GPR
   but ra/sp/s0/s1/a0/a4/a5 kept, the spills' row data, the claim's graph value `z4` at `aqKA`,
   the lk->cpu store's data / label (`wbytes 8 (mycpuRet tp)`, `L.xlLk + 16`) and the reloads'
   graph values; RESOURCES: `(i, aqKA) ↦ₐ locked …`, `(i, aqKA) ↦ₐ RNp …` (the claim; for
   `wpdAllocpidCs` and release's `OHeld`), the lk->cpu handle `(i, aqKm+4) ↦ₐ (True ∗ RVL (clb L)
   (i, aqKm+4) (wbytes 8 (mycpuRet tp)))` deposited by the store (the claim's `RCpu` half is
   CONSUMED by it — exactly `AxSpinHdB.FldMCpuOwn`'s `Hh` for release's holding), and the three
   reload annotations (`RLfact`, reload bytes = spill bytes).

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C row `AxSpinAq2`, Q-S2-1/2)

`AxSpinAq2.wpdAcquireP` is `wpdAcquire` on a PREFIX row, composed from `AxSpinAq2.headP` →
`AxSpinAq2.midP` → `AxSpinAq2.tailP` (the P-forms of `head`/`mid`/`tail`), which call the merged
P-forms `wpdPushOffP` (PO4), `holdingFromAcquireP` (HdC), `wpdSpinAqP` (Aq1), `wpdMycpuP` (E8) and
the position-generic `XxSdCpu` (Rl2).  Row premises: `RowAcquireP` (new here: `RowShP` windows,
`RowHoldingP`, the spin RMW items at present positions; no length conjunct),
`AxSpinAq1.spinRmwP` / `spinValsP`.  One `by_cases` on `LEN ≤ position` per row position (inside
the pieces: `k .. k + 3`, `aqKp`, `aqKh`, `aqKm`, `aqKm + 4 … + 8`); the end case is the WINDOWED,
RESOURCE-FREE hook (merged form, as AxSpinE8 / PO4 / HdA), with ONE exclusion:
  `HΨend : ∀ k', k ≤ k' → k' ≤ aqKm k b hb n + 8 → (hb = true → k' ≠ aqKp k b + 12) →
     (grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6, ⊢ wpdM … .MaybeStuck i ⟨pr, k'⟩ Ψ`
— the hook does NOT cover the DESIGNATED CUT `aq` (`t2KHd q + 12` of AxSpinT2f: holding's long arm
ended after its last reload, before acquire's `c.bnez a0,panic`).  That position is the premise
  `Kaq : hb = true → ∀ rsH, ⊢ KLongEnd … (aqKp k b) rsH Hra Hs0 Hs1 Hram Hs0m (fun _ => True)
     (ORacy L GT i (aqKp k b + 4))`
(RESOURCE-CARRYING: holding's end continuation, handed the `lk->cpu` read's `ORacy` / `rdFact`
deposit, the load values and the reload annotations; to be supplied by AxSpinT2h's D4 readback;
it is not discharged here).  `midP` uses `Kaq` twice: as holdingFromAcquireP's `KLongEnd`, and in
the `KLong` continuation when the row has length exactly `aqKp + 12` (`AxSpinAq2.gvLt`: the
reload at `aqKp + 11` is present).  Sub-windows: push_off `[k + 3, aqKp]`, holding
`[aqKp, aqKp (+ 11)]`, `midP` `[aqKp, if hb then aqKp + 11 else aqKp + 1]` (the short arm's end
`aqKp + 1` is not a cut for acquire: the hook; `AxSpinAq2.midWin`), spin `[aqKh, aqKm]`, mycpu
`[aqKm, aqKm + 4]`, `tailP` `[aqKh, aqKm + 8]` (it misses the cut because `midP`'s continuation
carries `aqKh < LEN`).  PINS GUARDED by position (`AxSpinT2f.AllocPins2` style): push_off's
(`k + 3 + 5`, `b → k + 3 + 10`, `tk + 2`, `tk + 6`), the s1 reloads (`tk + 8`, `aqKp + 11`),
holding's returns (`aqKp + 7`, `aqKp + 9`), mycpu's (`aqKm + 2`), acquire's (`aqKm + 5`); the
NON-PANIC ARM pin (stage 1's `hdArm`) is guarded by `aqKp + 12 < LEN` — a row continuing past the
cut took the normal arm (AxSpinT2f's gate conjunct supplies it in ApA); `Vb` is
value-conditional already.  The continuation `AxSpinAq2.KAcqP` is `KAcq` plus what push_off
hands on, PASSED THROUGH (not dropped): the `sw noff` / `sw intena` row labels, the second noff
read's value `vn` (`graphValue (tk + 4)`), and push_off's two CONDITIONAL genesis annotations
(`∀ _ : AxSpinLd4P.noWrBefore … , (i, ·) ↦ₐ ⌜genFact4 …⌝` at `k + 3 + 7` and `tk + 4`).
`head`, `mid`, `tail`, `wpdAcquire` keep their exact names and statements and are now the
full-row corollaries (`AxSpinAq2.rowAcquirePOfFull`, `rowShPOfSh`, `rowHoldingPOfFull`; hooks
and `Kaq` vacuous under the length conjunct; pins unguarded; the extra continuation data dropped).

## P1 GATE FORM (Lean-only; notes/weak-lb-thm2-pins.md §P1; what ApB's segment proof calls)

`AxSpinAq2.wpdAcquireG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxp Htxh
Ψ HΨmid k b hb n rs0 ib0 Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi Hra Hs0 Hs1 Hram Hs0m Mra Mms0 Pcl
Plk` has EXACTLY `wpdAcquireP`'s premises, in the same order, except (no `ret` argument):
  * push_off's five reload pins → `AxSpinT2i.Gate GT i (k+3+5) (stBytes 8 (ppo 0x14))`, `Vb`
    (the arm, unchanged), `b = true → Gate (k+3+10) (stBytes 8 (ppo 0x30))`, `Gate (tk+2)
    (stBytes 8 (ppo 0x1c))`, `Gate (tk+6) (stBytes 8 (pac 0x10))`, `Gate (tk+8) (stBytes 8
    (gprVal rs0 r10))` (`tk = k + 3 + 8 + (if b then 5 else 0)`);
  * holding's block → `hb = true → Gate (aqKp+7) (stBytes 8 (pch 0x1a)) ∧ Gate (aqKp+9) (stBytes
    8 (pac 0x16)) ∧ Gate (aqKp+11) (stBytes 8 (gprVal rs0 r10)) ∧ (aqKp+12 < LEN → ∀ vcpu, gv
    (aqKp+4) = some vcpu → hres … = 0)` (the non-panic arm stays a guarded value premise);
  * mycpu's → `Gate (aqKm+2) (stBytes 8 (pac 0x28))`; acquire's own `ra` → `Gate (aqKm+5)
    (stBytes 8 (gprVal rs0 r1))` (the entry ra = the caller's `jal` link); NEW `aqS1`: `∀ vw,
    graphData (i, k+2) = some vw → Gate (aqKm+7) vw` (against the spill's own row data — what
    T2f's `rlExp .aqS1 = wd row 2` / `gateBody` gives from `allocPre` alone, via `wdGrow`);
    `Hret : jalrTgt 0#12 (gprVal rs0 r1) = gprVal rs0 r1`;
  * `Kaq` (designated cut `aq`) and `HΨend` UNCHANGED;
  * continuation `AxSpinAq2.KAcqG … rs0 Pra Ps0 Ps1 Pn Pi` = `KAcqP` at `ret := gprVal rs0 r1`
    with the pure premise `⌜(vra' = stBytes 8 (gprVal rs0 r1) ∧ vs1' = stBytes 8 (gprVal rs0 9) ∧
    gprVal rs' r1 = gprVal rs0 r1 ∧ gprVal rs' 9 = gprVal rs0 9) ∧ <KAcqP's pure premise>⌝`.
Shared proofs (the old P-forms are their corollaries via `AxSpinT2i.gateOfPinG`, statements
unchanged): `AxSpinAq2.headG` (calls `wpdPushOffG`; ret := the link `pac 0x10`, s1 = lk from
push_off's post), `AxSpinAq2.midG` (calls `holdingFromAcquireG`; `KLongG` is reached only past
the cut, so `Kaq` is used only as `KLongEnd`), `AxSpinAq2.tailGr` (`ret` generic; calls
`wpdMycpuG`; at acquire's ra reload's boundary `aqKm + 6` a `by_cases` on the value: a wrong
value with `stBytes 8 ret` = the spill is REFUTED by `AxSpinT2i.cutReloadG`, otherwise the gate
gives the row end and the hook), `AxSpinAq2.wpdAcquireGr` (`ret` generic; all gates but `aqS1`).
`wpdAcquireG` = `wpdAcquireGr` at `ret := gprVal rs0 r1`, then in its continuation (`aqKm + 8`)
a wrong `ra` / `s1` value is REFUTED (`AxSpinT2i.wpdEnd1` + `rlFactEq` on the reload's `RLfact`,
row end from the gate) — PO4's `wpdPushOffG` pattern.  HONESTY: `wpdAcquireG` has NO reload pin;
its only value premises are the two arm selectors (`Vb`, the non-panic arm past the cut).

## Premises / honesty (Q20' provisional Option V)

* ROW: `RowAcquire k b hb n row …` (AxSpinAqr; `plk = L.xlLk`, `pcl = L.xlLk + 16`),
  `AxSpinAq1.spinRmw` (the RMW labels at `.WCexcl`, AxSpinAq1) and `spinVals`, `rowW8`, the
  callees' no-RMW / write-width facts, `CpuWin L GT i (i, aqKA …)` (AxSpinRl2, Q-T2-9: hart `i`'s
  own lk->cpu stores after the claim write `cvx i` or 0).
* PINS (graph VALUES of hart `i`'s OWN reads; the theorem proves nothing about a graph whose values
  differ): push_off's five (`wpdPushOff`: mycpu returns, the noff arm `b`, push_off's return to
  `acquire + 0x10`); holding's long-arm returns (`hb → …`, `holdingFromAcquire'`); mycpu's return to
  `acquire + 0x28`; acquire's own return (`(i, aqKm+5) = stBytes 8 ret`, `jalrTgt 0 ret = ret`;
  the caller instantiates `ret = allocproc + 0x44`).  NEW pins, of the same kind:
  - the NON-PANIC ARM of `if(holding(lk)) panic` (design §C.1): on the long arm,
    `∀ vcpu, gv (i, aqKp+4) = some vcpu → hres (0 + ldRes vcpu) (mycpuRet tp) = 0`, i.e. the
    lk->cpu read is not this cpu (`a0 = 0`); the short arm returns 0 by itself;
  - the two s1 RELOADS before the lock is used (DEVIATION from the design's pin list, forced): the
    lock address lives in s1 across `push_off` and `holding`, which spill and reload it; the
    reloads' values are only known through their `RLfact` ANNOTATIONS (not pure inside a WPd), and
    every lock-word leaf needs the address as a register value.  So, as release's design (§C.2:
    "the reload's graph value … is a pin like `Hval`"): `gv (i, tk+8) = stBytes 8 lkv` (push_off's
    s1 reload, `tk = k+3+8(+5)`) and `hb → gv (i, aqKp+11) = stBytes 8 lkv` (holding's).  Both are
    hart `i`'s private reloads of its own spill (ownership makes them true; T2-cuts discharges them
    with the other reload pins).
* Interrupts off (`ctrlOkSW`), warm TLB for every touched page, the slots private (`slot8`/`fld4`)
  and pairwise disjoint where the callees ask; acquire's three slots disjoint from every other
  write of the window (`djOut`) — all layout facts.
* Dropped (affine): holding's five reload annotations and `ORacy` deposit, mycpu's and push_off's
  reload annotations, `notheld`'s failed-spin returns (consumed by the claim).

## Deviations

1. The extra s1-reload pins (above).
2. The spin / claim RMW label class is `.WCexcl` (AxSpinAq1, 2026-10-08 fix); this file states no
   RMW label itself (it passes `AxSpinAq1.spinRmw` through).
3. `wpdAcquire` already names AxSpinH2's literal contract, so the theorem is file-qualified
   `AxSpinAq2.wpdAcquire` (as AxSpinAq1's header announces).  Split into `head`/`mid`/`tail` at the
   push_off/holding/spin seams (heartbeats), composed in one file.

**Reused** (by name): `XxReg`, `XxSt`, `XxLd`, `XxRet` (AxSpinE6); `wpdPushOff`, `slot8Tlb`,
`fld4Tlb`, `poSh` (AxSpinPO4); `holdingFromAcquire'` (AxSpinHdC); `KLong`/`KShort` (AxSpinHdA);
`wpdSpinAq`, `AxSpinAq1.KSpin`, `AxSpinAq1.spinRmw` (AxSpinAq1); `wpdMycpu` (AxSpinE8);
`XxSdCpuAcq`, `CpuWin` (AxSpinRl2); `RowAcquire`/`aqHead`/`aqTail`/`aqKp`/`aqKh`/`aqKm`/`aqKA`/
`aqKpPos`/`aqTailLen` (AxSpinAqr); `RowSh`/`rowShAppL`/`rowShNowr`/`nowrJoin`/`shStore`/`itDisj`/
`dj`/`alldj`/`rowMycpuOf`/`ax_spin_por_nowr` (AxSpinPOr); the text lemmas `tw1101`/`twEc06`/`twE822`/
`twE426`/`tw1000` (AxSpinPOt1), `tw60e2`/`tw6442` (AxSpinPOt2), `tw64a2`/`tw6105`/`tw8082`
(AxSpinPOt3), `twa84aa`/`twa8526`/`twa4705`/`twaEd11` (AxSpinAqt1), `twaE888` (AxSpinAqt2),
`tw4A0c`/`tw4A12`/`tw4A24` (AxSpinAqd); `certAddi`/`certAdd` (AxSpinE7), `certJAL`/`certBTYPE`
(AxSymCtl2); `stepRegs`/`stepRegs0`/`gbCtrl`/`gbPc`/`gbTlb`/`retxRefl`/`hitWSvpn`/
`AxSpinE8.ldResStBytes8`/`AxSpinE8.upd*` (AxSpinE8).

**Lean-only declarations** (all file-qualified): `AxSpinAq2.addZ`, `AxSpinAq2.c2`,
`AxSpinAq2.imm18`, `AxSpinAq2.rdNoWr`, `AxSpinAq2.stWr`, `AxSpinAq2.shWr`, `AxSpinAq2.djOut`,
`AxSpinAq2.nowrBody`, `AxSpinAq2.nowrSpill`, `AxSpinAq2.head`, `AxSpinAq2.liBnez`,
`AxSpinAq2.mid`, `AxSpinAq2.KTail`, `AxSpinAq2.tail`, `AxSpinAq2.KAcq`, `AxSpinAq2.wpdAcquire`
(+ 1 local macro); stage 2: `AxSpinAq2.gvLt`, `AxSpinAq2.shStoreP`, `AxSpinAq2.winMono`,
`AxSpinAq2.midWin`, `AxSpinAq2.rowAcquirePOfFull`, `AxSpinAq2.shWrP`, `AxSpinAq2.nowrBodyP`,
`AxSpinAq2.nowrSpillP`, `AxSpinAq2.headP`, `AxSpinAq2.midP`, `AxSpinAq2.tailP`, `AxSpinAq2.KAcqP`,
`AxSpinAq2.wpdAcquireP`, and (unqualified, grepped unique) `RowAcquireP`.  Reused for the P-form:
`wpdPushOffP`, `AxSpinLd4P.noWrBefore`/`genFact4` (AxSpinPO4); `holdingFromAcquireP`,
`ORacy` (AxSpinHdC/HdB); `KLongEnd`/`KShortEnd` (AxSpinHdA); `RowHoldingP`,
`AxSpinHd8.rowHoldingPOfFull` (AxSpinHd8); `wpdSpinAqP`, `AxSpinAq1.spinRmwP`/`spinValsP`
(AxSpinAq1); `wpdMycpuP`, `RowMycpuP` (AxSpinE8); `AxSpinPO3.rowMycpuPOf`/`rowShPNowr`;
`XxSdCpu` (AxSpinRl2); `RowShP`/`rowShP*` (AxSpinRowP).  P1 (all file-qualified):
`AxSpinAq2.headG`, `AxSpinAq2.midG`, `AxSpinAq2.tailGr`, `AxSpinAq2.wpdAcquireGr`,
`AxSpinAq2.KAcqG`, `AxSpinAq2.wpdAcquireG`; reused `wpdPushOffG` (PO4), `holdingFromAcquireG`
(HdC), `KLongG` (HdA), `wpdMycpuG` (E8), `AxSpinT2i.Gate`/`gateOfPinG`/`lenOfGate`/`cutReloadG`/
`wpdEnd1`/`rlFactEq` (T2i), `AxSpinPO4.stBytes8Len`.
-/
import Weak.AxSpinAq1
import Weak.AxSpinAqd
import Weak.AxSpinAqt1
import Weak.AxSpinPO4
import Weak.AxSpinHdC
import Weak.AxSpinRl2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_aq2_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-! # 1. Pure facts; no write to acquire's spill slots inside the window -/

theorem AxSpinAq2.addZ (v : BitVec 64) : v + sign_extend (m := 64) (0#12) = v := by
  rw [show sign_extend (m := 64) (0#12) = 0#64 by decide]
  exact BitVec.add_zero v

/-- `c.bnez a0`'s compressed register (`a0`). -/
def AxSpinAq2.c2 : BitVec 5 := creg5 (.Cregidx 2#3)
/-- `c.bnez a0,panic`'s offset (+28). -/
def AxSpinAq2.imm18 : BitVec 13 := sign_extend (m := 13) (14#8 +++ 0b0#1)

theorem AxSpinAq2.rdNoWr {lb : Lbl} {aq : Bool} {p : Int} {m : Nat} {x : Bool × Int × Nat} :
    aident lb = .IRead aq p m → aidentWr (aident lb) = some x → False := by
  intro E H
  rw [E] at H
  cases H

theorem AxSpinAq2.stWr {lb : Lbl} {p pa : Int} {w : Nat} {rl : Bool} {bb : Int} {m : Nat} :
    (∃ vw cls, lb = .LStore false p vw cls ∧ vw.length = 8) →
    aidentWr (aident lb) = some (rl, bb, m) → dj p 8 pa w → dj bb m pa w := by
  rintro ⟨vw, cls, rfl, Hl⟩ H Hd
  simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨_, rfl, rfl⟩ := H
  rw [Hl]
  exact Hd

/-- The writes of a `RowSh` window miss `(pa, w)` when every store item does. -/
theorem AxSpinAq2.shWr (k0 : Nat) (row : List Lbl) (sh : List Ritem) (pa : Int) (w : Nat) :
    RowSh k0 row sh → (∀ it ∈ sh, itDisj pa w it) →
    ∀ (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat), k0 ≤ k' → k' < k0 + sh.length →
      row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) → dj b m pa w := by
  intro H HF k' lb rl b m h1 h2 Hlb Hid
  obtain ⟨it, Hit⟩ : ∃ it, sh[k' - k0]? = some it :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨lb', Hlb', Hs⟩ := H (k' - k0) it Hit
  rw [show k0 + (k' - k0) = k' by omega, Hlb] at Hlb'
  cases Hlb'
  have Hd : itDisj pa w it := HF it (List.mem_of_getElem? Hit)
  cases it with
  | RF n => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hid; cases Hid
  | RP pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid
  | RS pb n =>
    obtain ⟨vw, cls, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    rw [Hl]
    exact Hd
  | RL pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid

/-- An acquire spill slot `(pa, w)` misses every other write of acquire's window (push_off's,
holding's and mycpu's slots and cpu fields, the lock word, `lk->cpu`). -/
def AxSpinAq2.djOut (pa : Int) (w : Nat)
    (qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int) : Prop :=
  dj qra 8 pa w ∧ dj qs0 8 pa w ∧ dj qs1 8 pa w ∧ dj qmra 8 pa w ∧ dj qms0 8 pa w ∧
  dj pn 4 pa w ∧ dj pint 4 pa w ∧ dj hra 8 pa w ∧ dj hs0 8 pa w ∧ dj hs1 8 pa w ∧
  dj hram 8 pa w ∧ dj hs0m 8 pa w ∧ dj plk 4 pa w ∧ dj pcl 8 pa w ∧ dj mra 8 pa w ∧
  dj ms0 8 pa w

/-- No write to `(pa, w)` strictly inside acquire's window after the spills (`k + 2`) up to the
boundary after the last reload (`aqKm + 8`). -/
theorem AxSpinAq2.nowrBody (k : Nat) (b hb : Bool) (n : Nat) (row : List Lbl)
    (pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int)
    (pa : Int) (w : Nat) :
    RowAcquire k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk
      pcl mra ms0 →
    AxSpinAq2.djOut pa w qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 →
    nowr row (k + 2) (aqKm k b hb n + 8) pa w := by
  rintro ⟨_, Hpo, Hho, Hsp, Hta, _⟩
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16⟩
  intro k' lb rl bb m ⟨h1, h2⟩ Hlb Hid
  have Ekp := aqKpPos k b
  by_cases c1 : k' < aqKp k b
  · -- push_off's window `k + 3 .. aqKp`
    refine AxSpinAq2.shWr (k + 3) row _ pa w Hpo ?_ k' lb rl bb m (by omega) ?_ Hlb Hid
    · cases b <;>
        simp only [poSh, ↓reduceIte, Bool.false_eq_true, List.nil_append] <;>
        ax_spin_por_nowr
    · rw [show (poSh b qra qs0 qs1 qmra qms0 pn pint).length = 17 + (if b then 5 else 0) by
        cases b <;> rfl]
      omega
  by_cases c2 : k' < aqKh k b hb
  · -- holding's window `aqKp .. aqKh`
    obtain ⟨j, rfl⟩ : ∃ j, k' = aqKp k b + j := ⟨k' - aqKp k b, by omega⟩
    unfold RowHolding at Hho
    cases hb with
    | false =>
      obtain ⟨_, _, Hsh⟩ := Hho
      rw [show aqKh k b false = aqKp k b + 1 from rfl] at c2
      obtain rfl : j = 0 := by omega
      obtain ⟨lb', Hl', aq, E⟩ := Hsh 0 (by omega)
      rw [Hlb] at Hl'
      cases Hl'
      exact (AxSpinAq2.rdNoWr E Hid).elim
    | true =>
      obtain ⟨_, _, Hsh, Hmy⟩ := Hho
      rw [show aqKh k b true = aqKp k b + 12 from rfl] at c2
      by_cases hm : j < 5 ∨ 8 < j
      · obtain ⟨lb', Hl', Hs⟩ := Hsh j (by omega) hm
        rw [Hlb] at Hl'
        cases Hl'
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 9 ∨ j = 10 ∨ j = 11 by omega)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · exact AxSpinAq2.stWr Hs Hid d8
        · exact AxSpinAq2.stWr Hs Hid d9
        · exact AxSpinAq2.stWr Hs Hid d10
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
      · obtain ⟨j', rfl⟩ : ∃ j', j = 5 + j' := ⟨j - 5, by omega⟩
        obtain ⟨lb', Hl', Hs⟩ := Hmy.2 j' (by omega)
        rw [show aqKp k b + 5 + j' = aqKp k b + (5 + j') by omega, Hlb] at Hl'
        cases Hl'
        rcases (show j' = 0 ∨ j' = 1 ∨ j' = 2 ∨ j' = 3 by omega) with rfl | rfl | rfl | rfl
        · exact AxSpinAq2.stWr Hs Hid d11
        · exact AxSpinAq2.stWr Hs Hid d12
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
  by_cases c3 : k' < aqKm k b hb n
  · -- the spin RMWs `aqKh .. aqKA`
    unfold aqKm at c3
    obtain ⟨lb', Hl', Hid'⟩ := Hsp (k' - aqKh k b hb) (by omega)
    rw [show aqKh k b hb + (k' - aqKh k b hb) = k' by omega, Hlb] at Hl'
    cases Hl'
    rw [Hid'] at Hid
    simp only [aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    exact d13
  · -- the tail `aqKm .. aqKm + 8`
    refine AxSpinAq2.shWr _ row _ pa w Hta ?_ k' lb rl bb m (by omega)
      (by rw [aqTailLen]; omega) Hlb Hid
    simp only [aqTail]
    ax_spin_por_nowr

/-- No write to acquire's spill slot `j` between its spill (`k + j`) and the boundary after the
last reload, from the row shape and the layout. -/
theorem AxSpinAq2.nowrSpill (k : Nat) (b hb : Bool) (n : Nat) (row : List Lbl)
    (pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int)
    (j : Nat) (pa : Int) :
    RowAcquire k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk
      pcl mra ms0 →
    j ≤ 2 →
    (∀ it ∈ ((aqHead pra ps0 ps1).take 3).drop (j + 1), itDisj pa 8 it) →
    AxSpinAq2.djOut pa 8 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 →
    nowr row (k + j) (aqKm k b hb n + 8) pa 8 := by
  intro HR hj Hh Ho
  have H1 := rowShNowr k row (aqHead pra ps0 ps1) j 3 pa 8 HR.1 (by simp [aqHead]) Hh
  exact nowrJoin row (k + j) (k + 2) _ pa 8 (by omega) H1
    (AxSpinAq2.nowrBody k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram
      hs0m plk pcl mra ms0 pa 8 HR Ho)

/-! ## Stage 2: prefix rows -/

/-- (Lean-only) a position with a graph value is PRESENT in the row. -/
theorem AxSpinAq2.gvLt (GD : Gdexec) (i k : Nat) (v : List (BitVec 8)) :
    graphValue GD (i, k) = some v → k < (AxOpsem.grow GD i).length := by
  intro h
  have E : gxLbl GD.gdG (i, k) = (AxOpsem.grow GD i)[k]? := by
    unfold gxLbl AxOpsem.grow growG
    cases GD.gdG.gxProg[i]? <;> simp
  unfold graphValue at h
  rw [E] at h
  cases hk : (AxOpsem.grow GD i)[k]? with
  | none => rw [hk] at h; simp at h
  | some lb => exact (List.getElem?_eq_some_iff.1 hk).1

/-- (Lean-only) `shStore` on a PREFIX window, at a present position. -/
theorem AxSpinAq2.shStoreP (k : Nat) (row : List Lbl) (sh : List Ritem) (j : Nat) (pa : Int)
    (n : Nat) :
    RowShP k row sh → sh[j]? = some (.RS pa n) → k + j < row.length →
    ∃ vw cls, row[k + j]? = some (.LStore false pa vw cls) ∧ vw.length = n := by
  intro H Hj Hk
  obtain ⟨lb, Hlb, vw, cls, rfl, Hl⟩ := H _ _ Hj Hk
  exact ⟨vw, cls, Hlb, Hl⟩

/-- (Lean-only) holding's call-site window `[kp, kp (+ 11)]` sits inside `midP`'s window. -/
theorem AxSpinAq2.winMono (hb : Bool) (a k' : Nat) :
    k' ≤ (if hb then a + 11 else a) → k' ≤ (if hb then a + 11 else a + 1) := by
  cases hb <;> simp <;> omega

/-- (Lean-only) `midP`'s window sits inside acquire's, and misses the designated cut `aq`
(`aqKp + 12`, the long arm's end). -/
theorem AxSpinAq2.midWin (k : Nat) (b hb : Bool) (n k' : Nat) :
    k' ≤ (if hb then aqKp k b + 11 else aqKp k b + 1) →
    k' ≤ aqKm k b hb n + 8 ∧ (hb = true → k' ≠ aqKp k b + 12) := by
  unfold aqKm aqKh
  cases hb <;> simp <;> omega

/-- (Lean-only, stage 2) `RowAcquire` on a PREFIX row: every window item that is PRESENT has
its shape (`RowShP`, `RowHoldingP`, the spin RMW items at present positions); no length
conjunct. -/
def RowAcquireP (k : Nat) (b hb : Bool) (n : Nat) (row : List Lbl)
    (pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int) :
    Prop :=
  RowShP k row (aqHead pra ps0 ps1) ∧
  RowShP (k + 3) row (poSh b qra qs0 qs1 qmra qms0 pn pint) ∧
  RowHoldingP (aqKp k b) row hb plk pcl hra hs0 hs1 hram hs0m ∧
  (∀ j, j ≤ n → aqKh k b hb + j < row.length → spinIt (aqKh k b hb + j) row plk) ∧
  RowShP (aqKm k b hb n) row (aqTail mra ms0 pcl pra ps0 ps1)

/-- (Lean-only) a full acquire row is a prefix row. -/
theorem AxSpinAq2.rowAcquirePOfFull (k : Nat) (b hb : Bool) (n : Nat) (row : List Lbl)
    (pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int) :
    RowAcquire k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk
      pcl mra ms0 →
    RowAcquireP k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk
      pcl mra ms0 := by
  rintro ⟨H1, H2, H3, H4, H5, _⟩
  exact ⟨rowShPOfSh H1, rowShPOfSh H2, AxSpinHd8.rowHoldingPOfFull _ _ _ _ _ _ _ _ _ _ H3,
    fun j hj _ => H4 j hj, rowShPOfSh H5⟩

/-- (Lean-only) `AxSpinAq2.shWr` on a PREFIX window. -/
theorem AxSpinAq2.shWrP (k0 : Nat) (row : List Lbl) (sh : List Ritem) (pa : Int) (w : Nat) :
    RowShP k0 row sh → (∀ it ∈ sh, itDisj pa w it) →
    ∀ (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat), k0 ≤ k' → k' < k0 + sh.length →
      row[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) → dj b m pa w := by
  intro H HF k' lb rl b m h1 h2 Hlb Hid
  have Hlt : k' < row.length := (List.getElem?_eq_some_iff.1 Hlb).1
  obtain ⟨it, Hit⟩ : ∃ it, sh[k' - k0]? = some it :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨lb', Hlb', Hs⟩ := H (k' - k0) it Hit (by omega)
  rw [show k0 + (k' - k0) = k' by omega, Hlb] at Hlb'
  cases Hlb'
  have Hd : itDisj pa w it := HF it (List.mem_of_getElem? Hit)
  cases it with
  | RF n => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hid; cases Hid
  | RP pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid
  | RS pb n =>
    obtain ⟨vw, cls, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    rw [Hl]
    exact Hd
  | RL pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid

/-- (Lean-only, stage 2) `AxSpinAq2.nowrBody` on a PREFIX row (absent positions carry no
write). -/
theorem AxSpinAq2.nowrBodyP (k : Nat) (b hb : Bool) (n : Nat) (row : List Lbl)
    (pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int)
    (pa : Int) (w : Nat) :
    RowAcquireP k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk
      pcl mra ms0 →
    AxSpinAq2.djOut pa w qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 →
    nowr row (k + 2) (aqKm k b hb n + 8) pa w := by
  rintro ⟨_, Hpo, Hho, Hsp, Hta⟩
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16⟩
  intro k' lb rl bb m ⟨h1, h2⟩ Hlb Hid
  have Hlt : k' < row.length := (List.getElem?_eq_some_iff.1 Hlb).1
  have Ekp := aqKpPos k b
  by_cases c1 : k' < aqKp k b
  · refine AxSpinAq2.shWrP (k + 3) row _ pa w Hpo ?_ k' lb rl bb m (by omega) ?_ Hlb Hid
    · cases b <;>
        simp only [poSh, ↓reduceIte, Bool.false_eq_true, List.nil_append] <;>
        ax_spin_por_nowr
    · rw [show (poSh b qra qs0 qs1 qmra qms0 pn pint).length = 17 + (if b then 5 else 0) by
        cases b <;> rfl]
      omega
  by_cases c2 : k' < aqKh k b hb
  · obtain ⟨j, rfl⟩ : ∃ j, k' = aqKp k b + j := ⟨k' - aqKp k b, by omega⟩
    unfold RowHoldingP at Hho
    cases hb with
    | false =>
      obtain ⟨_, Hsh⟩ := Hho
      rw [show aqKh k b false = aqKp k b + 1 from rfl] at c2
      obtain rfl : j = 0 := by omega
      obtain ⟨lb', Hl', aq, E⟩ := Hsh 0 (by omega) Hlt
      rw [Hlb] at Hl'
      cases Hl'
      exact (AxSpinAq2.rdNoWr E Hid).elim
    | true =>
      obtain ⟨_, Hsh, Hmy⟩ := Hho
      rw [show aqKh k b true = aqKp k b + 12 from rfl] at c2
      by_cases hm : j < 5 ∨ 8 < j
      · obtain ⟨lb', Hl', Hs⟩ := Hsh j (by omega) hm Hlt
        rw [Hlb] at Hl'
        cases Hl'
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 9 ∨ j = 10 ∨ j = 11 by omega)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · exact AxSpinAq2.stWr Hs Hid d8
        · exact AxSpinAq2.stWr Hs Hid d9
        · exact AxSpinAq2.stWr Hs Hid d10
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
      · obtain ⟨j', rfl⟩ : ∃ j', j = 5 + j' := ⟨j - 5, by omega⟩
        obtain ⟨lb', Hl', Hs⟩ := Hmy j' (by omega) (by omega)
        rw [show aqKp k b + 5 + j' = aqKp k b + (5 + j') by omega, Hlb] at Hl'
        cases Hl'
        rcases (show j' = 0 ∨ j' = 1 ∨ j' = 2 ∨ j' = 3 by omega) with rfl | rfl | rfl | rfl
        · exact AxSpinAq2.stWr Hs Hid d11
        · exact AxSpinAq2.stWr Hs Hid d12
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
        · obtain ⟨_, E⟩ := Hs; exact (AxSpinAq2.rdNoWr E Hid).elim
  by_cases c3 : k' < aqKm k b hb n
  · unfold aqKm at c3
    obtain ⟨lb', Hl', Hid'⟩ := Hsp (k' - aqKh k b hb) (by omega) (by omega)
    rw [show aqKh k b hb + (k' - aqKh k b hb) = k' by omega, Hlb] at Hl'
    cases Hl'
    rw [Hid'] at Hid
    simp only [aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    exact d13
  · refine AxSpinAq2.shWrP _ row _ pa w Hta ?_ k' lb rl bb m (by omega)
      (by rw [aqTailLen]; omega) Hlb Hid
    simp only [aqTail]
    ax_spin_por_nowr

/-- (Lean-only, stage 2) `AxSpinAq2.nowrSpill` on a PREFIX row. -/
theorem AxSpinAq2.nowrSpillP (k : Nat) (b hb : Bool) (n : Nat) (row : List Lbl)
    (pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 : Int)
    (j : Nat) (pa : Int) :
    RowAcquireP k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk
      pcl mra ms0 →
    j ≤ 2 →
    (∀ it ∈ ((aqHead pra ps0 ps1).take 3).drop (j + 1), itDisj pa 8 it) →
    AxSpinAq2.djOut pa 8 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m plk pcl mra ms0 →
    nowr row (k + j) (aqKm k b hb n + 8) pa 8 := by
  intro HR hj Hh Ho
  have H1 := AxSpinPO3.rowShPNowr k row (aqHead pra ps0 ps1) j 3 pa 8 HR.1 (by simp [aqHead]) Hh
  exact nowrJoin row (k + j) (k + 2) _ pa 8 (by omega) H1
    (AxSpinAq2.nowrBodyP k b hb n row pra ps0 ps1 qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram
      hs0m plk pcl mra ms0 pa 8 HR Ho)

/-! # 2. The three pieces -/

section ktail
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- The continuation of acquire's TAIL (boundary `aqKm + 8`, `PC = ret`): `spS` / `tp` are the
spin-entry sp / tp; the claim's `locked` / `RNp`, the lk->cpu deposit, the three reloads. -/
def AxSpinAq2.KTail (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64)
    (i : Agent) (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (b hb : Bool) (n : Nat)
    (rsS : RegFile) (spS tp ret : BitVec 64) (Pra Ps0 Ps1 : BitVec 64)
    (vra vs0 vs1 : List (BitVec 8)) : IProp GF :=
  iprop(∀ (vra' vs0' vs1' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
    ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rsS .tlb ∧
      gprVal rs' AxSpinE8.r2 = spS + sign_extend (m := 64) (caddi16spImm 2#6) ∧
      gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet tp ∧
      vra'.length = 8 ∧ vs0'.length = 8 ∧ vs1'.length = 8 ∧
      gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
      gprVal rs' 9#5 = ldRes false 8 vs1' ∧
      (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
        r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rsS r) ∧
      graphValue (gtAdGd GT) (i, aqKA k b hb n) = some AxSpinX4.z4 ∧
      graphData (gtAdGd GT) (i, aqKm k b hb n + 4) =
        some (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet tp)) ∧
      (∃ cls, (AxOpsem.grow (gtAdGd GT) i)[aqKm k b hb n + 4]? =
        some (.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet tp)) cls)) ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 5) = some vra' ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 6) = some vs0' ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 7) = some vs1'⌝ -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKA k b hb n) (locked nm.xnReg L.xlLk i (i, aqKA k b hb n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKA k b hb n)
      (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, aqKA k b hb n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 4)
      iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, aqKm k b hb n + 4)
        (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet tp))) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 5)
      iprop(⌜RLfact GT i (paZ Pra) (aqKm k b hb n + 5) vra⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 6)
      iprop(⌜RLfact GT i (paZ Ps0) (aqKm k b hb n + 6) vs0⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 7)
      iprop(⌜RLfact GT i (paZ Ps1) (aqKm k b hb n + 7) vs1⌝) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
      ⟨.PHart cpu (.pure ()) rs' none ib', aqKm k b hb n + 8⟩ Ψ)

end ktail

section pieces
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
variable (Htxh : holdingText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxp HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `AxSpinAq2.head` on a PREFIX row (`RowShP` windows, pins
guarded by position): a `by_cases` on `LEN ≤ position` at `k`, `k + 1`, `k + 2`, `k + 3` and
`aqKp k b`; push_off is `wpdPushOffP` with the sub-window `[k + 3, aqKp]`; the row-end case is
the WINDOWED, RESOURCE-FREE hook over `[k, aqKp]`.  The continuation additionally receives
push_off's two store labels, its second noff read's value, and its two CONDITIONAL genesis
annotations (passed on).

(Lean-only, P1) THE GATE FORM / shared proof: push_off is `wpdPushOffG` (its `ret` is the link
`acquire + 0x10` of `jal push_off`), every reload pin of push_off (three mycpu returns, its `ra`
and `s1` reloads) replaced by its `AxSpinT2i.Gate` against the spilled bytes; push_off's post
hands back `s1 = lk` directly.  `AxSpinAq2.headP` = this ∘ `AxSpinT2i.gateOfPinG`. -/
theorem AxSpinAq2.headG (k : Nat) (b : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi : BitVec 64) :
    -- the row
    RowShP k (AxOpsem.grow (gtAdGd GT) i) (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) →
    RowShP (k + 3) (AxOpsem.grow (gtAdGd GT) i)
      (poSh b (paZ Qra) (paZ Qs0) (paZ Qs1) (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi)) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0 → hitW rs0 (AxSpinHdB.pac 0) →
    hitW rs0 (pcm 0) →
    -- acquire's slots
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    -- push_off's slots and cpu fields
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm24) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm16) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm8) Qs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qs1, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Pn, 4),
      (paZ Pi, 4)] →
    -- P1: push_off's reload GATES (mycpu's three returns, its ra / s1 reloads; against the
    -- spilled bytes: the `jal` links and the lock in s1), and its arm (Q20')
    AxSpinT2i.Gate GT i (k + 3 + 5) (stBytes 8 (AxSpinPO.ppo 0x14)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 3 + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    (b = true → AxSpinT2i.Gate GT i (k + 3 + 10) (stBytes 8 (AxSpinPO.ppo 0x30))) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 2) (stBytes 8 (AxSpinPO.ppo 0x1c)) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 6) (stBytes 8 (AxSpinHdB.pac 0x10)) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 8)
      (stBytes 8 (gprVal rs0 AxSpinE8.r10)) →
    -- the row-end hook (stage 2; windowed, resource-free; no designated cut in this window)
    (∀ k' : Nat, k ≤ k' → k' ≤ aqKp k b → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
      ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (vn : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜(∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k + 3 + 8 + (if b then 5 else 0) + 5]? =
            some (.LStore false (paZ Pn) (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) cls)) ∧
          (b = true → ∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k + 3 + 12]? =
            some (.LStore false (paZ Pi) (stBytes 4 0#64) cls)) ∧
          graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 4) = some vn ∧
          ctrlOkSW T satp0 rs' ∧ rs' .PC = pch 0 ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs' AxSpinE8.r1 = AxSpinHdB.pac 0x16 ∧
          gprVal rs' AxSpinE8.r10 = gprVal rs0 AxSpinE8.r10 ∧
          gprVal rs' 9#5 = gprVal rs0 AxSpinE8.r10 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 9#5))⌝ -∗
        (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) (k + 3 + 7) (paZ Pn) 4,
          AxAnnot.annotOwn (GF := GF) (i, k + 3 + 7)
            iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 3 + 7)⌝)) -∗
        (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i)
            (k + 3 + 8 + (if b then 5 else 0) + 4) (paZ Pn) 4,
          AxAnnot.annotOwn (GF := GF) (i, k + 3 + 8 + (if b then 5 else 0) + 4)
            iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 3 + 8 + (if b then 5 else 0) + 4)⌝)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', aqKp k b⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HRh HRp Hw8 Hq1 Hq2 Hq3 Hq4 Hq5 Hwn Hnn Hwi Hc0 HPC0 Hhit0 HhitM
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Hdj V14 Vb V30 V1c Vret Vs1 HΨend
  obtain ⟨HdaS_ra, _, Hh_ra, Hpr_ra, _⟩ := Bra
  obtain ⟨HdaS_s0, _, Hh_s0, Hpr_s0, _⟩ := Bs0
  obtain ⟨HdaS_s1, _, Hh_s1, Hpr_s1, _⟩ := Bs1
  obtain ⟨T00, T02, T04, T06, T08, T0a, T0c, T10, T12, -⟩ := Htxa
  have Hkp : k + 20 ≤ aqKp k b := by unfold aqKp; split <;> omega
  have Etk : k + 3 + 8 + (if b then 5 else 0) + 9 = aqKp k b := by unfold aqKp; split <;> omega
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS := XxSt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  iintro C
  -- row end at k
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k
  · iclear C
    iapply (HΨend _ (Nat.le_refl _) (by omega) E0 _)
  -- ---- + 0x00: c.addi sp,-32 (row position k) ----
  iapply (XR _ rs0 k (AxSpinHdB.pac 0x00) true q00 none
    (some (2#5, spo (gprVal rs0 AxSpinE8.r2)))
    (retxRefl cpu rs0 k ib0) Hc0 HPC0 Hhit0
    (tw1101 σi T satp0 _ T00) (AxSpinE8.owOkSome 2#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _))
    (certAddi _ rs0 (AxSpinHdB.pac 0x00) true 2#5 2#5 _ (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = AxSpinHdB.pac 0x02 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  have Esp1 : gprVal rs1 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF1]; ax_spin_aq2_zsimp
  -- ---- + 0x02: c.sdsp ra,24(sp) (spill at k) ----
  iapply (XS _ rs1 k (AxSpinHdB.pac 0x02) true AxSpinPO3.imm24 1#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra
    (retxRefl cpu rs1 k ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (AxSpinHdB.pac 0x02) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs1 _ Htl1 Hhit0))
    (twEc06 σi T satp0 _ T02) (by rw [Esp1]) HdaS_ra
    (hitWAgree rs0 rs1 _ Htl1 Hh_ra) Hpr_ra Hw8 (by omega))
  iintro %rs2 %ib2 %HG2 %Hgd0
  have HF2 := stepRegs0 T satp0 _ rs1 _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = AxSpinHdB.pac 0x04 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  have Esp2 : gprVal rs2 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF2]; ax_spin_aq2_zsimp
  -- row end at k + 1
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1
  · iclear C
    iapply (HΨend _ (by omega) (by omega) E1 _)
  -- ---- + 0x04: c.sdsp s0,16(sp) (spill at k+1) ----
  iapply (XS _ rs2 (k + 1) (AxSpinHdB.pac 0x04) true AxSpinPO3.imm16 8#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0
    (retxRefl cpu rs2 (k + 1) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (AxSpinHdB.pac 0x04) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (twE822 σi T satp0 _ T04) (by rw [Esp2]) HdaS_s0
    (hitWAgree rs0 rs2 _ Htl2 Hh_s0) Hpr_s0 Hw8 (by omega))
  iintro %rs3 %ib3 %HG3 %Hgd1
  have HF3 := stepRegs0 T satp0 _ rs2 _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = AxSpinHdB.pac 0x06 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  have Esp3 : gprVal rs3 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF3]; ax_spin_aq2_zsimp
  -- row end at k + 2
  by_cases E2 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 2
  · iclear C
    iapply (HΨend _ (by omega) (by omega) E2 _)
  -- ---- + 0x06: c.sdsp s1,8(sp) (spill at k+2) ----
  iapply (XS _ rs3 (k + 2) (AxSpinHdB.pac 0x06) true AxSpinPO3.imm8 9#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1
    (retxRefl cpu rs3 (k + 2) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (AxSpinHdB.pac 0x06) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (twE426 σi T satp0 _ T06) (by rw [Esp3]) HdaS_s1
    (hitWAgree rs0 rs3 _ Htl3 Hh_s1) Hpr_s1 Hw8 (by omega))
  iintro %rs4 %ib4 %HG4 %Hgd2
  have HF4 := stepRegs0 T satp0 _ rs3 _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = AxSpinHdB.pac 0x08 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- row end at k + 3
  by_cases E3 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 3
  · iclear C
    iapply (HΨend _ (by omega) (by omega) E3 _)
  -- ---- + 0x08: c.addi4spn s0,sp,32 (k+3) ----
  have Hc5 := certAddi (ctrlOkSW T satp0) rs4 (AxSpinHdB.pac 0x08) true 2#5 8#5
    (caddi4spnImm 8#8) (by decide)
  simp only [HF4] at Hc5
  ax_spin_aq2_zsimp at Hc5
  iapply (XR _ rs4 (k + 3) (AxSpinHdB.pac 0x08) true q08 _ _
    (retxRefl cpu rs4 (k + 3) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (AxSpinHdB.pac 0x08) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs4 _ Htl4 Hhit0))
    (tw1000 σi T satp0 _ T08) (AxSpinE8.owOkSome 8#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _)) Hc5 (by omega))
  iintro %rs5 %ib5 %HG5
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = AxSpinHdB.pac 0x0a := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- + 0x0a: c.mv s1,a0 (k+3) ----
  have Hc6 := certAdd (ctrlOkSW T satp0) rs5 (AxSpinHdB.pac 0x0a) true 10#5 0#5 9#5 (by decide)
  simp only [HF5] at Hc6
  ax_spin_aq2_zsimp at Hc6
  iapply (XR _ rs5 (k + 3) (AxSpinHdB.pac 0x0a) true a0a _ _
    (retxRefl cpu rs5 (k + 3) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (AxSpinHdB.pac 0x0a) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs5 _ Htl5 Hhit0))
    (twa84aa σi T satp0 _ T0a) (AxSpinE8.owOkSome 9#5 _ (by decide))
    (rfFOfRf0 _ (rf0Add _ _ _)) Hc6 (by omega))
  iintro %rs6 %ib6 %HG6
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = AxSpinHdB.pac 0x0c := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- ---- + 0x0c: jal ra,push_off (k+3) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs6 (AxSpinHdB.pac 0x0c) false a0c (some (AxSpinPO.ppo 0))
      (some (1#5, BitVec.addInt (AxSpinHdB.pac 0x0c) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs6 (AxSpinHdB.pac 0x0c)
      false 2097082#21 1#5 (by decide)
    rw [show AxSpinHdB.pac 0x0c + sign_extend (m := 64) 2097082#21 = AxSpinPO.ppo 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (AxSpinHdB.pac 0x0c) (incr false)) =
      some (1#5, BitVec.addInt (AxSpinHdB.pac 0x0c) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs6 (k + 3) (AxSpinHdB.pac 0x0c) false a0c (some (AxSpinPO.ppo 0))
    (some (1#5, BitVec.addInt (AxSpinHdB.pac 0x0c) (incr false)))
    (retxRefl cpu rs6 (k + 3) ib6) (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (AxSpinHdB.pac 0x0c) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs6 _ Htl6 Hhit0))
    (tw4A0c σi T satp0 _ T0c) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 2097082#21 (.Regidx 1#5)) Hcj (by omega))
  iintro %rs7 %ib7 %HG7
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = AxSpinPO.ppo 0 := gbPc T satp0 _ _ _ _ _ _ HG7
  have Htl7 : rs7 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  have Esp7 : gprVal rs7 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF7]; ax_spin_aq2_zsimp
  have Etp7 : gprVal rs7 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 := by
    rw [HF7]; ax_spin_aq2_zsimp
  -- push_off's entry ra / s1: the `jal` link and the lock (`c.mv s1,a0`)
  have Era7 : gprVal rs7 AxSpinE8.r1 = AxSpinHdB.pac 0x10 := by
    rw [HF7]; ax_spin_aq2_zsimp; decide
  have Es17 : gprVal rs7 AxSpinPOr.r9 = gprVal rs0 AxSpinE8.r10 := by
    show gprVal rs7 9#5 = gprVal rs0 10#5
    rw [HF7]; ax_spin_aq2_zsimp
    exact BitVec.zero_add _
  -- ---- push_off, at k+3 (continuation at aqKp; P1 gate form) ----
  have WPo := wpdPushOffG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxp Ψ
    HΨmid (k + 3) b rs7 ib7 Qra Qs0 Qs1 Qmra Qms0 Pn Pi HRp Hw8
    Hq1 Hq2 Hq3 Hq4 Hq5 Hwn Hnn Hwi
    (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (AxSpinPO.ppo 0) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs7 _ Htl7 Hhit0))
    (hitWAgree rs0 rs7 _ Htl7 HhitM)
    (by rw [Esp7]; exact slot8Tlb _ _ _ _ _ _ _ _ Htl7 Bqra)
    (by rw [Esp7]; exact slot8Tlb _ _ _ _ _ _ _ _ Htl7 Bqs0)
    (by rw [Esp7]; exact slot8Tlb _ _ _ _ _ _ _ _ Htl7 Bqs1)
    (by rw [Esp7]; exact slot8Tlb _ _ _ _ _ _ _ _ Htl7 Bqmra)
    (by rw [Esp7]; exact slot8Tlb _ _ _ _ _ _ _ _ Htl7 Bqms0)
    (by rw [Etp7]; exact fld4Tlb _ _ _ _ _ _ _ _ Htl7 Bn)
    (by rw [Etp7]; exact fld4Tlb _ _ _ _ _ _ _ _ Htl7 Bi)
    Hdj V14 Vb V30 V1c (by rw [Era7]; exact Vret) (by rw [Es17]; exact Vs1)
    (by rw [Era7]; decide)
    (fun k' h1 h2 h3 => HΨend k' (by omega) (by omega) h3)
  rw [Etk] at WPo
  iapply WPo
  iintro %vn0 %vn %vra' %vs0' %vs1' %rs8 %ib8 %Hp - - - G1 G2
  obtain ⟨⟨-, -, -, Es18⟩, Hlbn, Hlbi, Hc8, HPC8, Htl8', -, Esp8, -, -, -, -, Hkeep8, -, -, -, -,
    -, -, Hgvn, -, -, -, -⟩ := Hp
  rw [Era7] at HPC8
  have Htl8 : rs8 .tlb = rs0 .tlb := Htl8'.trans Htl7
  have Es1 : gprVal rs8 9#5 = gprVal rs0 AxSpinE8.r10 := Es18.trans Es17
  -- row end at aqKp
  by_cases E4 : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKp k b
  · iclear C
    iclear G1
    iclear G2
    iapply (HΨend _ (by omega) (Nat.le_refl _) E4 _)
  -- ---- + 0x10: c.mv a0,s1 (aqKp) ----
  have Hc9 := certAdd (ctrlOkSW T satp0) rs8 (AxSpinHdB.pac 0x10) true 9#5 0#5 10#5 (by decide)
  iapply (XR _ rs8 (aqKp k b) (AxSpinHdB.pac 0x10) true a10 _ _
    (retxRefl cpu rs8 (aqKp k b) ib8) Hc8 HPC8
    (hitWSvpn rs8 (AxSpinHdB.pac 0x10) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs8 _ Htl8 Hhit0))
    (twa8526 σi T satp0 _ T10) (AxSpinE8.owOkSome 10#5 _ (by decide))
    (rfFOfRf0 _ (rf0Add _ _ _)) Hc9 (by omega))
  iintro %rs9 %ib9 %HG9
  have HF9 := stepRegs T satp0 _ rs8 _ _ _ _ _ rs9 (fun _ => rfl) HG9
  have HPC9 : rs9 .PC = AxSpinHdB.pac 0x12 := by rw [gbPc T satp0 _ _ _ _ _ _ HG9]; decide
  have Htl9 : rs9 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG9).trans Htl8
  -- ---- + 0x12: jal ra,holding (aqKp) ----
  have Hcj2 : CertC (ctrlOkSW T satp0) rs9 (AxSpinHdB.pac 0x12) false a12 (some (pch 0))
      (some (1#5, BitVec.addInt (AxSpinHdB.pac 0x12) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs9 (AxSpinHdB.pac 0x12)
      false 2097032#21 1#5 (by decide)
    rw [show AxSpinHdB.pac 0x12 + sign_extend (m := 64) 2097032#21 = pch 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (AxSpinHdB.pac 0x12) (incr false)) =
      some (1#5, BitVec.addInt (AxSpinHdB.pac 0x12) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs9 (aqKp k b) (AxSpinHdB.pac 0x12) false a12 (some (pch 0))
    (some (1#5, BitVec.addInt (AxSpinHdB.pac 0x12) (incr false)))
    (retxRefl cpu rs9 (aqKp k b) ib9) (gbCtrl T satp0 _ _ _ _ _ _ HG9) HPC9
    (hitWSvpn rs9 (AxSpinHdB.pac 0x12) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs9 _ Htl9 Hhit0))
    (tw4A12 σi T satp0 _ T12) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 2097032#21 (.Regidx 1#5)) Hcj2 (by omega))
  iintro %rs10 %ib10 %HG10
  have HF10 := stepRegs T satp0 _ rs9 _ _ _ _ _ rs10 HF9 HG10
  iapply C $$ %vn %rs10 %ib10 [] G1 G2
  ipureintro
  refine ⟨Hlbn, Hlbi, Hgvn, gbCtrl T satp0 _ _ _ _ _ _ HG10, gbPc T satp0 _ _ _ _ _ _ HG10,
    (gbTlb T satp0 _ _ _ _ _ _ HG10).trans Htl9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- sp
    rw [HF10]
    ax_spin_aq2_zsimp
    exact Esp8.trans Esp7
  · -- ra = the link
    rw [HF10]
    ax_spin_aq2_zsimp
    decide
  · -- a0 = s1 = the lock
    rw [HF10]
    ax_spin_aq2_zsimp
    rw [AxSpinE8.gprValZero rs8 0#5 rfl, BitVec.zero_add, Es1]
  · -- s1
    rw [HF10]
    ax_spin_aq2_zsimp
    exact Es1
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    rw [HF10]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n9 : r ≠ 9#5 := fun h => Hr9 (by rw [h]; rfl)
      have n10 : r ≠ 10#5 := fun h => Hr10 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
      rw [Hkeep8 r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15, HF7]
      simp (disch := assumption) only [AxSpinE8.updOther]
  · rw [Hgd0, HF1]
    ax_spin_aq2_zsimp
  · rw [Hgd1, HF2]
    ax_spin_aq2_zsimp
  · rw [Hgd2, HF3]
    ax_spin_aq2_zsimp

include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxp HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `AxSpinAq2.head` on a PREFIX row (`RowShP` windows, pins
guarded by position): a `by_cases` on `LEN ≤ position` at `k`, `k + 1`, `k + 2`, `k + 3` and
`aqKp k b`; push_off is `wpdPushOffP` with the sub-window `[k + 3, aqKp]`; the row-end case is
the WINDOWED, RESOURCE-FREE hook over `[k, aqKp]`.  The continuation additionally receives
push_off's two store labels, its second noff read's value, and its two CONDITIONAL genesis
annotations (passed on).  P1: the corollary of `AxSpinAq2.headG` via `AxSpinT2i.gateOfPinG`. -/
theorem AxSpinAq2.headP (k : Nat) (b : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi : BitVec 64) :
    -- the row
    RowShP k (AxOpsem.grow (gtAdGd GT) i) (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) →
    RowShP (k + 3) (AxOpsem.grow (gtAdGd GT) i)
      (poSh b (paZ Qra) (paZ Qs0) (paZ Qs1) (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi)) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0 → hitW rs0 (AxSpinHdB.pac 0) →
    hitW rs0 (pcm 0) →
    -- acquire's slots
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    -- push_off's slots and cpu fields
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm24) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm16) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm8) Qs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qs1, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Pn, 4),
      (paZ Pi, 4)] →
    -- the value pins (push_off's, at `k + 3`; + its s1 reload), GUARDED by position
    (k + 3 + 5 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14))) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 3 + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    (b = true → k + 3 + 10 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30))) →
    (k + 3 + 8 + (if b then 5 else 0) + 2 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 2) =
        some (stBytes 8 (AxSpinPO.ppo 0x1c))) →
    (k + 3 + 8 + (if b then 5 else 0) + 6 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 6) =
        some (stBytes 8 (AxSpinHdB.pac 0x10))) →
    (k + 3 + 8 + (if b then 5 else 0) + 8 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 8) =
        some (stBytes 8 (gprVal rs0 AxSpinE8.r10))) →
    -- the row-end hook (stage 2; windowed, resource-free; no designated cut in this window)
    (∀ k' : Nat, k ≤ k' → k' ≤ aqKp k b → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
      ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (vn : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜(∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k + 3 + 8 + (if b then 5 else 0) + 5]? =
            some (.LStore false (paZ Pn) (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) cls)) ∧
          (b = true → ∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k + 3 + 12]? =
            some (.LStore false (paZ Pi) (stBytes 4 0#64) cls)) ∧
          graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 4) = some vn ∧
          ctrlOkSW T satp0 rs' ∧ rs' .PC = pch 0 ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs' AxSpinE8.r1 = AxSpinHdB.pac 0x16 ∧
          gprVal rs' AxSpinE8.r10 = gprVal rs0 AxSpinE8.r10 ∧
          gprVal rs' 9#5 = gprVal rs0 AxSpinE8.r10 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 9#5))⌝ -∗
        (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) (k + 3 + 7) (paZ Pn) 4,
          AxAnnot.annotOwn (GF := GF) (i, k + 3 + 7)
            iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 3 + 7)⌝)) -∗
        (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i)
            (k + 3 + 8 + (if b then 5 else 0) + 4) (paZ Pn) 4,
          AxAnnot.annotOwn (GF := GF) (i, k + 3 + 8 + (if b then 5 else 0) + 4)
            iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 3 + 8 + (if b then 5 else 0) + 4)⌝)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', aqKp k b⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HRh HRp Hw8 Hq1 Hq2 Hq3 Hq4 Hq5 Hwn Hnn Hwi Hc0 HPC0 Hhit0 HhitM
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Hdj V14 Vb V30 V1c Vret Vs1 HΨend
  exact AxSpinAq2.headG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxp Ψ
    HΨmid k b rs0 ib0 Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi HRh HRp Hw8 Hq1 Hq2 Hq3 Hq4 Hq5
    Hwn Hnn Hwi Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Hdj
    (AxSpinT2i.gateOfPinG V14) Vb (fun h => AxSpinT2i.gateOfPinG (V30 h))
    (AxSpinT2i.gateOfPinG V1c) (AxSpinT2i.gateOfPinG Vret) (AxSpinT2i.gateOfPinG Vs1) HΨend

include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxp HΨmid in
/-- acquire + 0x00 … + 0x12: the prologue, `push_off`, `c.mv a0,s1`, `jal holding`; continuation
at holding's entry (boundary `aqKp k b`).  Stage 2: the full-row corollary of
`AxSpinAq2.headP`. -/
theorem AxSpinAq2.head (k : Nat) (b : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi : BitVec 64) :
    -- the row
    RowSh k (AxOpsem.grow (gtAdGd GT) i) (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) →
    RowSh (k + 3) (AxOpsem.grow (gtAdGd GT) i)
      (poSh b (paZ Qra) (paZ Qs0) (paZ Qs1) (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi)) →
    aqKp k b < (AxOpsem.grow (gtAdGd GT) i).length →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0 → hitW rs0 (AxSpinHdB.pac 0) →
    hitW rs0 (pcm 0) →
    -- acquire's slots
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    -- push_off's slots and cpu fields
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm24) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm16) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm8) Qs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qs1, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Pn, 4),
      (paZ Pi, 4)] →
    -- the value pins (push_off's, at `k + 3`; + its s1 reload)
    graphValue (gtAdGd GT) (i, k + 3 + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 3 + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    (b = true → graphValue (gtAdGd GT) (i, k + 3 + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30))) →
    graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 2) =
      some (stBytes 8 (AxSpinPO.ppo 0x1c)) →
    graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 6) =
      some (stBytes 8 (AxSpinHdB.pac 0x10)) →
    graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 8) =
      some (stBytes 8 (gprVal rs0 AxSpinE8.r10)) →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = pch 0 ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs' AxSpinE8.r1 = AxSpinHdB.pac 0x16 ∧
          gprVal rs' AxSpinE8.r10 = gprVal rs0 AxSpinE8.r10 ∧
          gprVal rs' 9#5 = gprVal rs0 AxSpinE8.r10 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 9#5))⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', aqKp k b⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HRh HRp Hlen Hw8 Hq1 Hq2 Hq3 Hq4 Hq5 Hwn Hnn Hwi Hc0 HPC0 Hhit0 HhitM
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Hdj V14 Vb V30 V1c Vret Vs1
  iintro C
  iapply (AxSpinAq2.headP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxp Ψ
    HΨmid k b rs0 ib0 Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi (rowShPOfSh HRh) (rowShPOfSh HRp)
    Hw8 Hq1 Hq2 Hq3 Hq4 Hq5 Hwn Hnn Hwi Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0
    Bn Bi Hdj (fun _ => V14) Vb (fun h _ => V30 h) (fun _ => V1c) (fun _ => Vret) (fun _ => Vs1)
    (fun _ _ h2 h3 => absurd h3 (by omega)))
  iintro %vn %rs' %ib' %Hp - -
  iapply C $$ %rs' %ib'
  ipureintro
  exact Hp.2.2.2


set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxa HΨmid in
/-- acquire + 0x16 / + 0x18: `c.li a4,1; c.bnez a0,panic` with `a0 = 0` — the branch falls
through to the spin loop at + 0x1a (register-only, both at boundary `u`). -/
theorem AxSpinAq2.liBnez (u : Nat) (rs1 : RegFile) (ib1 : Ibch) :
    ctrlOkSW T satp0 rs1 → rs1 .PC = AxSpinHdB.pac 0x16 → hitW rs1 (AxSpinHdB.pac 0) →
    gprVal rs1 AxSpinE8.r10 = 0#64 → u < (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (rs2 : RegFile) (ib2 : Ibch),
        ⌜ctrlOkSW T satp0 rs2 ∧ rs2 .PC = AxSpinHdB.pac 0x1a ∧ rs2 .tlb = rs1 .tlb ∧
          (∀ r : BitVec 5, r.toNat ≠ 14 → gprVal rs2 r = gprVal rs1 r)⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs2 none ib2, u⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs1 none ib1, u⟩ Ψ := by
  intro Hc HPC Hhit Ea0 Hlen
  have T16 := Htxa.2.2.2.2.2.2.2.2.2.1
  have T18 := Htxa.2.2.2.2.2.2.2.2.2.2.1
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  iintro C
  -- ---- + 0x16: c.li a4,1 ----
  iapply (XR _ rs1 u (AxSpinHdB.pac 0x16) true a16 none _
    (retxRefl cpu rs1 u ib1) Hc HPC
    (hitWSvpn rs1 (AxSpinHdB.pac 0x16) (AxSpinHdB.pac 0) (by decide) Hhit)
    (twa4705 σi T satp0 _ T16) (AxSpinE8.owOkSome 14#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _))
    (certAddi _ rs1 (AxSpinHdB.pac 0x16) true 0#5 14#5 _ (by decide)) Hlen)
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 (fun _ => rfl) HG2
  have HPC2 : rs2 .PC = AxSpinHdB.pac 0x18 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs1 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG2
  -- ---- + 0x18: c.bnez a0,panic — a0 = 0: not taken ----
  have Hcb := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs2
    (AxSpinHdB.pac 0x18) true AxSpinAq2.imm18 0#5 AxSpinAq2.c2 .BNE (by decide)
  have Hg : gval AxSpinAq2.c2 rs2 = 0#64 := by
    rw [show AxSpinAq2.c2 = 10#5 by decide]
    unfold gval
    rw [if_neg (by decide)]
    show gprVal rs2 10#5 = _
    rw [HF2]
    ax_spin_aq2_zsimp
    exact Ea0
  have Hg0 : gval 0#5 rs2 = 0#64 := by
    unfold gval
    rw [if_pos (by decide)]
    rfl
  have Eot : brOt .BNE AxSpinAq2.c2 0#5 rs2
      (AxSpinHdB.pac 0x18 + sign_extend (m := 64) AxSpinAq2.imm18) = none := by
    unfold brOt AxSymCtl2.bcond
    rw [Hg, Hg0]
    rfl
  rw [Eot] at Hcb
  iapply (XR _ rs2 u (AxSpinHdB.pac 0x18) true a18 none none
    (retxRefl cpu rs2 u ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (AxSpinHdB.pac 0x18) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs1 rs2 _ Htl2 Hhit))
    (twaEd11 σi T satp0 _ T18) trivial (AxSpinAp6.rfFBtype _ _ _ _) Hcb Hlen)
  iintro %rs3 %ib3 %HG3
  have HF3 := stepRegs0 T satp0 _ rs2 _ _ _ rs3 HF2 HG3
  iapply C $$ %rs3 %ib3
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HG3, ?_, (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2,
    fun r hr => ?_⟩
  · rw [gbPc T satp0 _ _ _ _ _ _ HG3]
    decide
  · rw [HF3]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs1 r E0]
    · have n14 : r ≠ 14#5 := fun h => hr (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxh HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `AxSpinAq2.mid` on a PREFIX row (`RowHoldingP`; pins
guarded by position): `holdingFromAcquireP` (sub-window `[aqKp, aqKp (+ 11)]`) and, in each arm's
continuation, a `by_cases` at `aqKh`.  Row ends: the windowed resource-free hook over
`[aqKp, if hb then aqKp + 11 else aqKp + 1]` (short arm: `KShort`'s and `KShortEnd`'s end at
`aqKp + 1` — not a cut for acquire); the long arm's end at `aqKp + 12` — THE DESIGNATED CUT
`aq` — is NOT the hook: it is the premise `Kaq` (resource-carrying: holding's `KLongEnd` with
the `lk->cpu` read's `ORacy` deposit), used both for holding's end continuation and for a
`KLong` continuation reached on a row of length `aqKp + 12`.  The non-panic arm pin is guarded
by `aqKp + 12 < LEN` (a row continuing past the cut took the normal arm).  The continuation also
receives `aqKh < (AxOpsem.grow (gtAdGd GT) i).length`.

(Lean-only, P1) THE GATE FORM / shared proof: holding is `holdingFromAcquireG` (its return is the
entry ra `acquire + 0x16`, `Era`), the long arm's three reload pins replaced by its
`AxSpinT2i.Gate`s (against `pch 0x1a`, `acquire + 0x16`, the lock `lkv` in s1); the long main
continuation is `KLongG` (reached only past the cut, `aqKp + 12 < LEN`, with the reload values in
hand), so `Kaq` is used once, as `KLongEnd`.  `AxSpinAq2.midP` = this ∘ `AxSpinT2i.gateOfPinG`. -/
theorem AxSpinAq2.midG (k : Nat) (b hb : Bool) (rsH : RegFile) (ibH : Ibch) (lkv tp : BitVec 64)
    (Hra Hs0 Hs1 Hram Hs0m Pcl Plk : BitVec 64) :
    RowHoldingP (aqKp k b) (AxOpsem.grow (gtAdGd GT) i) hb L.xlLk (L.xlLk + 16) (paZ Hra)
      (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0m) →
    ctrlOkSW T satp0 rsH → rsH .PC = pch 0 → hitW rsH (AxSpinHdB.pac 0) → hitW rsH (pcm 0) →
    gprVal rsH AxSpinE8.r10 = lkv → gprVal rsH 9#5 = lkv →
    gprVal rsH AxSpinE8.r1 = AxSpinHdB.pac 0x16 → gprVal rsH AxSpinE8.r4 = tp →
    hitW rsH lkv → hitW rsH (lkv + sign_extend (m := 64) (16#12)) →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rsH
      (AxSpinE8.sp1Of (spo (gprVal rsH AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Hram →
    AxSpinPO1.slot8 σi T L i rsH
      (AxSpinE8.sp1Of (spo (gprVal rsH AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    dataAtS σi T (.Load .Data) (lkv + sign_extend (m := 64) (16#12)) 8 Pcl →
    ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    dataAtS σi T (.Load .Data) lkv 4 Plk → ¬ L.xlText (paZ Plk) →
    -- P1: holding's long-arm reload GATES (mycpu's ra, holding's ra, holding's s1); the
    -- non-panic arm (GUARDED by the cut)
    (hb = true →
      AxSpinT2i.Gate GT i (aqKp k b + 7) (stBytes 8 (pch 0x1a)) ∧
      AxSpinT2i.Gate GT i (aqKp k b + 9) (stBytes 8 (AxSpinHdB.pac 0x16)) ∧
      AxSpinT2i.Gate GT i (aqKp k b + 11) (stBytes 8 lkv) ∧
      (aqKp k b + 12 < (AxOpsem.grow (gtAdGd GT) i).length →
        ∀ vcpu, graphValue (gtAdGd GT) (i, aqKp k b + 4) = some vcpu →
        hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet tp) = 0#64)) →
    -- the designated cut `aq` (long arm, row length `aqKp + 12`): the caller's arm
    (hb = true →
      ⊢ KLongEnd (hlc := hlc) L GT nm i Ψ (aqKp k b) rsH Hra Hs0 Hs1 Hram Hs0m
          (fun _ => iprop(True)) (ORacy L GT i (aqKp k b + 4))) →
    -- the row-end hook (windowed, resource-free; misses the cut `aqKp + 12`)
    (∀ k' : Nat, aqKp k b ≤ k' → k' ≤ (if hb then aqKp k b + 11 else aqKp k b + 1) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜aqKh k b hb < (AxOpsem.grow (gtAdGd GT) i).length ∧
          ctrlOkSW T satp0 rs' ∧ rs' .PC = AxSpinHdB.pac 0x1a ∧ rs' .tlb = rsH .tlb ∧
          gprVal rs' AxSpinE8.r2 = gprVal rsH AxSpinE8.r2 ∧ gprVal rs' 9#5 = lkv ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 14 → r.toNat ≠ 15 → gprVal rs' r = gprVal rsH r)⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', aqKh k b hb⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsH none ibH, aqKp k b⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc HPC Hhit HhitM Ea0 Es1 Era Etp Hhlk Hhcl
    Bra Bs0 Bs1 Bram Bs0m Hdisj Hdcl Hntcl Hnrcl Hdlk Hntlk Vp Kaq HΨend
  obtain ⟨Hd1, Hd2, Hd3, Hp1, Hn1⟩ := Bra
  obtain ⟨Hd4, Hd5, Hd6, Hp2, Hn2⟩ := Bs0
  obtain ⟨Hd7, Hd8, Hd9, Hp3, Hn3⟩ := Bs1
  obtain ⟨Hd10, Hd11, Hd12, Hp4, Hn4⟩ := Bram
  obtain ⟨Hd13, Hd14, Hd15, Hp5, Hn5⟩ := Bs0m
  have Es1H : gprVal rsH AxSpinHd8.r9 = lkv := Es1
  have W := holdingFromAcquireG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm
    Htxh Ψ HΨmid (aqKp k b) rsH ibH hb L.xlLk (L.xlLk + 16) Hra Hs0 Hs1 Hram Hs0m Pcl Plk HR Hw8
    H1 H2 H3 H4 H5 Hc HPC
    (hitWSvpn rsH (pch 0) (AxSpinHdB.pac 0) (by decide) Hhit) HhitM
    (by rw [Ea0, AxSpinAq2.addZ]; exact Hhlk) (by rw [Ea0]; exact Hhcl)
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
    (fun h => ⟨(Vp h).1, by rw [Era]; exact (Vp h).2.1, by rw [Es1H]; exact (Vp h).2.2.1⟩)
    (by rw [Era]; decide)
    (by rw [Ea0]; exact Hdcl) Hntcl Hnrcl (by rw [Ea0, AxSpinAq2.addZ]; exact Hdlk) Hntlk
    (fun k' h1 h2 h3 => HΨend k' h1 (AxSpinAq2.winMono hb _ _ h2) h3)
  have LB := AxSpinAq2.liBnez L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Ψ HΨmid
  iintro C
  cases hb with
  | true =>
    simp only [↓reduceIte] at W
    obtain ⟨-, -, -, Vcpu⟩ := Vp rfl
    iapply W
    isplit
    · -- the long main continuation: past the cut (`aqKp + 12 < LEN`), the reloads read the spills
      unfold KLongG
      iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %rs1 %ib1 %Hg %Hf Holk Hocpu H7 H8 H9 H10 H11
      obtain ⟨Hlt, -, -, Hvs1⟩ := Hg
      obtain ⟨Hc1, HPC1, Htl1, Ea01, Esp1, -, -, -, -, -, -, -, -, -, Es11, Hkeep1, -, Hgv4,
        -, -, -, -, -, -, -, -, -, -⟩ := Hf
      rw [Era] at HPC1
      iclear Holk
      iclear Hocpu
      iclear H7
      iclear H8
      iclear H9
      iclear H10
      iclear H11
      have Hlen : aqKh k b true < (AxOpsem.grow (gtAdGd GT) i).length := Hlt
      have Ea0' : gprVal rs1 AxSpinE8.r10 = 0#64 := by
        rw [Ea01, Etp]; exact Vcpu Hlt vcpu Hgv4
      have Es1' : gprVal rs1 9#5 = lkv := by
        rw [show (9#5 : BitVec 5) = AxSpinHd8.r9 from rfl, Es11, Hvs1, AxSpinE8.ldResStBytes8]
        exact Es1H
      rw [show aqKp k b + 12 = aqKh k b true from rfl]
      iapply (LB (aqKh k b true) rs1 ib1 Hc1 HPC1 (hitWAgree rsH rs1 _ Htl1 Hhit) Ea0' Hlen)
      iintro %rs2 %ib2 %H2
      obtain ⟨Hc2, HPC2, Htl2, Hk2⟩ := H2
      iapply C $$ %rs2 %ib2
      ipureintro
      refine ⟨Hlen, Hc2, HPC2, Htl2.trans Htl1, ?_, ?_, ?_⟩
      · rw [Hk2 2#5 (by decide)]; exact Esp1
      · rw [Hk2 9#5 (by decide)]; exact Es1'
      · intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr14 Hr15
        rw [Hk2 r Hr14]
        exact Hkeep1 r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    · -- holding's long-arm END continuation (row length `aqKp + 12`): the cut `aq`
      iclear C
      have KE0 := Kaq rfl
      ihave K0 := KE0
      iexact K0
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at W
    iapply W
    isplit
    · unfold KShort
      iintro %vlk %rs1 %ib1 %Hf -
      obtain ⟨Hc1, HPC1, Htl1, Ea01, -, -, -, Hkeep1⟩ := Hf
      rw [Era] at HPC1
      -- row end at aqKp + 1 (not a cut for acquire): the hook
      by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKp k b + 1
      · iclear C
        iapply (HΨend _ (by omega) (by simp) E1 _)
      have Hlen : aqKh k b false < (AxOpsem.grow (gtAdGd GT) i).length := by
        show aqKp k b + 1 < _
        omega
      rw [show aqKp k b + 1 = aqKh k b false from rfl]
      iapply (LB (aqKh k b false) rs1 ib1 Hc1 HPC1 (hitWAgree rsH rs1 _ Htl1 Hhit) Ea01 Hlen)
      iintro %rs2 %ib2 %H2
      obtain ⟨Hc2, HPC2, Htl2, Hk2⟩ := H2
      iapply C $$ %rs2 %ib2
      ipureintro
      refine ⟨Hlen, Hc2, HPC2, Htl2.trans Htl1, ?_, ?_, ?_⟩
      · rw [Hk2 2#5 (by decide)]; exact Hkeep1 2#5 (by decide) (by decide)
      · rw [Hk2 9#5 (by decide), Hkeep1 9#5 (by decide) (by decide)]; exact Es1
      · intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr14 Hr15
        rw [Hk2 r Hr14]
        exact Hkeep1 r Hr10 Hr15
    · -- holding's short-arm END continuation (row length `aqKp + 1`): not a cut for acquire
      unfold KShortEnd
      iintro %vlk %pr %Hp -
      iclear C
      have Hl1 := Hp.1
      iapply (HΨend _ (by omega) (by simp) (by omega) pr)


include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxh HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `AxSpinAq2.mid` on a PREFIX row (`RowHoldingP`; pins
guarded by position): `holdingFromAcquireP` (sub-window `[aqKp, aqKp (+ 11)]`) and, in each arm's
continuation, a `by_cases` at `aqKh`.  Row ends: the windowed resource-free hook over
`[aqKp, if hb then aqKp + 11 else aqKp + 1]` (short arm: `KShort`'s and `KShortEnd`'s end at
`aqKp + 1` — not a cut for acquire); the long arm's end at `aqKp + 12` — THE DESIGNATED CUT
`aq` — is NOT the hook: it is the premise `Kaq` (resource-carrying: holding's `KLongEnd` with
the `lk->cpu` read's `ORacy` deposit), used both for holding's end continuation and for a
`KLong` continuation reached on a row of length `aqKp + 12`.  The non-panic arm pin is guarded
by `aqKp + 12 < LEN` (a row continuing past the cut took the normal arm).  The continuation also
receives `aqKh < (AxOpsem.grow (gtAdGd GT) i).length`.  P1: the corollary of
`AxSpinAq2.midG` via `AxSpinT2i.gateOfPinG`. -/
theorem AxSpinAq2.midP (k : Nat) (b hb : Bool) (rsH : RegFile) (ibH : Ibch) (lkv tp : BitVec 64)
    (Hra Hs0 Hs1 Hram Hs0m Pcl Plk : BitVec 64) :
    RowHoldingP (aqKp k b) (AxOpsem.grow (gtAdGd GT) i) hb L.xlLk (L.xlLk + 16) (paZ Hra)
      (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0m) →
    ctrlOkSW T satp0 rsH → rsH .PC = pch 0 → hitW rsH (AxSpinHdB.pac 0) → hitW rsH (pcm 0) →
    gprVal rsH AxSpinE8.r10 = lkv → gprVal rsH 9#5 = lkv →
    gprVal rsH AxSpinE8.r1 = AxSpinHdB.pac 0x16 → gprVal rsH AxSpinE8.r4 = tp →
    hitW rsH lkv → hitW rsH (lkv + sign_extend (m := 64) (16#12)) →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rsH
      (AxSpinE8.sp1Of (spo (gprVal rsH AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Hram →
    AxSpinPO1.slot8 σi T L i rsH
      (AxSpinE8.sp1Of (spo (gprVal rsH AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    dataAtS σi T (.Load .Data) (lkv + sign_extend (m := 64) (16#12)) 8 Pcl →
    ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    dataAtS σi T (.Load .Data) lkv 4 Plk → ¬ L.xlText (paZ Plk) →
    -- the pins (GUARDED): holding's returns, its s1 reload, the non-panic arm
    (hb = true →
      (aqKp k b + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
        graphValue (gtAdGd GT) (i, aqKp k b + 7) = some (stBytes 8 (pch 0x1a))) ∧
      (aqKp k b + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
        graphValue (gtAdGd GT) (i, aqKp k b + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16))) ∧
      (aqKp k b + 11 < (AxOpsem.grow (gtAdGd GT) i).length →
        graphValue (gtAdGd GT) (i, aqKp k b + 11) = some (stBytes 8 lkv)) ∧
      (aqKp k b + 12 < (AxOpsem.grow (gtAdGd GT) i).length →
        ∀ vcpu, graphValue (gtAdGd GT) (i, aqKp k b + 4) = some vcpu →
        hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet tp) = 0#64)) →
    -- the designated cut `aq` (long arm, row length `aqKp + 12`): the caller's arm
    (hb = true →
      ⊢ KLongEnd (hlc := hlc) L GT nm i Ψ (aqKp k b) rsH Hra Hs0 Hs1 Hram Hs0m
          (fun _ => iprop(True)) (ORacy L GT i (aqKp k b + 4))) →
    -- the row-end hook (windowed, resource-free; misses the cut `aqKp + 12`)
    (∀ k' : Nat, aqKp k b ≤ k' → k' ≤ (if hb then aqKp k b + 11 else aqKp k b + 1) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜aqKh k b hb < (AxOpsem.grow (gtAdGd GT) i).length ∧
          ctrlOkSW T satp0 rs' ∧ rs' .PC = AxSpinHdB.pac 0x1a ∧ rs' .tlb = rsH .tlb ∧
          gprVal rs' AxSpinE8.r2 = gprVal rsH AxSpinE8.r2 ∧ gprVal rs' 9#5 = lkv ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 14 → r.toNat ≠ 15 → gprVal rs' r = gprVal rsH r)⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', aqKh k b hb⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsH none ibH, aqKp k b⟩ Ψ := by
  intro HR Hw8 H1 H2 H3 H4 H5 Hc HPC Hhit HhitM Ea0 Es1 Era Etp Hhlk Hhcl
    Bra Bs0 Bs1 Bram Bs0m Hdisj Hdcl Hntcl Hnrcl Hdlk Hntlk Vp Kaq HΨend
  exact AxSpinAq2.midG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxh Ψ
    HΨmid k b hb rsH ibH lkv tp Hra Hs0 Hs1 Hram Hs0m Pcl Plk HR Hw8 H1 H2 H3 H4 H5 Hc HPC Hhit
    HhitM Ea0 Es1 Era Etp Hhlk Hhcl Bra Bs0 Bs1 Bram Bs0m Hdisj Hdcl Hntcl Hnrcl Hdlk Hntlk
    (fun h => ⟨AxSpinT2i.gateOfPinG (Vp h).1, AxSpinT2i.gateOfPinG (Vp h).2.1,
      AxSpinT2i.gateOfPinG (Vp h).2.2.1, (Vp h).2.2.2⟩) Kaq HΨend

include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxh HΨmid in
/-- acquire's call of holding (boundary `aqKp k b`, `PC = holding`) through the not-taken panic
branch (boundary `aqKh k b hb`, `PC = acquire + 0x1a`), both arms of `hb`; the long arm's
non-panic value pin makes `a0 = 0`.  Stage 2: the full-row corollary of `AxSpinAq2.midP`. -/
theorem AxSpinAq2.mid (k : Nat) (b hb : Bool) (rsH : RegFile) (ibH : Ibch) (lkv tp : BitVec 64)
    (Hra Hs0 Hs1 Hram Hs0m Pcl Plk : BitVec 64) :
    RowHolding (aqKp k b) (AxOpsem.grow (gtAdGd GT) i) hb L.xlLk (L.xlLk + 16) (paZ Hra)
      (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m) →
    aqKh k b hb < (AxOpsem.grow (gtAdGd GT) i).length →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0m) →
    ctrlOkSW T satp0 rsH → rsH .PC = pch 0 → hitW rsH (AxSpinHdB.pac 0) → hitW rsH (pcm 0) →
    gprVal rsH AxSpinE8.r10 = lkv → gprVal rsH 9#5 = lkv →
    gprVal rsH AxSpinE8.r1 = AxSpinHdB.pac 0x16 → gprVal rsH AxSpinE8.r4 = tp →
    hitW rsH lkv → hitW rsH (lkv + sign_extend (m := 64) (16#12)) →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rsH
      (spo (gprVal rsH AxSpinE8.r2) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rsH
      (AxSpinE8.sp1Of (spo (gprVal rsH AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Hram →
    AxSpinPO1.slot8 σi T L i rsH
      (AxSpinE8.sp1Of (spo (gprVal rsH AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    dataAtS σi T (.Load .Data) (lkv + sign_extend (m := 64) (16#12)) 8 Pcl →
    ¬ L.xlText (paZ Pcl) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    dataAtS σi T (.Load .Data) lkv 4 Plk → ¬ L.xlText (paZ Plk) →
    -- the pins: holding's returns, its s1 reload, the non-panic arm
    (hb = true →
      graphValue (gtAdGd GT) (i, aqKp k b + 7) = some (stBytes 8 (pch 0x1a)) ∧
      graphValue (gtAdGd GT) (i, aqKp k b + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16)) ∧
      graphValue (gtAdGd GT) (i, aqKp k b + 11) = some (stBytes 8 lkv) ∧
      ∀ vcpu, graphValue (gtAdGd GT) (i, aqKp k b + 4) = some vcpu →
        hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet tp) = 0#64) →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = AxSpinHdB.pac 0x1a ∧ rs' .tlb = rsH .tlb ∧
          gprVal rs' AxSpinE8.r2 = gprVal rsH AxSpinE8.r2 ∧ gprVal rs' 9#5 = lkv ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 14 → r.toNat ≠ 15 → gprVal rs' r = gprVal rsH r)⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', aqKh k b hb⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsH none ibH, aqKp k b⟩ Ψ := by
  intro HR Hlen Hw8 H1 H2 H3 H4 H5 Hc HPC Hhit HhitM Ea0 Es1 Era Etp Hhlk Hhcl
    Bra Bs0 Bs1 Bram Bs0m Hdisj Hdcl Hntcl Hnrcl Hdlk Hntlk Vp
  have Hkh : aqKp k b + (if hb then 12 else 1) < (AxOpsem.grow (gtAdGd GT) i).length := Hlen
  iintro C
  iapply (AxSpinAq2.midP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxh Ψ
    HΨmid k b hb rsH ibH lkv tp Hra Hs0 Hs1 Hram Hs0m Pcl Plk
    (AxSpinHd8.rowHoldingPOfFull _ _ _ _ _ _ _ _ _ _ HR) Hw8 H1 H2 H3 H4 H5 Hc HPC Hhit HhitM
    Ea0 Es1 Era Etp Hhlk Hhcl Bra Bs0 Bs1 Bram Bs0m Hdisj Hdcl Hntcl Hnrcl Hdlk Hntlk
    (fun h => ⟨fun _ => (Vp h).1, fun _ => (Vp h).2.1, fun _ => (Vp h).2.2.1,
      fun _ => (Vp h).2.2.2⟩)
    (fun h => by
      subst h
      unfold KLongEnd
      iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp
      exact absurd Hp.1 (by simp only [↓reduceIte] at Hkh; omega))
    (fun _ _ h2 h3 => absurd h3 (by
      cases hb <;> simp only [Bool.false_eq_true, ↓reduceIte] at h2 Hkh <;> omega)))
  iintro %rs' %ib' %Hp
  iapply C $$ %rs' %ib'
  ipureintro
  exact Hp.2


set_option maxHeartbeats 4000000 in
include HL Hcons hmode hasid hppn Hfix Htxa Htxm HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `AxSpinAq2.tail` on a PREFIX row (`RowAcquireP`,
`AxSpinAq1.spinRmwP` / `spinValsP`; pins guarded): `wpdSpinAqP` (sub-window `[aqKh, aqKm]`),
`wpdMycpuP` (`[aqKm, aqKm + 4]`), the lk->cpu store by the position-generic `XxSdCpu`, and a
`by_cases` at `aqKm`, `aqKm + 4 … + 8`; the row-end case is the windowed resource-free hook over
`[aqKh, aqKm + 8]` (no designated cut in this window).

(Lean-only, P1) THE GATED CORE / shared proof (`ret` generic): mycpu is `wpdMycpuG` (its return
is the link `acquire + 0x28` of `jal mycpu`), the two return pins replaced by their
`AxSpinT2i.Gate`s (`aqKm + 2` against `acquire + 0x28`, `aqKm + 5` against `stBytes 8 ret`).  At
acquire's ra reload's boundary `aqKm + 6` a `by_cases` on the reloaded value: equal ⇒ the
P-form script; else, when `stBytes 8 ret` is the spill, the arm is `AxSpinT2i.cutReloadG` with
the reload's `RLfact` (refuted); otherwise the gate puts the row end at `aqKm + 6` (the hook).
`AxSpinAq2.tailP` = this ∘ `AxSpinT2i.gateOfPinG`. -/
theorem AxSpinAq2.tailGr (k : Nat) (b hb : Bool) (n : Nat) (rsS : RegFile) (ibS : Ibch)
    (spS tp ret lkv : BitVec 64) (Pra Ps0 Ps1 Mra Mms0 Pcl Plk : BitVec 64)
    (qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m : Int)
    (kra ks0 ks1 : Nat) (vra vs0 vs1 : List (BitVec 8)) (cra cs0 cs1 : WmClass) :
    -- the row
    RowAcquireP k b hb n (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) qra qs0 qs1
      qmra qms0 pn pint hra hs0 hs1 hram hs0m L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0) →
    AxSpinAq1.spinRmwP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n L.xlLk →
    AxSpinAq1.spinValsP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Mra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Mms0) →
    -- the spills (the caller's row facts)
    (AxOpsem.grow (gtAdGd GT) i)[kra]? = some (.LStore false (paZ Pra) vra cra) →
    vra.length = 8 → kra < aqKm k b hb n + 5 →
    nowr (AxOpsem.grow (gtAdGd GT) i) kra (aqKm k b hb n + 8) (paZ Pra) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks0]? = some (.LStore false (paZ Ps0) vs0 cs0) →
    vs0.length = 8 → ks0 < aqKm k b hb n + 6 →
    nowr (AxOpsem.grow (gtAdGd GT) i) ks0 (aqKm k b hb n + 8) (paZ Ps0) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks1]? = some (.LStore false (paZ Ps1) vs1 cs1) →
    vs1.length = 8 → ks1 < aqKm k b hb n + 7 →
    nowr (AxOpsem.grow (gtAdGd GT) i) ks1 (aqKm k b hb n + 8) (paZ Ps1) 8 →
    -- the entry state
    ctrlOkSW T satp0 rsS → rsS .PC = AxSpinHdB.pac 0x1a → hitW rsS (AxSpinHdB.pac 0) →
    hitW rsS (pcm 0) →
    gprVal rsS AxSpinE8.r2 = spS → gprVal rsS AxSpinE8.r4 = tp → gprVal rsS 9#5 = lkv →
    -- the lock word and lk->cpu
    hitW rsS lkv → hitW rsS (lkv + sign_extend (m := 64) (16#12)) →
    paZ Plk = L.xlLk → ¬ L.xlText (paZ Plk) → dataAtS σi T (accAmo true) lkv 4 Plk →
    dataAtS σi T (.Store .Data) (lkv + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 →
    -- acquire's slots (reloaded here), mycpu's slots
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    AxSpinPO1.slot8 σi T L i rsS (AxSpinE8.sp1Of spS + sign_extend (m := 64) AxSpinE8.immRa) Mra →
    AxSpinPO1.slot8 σi T L i rsS (AxSpinE8.sp1Of spS + sign_extend (m := 64) AxSpinE8.immS0) Mms0 →
    dj (paZ Mms0) 8 (paZ Mra) 8 →
    CpuWin L GT i (i, aqKA k b hb n) →
    -- P1: the reload GATES of mycpu's return and acquire's return
    AxSpinT2i.Gate GT i (aqKm k b hb n + 2) (stBytes 8 (AxSpinHdB.pac 0x28)) →
    AxSpinT2i.Gate GT i (aqKm k b hb n + 5) (stBytes 8 ret) →
    jalrTgt 0#12 ret = ret →
    -- the row-end hook (windowed, resource-free)
    (∀ k' : Nat, aqKh k b hb ≤ k' → k' ≤ aqKm k b hb n + 8 →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
      ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k'⟩ Ψ) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq2.KTail (hlc := hlc) L GT nm T satp0 i cpu Ψ k b hb n rsS spS tp ret Pra Ps0 Ps1
        vra vs0 vs1 -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsS none ibS, aqKh k b hb⟩ Ψ := by
  intro HR Hrmw Hvals Hw8 Hn_ra Hn_s0 Hn_s1 Hn_mra Hn_ms0
    Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hks1 Hls1 Hlt_s1 Hbw_s1
    Hc0 HPC0 Hhit0 HhitM Esp0 Etp0 Es10 Hhv Hhcl Hpl Hntl Hdal Hdcl Hpcl
    Bra Bs0 Bs1 Bmra Bms0 Hdm Hwin Vm Vr Hret HΨend
  have HRt := HR.2.2.2.2
  have Ekm : aqKm k b hb n = aqKh k b hb + (n + 1) := rfl
  obtain ⟨_, HdaL_ra, Hh_ra, Hpr_ra, Hnt_ra⟩ := Bra
  obtain ⟨_, HdaL_s0, Hh_s0, Hpr_s0, Hnt_s0⟩ := Bs0
  obtain ⟨_, HdaL_s1, Hh_s1, Hpr_s1, Hnt_s1⟩ := Bs1
  obtain ⟨HdaS_mra, HdaL_mra, Hh_mra, Hpr_mra, Hnt_mra⟩ := Bmra
  obtain ⟨HdaS_ms0, HdaL_ms0, Hh_ms0, Hpr_ms0, Hnt_ms0⟩ := Bms0
  have Htx := Htxa
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, T24, T28, T2a, T2c, T2e, T30, T32⟩ := Htx
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL := XxLd L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XT := XxRet L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have WM := wpdMycpuG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Ψ HΨmid
  unfold AxSpinAq2.KTail
  iintro #Hil Hnh C
  -- ---- the spin loop, at aqKh (claim at aqKA, continuation at aqKm) ----
  iapply (wpdSpinAqP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Ψ HΨmid k b hb n
    rsS ibS Plk Hrmw Hvals Hc0 HPC0
    (hitWSvpn rsS (AxSpinHdB.pac 0x1a) (AxSpinHdB.pac 0) (by decide) Hhit0) Hpl Hntl
    (by rw [Es10]; exact Hdal) (by rw [Es10]; exact Hhv)
    (fun k' h1 h2 h3 => HΨend k' h1 (by omega) h3)) $$ Hil Hnh
  unfold AxSpinAq1.KSpin
  rw [show aqKh k b hb + n = aqKA k b hb n from rfl]
  iintro %rs1 %ib1 %Hs HLK HCpu HNp
  obtain ⟨Hc1, HPC1, Htl1, -, Hkeep1, Hz⟩ := Hs
  rw [show aqKh k b hb + (n + 1) = aqKm k b hb n from rfl]
  -- row end at aqKm
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKm k b hb n
  · iclear C
    iclear HLK
    iclear HCpu
    iclear HNp
    iapply (HΨend _ (by omega) (by omega) E0 _)
  -- ---- + 0x24: jal ra,mycpu (aqKm) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs1 (AxSpinHdB.pac 0x24) false a24 (some (pcm 0))
      (some (1#5, BitVec.addInt (AxSpinHdB.pac 0x24) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs1 (AxSpinHdB.pac 0x24)
      false 3296#21 1#5 (by decide)
    rw [show AxSpinHdB.pac 0x24 + sign_extend (m := 64) 3296#21 = pcm 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (AxSpinHdB.pac 0x24) (incr false)) =
      some (1#5, BitVec.addInt (AxSpinHdB.pac 0x24) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs1 (aqKm k b hb n) (AxSpinHdB.pac 0x24) false a24 (some (pcm 0))
    (some (1#5, BitVec.addInt (AxSpinHdB.pac 0x24) (incr false)))
    (retxRefl cpu rs1 (aqKm k b hb n) ib1) Hc1 HPC1
    (hitWSvpn rs1 (AxSpinHdB.pac 0x24) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs1 _ Htl1 Hhit0))
    (tw4A24 σi T satp0 _ T24) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 3296#21 (.Regidx 1#5)) Hcj (by omega))
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 (fun _ => rfl) HG2
  have HPC2 : rs2 .PC = pcm 0 := gbPc T satp0 _ _ _ _ _ _ HG2
  have Htl2 : rs2 .tlb = rsS .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  have Esp2 : gprVal rs2 AxSpinE8.r2 = spS := by
    rw [HF2]; ax_spin_aq2_zsimp; rw [Hkeep1 2#5 (by decide)]; exact Esp0
  have Etp2 : gprVal rs2 AxSpinE8.r4 = tp := by
    rw [HF2]; ax_spin_aq2_zsimp; rw [Hkeep1 4#5 (by decide)]; exact Etp0
  have Es12 : gprVal rs2 9#5 = lkv := by
    rw [HF2]; ax_spin_aq2_zsimp; rw [Hkeep1 9#5 (by decide)]; exact Es10
  have Evra : AxSpinE8.vaRa rs2 = AxSpinE8.sp1Of spS + sign_extend (m := 64) AxSpinE8.immRa := by
    unfold AxSpinE8.vaRa; rw [Esp2]
  have Evs0 : AxSpinE8.vaS0 rs2 = AxSpinE8.sp1Of spS + sign_extend (m := 64) AxSpinE8.immS0 := by
    unfold AxSpinE8.vaS0; rw [Esp2]
  -- mycpu's entry ra: the `jal mycpu` link
  have Era2 : gprVal rs2 AxSpinE8.r1 = AxSpinHdB.pac 0x28 := by
    rw [HF2]; ax_spin_aq2_zsimp; decide
  -- ---- mycpu, at aqKm (continuation at aqKm + 4; P1 gate form) ----
  have HRm : RowMycpuP (aqKm k b hb n) (AxOpsem.grow (gtAdGd GT) i) (paZ Mra) (paZ Mms0) :=
    AxSpinPO3.rowMycpuPOf _ _ _ _ (rowShPAppL (s1 := mycSh (paZ Mra) (paZ Mms0))
      (s2 := [.RS (L.xlLk + 16) 8, .RL (paZ Pra) 8, .RL (paZ Ps0) 8, .RL (paZ Ps1) 8]) HRt)
  iapply (WM (aqKm k b hb n) rs2 ib2 Mra Mms0 HRm Hw8 Hn_mra Hn_ms0
    (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2 (hitWAgree rsS rs2 _ Htl2 HhitM)
    (by rw [Evra]; exact HdaS_mra) (by rw [Evra]; exact HdaL_mra)
    (by rw [Evra]; exact hitWAgree rsS rs2 _ Htl2 Hh_mra)
    (by rw [Evs0]; exact HdaS_ms0) (by rw [Evs0]; exact HdaL_ms0)
    (by rw [Evs0]; exact hitWAgree rsS rs2 _ Htl2 Hh_ms0)
    Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0 (by unfold dj at Hdm; omega) (by rw [Era2]; exact Vm)
    (by rw [Era2]; decide)
    (fun k' h1 h2 h3 => HΨend k' (by omega) (by omega) h3))
  iintro %vmra %vms0 %rs3 %ib3 %HM - -
  -- row end at aqKm + 4
  by_cases E4 : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKm k b hb n + 4
  · iclear C
    iclear HLK
    iclear HCpu
    iclear HNp
    iapply (HΨend _ (by omega) (by omega) E4 _)
  obtain ⟨Hc3, HPC3, Htl3', Ea03, Esp3, -, -, -, -, Hkeep3, -, -, -, -⟩ := HM
  rw [Era2] at HPC3
  have Htl3 : rs3 .tlb = rsS .tlb := Htl3'.trans Htl2
  have Ea0 : gprVal rs3 AxSpinE8.r10 = AxSpinE8.mycpuRet tp := by rw [Ea03, Etp2]
  have Es13 : gprVal rs3 9#5 = lkv := by
    rw [Hkeep3 9#5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact Es12
  -- ---- + 0x28: c.sd a0,16(s1) — the owned lk->cpu store (aqKm + 4) ----
  have HP : ⊢ RCpu (GF := GF) L nm.xnH (gtAdGd GT) (i, aqKA k b hb n) -∗
      iprop(True ∗ ∃ vold, RVL nm.xnH (gtAdGd GT) (clb L) (i, aqKA k b hb n) vold) := by
    unfold RCpu
    iintro H
    isplitr
    · itrivial
    · iexact H
  iapply (XxSdCpu L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
    _ rs3 (aqKm k b hb n + 4) (AxSpinHdB.pac 0x28) true 16#12 10#5 9#5
    (lkv + sign_extend (m := 64) (16#12)) Pcl (AxSpinE8.mycpuRet tp) (i, aqKA k b hb n)
    (RCpu L nm.xnH (gtAdGd GT) (i, aqKA k b hb n)) iprop(True)
    (retxRefl cpu rs3 (aqKm k b hb n + 4) ib3) Hc3 HPC3
    (hitWSvpn rs3 (AxSpinHdB.pac 0x28) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs3 _ Htl3 Hhit0))
    (twaE888 σi T satp0 _ T28) (by rw [Es13]) Hdcl (hitWAgree rsS rs3 _ Htl3 Hhcl) Hpcl Ea0
    rfl Hwin HP (by omega)) $$ HCpu
  iintro %rs4 %ib4 %HG4 %Hsd HDep
  -- row end at aqKm + 5
  by_cases E5 : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKm k b hb n + 5
  · iclear C
    iclear HLK
    iclear HNp
    iclear HDep
    iapply (HΨend _ (by omega) (by omega) E5 _)
  have HF4 := stepRegs0 T satp0 (gprVal rs3) rs3 _ _ _ rs4 (fun _ => rfl) HG4
  have HPC4 : rs4 .PC = AxSpinHdB.pac 0x2a := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rsS .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  have Esp3' : gprVal rs3 2#5 = spS := Esp3.trans Esp2
  -- ---- + 0x2a: c.ldsp ra,24(sp) — reload (aqKm + 5) ----
  iapply (XL _ rs4 (aqKm k b hb n + 5) (AxSpinHdB.pac 0x2a) true AxSpinPO3.imm24 2#5 1#5
    (spS + sign_extend (m := 64) AxSpinPO3.imm24) Pra kra vra cra
    (retxRefl cpu rs4 (aqKm k b hb n + 5) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (AxSpinHdB.pac 0x2a) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs4 _ Htl4 Hhit0))
    (tw60e2 σi T satp0 _ T2a) (by decide) (by rw [HF4, Esp3'])
    HdaL_ra (hitWAgree rsS rs4 _ Htl4 Hh_ra) Hpr_ra Hnt_ra Hn_ra Hkra Hlra Hlt_ra ?_
    (by omega))
  · intro k' lb' rl bb m Hk Hl Hid
    have := Hbw_ra k' lb' rl bb m ⟨Hk.1, by omega⟩ Hl Hid
    unfold dj at this
    omega
  iintro %vra' %rs5 %ib5 %Hlvra %HG5 %Hgv5 H5
  -- P1 GATE at the ra reload's boundary aqKm + 6: a wrong reloaded value ends the row there
  by_cases Hv : ¬ vra' = stBytes 8 ret
  · iclear C
    iclear HLK
    iclear HNp
    iclear HDep
    by_cases Hs : stBytes 8 ret = vra
    · -- `ret`'s bytes are the spill's: the reload CUT refutes the arm (RLfact read back)
      rw [Hs] at Hv Vr
      obtain ⟨lb5, Hlb5, Hsh5⟩ := HRt 5 (.RL (paZ Pra) 8) rfl (AxSpinAq2.gvLt _ _ _ _ Hgv5)
      iapply (AxSpinT2i.cutReloadG L GT nm Hcons i (aqKm k b hb n + 5) (paZ Pra) vra vra' Ψ
        ⟨lb5, Hlb5, Hsh5⟩ Hlra Hgv5 Hv Vr _) $$ H5
    · have Hend := AxSpinT2i.lenOfGate Vr Hgv5 Hv
      iclear H5
      iapply (HΨend _ (by omega) (by omega) (by omega) _)
  have Hvra : vra' = stBytes 8 ret := Classical.byContradiction Hv
  -- row end at aqKm + 6
  by_cases E6 : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKm k b hb n + 6
  · iclear C
    iclear HLK
    iclear HNp
    iclear HDep
    iclear H5
    iapply (HΨend _ (by omega) (by omega) E6 _)
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = AxSpinHdB.pac 0x2c := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rsS .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- + 0x2c: c.ldsp s0,16(sp) — reload (aqKm + 6) ----
  iapply (XL _ rs5 (aqKm k b hb n + 6) (AxSpinHdB.pac 0x2c) true AxSpinPO3.imm16 2#5 8#5
    (spS + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 ks0 vs0 cs0
    (retxRefl cpu rs5 (aqKm k b hb n + 6) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (AxSpinHdB.pac 0x2c) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs5 _ Htl5 Hhit0))
    (tw6442 σi T satp0 _ T2c) (by decide)
    (by rw [HF5]; ax_spin_aq2_zsimp; rw [Esp3'])
    HdaL_s0 (hitWAgree rsS rs5 _ Htl5 Hh_s0) Hpr_s0 Hnt_s0 Hn_s0 Hks0 Hls0 Hlt_s0 ?_
    (by omega))
  · intro k' lb' rl bb m Hk Hl Hid
    have := Hbw_s0 k' lb' rl bb m ⟨Hk.1, by omega⟩ Hl Hid
    unfold dj at this
    omega
  iintro %vs0' %rs6 %ib6 %Hlvs0 %HG6 %Hgv6 H6
  -- row end at aqKm + 7
  by_cases E7 : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKm k b hb n + 7
  · iclear C
    iclear HLK
    iclear HNp
    iclear HDep
    iclear H5
    iclear H6
    iapply (HΨend _ (by omega) (by omega) E7 _)
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = AxSpinHdB.pac 0x2e := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rsS .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- ---- + 0x2e: c.ldsp s1,8(sp) — reload (aqKm + 7) ----
  iapply (XL _ rs6 (aqKm k b hb n + 7) (AxSpinHdB.pac 0x2e) true AxSpinPO3.imm8 2#5 9#5
    (spS + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 ks1 vs1 cs1
    (retxRefl cpu rs6 (aqKm k b hb n + 7) ib6) (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (AxSpinHdB.pac 0x2e) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs6 _ Htl6 Hhit0))
    (tw64a2 σi T satp0 _ T2e) (by decide)
    (by rw [HF6]; ax_spin_aq2_zsimp; rw [Esp3'])
    HdaL_s1 (hitWAgree rsS rs6 _ Htl6 Hh_s1) Hpr_s1 Hnt_s1 Hn_s1 Hks1 Hls1 Hlt_s1 ?_
    (by omega))
  · intro k' lb' rl bb m Hk Hl Hid
    have := Hbw_s1 k' lb' rl bb m ⟨Hk.1, by omega⟩ Hl Hid
    unfold dj at this
    omega
  iintro %vs1' %rs7 %ib7 %Hlvs1 %HG7 %Hgv7 H7
  -- row end at aqKm + 8
  by_cases E8 : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKm k b hb n + 8
  · iclear C
    iclear HLK
    iclear HNp
    iclear HDep
    iclear H5
    iclear H6
    iclear H7
    iapply (HΨend _ (by omega) (by omega) E8 _)
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = AxSpinHdB.pac 0x30 := by rw [gbPc T satp0 _ _ _ _ _ _ HG7]; decide
  have Htl7 : rs7 .tlb = rsS .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  -- ---- + 0x30: c.addi16sp sp,32 (aqKm + 8) ----
  have Hc8 := certAddi (ctrlOkSW T satp0) rs7 (AxSpinHdB.pac 0x30) true 2#5 2#5
    (caddi16spImm 2#6) (by decide)
  simp only [HF7] at Hc8
  ax_spin_aq2_zsimp at Hc8
  iapply (XR _ rs7 (aqKm k b hb n + 8) (AxSpinHdB.pac 0x30) true q28 _ _
    (retxRefl cpu rs7 (aqKm k b hb n + 8) ib7) (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (AxSpinHdB.pac 0x30) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs7 _ Htl7 Hhit0))
    (tw6105 σi T satp0 _ T30) (AxSpinE8.owOkSome 2#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _)) Hc8 (by omega))
  iintro %rs8 %ib8 %HG8
  have HF8 := stepRegs T satp0 _ rs7 _ _ _ _ _ rs8 HF7 HG8
  have HPC8 : rs8 .PC = AxSpinHdB.pac 0x32 := by rw [gbPc T satp0 _ _ _ _ _ _ HG8]; decide
  have Htl8 : rs8 .tlb = rsS .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG8).trans Htl7
  -- ---- + 0x32: c.ret (aqKm + 8; the target is the reloaded ra, pinned by `Vr`) ----
  iapply (XT _ rs8 (aqKm k b hb n + 8) (AxSpinHdB.pac 0x32)
    (retxRefl cpu rs8 (aqKm k b hb n + 8) ib8) (gbCtrl T satp0 _ _ _ _ _ _ HG8) HPC8
    (hitWSvpn rs8 (AxSpinHdB.pac 0x32) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs8 _ Htl8 Hhit0))
    (tw8082 σi T satp0 _ T32) rfFIns1e (by omega))
  iintro %rs' %ib' %HGr
  have HFr := stepRegs0 T satp0 _ rs8 _ _ _ rs' HF8 HGr
  have Hgpr1 : gprVal rs8 1#5 = ldRes false 8 vra' := by
    rw [HF8]
    ax_spin_aq2_zsimp
  iapply C $$ %vra' %vs0' %vs1' %rs' %ib' [] HLK HNp HDep H5 H6 H7
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl8, ?_,
    ?_, Hlvra, Hlvs0, Hlvs1, ?_, ?_, ?_, ?_, Hz, Hsd.1, Hsd.2, Hgv5, Hgv6, Hgv7⟩
  · -- PC = ret
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    show jalrTgt 0#12 (gprVal rs8 1#5) = ret
    rw [Hgpr1, Hvra, AxSpinE8.ldResStBytes8, Hret]
  · -- sp
    rw [HFr]
    ax_spin_aq2_zsimp
    rw [Esp3']
  · -- a0
    rw [HFr]
    ax_spin_aq2_zsimp
    exact Ea0
  · rw [HFr]
    ax_spin_aq2_zsimp
  · rw [HFr]
    ax_spin_aq2_zsimp
  · rw [HFr]
    ax_spin_aq2_zsimp
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rsS r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n9 : r ≠ 9#5 := fun h => Hr9 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
      rw [Hkeep3 r Hr1 Hr2 Hr8 Hr10 Hr15, HF2]
      simp (disch := assumption) only [AxSpinE8.updOther]
      exact Hkeep1 r Hr15

include HL Hcons hmode hasid hppn Hfix Htxa Htxm HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `AxSpinAq2.tail` on a PREFIX row (`RowAcquireP`,
`AxSpinAq1.spinRmwP` / `spinValsP`; pins guarded): `wpdSpinAqP` (sub-window `[aqKh, aqKm]`),
`wpdMycpuP` (`[aqKm, aqKm + 4]`), the lk->cpu store by the position-generic `XxSdCpu`, and a
`by_cases` at `aqKm`, `aqKm + 4 … + 8`; the row-end case is the windowed resource-free hook over
`[aqKh, aqKm + 8]` (no designated cut in this window).  P1: the corollary of
`AxSpinAq2.tailGr` via `AxSpinT2i.gateOfPinG`. -/
theorem AxSpinAq2.tailP (k : Nat) (b hb : Bool) (n : Nat) (rsS : RegFile) (ibS : Ibch)
    (spS tp ret lkv : BitVec 64) (Pra Ps0 Ps1 Mra Mms0 Pcl Plk : BitVec 64)
    (qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m : Int)
    (kra ks0 ks1 : Nat) (vra vs0 vs1 : List (BitVec 8)) (cra cs0 cs1 : WmClass) :
    -- the row
    RowAcquireP k b hb n (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) qra qs0 qs1
      qmra qms0 pn pint hra hs0 hs1 hram hs0m L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0) →
    AxSpinAq1.spinRmwP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n L.xlLk →
    AxSpinAq1.spinValsP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Mra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Mms0) →
    -- the spills (the caller's row facts)
    (AxOpsem.grow (gtAdGd GT) i)[kra]? = some (.LStore false (paZ Pra) vra cra) →
    vra.length = 8 → kra < aqKm k b hb n + 5 →
    nowr (AxOpsem.grow (gtAdGd GT) i) kra (aqKm k b hb n + 8) (paZ Pra) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks0]? = some (.LStore false (paZ Ps0) vs0 cs0) →
    vs0.length = 8 → ks0 < aqKm k b hb n + 6 →
    nowr (AxOpsem.grow (gtAdGd GT) i) ks0 (aqKm k b hb n + 8) (paZ Ps0) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks1]? = some (.LStore false (paZ Ps1) vs1 cs1) →
    vs1.length = 8 → ks1 < aqKm k b hb n + 7 →
    nowr (AxOpsem.grow (gtAdGd GT) i) ks1 (aqKm k b hb n + 8) (paZ Ps1) 8 →
    -- the entry state
    ctrlOkSW T satp0 rsS → rsS .PC = AxSpinHdB.pac 0x1a → hitW rsS (AxSpinHdB.pac 0) →
    hitW rsS (pcm 0) →
    gprVal rsS AxSpinE8.r2 = spS → gprVal rsS AxSpinE8.r4 = tp → gprVal rsS 9#5 = lkv →
    -- the lock word and lk->cpu
    hitW rsS lkv → hitW rsS (lkv + sign_extend (m := 64) (16#12)) →
    paZ Plk = L.xlLk → ¬ L.xlText (paZ Plk) → dataAtS σi T (accAmo true) lkv 4 Plk →
    dataAtS σi T (.Store .Data) (lkv + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 →
    -- acquire's slots (reloaded here), mycpu's slots
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    AxSpinPO1.slot8 σi T L i rsS (AxSpinE8.sp1Of spS + sign_extend (m := 64) AxSpinE8.immRa) Mra →
    AxSpinPO1.slot8 σi T L i rsS (AxSpinE8.sp1Of spS + sign_extend (m := 64) AxSpinE8.immS0) Mms0 →
    dj (paZ Mms0) 8 (paZ Mra) 8 →
    CpuWin L GT i (i, aqKA k b hb n) →
    -- the pins (GUARDED): mycpu's return, acquire's return
    (aqKm k b hb n + 2 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 2) = some (stBytes 8 (AxSpinHdB.pac 0x28))) →
    (aqKm k b hb n + 5 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 5) = some (stBytes 8 ret)) →
    jalrTgt 0#12 ret = ret →
    -- the row-end hook (windowed, resource-free)
    (∀ k' : Nat, aqKh k b hb ≤ k' → k' ≤ aqKm k b hb n + 8 →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
      ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k'⟩ Ψ) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq2.KTail (hlc := hlc) L GT nm T satp0 i cpu Ψ k b hb n rsS spS tp ret Pra Ps0 Ps1
        vra vs0 vs1 -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsS none ibS, aqKh k b hb⟩ Ψ := by
  intro HR Hrmw Hvals Hw8 Hn_ra Hn_s0 Hn_s1 Hn_mra Hn_ms0
    Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hks1 Hls1 Hlt_s1 Hbw_s1
    Hc0 HPC0 Hhit0 HhitM Esp0 Etp0 Es10 Hhv Hhcl Hpl Hntl Hdal Hdcl Hpcl
    Bra Bs0 Bs1 Bmra Bms0 Hdm Hwin Vm Vr Hret HΨend
  exact AxSpinAq2.tailGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Ψ HΨmid
    k b hb n rsS ibS spS tp ret lkv Pra Ps0 Ps1 Mra Mms0 Pcl Plk qra qs0 qs1 qmra qms0 pn pint hra
    hs0 hs1 hram hs0m kra ks0 ks1 vra vs0 vs1 cra cs0 cs1 HR Hrmw Hvals Hw8 Hn_ra Hn_s0 Hn_s1
    Hn_mra Hn_ms0 Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hks1 Hls1 Hlt_s1 Hbw_s1
    Hc0 HPC0 Hhit0 HhitM Esp0 Etp0 Es10 Hhv Hhcl Hpl Hntl Hdal Hdcl Hpcl
    Bra Bs0 Bs1 Bmra Bms0 Hdm Hwin (AxSpinT2i.gateOfPinG Vm) (AxSpinT2i.gateOfPinG Vr) Hret HΨend

include HL Hcons hmode hasid hppn Hfix Htxa Htxm HΨmid in
/-- acquire + 0x1a … + 0x32: the spin loop (claim at `aqKA`), `jal mycpu`, mycpu, the owned
`lk->cpu` store, the three reloads, `c.addi16sp`, `c.ret` (boundary `aqKm + 8`).  Stage 2: the
full-row corollary of `AxSpinAq2.tailP`. -/
theorem AxSpinAq2.tail (k : Nat) (b hb : Bool) (n : Nat) (rsS : RegFile) (ibS : Ibch)
    (spS tp ret lkv : BitVec 64) (Pra Ps0 Ps1 Mra Mms0 Pcl Plk : BitVec 64)
    (qra qs0 qs1 qmra qms0 pn pint hra hs0 hs1 hram hs0m : Int)
    (kra ks0 ks1 : Nat) (vra vs0 vs1 : List (BitVec 8)) (cra cs0 cs1 : WmClass) :
    -- the row
    RowAcquire k b hb n (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) qra qs0 qs1
      qmra qms0 pn pint hra hs0 hs1 hram hs0m L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0) →
    AxSpinAq1.spinRmw (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n L.xlLk →
    spinVals (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Mra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Mms0) →
    -- the spills (the caller's row facts)
    (AxOpsem.grow (gtAdGd GT) i)[kra]? = some (.LStore false (paZ Pra) vra cra) →
    vra.length = 8 → kra < aqKm k b hb n + 5 →
    nowr (AxOpsem.grow (gtAdGd GT) i) kra (aqKm k b hb n + 8) (paZ Pra) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks0]? = some (.LStore false (paZ Ps0) vs0 cs0) →
    vs0.length = 8 → ks0 < aqKm k b hb n + 6 →
    nowr (AxOpsem.grow (gtAdGd GT) i) ks0 (aqKm k b hb n + 8) (paZ Ps0) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks1]? = some (.LStore false (paZ Ps1) vs1 cs1) →
    vs1.length = 8 → ks1 < aqKm k b hb n + 7 →
    nowr (AxOpsem.grow (gtAdGd GT) i) ks1 (aqKm k b hb n + 8) (paZ Ps1) 8 →
    -- the entry state
    ctrlOkSW T satp0 rsS → rsS .PC = AxSpinHdB.pac 0x1a → hitW rsS (AxSpinHdB.pac 0) →
    hitW rsS (pcm 0) →
    gprVal rsS AxSpinE8.r2 = spS → gprVal rsS AxSpinE8.r4 = tp → gprVal rsS 9#5 = lkv →
    -- the lock word and lk->cpu
    hitW rsS lkv → hitW rsS (lkv + sign_extend (m := 64) (16#12)) →
    paZ Plk = L.xlLk → ¬ L.xlText (paZ Plk) → dataAtS σi T (accAmo true) lkv 4 Plk →
    dataAtS σi T (.Store .Data) (lkv + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 →
    -- acquire's slots (reloaded here), mycpu's slots
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rsS (spS + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    AxSpinPO1.slot8 σi T L i rsS (AxSpinE8.sp1Of spS + sign_extend (m := 64) AxSpinE8.immRa) Mra →
    AxSpinPO1.slot8 σi T L i rsS (AxSpinE8.sp1Of spS + sign_extend (m := 64) AxSpinE8.immS0) Mms0 →
    dj (paZ Mms0) 8 (paZ Mra) 8 →
    CpuWin L GT i (i, aqKA k b hb n) →
    -- the pins: mycpu's return, acquire's return
    graphValue (gtAdGd GT) (i, aqKm k b hb n + 2) = some (stBytes 8 (AxSpinHdB.pac 0x28)) →
    graphValue (gtAdGd GT) (i, aqKm k b hb n + 5) = some (stBytes 8 ret) →
    jalrTgt 0#12 ret = ret →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq2.KTail (hlc := hlc) L GT nm T satp0 i cpu Ψ k b hb n rsS spS tp ret Pra Ps0 Ps1
        vra vs0 vs1 -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rsS none ibS, aqKh k b hb⟩ Ψ := by
  intro HR Hrmw Hvals Hw8 Hn_ra Hn_s0 Hn_s1 Hn_mra Hn_ms0
    Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hks1 Hls1 Hlt_s1 Hbw_s1
    Hc0 HPC0 Hhit0 HhitM Esp0 Etp0 Es10 Hhv Hhcl Hpl Hntl Hdal Hdcl Hpcl
    Bra Bs0 Bs1 Bmra Bms0 Hdm Hwin Vm Vr Hret
  have Hlen := HR.2.2.2.2.2
  exact AxSpinAq2.tailP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Ψ HΨmid
    k b hb n rsS ibS spS tp ret lkv Pra Ps0 Ps1 Mra Mms0 Pcl Plk qra qs0 qs1 qmra qms0 pn pint hra
    hs0 hs1 hram hs0m kra ks0 ks1 vra vs0 vs1 cra cs0 cs1
    (AxSpinAq2.rowAcquirePOfFull _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR)
    (AxSpinAq1.spinRmwPOf Hrmw) (AxSpinAq1.spinValsPOf Hvals) Hw8 Hn_ra Hn_s0 Hn_s1 Hn_mra Hn_ms0
    Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hks1 Hls1 Hlt_s1 Hbw_s1
    Hc0 HPC0 Hhit0 HhitM Esp0 Etp0 Es10 Hhv Hhcl Hpl Hntl Hdal Hdcl Hpcl
    Bra Bs0 Bs1 Bmra Bms0 Hdm Hwin (fun _ => Vm) (fun _ => Vr) Hret
    (fun _ _ h2 h3 => absurd h3 (by omega))


end pieces

/-! # 3. THE THEOREM -/

section acq
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- THE CALLER'S CONTINUATION of `acquire` (boundary `aqKm k b hb n + 8`, `PC = ret`), stated over
the entry registers `rs0`. -/
def AxSpinAq2.KAcq (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64)
    (i : Agent) (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (b hb : Bool) (n : Nat)
    (rs0 : RegFile) (ret : BitVec 64) (Pra Ps0 Ps1 : BitVec 64) : IProp GF :=
  iprop(∀ (vra' vs0' vs1' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
    ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
      gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
      gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
      vra'.length = 8 ∧ vs0'.length = 8 ∧ vs1'.length = 8 ∧
      gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
      gprVal rs' 9#5 = ldRes false 8 vs1' ∧
      (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
        r.toNat ≠ 10 → r.toNat ≠ 14 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
      graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
      graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
      graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 9#5)) ∧
      graphValue (gtAdGd GT) (i, aqKA k b hb n) = some AxSpinX4.z4 ∧
      graphData (gtAdGd GT) (i, aqKm k b hb n + 4) =
        some (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4))) ∧
      (∃ cls, (AxOpsem.grow (gtAdGd GT) i)[aqKm k b hb n + 4]? =
        some (.LStore false (L.xlLk + 16)
          (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4))) cls)) ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 5) = some vra' ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 6) = some vs0' ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 7) = some vs1'⌝ -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKA k b hb n) (locked nm.xnReg L.xlLk i (i, aqKA k b hb n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKA k b hb n)
      (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, aqKA k b hb n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 4)
      iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, aqKm k b hb n + 4)
        (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)))) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 5)
      iprop(⌜RLfact GT i (paZ Pra) (aqKm k b hb n + 5) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 6)
      iprop(⌜RLfact GT i (paZ Ps0) (aqKm k b hb n + 6) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 7)
      iprop(⌜RLfact GT i (paZ Ps1) (aqKm k b hb n + 7) (stBytes 8 (gprVal rs0 9#5))⌝) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
      ⟨.PHart cpu (.pure ()) rs' none ib', aqKm k b hb n + 8⟩ Ψ)

/-- (Lean-only, stage 2) THE CALLER'S CONTINUATION of `wpdAcquireP`: `KAcq` plus what push_off
hands on (passed through, not dropped): the `sw noff` / `sw intena` row labels (store data), the
second noff read's value `vn`, and push_off's two CONDITIONAL genesis annotations (each under
`AxSpinLd4P.noWrBefore`; the noff reads at `k + 3 + 7` and `tk + 4`). -/
def AxSpinAq2.KAcqP (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64)
    (i : Agent) (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (b hb : Bool) (n : Nat)
    (rs0 : RegFile) (ret : BitVec 64) (Pra Ps0 Ps1 Pn Pi : BitVec 64) : IProp GF :=
  iprop(∀ (vn vra' vs0' vs1' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
    ⌜(∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k + 3 + 8 + (if b then 5 else 0) + 5]? =
        some (.LStore false (paZ Pn) (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) cls)) ∧
      (b = true → ∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k + 3 + 12]? =
        some (.LStore false (paZ Pi) (stBytes 4 0#64) cls)) ∧
      graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 4) = some vn ∧
      ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
      gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
      gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
      vra'.length = 8 ∧ vs0'.length = 8 ∧ vs1'.length = 8 ∧
      gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
      gprVal rs' 9#5 = ldRes false 8 vs1' ∧
      (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
        r.toNat ≠ 10 → r.toNat ≠ 14 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
      graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
      graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
      graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 9#5)) ∧
      graphValue (gtAdGd GT) (i, aqKA k b hb n) = some AxSpinX4.z4 ∧
      graphData (gtAdGd GT) (i, aqKm k b hb n + 4) =
        some (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4))) ∧
      (∃ cls, (AxOpsem.grow (gtAdGd GT) i)[aqKm k b hb n + 4]? =
        some (.LStore false (L.xlLk + 16)
          (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4))) cls)) ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 5) = some vra' ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 6) = some vs0' ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 7) = some vs1'⌝ -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKA k b hb n) (locked nm.xnReg L.xlLk i (i, aqKA k b hb n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKA k b hb n)
      (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, aqKA k b hb n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 4)
      iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, aqKm k b hb n + 4)
        (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)))) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 5)
      iprop(⌜RLfact GT i (paZ Pra) (aqKm k b hb n + 5) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 6)
      iprop(⌜RLfact GT i (paZ Ps0) (aqKm k b hb n + 6) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 7)
      iprop(⌜RLfact GT i (paZ Ps1) (aqKm k b hb n + 7) (stBytes 8 (gprVal rs0 9#5))⌝) -∗
    (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) (k + 3 + 7) (paZ Pn) 4,
      AxAnnot.annotOwn (GF := GF) (i, k + 3 + 7)
        iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 3 + 7)⌝)) -∗
    (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i)
        (k + 3 + 8 + (if b then 5 else 0) + 4) (paZ Pn) 4,
      AxAnnot.annotOwn (GF := GF) (i, k + 3 + 8 + (if b then 5 else 0) + 4)
        iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 3 + 8 + (if b then 5 else 0) + 4)⌝)) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
      ⟨.PHart cpu (.pure ()) rs' none ib', aqKm k b hb n + 8⟩ Ψ)

/-- (Lean-only, P1) THE CALLER'S CONTINUATION of the gate form `wpdAcquireG`: `KAcqP` at
`ret := gprVal rs0 ra` (the caller's `jal` link) whose pure premise FIRST states what acquire's own
`ra` / `s1` reload gates give: both reloads read their spills, so `ra` / `s1` are the entry values
(the old `aqRet` / `aqS1` pins as consequences). -/
def AxSpinAq2.KAcqG (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64)
    (i : Agent) (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (b hb : Bool) (n : Nat)
    (rs0 : RegFile) (Pra Ps0 Ps1 Pn Pi : BitVec 64) : IProp GF :=
  iprop(∀ (vn vra' vs0' vs1' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
    ⌜(vra' = stBytes 8 (gprVal rs0 AxSpinE8.r1) ∧ vs1' = stBytes 8 (gprVal rs0 9#5) ∧
        gprVal rs' AxSpinE8.r1 = gprVal rs0 AxSpinE8.r1 ∧ gprVal rs' 9#5 = gprVal rs0 9#5) ∧
      (∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k + 3 + 8 + (if b then 5 else 0) + 5]? =
        some (.LStore false (paZ Pn) (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) cls)) ∧
      (b = true → ∃ cls, (AxOpsem.grow (gtAdGd GT) i)[k + 3 + 12]? =
        some (.LStore false (paZ Pi) (stBytes 4 0#64) cls)) ∧
      graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 4) = some vn ∧
      ctrlOkSW T satp0 rs' ∧ rs' .PC = gprVal rs0 AxSpinE8.r1 ∧ rs' .tlb = rs0 .tlb ∧
      gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
      gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
      vra'.length = 8 ∧ vs0'.length = 8 ∧ vs1'.length = 8 ∧
      gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
      gprVal rs' 9#5 = ldRes false 8 vs1' ∧
      (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
        r.toNat ≠ 10 → r.toNat ≠ 14 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
      graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
      graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
      graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 9#5)) ∧
      graphValue (gtAdGd GT) (i, aqKA k b hb n) = some AxSpinX4.z4 ∧
      graphData (gtAdGd GT) (i, aqKm k b hb n + 4) =
        some (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4))) ∧
      (∃ cls, (AxOpsem.grow (gtAdGd GT) i)[aqKm k b hb n + 4]? =
        some (.LStore false (L.xlLk + 16)
          (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4))) cls)) ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 5) = some vra' ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 6) = some vs0' ∧
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 7) = some vs1'⌝ -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKA k b hb n) (locked nm.xnReg L.xlLk i (i, aqKA k b hb n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKA k b hb n)
      (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, aqKA k b hb n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 4)
      iprop(True ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, aqKm k b hb n + 4)
        (WeakInterpProj.wbytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)))) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 5)
      iprop(⌜RLfact GT i (paZ Pra) (aqKm k b hb n + 5) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 6)
      iprop(⌜RLfact GT i (paZ Ps0) (aqKm k b hb n + 6) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, aqKm k b hb n + 7)
      iprop(⌜RLfact GT i (paZ Ps1) (aqKm k b hb n + 7) (stBytes 8 (gprVal rs0 9#5))⌝) -∗
    (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) (k + 3 + 7) (paZ Pn) 4,
      AxAnnot.annotOwn (GF := GF) (i, k + 3 + 7)
        iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 3 + 7)⌝)) -∗
    (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i)
        (k + 3 + 8 + (if b then 5 else 0) + 4) (paZ Pn) 4,
      AxAnnot.annotOwn (GF := GF) (i, k + 3 + 8 + (if b then 5 else 0) + 4)
        iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 3 + 8 + (if b then 5 else 0) + 4)⌝)) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
      ⟨.PHart cpu (.pure ()) rs' none ib', aqKm k b hb n + 8⟩ Ψ)

variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxa : acquireText σi T) (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
variable (Htxh : holdingText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxp Htxh HΨmid in
/-- **THE POSITIONAL `acquire` WPd** (design §C.1): from the boundary `k` (acquire's first memory
event) with `PC = acquire`, `a0 = lk` (`lkv`), interrupts off, warm TLB, on a row of shape
`RowAcquire k b hb n …` (push_off's arm `b`, holding's lock bit `hb`, `n` failed spins):
`isLock … RPid -∗ notheld i -∗ KAcq … -∗ WPd`, the continuation `KAcq` at `aqKm k b hb n + 8`
with the claim's `locked` / `RNp` at `aqKA`, the lk->cpu handle at `aqKm + 4` and the reloads.
Pins: Q20' Option V, see the header.

(Lean-only, stage 2) THE P-FORM, on a PREFIX row (`RowAcquireP`, `AxSpinAq1.spinRmwP` /
`spinValsP`; every pin GUARDED by its position, the non-panic arm by `aqKp + 12 < LEN`):
`headP` → `midP` → `tailP` with one `by_cases` at each of acquire's row positions (inside the
pieces) and at the seams `aqKp`; each callee gets its sub-window of the WINDOWED,
RESOURCE-FREE hook `HΨend` over `[k, aqKm + 8]`, which MISSES the designated cut `aq` (`hb = true
→ k' ≠ aqKp + 12`).  That cut (row length `aqKp + 12`, holding's long arm ended after its last
reload, before acquire's `c.bnez a0,panic`) is the premise `Kaq`: for every holding-entry
register file, holding's `KLongEnd` with the `lk->cpu` read's `ORacy` deposit — AxSpinT2h's arm
(D4 readback refutes the off arm / the normal arm is pure).  The continuation `KAcqP` also
receives what push_off hands on (store labels, the noff value, the two conditional genesis
annotations).

(Lean-only, P1) THE GATED CORE / shared proof (`ret` generic): `headG` → `midG` → `tailGr`, every
reload pin replaced by its `AxSpinT2i.Gate` (same slots, against the spilled bytes; acquire's
own return against `stBytes 8 ret`).  `AxSpinAq2.wpdAcquireP` = this ∘ `AxSpinT2i.gateOfPinG`;
`AxSpinAq2.wpdAcquireG` = this at `ret := gprVal rs0 ra` + the `s1` reload gate. -/
theorem AxSpinAq2.wpdAcquireGr (k : Nat) (b hb : Bool) (n : Nat) (rs0 : RegFile) (ib0 : Ibch)
    (ret : BitVec 64)
    (Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi Hra Hs0 Hs1 Hram Hs0m Mra Mms0 Pcl Plk : BitVec 64) :
    -- the row
    RowAcquireP k b hb n (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Qra)
      (paZ Qs0) (paZ Qs1) (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi) (paZ Hra) (paZ Hs0) (paZ Hs1)
      (paZ Hram) (paZ Hs0m) L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0) →
    AxSpinAq1.spinRmwP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n L.xlLk →
    AxSpinAq1.spinValsP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    (∀ p ∈ [paZ Pra, paZ Ps0, paZ Ps1, paZ Qra, paZ Qs0, paZ Qs1, paZ Qmra, paZ Qms0, paZ Hra,
      paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m, paZ Mra, paZ Mms0],
      noRmw8 (AxOpsem.grow (gtAdGd GT) i) p) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    CpuWin L GT i (i, aqKA k b hb n) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0 → hitW rs0 (AxSpinHdB.pac 0) →
    hitW rs0 (pcm 0) →
    -- the lock word (`a0 = lk`) and lk->cpu
    paZ Plk = L.xlLk → ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10) 4 Plk →
    dataAtS σi T (accAmo true) (gprVal rs0 AxSpinE8.r10) 4 Plk → hitW rs0 (gprVal rs0 AxSpinE8.r10) →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    -- acquire's slots (frame `spo sp0`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    -- push_off's slots and cpu fields (frame `spo (spo sp0)`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm24) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm16) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm8) Qs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    -- holding's slots (frame `spo (spo sp0)`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Hram →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    -- mycpu's slots (called from acquire: frame `spo sp0`)
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Mra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Mms0 →
    -- disjointness
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qs1, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Pn, 4),
      (paZ Pi, 4)] →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    dj (paZ Mms0) 8 (paZ Mra) 8 →
    dj (paZ Ps0) 8 (paZ Pra) 8 → dj (paZ Ps1) 8 (paZ Pra) 8 → dj (paZ Ps1) 8 (paZ Ps0) 8 →
    (∀ pa ∈ [paZ Pra, paZ Ps0, paZ Ps1], AxSpinAq2.djOut pa 8 (paZ Qra) (paZ Qs0) (paZ Qs1)
      (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi) (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m)
      L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0)) →
    -- P1: the reload GATES (against the spilled bytes): push_off's (+ its arm, Q20') …
    AxSpinT2i.Gate GT i (k + 3 + 5) (stBytes 8 (AxSpinPO.ppo 0x14)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 3 + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    (b = true → AxSpinT2i.Gate GT i (k + 3 + 10) (stBytes 8 (AxSpinPO.ppo 0x30))) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 2) (stBytes 8 (AxSpinPO.ppo 0x1c)) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 6) (stBytes 8 (AxSpinHdB.pac 0x10)) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 8)
      (stBytes 8 (gprVal rs0 AxSpinE8.r10)) →
    -- … holding's (+ the non-panic arm past the cut) …
    (hb = true →
      AxSpinT2i.Gate GT i (aqKp k b + 7) (stBytes 8 (pch 0x1a)) ∧
      AxSpinT2i.Gate GT i (aqKp k b + 9) (stBytes 8 (AxSpinHdB.pac 0x16)) ∧
      AxSpinT2i.Gate GT i (aqKp k b + 11) (stBytes 8 (gprVal rs0 AxSpinE8.r10)) ∧
      (aqKp k b + 12 < (AxOpsem.grow (gtAdGd GT) i).length →
        ∀ vcpu, graphValue (gtAdGd GT) (i, aqKp k b + 4) = some vcpu →
        hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)) = 0#64)) →
    -- … mycpu's return, acquire's own return
    AxSpinT2i.Gate GT i (aqKm k b hb n + 2) (stBytes 8 (AxSpinHdB.pac 0x28)) →
    AxSpinT2i.Gate GT i (aqKm k b hb n + 5) (stBytes 8 ret) →
    jalrTgt 0#12 ret = ret →
    -- THE DESIGNATED CUT `aq` (row length `aqKp + 12`): the caller's (AxSpinT2h's) arm
    (hb = true → ∀ rsH : RegFile,
      ⊢ KLongEnd (hlc := hlc) L GT nm i Ψ (aqKp k b) rsH Hra Hs0 Hs1 Hram Hs0m
          (fun _ => iprop(True)) (ORacy L GT i (aqKp k b + 4))) →
    -- the row-end hook (stage 2; windowed, resource-free; it does NOT cover the cut)
    (∀ k' : Nat, k ≤ k' → k' ≤ aqKm k b hb n + 8 → (hb = true → k' ≠ aqKp k b + 12) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq2.KAcqP (hlc := hlc) L GT nm T satp0 i cpu Ψ k b hb n rs0 ret Pra Ps0 Ps1 Pn Pi -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hrmw Hvals Hw8 Hnr Hwn Hnn Hwi Hnrcl Hwin Hc0 HPC0 Hhit0 HhitM
    Hpl Hntl HdlL HdlA Hhv Hpcl Hntcl HdcL HdcS Hhcl
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Bhra Bhs0 Bhs1 Bhram Bhs0m Bmra Bms0
    Hdj Hhdj Hdm D10 D20 D21 Hout V14 Vb V30 V1c Vret Vs1 Vh Vm Vr Hret Kaq HΨend
  have N : ∀ p, p ∈ [paZ Pra, paZ Ps0, paZ Ps1, paZ Qra, paZ Qs0, paZ Qs1, paZ Qmra, paZ Qms0,
      paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m, paZ Mra, paZ Mms0] →
      noRmw8 (AxOpsem.grow (gtAdGd GT) i) p := Hnr
  have HR' := HR
  obtain ⟨HRh, HRp, HRhold, -, -⟩ := HR'
  have Hk20 : k + 20 ≤ aqKp k b := by unfold aqKp; split <;> omega
  have Hkh1 : aqKp k b + 1 ≤ aqKh k b hb := by unfold aqKh; split <;> omega
  have Ekm : aqKm k b hb n = aqKh k b hb + (n + 1) := rfl
  have Ehk : hb = true → aqKh k b hb = aqKp k b + 12 := by intro h; subst h; rfl
  -- "no write between" each spill and its reload
  have NW0 := AxSpinAq2.nowrSpillP k b hb n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (paZ Pra) HR
    (by omega)
    (by
      intro it hit
      have hit' : it ∈ [Ritem.RS (paZ Ps0) 8, Ritem.RS (paZ Ps1) 8] := hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hit'
      rcases hit' with rfl | rfl
      · exact D10
      · exact D20)
    (Hout _ (by simp))
  rw [Nat.add_zero] at NW0
  have NW1 := AxSpinAq2.nowrSpillP k b hb n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 (paZ Ps0) HR
    (by omega)
    (by
      intro it hit
      have hit' : it ∈ [Ritem.RS (paZ Ps1) 8] := hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hit'
      subst hit'
      exact D21)
    (Hout _ (by simp))
  have NW2 := AxSpinAq2.nowrSpillP k b hb n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 (paZ Ps1) HR
    (by omega)
    (by
      intro it hit
      have hit' : it ∈ ([] : List Ritem) := hit
      simp only [List.not_mem_nil] at hit')
    (Hout _ (by simp))
  unfold AxSpinAq2.KAcqP
  iintro #Hil Hnh C
  -- ---- the head: prologue, push_off, jal holding ----
  iapply (AxSpinAq2.headG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxp Ψ
    HΨmid k b rs0 ib0 Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi HRh HRp Hw8
    (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp))
    Hwn Hnn Hwi Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Hdj
    V14 Vb V30 V1c Vret Vs1
    (fun k' h1 h2 h3 => HΨend k' h1 (by omega) (fun _ => by omega) h3))
  iintro %vn %rsH %ibH %Hh G1 G2
  obtain ⟨Hlbn, Hlbi, Hgvn, HcH, HPCH, HtlH, EspH, EraH, Ea0H, Es1H, HkeepH, Hgd0, Hgd1, Hgd2⟩ := Hh
  -- row end at aqKp (holding's entry)
  by_cases EP : (AxOpsem.grow (gtAdGd GT) i).length ≤ aqKp k b
  · iclear C
    iclear G1
    iclear G2
    iclear Hnh
    iapply (HΨend _ (by omega) (by omega) (fun _ => by omega) EP _)
  -- the spills' row labels (present: `k + 2 < aqKp < LEN`)
  obtain ⟨vra, cra, Hkra, Hlra⟩ := AxSpinAq2.shStoreP k _ (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) 0
    (paZ Pra) 8 HRh rfl (by omega)
  rw [Nat.add_zero] at Hkra
  obtain ⟨vs0, cs0, Hks0, Hls0⟩ := AxSpinAq2.shStoreP k _ (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) 1
    (paZ Ps0) 8 HRh rfl (by omega)
  obtain ⟨vs1, cs1, Hks1, Hls1⟩ := AxSpinAq2.shStoreP k _ (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) 2
    (paZ Ps1) 8 HRh rfl (by omega)
  have EtpH : gprVal rsH AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 :=
    HkeepH _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the spills' row bytes are the entry registers
  have Evra : vra = stBytes 8 (gprVal rs0 AxSpinE8.r1) := by
    unfold graphData at Hgd0
    rw [AxWp.growLookup _ _ _ _ Hkra] at Hgd0
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hgd0
  have Evs0 : vs0 = stBytes 8 (gprVal rs0 AxSpinE8.r8) := by
    unfold graphData at Hgd1
    rw [AxWp.growLookup _ _ _ _ Hks0] at Hgd1
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hgd1
  have Evs1 : vs1 = stBytes 8 (gprVal rs0 9#5) := by
    unfold graphData at Hgd2
    rw [AxWp.growLookup _ _ _ _ Hks1] at Hgd2
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hgd2
  subst Evra Evs0 Evs1
  -- ---- holding, the panic branch ----
  iapply (AxSpinAq2.midG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxh Ψ
    HΨmid k b hb rsH ibH (gprVal rs0 AxSpinE8.r10) (gprVal rs0 AxSpinE8.r4) Hra Hs0 Hs1 Hram Hs0m
    Pcl Plk HRhold Hw8
    (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp))
    HcH HPCH (hitWAgree rs0 rsH _ HtlH Hhit0) (hitWAgree rs0 rsH _ HtlH HhitM) Ea0H Es1H EraH
    EtpH (hitWAgree rs0 rsH _ HtlH Hhv) (hitWAgree rs0 rsH _ HtlH Hhcl)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhra)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhs0)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhs1)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhram)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhs0m)
    Hhdj HdcL Hntcl Hnrcl HdlL Hntl Vh (fun h => Kaq h rsH)
    (fun k' h1 h2 h3 => HΨend k' (by omega) (AxSpinAq2.midWin k b hb n k' h2).1
      (AxSpinAq2.midWin k b hb n k' h2).2 h3))
  iintro %rsS %ibS %Hm
  obtain ⟨HlhS, HcS, HPCS, HtlS', EspS, Es1S, HkeepS⟩ := Hm
  have HtlS : rsS .tlb = rs0 .tlb := HtlS'.trans HtlH
  have EspS' : gprVal rsS AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := EspS.trans EspH
  have EtpS : gprVal rsS AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 :=
    (HkeepS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans EtpH
  -- ---- the tail: the spin, mycpu, the lk->cpu store, the reloads, c.ret ----
  iapply (AxSpinAq2.tailGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Ψ HΨmid
    k b hb n rsS ibS (spo (gprVal rs0 AxSpinE8.r2)) (gprVal rs0 AxSpinE8.r4) ret
    (gprVal rs0 AxSpinE8.r10) Pra Ps0 Ps1 Mra Mms0 Pcl Plk _ _ _ _ _ _ _ _ _ _ _ _ k (k + 1) (k + 2)
    _ _ _ cra cs0 cs1 HR Hrmw Hvals Hw8
    (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp))
    Hkra Hlra (by omega) NW0
    Hks0 Hls0 (by omega) NW1
    Hks1 Hls1 (by omega) NW2
    HcS HPCS (hitWAgree rs0 rsS _ HtlS Hhit0) (hitWAgree rs0 rsS _ HtlS HhitM) EspS' EtpS Es1S
    (hitWAgree rs0 rsS _ HtlS Hhv) (hitWAgree rs0 rsS _ HtlS Hhcl) Hpl Hntl HdlA HdcS Hpcl
    (slot8Tlb _ _ _ _ _ _ _ _ HtlS Bra) (slot8Tlb _ _ _ _ _ _ _ _ HtlS Bs0)
    (slot8Tlb _ _ _ _ _ _ _ _ HtlS Bs1)
    (slot8Tlb _ _ _ _ _ _ _ _ HtlS Bmra) (slot8Tlb _ _ _ _ _ _ _ _ HtlS Bms0)
    Hdm Hwin Vm Vr Hret
    (fun k' h1 h2 h3 => HΨend k' (by omega) h2 (fun hh => by have := Ehk hh; omega) h3)) $$ Hil Hnh
  unfold AxSpinAq2.KTail
  iintro %vra' %vs0' %vs1' %rs' %ib' %Ht HLK HNp HDep H5 H6 H7
  obtain ⟨Hc', HPC', Htl', Esp', Ea0', Hl1, Hl2, Hl3, Era', Es0', Es1', Hkeep', Hz, Hgd4, Hlb4,
    Hgv5, Hgv6, Hgv7⟩ := Ht
  iapply C $$ %vn %vra' %vs0' %vs1' %rs' %ib' [] HLK HNp HDep H5 H6 H7 G1 G2
  ipureintro
  refine ⟨Hlbn, Hlbi, Hgvn, Hc', HPC', Htl'.trans HtlS, ?_, Ea0', Hl1, Hl2, Hl3, Era', Es0',
    Es1', ?_, Hgd0, Hgd1, Hgd2, Hz, Hgd4, Hlb4, Hgv5, Hgv6, Hgv7⟩
  · -- sp restored
    rw [Esp']
    unfold spo
    rw [BitVec.add_assoc,
      show sign_extend (m := 64) (sign_extend (m := 12) (32#6)) +
        sign_extend (m := 64) (caddi16spImm 2#6) = 0#64 by decide]
    exact BitVec.add_zero _
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr14 Hr15
    rw [Hkeep' r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15, HkeepS r Hr1 Hr2 Hr8 Hr9 Hr10 Hr14 Hr15]
    exact HkeepH r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15

include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxp Htxh HΨmid in
/-- **THE POSITIONAL `acquire` WPd** (design §C.1): from the boundary `k` (acquire's first memory
event) with `PC = acquire`, `a0 = lk` (`lkv`), interrupts off, warm TLB, on a row of shape
`RowAcquire k b hb n …` (push_off's arm `b`, holding's lock bit `hb`, `n` failed spins):
`isLock … RPid -∗ notheld i -∗ KAcq … -∗ WPd`, the continuation `KAcq` at `aqKm k b hb n + 8`
with the claim's `locked` / `RNp` at `aqKA`, the lk->cpu handle at `aqKm + 4` and the reloads.
Pins: Q20' Option V, see the header.

(Lean-only, stage 2) THE P-FORM, on a PREFIX row (`RowAcquireP`, `AxSpinAq1.spinRmwP` /
`spinValsP`; every pin GUARDED by its position, the non-panic arm by `aqKp + 12 < LEN`):
`headP` → `midP` → `tailP` with one `by_cases` at each of acquire's row positions (inside the
pieces) and at the seams `aqKp`; each callee gets its sub-window of the WINDOWED,
RESOURCE-FREE hook `HΨend` over `[k, aqKm + 8]`, which MISSES the designated cut `aq` (`hb = true
→ k' ≠ aqKp + 12`).  That cut (row length `aqKp + 12`, holding's long arm ended after its last
reload, before acquire's `c.bnez a0,panic`) is the premise `Kaq`: for every holding-entry
register file, holding's `KLongEnd` with the `lk->cpu` read's `ORacy` deposit — AxSpinT2h's arm
(D4 readback refutes the off arm / the normal arm is pure).  The continuation `KAcqP` also
receives what push_off hands on (store labels, the noff value, the two conditional genesis
annotations).  P1: the corollary of `AxSpinAq2.wpdAcquireGr` via `AxSpinT2i.gateOfPinG`. -/
theorem AxSpinAq2.wpdAcquireP (k : Nat) (b hb : Bool) (n : Nat) (rs0 : RegFile) (ib0 : Ibch)
    (ret : BitVec 64)
    (Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi Hra Hs0 Hs1 Hram Hs0m Mra Mms0 Pcl Plk : BitVec 64) :
    -- the row
    RowAcquireP k b hb n (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Qra)
      (paZ Qs0) (paZ Qs1) (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi) (paZ Hra) (paZ Hs0) (paZ Hs1)
      (paZ Hram) (paZ Hs0m) L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0) →
    AxSpinAq1.spinRmwP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n L.xlLk →
    AxSpinAq1.spinValsP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    (∀ p ∈ [paZ Pra, paZ Ps0, paZ Ps1, paZ Qra, paZ Qs0, paZ Qs1, paZ Qmra, paZ Qms0, paZ Hra,
      paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m, paZ Mra, paZ Mms0],
      noRmw8 (AxOpsem.grow (gtAdGd GT) i) p) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    CpuWin L GT i (i, aqKA k b hb n) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0 → hitW rs0 (AxSpinHdB.pac 0) →
    hitW rs0 (pcm 0) →
    -- the lock word (`a0 = lk`) and lk->cpu
    paZ Plk = L.xlLk → ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10) 4 Plk →
    dataAtS σi T (accAmo true) (gprVal rs0 AxSpinE8.r10) 4 Plk → hitW rs0 (gprVal rs0 AxSpinE8.r10) →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    -- acquire's slots (frame `spo sp0`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    -- push_off's slots and cpu fields (frame `spo (spo sp0)`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm24) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm16) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm8) Qs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    -- holding's slots (frame `spo (spo sp0)`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Hram →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    -- mycpu's slots (called from acquire: frame `spo sp0`)
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Mra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Mms0 →
    -- disjointness
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qs1, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Pn, 4),
      (paZ Pi, 4)] →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    dj (paZ Mms0) 8 (paZ Mra) 8 →
    dj (paZ Ps0) 8 (paZ Pra) 8 → dj (paZ Ps1) 8 (paZ Pra) 8 → dj (paZ Ps1) 8 (paZ Ps0) 8 →
    (∀ pa ∈ [paZ Pra, paZ Ps0, paZ Ps1], AxSpinAq2.djOut pa 8 (paZ Qra) (paZ Qs0) (paZ Qs1)
      (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi) (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m)
      L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0)) →
    -- the value pins (Q20' Option V), GUARDED by position: push_off's …
    (k + 3 + 5 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14))) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 3 + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    (b = true → k + 3 + 10 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30))) →
    (k + 3 + 8 + (if b then 5 else 0) + 2 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 2) =
        some (stBytes 8 (AxSpinPO.ppo 0x1c))) →
    (k + 3 + 8 + (if b then 5 else 0) + 6 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 6) =
        some (stBytes 8 (AxSpinHdB.pac 0x10))) →
    (k + 3 + 8 + (if b then 5 else 0) + 8 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 8) =
        some (stBytes 8 (gprVal rs0 AxSpinE8.r10))) →
    -- … holding's (returns, s1 reload, the non-panic arm past the cut) …
    (hb = true →
      (aqKp k b + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
        graphValue (gtAdGd GT) (i, aqKp k b + 7) = some (stBytes 8 (pch 0x1a))) ∧
      (aqKp k b + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
        graphValue (gtAdGd GT) (i, aqKp k b + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16))) ∧
      (aqKp k b + 11 < (AxOpsem.grow (gtAdGd GT) i).length →
        graphValue (gtAdGd GT) (i, aqKp k b + 11) = some (stBytes 8 (gprVal rs0 AxSpinE8.r10))) ∧
      (aqKp k b + 12 < (AxOpsem.grow (gtAdGd GT) i).length →
        ∀ vcpu, graphValue (gtAdGd GT) (i, aqKp k b + 4) = some vcpu →
        hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)) = 0#64)) →
    -- … mycpu's return, acquire's own return
    (aqKm k b hb n + 2 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 2) = some (stBytes 8 (AxSpinHdB.pac 0x28))) →
    (aqKm k b hb n + 5 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, aqKm k b hb n + 5) = some (stBytes 8 ret)) →
    jalrTgt 0#12 ret = ret →
    -- THE DESIGNATED CUT `aq` (row length `aqKp + 12`): the caller's (AxSpinT2h's) arm
    (hb = true → ∀ rsH : RegFile,
      ⊢ KLongEnd (hlc := hlc) L GT nm i Ψ (aqKp k b) rsH Hra Hs0 Hs1 Hram Hs0m
          (fun _ => iprop(True)) (ORacy L GT i (aqKp k b + 4))) →
    -- the row-end hook (stage 2; windowed, resource-free; it does NOT cover the cut)
    (∀ k' : Nat, k ≤ k' → k' ≤ aqKm k b hb n + 8 → (hb = true → k' ≠ aqKp k b + 12) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq2.KAcqP (hlc := hlc) L GT nm T satp0 i cpu Ψ k b hb n rs0 ret Pra Ps0 Ps1 Pn Pi -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hrmw Hvals Hw8 Hnr Hwn Hnn Hwi Hnrcl Hwin Hc0 HPC0 Hhit0 HhitM
    Hpl Hntl HdlL HdlA Hhv Hpcl Hntcl HdcL HdcS Hhcl
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Bhra Bhs0 Bhs1 Bhram Bhs0m Bmra Bms0
    Hdj Hhdj Hdm D10 D20 D21 Hout V14 Vb V30 V1c Vret Vs1 Vh Vm Vr Hret Kaq HΨend
  exact AxSpinAq2.wpdAcquireGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm
    Htxp Htxh Ψ HΨmid k b hb n rs0 ib0 ret Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi Hra Hs0 Hs1
    Hram Hs0m Mra Mms0 Pcl Plk HR Hrmw Hvals Hw8 Hnr Hwn Hnn Hwi Hnrcl Hwin Hc0 HPC0 Hhit0 HhitM
    Hpl Hntl HdlL HdlA Hhv Hpcl Hntcl HdcL HdcS Hhcl
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Bhra Bhs0 Bhs1 Bhram Bhs0m Bmra Bms0
    Hdj Hhdj Hdm D10 D20 D21 Hout (AxSpinT2i.gateOfPinG V14) Vb
    (fun h => AxSpinT2i.gateOfPinG (V30 h)) (AxSpinT2i.gateOfPinG V1c) (AxSpinT2i.gateOfPinG Vret)
    (AxSpinT2i.gateOfPinG Vs1)
    (fun h => ⟨AxSpinT2i.gateOfPinG (Vh h).1, AxSpinT2i.gateOfPinG (Vh h).2.1,
      AxSpinT2i.gateOfPinG (Vh h).2.2.1, (Vh h).2.2.2⟩)
    (AxSpinT2i.gateOfPinG Vm) (AxSpinT2i.gateOfPinG Vr) Hret Kaq HΨend

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxp Htxh HΨmid in
/-- (Lean-only, P1) **THE GATE FORM of the positional `acquire` WPd** (what ApB's segment proof
calls): `AxSpinAq2.wpdAcquireP`'s premises with EVERY reload pin replaced by its
`AxSpinT2i.Gate` (a row that continues past the reload read the spill) — push_off's five
(`k + 3 + 5`, `b → k + 3 + 10`, `tk + 2`, `tk + 6`, `tk + 8`), holding's three (`hb →` `aqKp + 7`,
`+ 9`, `+ 11`), mycpu's (`aqKm + 2`), acquire's own `ra` reload (`aqKm + 5`, against the ENTRY
`ra`: no `ret` argument, `ret := gprVal rs0 ra`, the caller's `jal` link) and acquire's `s1`
reload (`aqKm + 7`, against the spill's own row data `graphData (i, k + 2)`, as T2f's
`rlExp .aqS1`); `Kaq` (the designated cut `aq`) and the hook unchanged; continuation
`AxSpinAq2.KAcqG` (`ra` / `s1` restored, `PC = gprVal rs0 ra`).  Proof: `wpdAcquireGr`, then in
its continuation (row position `aqKm + 8`) a wrong `ra` / `s1` reload value puts the row end at
`aqKm + 6` / `aqKm + 8` (the gate), and the arm is REFUTED by the reload's `RLfact` read back
past the row end (`AxSpinT2i.wpdEnd1` + `AxSpinT2i.rlFactEq`). -/
theorem AxSpinAq2.wpdAcquireG (k : Nat) (b hb : Bool) (n : Nat) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi Hra Hs0 Hs1 Hram Hs0m Mra Mms0 Pcl Plk : BitVec 64) :
    -- the row
    RowAcquireP k b hb n (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Qra)
      (paZ Qs0) (paZ Qs1) (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi) (paZ Hra) (paZ Hs0) (paZ Hs1)
      (paZ Hram) (paZ Hs0m) L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0) →
    AxSpinAq1.spinRmwP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n L.xlLk →
    AxSpinAq1.spinValsP (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    (∀ p ∈ [paZ Pra, paZ Ps0, paZ Ps1, paZ Qra, paZ Qs0, paZ Qs1, paZ Qmra, paZ Qms0, paZ Hra,
      paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m, paZ Mra, paZ Mms0],
      noRmw8 (AxOpsem.grow (gtAdGd GT) i) p) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    CpuWin L GT i (i, aqKA k b hb n) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0 → hitW rs0 (AxSpinHdB.pac 0) →
    hitW rs0 (pcm 0) →
    -- the lock word (`a0 = lk`) and lk->cpu
    paZ Plk = L.xlLk → ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10) 4 Plk →
    dataAtS σi T (accAmo true) (gprVal rs0 AxSpinE8.r10) 4 Plk → hitW rs0 (gprVal rs0 AxSpinE8.r10) →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    -- acquire's slots (frame `spo sp0`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    -- push_off's slots and cpu fields (frame `spo (spo sp0)`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm24) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm16) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm8) Qs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    -- holding's slots (frame `spo (spo sp0)`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Hram →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    -- mycpu's slots (called from acquire: frame `spo sp0`)
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Mra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Mms0 →
    -- disjointness
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qs1, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Pn, 4),
      (paZ Pi, 4)] →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    dj (paZ Mms0) 8 (paZ Mra) 8 →
    dj (paZ Ps0) 8 (paZ Pra) 8 → dj (paZ Ps1) 8 (paZ Pra) 8 → dj (paZ Ps1) 8 (paZ Ps0) 8 →
    (∀ pa ∈ [paZ Pra, paZ Ps0, paZ Ps1], AxSpinAq2.djOut pa 8 (paZ Qra) (paZ Qs0) (paZ Qs1)
      (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi) (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m)
      L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0)) →
    -- P1: the reload GATES (against the spilled bytes): push_off's (+ its arm, Q20') …
    AxSpinT2i.Gate GT i (k + 3 + 5) (stBytes 8 (AxSpinPO.ppo 0x14)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 3 + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    (b = true → AxSpinT2i.Gate GT i (k + 3 + 10) (stBytes 8 (AxSpinPO.ppo 0x30))) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 2) (stBytes 8 (AxSpinPO.ppo 0x1c)) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 6) (stBytes 8 (AxSpinHdB.pac 0x10)) →
    AxSpinT2i.Gate GT i (k + 3 + 8 + (if b then 5 else 0) + 8)
      (stBytes 8 (gprVal rs0 AxSpinE8.r10)) →
    -- … holding's (+ the non-panic arm past the cut) …
    (hb = true →
      AxSpinT2i.Gate GT i (aqKp k b + 7) (stBytes 8 (pch 0x1a)) ∧
      AxSpinT2i.Gate GT i (aqKp k b + 9) (stBytes 8 (AxSpinHdB.pac 0x16)) ∧
      AxSpinT2i.Gate GT i (aqKp k b + 11) (stBytes 8 (gprVal rs0 AxSpinE8.r10)) ∧
      (aqKp k b + 12 < (AxOpsem.grow (gtAdGd GT) i).length →
        ∀ vcpu, graphValue (gtAdGd GT) (i, aqKp k b + 4) = some vcpu →
        hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)) = 0#64)) →
    -- … mycpu's return, acquire's own return
    AxSpinT2i.Gate GT i (aqKm k b hb n + 2) (stBytes 8 (AxSpinHdB.pac 0x28)) →
    AxSpinT2i.Gate GT i (aqKm k b hb n + 5) (stBytes 8 (gprVal rs0 AxSpinE8.r1)) →
    -- … acquire's s1 reload, against its spill's own row data (T2f `rlExp .aqS1 = wd row 2`)
    (∀ vw, graphData (gtAdGd GT) (i, k + 2) = some vw →
      AxSpinT2i.Gate GT i (aqKm k b hb n + 7) vw) →
    -- acquire's return address is the caller's `jal` link (2-aligned)
    jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = gprVal rs0 AxSpinE8.r1 →
    -- THE DESIGNATED CUT `aq` (row length `aqKp + 12`): the caller's (AxSpinT2h's) arm
    (hb = true → ∀ rsH : RegFile,
      ⊢ KLongEnd (hlc := hlc) L GT nm i Ψ (aqKp k b) rsH Hra Hs0 Hs1 Hram Hs0m
          (fun _ => iprop(True)) (ORacy L GT i (aqKp k b + 4))) →
    -- the row-end hook (stage 2; windowed, resource-free; it does NOT cover the cut)
    (∀ k' : Nat, k ≤ k' → k' ≤ aqKm k b hb n + 8 → (hb = true → k' ≠ aqKp k b + 12) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq2.KAcqG (hlc := hlc) L GT nm T satp0 i cpu Ψ k b hb n rs0 Pra Ps0 Ps1 Pn Pi -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hrmw Hvals Hw8 Hnr Hwn Hnn Hwi Hnrcl Hwin Hc0 HPC0 Hhit0 HhitM
    Hpl Hntl HdlL HdlA Hhv Hpcl Hntcl HdcL HdcS Hhcl
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Bhra Bhs0 Bhs1 Bhram Bhs0m Bmra Bms0
    Hdj Hhdj Hdm D10 D20 D21 Hout V14 Vb V30 V1c Vret Vs1 Vh Vm Vr Gs1 Hret Kaq HΨend
  have HRt := HR.2.2.2.2
  iintro #Hil Hnh C
  iapply (AxSpinAq2.wpdAcquireGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm
    Htxp Htxh Ψ HΨmid k b hb n rs0 ib0 (gprVal rs0 AxSpinE8.r1) Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0
    Pn Pi Hra Hs0 Hs1 Hram Hs0m Mra Mms0 Pcl Plk HR Hrmw Hvals Hw8 Hnr Hwn Hnn Hwi Hnrcl Hwin
    Hc0 HPC0 Hhit0 HhitM Hpl Hntl HdlL HdlA Hhv Hpcl Hntcl HdcL HdcS Hhcl
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Bhra Bhs0 Bhs1 Bhram Bhs0m Bmra Bms0
    Hdj Hhdj Hdm D10 D20 D21 Hout V14 Vb V30 V1c Vret Vs1 Vh Vm Vr Hret Kaq HΨend) $$ Hil Hnh
  unfold AxSpinAq2.KAcqP
  iintro %vn %vra' %vs0' %vs1' %rs' %ib' %Hp HLK HNp HDep H5 H6 H7 G1 G2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, Era', -, Es1', -, -, -, Hgd2, -, -, -, Hgv5, -,
    Hgv7⟩ := id Hp
  by_cases Hv5 : vra' = stBytes 8 (gprVal rs0 AxSpinE8.r1)
  · by_cases Hv7 : vs1' = stBytes 8 (gprVal rs0 9#5)
    · unfold AxSpinAq2.KAcqG
      iapply C $$ %vn %vra' %vs0' %vs1' %rs' %ib' [] HLK HNp HDep H5 H6 H7 G1 G2
      ipureintro
      refine ⟨⟨Hv5, Hv7, ?_, ?_⟩, Hp⟩
      · rw [Era', Hv5, AxSpinE8.ldResStBytes8]
      · rw [Es1', Hv7, AxSpinE8.ldResStBytes8]
    · -- a wrong s1 reload: the row ends at aqKm + 8, refuted by its RLfact
      have Hend := AxSpinT2i.lenOfGate (Gs1 _ Hgd2) Hgv7 Hv7
      obtain ⟨lb7, Hlb7, Hsh7⟩ := HRt 7 (.RL (paZ Ps1) 8) rfl (AxSpinAq2.gvLt _ _ _ _ Hgv7)
      iclear C
      iclear HLK
      iclear HNp
      iclear HDep
      iclear H5
      iclear H6
      iclear G1
      iclear G2
      iapply (AxSpinT2i.wpdEnd1 L GT nm i (aqKm k b hb n + 8) (by omega)
        (i, aqKm k b hb n + 7) rfl _ Ψ
        (fun HF => absurd (AxSpinT2i.rlFactEq GT Hcons i (aqKm k b hb n + 7) (paZ Ps1) _ vs1'
          ⟨lb7, Hlb7, Hsh7⟩ (AxSpinPO4.stBytes8Len _) Hgv7 HF) Hv7) _) $$ H7
  · -- a wrong ra reload: the row ends at aqKm + 6, refuted by its RLfact
    have Hend := AxSpinT2i.lenOfGate Vr Hgv5 Hv5
    obtain ⟨lb5, Hlb5, Hsh5⟩ := HRt 5 (.RL (paZ Pra) 8) rfl (AxSpinAq2.gvLt _ _ _ _ Hgv5)
    iclear C
    iclear HLK
    iclear HNp
    iclear HDep
    iclear H6
    iclear H7
    iclear G1
    iclear G2
    iapply (AxSpinT2i.wpdEnd1 L GT nm i (aqKm k b hb n + 8) (by omega)
      (i, aqKm k b hb n + 5) rfl _ Ψ
      (fun HF => absurd (AxSpinT2i.rlFactEq GT Hcons i (aqKm k b hb n + 5) (paZ Pra) _ vra'
        ⟨lb5, Hlb5, Hsh5⟩ (AxSpinPO4.stBytes8Len _) Hgv5 HF) Hv5) _) $$ H5

include HL Hcons hmode hasid hppn Hfix Htxa Htxm Htxp Htxh HΨmid in
/-- **THE POSITIONAL `acquire` WPd** (design §C.1): from the boundary `k` (acquire's first memory
event) with `PC = acquire`, `a0 = lk` (`lkv`), interrupts off, warm TLB, on a row of shape
`RowAcquire k b hb n …` (push_off's arm `b`, holding's lock bit `hb`, `n` failed spins):
`isLock … RPid -∗ notheld i -∗ KAcq … -∗ WPd`, the continuation `KAcq` at `aqKm k b hb n + 8`
with the claim's `locked` / `RNp` at `aqKA`, the lk->cpu handle at `aqKm + 4` and the reloads.
Pins: Q20' Option V, see the header.  Stage 2: the full-row corollary of
`AxSpinAq2.wpdAcquireP` (hook and the cut premise `Kaq` vacuous: `aqKm + 8 < LEN`). -/
theorem AxSpinAq2.wpdAcquire (k : Nat) (b hb : Bool) (n : Nat) (rs0 : RegFile) (ib0 : Ibch)
    (ret : BitVec 64)
    (Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi Hra Hs0 Hs1 Hram Hs0m Mra Mms0 Pcl Plk : BitVec 64) :
    -- the row
    RowAcquire k b hb n (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Qra)
      (paZ Qs0) (paZ Qs1) (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi) (paZ Hra) (paZ Hs0) (paZ Hs1)
      (paZ Hram) (paZ Hs0m) L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0) →
    AxSpinAq1.spinRmw (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n L.xlLk →
    spinVals (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    (∀ p ∈ [paZ Pra, paZ Ps0, paZ Ps1, paZ Qra, paZ Qs0, paZ Qs1, paZ Qmra, paZ Qms0, paZ Hra,
      paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m, paZ Mra, paZ Mms0],
      noRmw8 (AxOpsem.grow (gtAdGd GT) i) p) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ Pcl) m →
      m ≠ 8) →
    CpuWin L GT i (i, aqKA k b hb n) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0 → hitW rs0 (AxSpinHdB.pac 0) →
    hitW rs0 (pcm 0) →
    -- the lock word (`a0 = lk`) and lk->cpu
    paZ Plk = L.xlLk → ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10) 4 Plk →
    dataAtS σi T (accAmo true) (gprVal rs0 AxSpinE8.r10) 4 Plk → hitW rs0 (gprVal rs0 AxSpinE8.r10) →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    -- acquire's slots (frame `spo sp0`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    -- push_off's slots and cpu fields (frame `spo (spo sp0)`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm24) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm16) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinPO3.imm8) Qs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    -- holding's slots (frame `spo (spo sp0)`)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Hram →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    -- mycpu's slots (called from acquire: frame `spo sp0`)
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Mra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Mms0 →
    -- disjointness
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qs1, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Pn, 4),
      (paZ Pi, 4)] →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    dj (paZ Mms0) 8 (paZ Mra) 8 →
    dj (paZ Ps0) 8 (paZ Pra) 8 → dj (paZ Ps1) 8 (paZ Pra) 8 → dj (paZ Ps1) 8 (paZ Ps0) 8 →
    (∀ pa ∈ [paZ Pra, paZ Ps0, paZ Ps1], AxSpinAq2.djOut pa 8 (paZ Qra) (paZ Qs0) (paZ Qs1)
      (paZ Qmra) (paZ Qms0) (paZ Pn) (paZ Pi) (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m)
      L.xlLk (L.xlLk + 16) (paZ Mra) (paZ Mms0)) →
    -- the value pins (Q20' Option V): push_off's …
    graphValue (gtAdGd GT) (i, k + 3 + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 3 + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    (b = true → graphValue (gtAdGd GT) (i, k + 3 + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30))) →
    graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 2) =
      some (stBytes 8 (AxSpinPO.ppo 0x1c)) →
    graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 6) =
      some (stBytes 8 (AxSpinHdB.pac 0x10)) →
    graphValue (gtAdGd GT) (i, k + 3 + 8 + (if b then 5 else 0) + 8) =
      some (stBytes 8 (gprVal rs0 AxSpinE8.r10)) →
    -- … holding's (returns, s1 reload, the non-panic arm) …
    (hb = true →
      graphValue (gtAdGd GT) (i, aqKp k b + 7) = some (stBytes 8 (pch 0x1a)) ∧
      graphValue (gtAdGd GT) (i, aqKp k b + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16)) ∧
      graphValue (gtAdGd GT) (i, aqKp k b + 11) = some (stBytes 8 (gprVal rs0 AxSpinE8.r10)) ∧
      ∀ vcpu, graphValue (gtAdGd GT) (i, aqKp k b + 4) = some vcpu →
        hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)) = 0#64) →
    -- … mycpu's return, acquire's own return
    graphValue (gtAdGd GT) (i, aqKm k b hb n + 2) = some (stBytes 8 (AxSpinHdB.pac 0x28)) →
    graphValue (gtAdGd GT) (i, aqKm k b hb n + 5) = some (stBytes 8 ret) →
    jalrTgt 0#12 ret = ret →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq2.KAcq (hlc := hlc) L GT nm T satp0 i cpu Ψ k b hb n rs0 ret Pra Ps0 Ps1 -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hrmw Hvals Hw8 Hnr Hwn Hnn Hwi Hnrcl Hwin Hc0 HPC0 Hhit0 HhitM
    Hpl Hntl HdlL HdlA Hhv Hpcl Hntcl HdcL HdcS Hhcl
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Bhra Bhs0 Bhs1 Bhram Bhs0m Bmra Bms0
    Hdj Hhdj Hdm D10 D20 D21 Hout V14 Vb V30 V1c Vret Vs1 Vh Vm Vr Hret
  have Hlen := HR.2.2.2.2.2
  have Hc12 : hb = true → aqKp k b + 12 ≤ aqKm k b hb n + 8 := by
    intro h; subst h; unfold aqKm aqKh; simp only [↓reduceIte]; omega
  iintro #Hil Hnh C
  iapply (AxSpinAq2.wpdAcquireP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm
    Htxp Htxh Ψ HΨmid k b hb n rs0 ib0 ret Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi Hra Hs0 Hs1
    Hram Hs0m Mra Mms0 Pcl Plk
    (AxSpinAq2.rowAcquirePOfFull _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR)
    (AxSpinAq1.spinRmwPOf Hrmw) (AxSpinAq1.spinValsPOf Hvals) Hw8 Hnr Hwn Hnn Hwi Hnrcl Hwin
    Hc0 HPC0 Hhit0 HhitM Hpl Hntl HdlL HdlA Hhv Hpcl Hntcl HdcL HdcS Hhcl
    Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Bhra Bhs0 Bhs1 Bhram Bhs0m Bmra Bms0
    Hdj Hhdj Hdm D10 D20 D21 Hout (fun _ => V14) Vb (fun h _ => V30 h) (fun _ => V1c)
    (fun _ => Vret) (fun _ => Vs1)
    (fun h => ⟨fun _ => (Vh h).1, fun _ => (Vh h).2.1, fun _ => (Vh h).2.2.1,
      fun _ => (Vh h).2.2.2⟩)
    (fun _ => Vm) (fun _ => Vr) Hret
    (fun h _ => by
      have := Hc12 h
      unfold KLongEnd
      iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp
      exact absurd Hp.1 (by omega))
    (fun _ _ h2 _ h3 => absurd h3 (by omega))) $$ Hil Hnh
  unfold AxSpinAq2.KAcqP
  iintro %vn %vra' %vs0' %vs1' %rs' %ib' %Hp HLK HNp HDep H5 H6 H7 - -
  unfold AxSpinAq2.KAcq
  iapply C $$ %vra' %vs0' %vs1' %rs' %ib' [] HLK HNp HDep H5 H6 H7
  ipureintro
  exact Hp.2.2.2


end acq

end Weak
