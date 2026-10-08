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
(+ 1 local macro).
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
/-- acquire + 0x00 … + 0x12: the prologue, `push_off`, `c.mv a0,s1`, `jal holding`; continuation
at holding's entry (boundary `aqKp k b`). -/
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
  obtain ⟨HdaS_ra, _, Hh_ra, Hpr_ra, _⟩ := Bra
  obtain ⟨HdaS_s0, _, Hh_s0, Hpr_s0, _⟩ := Bs0
  obtain ⟨HdaS_s1, _, Hh_s1, Hpr_s1, _⟩ := Bs1
  obtain ⟨T00, T02, T04, T06, T08, T0a, T0c, T10, T12, -⟩ := Htxa
  have Hkp : k + 20 ≤ aqKp k b := by unfold aqKp; split <;> omega
  have Etk : k + 3 + 8 + (if b then 5 else 0) + 9 = aqKp k b := by unfold aqKp; split <;> omega
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS := XxSt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  iintro C
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
  -- ---- push_off, at k+3 (continuation at aqKp) ----
  have WPo := wpdPushOff L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxp Ψ
    HΨmid (k + 3) b rs7 ib7 (AxSpinHdB.pac 0x10) Qra Qs0 Qs1 Qmra Qms0 Pn Pi HRp
    (by rw [Etk]; exact Hlen) Hw8 Hq1 Hq2 Hq3 Hq4 Hq5 Hwn Hnn Hwi
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
    Hdj V14 Vb V30 V1c Vret (by decide)
  rw [Etk] at WPo
  iapply WPo
  iintro %vn0 %vn %vra' %vs0' %vs1' %rs8 %ib8 %Hp - - -
  obtain ⟨Hc8, HPC8, Htl8', -, Esp8, -, -, -, Es18, Hkeep8, -, -, -, -, -, -, -, -, -, -,
    Hgv8⟩ := Hp
  have Htl8 : rs8 .tlb = rs0 .tlb := Htl8'.trans Htl7
  have Es1 : gprVal rs8 9#5 = gprVal rs0 AxSpinE8.r10 := by
    rw [show (9#5 : BitVec 5) = AxSpinPOr.r9 from rfl, Es18,
      Option.some.inj (Hgv8.symm.trans Vs1), AxSpinE8.ldResStBytes8]
  -- ---- + 0x10: c.mv a0,s1 (aqKp) ----
  have Hc9 := certAdd (ctrlOkSW T satp0) rs8 (AxSpinHdB.pac 0x10) true 9#5 0#5 10#5 (by decide)
  iapply (XR _ rs8 (aqKp k b) (AxSpinHdB.pac 0x10) true a10 _ _
    (retxRefl cpu rs8 (aqKp k b) ib8) Hc8 HPC8
    (hitWSvpn rs8 (AxSpinHdB.pac 0x10) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rs0 rs8 _ Htl8 Hhit0))
    (twa8526 σi T satp0 _ T10) (AxSpinE8.owOkSome 10#5 _ (by decide))
    (rfFOfRf0 _ (rf0Add _ _ _)) Hc9 Hlen)
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
    (AxSpinPOx.rfFJal 2097032#21 (.Regidx 1#5)) Hcj2 Hlen)
  iintro %rs10 %ib10 %HG10
  have HF10 := stepRegs T satp0 _ rs9 _ _ _ _ _ rs10 HF9 HG10
  iapply C $$ %rs10 %ib10
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HG10, gbPc T satp0 _ _ _ _ _ _ HG10,
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
/-- acquire's call of holding (boundary `aqKp k b`, `PC = holding`) through the not-taken panic
branch (boundary `aqKh k b hb`, `PC = acquire + 0x1a`), both arms of `hb`; the long arm's
non-panic value pin makes `a0 = 0`. -/
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
  obtain ⟨Hd1, Hd2, Hd3, Hp1, Hn1⟩ := Bra
  obtain ⟨Hd4, Hd5, Hd6, Hp2, Hn2⟩ := Bs0
  obtain ⟨Hd7, Hd8, Hd9, Hp3, Hn3⟩ := Bs1
  obtain ⟨Hd10, Hd11, Hd12, Hp4, Hn4⟩ := Bram
  obtain ⟨Hd13, Hd14, Hd15, Hp5, Hn5⟩ := Bs0m
  have W := holdingFromAcquire' L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm
    Htxh Ψ HΨmid (aqKp k b) rsH ibH hb L.xlLk (L.xlLk + 16) Hra Hs0 Hs1 Hram Hs0m Pcl Plk HR Hw8
    H1 H2 H3 H4 H5 Hc HPC
    (hitWSvpn rsH (pch 0) (AxSpinHdB.pac 0) (by decide) Hhit) HhitM
    (by rw [Ea0, AxSpinAq2.addZ]; exact Hhlk) (by rw [Ea0]; exact Hhcl)
    Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
    (by
      split
      · rename_i h
        exact ⟨(Vp h).1, (Vp h).2.1⟩
      · rw [Era]
        decide)
    (by rw [Ea0]; exact Hdcl) Hntcl Hnrcl (by rw [Ea0, AxSpinAq2.addZ]; exact Hdlk) Hntlk
  have LB := AxSpinAq2.liBnez L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Ψ HΨmid
  iintro C
  cases hb with
  | true =>
    rw [if_pos rfl] at W
    obtain ⟨-, -, Vs1, Vcpu⟩ := Vp rfl
    iapply W
    unfold KLong
    iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %rs1 %ib1 %Hf - - - - - - -
    obtain ⟨Hc1, HPC1, Htl1, Ea01, Esp1, -, -, -, -, -, -, -, -, -, Es11, Hkeep1, -, Hgv4,
      -, -, -, -, -, -, -, -, -, Hgv11⟩ := Hf
    have Ea0' : gprVal rs1 AxSpinE8.r10 = 0#64 := by
      rw [Ea01, Etp]; exact Vcpu vcpu Hgv4
    have Es1' : gprVal rs1 9#5 = lkv := by
      rw [show (9#5 : BitVec 5) = AxSpinHd8.r9 from rfl, Es11,
        Option.some.inj (Hgv11.symm.trans Vs1), AxSpinE8.ldResStBytes8]
    rw [show aqKp k b + 12 = aqKh k b true from rfl]
    iapply (LB (aqKh k b true) rs1 ib1 Hc1 HPC1 (hitWAgree rsH rs1 _ Htl1 Hhit) Ea0' Hlen)
    iintro %rs2 %ib2 %H2
    obtain ⟨Hc2, HPC2, Htl2, Hk2⟩ := H2
    iapply C $$ %rs2 %ib2
    ipureintro
    refine ⟨Hc2, HPC2, Htl2.trans Htl1, ?_, ?_, ?_⟩
    · rw [Hk2 2#5 (by decide)]; exact Esp1
    · rw [Hk2 9#5 (by decide)]; exact Es1'
    · intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr14 Hr15
      rw [Hk2 r Hr14]
      exact Hkeep1 r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
  | false =>
    rw [if_neg Bool.false_ne_true] at W
    iapply W
    unfold KShort
    iintro %vlk %rs1 %ib1 %Hf -
    obtain ⟨Hc1, HPC1, Htl1, Ea01, -, -, -, Hkeep1⟩ := Hf
    rw [show aqKp k b + 1 = aqKh k b false from rfl]
    iapply (LB (aqKh k b false) rs1 ib1 Hc1 HPC1 (hitWAgree rsH rs1 _ Htl1 Hhit) Ea01 Hlen)
    iintro %rs2 %ib2 %H2
    obtain ⟨Hc2, HPC2, Htl2, Hk2⟩ := H2
    iapply C $$ %rs2 %ib2
    ipureintro
    refine ⟨Hc2, HPC2, Htl2.trans Htl1, ?_, ?_, ?_⟩
    · rw [Hk2 2#5 (by decide)]; exact Hkeep1 2#5 (by decide) (by decide)
    · rw [Hk2 9#5 (by decide), Hkeep1 9#5 (by decide) (by decide)]; exact Es1
    · intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr14 Hr15
      rw [Hk2 r Hr14]
      exact Hkeep1 r Hr10 Hr15

set_option maxHeartbeats 4000000 in
include HL Hcons hmode hasid hppn Hfix Htxa Htxm HΨmid in
/-- acquire + 0x1a … + 0x32: the spin loop (claim at `aqKA`), `jal mycpu`, mycpu, the owned
`lk->cpu` store, the three reloads, `c.addi16sp`, `c.ret` (boundary `aqKm + 8`). -/
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
  have HRt := HR.2.2.2.2.1
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
  have WM := wpdMycpu L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Ψ HΨmid
  unfold AxSpinAq2.KTail
  iintro #Hil Hnh C
  -- ---- the spin loop, at aqKh (claim at aqKA, continuation at aqKm) ----
  iapply (wpdSpinAq L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Ψ HΨmid k b hb n
    rsS ibS Plk Hrmw Hvals (by omega) Hc0 HPC0
    (hitWSvpn rsS (AxSpinHdB.pac 0x1a) (AxSpinHdB.pac 0) (by decide) Hhit0) Hpl Hntl
    (by rw [Es10]; exact Hdal) (by rw [Es10]; exact Hhv)) $$ Hil Hnh
  unfold AxSpinAq1.KSpin
  rw [show aqKh k b hb + n = aqKA k b hb n from rfl]
  iintro %rs1 %ib1 %Hs HLK HCpu HNp
  obtain ⟨Hc1, HPC1, Htl1, -, Hkeep1, Hz⟩ := Hs
  rw [show aqKh k b hb + (n + 1) = aqKm k b hb n from rfl]
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
  -- ---- mycpu, at aqKm (continuation at aqKm + 4) ----
  have HRm : RowMycpu (aqKm k b hb n) (AxOpsem.grow (gtAdGd GT) i) (paZ Mra) (paZ Mms0) :=
    rowMycpuOf _ _ _ _ (rowShAppL _ _ (mycSh (paZ Mra) (paZ Mms0))
      [.RS (L.xlLk + 16) 8, .RL (paZ Pra) 8, .RL (paZ Ps0) 8, .RL (paZ Ps1) 8] HRt) (by omega)
  iapply (WM (aqKm k b hb n) rs2 ib2 (AxSpinHdB.pac 0x28) Mra Mms0 HRm Hw8 Hn_mra Hn_ms0
    (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2 (hitWAgree rsS rs2 _ Htl2 HhitM)
    (by rw [Evra]; exact HdaS_mra) (by rw [Evra]; exact HdaL_mra)
    (by rw [Evra]; exact hitWAgree rsS rs2 _ Htl2 Hh_mra)
    (by rw [Evs0]; exact HdaS_ms0) (by rw [Evs0]; exact HdaL_ms0)
    (by rw [Evs0]; exact hitWAgree rsS rs2 _ Htl2 Hh_ms0)
    Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0 (by unfold dj at Hdm; omega) Vm (by decide))
  iintro %vmra %vms0 %rs3 %ib3 %HM - -
  obtain ⟨Hc3, HPC3, Htl3', Ea03, Esp3, -, -, -, -, Hkeep3, -, -, -, -⟩ := HM
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
  iapply (XxSdCpuAcq L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid k b hb n
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rs3 (AxSpinHdB.pac 0x28) true 16#12 10#5 9#5
    (lkv + sign_extend (m := 64) (16#12)) Pcl (AxSpinE8.mycpuRet tp) (i, aqKA k b hb n)
    (RCpu L nm.xnH (gtAdGd GT) (i, aqKA k b hb n)) iprop(True) HR
    (retxRefl cpu rs3 (aqKm k b hb n + 4) ib3) Hc3 HPC3
    (hitWSvpn rs3 (AxSpinHdB.pac 0x28) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs3 _ Htl3 Hhit0))
    (twaE888 σi T satp0 _ T28) (by rw [Es13]) Hdcl (hitWAgree rsS rs3 _ Htl3 Hhcl) Hpcl Ea0
    rfl Hwin HP) $$ HCpu
  iintro %rs4 %ib4 %HG4 %Hsd HDep
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
    (rfFOfRf0 _ (rf0Addi _ _ _)) Hc8 Hlen)
  iintro %rs8 %ib8 %HG8
  have HF8 := stepRegs T satp0 _ rs7 _ _ _ _ _ rs8 HF7 HG8
  have HPC8 : rs8 .PC = AxSpinHdB.pac 0x32 := by rw [gbPc T satp0 _ _ _ _ _ _ HG8]; decide
  have Htl8 : rs8 .tlb = rsS .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG8).trans Htl7
  -- ---- + 0x32: c.ret (aqKm + 8; the target is the reloaded ra, pinned by `Vr`) ----
  iapply (XT _ rs8 (aqKm k b hb n + 8) (AxSpinHdB.pac 0x32)
    (retxRefl cpu rs8 (aqKm k b hb n + 8) ib8) (gbCtrl T satp0 _ _ _ _ _ _ HG8) HPC8
    (hitWSvpn rs8 (AxSpinHdB.pac 0x32) (AxSpinHdB.pac 0) (by decide)
      (hitWAgree rsS rs8 _ Htl8 Hhit0))
    (tw8082 σi T satp0 _ T32) rfFIns1e Hlen)
  iintro %rs' %ib' %HGr
  have HFr := stepRegs0 T satp0 _ rs8 _ _ _ rs' HF8 HGr
  have Hvra : vra' = stBytes 8 ret := Option.some.inj (Hgv5.symm.trans Vr)
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
Pins: Q20' Option V, see the header. -/
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
  have N : ∀ p, p ∈ [paZ Pra, paZ Ps0, paZ Ps1, paZ Qra, paZ Qs0, paZ Qs1, paZ Qmra, paZ Qms0,
      paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m, paZ Mra, paZ Mms0] →
      noRmw8 (AxOpsem.grow (gtAdGd GT) i) p := Hnr
  have HR' := HR
  obtain ⟨HRh, HRp, HRhold, -, -, Hlen⟩ := HR'
  have Hk20 : k + 20 ≤ aqKp k b := by unfold aqKp; split <;> omega
  have Hkh1 : aqKp k b + 1 ≤ aqKh k b hb := by unfold aqKh; split <;> omega
  have Ekm : aqKm k b hb n = aqKh k b hb + (n + 1) := rfl
  have Hkp : aqKp k b < (AxOpsem.grow (gtAdGd GT) i).length := by omega
  have Hkh : aqKh k b hb < (AxOpsem.grow (gtAdGd GT) i).length := by omega
  -- the spills' row labels and "no write between"
  obtain ⟨vra, cra, Hkra, Hlra⟩ := shStore k _ (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) 0 (paZ Pra)
    8 HRh rfl
  rw [Nat.add_zero] at Hkra
  obtain ⟨vs0, cs0, Hks0, Hls0⟩ := shStore k _ (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) 1 (paZ Ps0)
    8 HRh rfl
  obtain ⟨vs1, cs1, Hks1, Hls1⟩ := shStore k _ (aqHead (paZ Pra) (paZ Ps0) (paZ Ps1)) 2 (paZ Ps1)
    8 HRh rfl
  have NW0 := AxSpinAq2.nowrSpill k b hb n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (paZ Pra) HR
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
  have NW1 := AxSpinAq2.nowrSpill k b hb n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 (paZ Ps0) HR
    (by omega)
    (by
      intro it hit
      have hit' : it ∈ [Ritem.RS (paZ Ps1) 8] := hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hit'
      subst hit'
      exact D21)
    (Hout _ (by simp))
  have NW2 := AxSpinAq2.nowrSpill k b hb n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 (paZ Ps1) HR
    (by omega)
    (by
      intro it hit
      have hit' : it ∈ ([] : List Ritem) := hit
      simp only [List.not_mem_nil] at hit')
    (Hout _ (by simp))
  unfold AxSpinAq2.KAcq
  iintro #Hil Hnh C
  -- ---- the head: prologue, push_off, jal holding ----
  iapply (AxSpinAq2.head L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxp Ψ
    HΨmid k b rs0 ib0 Pra Ps0 Ps1 Qra Qs0 Qs1 Qmra Qms0 Pn Pi HRh HRp Hkp Hw8
    (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp))
    Hwn Hnn Hwi Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bqra Bqs0 Bqs1 Bqmra Bqms0 Bn Bi Hdj
    V14 Vb V30 V1c Vret Vs1)
  iintro %rsH %ibH %Hh
  obtain ⟨HcH, HPCH, HtlH, EspH, EraH, Ea0H, Es1H, HkeepH, Hgd0, Hgd1, Hgd2⟩ := Hh
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
  iapply (AxSpinAq2.mid L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Htxh Ψ
    HΨmid k b hb rsH ibH (gprVal rs0 AxSpinE8.r10) (gprVal rs0 AxSpinE8.r4) Hra Hs0 Hs1 Hram Hs0m
    Pcl Plk HRhold Hkh Hw8
    (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp)) (N _ (by simp))
    HcH HPCH (hitWAgree rs0 rsH _ HtlH Hhit0) (hitWAgree rs0 rsH _ HtlH HhitM) Ea0H Es1H EraH
    EtpH (hitWAgree rs0 rsH _ HtlH Hhv) (hitWAgree rs0 rsH _ HtlH Hhcl)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhra)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhs0)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhs1)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhram)
    (by rw [EspH]; exact slot8Tlb _ _ _ _ _ _ _ _ HtlH Bhs0m)
    Hhdj HdcL Hntcl Hnrcl HdlL Hntl Vh)
  iintro %rsS %ibS %Hm
  obtain ⟨HcS, HPCS, HtlS', EspS, Es1S, HkeepS⟩ := Hm
  have HtlS : rsS .tlb = rs0 .tlb := HtlS'.trans HtlH
  have EspS' : gprVal rsS AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := EspS.trans EspH
  have EtpS : gprVal rsS AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 :=
    (HkeepS _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans EtpH
  -- ---- the tail: the spin, mycpu, the lk->cpu store, the reloads, c.ret ----
  iapply (AxSpinAq2.tail L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxa Htxm Ψ HΨmid
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
    Hdm Hwin Vm Vr Hret) $$ Hil Hnh
  unfold AxSpinAq2.KTail
  iintro %vra' %vs0' %vs1' %rs' %ib' %Ht HLK HNp HDep H5 H6 H7
  obtain ⟨Hc', HPC', Htl', Esp', Ea0', Hl1, Hl2, Hl3, Era', Es0', Es1', Hkeep', Hz, Hgd4, Hlb4,
    Hgv5, Hgv6, Hgv7⟩ := Ht
  iapply C $$ %vra' %vs0' %vs1' %rs' %ib' [] HLK HNp HDep H5 H6 H7
  ipureintro
  refine ⟨Hc', HPC', Htl'.trans HtlS, ?_, Ea0', Hl1, Hl2, Hl3, Era', Es0', Es1', ?_, Hgd0, Hgd1,
    Hgd2, Hz, Hgd4, Hlb4, Hgv5, Hgv6, Hgv7⟩
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

end acq

end Weak
