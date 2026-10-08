/-
Weak: **xv6's REAL `release`, positional WPd, part 2: THE THEOREM `wpdRelease`** — the whole
release (release = 0x80000ce0, 17 instructions of `releaseText`) as a POSITIONAL,
CALLER-INDEXED CPS WPd at the joint instance Ixv6, interrupts off (`ctrlOkSW`), WARM TLB, over
AxSpinRl1's row shape `RowRelease k c …` — Theorem 2 design (`notes/weak-lb-thm2-design.md`
§C.2, §D row `AxSpinRl4`).  NEW Lean file (no Rocq source).

## The theorem

For every `k`, `c` and every row with `RowRelease k c …`, from the entry state (PC = release +
0x00, a0 = the lock address `lk`) at row position `k`:

    WPd (boundary at k, regs rs0) {{Ψ}}
    ⇐ isLock ∗ (i, kc) ↦ₐ locked (i, kc) ∗ Qc            (acquire's claim)
      ∗ (i, kw) ↦ₐ Qw ∗ RVL clb (i, kw) (val's bytes)     (acquire's lk->cpu store)
      ∗ (i, ks) ↦ₐ RNp (i, ks)                            (allocpid's nextpid store)
      ∗ (∀ vra vs0 vs1 rs' ib', ⌜regime ∧ PC = ret ∧ TLB kept ∧ sp = sp0 ∧ a0 = mycpuRet tp ∧
            ra / s0 / s1 = the RELOADED words ∧ every GPR but ra/sp/s0/s1/a0/a5 kept ∧ the
            spills' row data ∧ the reloads' graph values⌝
          -∗ (i, relKw k) ↦ₐ notheld i                   (the release deposit)
          -∗ the three reload annotations (reload bytes = spill bytes, `RLfact`)
          -∗ WPd (boundary at relKe k c, regs rs') {{Ψ}})

Composition: `AxSpinRl4.wpdRelHead` (+ 0x00 … + 0x1a, continuation at `relKp k`) → `jal
pop_off` (XxReg, link = release + 0x22) → `AxSpinPO6.wpdPopOff` at `relKp k` (`ppSh c`,
continuation at `relKr k c`) → the three reloads (XxLd at `relKr k c + 0/1/2`, the
no-write-between windows from `rowReleaseNowr`) → c.addi16sp (XxReg) → c.ret (XxRet) at
`relKe k c`.  The caller (allocproc after `jal release`) continues at `relKe k c` with
PC = `ret`, the notheld deposit and the registers above.

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §A–§C row `AxSpinRl4/4b`)

`wpdReleaseP` is `wpdRelease` on a PREFIX row `RowReleaseP k c hb …` (AxSpinRl4; holding's
branch bit `hb` is the row's; the stage-1 pin `lkBranch (relKh k) true` is gone — `hb = false`
is the `rlS` arm): `AxSpinRl4.wpdRelHeadP` → `jal pop_off` → `AxSpinPO6.wpdPopOffP` at `relKp k`
→ the three reloads → c.addi16sp → c.ret, one `by_cases` per row position (`relKp k`, `relKr k c
+ 0/1/2`, `relKe k c`; the head's and pop_off's inside their P-forms).  Row ends:
* the WINDOWED, RESOURCE-FREE hook (exact merged form)
  `HΨend : ∀ k', k ≤ k' → k' ≤ relKe k c → (hb = false → k' ≠ relKh k + 1) → k' ≠ relKh k + 12 →
     k' ≠ relKp k + 7 → (c = false → k' ≠ relKp k + 9) → LEN ≤ k' → ∀ pr, ⊢ wpdM … ⟨pr, k'⟩ Ψ`;
* the FOUR designated cuts in release's row, excluded from the hook, as premises:
  `KrlS` / `KrlL` (release's holding, `rlS` / `rlL`: resource-carrying, exactly `wpdRelHeadP`'s —
  `OHeld` / `OOwn` deposits, load outputs, reload annotations, the nextpid anchor) and `KppN` /
  `KppI` (pop_off's `ppN` / `ppI`: `wpdPopOffP`'s cut arms passed UP, at `relKp k`).
pop_off's optional reloads `rlN` / `rlI` (`AxSpinPO5.rlOk4` premises at `relKp k + 6` / `+ 8`) are
PARAMETERS: push_off's noff / intena stores are not in release's context (they are acquire's), so
the caller (AxSpinApA) supplies `some` from push_off's post.  The continuation additionally
receives pop_off's two `AxSpinPO5.ann4O` annotations (Q-S2-4: kept, not dropped).  Every value pin
is GUARDED by its position (holding's and pop_off's as in the P-forms; release's own return
`relKr k c < LEN → …`); the `rlL` gate is `relKh k + 12 < LEN → lk->cpu read = mycpu`; pop_off's
`ppN` / `ppI` gates are `relKp k + 7 < LEN → …` / `c = false → relKp k + 9 < LEN → …`.
`wpdRelease` keeps its exact name and statement and is the corollary (`hb = true`, `rlN = rlI =
none`, `RowRelease ⇒ RowReleaseP`; hook and the four arms vacuous under `relKe k c < LEN`; pins
unguarded; the two `ann4O` annotations dropped).

## Pins and row premises (honesty notes)

1. GRAPH-VALUE PINS (Q20', provisional Option V): `wpdRelHead`'s four (holding's two return
   reloads, the lk->cpu read = mycpu's address so `c.beqz a0,panic` falls, holding's s1 reload =
   `lk`); `wpdPopOff`'s five (mycpu's return, the noff arm `c` and its non-panic fall-through,
   the intena arm, pop_off's return = release + 0x22); release's own ra reload at `relKr k c`
   = `ret` (+ `jalrTgt 0#12 ret = ret`, the caller's return address).  The theorem proves
   nothing about a graph whose values differ.  s0 / s1 after release are reported as the
   reloads' graph values (+ the `RLfact` annotations); pinning them is the caller's choice.
2. ROW PREMISES on hart `i`'s own events (AxSpinT2a supplies them from `allocFull`):
   `CpuWin` ×2 (Rl2), `HrelZ4` / `HrelOnly` (Rl3), as in `wpdRelHead`.
3. Ownership is load-bearing for the DATA: the lock word and lk->cpu (`locked`, the lk->cpu
   handle, `fxReleasePid`), the private slots (the reload annotations).

## Deviations from the design

1. Split Rl4 / Rl4b at the pop_off seam (as the design allows).
2. The slot premises are `AxSpinPO1.slot8` bundles at the entry registers (`spo` = sp − 32 for
   release's and pop_off's callers' frames); the row-disjointness premises are
   `alldj` of release's three slots and their disjointness from every write of the window
   (`relWr`, AxSpinRl1), which is exactly what `rowReleaseNowr` consumes.

**Reused:** `wpdRelHead`/`tw4R1e`/`AxSpinRl4.jalTgts`/`releaseText` (AxSpinRl4), `wpdPopOff`/
`ppSh` (AxSpinPO6), `slot8Tlb`/`fld4Tlb` (AxSpinPO4), `XxReg`/`XxLd`/`XxRet` (AxSpinE6),
`tw60e2`/`tw6442`/`tw64a2`/`tw6105`/`tw8082` (AxSpinPOt2/3), `AxSpinHd9.frameCancel32`,
`rowReleaseHead`/`rowReleasePop`/`rowReleaseLen`/`rowReleaseNowr`/`relWr` (AxSpinRl1),
`shStore`/`alldj`/`dj` (AxSpinPOr), `AxWp.growLookup`.  Stage 2: `wpdRelHeadP`/`RowReleaseP`/
`AxSpinRl4.relPHead`/`relPPop`/`relPNowr`/`rowRelPOfFull` (AxSpinRl4), `wpdPopOffP` (AxSpinPO6),
`AxSpinPO5.rlOk4`/`ann4O`, `rowShOfP` (AxSpinRowP).  New names grepped absent (`wpdReleaseP`).
-/
import Weak.AxSpinRl4
import Weak.AxSpinPO6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_rl4b_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-- (Lean-only) pop_off's continuation boundary is release's first reload. -/
theorem AxSpinRl4b.popEnd (k : Nat) (c : Bool) :
    relKp k + 8 + (if c then 0 else 1) + 2 = relKr k c := by
  cases c <;> simp only [relKr, ppLen, ↓reduceIte, Bool.false_eq_true] <;> omega

section release
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
variable (Htxm : mycpuText σi T) (Htxh : holdingText σi T) (Htxq : popOffText σi T)
  (Htxr : releaseText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 6400000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh Htxq Htxr HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `wpdRelease` on a PREFIX row (`RowReleaseP k c hb …`).
`AxSpinRl4.wpdRelHeadP` → `jal pop_off` → `AxSpinPO6.wpdPopOffP` at `relKp k` → the three
reloads → c.addi16sp → c.ret, one `by_cases` per row position.  Row ends: the WINDOWED,
RESOURCE-FREE hook on `[k, relKe k c]` EXCEPT the four designated cuts of release's row —
`rlS` (`relKh k + 1`, on `hb = false`) and `rlL` (`relKh k + 12`), whose arms `KrlS` / `KrlL`
are `wpdRelHeadP`'s (resource-carrying: `OHeld` / `OOwn` deposits, load outputs, reload
annotations, the nextpid anchor), and pop_off's `ppN` (`relKp k + 7`) and `ppI` (`relKp k + 9`,
on `c = false`), whose arms `KppN` / `KppI` are `wpdPopOffP`'s (passed up; the optional noff /
intena reloads `rlN` / `rlI` are parameters — push_off's stores are not in release's context).
Value pins guarded by position.  The continuation also receives pop_off's two `ann4O`
annotations. -/
theorem wpdReleaseP (k : Nat) (c hb : Bool) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS Qra Qs0 Qmra Qms0 Qn Qi : BitVec 64)
    (plk : Int) (kc kw ks : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF)
    (tsc : List Nat) (rvsc wvsc : List (BitVec 8)) (clsc : WmClass)
    (rlN rlI : Option (Nat × List (BitVec 8) × WmClass)) :
    -- the row (prefix)
    RowReleaseP k c hb (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) plk (paZ Pcl)
      (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m) (paZ Qra) (paZ Qs0) (paZ Qmra)
      (paZ Qms0) (paZ Qn) (paZ Qi) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0m) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pcl) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Qn) 4 →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Qn) 4 →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Qi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.prl 0 → hitW rs0 (AxSpinHdB.prl 0) →
    hitW rs0 (pcm 0) →
    -- release's three slots
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24)
      Pra →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16)
      Ps0 →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8)
      Ps1 →
    alldj [(paZ Pra, 8), (paZ Ps0, 8), (paZ Ps1, 8)] →
    (∀ p ∈ [paZ Pra, paZ Ps0, paZ Ps1], ∀ q ∈ relWr plk (paZ Pcl) (paZ Hra) (paZ Hs0) (paZ Hs1)
      (paZ Hram) (paZ Hs0m) (paZ Qra) (paZ Qs0) (paZ Qmra) (paZ Qms0) (paZ Qn), dj q.1 q.2 p 8) →
    -- holding's five slots
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
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    -- pop_off's slots and the cpu fields
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2))) +
        sign_extend (m := 64) AxSpinE8.immRa) Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2))) +
        sign_extend (m := 64) AxSpinE8.immS0) Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Qn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Qi →
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Qn, 4)] →
    -- the lock (a0 = its address)
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 PlkS →
    paZ PlkS = L.xlLk →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 PclS →
    paZ PclS = L.xlLk + 16 →
    -- acquire's claim and its lk->cpu store (the holder's facts; row items guarded)
    (relKh k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk tsc rvsc wvsc clsc)) →
    kc < relKh k → nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, relKh k) →
    (relKh k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[kw]? =
        some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls)) →
    kw < relKh k + 4 →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, relKh k + 4) → False) →
    -- ROW PREMISES (AxSpinRl2 / AxSpinRl3; row items guarded)
    CpuWin L GT i (i, kw) → CpuWin L GT i (i, relKh k + 4) →
    (relKw k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[relKw k]? = some (.LStore false L.xlLk AxSpinX4.z4 .WCrel)) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), relKc k < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = relKw k) →
    -- the nextpid anchor (allocpid's store, before release)
    ks < k → (relKw k < (AxOpsem.grow (gtAdGd GT) i).length →
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[ks]? = some l ∧ lbIsMem l = true) →
    -- GRAPH-VALUE PINS (Q20' Option V), guarded: holding's
    (relKh k + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 7) = some (stBytes 8 (pch 0x1a))) →
    (relKh k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10))) →
    -- the rlL GATE
    (relKh k + 12 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 4) =
        some (stBytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)))) →
    (relKh k + 11 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 11) = some (stBytes 8 (gprVal rs0 AxSpinE8.r10))) →
    -- pop_off's (AxSpinPO6.wpdPopOffP's, at relKp k; the ppN gate and the ppI gate guarded)
    (relKp k + 4 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKp k + 4) = some (stBytes 8 (ppp 0x0c))) →
    (relKp k + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
      ∀ vn, graphValue (gtAdGd GT) (i, relKp k + 6) = some vn →
        zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false) →
    (∀ vn, graphValue (gtAdGd GT) (i, relKp k + 6) = some vn →
      (addiwm1 (ldRes false 4 vn) != zero_reg) = c) →
    (c = false → relKp k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
      ∀ vi, graphValue (gtAdGd GT) (i, relKp k + 8) = some vi →
        (ldRes false 4 vi == zero_reg) = true) →
    (relKp k + 8 + (if c then 0 else 1) < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKp k + 8 + (if c then 0 else 1)) =
        some (stBytes 8 (AxSpinHdB.prl 0x22))) →
    -- pop_off's two (optional) field reloads
    AxSpinPO5.rlOk4 (AxOpsem.grow (gtAdGd GT) i) (paZ Qn) (relKp k + 6) rlN →
    (c = false → AxSpinPO5.rlOk4 (AxOpsem.grow (gtAdGd GT) i) (paZ Qi) (relKp k + 8) rlI) →
    -- release's own return
    (relKr k c < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKr k c) = some (stBytes 8 ret)) → jalrTgt 0#12 ret = ret →
    -- the row-end hook (windowed; NOT at the four designated cuts)
    (∀ k' : Nat, k ≤ k' → k' ≤ relKe k c → (hb = false → k' ≠ relKh k + 1) →
      k' ≠ relKh k + 12 → k' ≠ relKp k + 7 → (c = false → k' ≠ relKp k + 9) →
      (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    -- the designated cut rlS (hb = false: row ends right after holding's lw)
    (hb = false →
      ⊢ AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
        KShortEnd (hlc := hlc) L GT nm i Ψ (relKh k)
          (fun v => iprop(OHeld L GT nm i kc (relKh k) Qc (relKh k) v ∗ AxAnnot.annotOwn (i, kw)
            iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val))))) →
    -- the designated cut rlL (hb = true: row ends after holding's last reload)
    (hb = true → ∀ rs : RegFile, gprVal rs AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 →
      gprVal rs AxSpinE8.r10 = gprVal rs0 AxSpinE8.r10 →
      ⊢ AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
        KLongEnd (hlc := hlc) L GT nm i Ψ (relKh k) rs Hra Hs0 Hs1 Hram Hs0m
          (OHeld L GT nm i kc (relKh k) Qc (relKh k))
          (OOwn L GT nm i kw (relKh k + 4) val Qw (relKh k + 4))) →
    -- the designated cut ppN (row ends right after pop_off's noff load)
    ((AxOpsem.grow (gtAdGd GT) i).length = relKp k + 7 →
      ∀ (vn : List (BitVec 8)) (pr : Pexv6), graphValue (gtAdGd GT) (i, relKp k + 6) = some vn →
        ⊢ AxSpinPO5.ann4O (GF := GF) GT i (paZ Qn) (relKp k + 6) rlN -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨pr, relKp k + 7⟩ Ψ) →
    -- the designated cut ppI (arm c = false; row ends right after pop_off's intena load)
    (c = false → (AxOpsem.grow (gtAdGd GT) i).length = relKp k + 9 →
      ∀ (vn vi : List (BitVec 8)) (pr : Pexv6),
        graphValue (gtAdGd GT) (i, relKp k + 6) = some vn →
        graphValue (gtAdGd GT) (i, relKp k + 8) = some vi →
        ⊢ AxSpinPO5.ann4O (GF := GF) GT i (paZ Qn) (relKp k + 6) rlN -∗
          AxSpinPO5.ann4O (GF := GF) GT i (paZ Qi) (relKp k + 8) rlI -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨pr, relKp k + 9⟩ Ψ) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Qc) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
      (∀ (vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinHd8.r9)) ∧
          graphValue (gtAdGd GT) (i, relKr k c) = some vra ∧
          graphValue (gtAdGd GT) (i, relKr k c + 1) = some vs0 ∧
          graphValue (gtAdGd GT) (i, relKr k c + 2) = some vs1⌝ -∗
        AxAnnot.annotOwn (i, relKw k) (notheld nm.xnReg L.xlLk i) -∗
        AxAnnot.annotOwn (GF := GF) (i, relKr k c)
          iprop(⌜RLfact GT i (paZ Pra) (relKr k c) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, relKr k c + 1)
          iprop(⌜RLfact GT i (paZ Ps0) (relKr k c + 1) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, relKr k c + 2)
          iprop(⌜RLfact GT i (paZ Ps1) (relKr k c + 2) (stBytes 8 (gprVal rs0 AxSpinHd8.r9))⌝) -∗
        AxSpinPO5.ann4O (GF := GF) GT i (paZ Qn) (relKp k + 6) rlN -∗
        AxSpinPO5.ann4O (GF := GF) GT i (paZ Qi) (relKp k + 8) (if c then none else rlI) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKe k c⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnra Hns0 Hns1 Hnr1 Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hnq1 Hnq2 Hnq3 Hnq4 Hwle Hnrn Hnri
    Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 HdjS HdjW Bh1 Bh2 Bh3 Bh4 Bh5 Hdisj
    Bqra Bqs0 Bqmra Bqms0 Bqn Bqi HdjQ
    Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    Hkc Hkck Hnl Hkw Hkwk Hnoint HwinW HwinR HrelZ4 HrelOnly Hks Hksm
    Hvm Hvr Hvcpu Hvs1 Hval0c Hvge Hvc Hvz Hvalr HrlN HrlI HvalR Hret HΨend KrlS KrlL KppN KppI
  have Htxr' := Htxr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, T1e, T22, T24, T26, T28, T2a⟩ := Htxr'
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL := XxLd L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XT := XxRet L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have Hpl : 10 ≤ ppLen c := by unfold ppLen; split <;> omega
  have HdaL_ra := Bra.2.1
  have Hh_ra := Bra.2.2.1
  have Hpr_ra := Bra.2.2.2.1
  have Hnt_ra := Bra.2.2.2.2
  have HdaL_s0 := Bs0.2.1
  have Hh_s0 := Bs0.2.2.1
  have Hpr_s0 := Bs0.2.2.2.1
  have Hnt_s0 := Bs0.2.2.2.2
  have HdaL_s1 := Bs1.2.1
  have Hh_s1 := Bs1.2.2.1
  have Hpr_s1 := Bs1.2.2.2.1
  have Hnt_s1 := Bs1.2.2.2.2
  iintro #Hil Hcl Hwl Hnp C
  -- ---- the head: release + 0x00 … + 0x1a (k … relKw k) ----
  iapply (wpdRelHeadP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Htxr Ψ
    HΨmid k c hb rs0 ib0 Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS plk (paZ Qra)
    (paZ Qs0) (paZ Qmra) (paZ Qms0) (paZ Qn) (paZ Qi) kc kw ks val cls Qc Qw tsc rvsc wvsc clsc
    HR Hw8 Hnr1 Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bh1 Bh2 Bh3 Bh4 Bh5 Hdisj
    Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    Hkc Hkck Hnl Hkw Hkwk Hnoint HwinW HwinR HrelZ4 HrelOnly Hks Hksm Hvm Hvr Hvcpu Hvs1
    (fun k' h1 h2 h3 h4 h5 pr => HΨend k' h1 (by simp only [relKw, relKe, relKr, relKp] at h2 ⊢; omega)
      h3 h4 (by simp only [relKw, relKp] at h2 ⊢; omega)
      (fun _ => by simp only [relKw, relKp] at h2 ⊢; omega) h5 pr) KrlS KrlL)
    $$ Hil Hcl Hwl Hnp
  iintro %rs1 %ib1 %HH Hnh
  obtain ⟨Hc1, HPC1, Htl1, Esp1, Es11, Ekeep1, Hgd0, Hgd1, Hgd2⟩ := HH
  -- row end at relKp k
  by_cases Ep : (AxOpsem.grow (gtAdGd GT) i).length ≤ relKp k
  · iclear C
    iclear Hnh
    iapply (HΨend _ (by simp only [relKp]; omega) (by simp only [relKe, relKr, relKp]; omega)
      (fun _ => by simp only [relKp, relKh]; omega) (by simp only [relKp, relKh]; omega)
      (by omega) (fun _ => by omega) Ep _)
  -- ---- + 0x1e: jal ra,pop_off (relKp k) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs1 (AxSpinHdB.prl 0x1e) false rl1e (some (ppp 0))
      (some (1#5, BitVec.addInt (AxSpinHdB.prl 0x1e) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs1 (AxSpinHdB.prl 0x1e)
      false 2097050#21 1#5 (by decide)
    rw [AxSpinRl4.jalTgts.2] at h
    rw [show linkOw 1#5 (BitVec.addInt (AxSpinHdB.prl 0x1e) (incr false)) =
      some (1#5, BitVec.addInt (AxSpinHdB.prl 0x1e) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs1 (relKp k) (AxSpinHdB.prl 0x1e) false rl1e (some (ppp 0))
    (some (1#5, BitVec.addInt (AxSpinHdB.prl 0x1e) (incr false)))
    (retxRefl cpu rs1 (relKp k) ib1) Hc1 HPC1
    (hitWSvpn rs1 (AxSpinHdB.prl 0x1e) (AxSpinHdB.prl 0) (by decide)
      (hitWAgree rs0 rs1 _ Htl1 Hhit0))
    (tw4R1e σi T satp0 _ T1e) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 2097050#21 (.Regidx 1#5)) Hcj (by omega))
  iintro %rs2 %ib2 %HG2
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 (fun _ => rfl) HG2
  have HPC2 : rs2 .PC = ppp 0 := gbPc T satp0 _ _ _ _ _ _ HG2
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  have Esp2 : gprVal rs2 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF2]; ax_spin_rl4b_zsimp; exact Esp1
  have Etp2 : gprVal rs2 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 := by
    rw [HF2]; ax_spin_rl4b_zsimp
    exact Ekeep1 4#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have Ekeep2 : ∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
      r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs2 r = gprVal rs0 r := by
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    rw [HF2]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
      exact Ekeep1 r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
  -- ---- pop_off, at relKp k (P-form) ----
  have HRp := AxSpinRl4.relPPop HR
  iapply (wpdPopOffP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxq Ψ HΨmid
    (relKp k) c rs2 ib2 (AxSpinHdB.prl 0x22) Qra Qs0 Qmra Qms0 Qn Qi rlN rlI HRp
    Hw8 Hnq1 Hnq2 Hnq3 Hnq4 Hwle Hnrn Hnri
    (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (ppp 0) (AxSpinHdB.prl 0) (by decide) (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (hitWAgree rs0 rs2 _ Htl2 HhitM)
    (by rw [Esp2]; exact slot8Tlb σi T L i rs0 rs2 _ _ Htl2 Bqra)
    (by rw [Esp2]; exact slot8Tlb σi T L i rs0 rs2 _ _ Htl2 Bqs0)
    (by rw [Esp2]; exact slot8Tlb σi T L i rs0 rs2 _ _ Htl2 Bqmra)
    (by rw [Esp2]; exact slot8Tlb σi T L i rs0 rs2 _ _ Htl2 Bqms0)
    (by rw [Etp2]; exact fld4Tlb σi T L i rs0 rs2 _ _ Htl2 Bqn)
    (by rw [Etp2]; exact fld4Tlb σi T L i rs0 rs2 _ _ Htl2 Bqi)
    HdjQ Hval0c Hvge Hvc Hvz Hvalr (by decide) HrlN HrlI
    (fun k' h1 h2 h3 h4 h5 pr => HΨend k' (by simp only [relKp] at h1 ⊢; omega)
      (by rw [AxSpinRl4b.popEnd] at h2; simp only [relKe]; omega)
      (fun _ => by simp only [relKp, relKh] at h1 ⊢; omega)
      (by simp only [relKp, relKh] at h1 ⊢; omega) h3 h4 h5 pr) KppN KppI)
  iintro %vn %vi %vra' %vs0' %rs3 %ib3 %HP - - HaN HaI
  obtain ⟨Hc3, HPC3, Htl3', Esp3, Ea03, -, -, Ekeep3, -⟩ := HP
  have Htl3 : rs3 .tlb = rs0 .tlb := Htl3'.trans Htl2
  have Esp3' : gprVal rs3 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := Esp3.trans Esp2
  rw [AxSpinRl4b.popEnd]
  have HF3 : ∀ r, gprVal rs3 r = gprVal rs3 r := fun _ => rfl
  -- row end at relKr k c (pop_off's continuation)
  by_cases Er0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ relKr k c
  · iclear C
    iclear Hnh
    iclear HaN
    iclear HaI
    iapply (HΨend _ (by simp only [relKr, relKp]; omega) (by simp only [relKe]; omega)
      (fun _ => by simp only [relKr, relKp, relKh]; omega)
      (by simp only [relKr, relKp, relKh]; omega) (by simp only [relKr]; omega)
      (fun _ => by simp only [relKr]; omega) Er0 _)
  -- the spills' row labels (all present: k + 2 < relKr k c < LEN)
  have HRh := rowShOfP (AxSpinRl4.relPHead HR)
    (by simp only [relHead, List.length_cons, List.length_nil, relKr, relKp] at Er0 ⊢; omega)
  obtain ⟨vwra, cra, Hkra, Hlra⟩ := shStore k _ _ 0 (paZ Pra) 8 HRh rfl
  obtain ⟨vws0, cs0, Hks0, Hls0⟩ := shStore k _ _ 1 (paZ Ps0) 8 HRh rfl
  obtain ⟨vws1, cs1, Hks1, Hls1⟩ := shStore k _ _ 2 (paZ Ps1) 8 HRh rfl
  rw [Nat.add_zero] at Hkra
  have NW0 := AxSpinRl4.relPNowr 0 (by decide) (paZ Pra) 8 HR (by omega)
    (by
      simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      exact ⟨HdjS 1 0 _ _ rfl rfl (by decide), HdjS 2 0 _ _ rfl rfl (by decide)⟩)
    (HdjW _ (by simp))
  simp only [Nat.add_zero] at NW0
  -- ---- + 0x22: c.ldsp ra,24(sp) — reload (relKr k c) ----
  iapply (XL _ rs3 (relKr k c) (AxSpinHdB.prl 0x22) true AxSpinPO3.imm24 2#5 1#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra k vwra cra
    (retxRefl cpu rs3 (relKr k c) ib3) Hc3 HPC3
    (hitWSvpn rs3 (AxSpinHdB.prl 0x22) (AxSpinHdB.prl 0) (by decide)
      (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (tw60e2 σi T satp0 _ T22) (by decide) (by rw [Esp3']) HdaL_ra
    (hitWAgree rs0 rs3 _ Htl3 Hh_ra) Hpr_ra Hnt_ra Hnra Hkra Hlra
    (by simp only [relKr, relKp]; omega)
    (fun k' lb rl b m h hl hid => by
      have := NW0 k' lb rl b m h hl hid; unfold dj at this; omega) (by omega))
  iintro %vra %rs4 %ib4 %Hlvra %HG4 %Hgv0 H0
  have HF4 := stepRegs T satp0 _ rs3 _ _ _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = AxSpinHdB.prl 0x24 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- row end at relKr k c + 1
  by_cases Er1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ relKr k c + 1
  · iclear C
    iclear Hnh
    iclear HaN
    iclear HaI
    iclear H0
    iapply (HΨend _ (by simp only [relKr, relKp]; omega) (by simp only [relKe]; omega)
      (fun _ => by simp only [relKr, relKp, relKh]; omega)
      (by simp only [relKr, relKp, relKh]; omega) (by simp only [relKr]; omega)
      (fun _ => by simp only [relKr]; omega) Er1 _)
  have NW1 := AxSpinRl4.relPNowr 1 (by decide) (paZ Ps0) 8 HR (by omega)
    (by
      simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq]
      exact HdjS 2 1 _ _ rfl rfl (by decide))
    (HdjW _ (by simp))
  -- ---- + 0x24: c.ldsp s0,16(sp) — reload (relKr k c + 1) ----
  iapply (XL _ rs4 (relKr k c + 1) (AxSpinHdB.prl 0x24) true AxSpinPO3.imm16 2#5 8#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 (k + 1) vws0 cs0
    (retxRefl cpu rs4 (relKr k c + 1) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (AxSpinHdB.prl 0x24) (AxSpinHdB.prl 0) (by decide)
      (hitWAgree rs0 rs4 _ Htl4 Hhit0))
    (tw6442 σi T satp0 _ T24) (by decide) (by rw [HF4]; ax_spin_rl4b_zsimp; rw [Esp3'])
    HdaL_s0 (hitWAgree rs0 rs4 _ Htl4 Hh_s0) Hpr_s0 Hnt_s0 Hns0 Hks0 Hls0
    (by simp only [relKr, relKp]; omega)
    (fun k' lb rl b m h hl hid => by
      have := NW1 k' lb rl b m h hl hid; unfold dj at this; omega) (by omega))
  iintro %vs0 %rs5 %ib5 %Hlvs0 %HG5 %Hgv1 H1
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = AxSpinHdB.prl 0x26 := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- row end at relKr k c + 2
  by_cases Er2 : (AxOpsem.grow (gtAdGd GT) i).length ≤ relKr k c + 2
  · iclear C
    iclear Hnh
    iclear HaN
    iclear HaI
    iclear H0
    iclear H1
    iapply (HΨend _ (by simp only [relKr, relKp]; omega) (by simp only [relKe]; omega)
      (fun _ => by simp only [relKr, relKp, relKh]; omega)
      (by simp only [relKr, relKp, relKh]; omega) (by simp only [relKr]; omega)
      (fun _ => by simp only [relKr]; omega) Er2 _)
  have NW2 := AxSpinRl4.relPNowr 2 (by decide) (paZ Ps1) 8 HR (by omega)
    (by intro q hq; simp at hq)
    (HdjW _ (by simp))
  -- ---- + 0x26: c.ldsp s1,8(sp) — reload (relKr k c + 2) ----
  iapply (XL _ rs5 (relKr k c + 2) (AxSpinHdB.prl 0x26) true AxSpinPO3.imm8 2#5 9#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 (k + 2) vws1 cs1
    (retxRefl cpu rs5 (relKr k c + 2) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (AxSpinHdB.prl 0x26) (AxSpinHdB.prl 0) (by decide)
      (hitWAgree rs0 rs5 _ Htl5 Hhit0))
    (tw64a2 σi T satp0 _ T26) (by decide) (by rw [HF5]; ax_spin_rl4b_zsimp; rw [Esp3'])
    HdaL_s1 (hitWAgree rs0 rs5 _ Htl5 Hh_s1) Hpr_s1 Hnt_s1 Hns1 Hks1 Hls1
    (by simp only [relKr, relKp]; omega)
    (fun k' lb rl b m h hl hid => by
      have := NW2 k' lb rl b m h hl hid; unfold dj at this; omega) (by omega))
  iintro %vs1 %rs6 %ib6 %Hlvs1 %HG6 %Hgv2 H2
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = AxSpinHdB.prl 0x28 := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  rw [show relKr k c + 2 + 1 = relKe k c from rfl]
  -- row end at relKe k c
  by_cases Ee : (AxOpsem.grow (gtAdGd GT) i).length ≤ relKe k c
  · iclear C
    iclear Hnh
    iclear HaN
    iclear HaI
    iclear H0
    iclear H1
    iclear H2
    iapply (HΨend _ (by simp only [relKe, relKr, relKp]; omega) (Nat.le_refl _)
      (fun _ => by simp only [relKe, relKr, relKp, relKh]; omega)
      (by simp only [relKe, relKr, relKp, relKh]; omega) (by simp only [relKe, relKr]; omega)
      (fun _ => by simp only [relKe, relKr]; omega) Ee _)
  -- ---- + 0x28: c.addi16sp sp,32 (relKe k c) ----
  have Hc7 := certAddi (ctrlOkSW T satp0) rs6 (AxSpinHdB.prl 0x28) true 2#5 2#5
    (caddi16spImm 2#6) (by decide)
  simp only [HF6] at Hc7
  ax_spin_rl4b_zsimp at Hc7
  iapply (XR _ rs6 (relKe k c) (AxSpinHdB.prl 0x28) true q28 _ _
    (retxRefl cpu rs6 (relKe k c) ib6) (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (AxSpinHdB.prl 0x28) (AxSpinHdB.prl 0) (by decide)
      (hitWAgree rs0 rs6 _ Htl6 Hhit0))
    (tw6105 σi T satp0 _ T28) (AxSpinE8.owOkSome 2#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _)) Hc7 (by omega))
  iintro %rs7 %ib7 %HG7
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = AxSpinHdB.prl 0x2a := by rw [gbPc T satp0 _ _ _ _ _ _ HG7]; decide
  have Htl7 : rs7 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  -- ---- + 0x2a: c.ret (relKe k c; Q20': the target is the reloaded ra, pinned) ----
  iapply (XT _ rs7 (relKe k c) (AxSpinHdB.prl 0x2a)
    (retxRefl cpu rs7 (relKe k c) ib7) (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (AxSpinHdB.prl 0x2a) (AxSpinHdB.prl 0) (by decide)
      (hitWAgree rs0 rs7 _ Htl7 Hhit0))
    (tw8082 σi T satp0 _ T2a) rfFIns1e (by omega))
  iintro %rs' %ib' %HGr
  have HFr := stepRegs0 T satp0 _ rs7 _ _ _ rs' HF7 HGr
  -- the spills' row data are the entry values of ra / s0 / s1
  have Ev : ∀ (kk : Nat) (pa : Int) (vw : List (BitVec 8)) (cl : WmClass) (v : BitVec 64),
      (AxOpsem.grow (gtAdGd GT) i)[kk]? = some (.LStore false pa vw cl) →
      graphData (gtAdGd GT) (i, kk) = some (stBytes 8 v) → vw = stBytes 8 v := by
    intro kk pa vw cl v Hl Hg
    rw [graphData, AxWp.growLookup _ _ _ _ Hl] at Hg
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hg
  obtain rfl := Ev _ _ _ _ _ Hkra Hgd0
  obtain rfl := Ev _ _ _ _ _ Hks0 Hgd1
  obtain rfl := Ev _ _ _ _ _ Hks1 Hgd2
  have Hvra : vra = stBytes 8 ret :=
    Option.some.inj (Hgv0.symm.trans (HvalR (by simp only [relKe] at Ee; omega)))
  have Hgpr1 : gprVal rs7 1#5 = ldRes false 8 vra := by
    rw [HF7]
    ax_spin_rl4b_zsimp
  iapply C $$ %vra %vs0 %vs1 %rs' %ib' [] Hnh H0 H1 H2 HaN HaI
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl7, ?_,
    ?_, Hlvra, Hlvs0, Hlvs1, ?_, ?_, ?_, ?_, Hgd0, Hgd1, Hgd2, Hgv0, Hgv1, Hgv2⟩
  · -- PC = ret
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    show jalrTgt 0#12 (gprVal rs7 1#5) = ret
    rw [Hgpr1, Hvra, AxSpinE8.ldResStBytes8, Hret]
  · -- sp restored
    rw [HFr]
    ax_spin_rl4b_zsimp
    rw [Esp3']
    exact AxSpinHd9.frameCancel32 _
  · -- a0 = mycpuRet tp (pop_off's)
    rw [HFr]
    ax_spin_rl4b_zsimp
    rw [Ea03, Etp2]
  · rw [HFr]; ax_spin_rl4b_zsimp
  · rw [HFr]; ax_spin_rl4b_zsimp
  · rw [HFr]; ax_spin_rl4b_zsimp
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n9 : r ≠ 9#5 := fun h => Hr9 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
      rw [Ekeep3 r Hr1 Hr2 Hr8 Hr10 Hr15]
      exact Ekeep2 r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh Htxq Htxr HΨmid in
/-- THE POSITIONAL RELEASE WPd (xv6's real `release`, the holder's path, pop_off arm `c`):
continuation at `relKe k c` (after the c.ret) with PC = `ret`, the notheld deposit and the
reloaded registers.  Stage 2: the full-row corollary of `wpdReleaseP` (`hb = true`, no
pop_off reload claimed, `rlN = rlI = none`; the hook and the four cut arms are vacuous under
`relKe k c < LEN`; the pins unguarded). -/
theorem wpdRelease (k : Nat) (c : Bool) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS Qra Qs0 Qmra Qms0 Qn Qi : BitVec 64)
    (plk : Int) (kc kw ks : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF)
    (tsc : List Nat) (rvsc wvsc : List (BitVec 8)) (clsc : WmClass) :
    -- the row
    RowRelease k c (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) plk (paZ Pcl)
      (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m) (paZ Qra) (paZ Qs0) (paZ Qmra)
      (paZ Qms0) (paZ Qn) (paZ Qi) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0m) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pcl) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Qms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Qn) 4 →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Qn) 4 →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Qi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.prl 0 → hitW rs0 (AxSpinHdB.prl 0) →
    hitW rs0 (pcm 0) →
    -- release's three slots
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24)
      Pra →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16)
      Ps0 →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8)
      Ps1 →
    alldj [(paZ Pra, 8), (paZ Ps0, 8), (paZ Ps1, 8)] →
    (∀ p ∈ [paZ Pra, paZ Ps0, paZ Ps1], ∀ q ∈ relWr plk (paZ Pcl) (paZ Hra) (paZ Hs0) (paZ Hs1)
      (paZ Hram) (paZ Hs0m) (paZ Qra) (paZ Qs0) (paZ Qmra) (paZ Qms0) (paZ Qn), dj q.1 q.2 p 8) →
    -- holding's five slots
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
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    -- pop_off's slots and the cpu fields
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Qra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Qs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2))) +
        sign_extend (m := 64) AxSpinE8.immRa) Qmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2))) +
        sign_extend (m := 64) AxSpinE8.immS0) Qms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Qn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Qi →
    alldj [(paZ Qra, 8), (paZ Qs0, 8), (paZ Qmra, 8), (paZ Qms0, 8), (paZ Qn, 4)] →
    -- the lock (a0 = its address)
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 PlkS →
    paZ PlkS = L.xlLk →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 PclS →
    paZ PclS = L.xlLk + 16 →
    -- acquire's claim and its lk->cpu store (the holder's facts)
    (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk tsc rvsc wvsc clsc) →
    kc < relKh k → nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, relKh k) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? =
      some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls) →
    kw < relKh k + 4 →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, relKh k + 4) → False) →
    -- ROW PREMISES (AxSpinRl2 / AxSpinRl3; AxSpinT2a supplies them)
    CpuWin L GT i (i, kw) → CpuWin L GT i (i, relKh k + 4) →
    (AxOpsem.grow (gtAdGd GT) i)[relKw k]? = some (.LStore false L.xlLk AxSpinX4.z4 .WCrel) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), relKc k < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = relKw k) →
    -- the nextpid anchor (allocpid's store, before release)
    ks < k → (∃ l, (AxOpsem.grow (gtAdGd GT) i)[ks]? = some l ∧ lbIsMem l = true) →
    -- GRAPH-VALUE PINS (Q20' Option V): holding's
    graphValue (gtAdGd GT) (i, relKh k + 7) = some (stBytes 8 (pch 0x1a)) →
    graphValue (gtAdGd GT) (i, relKh k + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10)) →
    graphValue (gtAdGd GT) (i, relKh k + 4) =
      some (stBytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4))) →
    graphValue (gtAdGd GT) (i, relKh k + 11) = some (stBytes 8 (gprVal rs0 AxSpinE8.r10)) →
    -- pop_off's
    graphValue (gtAdGd GT) (i, relKp k + 4) = some (stBytes 8 (ppp 0x0c)) →
    (∀ vn, graphValue (gtAdGd GT) (i, relKp k + 6) = some vn →
      zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false) →
    (∀ vn, graphValue (gtAdGd GT) (i, relKp k + 6) = some vn →
      (addiwm1 (ldRes false 4 vn) != zero_reg) = c) →
    (c = false → ∀ vi, graphValue (gtAdGd GT) (i, relKp k + 8) = some vi →
      (ldRes false 4 vi == zero_reg) = true) →
    graphValue (gtAdGd GT) (i, relKp k + 8 + (if c then 0 else 1)) =
      some (stBytes 8 (AxSpinHdB.prl 0x22)) →
    -- release's own return
    graphValue (gtAdGd GT) (i, relKr k c) = some (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Qc) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
      (∀ (vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinHd8.r9)) ∧
          graphValue (gtAdGd GT) (i, relKr k c) = some vra ∧
          graphValue (gtAdGd GT) (i, relKr k c + 1) = some vs0 ∧
          graphValue (gtAdGd GT) (i, relKr k c + 2) = some vs1⌝ -∗
        AxAnnot.annotOwn (i, relKw k) (notheld nm.xnReg L.xlLk i) -∗
        AxAnnot.annotOwn (GF := GF) (i, relKr k c)
          iprop(⌜RLfact GT i (paZ Pra) (relKr k c) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, relKr k c + 1)
          iprop(⌜RLfact GT i (paZ Ps0) (relKr k c + 1) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, relKr k c + 2)
          iprop(⌜RLfact GT i (paZ Ps1) (relKr k c + 2) (stBytes 8 (gprVal rs0 AxSpinHd8.r9))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKe k c⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnra Hns0 Hns1 Hnr1 Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hnq1 Hnq2 Hnq3 Hnq4 Hwle Hnrn Hnri
    Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 HdjS HdjW Bh1 Bh2 Bh3 Bh4 Bh5 Hdisj
    Bqra Bqs0 Bqmra Bqms0 Bqn Bqi HdjQ
    Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    Hkc Hkck Hnl Hkw Hkwk Hnoint HwinW HwinR HrelZ4 HrelOnly Hks Hksm
    Hvm Hvr Hvcpu Hvs1 Hval0c Hvge Hvc Hvz Hvalr HvalR Hret
  have Hlen := (rowReleaseLen HR).1
  have Hpl : 10 ≤ ppLen c := by unfold ppLen; split <;> omega
  simp only [relKe, relKr, relKp] at Hlen
  iintro #Hil Hcl Hwl Hnp C
  iapply (wpdReleaseP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Htxq Htxr
    Ψ HΨmid k c true rs0 ib0 ret Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS Qra Qs0 Qmra
    Qms0 Qn Qi plk kc kw ks val cls Qc Qw tsc rvsc wvsc clsc none none
    (AxSpinRl4.rowRelPOfFull HR) Hw8 Hnra Hns0 Hns1 Hnr1 Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hnq1 Hnq2
    Hnq3 Hnq4 Hwle Hnrn Hnri Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 HdjS HdjW Bh1 Bh2 Bh3 Bh4 Bh5 Hdisj
    Bqra Bqs0 Bqmra Bqms0 Bqn Bqi HdjQ
    Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    (fun _ => Hkc) Hkck Hnl (fun _ => Hkw) Hkwk Hnoint HwinW HwinR (fun _ => HrelZ4) HrelOnly
    Hks (fun _ => Hksm) (fun _ => Hvm) (fun _ => Hvr) (fun _ => Hvcpu) (fun _ => Hvs1)
    (fun _ => Hval0c) (fun _ => Hvge) Hvc (fun hc _ => Hvz hc) (fun _ => Hvalr) trivial
    (fun _ => trivial) (fun _ => HvalR) Hret
    (fun _ _ h2 _ _ _ _ h7 _ => absurd h7 (by simp only [relKe, relKr, relKp] at h2; omega))
    (fun h => nomatch h)
    (fun _ _ _ _ => by
      iintro -
      unfold KLongEnd
      iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp
      exact absurd Hp.1 (by simp only [relKh]; omega))
    (fun h => absurd h (by simp only [relKp]; omega))
    (fun _ h => absurd h (by simp only [relKp]; omega))) $$ Hil Hcl Hwl Hnp
  iintro %vra %vs0 %vs1 %rs' %ib' %H Hnh H0 H1 H2 - -
  iapply C $$ %vra %vs0 %vs1 %rs' %ib' %H Hnh H0 H1 H2

end release

end Weak
