/-
Weak: **W13-wit — hart 0 from `_entry` to its first UART store, a device-ACTIVE `xv6ConfS`
bundle** (plan `notes/weak-allocproc-plan.md` rev 45, §C top THIRD LAUNCH SET "W13 (W)" and §C
W13 (W): W13-wit, D31; [R38.s1]; [R41.s6]).

Lean-only, no Rocq twin.

## What this file proves

`w13Wit`: the one-row graph `W13Wit.GT` — hart 0's 28 memory events from `_entry` (PC
`0x80000000`, the boot landing file of `SrvwmoXv6Witness.sigma0`) through `start`, `timerinit`,
`mret`, `main`, `cpuid`, `consoleinit`, `initlock`, `uartinit`, `uartinitone` to its FIRST UART
STORE `sb zero,1(a5)` at `0x800008a0` (`Xv6/KernelImage.lean:1525`), the I/O event
`LIo .wr 0x10000001 [0]` at row position 27 — with a NON-EMPTY fabric list `gfDev = [(0, 27)]`
satisfies **`xv6ConfS`** (the device-active tagged conformance, `Weak/GraphFabConf.lean`) at xv6's
boot `xboot sigma0`, the boot fabric, the boot image and `NCPU + 1` rows; AND the same graph is
consistent under the tagged riscv.cat model (`rvwmoCatConsistentT`, computed, `catTConsistentBSound`).
`W13Wit.confB`: **the decidable side of `xv6ConfS`'s Bool twin** (`xv6ConfSB`, `Weak/W13WitRun.lean` §3) evaluates
`true` on the bundle — including the tagged well-formedness `gtdepsWf` over the REAL `rowDepsT` of
the run's emission, among them the I/O-endpoint edges into the UART store: `ld a5,0(a0)` →
`sb zero,1(a5)` (position 26 → 27, `DTaddr`, [R38.s2] (a)) and the `DTctrl`/`DTr13` edges from the
stack loads that fed the returns (positions 0, 5, 11, 20).  `W13Wit.gfDevWIo`: `gfDevWIo` holds on
the projected bundle, through `gfDevWIoOfXv6` (the HART half; the disk-side `usedElemGateOk` is
vacuous here — no disk row).

## How

The run is COMPUTED, not written down: `W13Wit.runRow` (`Weak/W13WitRun.lean` §1) steps the Sail
model node by node from hart 0's cycle boundary, at tick `false`, answering register reads from the
register file, fetches from the boot image (timestamp 0) and plain loads from the row's own stores
over the image (so the load values are the sequential ones), and stops after the first MMIO store
(`devWrite` of the boot fabric).  ONE kernel evaluation (`W13Wit.runOk`, `decide +kernel`, about
40 s on the build VM; 11 575 administrative nodes in front of the 28 events) checks that the run
succeeds with exactly the row `W13Wit.row` and the tagged deps `W13Wit.deps`; the runner's
soundness (`W13Wit.runRowSound`) turns that into the emission (`hemitf`), and `xv6ConfSZBSound`
assembles `xv6ConfS`.  The fabric is the boot fabric `efInit sigma0.wgdev` throughout, but for the
UART store's block, which moves it (its contact bit is the only `true` one).

SCOPE ([R41.s6]).  The witness exercises `gfDevWIo`'s HART half only: there is no disk activity
before the first UART store, so the disk half is vacuous here and the Bool twin cannot catch a
wrong guess about it; the disk half's computed check is W14's device-active witness.  The run
does not reach `allocproc` (W14).  The fetch clause of `w13Wit` is the Zifencei slot of
`xv6ConfS` (`emZifencei ∧ emFetchIn`; W5d-G G6-2's `w13WitZ`, renamed at G6-4, which retired the
PINNED `w13Wit` over `emFetchImg`): the runner answers fetches from the kernel-text image
`W13Wit.imText` (`[0x80000000, etext = 0x80007000)`), so the run itself shows every fetch reads
text, and `W13Wit.confZB` (`xv6ConfSZB`, kernel-evaluated) shows no write of the run touches text —
a pinned fetch of unwritten bytes satisfies `gzFetch` and has no fragment edge (`xv6ConfSZBSound`).

**Name map.**  None (Lean-only).  Main declarations: `W13Wit.row`, `W13Wit.deps`, `W13Wit.GT`,
`W13Wit.runOk`, `W13Wit.confB`, `W13Wit.catT`, `w13Wit`, `W13Wit.gfDevWIo`; W5d-G G6-2:
`W13Wit.imText`, `W13Wit.rowsOk`, `W13Wit.confZB`; helpers file-qualified `W13Wit.*`.
-/
import Weak.W13WitRun

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Dtag

/-! # 1. The run -/

def W13Wit.c0 : CPU := ⟨0, by decide⟩

/-- Hart 0 at its cycle boundary, at the boot landing file (PC `0x80000000`, `_entry`). -/
def W13Wit.h0 : W13Wit.Hs := ⟨FreeM.pure (), SrvwmoXv6Witness.rs0, ibNone⟩

/-- The boot fabric. -/
def W13Wit.d0 : Efab := efInit SrvwmoXv6Witness.sigma0.wgdev

/-- THE FETCH IMAGE (W5d-G G6-2): the boot image on the kernel TEXT `[0x80000000, etext)`
(`etext = 0x80007000`, `Xv6/KernelImage.lean`), nothing elsewhere.  The runner answers fetches
from it, so a fetch outside the text makes the run fail. -/
def W13Wit.imText : Image := fun z =>
  if decide (0x80000000 ≤ z ∧ z < 0x80007000) then W13Wit.imf z else none

theorem W13Wit.imTextSub : ∀ z b, W13Wit.imText z = some b → W13Wit.imf z = some b := by
  intro z b h
  unfold W13Wit.imText at h
  split at h
  · exact h
  · cases h

/-- THE RUN (unevaluated): at most 64 events, at most 40 000 administrative nodes per block;
loads answered over the boot image, fetches by the text image. -/
noncomputable def W13Wit.out : Option W13Wit.Out :=
  W13Wit.runRow W13Wit.c0 W13Wit.imf W13Wit.imText 40000 64 0 W13Wit.h0 wsInit dtInit [] 0 W13Wit.d0

/-- The `n` little-endian bytes of `v`. -/
def W13Wit.bs (n v : Nat) : List (BitVec 8) := WeakInterpProj.wbytes n (BitVec.ofNat (8 * n) v)

/-- THE ROW: hart 0's memory events, `_entry` to the first UART store (per event: its pc and the
number of administrative nodes in front of it).  Loads carry their per-byte write indices (0 = the
image). -/
def W13Wit.row : List Lbl := [
    -- 0: pc 0x80000004 (328 admin nodes)
    .LLoad false 0x8000a3e8 [0, 0, 0, 0, 0, 0, 0, 0] (W13Wit.bs 8 0x8000a420),
    -- 1: pc 0x8000005a (1359 admin nodes)
    .LStore false 0x8000b418 (W13Wit.bs 8 0x8000001a) .WCplain,
    -- 2: pc 0x8000005c (297 admin nodes)
    .LStore false 0x8000b410 (W13Wit.bs 8 0x0) .WCplain,
    -- 3: pc 0x8000001e (4586 admin nodes)
    .LStore false 0x8000b408 (W13Wit.bs 8 0x800000c2) .WCplain,
    -- 4: pc 0x80000020 (72 admin nodes)
    .LStore false 0x8000b400 (W13Wit.bs 8 0x8000b420) .WCplain,
    -- 5: pc 0x80000050 (897 admin nodes)
    .LLoad false 0x8000b408 [3, 3, 3, 3, 3, 3, 3, 3] (W13Wit.bs 8 0x800000c2),
    -- 6: pc 0x80000052 (66 admin nodes)
    .LLoad false 0x8000b400 [4, 4, 4, 4, 4, 4, 4, 4] (W13Wit.bs 8 0x8000b420),
    -- 7: pc 0x80000ed0 (495 admin nodes)
    .LStore false 0x8000b408 (W13Wit.bs 8 0x800000c2) .WCplain,
    -- 8: pc 0x80000ed2 (82 admin nodes)
    .LStore false 0x8000b400 (W13Wit.bs 8 0x8000b420) .WCplain,
    -- 9: pc 0x8000194a (255 admin nodes)
    .LStore false 0x8000b3f8 (W13Wit.bs 8 0x80000eda) .WCplain,
    -- 10: pc 0x8000194c (81 admin nodes)
    .LStore false 0x8000b3f0 (W13Wit.bs 8 0x8000b410) .WCplain,
    -- 11: pc 0x80001954 (234 admin nodes)
    .LLoad false 0x8000b3f8 [7, 7, 7, 7, 7, 7, 7, 7] (W13Wit.bs 8 0x80000eda),
    -- 12: pc 0x80001956 (75 admin nodes)
    .LLoad false 0x8000b3f0 [8, 8, 8, 8, 8, 8, 8, 8] (W13Wit.bs 8 0x8000b410),
    -- 13: pc 0x80000436 (489 admin nodes)
    .LStore false 0x8000b3f8 (W13Wit.bs 8 0x80000f14) .WCplain,
    -- 14: pc 0x80000438 (81 admin nodes)
    .LStore false 0x8000b3f0 (W13Wit.bs 8 0x8000b410) .WCplain,
    -- 15: pc 0x80000bda (445 admin nodes)
    .LStore false 0x8000b3e8 (W13Wit.bs 8 0x80000450) .WCplain,
    -- 16: pc 0x80000bdc (81 admin nodes)
    .LStore false 0x8000b3e0 (W13Wit.bs 8 0x8000b400) .WCplain,
    -- 17: pc 0x80000be0 (132 admin nodes)
    .LStore false 0x80012428 (W13Wit.bs 8 0x80007000) .WCplain,
    -- 18: pc 0x80000be2 (92 admin nodes)
    .LStore false 0x80012420 (W13Wit.bs 4 0x0) .WCplain,
    -- 19: pc 0x80000be6 (92 admin nodes)
    .LStore false 0x80012430 (W13Wit.bs 8 0x0) .WCplain,
    -- 20: pc 0x80000bea (75 admin nodes)
    .LLoad false 0x8000b3e8 [11, 11, 11, 11, 11, 11, 11, 11] (W13Wit.bs 8 0x80000450),
    -- 21: pc 0x80000bec (74 admin nodes)
    .LLoad false 0x8000b3e0 [12, 12, 12, 12, 12, 12, 12, 12] (W13Wit.bs 8 0x8000b400),
    -- 22: pc 0x800008e8 (300 admin nodes)
    .LStore false 0x8000b3e8 (W13Wit.bs 8 0x80000454) .WCplain,
    -- 23: pc 0x800008ea (82 admin nodes)
    .LStore false 0x8000b3e0 (W13Wit.bs 8 0x8000b400) .WCplain,
    -- 24: pc 0x80000898 (520 admin nodes)
    .LStore false 0x8000b3d8 (W13Wit.bs 8 0x80000902) .WCplain,
    -- 25: pc 0x8000089a (82 admin nodes)
    .LStore false 0x8000b3d0 (W13Wit.bs 8 0x8000b3f0) .WCplain,
    -- 26: pc 0x8000089e (125 admin nodes)
    .LLoad false 0x8000a390 [0, 0, 0, 0, 0, 0, 0, 0] (W13Wit.bs 8 0x10000000),
    -- 27: pc 0x800008a0 (78 admin nodes)
    .LIo .wr 0x10000001 (W13Wit.bs 1 0x0)
  ]

/-- THE TAGGED DEPS of the run's emission (`rowDepsT`; duplicates as the fold emits them). -/
def W13Wit.deps : List Redge := [
    ((0, 1), DTaddr), ((0, 2), DTaddr), ((0, 2), DTr13), ((0, 3), DTaddr),
    ((0, 3), DTr13), ((0, 4), DTaddr), ((0, 4), DTdata), ((0, 4), DTr13),
    ((0, 7), DTaddr), ((5, 7), DTdata), ((0, 7), DTdata), ((5, 7), DTctrl),
    ((0, 7), DTctrl), ((0, 7), DTr13), ((0, 8), DTaddr), ((6, 8), DTdata),
    ((0, 8), DTdata), ((5, 8), DTctrl), ((0, 8), DTctrl), ((0, 8), DTr13),
    ((0, 9), DTaddr), ((5, 9), DTctrl), ((0, 9), DTctrl), ((0, 9), DTr13),
    ((0, 10), DTaddr), ((0, 10), DTdata), ((5, 10), DTctrl), ((0, 10), DTctrl),
    ((0, 10), DTr13), ((0, 13), DTaddr), ((5, 13), DTctrl), ((0, 13), DTctrl),
    ((11, 13), DTctrl), ((0, 13), DTctrl), ((0, 13), DTr13), ((0, 14), DTaddr),
    ((12, 14), DTdata), ((0, 14), DTdata), ((5, 14), DTctrl), ((0, 14), DTctrl),
    ((11, 14), DTctrl), ((0, 14), DTctrl), ((0, 14), DTr13), ((0, 15), DTaddr),
    ((5, 15), DTctrl), ((0, 15), DTctrl), ((11, 15), DTctrl), ((0, 15), DTctrl),
    ((0, 15), DTr13), ((0, 16), DTaddr), ((0, 16), DTdata), ((5, 16), DTctrl),
    ((0, 16), DTctrl), ((11, 16), DTctrl), ((0, 16), DTctrl), ((0, 16), DTr13),
    ((5, 17), DTctrl), ((0, 17), DTctrl), ((11, 17), DTctrl), ((0, 17), DTctrl),
    ((0, 17), DTr13), ((5, 18), DTctrl), ((0, 18), DTctrl), ((11, 18), DTctrl),
    ((0, 18), DTctrl), ((0, 18), DTr13), ((5, 19), DTctrl), ((0, 19), DTctrl),
    ((11, 19), DTctrl), ((0, 19), DTctrl), ((0, 19), DTr13), ((0, 22), DTaddr),
    ((5, 22), DTctrl), ((0, 22), DTctrl), ((11, 22), DTctrl), ((0, 22), DTctrl),
    ((20, 22), DTctrl), ((0, 22), DTctrl), ((0, 22), DTr13), ((0, 23), DTaddr),
    ((21, 23), DTdata), ((0, 23), DTdata), ((5, 23), DTctrl), ((0, 23), DTctrl),
    ((11, 23), DTctrl), ((0, 23), DTctrl), ((20, 23), DTctrl), ((0, 23), DTctrl),
    ((0, 23), DTr13), ((0, 24), DTaddr), ((5, 24), DTctrl), ((0, 24), DTctrl),
    ((11, 24), DTctrl), ((0, 24), DTctrl), ((20, 24), DTctrl), ((0, 24), DTctrl),
    ((0, 24), DTr13), ((0, 25), DTaddr), ((0, 25), DTdata), ((5, 25), DTctrl),
    ((0, 25), DTctrl), ((11, 25), DTctrl), ((0, 25), DTctrl), ((20, 25), DTctrl),
    ((0, 25), DTctrl), ((0, 25), DTr13), ((26, 27), DTaddr), ((5, 27), DTctrl),
    ((0, 27), DTctrl), ((11, 27), DTctrl), ((0, 27), DTctrl), ((20, 27), DTctrl),
    ((0, 27), DTctrl), ((0, 27), DTr13)
  ]

/-- The run's check: it succeeds, with exactly this row and these deps. -/
def W13Wit.outOk (o : Option W13Wit.Out) : Bool :=
  match o with
  | some o => decide (o.oRow = W13Wit.row) && decide (o.oDeps = W13Wit.deps)
  | none => false

/-- **THE KERNEL EVALUATION** (the only one of the run). -/
theorem W13Wit.runOk : W13Wit.outOk W13Wit.out = true := by decide +kernel

theorem W13Wit.outSpec :
    ∃ o, W13Wit.out = some o ∧ o.oRow = W13Wit.row ∧ o.oDeps = W13Wit.deps := by
  have h := W13Wit.runOk
  generalize W13Wit.out = O at h ⊢
  cases O with
  | none => simp [W13Wit.outOk] at h
  | some o =>
    simp only [W13Wit.outOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨o, rfl, h.1, h.2⟩

theorem W13Wit.rowLen : W13Wit.row.length = 28 := by decide

/-- The row's last event is the UART store (IER := 0). -/
theorem W13Wit.rowIo : W13Wit.row[27]? = some (.LIo .wr 0x10000001 [0#8]) := by decide

/-! # 2. The bundle -/

/-- gmo = program order. -/
def W13Wit.gmo : List Geid := (List.range 28).map (fun k => (0, k))

/-- THE BUNDLE: one row (hart 0), the computable boot image, the run's tagged deps, and the
fabric list `[(0, 27)]` (the UART store). -/
def W13Wit.GT : GfexecT :=
  ⟨⟨⟨W13Wit.imf, [W13Wit.row], W13Wit.gmo⟩,
    W13Wit.deps.map (fun e => (((0, e.1.1), (0, e.1.2)), e.2)), []⟩, [(0, 27)]⟩

/-- The contact bits = the moved flags: the last block only. -/
def W13Wit.tqs : List Bool := (List.range 28).map (fun k => decide (k + 1 = 28))

def W13Wit.cert : GfRowCert := ⟨W13Wit.deps, W13Wit.tqs, W13Wit.tqs⟩

theorem W13Wit.tqsGetD : ∀ k, k < 28 → W13Wit.tqs.getD k false = decide (k + 1 = 28) := by
  decide

/-- **THE BOOL TWIN EVALUATES `true`** ([R38.s1]). -/
theorem W13Wit.confB : xv6ConfSB (NCPU + 1) W13Wit.GT [W13Wit.cert] = true := by decide +kernel

/-- … and the tagged riscv.cat model holds on the same graph (computed). -/
theorem W13Wit.catT : rvwmoCatConsistentT W13Wit.GT.gfGd :=
  catTConsistentBSound _ (by decide +kernel)

/-! # 3. The witness -/

theorem W13Wit.boot0 : xboot SrvwmoXv6Witness.sigma0 0 = W13Wit.pex W13Wit.c0 W13Wit.h0 := rfl

/-- (Lean-only) THE ROW FACTS of the run, at any image `P` the text pins transfer to: the
emission, its tagged deps, its fetches pinned to `P`, the contact bits / moved flags of the
certificate, the fabric trace. -/
theorem W13Wit.rowsOk (P : Image)
    (hP : ∀ l, WeakAxRealize.fetchPin W13Wit.imText l → WeakAxRealize.fetchPin P l) :
    ∃ fab : Nat → Efab, fab 0 = W13Wit.d0 ∧
      ∀ (i : Nat) (row : List Lbl) (rc : GfRowCert), W13Wit.GT.gfGd.gtG.gxProg[i]? = some row →
        [W13Wit.cert][i]? = some rc →
        ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
          hartConff i row (xboot SrvwmoXv6Witness.sigma0 i) dvi dvo tq em ∧
          rowDepsT em.emItems = rc.rcDeps ∧
          emFetchImg P em ∧
          (∀ k, k < row.length → tq k = rc.rcTq.getD k false) ∧
          (∀ k, k < row.length → rc.rcMoved.getD k false = false → dvi k = dvo k) ∧
          (∀ k n, W13Wit.GT.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1)) := by
  obtain ⟨o, hO, hrow, hdeps⟩ := W13Wit.outSpec
  obtain ⟨es, hem, hd, hf⟩ := W13Wit.runRowSound W13Wit.c0 W13Wit.imf W13Wit.imText 40000 W13Wit.d0
    28 64 0 W13Wit.h0 wsInit dtInit [] 0 o hO (by rw [hrow, W13Wit.rowLen])
  refine ⟨fun n => if n = 0 then W13Wit.d0 else o.oDfin, rfl, ?_⟩
  intro i row rc hrow' hrc
  cases i with
  | succ i => simp [W13Wit.GT] at hrow'
  | zero =>
    simp only [W13Wit.GT, List.getElem?_cons_zero, Option.some.injEq] at hrow'
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hrc
    subst hrow' hrc
    refine ⟨⟨es, W13Wit.pex W13Wit.c0 o.oFin⟩, fun _ => W13Wit.d0,
      fun j => if j + 1 = 28 then o.oDfin else W13Wit.d0, fun j => decide (j + 1 = 28),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show hemitf _ _ _ 0 wsInit W13Wit.row (xboot SrvwmoXv6Witness.sigma0 0) es _
      rw [W13Wit.boot0, ← hrow]
      exact hem
    · show rowDepsTAux dtInit es = W13Wit.deps
      rw [hd, hdeps]
    · intro l hl
      exact hP l (hf l hl)
    · intro k hk
      rw [W13Wit.rowLen] at hk
      exact (W13Wit.tqsGetD k hk).symm
    · intro k hk hmv
      rw [W13Wit.rowLen] at hk
      show W13Wit.d0 = if k + 1 = 28 then o.oDfin else W13Wit.d0
      have : ¬ (k + 1 = 28) := by
        have h2 := W13Wit.tqsGetD k hk
        simp only [W13Wit.cert] at hmv
        rw [hmv] at h2
        simpa using h2.symm
      simp [this]
    · intro k n hn
      simp only [W13Wit.GT] at hn
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨-, rfl⟩ := hn
        exact ⟨rfl, rfl⟩
      | succ n => simp at hn

/-- **THE ZIFENCEI BOOL TWIN EVALUATES `true`** (W5d-G G6-2): `xv6ConfSB` and no write of the
run touches the kernel text. -/
theorem W13Wit.confZB : xv6ConfSZB (NCPU + 1) W13Wit.GT [W13Wit.cert] W13Wit.imText = true := by
  decide +kernel

/-- **W13-wit** (W5d-G G6-2's `w13WitZ`, renamed at G6-4): xv6's hart 0, from `_entry` to its
first UART store, is a device-ACTIVE `xv6ConfS` bundle (non-empty `gfDev`, its one member the I/O
event) under the UNPINNED fetch clause `emZifencei ∧ emFetchIn` at the real boot — hart 0 fetches
only kernel text (the runner's fetch image) and writes none of it — and the same graph is
consistent under the tagged riscv.cat model. -/
theorem w13Wit :
    xv6ConfS (xboot SrvwmoXv6Witness.sigma0) (efInit SrvwmoXv6Witness.sigma0.wgdev)
      (imgZ SrvwmoXv6Witness.sigma0.wgimg) (NCPU + 1) W13Wit.GT ∧
    W13Wit.GT.gfDev = [(0, 27)] ∧
    W13Wit.GT.gfGd.gtG.gxProg = [W13Wit.row] ∧
    W13Wit.row[27]? = some (.LIo .wr 0x10000001 [0#8]) ∧
    rvwmoCatConsistentT W13Wit.GT.gfGd := by
  have himg : imgZ SrvwmoXv6Witness.sigma0.wgimg = W13Wit.imf := W13Wit.imfEq
  obtain ⟨fab, hfab, hr⟩ := W13Wit.rowsOk W13Wit.imText (fun _ h => h)
  exact ⟨(xv6ConfSZBSound (xboot SrvwmoXv6Witness.sigma0) (efInit SrvwmoXv6Witness.sigma0.wgdev)
    (imgZ SrvwmoXv6Witness.sigma0.wgimg) (NCPU + 1) W13Wit.GT [W13Wit.cert] fab W13Wit.imText
    W13Wit.confZB himg.symm hfab (by rw [himg]; exact W13Wit.imTextSub) hr).1,
    rfl, rfl, W13Wit.rowIo, W13Wit.catT⟩

/-- The HART half of `gfDevWIo`, exercised: the projected bundle's fabric members are writes or
I/O events (`gfDevWIoOfXv6`; `usedElemGateOk` is vacuous — the bundle has no disk row). -/
theorem W13Wit.gfDevWIo : gfDevWIo (forgetF W13Wit.GT) := by
  obtain ⟨-, hlen, fab, hconf, -⟩ := xv6ConfSForget _ _ _ _ _ w13Wit.1
  refine gfDevWIoOfXv6 _ _ fab _ hconf (GraphFabConf.xbootHart SrvwmoXv6Witness.sigma0) hlen ?_
  intro k hk
  simp [forgetF, W13Wit.GT, NCPU] at hk

end Weak
