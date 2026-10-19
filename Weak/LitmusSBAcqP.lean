/-
Weak: **allocproc route P, spike P0(b)** (`notes/weak-allocproc-routeP-design.md` §0 FINDING F-P1, §5
row P0 (b), §8 Q-P-R1).  Lean-only, no Rocq twin.  A LEAF: nothing imports this file (it imports
`Weak.LitmusSBAcq`, whose `SBAcq.*` kit and Litmus 1 it reuses).

## Spec first (RVWMO / riscv.cat / Sail / Zifencei / PMAs)

A RAM store `w` followed in program order by an MMIO store `X` with NO fence between: RVWMO's ppo
orders `w` before `X` only by rule 4 with a fence whose predecessor set has `w` and whose successor
set has `o` (`fence w,o` or wider), by rule 6/7 (`X` cannot carry `.rl`; it is a plain `sb`), or by a
dependency (whose source is a READ — `w` is a store).  The PMA memory-ordering attributes order I/O
accesses among themselves (strongly-ordered channels), never a main-memory access against an I/O one;
the unprivileged spec's I/O-ordering appendix says ordering between main memory and I/O comes only from
FENCEs with i/o bits.  xv6 runs with `menvcfg = 0` and Sail's `execute_FENCE` keys on the memory bits
only (D48, `GraphFabResidue` header), so not even a `fence iorw,iorw` would order the pair; xv6 has none
there anyway (the image's seven fences: `release`, `main`'s two `started` fences, `virtio_disk_rw`'s and
`virtio_disk_intr`'s two each).  Zifencei is silent.  So **under RVWMO + PMAs the THR store `X` may
precede `w` in global memory order** — the census's "`w‴ <gmo X` is not required" is right w.r.t. the
ISA.  The published theorem's trusted I/O item `ioResidueGmo` (`Weak/GraphFabResidue.lean`, arm (R1):
a RAM access po-before an I/O event is gmo-before it; [OWN.12] D32 (a′), [OWN.53] (R3′)) is therefore
**STRONGER than RVWMO + PMAs** (a named platform assumption: QEMU-TCG MMIO acts as a one-way fence).

## What is proved

* §1 the residue arms as edges: `SBAcqP.r1Lt` (R1), `SBAcqP.r2Lt` (R2), `SBAcqP.fabLt` (R3, fabric),
  and the composite I/O HOP `SBAcqP.ioHop` (RAM `w` <po I/O `X` <fab I/O `L` <po RAM write `R` ⇒
  `w <gmo R`): under the item, no RAM store can be overtaken through a device by a hand-off.
* §2 **F-P1, the UART-0 3-hart chain** (`notes/W10-K0-census.md` §3, pcs of `Xv6/KernelImage.lean`):
  hart 2 = `sleep_prepare`'s `release(P2.lock)` store `w‴` (`0x80000cfa`), `acquire(uarts[0].tx)`,
  LSR read (`0x80000976`), THR store `X` (`0x80000988`); hart 1 = `uartintr(0)`'s LSR read `LSR₁`
  (`0x80000a3a`, THRE = 0: `X` before it in fabric order), `consoleintr`'s `acquire(cons)` /
  `release(cons)` (`R_y`); hart 3 = the next `consoleintr`'s `acquire(cons)` (`A_y3`, reads `R_y`),
  then `wakeup` → `acquire(P2.lock)`: `holding+0x0` (`r3`) reads the stale 1, the `amoswap` fails.
  `SBAcqP.uCat`/`SBAcqP.uCatT`: the chain is RVWMO-CONSISTENT (witness `SBAcqP.uBuffered`: `X` is
  gmo-before `w‴`).  `SBAcqP.uIoNo`: **in EVERY gmo (any image, any deps) with the chain's rf and
  fabric order, `ioResidueGmo` FAILS** — the cycle `w‴ <R1 X <R3 LSR₁ <R2 R_y <rf A_y3 <aq r3 <fr w‴`.
  `SBAcqP.uNotIo` (the witness violates the item) and `SBAcqP.uNoR1Ok` (the witness satisfies every
  OTHER arm: (R2), (R2′), (R3)) — so (R1) is exactly the arm that excludes it.  The 2-hart variant
  (hart 1's own `wakeup`): `SBAcqP.u2Cat`, `SBAcqP.u2IoNo`, `SBAcqP.u2NotIo`.  **F-P1 CONFIRMED.**
* §3 **the route-P member of Litmus 1** (non-vacuity).  `SBAcqP.FifoCore` (issue/land positions: each
  hart's events in program order, a plain store ISSUES at its step and LANDS later, FIFO per hart,
  drains at a `pw ∧ sr` fence / `.rl` / a same-address exclusive read; an AMO lands at its step),
  `SBAcqP.ReadsGF` (every member read returns GF's source: forwarded from the hart's own pending
  po-latest store, or the landed co-latest write at the read's step — reads at the landed TOP),
  `SBAcqP.CoGF` (landing order = GF co per byte) and the design's §3.2 gate (`SBAcqP.GateWr`: a write
  lands only after every GF reader of a co-earlier write is realized; `SBAcqP.gateRdOf`: every read's
  source is landed or own).  `SBAcqP.l1MemberP`: Litmus 1 (`SBAcq.l1`) HAS such a member — the §4
  table of the design, both release stores landing after the other hart's failed `amoswap` (`decide
  +kernel`).  `SBAcqP.l1NeedsLanding`: with landing at issue there is none — the landing freedom is
  what the member uses.
* §4 **the δ1′ worst candidate, the racy `ip->ref` read** (`ilock+0xe`, census row 3.3, route T):
  hart 2 releases `z`, takes `itable.lock` and increments `ip->ref` (no fence between the release and
  the increment); hart 1's racy `ilock` read sees the increment, then `acquiresleep` releases
  `ip->lock.lk`; hart 3 acquires it and reads `z` stale.  `SBAcqP.l3Cat`: RVWMO-consistent (the census
  site satisfies `l2cNo`'s "unsynchronized read of a store made after a buffered release");
  `SBAcqP.l3NoMember`: no δ1′ lockstep member with the SAME rf (`SBAcq.TsoCore` + `SBAcq.floorSrc`);
  `SBAcqP.l3MemberT`: a δ1′ member EXISTS once the racy read is re-sourced to an older `≥ 1` value (the
  route-T taint discharge: the value feeds only `blez → unreachable`).  So δ1′'s sufficiency on this
  site rests on the 6m T-datum, not on the order.

Spec: theorems about the existing model and the trusted item's TEXT; nothing assumed.  Lean-only
helpers `SBAcqP.*`.
-/
import Weak.LitmusSBAcq
import Weak.GraphFabResidue

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The residue arms as gmo edges -/

/-- (R1): a RAM access po-before an I/O event is gmo-before it. -/
theorem SBAcqP.r1Lt (GF : Gfexec) (w x : Geid) (lw lx : Lbl) (hio : ioResidueGmo GF)
    (hw : gxLbl GF.gfGd.gdG w = some lw) (hx : gxLbl GF.gfGd.gdG x = some lx)
    (ha : w.1 = x.1) (hk : w.2 < x.2) (hm : lbIsMem lw = true) (hn : lbIsIo lw = false)
    (hi : lbIsIo lx = true) : gmoLt GF.gfGd.gdG w x :=
  hio w x (Or.inl ⟨SBAcq.gpoOf _ w x lw lx hw hx ha hk, ⟨lw, hw, hm⟩,
    by unfold gisIo; rw [hw]; exact hn, by unfold gisIo; rw [hx]; exact hi⟩)

/-- (R2): an I/O event po-before a RAM write is gmo-before it. -/
theorem SBAcqP.r2Lt (GF : Gfexec) (x y : Geid) (lx ly : Lbl) (hio : ioResidueGmo GF)
    (hx : gxLbl GF.gfGd.gdG x = some lx) (hy : gxLbl GF.gfGd.gdG y = some ly)
    (ha : x.1 = y.1) (hk : x.2 < y.2) (hi : lbIsIo lx = true) (hW : lbIsW ly = true) :
    gmoLt GF.gfGd.gdG x y :=
  hio x y (Or.inr (Or.inl ⟨SBAcq.gpoOf _ x y lx ly hx hy ha hk,
    by unfold gisIo; rw [hx]; exact hi, by unfold gisW; rw [hy]; exact hW⟩))

/-- (R3), fabric part: `gmem` fabric members in fabric order. -/
theorem SBAcqP.fabLt (GF : Gfexec) (x y : Geid) (lx ly : Lbl) (hio : ioResidueGmo GF)
    (hx : gxLbl GF.gfGd.gdG x = some lx) (hy : gxLbl GF.gfGd.gdG y = some ly)
    (hmx : lbIsMem lx = true) (hmy : lbIsMem ly = true) (hb : gfBefore GF x y) :
    gmoLt GF.gfGd.gdG x y :=
  hio x y (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨lx, hx, hmx⟩, ⟨ly, hy, hmy⟩, hb⟩))))

/-- **THE I/O HOP**: a RAM access `w` po-before an I/O event `X` of its hart, `X` before `L` in fabric
order, `L` an I/O event po-before a RAM WRITE `R` of another (or the same) hart: `w <gmo R`.  Every
hand-off of information from one hart to another through a device has this shape. -/
theorem SBAcqP.ioHop (GF : Gfexec) (w X L R : Geid) (lw lX lL lR : Lbl) (hio : ioResidueGmo GF)
    (hw : gxLbl GF.gfGd.gdG w = some lw) (hX : gxLbl GF.gfGd.gdG X = some lX)
    (hL : gxLbl GF.gfGd.gdG L = some lL) (hR : gxLbl GF.gfGd.gdG R = some lR)
    (h1 : w.1 = X.1) (h2 : w.2 < X.2) (hmw : lbIsMem lw = true) (hnw : lbIsIo lw = false)
    (hiX : lbIsIo lX = true) (hfab : gfBefore GF X L) (hiL : lbIsIo lL = true)
    (h3 : L.1 = R.1) (h4 : L.2 < R.2) (hWR : lbIsW lR = true) : gmoLt GF.gfGd.gdG w R :=
  gmoLtTrans _ _ _ _ (SBAcqP.r1Lt GF w X lw lX hio hw hX h1 h2 hmw hnw hiX)
    (gmoLtTrans _ _ _ _
      (SBAcqP.fabLt GF X L lX lL hio hX hL (by simp [lbIsMem, hiX]) (by simp [lbIsMem, hiL]) hfab)
      (SBAcqP.r2Lt GF L R lL lR hio hL hR h3 h4 hiL hWR))

/-! # 2. F-P1 — the UART-0 3-hart chain

Row = census hart − 1.  Bytes: `z` = `P2.lock` = 0, `y` = `cons` = 2, `uarts[0].tx` = 3; I/O
addresses UART 0 THR `0x10000000`, LSR `0x10000005`.
Row 0 (hart 1, `uartintr(0)` → `consoleintr`): `LSR₁` (0,0) THRE = 0; `acquire(cons)` (0,1); release
fence `rw,w` (0,2); `R_y` = `sw zero` (0,3).
Row 1 (hart 2, `uartwrite`): `sleep_prepare`'s `acquire(P2.lock)` (1,0); release fence (1,1); `w‴`
(1,2); `acquire(uarts[0].tx)` (1,3); LSR read (1,4); THR store `X` (1,5).
Row 2 (hart 3, `consoleintr` → `wakeup`): `A_y3` (2,0) reads `R_y`; `holding+0x0` `r3` (2,1) reads
`P2.lock = 1` from (1,0); the `amoswap.w.aq` fails (2,2). -/

def SBAcqP.thr : Int := 0x10000000

def SBAcqP.lsr : Int := 0x10000005

def SBAcqP.uProg (ty t3 : Nat) : List (List Lbl) :=
  [[LIo .rd SBAcqP.lsr [0#8],
    LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 2 [b0] .WCplain],
   [LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain,
    LRmw true false 3 [0] [b0] [b1] .WCexcl,
    LIo .rd SBAcqP.lsr [0x60#8],
    LIo .wr SBAcqP.thr [0x24#8]],
   [LRmw true false 2 [ty] [b0] [b1] .WCexcl,
    LLoad false 0 [t3] [b1],
    LRmw true false 0 [t3] [b1] [b1] .WCexcl]]

/-- The witness gmo: hart 2's acquires and MMIO first, the chain, `w‴` LAST. -/
def SBAcqP.uGmo : List Geid :=
  [(1, 0), (1, 3), (1, 4), (1, 5), (0, 0), (0, 1), (0, 3), (2, 0), (2, 1), (2, 2), (1, 2)]

def SBAcqP.uGd : Gdexec := AxLitmus.mkgd (SBAcqP.uProg 4 1) SBAcqP.uGmo []

/-- The bundle: fabric order = hart 2's LSR read, its THR store, hart 1's LSR read. -/
def SBAcqP.uF : Gfexec := ⟨SBAcqP.uGd, [(1, 4), (1, 5), (0, 0)]⟩

/-- **THE UART CHAIN IS RVWMO-CONSISTENT** (the faithful cat model). -/
theorem SBAcqP.uCat : rvwmoCatConsistent SBAcqP.uGd := catConsistentBSound _ (by decide +kernel)

/-- The tagged model, with the control dependencies (`uartintr`'s branch on `LSR₁` into its later
stores, the spin loops, `uartwrite`'s LSR/tx-lock branches into the THR store). -/
def SBAcqP.uDeps : List Tdep :=
  [(((0, 0), (0, 1)), Dtag.DTctrl), (((0, 0), (0, 3)), Dtag.DTctrl), (((0, 1), (0, 3)), Dtag.DTctrl),
   (((1, 0), (1, 2)), Dtag.DTctrl), (((1, 0), (1, 3)), Dtag.DTctrl), (((1, 3), (1, 5)), Dtag.DTctrl),
   (((1, 4), (1, 5)), Dtag.DTctrl), (((2, 0), (2, 2)), Dtag.DTctrl), (((2, 1), (2, 2)), Dtag.DTctrl)]

theorem SBAcqP.uCatT : rvwmoCatConsistentT (mkgt (SBAcqP.uProg 4 1) SBAcqP.uGmo SBAcqP.uDeps) :=
  catTConsistentBSound _ (by decide +kernel)

/-- The outcome's rf: `A_y3` reads `R_y` (write #4), `r3`/the failed spin read hart 2's acquire
(write #1). -/
theorem SBAcqP.uRf : gwriteAt SBAcqP.uGd.gdG 4 = some (0, 3) ∧ gwriteAt SBAcqP.uGd.gdG 1 = some (1, 0) := by
  decide +kernel

/-- In the witness the THR store and `LSR₁` are gmo-BEFORE `w‴` (the RVWMO freedom). -/
theorem SBAcqP.uBuffered :
    gmoLt SBAcqP.uGd.gdG (1, 5) (1, 2) ∧ gmoLt SBAcqP.uGd.gdG (0, 0) (1, 2) :=
  ⟨(gmoLtBSpec _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩

/-- No `.rl` bit (rules 6/8, omitted by the tree's cat model, are vacuous). -/
theorem SBAcqP.uNoRl : (SBAcqP.uProg 4 1).flatten.all (fun l => !lbRl l) = true := by decide +kernel

/-- **F-P1: THE UART CHAIN IS EXCLUDED BY THE TRUSTED I/O ITEM** — every gmo (any image, any deps)
with the chain's rf and fabric order violates `ioResidueGmo`:
`w‴ <R1 X <R3 LSR₁ <R2 R_y <rf A_y3 <aq r3 <fr w‴`. -/
theorem SBAcqP.uIoNo (GF : Gfexec) (ty t3 : Nat) (hP : GF.gfGd.gdG.gxProg = SBAcqP.uProg ty t3)
    (hok : SBAcq.Ok6 GF.gfGd.gdG) (hio : ioResidueGmo GF) (hfab : gfBefore GF (1, 5) (0, 0))
    (hsy : gwriteAt GF.gfGd.gdG ty = some (0, 3)) (hs3 : gwriteAt GF.gfGd.gdG t3 = some (1, 0)) :
    False := by
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L00 : gxLbl GF.gfGd.gdG (0, 0) = some (LIo .rd SBAcqP.lsr [0#8]) :=
    (SBAcq.lblOf _ _ hP 0 0).trans rfl
  have L03 : gxLbl GF.gfGd.gdG (0, 3) = some (LStore false 2 [b0] .WCplain) :=
    (SBAcq.lblOf _ _ hP 0 3).trans rfl
  have L10 : gxLbl GF.gfGd.gdG (1, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf _ _ hP 1 0).trans rfl
  have L12 : gxLbl GF.gfGd.gdG (1, 2) = some (LStore false 0 [b0] .WCplain) :=
    (SBAcq.lblOf _ _ hP 1 2).trans rfl
  have L15 : gxLbl GF.gfGd.gdG (1, 5) = some (LIo .wr SBAcqP.thr [0x24#8]) :=
    (SBAcq.lblOf _ _ hP 1 5).trans rfl
  have L20 : gxLbl GF.gfGd.gdG (2, 0) = some (LRmw true false 2 [ty] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf _ _ hP 2 0).trans rfl
  have L21 : gxLbl GF.gfGd.gdG (2, 1) = some (LLoad false 0 [t3] [b1]) :=
    (SBAcq.lblOf _ _ hP 2 1).trans rfl
  have k1 := SBAcqP.r1Lt GF (1, 2) (1, 5) _ _ hio L12 L15 rfl (by decide) rfl rfl rfl
  have k2 := SBAcqP.fabLt GF (1, 5) (0, 0) _ _ hio L15 L00 rfl rfl hfab
  have k3 := SBAcqP.r2Lt GF (0, 0) (0, 3) _ _ hio L00 L03 rfl (by decide) rfl rfl
  exact SBAcq.l2Core _ hwf hlv (1, 0) (1, 2) (0, 0) (0, 3) (2, 0) (2, 1) 2 0 ty t3 b0 b1 b0
    (SBAcq.rdRmw _ _ _ _ _ _ _ _ _ L20) hsy (by decide)
    (SBAcq.rdLd _ _ _ _ _ _ L21) hs3 (SBAcq.wrSt _ _ _ _ _ _ L12)
    (SBAcq.acqLt _ _ _ _ _ hp L10 L12 rfl (by decide) rfl rfl rfl) (by decide)
    k3 (SBAcq.acqLt _ _ _ _ _ hp L20 L21 rfl (by decide) rfl rfl rfl) (gmoLtTrans _ _ _ _ k1 k2)

/-- …so the RVWMO-consistent witness bundle violates the item. -/
theorem SBAcqP.uNotIo : ¬ ioResidueGmo SBAcqP.uF := fun h =>
  SBAcqP.uIoNo SBAcqP.uF 4 1 rfl (SBAcq.ok6OfCat _ SBAcqP.uCat) h ⟨1, 2, rfl, rfl, by omega⟩
    SBAcqP.uRf.1 SBAcqP.uRf.2

/-! ## 2.1 (R1) is the arm that excludes it: the witness satisfies every other arm -/

/-- The residue minus (R1): (R2) ∨ (R2′) ∨ (R3) — `ioResidue GF x y ↔ (R1) ∨ ioResidueNoR1 GF x y`
holds by `Iff.rfl`. -/
def SBAcqP.ioResidueNoR1 (GF : Gfexec) (x y : Geid) : Prop :=
  (WeakRvwmoGraph.gpo GF.gfGd.gdG x y ∧ gisIo GF.gfGd.gdG x = true ∧
    gisW GF.gfGd.gdG y = true) ∨
  (WeakRvwmoGraph.gpo GF.gfGd.gdG x y ∧ gisIo GF.gfGd.gdG x = true ∧
    gisR GF.gfGd.gdG y = true ∧ y.1 = NCPU) ∨
  (gisIo GF.gfGd.gdG x = true ∧ gisIo GF.gfGd.gdG y = true ∧ WeakRvwmoGraph.gpo GF.gfGd.gdG x y) ∨
  (gmem GF.gfGd.gdG x ∧ gmem GF.gfGd.gdG y ∧ gfBefore GF x y)

theorem SBAcqP.ioResidueSplit (GF : Gfexec) (x y : Geid) :
    ioResidue GF x y ↔
      (WeakRvwmoGraph.gpo GF.gfGd.gdG x y ∧ gmem GF.gfGd.gdG x ∧
        gisIo GF.gfGd.gdG x = false ∧ gisIo GF.gfGd.gdG y = true) ∨ SBAcqP.ioResidueNoR1 GF x y :=
  Iff.rfl

def SBAcqP.beforeB (L : List Geid) (x y : Geid) : Bool :=
  (List.range L.length).any (fun i => (List.range L.length).any (fun j =>
    decide (L[i]? = some x) && decide (L[j]? = some y) && decide (i < j)))

theorem SBAcqP.beforeBOf (L : List Geid) (x y : Geid) : before L x y → SBAcqP.beforeB L x y = true := by
  rintro ⟨i, j, hi, hj, hij⟩
  have hil : i < L.length := lookup_lt_is_Some.1 (by rw [hi]; rfl)
  have hjl : j < L.length := lookup_lt_is_Some.1 (by rw [hj]; rfl)
  unfold SBAcqP.beforeB
  rw [existsbExistsTrue]
  refine ⟨i, List.mem_range.2 hil, ?_⟩
  show (List.range L.length).any (fun j =>
    decide (L[i]? = some x) && decide (L[j]? = some y) && decide (i < j)) = true
  rw [existsbExistsTrue]
  exact ⟨j, List.mem_range.2 hjl, by simp [hi, hj, hij]⟩

def SBAcqP.armsNoR1B (GF : Gfexec) (x y : Geid) : Bool :=
  (gpoB GF.gfGd.gdG x y && gisIo GF.gfGd.gdG x && gisW GF.gfGd.gdG y) ||
  (gpoB GF.gfGd.gdG x y && gisIo GF.gfGd.gdG x && gisR GF.gfGd.gdG y && decide (y.1 = NCPU)) ||
  (gisIo GF.gfGd.gdG x && gisIo GF.gfGd.gdG y && gpoB GF.gfGd.gdG x y) ||
  (glblB GF.gfGd.gdG x lbIsMem && glblB GF.gfGd.gdG y lbIsMem && SBAcqP.beforeB GF.gfDev x y)

def SBAcqP.resNoR1B (GF : Gfexec) : Bool :=
  (gevents GF.gfGd.gdG).all (fun x => (gevents GF.gfGd.gdG).all (fun y =>
    !SBAcqP.armsNoR1B GF x y || gmoLtB GF.gfGd.gdG x y))

theorem SBAcqP.resNoR1BSound (GF : Gfexec) :
    SBAcqP.resNoR1B GF = true → ∀ x y, SBAcqP.ioResidueNoR1 GF x y → gmoLt GF.gfGd.gdG x y := by
  intro hb x y hr
  unfold SBAcqP.ioResidueNoR1 at hr
  have hxy : x ∈ gevents GF.gfGd.gdG ∧ y ∈ gevents GF.gfGd.gdG := by
    rcases hr with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨-, -, hp⟩ | ⟨⟨lx, hx, -⟩, ⟨ly, hy, -⟩, -⟩
    · exact gpoGevents _ _ _ hp
    · exact gpoGevents _ _ _ hp
    · exact gpoGevents _ _ _ hp
    · exact ⟨geventsOfLbl _ _ _ hx, geventsOfLbl _ _ _ hy⟩
  have h := (forallbForallTrue _ _).1 ((forallbForallTrue _ _).1 hb x hxy.1) y hxy.2
  have harm : SBAcqP.armsNoR1B GF x y = true := by
    unfold SBAcqP.armsNoR1B
    rcases hr with ⟨hp, h1, h2⟩ | ⟨hp, h1, h2, h3⟩ | ⟨h1, h2, hp⟩ | ⟨hx, hy, hb'⟩
    · simp [(gpoBSpec _ _ _).2 hp, h1, h2]
    · simp [(gpoBSpec _ _ _).2 hp, h1, h2, h3]
    · simp [(gpoBSpec _ _ _).2 hp, h1, h2]
    · simp [(glblBSpec _ _ lbIsMem).2 hx, (glblBSpec _ _ lbIsMem).2 hy, SBAcqP.beforeBOf _ _ _ hb']
  simp only [harm, Bool.not_true, Bool.false_or] at h
  exact (gmoLtBSpec _ _ _).1 h

/-- **(R1) IS THE ONLY ARM THAT BITES**: the RVWMO-consistent UART witness satisfies (R2), (R2′) and
(R3); with `SBAcqP.uNotIo`, the chain lives exactly in the gap between RVWMO + PMAs (+ the device
fabric) and (R1). -/
theorem SBAcqP.uNoR1Ok : ∀ x y, SBAcqP.ioResidueNoR1 SBAcqP.uF x y → gmoLt SBAcqP.uF.gfGd.gdG x y :=
  SBAcqP.resNoR1BSound _ (by decide +kernel)

/-! ## 2.2 The 2-hart UART variant (census §3 end): hart 1's OWN `wakeup`

Row 0 (hart 1): `LSR₁` (0,0); `acquire(cons)` (0,1); `wakeup` → `holding+0x0` on `P2.lock` (0,2),
stale; the failed `amoswap` (0,3).  Row 1 = hart 2 as above. -/

def SBAcqP.u2Prog (t1 : Nat) : List (List Lbl) :=
  [[LIo .rd SBAcqP.lsr [0#8],
    LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LLoad false 0 [t1] [b1],
    LRmw true false 0 [t1] [b1] [b1] .WCexcl],
   [LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain,
    LRmw true false 3 [0] [b0] [b1] .WCexcl,
    LIo .rd SBAcqP.lsr [0x60#8],
    LIo .wr SBAcqP.thr [0x24#8]]]

def SBAcqP.u2Gmo : List Geid :=
  [(1, 0), (1, 3), (1, 4), (1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (1, 2)]

def SBAcqP.u2Gd : Gdexec := AxLitmus.mkgd (SBAcqP.u2Prog 1) SBAcqP.u2Gmo []

def SBAcqP.u2F : Gfexec := ⟨SBAcqP.u2Gd, [(1, 4), (1, 5), (0, 0)]⟩

theorem SBAcqP.u2Cat : rvwmoCatConsistent SBAcqP.u2Gd := catConsistentBSound _ (by decide +kernel)

theorem SBAcqP.u2Rf : gwriteAt SBAcqP.u2Gd.gdG 1 = some (1, 0) := by decide +kernel

/-- The 2-hart variant is excluded too: `w‴ <(R1;R3;R2) A_cons <aq r1 <fr w‴`. -/
theorem SBAcqP.u2IoNo (GF : Gfexec) (t1 : Nat) (hP : GF.gfGd.gdG.gxProg = SBAcqP.u2Prog t1)
    (hok : SBAcq.Ok6 GF.gfGd.gdG) (hio : ioResidueGmo GF) (hfab : gfBefore GF (1, 5) (0, 0))
    (hs1 : gwriteAt GF.gfGd.gdG t1 = some (1, 0)) : False := by
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L00 : gxLbl GF.gfGd.gdG (0, 0) = some (LIo .rd SBAcqP.lsr [0#8]) :=
    (SBAcq.lblOf _ _ hP 0 0).trans rfl
  have L01 : gxLbl GF.gfGd.gdG (0, 1) = some (LRmw true false 2 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf _ _ hP 0 1).trans rfl
  have L02 : gxLbl GF.gfGd.gdG (0, 2) = some (LLoad false 0 [t1] [b1]) :=
    (SBAcq.lblOf _ _ hP 0 2).trans rfl
  have L10 : gxLbl GF.gfGd.gdG (1, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf _ _ hP 1 0).trans rfl
  have L12 : gxLbl GF.gfGd.gdG (1, 2) = some (LStore false 0 [b0] .WCplain) :=
    (SBAcq.lblOf _ _ hP 1 2).trans rfl
  have L15 : gxLbl GF.gfGd.gdG (1, 5) = some (LIo .wr SBAcqP.thr [0x24#8]) :=
    (SBAcq.lblOf _ _ hP 1 5).trans rfl
  have k1 := SBAcqP.ioHop GF (1, 2) (1, 5) (0, 0) (0, 1) _ _ _ _ hio L12 L15 L00 L01
    rfl (by decide) rfl rfl rfl hfab rfl rfl (by decide) rfl
  have k2 := SBAcq.acqLt _ _ _ _ _ hp L01 L02 rfl (by decide) rfl rfl rfl
  have k3 := SBAcq.frLt _ (0, 2) (1, 0) (1, 2) 0 t1 b1 b0 hwf hlv (SBAcq.rdLd _ _ _ _ _ _ L02) hs1
    (SBAcq.wrSt _ _ _ _ _ _ L12) (SBAcq.acqLt _ _ _ _ _ hp L10 L12 rfl (by decide) rfl rfl rfl)
    (by decide)
  exact gmoLtIrrefl _ (1, 2) (gmoLtTrans _ _ _ _ k1 (gmoLtTrans _ _ _ _ k2 k3))

theorem SBAcqP.u2NotIo : ¬ ioResidueGmo SBAcqP.u2F := fun h =>
  SBAcqP.u2IoNo SBAcqP.u2F 1 rfl (SBAcq.ok6OfCat _ SBAcqP.u2Cat) h ⟨1, 2, rfl, rfl, by omega⟩
    SBAcqP.u2Rf

/-! # 3. The route-P member: a FIFO store buffer with landings (design §2.2, §3.2)

Positions: `p e` = event `e`'s step (a plain store's ISSUE), `q w` = plain store `w`'s LANDING; an AMO
(exclusive) write lands at its step.  `lpos` = the landing position of any write. -/

/-- A draining fence: predecessor `w` and successor `r` (`rw,rw`, `rw,r`, `w,rw`, `w,r`, `tso`). -/
def SBAcqP.isDrainF (l : Lbl) : Bool :=
  match l with
  | LFence _ pw sr _ => pw && sr
  | _ => false

/-- An exclusive access (its read half drains the hart's overlapping pending stores). -/
def SBAcqP.isExcl (l : Lbl) : Bool :=
  match l with
  | LRmw .. => true
  | _ => false

def SBAcqP.lpos (G : Gexec) (p q : Geid → Nat) (w : Geid) : Nat :=
  if glblB G w SBAcq.isSt = true then q w else p w

/-- The FIFO/landing core (machine rules §2.2: issue, land, FIFO, drains). -/
structure SBAcqP.FifoCore (G : Gexec) (p q : Geid → Nat) : Prop where
  po : ∀ e1 e2, WeakRvwmoGraph.gpo G e1 e2 → p e1 < p e2
  issue : ∀ w, glblIs G w SBAcq.isSt → p w < q w
  fifo : ∀ w1 w2, WeakRvwmoGraph.gpo G w1 w2 → glblIs G w1 SBAcq.isSt → glblIs G w2 SBAcq.isSt →
    q w1 < q w2
  drainF : ∀ w f, WeakRvwmoGraph.gpo G w f → glblIs G w SBAcq.isSt → glblIs G f SBAcqP.isDrainF →
    q w < p f
  drainRl : ∀ w e, WeakRvwmoGraph.gpo G w e → glblIs G w SBAcq.isSt → glblIs G e lbRl → q w < p e
  drainX : ∀ w e a u t v, WeakRvwmoGraph.gpo G w e → glblIs G w SBAcq.isSt → gwritesByte G w a u →
    glblIs G e SBAcqP.isExcl → greadsByte G e a t v → q w < p e

/-- **Every member read returns GF's source** (lockstep with EQUAL values): forwarded from the
hart's own pending po-latest store to the byte, or the landed co-latest write at the read's step (the
member reads at the landed TOP); an image read sees no landed write and no own earlier store. -/
def SBAcqP.ReadsGF (G : Gexec) (p q : Geid → Nat) : Prop :=
  (∀ r a t v w, greadsByte G r a t v → gwriteAt G t = some w →
    (WeakRvwmoGraph.gpo G w r ∧ glblIs G w SBAcq.isSt ∧ p r < q w ∧
      ∀ w' u, WeakRvwmoGraph.gpo G w w' → WeakRvwmoGraph.gpo G w' r → ¬ gwritesByte G w' a u) ∨
    (SBAcqP.lpos G p q w < p r ∧
      (∀ w' u, gwritesByte G w' a u → w' ≠ r → SBAcqP.lpos G p q w < SBAcqP.lpos G p q w' →
        p r < SBAcqP.lpos G p q w') ∧
      (∀ w' u, WeakRvwmoGraph.gpo G w' r → glblIs G w' SBAcq.isSt → gwritesByte G w' a u →
        q w' < p r))) ∧
  (∀ r a v, greadsByte G r a 0 v →
    (∀ w' u, gwritesByte G w' a u → w' ≠ r → p r < SBAcqP.lpos G p q w') ∧
    (∀ w' u, WeakRvwmoGraph.gpo G w' r → ¬ gwritesByte G w' a u))

/-- The member's per-byte co (landing order) is GF's. -/
def SBAcqP.CoGF (G : Gexec) (p q : Geid → Nat) : Prop :=
  ∀ w1 w2 a u1 u2, gwritesByte G w1 a u1 → gwritesByte G w2 a u2 → gmoLt G w1 w2 →
    SBAcqP.lpos G p q w1 < SBAcqP.lpos G p q w2

/-- THE §3.2 GATE, write half: a write becomes member-latest at a byte only after every GF reader of
a co-earlier write to that byte is realized. -/
def SBAcqP.GateWr (G : Gexec) (p q : Geid → Nat) : Prop :=
  ∀ w' a u r t v w0, gwritesByte G w' a u → greadsByte G r a t v → gwriteAt G t = some w0 →
    gmoLt G w0 w' → r ≠ w' → p r < SBAcqP.lpos G p q w'

/-- THE §3.2 GATE, read half: every read's GF source is landed before it, or the row's own store. -/
theorem SBAcqP.gateRdOf (G : Gexec) (p q : Geid → Nat) : SBAcqP.ReadsGF G p q →
    ∀ r a t v w, greadsByte G r a t v → gwriteAt G t = some w →
      SBAcqP.lpos G p q w < p r ∨ WeakRvwmoGraph.gpo G w r := by
  intro h r a t v w hr hw
  rcases h.1 r a t v w hr hw with ⟨hg, -⟩ | ⟨hl, -⟩
  · exact Or.inr hg
  · exact Or.inl hl

/-! ## 3.1 The boolean checker -/

def SBAcqP.all2B (G : Gexec) (f : Geid → Geid → Bool) : Bool :=
  (gevents G).all (fun x => (gevents G).all (fun y => f x y))

theorem SBAcqP.all2Sound (G : Gexec) (f : Geid → Geid → Bool) :
    SBAcqP.all2B G f = true → ∀ x y, x ∈ gevents G → y ∈ gevents G → f x y = true :=
  fun h x y hx hy => (forallbForallTrue _ _).1 ((forallbForallTrue _ _).1 h x hx) y hy

theorem SBAcqP.lblEv (G : Gexec) (e : Geid) (P : Lbl → Bool) : glblIs G e P → e ∈ gevents G :=
  fun ⟨l, hl, _⟩ => geventsOfLbl G e l hl

def SBAcqP.overlapB (G : Gexec) (w e : Geid) : Bool :=
  (gwrBytes G w).any (fun x => (grdBytes G e).any (fun y => decide (y.1.1 = x.1)))

theorem SBAcqP.overlapOf (G : Gexec) (w e : Geid) (a : Int) (u : BitVec 8) (t : Nat) (v : BitVec 8) :
    gwritesByte G w a u → greadsByte G e a t v → SBAcqP.overlapB G w e = true := by
  intro hw hr
  unfold SBAcqP.overlapB
  rw [existsbExistsTrue]
  refine ⟨(a, u), (gwritesByteBytes _ _ _ _).1 hw, ?_⟩
  show (grdBytes G e).any (fun y => decide (y.1.1 = a)) = true
  rw [existsbExistsTrue]
  exact ⟨((a, t), v), (greadsByteBytes _ _ _ _ _).1 hr, by simp⟩

def SBAcqP.coreB (G : Gexec) (p q : Geid → Nat) : Bool :=
  SBAcqP.all2B G (fun e1 e2 => !gpoB G e1 e2 || decide (p e1 < p e2)) &&
  (gevents G).all (fun w => !glblB G w SBAcq.isSt || decide (p w < q w)) &&
  SBAcqP.all2B G (fun w e => !(gpoB G w e && glblB G w SBAcq.isSt && glblB G e SBAcq.isSt) ||
    decide (q w < q e)) &&
  SBAcqP.all2B G (fun w e => !(gpoB G w e && glblB G w SBAcq.isSt && glblB G e SBAcqP.isDrainF) ||
    decide (q w < p e)) &&
  SBAcqP.all2B G (fun w e => !(gpoB G w e && glblB G w SBAcq.isSt && glblB G e lbRl) ||
    decide (q w < p e)) &&
  SBAcqP.all2B G (fun w e => !(gpoB G w e && glblB G w SBAcq.isSt && glblB G e SBAcqP.isExcl &&
    SBAcqP.overlapB G w e) || decide (q w < p e))

theorem SBAcqP.coreBSound (G : Gexec) (p q : Geid → Nat) :
    SBAcqP.coreB G p q = true → SBAcqP.FifoCore G p q := by
  unfold SBAcqP.coreB
  simp only [Bool.and_eq_true]
  rintro ⟨⟨⟨⟨⟨hpo, hiss⟩, hfifo⟩, hdf⟩, hdr⟩, hdx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e1 e2 hg
    obtain ⟨m1, m2⟩ := gpoGevents G e1 e2 hg
    have h := SBAcqP.all2Sound G _ hpo e1 e2 m1 m2
    simpa [(gpoBSpec _ _ _).2 hg] using h
  · intro w hs
    have h := (forallbForallTrue _ _).1 hiss w (SBAcqP.lblEv G w _ hs)
    simpa [(glblBSpec _ _ _).2 hs] using h
  · intro w1 w2 hg h1 h2
    obtain ⟨m1, m2⟩ := gpoGevents G w1 w2 hg
    have h := SBAcqP.all2Sound G _ hfifo w1 w2 m1 m2
    simpa [(gpoBSpec _ _ _).2 hg, (glblBSpec _ _ _).2 h1, (glblBSpec _ _ _).2 h2] using h
  · intro w f hg h1 h2
    obtain ⟨m1, m2⟩ := gpoGevents G w f hg
    have h := SBAcqP.all2Sound G _ hdf w f m1 m2
    simpa [(gpoBSpec _ _ _).2 hg, (glblBSpec _ _ _).2 h1, (glblBSpec _ _ _).2 h2] using h
  · intro w e hg h1 h2
    obtain ⟨m1, m2⟩ := gpoGevents G w e hg
    have h := SBAcqP.all2Sound G _ hdr w e m1 m2
    simpa [(gpoBSpec _ _ _).2 hg, (glblBSpec _ _ _).2 h1, (glblBSpec _ _ _).2 h2] using h
  · intro w e a u t v hg h1 hw h2 hr
    obtain ⟨m1, m2⟩ := gpoGevents G w e hg
    have h := SBAcqP.all2Sound G _ hdx w e m1 m2
    simpa [(gpoBSpec _ _ _).2 hg, (glblBSpec _ _ _).2 h1, (glblBSpec _ _ _).2 h2,
      SBAcqP.overlapOf G w e a u t v hw hr] using h

def SBAcqP.fwdB (G : Gexec) (p q : Geid → Nat) (r : Geid) (a : Int) (w : Geid) : Bool :=
  gpoB G w r && glblB G w SBAcq.isSt && decide (p r < q w) &&
  (gevents G).all (fun w' => !(gpoB G w w' && gpoB G w' r && gwaB G w' a))

def SBAcqP.landB (G : Gexec) (p q : Geid → Nat) (r : Geid) (a : Int) (w : Geid) : Bool :=
  decide (SBAcqP.lpos G p q w < p r) &&
  (gevents G).all (fun w' => !(gwaB G w' a && !decide (w' = r) &&
      decide (SBAcqP.lpos G p q w < SBAcqP.lpos G p q w')) ||
    decide (p r < SBAcqP.lpos G p q w')) &&
  (gevents G).all (fun w' => !(gpoB G w' r && glblB G w' SBAcq.isSt && gwaB G w' a) ||
    decide (q w' < p r))

def SBAcqP.imgB (G : Gexec) (p q : Geid → Nat) (r : Geid) (a : Int) : Bool :=
  (gevents G).all (fun w' => !(gwaB G w' a && !decide (w' = r)) || decide (p r < SBAcqP.lpos G p q w')) &&
  (gevents G).all (fun w' => !(gpoB G w' r && gwaB G w' a))

def SBAcqP.rdAt (G : Gexec) (p q : Geid → Nat) (r : Geid) (a : Int) (t : Nat) : Bool :=
  match gwriteAt G t with
  | some w => SBAcqP.fwdB G p q r a w || SBAcqP.landB G p q r a w
  | none => SBAcqP.imgB G p q r a

def SBAcqP.readsB (G : Gexec) (p q : Geid → Nat) : Bool :=
  (gevents G).all (fun r => (grdBytes G r).all (fun x => SBAcqP.rdAt G p q r x.1.1 x.1.2))

theorem SBAcqP.rdAtOf (G : Gexec) (p q : Geid → Nat) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    SBAcqP.readsB G p q = true → greadsByte G r a t v → SBAcqP.rdAt G p q r a t = true := by
  intro h hr
  have h1 := (forallbForallTrue _ _).1 h r (greadsByteGevents G r a t v hr)
  exact (forallbForallTrue _ _).1 h1 ((a, t), v) ((greadsByteBytes G r a t v).1 hr)

theorem SBAcqP.readsBSound (G : Gexec) (p q : Geid → Nat) :
    SBAcqP.readsB G p q = true → SBAcqP.ReadsGF G p q := by
  intro hb
  refine ⟨?_, ?_⟩
  · intro r a t v w hr hw
    have h := SBAcqP.rdAtOf G p q r a t v hb hr
    unfold SBAcqP.rdAt at h
    simp only [hw] at h
    rw [Bool.or_eq_true] at h
    rcases h with hf | hl
    · unfold SBAcqP.fwdB at hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨⟨⟨hg, hs⟩, hlt⟩, hall⟩ := hf
      refine Or.inl ⟨(gpoBSpec _ _ _).1 hg, (glblBSpec _ _ _).1 hs, hlt, ?_⟩
      intro w' u h1 h2 hwb
      have := (forallbForallTrue _ _).1 hall w' (gwritesByteGevents G w' a u hwb)
      simp [(gpoBSpec _ _ _).2 h1, (gpoBSpec _ _ _).2 h2, (gwaBSpec G w' a).2 ⟨u, hwb⟩] at this
    · unfold SBAcqP.landB at hl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨⟨hlt, hco⟩, hown⟩ := hl
      refine Or.inr ⟨hlt, ?_, ?_⟩
      · intro w' u hwb hne hlt'
        have := (forallbForallTrue _ _).1 hco w' (gwritesByteGevents G w' a u hwb)
        simpa [(gwaBSpec G w' a).2 ⟨u, hwb⟩, hne, hlt'] using this
      · intro w' u hg hs hwb
        have := (forallbForallTrue _ _).1 hown w' (gwritesByteGevents G w' a u hwb)
        simpa [(gpoBSpec _ _ _).2 hg, (glblBSpec _ _ _).2 hs, (gwaBSpec G w' a).2 ⟨u, hwb⟩] using this
  · intro r a v hr
    have h := SBAcqP.rdAtOf G p q r a 0 v hb hr
    have h0 : gwriteAt G 0 = none := rfl
    unfold SBAcqP.rdAt SBAcqP.imgB at h
    simp only [h0, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · intro w' u hwb hne
      have := (forallbForallTrue _ _).1 h1 w' (gwritesByteGevents G w' a u hwb)
      simpa [(gwaBSpec G w' a).2 ⟨u, hwb⟩, hne] using this
    · intro w' u hg hwb
      have := (forallbForallTrue _ _).1 h2 w' (gwritesByteGevents G w' a u hwb)
      simp [(gpoBSpec _ _ _).2 hg, (gwaBSpec G w' a).2 ⟨u, hwb⟩] at this

def SBAcqP.coB (G : Gexec) (p q : Geid → Nat) : Bool :=
  SBAcqP.all2B G (fun w1 w2 => !(gmoLtB G w1 w2 && (gwrBytes G w1).any (fun x => gwaB G w2 x.1)) ||
    decide (SBAcqP.lpos G p q w1 < SBAcqP.lpos G p q w2))

theorem SBAcqP.coBSound (G : Gexec) (p q : Geid → Nat) :
    SBAcqP.coB G p q = true → SBAcqP.CoGF G p q := by
  intro hb w1 w2 a u1 u2 h1 h2 hlt
  have h := SBAcqP.all2Sound G _ hb w1 w2 (gwritesByteGevents G w1 a u1 h1)
    (gwritesByteGevents G w2 a u2 h2)
  have hany : (gwrBytes G w1).any (fun x => gwaB G w2 x.1) = true :=
    (existsbExistsTrue _ _).2 ⟨(a, u1), (gwritesByteBytes _ _ _ _).1 h1, (gwaBSpec _ _ _).2 ⟨u2, h2⟩⟩
  simp only [(gmoLtBSpec _ _ _).2 hlt, hany, Bool.and_self, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at h
  exact h

def SBAcqP.gateAt (G : Gexec) (p q : Geid → Nat) (w' r : Geid) (a : Int) (t : Nat) : Bool :=
  match gwriteAt G t with
  | some w0 => !(gwaB G w' a && gmoLtB G w0 w' && !decide (r = w')) ||
      decide (p r < SBAcqP.lpos G p q w')
  | none => true

def SBAcqP.gateB (G : Gexec) (p q : Geid → Nat) : Bool :=
  SBAcqP.all2B G (fun w' r => (grdBytes G r).all (fun x => SBAcqP.gateAt G p q w' r x.1.1 x.1.2))

theorem SBAcqP.gateBSound (G : Gexec) (p q : Geid → Nat) :
    SBAcqP.gateB G p q = true → SBAcqP.GateWr G p q := by
  intro hb w' a u r t v w0 hw hr hs hlt hne
  have h := SBAcqP.all2Sound G _ hb w' r (gwritesByteGevents G w' a u hw)
    (greadsByteGevents G r a t v hr)
  have h2 : SBAcqP.gateAt G p q w' r a t = true :=
    (forallbForallTrue _ _).1 h ((a, t), v) ((greadsByteBytes G r a t v).1 hr)
  unfold SBAcqP.gateAt at h2
  simp only [hs] at h2
  simpa [(gwaBSpec G w' a).2 ⟨u, hw⟩, (gmoLtBSpec _ _ _).2 hlt, hne] using h2

def SBAcqP.memberPB (G : Gexec) (p q : Geid → Nat) : Bool :=
  SBAcqP.coreB G p q && SBAcqP.readsB G p q && SBAcqP.coB G p q && SBAcqP.gateB G p q

theorem SBAcqP.memberPBSound (G : Gexec) (p q : Geid → Nat) :
    SBAcqP.memberPB G p q = true →
    SBAcqP.FifoCore G p q ∧ SBAcqP.ReadsGF G p q ∧ SBAcqP.CoGF G p q ∧ SBAcqP.GateWr G p q := by
  unfold SBAcqP.memberPB
  simp only [Bool.and_eq_true]
  rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨SBAcqP.coreBSound G p q h1, SBAcqP.readsBSound G p q h2, SBAcqP.coBSound G p q h3,
    SBAcqP.gateBSound G p q h4⟩

/-! ## 3.2 The walk as a list of items -/

/-- `(false, e)`: event `e`'s step (a plain store's ISSUE); `(true, w)`: plain store `w` LANDS. -/
abbrev SBAcqP.Item : Type := Bool × Geid

def SBAcqP.posIn : List SBAcqP.Item → SBAcqP.Item → Nat
  | [], _ => 0
  | y :: ys, x => if y = x then 0 else SBAcqP.posIn ys x + 1

def SBAcqP.pOf (ord : List SBAcqP.Item) (e : Geid) : Nat := SBAcqP.posIn ord (false, e)

def SBAcqP.qOf (ord : List SBAcqP.Item) (w : Geid) : Nat := SBAcqP.posIn ord (true, w)

/-- The item list is an interleaving: no repeats, every event once, every plain store's landing once,
nothing else. -/
def SBAcqP.OrdOk (G : Gexec) (ord : List SBAcqP.Item) : Prop :=
  ord.Nodup ∧
  (∀ e ∈ gevents G, (false, e) ∈ ord ∧ (glblB G e SBAcq.isSt = true → (true, e) ∈ ord)) ∧
  (∀ it ∈ ord, it.2 ∈ gevents G ∧ (it.1 = true → glblB G it.2 SBAcq.isSt = true))

/-- The design's §4 walk of Litmus 1: acquires land at once, both releases ISSUE (pending), the
acquires of `e`/`c`, the stale spin reads and failed `amoswap`s replay with GF's values, and the
releases LAND last. -/
def SBAcqP.ord1P : List SBAcqP.Item :=
  [(false, (0, 0)), (false, (1, 0)), (false, (0, 1)), (false, (1, 1)), (false, (0, 2)),
   (false, (1, 2)), (false, (0, 3)), (false, (1, 3)), (false, (0, 4)), (false, (1, 4)),
   (false, (0, 5)), (false, (1, 5)), (true, (0, 2)), (true, (1, 2))]

/-- **NON-VACUITY: LITMUS 1 HAS A ROUTE-P MEMBER** — a FIFO/landing interleaving in which every read
returns GF's source (equal values, no skip, no silent step), the landing co is GF's, and the §3.2 gate
holds. -/
theorem SBAcqP.l1MemberP :
    SBAcqP.OrdOk SBAcq.l1.gdG SBAcqP.ord1P ∧
    SBAcqP.FifoCore SBAcq.l1.gdG (SBAcqP.pOf SBAcqP.ord1P) (SBAcqP.qOf SBAcqP.ord1P) ∧
    SBAcqP.ReadsGF SBAcq.l1.gdG (SBAcqP.pOf SBAcqP.ord1P) (SBAcqP.qOf SBAcqP.ord1P) ∧
    SBAcqP.CoGF SBAcq.l1.gdG (SBAcqP.pOf SBAcqP.ord1P) (SBAcqP.qOf SBAcqP.ord1P) ∧
    SBAcqP.GateWr SBAcq.l1.gdG (SBAcqP.pOf SBAcqP.ord1P) (SBAcqP.qOf SBAcqP.ord1P) :=
  ⟨by unfold SBAcqP.OrdOk; decide +kernel, SBAcqP.memberPBSound _ _ _ (by decide +kernel)⟩

/-- …and the landing freedom is what it uses: if every plain store landed before its hart's next
event (a store log without a buffer), no positions satisfy the core and the read rule —
`q w′ < p A1 < p F1 < q w″ < p A2 < p F2 < q w′`. -/
theorem SBAcqP.l1NeedsLanding (p q : Geid → Nat) (hc : SBAcqP.FifoCore SBAcq.l1.gdG p q)
    (hr : SBAcqP.ReadsGF SBAcq.l1.gdG p q)
    (hland : ∀ w e, WeakRvwmoGraph.gpo SBAcq.l1.gdG w e → glblIs SBAcq.l1.gdG w SBAcq.isSt →
      q w < p e) : False := by
  have hl00 : SBAcqP.lpos SBAcq.l1.gdG p q (0, 0) = p (0, 0) := by
    unfold SBAcqP.lpos; exact if_neg (by decide +kernel)
  have hl10 : SBAcqP.lpos SBAcq.l1.gdG p q (1, 0) = p (1, 0) := by
    unfold SBAcqP.lpos; exact if_neg (by decide +kernel)
  have hl02 : SBAcqP.lpos SBAcq.l1.gdG p q (0, 2) = q (0, 2) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  have hl12 : SBAcqP.lpos SBAcq.l1.gdG p q (1, 2) = q (1, 2) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  have s02 : glblIs SBAcq.l1.gdG (0, 2) SBAcq.isSt := (glblBSpec _ _ _).1 (by decide +kernel)
  have s12 : glblIs SBAcq.l1.gdG (1, 2) SBAcq.isSt := (glblBSpec _ _ _).1 (by decide +kernel)
  have a1 := hland (0, 2) (0, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) s02
  have a2 := hland (1, 2) (1, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) s12
  have o1 := hc.po (0, 3) (0, 5) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have o2 := hc.po (1, 3) (1, 5) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have o3 := hc.po (1, 0) (1, 2) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have o4 := hc.po (0, 0) (0, 2) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have i1 := hc.issue (0, 2) s02
  have i2 := hc.issue (1, 2) s12
  have f1 : p (0, 5) < q (1, 2) := by
    rcases hr.1 (0, 5) 2 2 b1 (1, 0) ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SBAcq.l1Rf.1 with
      ⟨hg, -⟩ | ⟨-, hco, -⟩
    · exact absurd hg.1 (by decide)
    · have := hco (1, 2) b0 ((gwbBSpec _ _ _ _).1 (by decide +kernel)) (by decide) (by omega)
      omega
  have f2 : p (1, 5) < q (0, 2) := by
    rcases hr.1 (1, 5) 0 1 b1 (0, 0) ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SBAcq.l1Rf.2 with
      ⟨hg, -⟩ | ⟨-, hco, -⟩
    · exact absurd hg.1 (by decide)
    · have := hco (0, 2) b0 ((gwbBSpec _ _ _ _).1 (by decide +kernel)) (by decide) (by omega)
      omega
  omega

/-! # 4. The δ1′ worst candidate — the racy `ip->ref` read (`ilock+0xe`, route T)

Bytes: `z` = 0 (hart 2's released lock, e.g. a `p->lock` released in `wakeup`), `y` = 2
(`ip->lock.lk`), `itable.lock` = 3, `ip->ref` = 4 (image value 1).
Row 0 (hart 1, `ilock` → `acquiresleep`): `ip->ref` racy read `rB` (0,0); `acquire(ip->lock.lk)` (0,1);
release fence (0,2); `R_y` (0,3).
Row 1 (hart 2): `acquire(z)` (1,0); release fence (1,1); `w‴` (1,2); `acquire(itable.lock)` (1,3);
`ip->ref` load (1,4); `ip->ref = 2` (1,5) — NO fence between `w‴` and the increment.
Row 2 (hart 3): `acquire(ip->lock.lk)` `A_y3` (2,0) reads `R_y`; `holding+0x0` on `z` (2,1), stale;
the failed `amoswap` (2,2). -/

def SBAcqP.img3 : Image := fun a => if a = 4 then some b1 else some b0

def SBAcqP.b2 : BitVec 8 := 2#8

def SBAcqP.l3Prog (tr ty t3 : Nat) (vr : BitVec 8) : List (List Lbl) :=
  [[LLoad false 4 [tr] [vr],
    LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 2 [b0] .WCplain],
   [LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain,
    LRmw true false 3 [0] [b0] [b1] .WCexcl,
    LLoad false 4 [0] [b1],
    LStore false 4 [SBAcqP.b2] .WCplain],
   [LRmw true false 2 [ty] [b0] [b1] .WCexcl,
    LLoad false 0 [t3] [b1],
    LRmw true false 0 [t3] [b1] [b1] .WCexcl]]

def SBAcqP.l3Gmo : List Geid :=
  [(1, 0), (1, 3), (1, 4), (1, 5), (0, 0), (0, 1), (0, 3), (2, 0), (2, 1), (2, 2), (1, 2)]

/-- GF: the racy read sees the increment (write #3). -/
def SBAcqP.l3 : Gdexec := ⟨⟨SBAcqP.img3, SBAcqP.l3Prog 3 5 1 SBAcqP.b2, SBAcqP.l3Gmo⟩, [], []⟩

/-- **THE `ip->ref` CHAIN IS RVWMO-CONSISTENT.** -/
theorem SBAcqP.l3Cat : rvwmoCatConsistent SBAcqP.l3 := catConsistentBSound _ (by decide +kernel)

theorem SBAcqP.l3Rf :
    gwriteAt SBAcqP.l3.gdG 3 = some (1, 5) ∧ gwriteAt SBAcqP.l3.gdG 5 = some (0, 3) ∧
    gwriteAt SBAcqP.l3.gdG 1 = some (1, 0) := by
  decide +kernel

/-- **No δ1′ lockstep member with GF's rf** (`SBAcq.TsoCore` + the source floor):
`p w‴ < p s < p rB < p R_y ≤ fl r3 < p w‴`. -/
theorem SBAcqP.l3NoMember (p fl : Geid → Nat) :
    SBAcq.TsoCore SBAcqP.l3.gdG p fl → SBAcq.floorSrc SBAcqP.l3.gdG p fl → False := by
  intro hm hf
  have e1 := hm.po (1, 2) (1, 5) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e2 := hm.po (0, 0) (0, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e3 := hm.po (1, 0) (1, 2) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have r := hm.rfSrc (0, 0) 4 3 SBAcqP.b2 (1, 5) ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcqP.l3Rf.1
  have f := hf (2, 0) (2, 1) 2 5 b0 (0, 3) ((gpoBSpec _ _ _).1 (by decide +kernel))
    ((glblBSpec _ _ _).1 (by decide +kernel)) ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcqP.l3Rf.2.1
  have s := hm.stale (2, 1) 0 1 b1 (1, 0) (1, 2) b0 ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcqP.l3Rf.2.2 ((glblBSpec _ _ _).1 (by decide +kernel)) ((gwbBSpec _ _ _ _).1 (by decide +kernel))
    e3
  omega

/-- The route-T re-sourcing: the racy read returns the image's `ip->ref = 1` instead of GF's 2 (both
`≥ 1`: `ilock`'s `blez` takes the same arm, the taint dies there). -/
def SBAcqP.l3t : Gdexec := ⟨⟨SBAcqP.img3, SBAcqP.l3Prog 0 5 1 b1, SBAcqP.l3Gmo⟩, [], []⟩

def SBAcqP.ord3 : List Geid :=
  [(1, 0), (0, 0), (0, 1), (0, 3), (2, 0), (2, 1), (2, 2), (1, 2), (1, 3), (1, 4), (1, 5)]

def SBAcqP.fl3 (e : Geid) : Nat := if e.1 = 2 then 4 else 0

/-- **…but a δ1′ member EXISTS after the route-T re-sourcing** — δ1′ is sufficient on this site
exactly because the 6m T-datum (`ip->ref ≥ 1` both sides) lets the racy read be replayed before the
increment. -/
theorem SBAcqP.l3MemberT :
    SBAcq.TsoCore SBAcqP.l3t.gdG (SBAcq.posIn SBAcqP.ord3) SBAcqP.fl3 ∧
    SBAcq.floorSrc SBAcqP.l3t.gdG (SBAcq.posIn SBAcqP.ord3) SBAcqP.fl3 ∧
    SBAcq.srcLe SBAcqP.l3t.gdG (SBAcq.posIn SBAcqP.ord3) SBAcqP.fl3 :=
  SBAcq.memberBSound _ _ _ (by decide +kernel)

end Weak
