/-
Weak: **allocproc route P, increment P-W3 — two rows of the `noStuckP` per-head table FAIL**
(`notes/weak-allocproc-routeP-design.md` §3.4, `notes/weak-allocproc-plan-review-R45.md` §2.4 table rows
H3 and H4; plan rev 55 row P-W3).  Lean-only, no Rocq twin.  A leaf of the route-P record (imports
`Weak.LitmusSBAcqP`, whose `SBAcqP.*` member kit — `ReadsGF`, `GateWr`, `CoGF`, `FifoCore`, the boolean
member checker — it reuses verbatim).

The progress argument of design §3.4 needs, for every BLOCKED head `e_y` that some item waits on through
an event `m` of `e_y`'s row (an unrealized reader of a landing's co-predecessor (E3), a source write not
yet issued (R43 R6), the next fabric member (Efab)), `gmo(e_y) ≤ gmo(m)`; the R45 table lists why per head
kind.  Two rows are wrong on xv6 shapes, each machine-checked here as an RVWMO-consistent graph with
NO gate-respecting member:

* **§1 F-P-W3-1 (row H3, `holding+0x0`).**  R45: "`holding+0x0/+0x12`: `→ctrl amoswap.aq →(rule 5)` every
  later read — no read between (`li a0,0; ret; bnez; amoswap`)".  That is the path where the `lw` reads
  ZERO.  `holding` is `lw a5,0(a0); bnez a5,+8; li a0,0; ret; …; ld a5,16(a0)` (`0x80000b82`…`0x80000b94`):
  when the `lw` reads NONZERO, `holding+0x12` (`ld lk->cpu`) follows, a read of another byte that
  RVWMO lets be satisfied before it (no fence, no `.aq`, no address dependency on the loaded value; rule 11
  orders `ctrl;[W]` only).  A blocked `holding+0x0` reads nonzero exactly when its source is a not-yet-
  issued `amoswap` (plain stores to `locked` write 0).  The 3-hart execution: hart u releases `lk`
  (`lk->cpu = 0` = `W`, `fence rw,w`, `sw zero` = `Rel`), hart z acquires it (`holding+0x0` reads `Rel`,
  `amoswap.aq`), hart y's `holding+0x0` reads z's swap (1) and its `holding+0x12` reads the STALE
  `lk->cpu` of u's tenure (`W` co-after).  `SbStuck.l5Cat`/`l5CatT`: RVWMO-consistent.
  **`SbStuck.l5NoMemberP`**: no member with program order, `ReadsGF` (the §3.2 read gate), `GateWr` (the
  landing gate) and the fence-epoch landing law — the cycle `r0 <po r1 <gate W <ep Rel <rf e_z <po a_z
  <rf r0`.  Repair (FAITHFUL, gate-only): read a non-exempt plain load at the TOP when the top VALUE is
  GF's value (a VALUE gate): `SbStuck.l5MemberV` — the member exists once `r0` reads the landed 1 of u's
  own swap (`SbStuck.l5v`, `SbStuck.l5vOnlyR0`: the only change is `r0`'s timestamp; values equal).
* **§2 F-P-W3-2 (row H4, fabric member).**  R45: "H4 fabric member | (R3) | trusted arm".  (R3) orders
  fabric members and same-row I/O among themselves; NOTHING orders a hart's I/O event before its
  program-later RAM READ (RVWMO + PMAs: I/O and RAM are ordered only by fences with i/o bits, which Sail
  drops (D48), or deps; the trusted residue has (R1) RAM→I/O, (R2) I/O→RAM write, (R2′) I/O→disk-row RAM
  read).  `uartintr` → `uartgetc`'s LSR read, then `consoleintr` → `acquire(&cons.lock)` →
  `holding+0x0`; hart y holds `cons.lock` after u's release and writes THR (`consputc` →
  `uartputc_sync`) before x's LSR read in fabric order; x's `holding+0x0` reads the stale 1 of u's swap.
  `SbStuck.l6Cat`: RVWMO-consistent; `SbStuck.l6Res`: the trusted residue `ioResidueGmo` HOLDS;
  `SbStuck.l6WIo`: `gfDevWIo`.  **`SbStuck.l6NoMember`**: no member with program order, fabric order,
  `GateWr` and `CoGF` — `ReadsGF` is NOT used, so a value gate does not help: the cycle `a_y <po f <fab
  e_x <po m <gate W <co a_y`.  **`SbStuck.l6IoRdNo`**: the execution is excluded by the CANDIDATE trusted
  arm `SbStuck.ioRdGmo` ((R2″): an I/O event po-before a RAM READ is gmo-before it) — STRONGER than
  RVWMO + PMAs, the read-side twin of (R1) (true of QEMU-TCG on a TSO host: MMIO is a helper call, loads
  are not reordered with earlier loads).

Spec: theorems about the existing model and the trusted item's TEXT; nothing assumed.  `SbStuck.ioRdGmo`
is a DEFINITION (a candidate premise for the owner), used only as a hypothesis of `l6IoRdNo`.  Lean-only
helpers `SbStuck.*`.
-/
import Weak.LitmusSBAcqP
import Weak.WeakRvwmoLin2

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. F-P-W3-1 — `holding+0x0` reading NONZERO, then `holding+0x12`

Bytes: `locked` = 0, `cpu` = 1 (one byte each; the all-zero image: `lk` free, `lk->cpu = 0`); hart u's
`mycpu()` = 2.
Row 0 (hart u, `acquire` … `release`): `a_u` (0,0) = `acquire+0x1c` `amoswap.w.aq` (0 → 1); `c0` (0,1) =
`acquire+0x28` `sd a0,16(s1)` (`lk->cpu = 2`); `W` (0,2) = `release+0x12` `sd zero,16(s1)`; `fence rw,w`
(0,3) = `release+0x16`; `Rel` (0,4) = `release+0x1a` `sw zero,0(s1)`.
Row 1 (hart y, `acquire` → `holding`): `r0` (1,0) = `holding+0x0` reads `locked = 1` from `a_z` (#5);
`r1` (1,1) = `holding+0x12` reads `cpu = 2` from `c0` (#2) — stale, `W` is co-after.
Row 2 (hart z, `acquire`): `e_z` (2,0) = `holding+0x0` reads `locked = 0` from `Rel` (#4); `a_z` (2,1) =
the `amoswap.w.aq`, succeeds (0 → 1).
Witness gmo: `a_u < c0 < r1 < W < Rel < e_z < a_z < r0` (`r1` before `r0`: load–load reordering). -/

def SbStuck.l5Prog (t0 : Nat) : List (List Lbl) :=
  [[LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LStore false 1 [SBAcqP.b2] .WCplain,
    LStore false 1 [b0] .WCplain,
    LFence true true false true,
    LStore false 0 [b0] .WCplain],
   [LLoad false 0 [t0] [b1],
    LLoad false 1 [2] [SBAcqP.b2]],
   [LLoad false 0 [4] [b0],
    LRmw true false 0 [4] [b0] [b1] .WCexcl]]

def SbStuck.l5Gmo : List Geid :=
  [(0, 0), (0, 1), (1, 1), (0, 2), (0, 4), (2, 0), (2, 1), (1, 0)]

def SbStuck.l5 : Gdexec := AxLitmus.mkgd (SbStuck.l5Prog 5) SbStuck.l5Gmo []

/-- **F-P-W3-1's EXECUTION IS RVWMO-CONSISTENT** (the faithful cat model). -/
theorem SbStuck.l5Cat : rvwmoCatConsistent SbStuck.l5 := catConsistentBSound _ (by decide +kernel)

/-- The tagged model with the text's dependencies: `acquire`'s spin branch into u's later stores,
`holding`'s branch into z's `amoswap` (rule 11; `r0 → r1` is `ctrl;[R]`, NOT an edge). -/
def SbStuck.l5Deps : List Tdep :=
  [(((0, 0), (0, 1)), Dtag.DTctrl), (((0, 0), (0, 2)), Dtag.DTctrl), (((0, 0), (0, 4)), Dtag.DTctrl),
   (((2, 0), (2, 1)), Dtag.DTctrl)]

theorem SbStuck.l5CatT : rvwmoCatConsistentT (mkgt (SbStuck.l5Prog 5) SbStuck.l5Gmo SbStuck.l5Deps) :=
  catTConsistentBSound _ (by decide +kernel)

/-- The outcome's rf: `r0` ← `a_z` (#5), `r1` ← `c0` (#2), `e_z` ← `Rel` (#4). -/
theorem SbStuck.l5Rf :
    gwriteAt SbStuck.l5.gdG 5 = some (2, 1) ∧ gwriteAt SbStuck.l5.gdG 2 = some (0, 1) ∧
    gwriteAt SbStuck.l5.gdG 4 = some (0, 4) := by
  decide +kernel

/-- `r1` is gmo-BEFORE `r0` (the RVWMO freedom the table row overlooks). -/
theorem SbStuck.l5Reorder : gmoLt SbStuck.l5.gdG (1, 1) (1, 0) := (gmoLtBSpec _ _ _).1 (by decide +kernel)

theorem SbStuck.l5NoRl : (SbStuck.l5Prog 5).flatten.all (fun l => !lbRl l) = true := by decide +kernel

/-- **F-P-W3-1: NO ROUTE-P MEMBER UNDER THE §3.2 GATE** — for ANY issue/landing positions with program
order, the read gate (`ReadsGF`: every read's GF source landed before it, or the row's own pending store),
the landing gate (`GateWr`) and the fence law of every lawful landing policy (`SbPol.fenced`: `W`,
issued before u's `fence rw,w`, lands before `Rel`): `p r0 < p r1 < q W < q Rel < p e_z < p a_z < p r0`. -/
theorem SbStuck.l5NoMemberP (p q : Geid → Nat)
    (hpo : ∀ e1 e2, WeakRvwmoGraph.gpo SbStuck.l5.gdG e1 e2 → p e1 < p e2)
    (hr : SBAcqP.ReadsGF SbStuck.l5.gdG p q) (hg : SBAcqP.GateWr SbStuck.l5.gdG p q)
    (hep : q (0, 2) < q (0, 4)) : False := by
  have hlaz : SBAcqP.lpos SbStuck.l5.gdG p q (2, 1) = p (2, 1) := by
    unfold SBAcqP.lpos; exact if_neg (by decide +kernel)
  have hlRel : SBAcqP.lpos SbStuck.l5.gdG p q (0, 4) = q (0, 4) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  have hlW : SBAcqP.lpos SbStuck.l5.gdG p q (0, 2) = q (0, 2) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  have a1 : p (2, 1) < p (1, 0) := by
    rcases hr.1 (1, 0) 0 5 b1 (2, 1) ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SbStuck.l5Rf.1 with
      ⟨hgp, -⟩ | ⟨hl, -⟩
    · exact absurd hgp.1 (by decide)
    · rw [hlaz] at hl; exact hl
  have a2 := hpo (2, 0) (2, 1) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have a3 : q (0, 4) < p (2, 0) := by
    rcases hr.1 (2, 0) 0 4 b0 (0, 4) ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SbStuck.l5Rf.2.2 with
      ⟨hgp, -⟩ | ⟨hl, -⟩
    · exact absurd hgp.1 (by decide)
    · rw [hlRel] at hl; exact hl
  have a5 : p (1, 1) < q (0, 2) := by
    have := hg (0, 2) 1 b0 (1, 1) 2 SBAcqP.b2 (0, 1) ((gwbBSpec _ _ _ _).1 (by decide +kernel))
      ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SbStuck.l5Rf.2.1
      ((gmoLtBSpec _ _ _).1 (by decide +kernel)) (by decide)
    rw [hlW] at this; exact this
  have a6 := hpo (1, 0) (1, 1) ((gpoBSpec _ _ _).1 (by decide +kernel))
  omega

/-- …in particular no FIFO member (FIFO implies the fence law). -/
theorem SbStuck.l5NoMemberFifo (p q : Geid → Nat) :
    ¬ (SBAcqP.FifoCore SbStuck.l5.gdG p q ∧ SBAcqP.ReadsGF SbStuck.l5.gdG p q ∧
      SBAcqP.CoGF SbStuck.l5.gdG p q ∧ SBAcqP.GateWr SbStuck.l5.gdG p q) :=
  fun ⟨hc, hr, _, hg⟩ => SbStuck.l5NoMemberP p q hc.po hr hg
    (hc.fifo (0, 2) (0, 4) ((gpoBSpec _ _ _).1 (by decide +kernel))
      ((glblBSpec _ _ _).1 (by decide +kernel)) ((glblBSpec _ _ _).1 (by decide +kernel)))

/-- **THE REPAIR: A VALUE GATE** — `r0` replays at the landed TOP, where u's own `a_u` (#1) holds the
same value 1 (`Rel` is still pending); `SbStuck.l5v` is the graph with `r0` re-sourced so (the member's
own rf; values unchanged).  The walk: u to `Rel`'s issue (`c0` landed), y's `r0` (top 1) and `r1` (top 2,
`W` pending), `L(W)`, `L(Rel)`, z's `e_z` (0) and `amoswap`. -/
def SbStuck.l5v : Gdexec := AxLitmus.mkgd (SbStuck.l5Prog 1) SbStuck.l5Gmo []

def SbStuck.ord5V : List SBAcqP.Item :=
  [(false, (0, 0)), (false, (0, 1)), (true, (0, 1)), (false, (0, 2)), (false, (0, 3)), (false, (0, 4)),
   (false, (1, 0)), (false, (1, 1)), (true, (0, 2)), (true, (0, 4)), (false, (2, 0)), (false, (2, 1))]

theorem SbStuck.l5MemberV :
    SBAcqP.OrdOk SbStuck.l5v.gdG SbStuck.ord5V ∧
    SBAcqP.FifoCore SbStuck.l5v.gdG (SBAcqP.pOf SbStuck.ord5V) (SBAcqP.qOf SbStuck.ord5V) ∧
    SBAcqP.ReadsGF SbStuck.l5v.gdG (SBAcqP.pOf SbStuck.ord5V) (SBAcqP.qOf SbStuck.ord5V) ∧
    SBAcqP.CoGF SbStuck.l5v.gdG (SBAcqP.pOf SbStuck.ord5V) (SBAcqP.qOf SbStuck.ord5V) ∧
    SBAcqP.GateWr SbStuck.l5v.gdG (SBAcqP.pOf SbStuck.ord5V) (SBAcqP.qOf SbStuck.ord5V) :=
  ⟨by unfold SBAcqP.OrdOk; decide +kernel, SBAcqP.memberPBSound _ _ _ (by decide +kernel)⟩

/-- The re-sourcing touches ONLY `r0`'s timestamp (value 1 kept); gmo unchanged. -/
theorem SbStuck.l5vOnlyR0 :
    (SbStuck.l5v.gdG.gxProg.zip SbStuck.l5.gdG.gxProg).map (fun p => (p.1.zip p.2).filter
      (fun q => q.1 ≠ q.2)) =
      [[], [(LLoad false 0 [1] [b1], LLoad false 0 [5] [b1])], []] ∧
    SbStuck.l5v.gdG.gxGmo = SbStuck.l5.gdG.gxGmo := by
  decide +kernel

/-! # 2. F-P-W3-2 — an I/O head before a program-later RAM read

Byte `lock` = 0 (`cons.lock.locked`); UART 0 THR/LSR (`SBAcqP.thr`/`SBAcqP.lsr`).
Row 0 (hart u, `release(&cons.lock)`): `a_u` (0,0) its `amoswap.w.aq` (0 → 1); `fence rw,w` (0,1);
`W` (0,2) = `sw zero`.
Row 1 (hart y, `consoleintr` → `acquire(&cons.lock)` → `consputc` → `uartputc_sync`): `e_y` (1,0) =
`holding+0x0` reads 0 = `W` (#2); `a_y` (1,1) the `amoswap.w.aq` (0 → 1); `f` (1,2) = the THR store.
Row 2 (hart x, `uartintr` → `uartgetc`, then `consoleintr` → `acquire(&cons.lock)`): `e_x` (2,0) = the
LSR read (an I/O load, after `f` in fabric order); `m` (2,1) = `holding+0x0` reads the STALE 1 of `a_u`
(#1; `W` is co-after).
Fabric order `[f, e_x]`.  Witness gmo: `a_u < m < W < e_y < a_y < f < e_x` (`m` before `e_x`). -/

def SbStuck.l6Prog : List (List Lbl) :=
  [[LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain],
   [LLoad false 0 [2] [b0],
    LRmw true false 0 [2] [b0] [b1] .WCexcl,
    LIo .wr SBAcqP.thr [0x24#8]],
   [LIo .rd SBAcqP.lsr [0x61#8],
    LLoad false 0 [1] [b1]]]

def SbStuck.l6Gmo : List Geid :=
  [(0, 0), (2, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0)]

def SbStuck.l6 : Gdexec := AxLitmus.mkgd SbStuck.l6Prog SbStuck.l6Gmo []

def SbStuck.l6F : Gfexec := ⟨SbStuck.l6, [(1, 2), (2, 0)]⟩

/-- **F-P-W3-2's EXECUTION IS RVWMO-CONSISTENT.** -/
theorem SbStuck.l6Cat : rvwmoCatConsistent SbStuck.l6 := catConsistentBSound _ (by decide +kernel)

/-- The tagged model with the text's control dependencies (spin branches into the swaps' and the THR
store's writes; `uartgetc`'s LSR branch reaches `m` only as `ctrl;[R]`, NOT an edge). -/
def SbStuck.l6Deps : List Tdep :=
  [(((0, 0), (0, 2)), Dtag.DTctrl), (((1, 0), (1, 1)), Dtag.DTctrl), (((1, 1), (1, 2)), Dtag.DTctrl)]

theorem SbStuck.l6CatT : rvwmoCatConsistentT (mkgt SbStuck.l6Prog SbStuck.l6Gmo SbStuck.l6Deps) :=
  catTConsistentBSound _ (by decide +kernel)

theorem SbStuck.l6Rf :
    gwriteAt SbStuck.l6.gdG 1 = some (0, 0) ∧ gwriteAt SbStuck.l6.gdG 2 = some (0, 2) := by
  decide +kernel

theorem SbStuck.l6NoRl : SbStuck.l6Prog.flatten.all (fun l => !lbRl l) = true := by decide +kernel

/-! ## 2.1 The trusted residue holds on the witness -/

/-- (R1) as a boolean. -/
def SbStuck.r1B (GF : Gfexec) (x y : Geid) : Bool :=
  gpoB GF.gfGd.gdG x y && glblB GF.gfGd.gdG x lbIsMem && !gisIo GF.gfGd.gdG x && gisIo GF.gfGd.gdG y

def SbStuck.resB (GF : Gfexec) : Bool :=
  (gevents GF.gfGd.gdG).all (fun x => (gevents GF.gfGd.gdG).all (fun y =>
    !(SbStuck.r1B GF x y || SBAcqP.armsNoR1B GF x y) || gmoLtB GF.gfGd.gdG x y))

theorem SbStuck.resBSound (GF : Gfexec) : SbStuck.resB GF = true → ioResidueGmo GF := by
  intro hb x y hr
  rcases (SBAcqP.ioResidueSplit GF x y).1 hr with ⟨hp, hm, hn, hi⟩ | hr'
  · have hxy := gpoGevents _ _ _ hp
    have h := (forallbForallTrue _ _).1 ((forallbForallTrue _ _).1 hb x hxy.1) y hxy.2
    have harm : SbStuck.r1B GF x y = true := by
      unfold SbStuck.r1B
      simp [(gpoBSpec _ _ _).2 hp, (glblBSpec _ _ lbIsMem).2 hm, hn, hi]
    simp only [harm, Bool.true_or, Bool.not_true, Bool.false_or] at h
    exact (gmoLtBSpec _ _ _).1 h
  · have hb' : SBAcqP.resNoR1B GF = true := by
      unfold SBAcqP.resNoR1B
      rw [forallbForallTrue]
      intro x' hx'
      rw [forallbForallTrue]
      intro y' hy'
      have h := (forallbForallTrue _ _).1 ((forallbForallTrue _ _).1 hb x' hx') y' hy'
      cases h1 : SBAcqP.armsNoR1B GF x' y' <;> simp_all
    exact SBAcqP.resNoR1BSound GF hb' x y hr'

/-- **THE TRUSTED I/O ITEM HOLDS ON THE WITNESS** — (R1) (`e_y`, `a_y` before `f`), (R3) (`f` before
`e_x`); (R2)/(R2′) are vacuous. -/
theorem SbStuck.l6Res : ioResidueGmo SbStuck.l6F := SbStuck.resBSound _ (by decide +kernel)

/-- The fabric members are writes or I/O (`gfDevWIo`, the published bundle's named premise). -/
theorem SbStuck.l6WIo : gfDevWIo SbStuck.l6F := by
  intro e he
  simp only [SbStuck.l6F, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl <;> decide +kernel

/-! ## 2.2 No member, whatever the read gate -/

/-- **F-P-W3-2: NO ROUTE-P MEMBER** — for ANY issue/landing positions with program order, fabric order
(`f` before `e_x`), the landing gate (`GateWr`) and per-byte co (`CoGF`): `p a_y < p f < p e_x < p m <
q W < p a_y`.  The read gate is NOT used, so the VALUE gate of §1 does not repair it. -/
theorem SbStuck.l6NoMember (p q : Geid → Nat)
    (hpo : ∀ e1 e2, WeakRvwmoGraph.gpo SbStuck.l6.gdG e1 e2 → p e1 < p e2)
    (hfab : p (1, 2) < p (2, 0))
    (hg : SBAcqP.GateWr SbStuck.l6.gdG p q) (hco : SBAcqP.CoGF SbStuck.l6.gdG p q) : False := by
  have hlay : SBAcqP.lpos SbStuck.l6.gdG p q (1, 1) = p (1, 1) := by
    unfold SBAcqP.lpos; exact if_neg (by decide +kernel)
  have hlW : SBAcqP.lpos SbStuck.l6.gdG p q (0, 2) = q (0, 2) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  have b1' := hpo (1, 1) (1, 2) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have b3 := hpo (2, 0) (2, 1) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have b4 : p (2, 1) < q (0, 2) := by
    have := hg (0, 2) 0 b0 (2, 1) 1 b1 (0, 0) ((gwbBSpec _ _ _ _).1 (by decide +kernel))
      ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SbStuck.l6Rf.1
      ((gmoLtBSpec _ _ _).1 (by decide +kernel)) (by decide)
    rw [hlW] at this; exact this
  have b5 : q (0, 2) < p (1, 1) := by
    have := hco (0, 2) (1, 1) 0 b0 b1 ((gwbBSpec _ _ _ _).1 (by decide +kernel))
      ((gwbBSpec _ _ _ _).1 (by decide +kernel)) ((gmoLtBSpec _ _ _).1 (by decide +kernel))
    rw [hlW, hlay] at this; exact this
  omega

/-! ## 2.3 The read-side twin of (R1) excludes it -/

/-- **CANDIDATE TRUSTED ARM (R2″)** (NOT a premise anywhere; for the owner question): an I/O event
po-before a RAM READ of its row is gmo-before it.  STRONGER than RVWMO + PMAs. -/
def SbStuck.ioRdGmo (GF : Gfexec) : Prop :=
  ∀ x y, WeakRvwmoGraph.gpo GF.gfGd.gdG x y → gisIo GF.gfGd.gdG x = true → gisR GF.gfGd.gdG y = true →
    gmoLt GF.gfGd.gdG x y

/-- **(R2″) EXCLUDES F-P-W3-2** — in EVERY gmo (any image, any deps) with the witness's rows, rf and
fabric order, the residue plus (R2″) fail: `e_x <R2″ m <fr W <rf a_y <aq f <R3 e_x`. -/
theorem SbStuck.l6IoRdNo (GF : Gfexec) (hP : GF.gfGd.gdG.gxProg = SbStuck.l6Prog)
    (hok : SBAcq.Ok6 GF.gfGd.gdG) (hio : ioResidueGmo GF) (hrd : SbStuck.ioRdGmo GF)
    (hfab : gfBefore GF (1, 2) (2, 0))
    (hsm : gwriteAt GF.gfGd.gdG 1 = some (0, 0)) (hsy : gwriteAt GF.gfGd.gdG 2 = some (0, 2)) :
    False := by
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L00 : gxLbl GF.gfGd.gdG (0, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf _ _ hP 0 0).trans rfl
  have L02 : gxLbl GF.gfGd.gdG (0, 2) = some (LStore false 0 [b0] .WCplain) :=
    (SBAcq.lblOf _ _ hP 0 2).trans rfl
  have L11 : gxLbl GF.gfGd.gdG (1, 1) = some (LRmw true false 0 [2] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf _ _ hP 1 1).trans rfl
  have L12 : gxLbl GF.gfGd.gdG (1, 2) = some (LIo .wr SBAcqP.thr [0x24#8]) :=
    (SBAcq.lblOf _ _ hP 1 2).trans rfl
  have L20 : gxLbl GF.gfGd.gdG (2, 0) = some (LIo .rd SBAcqP.lsr [0x61#8]) :=
    (SBAcq.lblOf _ _ hP 2 0).trans rfl
  have L21 : gxLbl GF.gfGd.gdG (2, 1) = some (LLoad false 0 [1] [b1]) :=
    (SBAcq.lblOf _ _ hP 2 1).trans rfl
  have k1 : gmoLt GF.gfGd.gdG (2, 0) (2, 1) :=
    hrd _ _ (SBAcq.gpoOf _ _ _ _ _ L20 L21 rfl (by decide))
      (by unfold gisIo; rw [L20]; rfl) (by unfold gisR; rw [L21]; rfl)
  have k2 : gmoLt GF.gfGd.gdG (2, 1) (0, 2) :=
    SBAcq.frLt _ (2, 1) (0, 0) (0, 2) 0 1 b1 b0 hwf hlv (SBAcq.rdLd _ _ _ _ _ _ L21) hsm
      (SBAcq.wrSt _ _ _ _ _ _ L02)
      (SBAcq.acqLt _ _ _ _ _ hp L00 L02 rfl (by decide) rfl rfl rfl) (by decide)
  have k3 : gmoLt GF.gfGd.gdG (0, 2) (1, 1) :=
    SBAcq.rfLt _ (1, 1) (0, 2) 0 2 b0 hlv (SBAcq.rdRmw _ _ _ _ _ _ _ _ _ L11) hsy (by decide)
  have k4 : gmoLt GF.gfGd.gdG (1, 1) (1, 2) :=
    SBAcq.acqLt _ _ _ _ _ hp L11 L12 rfl (by decide) rfl rfl rfl
  have k5 := SBAcqP.fabLt GF (1, 2) (2, 0) _ _ hio L12 L20 rfl rfl hfab
  exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ k1 (gmoLtTrans _ _ _ _ k2 (gmoLtTrans _ _ _ _ k3
    (gmoLtTrans _ _ _ _ k4 k5))))

end Weak
