/-
Weak: **W13 (T) — the graph-tier I/O-ordering PLATFORM ASSUMPTION `ioResidueGmo`** (Lean-only, no
Rocq twin; plan `notes/weak-allocproc-plan.md` §A(†), §C W13 (T); D38 [OWN.14], D32 (a′) [OWN.12],
D45–D49 (a) [OWN.16][OWN.17], G3-Q (a″) [OWN.17], D51–D52 (a) [OWN.18]).

**What this file is.**  A NAMED TRUSTED-BASE ITEM of the published theorem (§A item 6), stated over
I/O-class GRAPH EVENTS (`Lbl.LIo`, W13 (E)).  It is an INCLUSION, not an acyclicity over an extended
order: gmo is already total over the memory events, and `ioResidueGmo GF` says that the residue
`ioResidue GF` — the I/O orderings the published theorem needs and that riscv.cat's ppo does NOT give
— lies inside gmo.  The four arms (`x` before `y`, `gpo` = same row, program order):

* **(R1)** `gpo x y ∧ gmem x ∧ ¬ gisIo x ∧ gisIo y` — a row's RAM accesses (READS included)
  po-before an I/O event.  On the disk row (`y.1 = NCPU`) this was "DMA writes are gmo-before
  COMMIT": device-MODEL semantics, the one place (T) carries disk correctness [R7.3].  Since W-DISK
  (`Weak/VirtioProg.lean`, [OWN.31][OWN.32]) there is no COMMIT event: the completion rides the
  used-idx RAM STORE, ordered after the request's DMA writes by the device-side `DFence` (rule 4)
  and the single order, and (R1)'s disk use shrinks to the START event, the ring POP event (the
  avail-index / ring reads po-before it) and the UART/PLIC moves.  The text of (R1) is unchanged.
* **(R2)** `gpo x y ∧ gisIo x ∧ gisW y` — an I/O event po-before a RAM WRITE (`grule14`'s shape).
  RAM READS po-after an I/O event stay UNORDERED on hart rows (the (a′) point [R7.1]).
* **(R2′)** `gpo x y ∧ gisIo x ∧ gisR y ∧ y.1 = NCPU` — an I/O event po-before a DISK-ROW RAM read
  (G3-Q RULED (a″) [OWN.17]: the device model's "reads after the MMIO see everything before it").
* **(R3)** `gisIo x ∧ gisIo y ∧ (gpo x y ∨ gfBefore GF x y)` — same-row issue order and FABRIC order
  among I/O events, stated on the ORDER `gfBefore` (not on `gdevAdj`, so hulls that cut I/O events
  out keep it).

**Spec standing (owner rule: RVWMO/Sail/Zifencei/PMAs first).**  RVWMO's appendix "I/O Ordering":
for I/O "the load value axiom and atomicity axiom in general do not apply"; ordering between I/O and
main memory comes only from FENCEs with i/o bits, and ordering among I/O accesses only from PMA
strongly-ordered channels.  xv6 boots with `menvcfg = 0`, and Sail's `execute_FENCE` keys on the
memory bits only, so the i/o bits give NO ordering (D48).  Hence the residue is STRONGER than the
ISA: (R1)/(R2) are realization-necessary platform facts (QEMU-TCG MMIO acts as a one-way fence) —
ISA-given at three xv6 sites only (§B(11b)); (R3)'s same-row part is ISA-given within ONE channel
(PMA, F2) and a residue across channels; its fabric part and (R2′) are device-model semantics; the
one-row device model's coupling of DMA to UART/PLIC moves is a named model artifact (D51).  What ppo
DOES give I/O events (rule 5 `gacqPo`'s `gmem e2`, a strengthening of appendix (c1), D52; the (c1)
dependency edges, W13 (F-dep)) is graph structure, not part of this item.

**Free when no row has an I/O event** (`ioResidueNodev`), so LB and W→W reordering stay in the
quantifier (contrast `lbExcluded`, `W13Spike.lean`: the literal `gfexecConsistent'` excludes LB at an EMPTY
fabric).  **Admits the SC case** that both landed block-level dev axioms reject
(`scDevExcluded`, `W13Spike.lean`): `w13fIo` re-encodes the spike's `w13f` with the two MMIO accesses as
their OWN events, gmo `MMIO₀ < MMIO₁ < st < ld` — `w13fIoResidueOk` is W13 (T)'s acceptance (the re-check of
`w13fIoOk` of `W13Spike.lean`, which is in namespace `Weak` unqualified).  It is not vacuous: reversing the fabric order is excluded (`w13fIoRevExcluded`).
It does NOT assume `racyD` acyclicity — the cycle kill carries that.  The rank proof of
`ioObAcyclicNodev` (`W13Spike.lean`) re-done: gmo extended by the residue stays acyclic under the item
(`ioResidueAcyclic`).

**Status of the surrounding model at this file's landing.**  Statement text is final.  W13 (M):
`gmem` holds of I/O events (`lbIsMem l = lbIsR l || lbIsW l || lbIsIo l`, `WeakRvwmoGraph`
deviation 6), so they are in gmo; `gfIoDev` is the bundle clause `gisIo (i, k) ↔ (i, k) ∈ gfDev`
(§3.1).  Until W13 (I) flips `gwf`'s `LIo` shape arm, `projLbl`, and `lblRealizes*` ([OWN.27]),
no `gwf` graph carries an `LIo` event and the item is satisfied for free
(`GraphFabResidue.ioResidueGwfInterim`).  `forgetF`/`GfexecT` (W13 (I)/(W)) do not exist yet: the item is stated on the
untagged fabric bundle `Gfexec`, which is what `ioResidueGmo (forgetF GT)` instantiates.

Names (plan text): `gisIo`, `gisR`, `gfBefore`, `ioResidue`, `ioResidueGmo`, `ioResidueNodev`,
`w13fIo`, `w13fIoResidueOk`; also `gfIoDev`, `ioResidueAcyclic`, `w13fIoG`, `w13fIoRevExcluded`; Lean-only helpers file-qualified `GraphFabResidue.*`.
-/
import Weak.WeakRvwmoFab
import Weak.WeakRvwmoTopo

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! ## 1. The event classifiers and the fabric order -/

/-- An I/O-class event (`Lbl.LIo`, any kind). -/
def gisIo (G : Gexec) (e : Geid) : Bool :=
  match gxLbl G e with
  | some l => lbIsIo l
  | none => false

/-- A RAM read event (`lbIsR`: `LLoad`/`LRmw`; never an I/O event, D47 (a)). -/
def gisR (G : Gexec) (e : Geid) : Bool :=
  match gxLbl G e with
  | some l => lbIsR l
  | none => false

/-- FABRIC ORDER: `x` strictly before `y` in the fabric's I/O-event list. -/
def gfBefore (GF : Gfexec) (x y : Geid) : Prop := before GF.gfDev x y

/-! ## 2. The residue and THE TRUSTED-BASE ITEM -/

/-- The I/O-ordering residue: (R1) ∨ (R2) ∨ (R2′) ∨ (R3), see the header. -/
def ioResidue (GF : Gfexec) (x y : Geid) : Prop :=
  -- (R1) RAM access po-before an I/O event
  (WeakRvwmoGraph.gpo GF.gfGd.gdG x y ∧ gmem GF.gfGd.gdG x ∧
    gisIo GF.gfGd.gdG x = false ∧ gisIo GF.gfGd.gdG y = true) ∨
  -- (R2) I/O event po-before a RAM write
  (WeakRvwmoGraph.gpo GF.gfGd.gdG x y ∧ gisIo GF.gfGd.gdG x = true ∧
    gisW GF.gfGd.gdG y = true) ∨
  -- (R2′) I/O event po-before a DISK-ROW RAM read (G3-Q (a″))
  (WeakRvwmoGraph.gpo GF.gfGd.gdG x y ∧ gisIo GF.gfGd.gdG x = true ∧
    gisR GF.gfGd.gdG y = true ∧ y.1 = NCPU) ∨
  -- (R3) I/O events: same-row issue order or fabric order
  (gisIo GF.gfGd.gdG x = true ∧ gisIo GF.gfGd.gdG y = true ∧
    (WeakRvwmoGraph.gpo GF.gfGd.gdG x y ∨ gfBefore GF x y))

/-- **THE TRUSTED-BASE ITEM**: the residue is gmo-forward. -/
def ioResidueGmo (GF : Gfexec) : Prop :=
  ∀ x y, ioResidue GF x y → gmoLt GF.gfGd.gdG x y

/-! ## 3. Basic facts -/

theorem GraphFabResidue.gisIoLbl (G : Gexec) (e : Geid) :
    gisIo G e = true → ∃ kd ba vs, gxLbl G e = some (LIo kd ba vs) := by
  unfold gisIo
  rcases h : gxLbl G e with _ | l
  · simp
  · cases l <;> simp [lbIsIo]

/-- Every arm of the residue has an I/O endpoint. -/
theorem GraphFabResidue.ioResidueIo (GF : Gfexec) (x y : Geid) :
    ioResidue GF x y → gisIo GF.gfGd.gdG x = true ∨ gisIo GF.gfGd.gdG y = true := by
  rintro (⟨-, -, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩)
  · exact Or.inr h
  all_goals exact Or.inl h

/-- **Free when no row has an I/O event**: LB and W→W reordering stay in the quantifier. -/
theorem ioResidueNodev (GF : Gfexec) :
    (∀ e, gisIo GF.gfGd.gdG e = false) → ioResidueGmo GF := by
  intro hno x y hr
  rcases GraphFabResidue.ioResidueIo GF x y hr with h | h <;> simp [hno] at h

/-- The LB graph (riscv.cat-consistent, `lbExcluded`, `W13Spike.lean`) satisfies the item at any fabric. -/
theorem GraphFabResidue.lbIoOk (dev : List Geid) : ioResidueGmo ⟨lbgd, dev⟩ := by
  refine ioResidueNodev _ ?_
  rintro ⟨i, k⟩
  show gisIo lbg (i, k) = false
  unfold gisIo
  rcases i with _ | _ | i <;> rcases k with _ | _ | k <;> simp [gxLbl, lbg, lbIsIo]

/-- A fabric step is fabric order. -/
theorem GraphFabResidue.gdevAdjGfBefore (GF : Gfexec) (a b : Geid) :
    gdevAdj GF a b → gfBefore GF a b := by
  rintro ⟨n, h1, h2⟩
  exact ⟨n, n + 1, h1, h2, Nat.lt_succ_self n⟩

/-- Under the item, every fabric step is gmo-forward (FabInd's `gdevAdj ⊆ gmo`, now DERIVED, on
I/O events). -/
theorem GraphFabResidue.gdevAdjGmo (GF : Gfexec) (a b : Geid) :
    ioResidueGmo GF → gisIo GF.gfGd.gdG a = true → gisIo GF.gfGd.gdG b = true →
    gdevAdj GF a b → gmoLt GF.gfGd.gdG a b :=
  fun h ha hb hd => h a b (Or.inr (Or.inr (Or.inr ⟨ha, hb, Or.inr
    (GraphFabResidue.gdevAdjGfBefore GF a b hd)⟩)))

/-- The rank proof of `ioObAcyclicNodev` (`W13Spike.lean`), re-done: under the item, gmo extended by the
residue is acyclic (gmo positions rank it). -/
theorem ioResidueAcyclic (GF : Gfexec) :
    ioResidueGmo GF →
    ∀ x, ¬ tc (fun a b => gmoLt GF.gfGd.gdG a b ∨ ioResidue GF a b) x x := by
  intro h x hx
  have key : ∀ a b, tc (fun a b => gmoLt GF.gfGd.gdG a b ∨ ioResidue GF a b) a b →
      gpos GF.gfGd.gdG a < gpos GF.gfGd.gdG b := by
    intro a b hab
    induction hab with
    | single hs => rcases hs with hs | hs
                   · exact hs.2.2
                   · exact (h _ _ hs).2.2
    | tail _ hs ih =>
        rcases hs with hs | hs
        · exact Nat.lt_trans ih hs.2.2
        · exact Nat.lt_trans ih (h _ _ hs).2.2
  exact Nat.lt_irrefl _ (key x x hx)

/-! ## 3.1 W13 (M): the bundle clause, and the interim state

`gfIoDev` is the clause `gisIo (i, k) ↔ (i, k) ∈ gfDev` that the fabric-aware conformance bundles
gain (§A(†): `xv6ConfS` on `gfexecConfIO`, W13 (I)/(W); `gdexecQconfT`, W12) in place of
`isDevBlock em k ↔ (i, k) ∈ gfDev` (`gfexecConf`).  Neither bundle exists yet, so the clause is
stated here as a predicate for them to include. -/

def gfIoDev (GF : Gfexec) : Prop :=
  ∀ (i : Nat) (row : List Lbl), GF.gfGd.gdG.gxProg[i]? = some row →
    ∀ k, k < row.length → (gisIo GF.gfGd.gdG (i, k) = true ↔ (i, k) ∈ GF.gfDev)

/-- With no I/O event, the empty fabric list satisfies the clause. -/
theorem GraphFabResidue.gfIoDevNodev (GD : Gdexec) :
    (∀ e, gisIo GD.gdG e = false) → gfIoDev ⟨GD, []⟩ := by
  intro hno i row _ k _
  simp [hno]

/-- INTERIM (until W13 (I) flips `gwf`'s `LIo` shape arm, [OWN.27]): a `gwf` graph has no I/O
event, so the item holds at any fabric list. -/
theorem GraphFabResidue.ioResidueGwfInterim (GF : Gfexec) :
    gwf GF.gfGd.gdG → ioResidueGmo GF := by
  intro hwf
  refine ioResidueNodev GF (fun e => ?_)
  unfold gisIo
  rcases hl : gxLbl GF.gfGd.gdG e with _ | l
  · rfl
  · exact WeakRvwmoGraph.gwfNoIo _ e l hwf hl

/-! ## 4. The re-encoded `w13f`: the SC case is admitted (W13 (T) acceptance)

The spike's `w13f` (`W13Spike.lean`) folds each hart's MMIO access into its next memory event, and
both landed dev axioms reject it.  Here each MMIO access is its OWN graph event: row 0 =
`[MMIO₀; ld x = 1]`, row 1 = `[MMIO₁; st x := 1]`, gmo `MMIO₀ < MMIO₁ < st < ld`, fabric order
`MMIO₀, MMIO₁`.  (The read's `ts` entry `1` names the first write in gmo, `(1, 1)`.)  The execution
is plain SC. -/

/-- The UART MMIO store `sb zero,1(a5)` (IER := 0), the first I/O event of hart 0's boot. -/
def GraphFabResidue.uartIer : Lbl := LIo .wr 0x10000001 [0]

def w13fIoG : Gexec :=
  ⟨img0,
   [[GraphFabResidue.uartIer, LLoad false 0 [1] [b1]],
    [GraphFabResidue.uartIer, LStore false 0 [b1] .WCplain]],
   [(0, 0), (1, 0), (1, 1), (0, 1)]⟩

def w13fIo : Gfexec := ⟨⟨w13fIoG, []⟩, [(0, 0), (1, 0)]⟩

/-- The four labels of `w13fIoG`. -/
theorem GraphFabResidue.w13fIoLbl (e : Geid) :
    (gxLbl w13fIoG e).isSome = true → e = (0, 0) ∨ e = (0, 1) ∨ e = (1, 0) ∨ e = (1, 1) := by
  obtain ⟨i, k⟩ := e
  intro h
  rcases i with _ | _ | i <;> rcases k with _ | _ | k <;> simp [gxLbl, w13fIoG] at h ⊢

theorem GraphFabResidue.gisIoSome (G : Gexec) (e : Geid) :
    gisIo G e = true → (gxLbl G e).isSome = true := by
  unfold gisIo
  rcases gxLbl G e with _ | l <;> simp

theorem GraphFabResidue.gmemSome (G : Gexec) (e : Geid) :
    gmem G e → (gxLbl G e).isSome = true := by
  rintro ⟨l, hl, -⟩
  simp [hl]

theorem GraphFabResidue.w13fBeforeMem (x y : Geid) :
    gfBefore w13fIo x y → (x = (0, 0) ∧ y = (1, 0)) := by
  rintro ⟨i, j, hi, hj, hij⟩
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
    simp [w13fIo] at hi hj <;> first | omega | exact ⟨hi.symm, hj.symm⟩

/-- **W13 (T) acceptance**: the re-encoded SC execution satisfies the item. -/
theorem w13fIoResidueOk : ioResidueGmo w13fIo := by
  intro x y hr
  -- both endpoints are events of the graph
  have hxy : (gxLbl w13fIoG x).isSome = true ∧ (gxLbl w13fIoG y).isSome = true := by
    rcases hr with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hx, hy, -⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨GraphFabResidue.gisIoSome _ _ hx, GraphFabResidue.gisIoSome _ _ hy⟩
  rcases GraphFabResidue.w13fIoLbl x hxy.1 with rfl | rfl | rfl | rfl <;>
  rcases GraphFabResidue.w13fIoLbl y hxy.2 with rfl | rfl | rfl | rfl <;>
  first
  | (show gmoLt w13fIoG _ _; unfold gmoLt; decide +kernel)
  | (exfalso
     rcases hr with ⟨hp, hm, hx, hy⟩ | ⟨hp, hx, hy⟩ | ⟨hp, hx, hy, hn⟩ | ⟨hx, hy, hp | hb⟩
     all_goals first
       | exact absurd hp.2.1 (by decide)
       | exact absurd hp.1 (by decide)
       | exact absurd hx (by decide)
       | exact absurd hy (by decide)
       | exact absurd hn (by decide)
       | (have := GraphFabResidue.w13fBeforeMem _ _ hb; simp at this))

/-- …and the item is not vacuous: the same graph with the fabric order REVERSED (MMIO₁ first) is
excluded, since gmo puts MMIO₀ first. -/
theorem w13fIoRevExcluded : ¬ ioResidueGmo ⟨⟨w13fIoG, []⟩, [(1, 0), (0, 0)]⟩ := by
  intro h
  have := h (1, 0) (0, 0) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inr ⟨0, 1, rfl, rfl, by omega⟩⟩)))
  revert this
  unfold gmoLt
  decide +kernel

end Weak
