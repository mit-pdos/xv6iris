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
* **(R3)** `(gisIo x ∧ gisIo y ∧ gpo x y) ∨ (gmem x ∧ gmem y ∧ gfBefore GF x y)` — same-row issue
  order among I/O events, and FABRIC order among the fabric members that HAVE a memory-order
  position (`gmem`), stated on the ORDER `gfBefore` (not on `gdevAdj`, so hulls that cut members out
  keep it).

**W13 (R3′) — a TRUSTED-SURFACE TEXT CHANGE ([OWN.53] Q-L-R3 (a), [R39.3], [R40.1] (α); plan §A(6),
§C top "W13 (R3′)").**  Until W13 (R3′) the fabric arm read `gisIo x ∧ gisIo y ∧ gfBefore GF x y`
(I/O PAIRS only).  It now orders ALL `gfDev` members that have a memory-order position (`gmem`: the
disk's fabric-moving `DWriteDev` RAM stores included; the disk row's `DFence` `LFence` block
excluded) — STRONGER than the silent ISA, EQUAL to MachCSL on those events (there the disk's
used-idx/status `DWriteDev` stores and the harts' MMIO are ONE fabric order), and EQUAL in strength
to "all members" on every (L) anchor (anchors are `gmem`).  WHY over `gmem` members only (the
COUNTER-MODEL to an unrestricted arm): the disk program has one `DFence` (`VirtioProg.lean`, before
the used-idx write), emitted as the ROW event `LFence true true true true` (`WeakEvInst.lean`
`pdiskProg`'s `DFence` arm); the own-guard SKIP at the used-ELEMENT `DWriteDev` is SILENT
(`LSilent`, an admin label) and folds into the NEXT row item's block — that `DFence` — while
`pdevEv` is `true` at every disk `DWriteDev` node, so that block's contact bit is `true` and it is a
`gfDev` member (`WeakRvwmoFab`'s membership clause, `… ∨ tq k = true`) whose label is a fence:
neither `gmem` (`lbIsMem` = R ∨ W ∨ Io) nor an (L) anchor.  `gmoLt` needs both endpoints in
`gxGmo`, which holds exactly the `gmem` events (`graphOfCand` filters `lbIsMem`), so an
UNRESTRICTED arm `gfBefore → gmoLt` would make THIS trusted item UNSATISFIABLE on every such
bundle (R38's vacuity class on trusted text).  Satisfiability with a non-I/O `DWriteDev` member is
COMPUTED: `GraphFabResidue.diskFabResidueOk` (§5; its reversal is excluded,
`GraphFabResidue.diskFabRevExcluded`, which the pre-(R3′) arm did NOT exclude).

**Spec standing (owner rule: RVWMO/Sail/Zifencei/PMAs first).**  RVWMO's appendix "I/O Ordering":
for I/O "the load value axiom and atomicity axiom in general do not apply"; ordering between I/O and
main memory comes only from FENCEs with i/o bits, and ordering among I/O accesses only from PMA
strongly-ordered channels.  xv6 boots with `menvcfg = 0`, and Sail's `execute_FENCE` keys on the
memory bits only, so the i/o bits give NO ordering (D48).  Hence the residue is STRONGER than the
ISA: (R1)/(R2) are realization-necessary platform facts (QEMU-TCG MMIO acts as a one-way fence) —
ISA-given at three xv6 sites only (§B(11b)); (R3)'s same-row part is ISA-given within ONE channel
(PMA, F2) and a residue across channels; its fabric part and (R2′) are device-model semantics
(RVWMO/riscv.cat/Sail have no device events, Zifencei and the PMAs are silent: the fabric arm over
`gmem` members is device-model trusted text, STRONGER than the ISA, EQUAL to MachCSL); the
one-row device model's coupling of DMA to UART/PLIC moves is a named model artifact (D51).  What ppo
DOES give I/O events (rule 5 `gacqPo`'s `gmem e2`, a strengthening of appendix (c1), D52; the (c1)
dependency edges, W13 (F-dep)) is graph structure, not part of this item.

**Free when no row has an I/O event and the fabric is empty** (`ioResidueNodev`; since (R3′) the
fabric arm can fire on non-I/O `gmem` members, so the empty fabric is part of the premise), so LB
and W→W reordering stay in the
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
deviation 6), so they are in gmo.  W13 (I)'s bundle half ([OWN.43]): `gfIoDev` (§3.1) is the
GRAPH-VISIBLE half of `gfexecConfIO`'s membership-by-fabric-CONTACT clause, `gisIo (i, k) →
(i, k) ∈ gfDev` (`GraphFabResidue.gfIoDevOfConf`), superseding (M)'s interim `↔`; `gisIo` itself
moved to `WeakRvwmoFab` (the bundle names it).  W13 (I) ([OWN.27]) flipped `gwf`'s `LIo` shape arm, `projLbl` and `lblRealizes*`, so a
`gwf` graph may now carry `LIo` events; the interim lemma `ioResidueGwfInterim` (the item for free
on every `gwf` graph, true only while that arm was `False`) is RETIRED with the flip.  `forgetF`/`GfexecT` (W13 (W)) do not exist yet: the item is stated on the
untagged fabric bundle `Gfexec`, which is what `ioResidueGmo (forgetF GT)` instantiates.

Names (plan text): `gisIo`, `gisR`, `gfBefore`, `ioResidue`, `ioResidueGmo`, `ioResidueNodev`,
`w13fIo`, `w13fIoResidueOk`; also `gfIoDev`, `ioResidueAcyclic`, `w13fIoG`, `w13fIoRevExcluded`; Lean-only helpers file-qualified `GraphFabResidue.*`
(W13 (R3′): `GraphFabResidue.gisIoGmem`, `GraphFabResidue.diskFab*`).
-/
import Weak.WeakRvwmoFab
import Weak.WeakRvwmoTopo

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! ## 1. The event classifiers and the fabric order -/

-- `gisIo` (an I/O-class event, `Lbl.LIo`, any kind) is `WeakRvwmoFab`'s (W13 (I)).

/-- A RAM read event (`lbIsR`: `LLoad`/`LRmw`; never an I/O event, D47 (a)). -/
def gisR (G : Gexec) (e : Geid) : Bool :=
  match gxLbl G e with
  | some l => lbIsR l
  | none => false

/-- FABRIC ORDER: `x` strictly before `y` in the fabric's member list. -/
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
  -- (R3) I/O events in same-row issue order, or `gmem` fabric members in fabric order (W13 (R3′))
  (gisIo GF.gfGd.gdG x = true ∧ gisIo GF.gfGd.gdG y = true ∧ WeakRvwmoGraph.gpo GF.gfGd.gdG x y) ∨
  (gmem GF.gfGd.gdG x ∧ gmem GF.gfGd.gdG y ∧ gfBefore GF x y)

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

/-- An I/O event has a memory-order position (`lbIsMem` includes `lbIsIo`, W13 (M)). -/
theorem GraphFabResidue.gisIoGmem (G : Gexec) (e : Geid) : gisIo G e = true → gmem G e := by
  unfold gisIo
  rcases h : gxLbl G e with _ | l
  · simp
  · intro hio
    exact ⟨l, h, by unfold lbIsMem; simp [hio]⟩

/-- Every arm of the residue has an I/O endpoint, or both endpoints are `gmem` fabric members in
fabric order (the (R3′) fabric arm). -/
theorem GraphFabResidue.ioResidueIo (GF : Gfexec) (x y : Geid) :
    ioResidue GF x y → gisIo GF.gfGd.gdG x = true ∨ gisIo GF.gfGd.gdG y = true ∨
      (gmem GF.gfGd.gdG x ∧ gmem GF.gfGd.gdG y ∧ gfBefore GF x y) := by
  rintro (⟨-, -, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ | h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- **Free when no row has an I/O event and the fabric is empty**: LB and W→W reordering stay in
the quantifier. -/
theorem ioResidueNodev (GF : Gfexec) :
    (∀ e, gisIo GF.gfGd.gdG e = false) → GF.gfDev = [] → ioResidueGmo GF := by
  intro hno hdev x y hr
  rcases GraphFabResidue.ioResidueIo GF x y hr with h | h | ⟨-, -, i, j, hi, -⟩
  · simp [hno] at h
  · simp [hno] at h
  · simp [hdev] at hi

/-- The LB graph (riscv.cat-consistent, `lbExcluded`, `W13Spike.lean`) satisfies the item at the
empty fabric (the LB graph has no fabric). -/
theorem GraphFabResidue.lbIoOk : ioResidueGmo ⟨lbgd, []⟩ := by
  refine ioResidueNodev _ ?_ rfl
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
I/O events; since (R3′) on every `gmem` member, `GraphFabResidue.gdevAdjGmoMem`). -/
theorem GraphFabResidue.gdevAdjGmoMem (GF : Gfexec) (a b : Geid) :
    ioResidueGmo GF → gmem GF.gfGd.gdG a → gmem GF.gfGd.gdG b →
    gdevAdj GF a b → gmoLt GF.gfGd.gdG a b :=
  fun h ha hb hd => h a b (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb,
    GraphFabResidue.gdevAdjGfBefore GF a b hd⟩))))

theorem GraphFabResidue.gdevAdjGmo (GF : Gfexec) (a b : Geid) :
    ioResidueGmo GF → gisIo GF.gfGd.gdG a = true → gisIo GF.gfGd.gdG b = true →
    gdevAdj GF a b → gmoLt GF.gfGd.gdG a b :=
  fun h ha hb hd => GraphFabResidue.gdevAdjGmoMem GF a b h (GraphFabResidue.gisIoGmem _ a ha)
    (GraphFabResidue.gisIoGmem _ b hb) hd

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

/-! ## 3.1 W13 (I): the bundle's I/O-by-class clause

`gfIoDev` is the GRAPH-VISIBLE half of `gfexecConfIO`'s membership clause (fabric CONTACT,
[OWN.43]): every I/O-class event is a `gfDev` member.  The converse is FALSE by design: the
non-I/O members (blocks that move or read the fabric, e.g. the disk's `DWriteDev` stores) are read
off the emission's endpoints and contact bits, which the graph does not carry.  W13 (M)'s interim
form `gisIo (i, k) ↔ (i, k) ∈ gfDev` (unsatisfiable once a fabric-moving RAM store is a member)
is superseded. -/

def gfIoDev (GF : Gfexec) : Prop :=
  ∀ (i : Nat) (row : List Lbl), GF.gfGd.gdG.gxProg[i]? = some row →
    ∀ k, k < row.length → gisIo GF.gfGd.gdG (i, k) = true → (i, k) ∈ GF.gfDev

/-- With no I/O event, the empty fabric list satisfies the clause. -/
theorem GraphFabResidue.gfIoDevNodev (GD : Gdexec) :
    (∀ e, gisIo GD.gdG e = false) → gfIoDev ⟨GD, []⟩ := by
  intro hno i row _ k _ h
  simp [hno] at h

/-- The bundle gives the clause (its first membership disjunct). -/
theorem GraphFabResidue.gfIoDevOfConf (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) : gfexecConfIO boot d0 fab GF → gfIoDev GF := by
  rintro ⟨_, _, _, hc⟩ i row hrow k hk hio
  obtain ⟨_, _, _, _, _, hiff, _⟩ := hc i row hrow
  exact (hiff k hk).2 (Or.inl hio)

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
    rcases hr with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hx, hy, -⟩ | ⟨hx, hy, -⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨GraphFabResidue.gisIoSome _ _ hx, GraphFabResidue.gisIoSome _ _ hy⟩
    · exact ⟨GraphFabResidue.gmemSome _ _ hx, GraphFabResidue.gmemSome _ _ hy⟩
  rcases GraphFabResidue.w13fIoLbl x hxy.1 with rfl | rfl | rfl | rfl <;>
  rcases GraphFabResidue.w13fIoLbl y hxy.2 with rfl | rfl | rfl | rfl <;>
  first
  | (show gmoLt w13fIoG _ _; unfold gmoLt; decide +kernel)
  | (exfalso
     rcases hr with ⟨hp, hm, hx, hy⟩ | ⟨hp, hx, hy⟩ | ⟨hp, hx, hy, hn⟩ | ⟨hx, hy, hp⟩ |
       ⟨hx, hy, hb⟩
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
  have := h (1, 0) (0, 0) (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨GraphFabResidue.gisIoGmem _ _ rfl, GraphFabResidue.gisIoGmem _ _ rfl,
      ⟨0, 1, rfl, rfl, by omega⟩⟩))))
  revert this
  unfold gmoLt
  decide +kernel

/-! ## 5. W13 (R3′) satisfiability with a `DWriteDev` member ([R39.s4])

The (R3′) analogue of [R38.s1]: the widened fabric arm is SATISFIABLE on a bundle whose fabric holds
a NON-I/O member — the disk row's used-idx `DWriteDev` RAM store (row `NCPU`, the label shape of
`pdiskProg`'s THE-STORE arm after projection, `LStore false _ _ .WCplain`) beside a hart MMIO event.
Rows `1 … NCPU - 1` are empty; gmo `MMIO < used-idx store`, fabric order `MMIO, used-idx store`.
The reversed fabric order is EXCLUDED (`diskFabRevExcluded`) — the pre-(R3′) arm (I/O pairs only)
did not order this pair at all, so this is exactly the widening. -/

/-- (Lean-only) the used-idx store (`VirtioProg`'s last `DWriteDev`; address/bytes illustrative). -/
def GraphFabResidue.usedIdxSt : Lbl := LStore false 0 [b1] .WCplain

def GraphFabResidue.diskFabG : Gexec :=
  ⟨img0,
   [[GraphFabResidue.uartIer], [], [], [], [], [], [], [], [GraphFabResidue.usedIdxSt]],
   [(0, 0), (NCPU, 0)]⟩

def GraphFabResidue.diskFab : Gfexec := ⟨⟨GraphFabResidue.diskFabG, []⟩, [(0, 0), (NCPU, 0)]⟩

/-- The member `(NCPU, 0)` is a disk-row RAM WRITE, not an I/O event. -/
theorem GraphFabResidue.diskFabMember :
    (NCPU, 0) ∈ GraphFabResidue.diskFab.gfDev ∧
    gisW GraphFabResidue.diskFabG (NCPU, 0) = true ∧
    gisIo GraphFabResidue.diskFabG (NCPU, 0) = false := by
  decide

theorem GraphFabResidue.diskFabLbl (e : Geid) :
    (gxLbl GraphFabResidue.diskFabG e).isSome = true → e = (0, 0) ∨ e = (NCPU, 0) := by
  obtain ⟨i, k⟩ := e
  intro h
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> rcases k with _ | k <;>
    simp [gxLbl, GraphFabResidue.diskFabG, NCPU] at h ⊢

theorem GraphFabResidue.diskFabBeforeMem (x y : Geid) :
    gfBefore GraphFabResidue.diskFab x y → (x = (0, 0) ∧ y = (NCPU, 0)) := by
  rintro ⟨i, j, hi, hj, hij⟩
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
    simp [GraphFabResidue.diskFab] at hi hj <;> first | omega | exact ⟨hi.symm, hj.symm⟩

/-- **[R39.s4]**: the trusted item is SATISFIABLE on a bundle with a `DWriteDev` member. -/
theorem GraphFabResidue.diskFabResidueOk : ioResidueGmo GraphFabResidue.diskFab := by
  intro x y hr
  have hxy : (gxLbl GraphFabResidue.diskFabG x).isSome = true ∧
      (gxLbl GraphFabResidue.diskFabG y).isSome = true := by
    rcases hr with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hx, hy, -⟩ | ⟨hx, hy, -⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨GraphFabResidue.gisIoSome _ _ hx, GraphFabResidue.gisIoSome _ _ hy⟩
    · exact ⟨GraphFabResidue.gmemSome _ _ hx, GraphFabResidue.gmemSome _ _ hy⟩
  rcases GraphFabResidue.diskFabLbl x hxy.1 with rfl | rfl <;>
  rcases GraphFabResidue.diskFabLbl y hxy.2 with rfl | rfl <;>
  first
  | (show gmoLt GraphFabResidue.diskFabG _ _; unfold gmoLt; decide +kernel)
  | (exfalso
     rcases hr with ⟨hp, hm, hx, hy⟩ | ⟨hp, hx, hy⟩ | ⟨hp, hx, hy, hn⟩ | ⟨hx, hy, hp⟩ |
       ⟨hx, hy, hb⟩
     all_goals first
       | exact absurd hp.2.1 (by decide)
       | exact absurd hp.1 (by decide)
       | exact absurd hx (by decide)
       | exact absurd hy (by decide)
       | exact absurd hn (by decide)
       | (have := GraphFabResidue.diskFabBeforeMem _ _ hb; simp [NCPU] at this))

/-- …and the widened arm bites on the non-I/O member: the reversed fabric order is excluded. -/
theorem GraphFabResidue.diskFabRevExcluded :
    ¬ ioResidueGmo ⟨⟨GraphFabResidue.diskFabG, []⟩, [(NCPU, 0), (0, 0)]⟩ := by
  intro h
  have := h (NCPU, 0) (0, 0) (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨⟨GraphFabResidue.usedIdxSt, rfl, rfl⟩, GraphFabResidue.gisIoGmem _ _ rfl,
      ⟨0, 1, rfl, rfl, by omega⟩⟩))))
  revert this
  unfold gmoLt
  decide +kernel

end Weak
