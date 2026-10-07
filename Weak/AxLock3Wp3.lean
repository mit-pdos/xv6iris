/-
Weak: **A7-T2c continued: graph lemmas for the lock3s concrete row shapes** (`AxLock3Prog.l3pWRow`
/ `l3pRRow`), over an ABSTRACT `GD` with just the row hypothesis (AxSL tier).

Rocq: `iris/AxLock3Wp3.v` @ xxvzwolszwmp.

## What is proved

The `gppoCat6`/`lobp` membership facts that `naSplittingWf (lobp GD (i,k)) …` needs at the
`x`-write and release positions of the lock3s rows, for the policy `AxProtLock3.lockAxpol`
(`lobp e` = same-hart `gppoCat6`-predecessors in `gxGmo`).

  §1  `l3pLobpIntro` — a `gppoCat6`-related pair `(w, e)` with `w` a memory event, under `gwf`,
      lands in `lobp GD e`.
  §2  THE WRITER ROW (`l3pWRow t old v` = `[LRmw(acq) L; LStore x v; LFence rw,w; LStore L b0]`):
      the label lookups, the acquire is `gacqPo`-before the `x`-write (position 1) and the
      release (position 3) — rule 5 (the fence at 2 is not a memory event, so rule 5 does not
      reach it); the `x`-write is `gfenceCovers`-before the release via the row's own `rw,w`
      fence (rule 4).  Corollaries `(i,0) ∈ lobp (i,1)`, `(i,0) ∈ lobp (i,3)`,
      `(i,1) ∈ lobp (i,3)`.
  §3  THE READER ROW (`l3pRRow t old tx vB` = `[LRmw(acq) L; LLoad x; LFence rw,w; LStore L b0]`):
      the same acquire facts at positions 1 and 3; corollaries `(i,0) ∈ lobp (i,1)`,
      `(i,0) ∈ lobp (i,3)`.  (No `x`→release fence fact: the reader never writes `x`.)

The Rocq header's "WHAT IS NOT HERE" (the `wpd_writer_hart`/`wpd_reader_hart` WPd assembly) is
equally absent here.

## Deviations from Rocq

1. NAMES: camelCase, `l3p_` ↦ `l3p` (map below).  No name of this file is in the
   duplicated-name table; no Lean-only helpers.  `Arch.pa` ↦ `PAddr`, `bv 8` ↦ `BitVec 8`.
2. `lobp GD e` (Rocq: resolved through the global instance `lock_axpol`) is written
   `@Axpol.lobp lockAxpol GD e` — `lockAxpol` is a named def in Lean (AxProtLock3 deviation 4),
   passed explicitly.
3. Section hypothesis `Hrow` is `include`d (every lemma of its section uses it, as in Rocq);
   `Hwf` stays an explicit argument of the corollaries, as in Rocq.
4. O2 Stage C: no change needed — the rows have no fetch item (graph `Lbl` has no fetch
   constructor).

**Rocq → Lean name map.**  `l3p_lobp_intro` `l3pLobpIntro`; writer: `l3p_w_lbl0..3`
`l3pWLbl0..3`, `l3p_w_gmem0/1` `l3pWGmem0/1`, `l3p_w_gacq_po_xwrite` `l3pWGacqPoXwrite`,
`l3p_w_gacq_po_rel` `l3pWGacqPoRel`, `l3p_w_gfence_covers_xwrite_rel`
`l3pWGfenceCoversXwriteRel`, `l3p_w_acq_in_lobp_xwrite` `l3pWAcqInLobpXwrite`,
`l3p_w_acq_in_lobp_rel` `l3pWAcqInLobpRel`, `l3p_w_xwrite_in_lobp_rel` `l3pWXwriteInLobpRel`;
reader: `l3p_r_lbl0/1/3` `l3pRLbl0/1/3`, `l3p_r_gmem0` `l3pRGmem0`, `l3p_r_gacq_po_xread`
`l3pRGacqPoXread`, `l3p_r_gacq_po_rel` `l3pRGacqPoRel`, `l3p_r_acq_in_lobp_xread`
`l3pRAcqInLobpXread`, `l3p_r_acq_in_lobp_rel` `l3pRAcqInLobpRel`.

**Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxLock3Prog
import Weak.AxProtLock3

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## 1. The generic membership lemma -/

/-- Any `gppoCat6`-related pair whose PREDECESSOR is a memory event lands in `lobp` (under
`gwf`, which makes `gxGmo` agree with `gmem`). -/
theorem l3pLobpIntro (GD : Gdexec) (w e : Geid) :
    gwf GD.gdG → gmem GD.gdG w → gppoCat6 GD.gdG w e → w ∈ @Axpol.lobp lockAxpol GD e := by
  intro hwf hmem hc6
  change w ∈ lockPolLobp GD e
  unfold lockPolLobp
  rw [elemOfListToSet, List.mem_filter]
  exact ⟨(hwf.2.1 w).2 hmem, (gppoCat6BSpec _ _ _).2 hc6⟩

/-! ## 2. The writer row: `[LRmw(acq); LStore x v; LFence rw,w; LStore L unlocked]` -/

section Writer

variable (Lpa xpa : PAddr) (GD : Gdexec) (i : Nat) (t : Nat) (old v : BitVec 8)
variable (Hrow : AxOpsem.grow GD i = l3pWRow Lpa xpa t old v)
include Hrow

theorem l3pWLbl0 :
    gxLbl GD.gdG (i, 0) = some (.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain) :=
  AxWp.growLookup GD i 0 _ (by rw [Hrow]; rfl)

theorem l3pWLbl1 : gxLbl GD.gdG (i, 1) = some (.LStore false (l3pXbase xpa) [v] .WCplain) :=
  AxWp.growLookup GD i 1 _ (by rw [Hrow]; rfl)

theorem l3pWLbl2 : gxLbl GD.gdG (i, 2) = some (.LFence true true false true) :=
  AxWp.growLookup GD i 2 _ (by rw [Hrow]; rfl)

theorem l3pWLbl3 : gxLbl GD.gdG (i, 3) = some (.LStore false (l3pLbase Lpa) [b0] .WCplain) :=
  AxWp.growLookup GD i 3 _ (by rw [Hrow]; rfl)

theorem l3pWGmem0 : gmem GD.gdG (i, 0) := ⟨_, l3pWLbl0 Lpa xpa GD i t old v Hrow, rfl⟩

theorem l3pWGmem1 : gmem GD.gdG (i, 1) := ⟨_, l3pWLbl1 Lpa xpa GD i t old v Hrow, rfl⟩

/-- 2.1 RULE 5 at the `x`-write. -/
theorem l3pWGacqPoXwrite : gacqPo GD.gdG (i, 0) (i, 1) := by
  have h0 := l3pWLbl0 Lpa xpa GD i t old v Hrow
  have h1 := l3pWLbl1 Lpa xpa GD i t old v Hrow
  refine ⟨⟨rfl, by simp, by rw [h0]; rfl, by rw [h1]; rfl⟩, ⟨_, h0, rfl⟩, ⟨_, h0, rfl⟩,
    l3pWGmem1 Lpa xpa GD i t old v Hrow⟩

/-- 2.1 RULE 5 at the release. -/
theorem l3pWGacqPoRel : gacqPo GD.gdG (i, 0) (i, 3) := by
  have h0 := l3pWLbl0 Lpa xpa GD i t old v Hrow
  have h3 := l3pWLbl3 Lpa xpa GD i t old v Hrow
  exact ⟨⟨rfl, by simp, by rw [h0]; rfl, by rw [h3]; rfl⟩, ⟨_, h0, rfl⟩, ⟨_, h0, rfl⟩,
    ⟨_, h3, rfl⟩⟩

/-- 2.2 RULE 4: the `x`-write is `gfenceCovers`-before the release via the row's own `rw,w`
fence (the `pw`/`sw` arms; both endpoints are writes). -/
theorem l3pWGfenceCoversXwriteRel : gfenceCovers GD.gdG (i, 1) (i, 3) :=
  ⟨true, true, false, true,
    ⟨rfl, by simp, 2, by simp, by simp, l3pWLbl2 Lpa xpa GD i t old v Hrow⟩,
    .inr ⟨⟨_, l3pWLbl1 Lpa xpa GD i t old v Hrow, rfl⟩, rfl⟩,
    .inr ⟨⟨_, l3pWLbl3 Lpa xpa GD i t old v Hrow, rfl⟩, rfl⟩⟩

/-! ### 2.3 The `lobp` membership corollaries -/

theorem l3pWAcqInLobpXwrite (Hwf : gwf GD.gdG) : (i, 0) ∈ @Axpol.lobp lockAxpol GD (i, 1) :=
  l3pLobpIntro GD _ _ Hwf (l3pWGmem0 Lpa xpa GD i t old v Hrow)
    (.inr (.inr (.inr (.inr (.inl (l3pWGacqPoXwrite Lpa xpa GD i t old v Hrow))))))

theorem l3pWAcqInLobpRel (Hwf : gwf GD.gdG) : (i, 0) ∈ @Axpol.lobp lockAxpol GD (i, 3) :=
  l3pLobpIntro GD _ _ Hwf (l3pWGmem0 Lpa xpa GD i t old v Hrow)
    (.inr (.inr (.inr (.inr (.inl (l3pWGacqPoRel Lpa xpa GD i t old v Hrow))))))

theorem l3pWXwriteInLobpRel (Hwf : gwf GD.gdG) : (i, 1) ∈ @Axpol.lobp lockAxpol GD (i, 3) :=
  l3pLobpIntro GD _ _ Hwf (l3pWGmem1 Lpa xpa GD i t old v Hrow)
    (.inr (.inr (.inr (.inl (l3pWGfenceCoversXwriteRel Lpa xpa GD i t old v Hrow)))))

end Writer

/-! ## 3. The reader row: `[LRmw(acq); LLoad x; LFence rw,w; LStore L unlocked]` -/

section Reader

variable (Lpa xpa : PAddr) (GD : Gdexec) (i : Nat) (t : Nat) (old : BitVec 8) (tx : Nat)
  (vB : BitVec 8)
variable (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB)
include Hrow

theorem l3pRLbl0 :
    gxLbl GD.gdG (i, 0) = some (.LRmw true false (l3pLbase Lpa) [t] [old] [b1] .WCplain) :=
  AxWp.growLookup GD i 0 _ (by rw [Hrow]; rfl)

theorem l3pRLbl1 : gxLbl GD.gdG (i, 1) = some (.LLoad false (l3pXbase xpa) [tx] [vB]) :=
  AxWp.growLookup GD i 1 _ (by rw [Hrow]; rfl)

theorem l3pRLbl3 : gxLbl GD.gdG (i, 3) = some (.LStore false (l3pLbase Lpa) [b0] .WCplain) :=
  AxWp.growLookup GD i 3 _ (by rw [Hrow]; rfl)

theorem l3pRGmem0 : gmem GD.gdG (i, 0) := ⟨_, l3pRLbl0 Lpa xpa GD i t old tx vB Hrow, rfl⟩

/-- 3.1 RULE 5 at the `x`-read. -/
theorem l3pRGacqPoXread : gacqPo GD.gdG (i, 0) (i, 1) := by
  have h0 := l3pRLbl0 Lpa xpa GD i t old tx vB Hrow
  have h1 := l3pRLbl1 Lpa xpa GD i t old tx vB Hrow
  exact ⟨⟨rfl, by simp, by rw [h0]; rfl, by rw [h1]; rfl⟩, ⟨_, h0, rfl⟩, ⟨_, h0, rfl⟩,
    ⟨_, h1, rfl⟩⟩

/-- 3.1 RULE 5 at the release. -/
theorem l3pRGacqPoRel : gacqPo GD.gdG (i, 0) (i, 3) := by
  have h0 := l3pRLbl0 Lpa xpa GD i t old tx vB Hrow
  have h3 := l3pRLbl3 Lpa xpa GD i t old tx vB Hrow
  exact ⟨⟨rfl, by simp, by rw [h0]; rfl, by rw [h3]; rfl⟩, ⟨_, h0, rfl⟩, ⟨_, h0, rfl⟩,
    ⟨_, h3, rfl⟩⟩

/-! ### 3.2 The `lobp` membership corollaries -/

theorem l3pRAcqInLobpXread (Hwf : gwf GD.gdG) : (i, 0) ∈ @Axpol.lobp lockAxpol GD (i, 1) :=
  l3pLobpIntro GD _ _ Hwf (l3pRGmem0 Lpa xpa GD i t old tx vB Hrow)
    (.inr (.inr (.inr (.inr (.inl (l3pRGacqPoXread Lpa xpa GD i t old tx vB Hrow))))))

theorem l3pRAcqInLobpRel (Hwf : gwf GD.gdG) : (i, 0) ∈ @Axpol.lobp lockAxpol GD (i, 3) :=
  l3pLobpIntro GD _ _ Hwf (l3pRGmem0 Lpa xpa GD i t old tx vB Hrow)
    (.inr (.inr (.inr (.inr (.inl (l3pRGacqPoRel Lpa xpa GD i t old tx vB Hrow))))))

end Reader

end Weak
