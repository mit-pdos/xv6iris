/-
Weak: **W13 spike — what the fabric-order hypotheses exclude** (Lean-only scratch, no Rocq twin).

Report: `notes/W13-spike.md`.  Two machine-checked facts behind its verdict.

1. `lbExcluded`: route-b's "honest axiom" `po ∪ rf ∪ gmo|W ∪ dev` acyclic, as it EXISTS in the tree
   (`WeakRvwmoLin2.gfexecConsistent'`), already fails at an EMPTY fabric order on the LB graph
   `lbgd`, which is riscv.cat-consistent.  Taken as a hypothesis on the quantified graph it would
   exclude load buffering — against [OWN.2] — and it subsumes the cycle kill.
2. `scDevExcluded` / `scDevUnrealizable`: on the SC graph `mpg'` (hart 1 stores x, hart 0 loads it)
   with fabric order "hart 0's dev block, then hart 1's" (`w13f`), both landed dev axioms fail
   (`gfexecConsistent'` and FabInd's `gdevAdj ⊆ gmo`), and NO trace extending `po ∪ rf ∪ gmo|W`
   visits the blocks in fabric order.  The execution (MMIO₀; MMIO₁; st x; ld x = 1) is plain SC.
   The cause is the block-atomic folding of `LDev` into the next tagged step
   (`WeakAxRealize.execProgOk'`), not the choice of axiom.
3. `ioObAcyclic` (the PROPOSED trusted-base item: gmo extended by I/O nodes, strongly ordered in
   program order, fabric-ordered among themselves) is free at an empty fabric
   (`ioObAcyclicNodev`) and admits `w13f` (`w13fIoOk`).
-/
import Weak.WeakRvwmoLin2
import Weak.AxGraphCat

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## 1. The literal axiom excludes LB at an empty fabric -/

theorem W13Spike.lbCycle : tc (ptraceRelF ⟨lbgd, []⟩) (0, 0) (0, 0) :=
  tc_l (Or.inl (Or.inl lbgGpow0.1))
    (tc_l (Or.inl (Or.inr (Or.inl WeakRvwmoLinInd.lbgGrf01)))
      (tc_l (Or.inl (Or.inl lbgGpow1.1))
        (tc_once (Or.inl (Or.inr (Or.inl WeakRvwmoLinInd.lbgGrf10))))))

theorem lbExcluded :
    rvwmoCatConsistent lbgd ∧ ¬ gfexecConsistent' ⟨lbgd, []⟩ :=
  ⟨minusImpliesCat _ lbGraphDepsConsistent, fun h => h.2 _ W13Spike.lbCycle⟩

/-! ## 2. Block-atomic dev order excludes an SC execution -/

/-- `mpg'` (gmo `[(1,0); (0,0); (0,1)]`) with hart 0's read `(0,0)` fabric-BEFORE hart 1's
store `(1,0)` — the store the read reads from. -/
def w13f : Gfexec := ⟨mpgd', [(0, 0), (1, 0)]⟩

theorem W13Spike.grf10 : WeakRvwmoAcyc.grf mpg' (1, 0) (0, 0) :=
  ⟨0, 1, b1, ⟨Lbl.LLoad false 0 [1] [b1], 0, [1], [b1], 0, rfl, rfl, rfl, rfl,
    by simp [accAddr]⟩, by decide⟩

theorem W13Spike.dev01 : gdevAdj w13f (0, 0) (1, 0) := ⟨0, rfl, rfl⟩

theorem W13Spike.notGmo : ¬ gmoLt mpg' (0, 0) (1, 0) := by
  unfold gmoLt
  decide +kernel

theorem scDevExcluded :
    rvwmoCatConsistent mpgd' ∧ grule14 mpg' ∧
    ¬ gfexecConsistent' w13f ∧ ¬ gfexecConsistent w13f := by
  refine ⟨minusImpliesCat _ mpg'DepsConsistent, mpg'Rule14, ?_, ?_⟩
  · intro h
    exact h.2 (0, 0)
      (tc_l (Or.inr W13Spike.dev01) (tc_once (Or.inl (Or.inr (Or.inl W13Spike.grf10)))))
  · intro h
    exact W13Spike.notGmo (h.2 _ _ W13Spike.dev01)

/-- Every trace of `mpg'` puts the store before the read, so none is `trDevOrdered` for `w13f`. -/
theorem scDevUnrealizable (L : List Geid) :
    ptraceExt mpg' L → ¬ before L (0, 0) (1, 0) := by
  intro hext hb
  have hnd : L.Nodup := tnd mpg' L hext
  obtain ⟨i, j, hi, hj, hij⟩ := hb
  obtain ⟨i', j', hi', hj', hij'⟩ := hext.2 _ _ (Or.inr (Or.inl W13Spike.grf10))
  have e1 : i = j' := NoDup_lookup hnd hi hj'
  have e2 : j = i' := NoDup_lookup hnd hj hi'
  omega

/-! ## 3. The proposed trusted-base item: riscv's ob/gmo extended by I/O events

Device accesses are NOT graph events; a dev block `(i, k) ∈ gfDev` is the I/O access that hart `i`
performs between its events `k - 1` and `k`.  `ioOrd` orders memory events by gmo, an I/O node
after every memory event of its hart before it and before every memory event of its hart at or
after `k` (strongly-ordered I/O, in program order), and I/O nodes by the fabric. -/

inductive Ioev where
  | ev (e : Geid)
  | dv (i k : Nat)
  deriving DecidableEq

def ioOrd (GF : Gfexec) : Ioev → Ioev → Prop
  | .ev x, .ev y => gmoLt GF.gfGd.gdG x y
  | .ev x, .dv i k => (i, k) ∈ GF.gfDev ∧ x.1 = i ∧ x.2 < k ∧ gmem GF.gfGd.gdG x
  | .dv i k, .ev y => (i, k) ∈ GF.gfDev ∧ y.1 = i ∧ k ≤ y.2 ∧ gmem GF.gfGd.gdG y
  | .dv i k, .dv j l => (i, k) ∈ GF.gfDev ∧ (j, l) ∈ GF.gfDev ∧ ((i = j ∧ k < l) ∨ gdevAdj GF (i, k) (j, l))

/-- THE TRUSTED-BASE ITEM (proposal): the I/O-extended global order is acyclic. -/
def ioObAcyclic (GF : Gfexec) : Prop := ∀ x, ¬ tc (ioOrd GF) x x

theorem W13Spike.rankAcyclic {A : Type _} (R : A → A → Prop) (f : A → Nat) :
    (∀ a b, R a b → f a < f b) → ∀ x, ¬ tc R x x := by
  intro hf x hx
  have key : ∀ a b, tc R a b → f a < f b := by
    intro a b h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hf _ _ h)
  exact Nat.lt_irrefl _ (key x x hx)

/-- At an EMPTY fabric the item is free: it constrains nothing beyond gmo (so LB and W→W
reordering stay in the quantifier, unlike `gfexecConsistent'`). -/
theorem ioObAcyclicNodev (GD : Gdexec) : ioObAcyclic ⟨GD, []⟩ := by
  refine W13Spike.rankAcyclic _ (fun | .ev e => gpos GD.gdG e | .dv _ _ => 0) ?_
  rintro (a | ⟨_, _⟩) (b | ⟨_, _⟩) h
  · exact h.2.2
  all_goals simp [ioOrd] at h

/-- … and it ADMITS the SC execution `w13f` that both landed dev axioms reject. -/
theorem w13fIoOk : ioObAcyclic w13f := by
  refine W13Spike.rankAcyclic _
    (fun | .ev e => 2 + gpos mpg' e | .dv i _ => i) ?_
  rintro (a | ⟨i, k⟩) (b | ⟨j, l⟩) h
  · have : gpos mpg' a < gpos mpg' b := h.2.2
    show 2 + gpos mpg' a < 2 + gpos mpg' b
    omega
  · obtain ⟨hm, -, hk, -⟩ := h
    simp [w13f] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · obtain ⟨hm, -⟩ := h
    simp [w13f] at hm
    show i < 2 + gpos mpg' b
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · obtain ⟨hm, hm', hor⟩ := h
    simp only [w13f, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm hm'
    show i < j
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hor with ⟨-, h⟩ | ⟨n, h1, h2⟩
      · omega
      · rcases n with _ | _ | n <;> simp [w13f] at h1 h2
    · omega
    · rcases hor with ⟨h, -⟩ | ⟨n, h1, h2⟩
      · omega
      · rcases n with _ | _ | n <;> simp [w13f] at h1 h2
    · rcases hor with ⟨-, h⟩ | ⟨n, h1, h2⟩
      · omega
      · rcases n with _ | _ | n <;> simp [w13f] at h1 h2

end Weak
