/-
Weak: **finding F3: the gmo prefix below the minimal violating write is NOT a
`restrOk` restriction** (route B, §4d.1 F3).

Rocq: `iris/WeakRvwmoProbeRestr.v` @ xxvzwolszwmp.

The Rocq header, in substance.  §4b's closure claim holds only for the
witness's hart; B1b needs causal hulls.

THE WITNESS `erg`: the minimal violation of §4b, plus a SECOND HART WITH AN
EARLY READ.

    hart 0:  e  = (0,0)  LLoad  byte 0  (ts = [0], the era-initial image)
             w  = (0,1)  LStore byte 8            (the violating write)
    hart 1:  r1 = (1,0)  LLoad  byte 16 (ts = [0])
             r2 = (1,1)  LLoad  byte 24 (ts = [0])

    gmo:     r2  <  w  <  r1  <  e

`r2` is gmo-BELOW `w` while its own po-PREDECESSOR `r1` is gmo-above it.  Two
plain loads of DIFFERENT bytes are related by no arm of ppo⁻, so the graph is
consistent (`ergConsistent`), and hart 1's pair is not a rule-14 violation, so
nothing in the minimality of `w` excludes it (`ergWMinViol`).

THE POINT.  `restrOk erg cs 1` (`n = gpos w = 1`) has NO solution
(`ergNoRestr`): `take 1 erg.gxGmo = [r2]`, so the cut admits `r2`, hence (a
per-hart PREFIX) `r1`, and then `restrOk`'s second clause puts `r1` in a gmo
prefix that does not contain it.  The right object is the CAUSAL HULL (closed
under po-predecessors and rf-sources).

The image is TOTAL ("every byte is 0", `imgE`), not `img0`'s two-entry map.

A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  No name of this
   file is in `notes/weak-port-dupnames.json`.
2. VOCABULARY: as `Weak/WeakRvwmoProbeSwap.lean` deviation 2 (`GExec` ↦ an
   anonymous constructor; `WeakLitmus.b0`/`b1` ↦ `b0`/`b1`).
3. The closed `vm_compute` side conditions (`gpos` arithmetic) are `decide`.
4. Lean-only helper (no Rocq twin): `ergLbl` (the four labels of `erg`).

**Name map** (Rocq → Lean): `imgE`; `erg`; `erg_acc` ↦ `ergAcc`; `erg_wr` ↦
`ergWr`; `erg_consistent` ↦ `ergConsistent`; `erg_w_min_viol` ↦ `ergWMinViol`;
`erg_take1` ↦ `ergTake1`; `erg_gpos_w` ↦ `ergGposW`; `erg_no_restr` ↦
`ergNoRestr`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakMem
import Weak.WeakLitmus
import Weak.WeakAxiomatic
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg
import Weak.WeakRvwmoRestr

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. The graph -/

/-- Every byte reads as 0 at the era-initial index. -/
def imgE : Image := fun _ => some b0

def erg : Gexec :=
  ⟨imgE,
   [[LLoad false 0 [0] [b0],
     LStore false 8 [b1] .WCplain],
    [LLoad false 16 [0] [b0],
     LLoad false 24 [0] [b0]]],
   [(1, 1), (0, 1), (1, 0), (0, 0)]⟩

/-- Lean-only: the four labels of `erg`. -/
theorem ergLbl (e : Geid) (l : Lbl) : gxLbl erg e = some l →
    (e = (0, 0) ∧ l = LLoad false 0 [0] [b0]) ∨
    (e = (0, 1) ∧ l = LStore false 8 [b1] .WCplain) ∨
    (e = (1, 0) ∧ l = LLoad false 16 [0] [b0]) ∨
    (e = (1, 1) ∧ l = LLoad false 24 [0] [b0]) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | k <;> simp [gxLbl, erg] at hl <;>
    subst hl <;> simp

/-! # 2. The byte footprints -/

theorem ergAcc (e : Geid) (a : Int) :
    gaccesses erg e a →
    (e = (0, 0) ∧ a = 0) ∨ (e = (0, 1) ∧ a = 8) ∨
    (e = (1, 0) ∧ a = 16) ∨ (e = (1, 1) ∧ a = 24) := by
  rintro (⟨v, l, base, vs, j, hl, hwr, hv, ha⟩ | ⟨t, v, l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩)
  · rcases ergLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
      rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp
  · rcases ergLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
      rcases j with _ | j <;> simp at ht <;> simp [accAddr] at ha <;> subst ha <;> simp

/-- THE ONLY WRITE is hart 0's store, and it touches byte 8 alone. -/
theorem ergWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte erg e a v → e = (0, 1) ∧ a = 8 := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases ergLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp

/-! # 3. (a) `erg` is RVWMO⁻-consistent -/

theorem ergConsistent : rvwmoMinusConsistent erg := by
  refine ⟨⟨by decide, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      simp only [erg, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, _⟩
      rcases ergLbl e l hl with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [erg] at hp <;> subst hp <;>
      rcases k with _ | _ | k <;> simp at hk <;> subst hk <;> simp
  · -- ppo⁻ ⊆ gmo: there are NO ppo⁻ edges.  Hart 1's two LOADS are unordered —
    -- different bytes, and load–load is not a ppo⁻ arm.
    intro e1 e2 hppo
    exfalso
    rcases hppo with ⟨⟨hag, hlt, _, _⟩, a, h1, h2⟩ | ⟨pr, pw, sr, sw, ⟨hag, hlt, kf, hk1, hk2, hlf⟩, _, _⟩ |
        ⟨_, ⟨l, hl, hr⟩, ⟨l', hl', haq⟩, _⟩ | ⟨_, ⟨l, hl, hrc⟩, _⟩
    · rcases ergAcc e1 a h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases ergAcc e2 _ h2 with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ <;>
        simp at hag hlt ha
    · rcases ergLbl _ _ hlf with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
    · rw [hl] at hl'
      cases hl'
      rcases ergLbl e1 _ hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [lbAq] at haq
    · rcases ergLbl e1 l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [lbRcsc, lbAq, lbRl] at hrc
  · -- load value: all three reads name the ERA-INITIAL image, and the one write
    -- in the graph touches none of their bytes
    rintro e a t v ⟨l, base, ts, vs, j, hl, hrd, hj, hv, ha⟩
    rcases ergLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
      rcases j with _ | j <;> simp at hj hv <;> subst hj hv <;> simp [accAddr] at ha <;>
      subst ha <;>
      refine ⟨rfl, ?_⟩ <;>
      intro w' v' hw' _ <;>
      obtain ⟨-, hab⟩ := ergWr w' _ _ hw' <;>
      exact absurd hab (by decide)
  · -- atomicity: no event both reads and writes
    rintro e a t v ⟨l', base, ts, vs, j, hl', hrd, -⟩ ⟨l, hl, hw⟩
    rw [hl] at hl'
    cases hl'
    rcases ergLbl e _ hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbIsW, lbRd] at hw hrd

/-! # 4. (b) `w = (0,1)` is the gmo-minimal violating write, `e = (0,0)` its
po-minimal witness — the two minimality clauses of the kills -/

theorem ergWMinViol :
    gviol erg (0, 0) (0, 1) ∧
    (∀ e' w', gviol erg e' w' → ¬ gmoLt erg w' (0, 1)) ∧
    (∀ e', gviol erg e' (0, 1) → ¬ (e'.2 < ((0, 0) : Geid).2)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the violation: `e` po-before `w`, `w` gmo-before `e`
    refine ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, by decide, by decide, ?_⟩
    decide
  · -- gmo-MINIMAL among violating writes: the only write is `w` itself
    rintro e' w' ⟨-, -, ⟨l, hl, hisw⟩, -⟩ ⟨-, -, hpos⟩
    rcases ergLbl w' l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hisw (by decide)
    · exact absurd hpos (by decide)
    · exact absurd hisw (by decide)
    · exact absurd hisw (by decide)
  · -- po-MINIMAL witness: `e` sits at po position 0
    intro e' _ hlt
    exact absurd hlt (Nat.not_lt_zero _)

/-! # 5. (c) THE POINT: no cut vector restricts `erg` at the frontier -/

theorem ergTake1 : erg.gxGmo.take 1 = [((1, 1) : Geid)] := rfl

/-- `gpos erg w = 1`, so the gmo prefix strictly below the minimal violating
write is `take 1 erg.gxGmo = [r2]`. -/
theorem ergGposW : gpos erg (0, 1) = 1 := by decide

theorem ergNoRestr : ∀ cs, ¬ restrOk erg cs 1 := by
  intro cs hok
  -- `r2 = (1,1)` is in the gmo prefix, so the cut admits it ...
  have hr2 : gcut cs (1, 1) = true := by
    apply restrOkCut erg cs 1 (1, 1) hok
    rw [ergTake1]
    exact List.mem_singleton_self _
  obtain ⟨c, hc, hlt⟩ := gcutElim cs (1, 1) hr2
  -- ... and a cut is a per-hart PREFIX, so it admits `r1 = (1,0)` too
  have hr1 : gcut cs (1, 0) = true := gcutIntro cs (1, 0) c hc (by simp at hlt ⊢; omega)
  have hm : gmem erg (1, 0) := ⟨_, rfl, rfl⟩
  -- but then `restrOk`'s second clause puts `r1` in a prefix without it
  have hin := restrOkIn erg cs 1 _ hok hm hr1
  rw [ergTake1, List.mem_singleton] at hin
  exact absurd hin (by decide)

end Weak
