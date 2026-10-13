/-
Weak: **finding F1: `killK1` is STRONGER than the theorem needs** (route B,
§4d.1).

Rocq: `iris/WeakRvwmoProbeK1.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `killK1`'s hypotheses hold at a graph that
NORMALIZES (source-descent resolves it: `w0` below `w`, then `e` below `w`); the
obligation as stated cannot be discharged for xv6 — see route-b §4d.1 F1.

THE WITNESS `mpg`: the message-passing READER WITHOUT A FENCE, with an
INDEPENDENT EARLY STORE on the reader's hart.

    hart 0:  e = (0,0)  LLoad  byte 0, ts = [2]  (reads hart 1's store)
             w = (0,1)  LStore byte 8            (the violating write)
    hart 1:  w0 = (1,0) LStore byte 0            (e's rf-source)

    gmo:     w  <  w0  <  e

`w` is the gmo-MINIMAL rule-14 violating write, `e` its po-MINIMAL witness, a
read, whose rf-source `w0` is CROSS-HART and gmo-strictly inside `(w, e)`:
exactly `killK1`'s hypotheses, so `killK1 mpgd` is false (`mpgdKillK1False`).

THE POINT: `mpg` nevertheless NORMALIZES.  The rows-equivalent graph `mpg'`
(gmo `w0 < e < w`, the read's `ts` renamed by `tswap 1`) satisfies `grule14`
(`mpg'Rule14`), is consistent (`mpg'Consistent`), and `gdEquiv` relates the
two (`mpgEquiv`).  So at this graph the normalization SUCCEEDS while `killK1`
DEMANDS a refutation.

A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1 (the Rocq primes
   stay: `mpg'_acc` ↦ `mpg'Acc`).  No name of this file is in
   `notes/weak-port-dupnames.json`; the `WeakRvwmoGraph` duplicate used is
   referred to qualified (`WeakRvwmoGraph.gpo`).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`Z` ↦ `Int`, `bv 8` ↦
   `BitVec 8`, `WeakLitmus.img0`/`b1` ↦ `img0`/`b1`).
3. The closed `vm_compute` side conditions (gmo membership, `gpos`/`gwix`
   values, `gwriteAt`, `gwrites`) are `decide`.
4. Lean-only helpers (no Rocq twin): `mpgLbl`, `mpg'Lbl` (the three labels of
   each graph, the engine of every case split), as `WeakRvwmoGraph.lbgLbl`.

**Name map** (Rocq → Lean): `mpg`; `mpgd`; `mpg'`; `mpgd'`; `mpg_acc` ↦
`mpgAcc`; `mpg_wr` ↦ `mpgWr`; `mpg'_acc` ↦ `mpg'Acc`; `mpg'_wr` ↦ `mpg'Wr`;
`mpg_consistent` ↦ `mpgConsistent`; `mpg_deps_consistent` ↦
`mpgDepsConsistent`; `mpgd_kill_K1_false` ↦ `mpgdKillK1False`;
`mpg'_consistent` ↦ `mpg'Consistent`; `mpg'_deps_consistent` ↦
`mpg'DepsConsistent`; `mpg'_rule14` ↦ `mpg'Rule14`; `mpg_rows_rel` ↦
`mpgRowsRel`; `mpg_gwrites` ↦ `mpgGwrites`; `mpg'_gwrites` ↦ `mpg'Gwrites`;
`mpg_wperm` ↦ `mpgWperm`; `mpg_equiv` ↦ `mpgEquiv`; `mpg_normalizes` ↦
`mpgNormalizes`.

**Not ported:** nothing.
-/
import Weak.WeakMem
import Weak.WeakLitmus
import Weak.WeakAxiomatic
import Weak.WeakAxiomatic2
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg
import Weak.WeakRvwmoNorm

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. The two graphs -/

/-- `mpg`: gmo = `[w; w0; e]`.  The read's `ts` entry names write index 2, hart
1's store `w0`. -/
def mpg : Gexec :=
  ⟨img0,
   [[LLoad false 0 [2] [b1], LStore false 8 [b1] .WCplain],
    [LStore false 0 [b1] .WCplain]],
   [(0, 1), (1, 0), (0, 0)]⟩

def mpgd : Gdexec := ⟨mpg, []⟩

/-- `mpg'`: gmo = `[w0; e; w]`.  The SAME rows with the read's `ts` entry
renamed by `tswap 1` (2 ↦ 1). -/
def mpg' : Gexec :=
  ⟨img0,
   [[LLoad false 0 [1] [b1], LStore false 8 [b1] .WCplain],
    [LStore false 0 [b1] .WCplain]],
   [(1, 0), (0, 0), (0, 1)]⟩

def mpgd' : Gdexec := ⟨mpg', []⟩

/-! # 2. The byte footprints -/

/-- Lean-only: the three labels of `mpg`. -/
theorem mpgLbl (e : Geid) (l : Lbl) : gxLbl mpg e = some l →
    (e = (0, 0) ∧ l = LLoad false 0 [2] [b1]) ∨
    (e = (0, 1) ∧ l = LStore false 8 [b1] .WCplain) ∨
    (e = (1, 0) ∧ l = LStore false 0 [b1] .WCplain) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | k <;> simp [gxLbl, mpg] at hl <;>
    subst hl <;> simp

/-- Lean-only: the three labels of `mpg'`. -/
theorem mpg'Lbl (e : Geid) (l : Lbl) : gxLbl mpg' e = some l →
    (e = (0, 0) ∧ l = LLoad false 0 [1] [b1]) ∨
    (e = (0, 1) ∧ l = LStore false 8 [b1] .WCplain) ∨
    (e = (1, 0) ∧ l = LStore false 0 [b1] .WCplain) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | k <;> simp [gxLbl, mpg'] at hl <;>
    subst hl <;> simp

theorem mpgAcc (e : Geid) (a : Int) :
    gaccesses mpg e a →
    (e = (0, 0) ∧ a = 0) ∨ (e = (0, 1) ∧ a = 8) ∨ (e = (1, 0) ∧ a = 0) := by
  rintro (⟨v, l, base, vs, j, hl, hwr, hv, ha⟩ | ⟨t, v, l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩)
  · rcases mpgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
      rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp
  · rcases mpgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
      rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp

theorem mpgWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte mpg e a v →
    (e = (0, 1) ∧ a = 8) ∨ (e = (1, 0) ∧ a = 0) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases mpgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp

theorem mpg'Acc (e : Geid) (a : Int) :
    gaccesses mpg' e a →
    (e = (0, 0) ∧ a = 0) ∨ (e = (0, 1) ∧ a = 8) ∨ (e = (1, 0) ∧ a = 0) := by
  rintro (⟨v, l, base, vs, j, hl, hwr, hv, ha⟩ | ⟨t, v, l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩)
  · rcases mpg'Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
      rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp
  · rcases mpg'Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
      rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp

theorem mpg'Wr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte mpg' e a v →
    (e = (0, 1) ∧ a = 8) ∨ (e = (1, 0) ∧ a = 0) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases mpg'Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp

/-! # 3. (a) `mpg` is RVWMO⁻(+deps)-consistent -/

theorem mpgConsistent : rvwmoMinusConsistent mpg := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · decide
  · intro e
    constructor
    · intro he
      simp only [mpg, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, hm⟩
      rcases mpgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [mpg] at hp <;> subst hp <;>
      rcases k with _ | _ | k <;> simp at hk <;> subst hk <;> simp
  · -- ppo⁻ ⊆ gmo: there are NO ppo⁻ edges
    intro e1 e2 hppo
    exfalso
    rcases hppo with hpl | hf | ha | hr
    · obtain ⟨⟨hag, hlt, _, _⟩, a, h1, h2⟩ := hpl
      rcases mpgAcc e1 a h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases mpgAcc e2 _ h2 with ⟨rfl, ha2⟩ | ⟨rfl, ha2⟩ | ⟨rfl, ha2⟩ <;>
        simp at hag hlt ha2
    · obtain ⟨pr, pw, sr, sw, ⟨_, _, kf, _, _, hlf⟩, _, _⟩ := hf
      rcases mpgLbl _ _ hlf with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    · obtain ⟨_, ⟨l, hl, _⟩, ⟨l', hl', haq⟩, _⟩ := ha
      rw [hl, Option.some.injEq] at hl'
      subst hl'
      rcases mpgLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbAq] at haq
    · obtain ⟨_, ⟨l, hl, hrc⟩, _⟩ := hr
      rcases mpgLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbRcsc, lbAq, lbRl] at hrc
  · -- load value: the ONE read, byte 0 at write index 2 = hart 1's store
    intro e a t v hr
    obtain ⟨l, base, ts, vs, j, hl, hrd, hj, hv, ha⟩ := hr
    rcases mpgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbRd] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    rcases j with _ | j <;> simp at hj hv
    subst hj hv
    simp [accAddr] at ha
    subst ha
    refine ⟨?_, ?_⟩
    · show ∃ w, gwriteAt mpg 2 = some w ∧ gwritesByte mpg w 0 b1 ∧ gvisible mpg w (0, 0)
      refine ⟨(1, 0), by decide, ⟨LStore false 0 [b1] .WCplain, 0, [b1], 0, rfl, rfl, rfl,
        by simp [accAddr]⟩, Or.inl ⟨by decide, by decide, by decide⟩⟩
    · intro w' v' hw' _
      rcases mpgWr w' _ _ hw' with ⟨rfl, hab⟩ | ⟨rfl, _⟩
      · simp at hab
      · decide
  · -- atomicity: no event both reads and writes
    intro e a t v hr ⟨l, hl, hw⟩
    obtain ⟨l', base, ts, vs, j, hl', hrd, _⟩ := hr
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    rcases mpgLbl e l hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [lbIsW, lbRd] at hw hrd

theorem mpgDepsConsistent : rvwmoMinusDepsConsistent mpgd :=
  ⟨mpgConsistent, fun _ h => by simp [mpgd] at h, fun _ h => by simp [mpgd] at h⟩

/-! # 4. (b) `killK1` is FALSE at `mpg` — its hypotheses all hold -/

theorem mpgdKillK1False : ¬ killK1 mpgd := by
  intro hK
  refine hK mpgd (gdEquivRefl mpgd mpgDepsConsistent) (0, 1) (0, 0) 0 2 b1 (1, 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the violation: e po-before w, w gmo-before e
    refine ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_, ?_, ?_⟩ <;> decide
  · -- `(0,1)` is gmo-minimal: it sits at gmo position 0
    rintro e' w' _ ⟨_, _, hlt⟩
    have h0 : gpos mpgd.gdG (0, 1) = 0 := by decide
    omega
  · -- `(0,0)` is po-minimal: it sits at po position 0
    intro e' _ hlt
    exact Nat.not_lt_zero _ hlt
  · -- the witness is a read
    rfl
  · -- it reads byte 0 at write index 2
    exact ⟨LLoad false 0 [2] [b1], 0, [2], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩
  · -- write index 2 is hart 1's store
    decide
  · -- which is CROSS-HART
    decide
  · -- and sits gmo-above the violating write ...
    refine ⟨?_, ?_, ?_⟩ <;> decide
  · -- ... and gmo-below the witness
    refine ⟨?_, ?_, ?_⟩ <;> decide

/-! # 5. (c) THE POINT: `mpg` HAS a rows-equivalent rule-14 graph -/

theorem mpg'Consistent : rvwmoMinusConsistent mpg' := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · decide
  · intro e
    constructor
    · intro he
      simp only [mpg', List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, hm⟩
      rcases mpg'Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [mpg'] at hp <;> subst hp <;>
      rcases k with _ | _ | k <;> simp at hk <;> subst hk <;> simp
  · intro e1 e2 hppo
    exfalso
    rcases hppo with hpl | hf | ha | hr
    · obtain ⟨⟨hag, hlt, _, _⟩, a, h1, h2⟩ := hpl
      rcases mpg'Acc e1 a h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases mpg'Acc e2 _ h2 with ⟨rfl, ha2⟩ | ⟨rfl, ha2⟩ | ⟨rfl, ha2⟩ <;>
        simp at hag hlt ha2
    · obtain ⟨pr, pw, sr, sw, ⟨_, _, kf, _, _, hlf⟩, _, _⟩ := hf
      rcases mpg'Lbl _ _ hlf with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    · obtain ⟨_, ⟨l, hl, _⟩, ⟨l', hl', haq⟩, _⟩ := ha
      rw [hl, Option.some.injEq] at hl'
      subst hl'
      rcases mpg'Lbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbAq] at haq
    · obtain ⟨_, ⟨l, hl, hrc⟩, _⟩ := hr
      rcases mpg'Lbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbRcsc, lbAq, lbRl] at hrc
  · -- load value: byte 0 at write index 1 = hart 1's store, now FIRST
    intro e a t v hr
    obtain ⟨l, base, ts, vs, j, hl, hrd, hj, hv, ha⟩ := hr
    rcases mpg'Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbRd] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    rcases j with _ | j <;> simp at hj hv
    subst hj hv
    simp [accAddr] at ha
    subst ha
    refine ⟨?_, ?_⟩
    · show ∃ w, gwriteAt mpg' 1 = some w ∧ gwritesByte mpg' w 0 b1 ∧ gvisible mpg' w (0, 0)
      refine ⟨(1, 0), by decide, ⟨LStore false 0 [b1] .WCplain, 0, [b1], 0, rfl, rfl, rfl,
        by simp [accAddr]⟩, Or.inl ⟨by decide, by decide, by decide⟩⟩
    · intro w' v' hw' _
      rcases mpg'Wr w' _ _ hw' with ⟨rfl, hab⟩ | ⟨rfl, _⟩
      · simp at hab
      · decide
  · intro e a t v hr ⟨l, hl, hw⟩
    obtain ⟨l', base, ts, vs, j, hl', hrd, _⟩ := hr
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    rcases mpg'Lbl e l hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [lbIsW, lbRd] at hw hrd

theorem mpg'DepsConsistent : rvwmoMinusDepsConsistent mpgd' :=
  ⟨mpg'Consistent, fun _ h => by simp [mpgd'] at h, fun _ h => by simp [mpgd'] at h⟩

/-- RULE 14 holds in `mpg'`: the only po pair is `e < w`, and `e` is now
gmo-below `w`. -/
theorem mpg'Rule14 : grule14 mpg' := by
  rintro e w hpo ⟨le, hle, _⟩ ⟨lw, hlw, hww⟩
  rcases mpg'Lbl w lw hlw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbIsW] at hww
  · rcases mpg'Lbl e le hle with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- the ONE surviving pair: hart 0's load po-before hart 0's store
      exact ⟨by decide, by decide, by decide⟩
    · exact absurd hpo.2.1 (by decide)
    · exact absurd hpo.1 (by decide)
  · rcases mpg'Lbl e le hle with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hpo.1 (by decide)
    · exact absurd hpo.1 (by decide)
    · exact absurd hpo.2.1 (by decide)

/-! ## 5.1 The rows correspondence: `tswap 1` renames write index 2 to 1 -/

theorem mpgRowsRel : rowsRel (tswap 1) mpg mpg' :=
  ⟨rfl, by decide, by decide⟩

theorem mpgGwrites : gwrites mpg = [(0, 1), (1, 0)] := by decide

theorem mpg'Gwrites : gwrites mpg' = [(1, 0), (0, 1)] := by decide

theorem mpgWperm : wperm (tswap 1) mpg mpg' := by
  refine ⟨tswapInj 1, ?_, ?_⟩
  · intro t
    rcases t with _ | _ | _ | t
    · decide
    · decide
    · decide
    · have ht : tswap 1 (t + 1 + 1 + 1) = t + 1 + 1 + 1 := by
        simp [tswap, sidx]
      rw [ht]
      simp only [gwriteAt, mpgGwrites, mpg'Gwrites]
      simp
  · rw [mpgGwrites, mpg'Gwrites]
    rfl

/-- THE STATEMENT OF THE FINDING: the two graphs are `gdEquiv`, and the second
satisfies rule 14 — so `mpg` normalizes, yet `killK1` demands that its
configuration be impossible. -/
theorem mpgEquiv : gdEquiv mpgd mpgd' :=
  ⟨tswap 1, mpgRowsRel, mpgWperm, rfl, mpg'DepsConsistent⟩

theorem mpgNormalizes : ∃ GD', gdEquiv mpgd GD' ∧ grule14 GD'.gdG :=
  ⟨mpgd', mpgEquiv, mpg'Rule14⟩

end Weak
