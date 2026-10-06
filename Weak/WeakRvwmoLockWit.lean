/-
Weak: **the lock-protocol kit's satisfiability witness** (route B, B2e-2).

Rocq: `iris/WeakRvwmoLockWit.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§4c; the kit is `Weak/WeakRvwmoLock.lean`).  `csKill` is a KILL — its conclusion
is `False` — so nothing in its statement rules out the hypotheses being jointly
contradictory.  This file closes that gap with a concrete two-hart graph `lkg`
on which every PROTOCOL and COVERAGE hypothesis of `csKill` holds at once
(`csKillHypsSat`).  The K1 configuration (`gviol G e w`, `gmoLt G w w0`,
`gmoLt G w0 e`) is deliberately left out: a graph carrying it as well is exactly
what `csKill` refutes.  `lkgNoViol` records the other half: the witness is
rule-14 CLEAN, so `csKill` is silent on it.

The check found a design bug, fixed in `WeakRvwmoGraph` (`gacqPo` gained its
`gmem G e2` conjunct, riscv.cat's `ppo ⊆ M × M`): without it every lock client's
acquire po-before its release FENCE demanded a gmo position for a fence, and the
hypothesis set was unsatisfiable for EVERY graph.

THE WITNESS.  One lock byte (address 0) and one data byte (address 8); hart 0
takes the lock first, hart 1's acquire reads hart 0's release.

    hart 0                                hart 1
    (0,0) ACQ  amoswap.aq  b:0 -> 1       (1,0) ACQ  amoswap.aq  b:0 -> 1
               reads the image (t=0)                 reads (0,3) (t=2)
    (0,1) LOAD d  (the CS body)           (1,1) STORE d := 1  (the CS body)
    (0,2) FENCE rw,rw                     (1,2) FENCE rw,rw
    (0,3) REL  store b := 0               (1,3) REL  store b := 0

gmo is program order per hart with hart 0's section first, so the two windows
are [1,2] and [3,5] in write indices — disjoint (`lkgWinExcl`).

A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  No name of this
   file is in `notes/weak-port-dupnames.json`.
2. VOCABULARY: as `WeakRvwmoLock` deviation 2; `GExec img prog gmo` ↦
   `⟨img, prog, gmo⟩`; `WeakLitmus.b0`/`b1`/`img0` ↦ `b0`/`b1`/`img0`;
   `WeakLitmus.img0_x`/`img0_y`/`b0_ne_b1` ↦ `img0X`/`img0Y`/`b0NeB1`.  The
   Rocq `Local Notation`s `ACQh`… are Lean `local notation`s.
3. The closed `vm_compute` side conditions (`gwrites` lookups, gmo positions,
   index comparisons) are `decide`.
4. Lean-only helper (no Rocq twin): `lkgLbl` (the eight labels of `lkg`, the
   engine of every case split, as `WeakRvwmoGraph.lbgLbl`).

**Name map** (Rocq → Lean): `lkg`; `lkg_nodup` ↦ `lkgNodup`; `lkg_gpos_of` ↦
`lkgGposOf`; `lkg_gwix_of` ↦ `lkgGwixOf`; `lkg_p00`/`p01`/`p03`/`p10`/`p11`/`p13`
↦ `lkgP00`/…/`lkgP13`; `lkg_w00`/`w03`/`w10`/`w11`/`w13` ↦ `lkgW00`/…/`lkgW13`;
`lkg_mem_inv` ↦ `lkgMemInv`; `lkg_gmo_mem` ↦ `lkgGmoMem`; `lkg_mo` ↦ `lkgMo`;
`lkg_gmo_po` ↦ `lkgGmoPo`; `lkg_wr` ↦ `lkgWr`; `lkg_rd` ↦ `lkgRd`;
`lkg_wr_lock` ↦ `lkgWrLock`; `lkg_wr_data` ↦ `lkgWrData`; `lkg_consistent` ↦
`lkgConsistent`; `lkg_pattern` ↦ `lkgPattern`; `lkg_acq_h`/`_j` ↦
`lkgAcqH`/`lkgAcqJ`; `lkg_rel_h`/`_j` ↦ `lkgRelH`/`lkgRelJ`; `lkg_cs_h`/`_j` ↦
`lkgCsH`/`lkgCsJ`; `lkg_paired` ↦ `lkgPaired`; `lkg_win_excl` ↦ `lkgWinExcl`;
`lkg_win_excl_h_first` ↦ `lkgWinExclHFirst`; `lkg_aq_h`/`_j` ↦
`lkgAqH`/`lkgAqJ`; `lkg_fence_h`/`_j` ↦ `lkgFenceH`/`lkgFenceJ`;
`cs_kill_hyps_sat` ↦ `csKillHypsSat`; `lkg_no_viol` ↦ `lkgNoViol`;
`lkg_rule14` ↦ `lkgRule14`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakMem
import Weak.WeakLitmus
import Weak.WeakAxiomatic
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg
import Weak.WeakRvwmoLock

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. The graph -/

def lkg : Gexec :=
  ⟨img0,
   [[LRmw true false 0 [0] [b0] [b1] .WCexcl,
     LLoad false 8 [0] [b0],
     LFence true true true true,
     LStore true 0 [b0] .WCrel],
    [LRmw true false 0 [2] [b0] [b1] .WCexcl,
     LStore false 8 [b1] .WCplain,
     LFence true true true true,
     LStore true 0 [b0] .WCrel]],
   [(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 3)]⟩

/- Shorthands for the six memory events. -/
local notation "ACQh" => ((0, 0) : Geid)
local notation "EVh" => ((0, 1) : Geid)
local notation "RELh" => ((0, 3) : Geid)
local notation "ACQj" => ((1, 0) : Geid)
local notation "EVj" => ((1, 1) : Geid)
local notation "RELj" => ((1, 3) : Geid)

/-! # 2. Inversions and the position/index arithmetic -/

theorem lkgNodup : lkg.gxGmo.Nodup := by decide

theorem lkgGposOf (n : Nat) (e : Geid) : lkg.gxGmo[n]? = some e → gpos lkg e = n :=
  gposOfLookup lkg n e lkgNodup

theorem lkgGwixOf (n : Nat) (w : Geid) : (gwrites lkg)[n]? = some w → gwix lkg w = n + 1 :=
  gwixOfLookup lkg n w lkgNodup

theorem lkgP00 : gpos lkg ACQh = 0 := lkgGposOf _ _ (by decide)
theorem lkgP01 : gpos lkg EVh = 1 := lkgGposOf _ _ (by decide)
theorem lkgP03 : gpos lkg RELh = 2 := lkgGposOf _ _ (by decide)
theorem lkgP10 : gpos lkg ACQj = 3 := lkgGposOf _ _ (by decide)
theorem lkgP11 : gpos lkg EVj = 4 := lkgGposOf _ _ (by decide)
theorem lkgP13 : gpos lkg RELj = 5 := lkgGposOf _ _ (by decide)

theorem lkgW00 : gwix lkg ACQh = 1 := lkgGwixOf 0 _ (by decide)
theorem lkgW03 : gwix lkg RELh = 2 := lkgGwixOf 1 _ (by decide)
theorem lkgW10 : gwix lkg ACQj = 3 := lkgGwixOf 2 _ (by decide)
theorem lkgW11 : gwix lkg EVj = 4 := lkgGwixOf 3 _ (by decide)
theorem lkgW13 : gwix lkg RELj = 5 := lkgGwixOf 4 _ (by decide)

/-- Lean-only: the eight labels of `lkg`. -/
theorem lkgLbl (e : Geid) (l : Lbl) : gxLbl lkg e = some l →
    (e = ACQh ∧ l = LRmw true false 0 [0] [b0] [b1] .WCexcl) ∨
    (e = EVh ∧ l = LLoad false 8 [0] [b0]) ∨
    (e = (0, 2) ∧ l = LFence true true true true) ∨
    (e = RELh ∧ l = LStore true 0 [b0] .WCrel) ∨
    (e = ACQj ∧ l = LRmw true false 0 [2] [b0] [b1] .WCexcl) ∨
    (e = EVj ∧ l = LStore false 8 [b1] .WCplain) ∨
    (e = (1, 2) ∧ l = LFence true true true true) ∨
    (e = RELj ∧ l = LStore true 0 [b0] .WCrel) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | _ | _ | k <;> simp [gxLbl, lkg] at hl <;>
    subst hl <;> simp

/-- The six memory events, and nothing else. -/
theorem lkgMemInv (e : Geid) :
    gmem lkg e →
    e = ACQh ∨ e = EVh ∨ e = RELh ∨ e = ACQj ∨ e = EVj ∨ e = RELj := by
  rintro ⟨l, hl, hm⟩
  rcases lkgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | decide | exact absurd hm (by decide)

theorem lkgGmoMem (e : Geid) : gmem lkg e → e ∈ lkg.gxGmo := by
  intro h
  rcases lkgMemInv e h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem lkgMo (e1 e2 : Geid) :
    gmem lkg e1 → gmem lkg e2 → gpos lkg e1 < gpos lkg e2 → gmoLt lkg e1 e2 :=
  fun h1 h2 hlt => ⟨lkgGmoMem e1 h1, lkgGmoMem e2 h2, hlt⟩

/-- THE SHAPE OF THIS EXECUTION: gmo IS per-hart program order (hart 0's
section first), so every same-hart po-earlier memory event is gmo-earlier.
Every ppo⁻ arm is same-hart, po-earlier and memory-to-memory, so this one lemma
discharges `gppoGmo` wholesale. -/
theorem lkgGmoPo (e1 e2 : Geid) :
    gmem lkg e1 → gmem lkg e2 → e1.1 = e2.1 → e1.2 < e2.2 → gmoLt lkg e1 e2 := by
  intro hm1 hm2 hag hlt
  refine ⟨lkgGmoMem e1 hm1, lkgGmoMem e2 hm2, ?_⟩
  rcases lkgMemInv e1 hm1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases lkgMemInv e2 hm2 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hag hlt <;> decide

/-- The write footprints. -/
theorem lkgWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte lkg e a v →
    (e = ACQh ∧ a = 0 ∧ v = b1) ∨
    (e = RELh ∧ a = 0 ∧ v = b0) ∨
    (e = ACQj ∧ a = 0 ∧ v = b1) ∨
    (e = EVj ∧ a = 8 ∧ v = b1) ∨
    (e = RELj ∧ a = 0 ∧ v = b0) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases lkgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha hv <;> simp

/-- The read footprints. -/
theorem lkgRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte lkg e a t v →
    (e = ACQh ∧ a = 0 ∧ t = 0 ∧ v = b0) ∨
    (e = EVh ∧ a = 8 ∧ t = 0 ∧ v = b0) ∨
    (e = ACQj ∧ a = 0 ∧ t = 2 ∧ v = b0) := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases lkgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
    rcases j with _ | j <;> simp at ht hv <;> simp [accAddr] at ha <;> subst ha ht hv <;> simp

/-- The two per-byte specializations the protocol proofs use. -/
theorem lkgWrLock (w : Geid) (v : BitVec 8) :
    gwritesByte lkg w 0 v →
    (w = ACQh ∧ v = b1) ∨ (w = RELh ∧ v = b0) ∨
    (w = ACQj ∧ v = b1) ∨ (w = RELj ∧ v = b0) := by
  intro h
  rcases lkgWr w 0 v h with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨-, hab, -⟩ |
      ⟨rfl, -, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact absurd hab (by omega)
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem lkgWrData (w : Geid) (v : BitVec 8) :
    gwritesByte lkg w 8 v → w = EVj ∧ v = b1 := by
  intro h
  rcases lkgWr w 8 v h with ⟨-, hab, -⟩ | ⟨-, hab, -⟩ | ⟨-, hab, -⟩ | ⟨rfl, -, rfl⟩ |
      ⟨-, hab, -⟩
  · exact absurd hab (by omega)
  · exact absurd hab (by omega)
  · exact absurd hab (by omega)
  · exact ⟨rfl, rfl⟩
  · exact absurd hab (by omega)

/-! # 3. `lkg` is RVWMO⁻-consistent -/

theorem lkgConsistent : rvwmoMinusConsistent lkg := by
  refine ⟨⟨lkgNodup, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      simp only [lkg, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · exact lkgGmoMem e
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [lkg] at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | k <;> simp at hk <;> subst hk <;> simp
  · -- ppo⁻ ⊆ gmo: every arm is same-hart, po-earlier, memory-to-memory
    intro e1 e2 hppo
    obtain ⟨hm1, hm2⟩ := gppoGmem lkg e1 e2 hppo
    obtain ⟨hag, hlt⟩ := gppoPoLt lkg e1 e2 hppo
    exact lkgGmoPo e1 e2 hm1 hm2 hag hlt
  · -- load value
    intro e a t v hr
    rcases lkgRd e a t v hr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩
    · -- the h-acquire reads the image: it is gmo- and po-first
      refine ⟨img0X, ?_⟩
      intro w' v' _ hvis
      exfalso
      rcases hvis with ⟨_, _, hp⟩ | ⟨_, hoff, _⟩
      · rw [lkgP00] at hp
        omega
      · exact absurd hoff (Nat.not_lt_zero _)
    · -- the CS-body load reads the data byte's image value
      refine ⟨img0Y, ?_⟩
      intro w' v' hw' hvis
      obtain ⟨rfl, rfl⟩ := lkgWrData w' v' hw'
      exfalso
      rcases hvis with ⟨_, _, hp⟩ | ⟨hag, _, _⟩
      · rw [lkgP11, lkgP01] at hp
        omega
      · exact absurd hag (by decide)
    · -- the j-acquire reads the h-release, which is co-maximal below it
      refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt lkg 2 = some w ∧ gwritesByte lkg w 0 b0 ∧ gvisible lkg w ACQj
        refine ⟨RELh, by decide,
          ⟨LStore true 0 [b0] .WCrel, 0, [b0], 0, rfl, rfl, rfl, by simp [accAddr]⟩, ?_⟩
        refine Or.inl (lkgMo _ _ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ ?_)
        rw [lkgP03, lkgP10]
        omega
      · intro w' v' hw' hvis
        rcases lkgWrLock w' v' hw' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · rw [lkgW00]; omega
        · rw [lkgW03]; omega
        · exfalso
          rcases hvis with hmo | ⟨_, hoff, _⟩
          · exact gmoLtIrrefl lkg _ hmo
          · exact absurd hoff (Nat.lt_irrefl _)
        · exfalso
          rcases hvis with ⟨_, _, hp⟩ | ⟨_, hoff, _⟩
          · rw [lkgP13, lkgP10] at hp
            omega
          · exact absurd hoff (by decide)
  · -- atomicity: the two RMWs read their own immediate co-predecessor
    intro e a t v hr hw w' v' _ hbetw
    obtain ⟨hlo, hhi⟩ := hbetw
    rcases lkgRd e a t v hr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩
    · rw [lkgW00] at hhi
      omega
    · obtain ⟨l, hl, hlw⟩ := hw
      have h01 : gxLbl lkg EVh = some (LLoad false 8 [0] [b0]) := rfl
      rw [h01, Option.some.injEq] at hl
      subst hl
      exact absurd hlw (by decide)
    · rw [lkgW10] at hhi
      omega

/-! # 4. The lock protocol on byte 0 -/

theorem lkgPattern : lockPattern lkg 0 := by
  refine ⟨fun v0 hv => ?_, fun w v hw => ?_⟩
  · have hx : lkg.gxImg 0 = some lockFree := img0X
    rw [hx] at hv
    exact (Option.some.inj hv).symm
  · rcases lkgWrLock w v hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      refine ⟨⟨_, rfl, rfl⟩, fun h => b0NeB1 h.symm, 0, ?_⟩
      exact ⟨LRmw true false 0 [0] [b0] [b1] .WCexcl, 0, [0], [b0], 0, rfl, rfl, rfl, rfl,
        by simp [accAddr]⟩
    · right; rfl
    · left
      refine ⟨⟨_, rfl, rfl⟩, fun h => b0NeB1 h.symm, 2, ?_⟩
      exact ⟨LRmw true false 0 [2] [b0] [b1] .WCexcl, 0, [2], [b0], 0, rfl, rfl, rfl, rfl,
        by simp [accAddr]⟩
    · right; rfl

theorem lkgAcqH : lockAcq lkg 0 ACQh :=
  ⟨b1, ⟨LRmw true false 0 [0] [b0] [b1] .WCexcl, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
    fun h => b0NeB1 h.symm⟩

theorem lkgAcqJ : lockAcq lkg 0 ACQj :=
  ⟨b1, ⟨LRmw true false 0 [2] [b0] [b1] .WCexcl, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
    fun h => b0NeB1 h.symm⟩

theorem lkgRelH : lockRel lkg 0 RELh :=
  ⟨LStore true 0 [b0] .WCrel, 0, [b0], 0, rfl, rfl, rfl, by simp [accAddr]⟩

theorem lkgRelJ : lockRel lkg 0 RELj :=
  ⟨LStore true 0 [b0] .WCrel, 0, [b0], 0, rfl, rfl, rfl, by simp [accAddr]⟩

/-- The two critical sections, built the way B2e-3 will build them: from the
PO-LOCAL fact that between my acquire and my release my hart writes the lock
byte nowhere else. -/
theorem lkgCsH : lockCs lkg 0 ACQh RELh := by
  apply lockCsIntro lkg 0 ACQh RELh lkgConsistent ⟨rfl, by decide, rfl, rfl⟩ lkgAcqH lkgRelH
  intro x v hx hag hlo hhi
  rcases lkgWrLock x v hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    revert hag hlo hhi <;> decide

theorem lkgCsJ : lockCs lkg 0 ACQj RELj := by
  apply lockCsIntro lkg 0 ACQj RELj lkgConsistent ⟨rfl, by decide, rfl, rfl⟩ lkgAcqJ lkgRelJ
  intro x v hx hag hlo hhi
  rcases lkgWrLock x v hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    revert hag hlo hhi <;> decide

theorem lkgPaired : lockPaired lkg 0 := by
  intro R hR
  rcases lkgWrLock R lockFree hR with ⟨rfl, hv⟩ | ⟨rfl, -⟩ | ⟨rfl, hv⟩ | ⟨rfl, -⟩
  · exact absurd hv b0NeB1
  · exact ⟨ACQh, lkgCsH⟩
  · exact absurd hv b0NeB1
  · exact ⟨ACQj, lkgCsJ⟩

/-! # 5. THE WINDOWS REALLY ORDER

`winExclOfPattern`'s conclusion instantiated at the two sections — and
resolved: it is the LEFT disjunct, hart 0's release (write index 2) below hart
1's acquire (write index 3). -/

theorem lkgWinExcl :
    gwix lkg RELh < gwix lkg ACQj ∨ gwix lkg RELj < gwix lkg ACQh :=
  winExclOfPattern lkg 0 lkgConsistent lkgPattern lkgPaired
    ACQh RELh ACQj RELj lkgCsH lkgCsJ (by decide)

theorem lkgWinExclHFirst : gwix lkg RELh < gwix lkg ACQj := by
  rcases lkgWinExcl with h | h
  · exact h
  · rw [lkgW13, lkgW00] at h
    omega

/-! # 6. THE COVERAGE FACTS, AND THE SATISFIABILITY STATEMENT -/

theorem lkgAqH : glblIs lkg ACQh lbAq := ⟨LRmw true false 0 [0] [b0] [b1] .WCexcl, rfl, rfl⟩

theorem lkgAqJ : glblIs lkg ACQj lbAq := ⟨LRmw true false 0 [2] [b0] [b1] .WCexcl, rfl, rfl⟩

/-- The release fence covers the CS body to the release: `(0,2)` / `(1,2)` sit
at an INTERMEDIATE po position of the same hart, which is `gfenceBetween`'s
shape. -/
theorem lkgFenceH : gfenceCovers lkg EVh RELh :=
  ⟨true, true, true, true, ⟨rfl, by decide, 2, by decide, by decide, rfl⟩,
    Or.inl ⟨⟨LLoad false 8 [0] [b0], rfl, rfl⟩, rfl⟩,
    Or.inr ⟨⟨LStore true 0 [b0] .WCrel, rfl, rfl⟩, rfl⟩⟩

theorem lkgFenceJ : gfenceCovers lkg EVj RELj :=
  ⟨true, true, true, true, ⟨rfl, by decide, 2, by decide, by decide, rfl⟩,
    Or.inr ⟨⟨LStore false 8 [b1] .WCplain, rfl, rfl⟩, rfl⟩,
    Or.inr ⟨⟨LStore true 0 [b0] .WCrel, rfl, rfl⟩, rfl⟩⟩

/-- THE STATEMENT: every hypothesis of `csKill` except the three
K1-configuration facts (`gviol G e w`, `gmoLt G w w0`, `gmoLt G w0 e`) holds
simultaneously.  A graph carrying the configuration as well is exactly what
`csKill` refutes. -/
theorem csKillHypsSat :
    ∃ (G : Gexec) (b : Int) (e w0 A_h R_h A_j R_j : Geid),
      rvwmoMinusConsistent G ∧
      lockPattern G b ∧ lockPaired G b ∧
      lockCs G b A_h R_h ∧
      WeakRvwmoGraph.gpo G A_h e ∧ glblIs G A_h lbAq ∧ gfenceCovers G e R_h ∧
      lockCs G b A_j R_j ∧
      WeakRvwmoGraph.gpo G A_j w0 ∧ glblIs G A_j lbAq ∧ gfenceCovers G w0 R_j ∧
      e.1 ≠ w0.1 :=
  ⟨lkg, 0, EVh, EVj, ACQh, RELh, ACQj, RELj,
    lkgConsistent, lkgPattern, lkgPaired, lkgCsH,
    ⟨rfl, by decide, rfl, rfl⟩, lkgAqH, lkgFenceH, lkgCsJ,
    ⟨rfl, by decide, rfl, rfl⟩, lkgAqJ, lkgFenceJ, by decide⟩

/-! # 7. THE OTHER HALF: the witness has no violation

`csKill` is not vacuous, but neither does it FIRE here: `lkg` is rule-14 clean,
so the configuration facts it would need are absent. -/

theorem lkgNoViol (e w : Geid) : ¬ gviol lkg e w := by
  rintro ⟨hpo, hme, hw, hmo⟩
  obtain ⟨hag, hlt, _, _⟩ := hpo
  exact gmoLtIrrefl lkg e (gmoLtTrans lkg e w e
    (lkgGmoPo e w hme (WeakRvwmoGraph.glblIsWGmem lkg w hw) hag hlt) hmo)

theorem lkgRule14 : grule14 lkg :=
  gviolGrule14 lkg lkgConsistent.1 lkgNoViol

end Weak
