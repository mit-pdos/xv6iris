/-
Weak: **the failed-swap probe: `lockPattern` is FALSE for every contended xv6
lock** (route B, §4d.1 finding F4(a)).

Rocq: `iris/WeakRvwmoProbeSwap.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§4d.1; the kit under probe is `Weak/WeakRvwmoLock.lean`, not modified here).
xv6's `acquire` spins with `while (__sync_lock_test_and_set(&lk->locked, 1) != 0)`,
an `amoswap.w.aq` that UNCONDITIONALLY WRITES 1.  A FAILED iteration is a
`b`-write of a NONZERO byte whose own read entry at `b` names a NONZERO value.
`lockPattern G b` admits only releases (`v = lockFree`) and acquires (an RMW
reading `lockFree`), so a failed swap is neither, and `lockPattern` is FALSE on
every execution in which a lock is CONTENDED — a hypothesis of
`winExclOfPattern` and, through it, of `csKill`.

THE REPAIR (not made here): a THIRD ARM (an RMW reading nonzero and writing
nonzero); `acqNoOverlap`'s induction must step over such writes, and
`acqSrcRel` survives only for acquires proper.

WHAT IS MACHINE-CHECKED.  `swg` is `WeakRvwmoLockWit.lkg` with ONE extra event:
hart 1 spins once — a failed `amoswap.w.aq` reading the 1 that hart 0's acquire
wrote — before its successful acquire.

    hart 0                                hart 1
    (0,0) ACQ  amoswap.aq  b:0 -> 1       (1,0) SWP amoswap.aq b:1 -> 1
               reads the image (t=0)                reads (0,0) (t=1)  <<<< NEW
    (0,1) LOAD d  (the CS body)           (1,1) ACQ amoswap.aq b:0 -> 1
    (0,2) FENCE rw,rw                                reads (0,3) (t=3)
    (0,3) REL  store b := 0               (1,2) STORE d := 1  (the CS body)
                                          (1,3) FENCE rw,rw
                                          (1,4) REL  store b := 0

`swgConsistent` (a contended lock is a LEGITIMATE execution), `swgNoPattern`
(THE FINDING), `swgPaired` (otherwise protocol-clean).

A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  No name of this
   file is in `notes/weak-port-dupnames.json`.
2. VOCABULARY: as `Weak/WeakRvwmoLockWit.lean` deviation 2 (the Rocq
   `Local Notation`s are Lean `local notation`s).
3. The closed `vm_compute` side conditions and the `gpos`-rewrite arithmetic of
   the load-value cases are `decide`.
4. Lean-only helper (no Rocq twin): `swgLbl` (the nine labels of `swg`).

**Name map** (Rocq → Lean): `swg`; `swg_nodup` ↦ `swgNodup`; `swg_gpos_of` ↦
`swgGposOf`; `swg_gwix_of` ↦ `swgGwixOf`; `swg_p00`/`p10`/`p01`/`p03`/`p11`/
`p12`/`p14` ↦ `swgP00`/…/`swgP14`; `swg_w00`/`w10`/`w03`/`w11`/`w12`/`w14` ↦
`swgW00`/…/`swgW14`; `swg_mem_inv` ↦ `swgMemInv`; `swg_gmo_mem` ↦ `swgGmoMem`;
`swg_gmo_po` ↦ `swgGmoPo`; `swg_wr` ↦ `swgWr`; `swg_rd` ↦ `swgRd`;
`swg_wr_lock` ↦ `swgWrLock`; `swg_wr_data` ↦ `swgWrData`; `swg_consistent` ↦
`swgConsistent`; `swg_swp_writes_one` ↦ `swgSwpWritesOne`;
`swg_swp_reads_one` ↦ `swgSwpReadsOne`; `swg_no_pattern` ↦ `swgNoPattern`;
`swg_swp_lock_acq` ↦ `swgSwpLockAcq`; `swg_acq_h`/`_j` ↦ `swgAcqH`/`swgAcqJ`;
`swg_rel_h`/`_j` ↦ `swgRelH`/`swgRelJ`; `swg_cs_h`/`_j` ↦ `swgCsH`/`swgCsJ`;
`swg_paired` ↦ `swgPaired`.

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

/-! # 1. The graph

Write indices (`gwix`, 1-based) after the insertion:

    1  ACQh  (0,0)      4  ACQj  (1,1)
    2  SWP   (1,0)      5  EVj   (1,2)
    3  RELh  (0,3)      6  RELj  (1,4)

so the failed swap's read index is 1 (hart 0's acquire) and hart 1's successful
acquire reads index 3 (hart 0's release). -/

def swg : Gexec :=
  ⟨img0,
   [[LRmw true false 0 [0] [b0] [b1] .WCexcl,
     LLoad false 8 [0] [b0],
     LFence true true true true,
     LStore true 0 [b0] .WCrel],
    [LRmw true false 0 [1] [b1] [b1] .WCexcl,
     LRmw true false 0 [3] [b0] [b1] .WCexcl,
     LStore false 8 [b1] .WCplain,
     LFence true true true true,
     LStore true 0 [b0] .WCrel]],
   [(0, 0), (1, 0), (0, 1), (0, 3), (1, 1), (1, 2), (1, 4)]⟩

local notation "ACQh" => ((0, 0) : Geid)
local notation "EVh" => ((0, 1) : Geid)
local notation "RELh" => ((0, 3) : Geid)
local notation "SWP" => ((1, 0) : Geid)
local notation "ACQj" => ((1, 1) : Geid)
local notation "EVj" => ((1, 2) : Geid)
local notation "RELj" => ((1, 4) : Geid)

/-! # 2. Inversions and the position/index arithmetic -/

theorem swgNodup : swg.gxGmo.Nodup := by decide

theorem swgGposOf (n : Nat) (e : Geid) : swg.gxGmo[n]? = some e → gpos swg e = n :=
  gposOfLookup swg n e swgNodup

theorem swgGwixOf (n : Nat) (w : Geid) : (gwrites swg)[n]? = some w → gwix swg w = n + 1 :=
  gwixOfLookup swg n w swgNodup

theorem swgP00 : gpos swg ACQh = 0 := swgGposOf _ _ (by decide)
theorem swgP10 : gpos swg SWP = 1 := swgGposOf _ _ (by decide)
theorem swgP01 : gpos swg EVh = 2 := swgGposOf _ _ (by decide)
theorem swgP03 : gpos swg RELh = 3 := swgGposOf _ _ (by decide)
theorem swgP11 : gpos swg ACQj = 4 := swgGposOf _ _ (by decide)
theorem swgP12 : gpos swg EVj = 5 := swgGposOf _ _ (by decide)
theorem swgP14 : gpos swg RELj = 6 := swgGposOf _ _ (by decide)

theorem swgW00 : gwix swg ACQh = 1 := swgGwixOf 0 _ (by decide)
theorem swgW10 : gwix swg SWP = 2 := swgGwixOf 1 _ (by decide)
theorem swgW03 : gwix swg RELh = 3 := swgGwixOf 2 _ (by decide)
theorem swgW11 : gwix swg ACQj = 4 := swgGwixOf 3 _ (by decide)
theorem swgW12 : gwix swg EVj = 5 := swgGwixOf 4 _ (by decide)
theorem swgW14 : gwix swg RELj = 6 := swgGwixOf 5 _ (by decide)

/-- Lean-only: the nine labels of `swg`. -/
theorem swgLbl (e : Geid) (l : Lbl) : gxLbl swg e = some l →
    (e = ACQh ∧ l = LRmw true false 0 [0] [b0] [b1] .WCexcl) ∨
    (e = EVh ∧ l = LLoad false 8 [0] [b0]) ∨
    (e = (0, 2) ∧ l = LFence true true true true) ∨
    (e = RELh ∧ l = LStore true 0 [b0] .WCrel) ∨
    (e = SWP ∧ l = LRmw true false 0 [1] [b1] [b1] .WCexcl) ∨
    (e = ACQj ∧ l = LRmw true false 0 [3] [b0] [b1] .WCexcl) ∨
    (e = EVj ∧ l = LStore false 8 [b1] .WCplain) ∨
    (e = (1, 3) ∧ l = LFence true true true true) ∨
    (e = RELj ∧ l = LStore true 0 [b0] .WCrel) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | _ | _ | _ | k <;> simp [gxLbl, swg] at hl <;>
    subst hl <;> simp

/-- The seven memory events, and nothing else. -/
theorem swgMemInv (e : Geid) :
    gmem swg e →
    e = ACQh ∨ e = EVh ∨ e = RELh ∨ e = SWP ∨ e = ACQj ∨ e = EVj ∨ e = RELj := by
  rintro ⟨l, hl, hm⟩
  rcases swgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | decide | exact absurd hm (by decide)

theorem swgGmoMem (e : Geid) : gmem swg e → e ∈ swg.gxGmo := by
  intro h
  rcases swgMemInv e h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- gmo IS per-hart program order, so every same-hart po-earlier memory event
is gmo-earlier — this one lemma discharges `gppoGmo` wholesale. -/
theorem swgGmoPo (e1 e2 : Geid) :
    gmem swg e1 → gmem swg e2 → e1.1 = e2.1 → e1.2 < e2.2 → gmoLt swg e1 e2 := by
  intro hm1 hm2 hag hlt
  refine ⟨swgGmoMem e1 hm1, swgGmoMem e2 hm2, ?_⟩
  rcases swgMemInv e1 hm1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases swgMemInv e2 hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hag hlt <;> decide

/-- The write footprints. -/
theorem swgWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte swg e a v →
    (e = ACQh ∧ a = 0 ∧ v = b1) ∨
    (e = RELh ∧ a = 0 ∧ v = b0) ∨
    (e = SWP ∧ a = 0 ∧ v = b1) ∨
    (e = ACQj ∧ a = 0 ∧ v = b1) ∨
    (e = EVj ∧ a = 8 ∧ v = b1) ∨
    (e = RELj ∧ a = 0 ∧ v = b0) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases swgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha hv <;> simp

/-- The read footprints.  THE HEART OF THE FINDING is the third arm: the failed
swap's read entry at byte 0 names the value `b1`, not `b0`. -/
theorem swgRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte swg e a t v →
    (e = ACQh ∧ a = 0 ∧ t = 0 ∧ v = b0) ∨
    (e = EVh ∧ a = 8 ∧ t = 0 ∧ v = b0) ∨
    (e = SWP ∧ a = 0 ∧ t = 1 ∧ v = b1) ∨
    (e = ACQj ∧ a = 0 ∧ t = 3 ∧ v = b0) := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases swgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
    rcases j with _ | j <;> simp at ht hv <;> simp [accAddr] at ha <;> subst ha ht hv <;> simp

theorem swgWrLock (w : Geid) (v : BitVec 8) :
    gwritesByte swg w 0 v →
    (w = ACQh ∧ v = b1) ∨ (w = RELh ∧ v = b0) ∨
    (w = SWP ∧ v = b1) ∨ (w = ACQj ∧ v = b1) ∨
    (w = RELj ∧ v = b0) := by
  intro h
  rcases swgWr w 0 v h with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ |
      ⟨-, hab, -⟩ | ⟨rfl, -, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact absurd hab (by omega)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

theorem swgWrData (w : Geid) (v : BitVec 8) :
    gwritesByte swg w 8 v → w = EVj ∧ v = b1 := by
  intro h
  rcases swgWr w 8 v h with ⟨-, hab, -⟩ | ⟨-, hab, -⟩ | ⟨-, hab, -⟩ | ⟨-, hab, -⟩ |
      ⟨rfl, -, rfl⟩ | ⟨-, hab, -⟩
  · exact absurd hab (by omega)
  · exact absurd hab (by omega)
  · exact absurd hab (by omega)
  · exact absurd hab (by omega)
  · exact ⟨rfl, rfl⟩
  · exact absurd hab (by omega)

/-! # 3. `swg` IS RVWMO⁻-CONSISTENT — the contended lock is a real execution -/

theorem swgConsistent : rvwmoMinusConsistent swg := by
  refine ⟨⟨swgNodup, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      simp only [swg, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · exact swgGmoMem e
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [swg] at hp <;> subst hp <;>
      rcases k with _ | _ | _ | _ | _ | k <;> simp at hk <;> subst hk <;> simp
  · -- ppo⁻ ⊆ gmo
    intro e1 e2 hppo
    obtain ⟨hm1, hm2⟩ := gppoGmem swg e1 e2 hppo
    obtain ⟨hag, hlt⟩ := gppoPoLt swg e1 e2 hppo
    exact swgGmoPo e1 e2 hm1 hm2 hag hlt
  · -- load value
    intro e a t v hr
    rcases swgRd e a t v hr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · -- ACQh reads the image: it is gmo- and po-first
      refine ⟨img0X, ?_⟩
      intro w' v' _ hvis
      exfalso
      rcases hvis with ⟨_, _, hp⟩ | ⟨_, hoff, _⟩
      · rw [swgP00] at hp
        omega
      · exact absurd hoff (Nat.not_lt_zero _)
    · -- EVh reads the data byte's image value
      refine ⟨img0Y, ?_⟩
      intro w' v' hw' hvis
      obtain ⟨rfl, rfl⟩ := swgWrData w' v' hw'
      exfalso
      rcases hvis with ⟨_, _, hp⟩ | ⟨hag, _, _⟩
      · rw [swgP12, swgP01] at hp
        omega
      · exact absurd hag (by decide)
    · -- THE FAILED SWAP reads hart 0's acquire (write index 1)
      refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt swg 1 = some w ∧ gwritesByte swg w 0 b1 ∧ gvisible swg w SWP
        refine ⟨ACQh, by decide,
          ⟨LRmw true false 0 [0] [b0] [b1] .WCexcl, 0, [b1], 0, rfl, rfl, rfl,
            by simp [accAddr]⟩, ?_⟩
        refine Or.inl ⟨swgGmoMem _ ⟨_, rfl, rfl⟩, swgGmoMem _ ⟨_, rfl, rfl⟩, ?_⟩
        rw [swgP00, swgP10]
        omega
      · intro w' v' hw' hvis
        rcases swgWrLock w' v' hw' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Nat.le_of_eq swgW00
        · exfalso
          rcases hvis with ⟨_, _, hp⟩ | ⟨hag, _, _⟩
          · rw [swgP03, swgP10] at hp
            omega
          · exact absurd hag (by decide)
        · exfalso
          rcases hvis with hmo | ⟨_, hoff, _⟩
          · exact gmoLtIrrefl swg _ hmo
          · exact absurd hoff (Nat.lt_irrefl _)
        · exfalso
          rcases hvis with ⟨_, _, hp⟩ | ⟨_, hoff, _⟩
          · rw [swgP11, swgP10] at hp
            omega
          · exact absurd hoff (by decide)
        · exfalso
          rcases hvis with ⟨_, _, hp⟩ | ⟨_, hoff, _⟩
          · rw [swgP14, swgP10] at hp
            omega
          · exact absurd hoff (by decide)
    · -- ACQj reads the h-release, now at write index 3
      refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt swg 3 = some w ∧ gwritesByte swg w 0 b0 ∧ gvisible swg w ACQj
        refine ⟨RELh, by decide,
          ⟨LStore true 0 [b0] .WCrel, 0, [b0], 0, rfl, rfl, rfl, by simp [accAddr]⟩, ?_⟩
        refine Or.inl ⟨swgGmoMem _ ⟨_, rfl, rfl⟩, swgGmoMem _ ⟨_, rfl, rfl⟩, ?_⟩
        rw [swgP03, swgP11]
        omega
      · intro w' v' hw' hvis
        rcases swgWrLock w' v' hw' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · rw [swgW00]; omega
        · exact Nat.le_of_eq swgW03
        · rw [swgW10]; omega
        · exfalso
          rcases hvis with hmo | ⟨_, hoff, _⟩
          · exact gmoLtIrrefl swg _ hmo
          · exact absurd hoff (Nat.lt_irrefl _)
        · exfalso
          rcases hvis with ⟨_, _, hp⟩ | ⟨_, hoff, _⟩
          · rw [swgP14, swgP11] at hp
            omega
          · exact absurd hoff (by decide)
  · -- atomicity: each RMW's read source is its immediate co-predecessor
    intro e a t v hr hw w' v' _ hbetw
    obtain ⟨hlo, hhi⟩ := hbetw
    rcases swgRd e a t v hr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [swgW00] at hhi
      omega
    · obtain ⟨l, hl, hlw⟩ := hw
      have h01 : gxLbl swg EVh = some (LLoad false 8 [0] [b0]) := rfl
      rw [h01, Option.some.injEq] at hl
      subst hl
      exact absurd hlw (by decide)
    · rw [swgW10] at hhi
      omega
    · rw [swgW11] at hhi
      omega

/-! # 4. THE FINDING: `lockPattern` IS FALSE ON `swg`

The failed swap is a byte-0 write of `b1`.  The release arm needs
`b1 = lockFree`; the acquire arm needs a read entry of `swg` at `SWP`, byte 0,
valued `lockFree` — and `swgRd` says that entry is valued `b1`. -/

theorem swgSwpWritesOne : gwritesByte swg SWP 0 b1 :=
  ⟨LRmw true false 0 [1] [b1] [b1] .WCexcl, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩

/-- The failed swap reads NONZERO: no read entry of it at byte 0 is free. -/
theorem swgSwpReadsOne (t : Nat) : ¬ greadsByte swg SWP 0 t lockFree := by
  intro h
  rcases swgRd _ _ _ _ h with ⟨he, -⟩ | ⟨he, -⟩ | ⟨-, -, -, hv⟩ | ⟨he, -⟩
  · exact absurd he (by decide)
  · exact absurd he (by decide)
  · exact b0NeB1 hv
  · exact absurd he (by decide)

theorem swgNoPattern : ¬ lockPattern swg 0 := by
  rintro ⟨_, hpat⟩
  rcases hpat SWP b1 swgSwpWritesOne with ⟨_, _, t, ht⟩ | hz
  · exact swgSwpReadsOne t ht
  · exact b0NeB1 hz.symm

/-- For the record: `SWP` IS an acquire in the LOOSE sense (`lockAcq`, a nonzero
`b`-write).  What fails is the pattern's demand that every such write have read
`lockFree`. -/
theorem swgSwpLockAcq : lockAcq swg 0 SWP :=
  ⟨b1, swgSwpWritesOne, fun h => b0NeB1 h.symm⟩

/-! # 5. THE GRAPH IS OTHERWISE PROTOCOL-CLEAN: `lockPaired` SURVIVES

Hart 1's section is unaffected by the spin because the failed swap is po-BEFORE
hart 1's acquire, hence not co-between the acquire and the release. -/

theorem swgAcqH : lockAcq swg 0 ACQh :=
  ⟨b1, ⟨LRmw true false 0 [0] [b0] [b1] .WCexcl, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
    fun h => b0NeB1 h.symm⟩

theorem swgAcqJ : lockAcq swg 0 ACQj :=
  ⟨b1, ⟨LRmw true false 0 [3] [b0] [b1] .WCexcl, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
    fun h => b0NeB1 h.symm⟩

theorem swgRelH : lockRel swg 0 RELh :=
  ⟨LStore true 0 [b0] .WCrel, 0, [b0], 0, rfl, rfl, rfl, by simp [accAddr]⟩

theorem swgRelJ : lockRel swg 0 RELj :=
  ⟨LStore true 0 [b0] .WCrel, 0, [b0], 0, rfl, rfl, rfl, by simp [accAddr]⟩

theorem swgCsH : lockCs swg 0 ACQh RELh := by
  apply lockCsIntro swg 0 ACQh RELh swgConsistent ⟨rfl, by decide, rfl, rfl⟩ swgAcqH swgRelH
  intro x v hx hag hlo hhi
  rcases swgWrLock x v hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    revert hag hlo hhi <;> decide

theorem swgCsJ : lockCs swg 0 ACQj RELj := by
  apply lockCsIntro swg 0 ACQj RELj swgConsistent ⟨rfl, by decide, rfl, rfl⟩ swgAcqJ swgRelJ
  intro x v hx hag hlo hhi
  rcases swgWrLock x v hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    revert hag hlo hhi <;> decide

theorem swgPaired : lockPaired swg 0 := by
  intro R hR
  rcases swgWrLock R lockFree hR with ⟨rfl, hv⟩ | ⟨rfl, -⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, -⟩
  · exact absurd hv b0NeB1
  · exact ⟨ACQh, swgCsH⟩
  · exact absurd hv b0NeB1
  · exact absurd hv b0NeB1
  · exact ⟨ACQj, swgCsJ⟩

end Weak
