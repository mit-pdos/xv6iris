/-
MachCSL: separation-logic resources for the machine state.

- `r ↦ᵣ[cpu]{dq} v` -- hart `cpu`'s register `r` holds `v` (one `ghost_map`
  per hart, keyed by the register's constructor index, valued in the
  dependent pair `⟨r, v⟩`);
- `a ↦ₕ{dq} H`      -- physical byte `a` has write history `H` (iris-lean's
  `gen_heap` over the byte histories of `MachCSL.TsoMem`); the context-indexed
  points-to `a ↦ₘ{dq} v` of `MachCSL.Ctx` is built on it.

Eras (the Rocq prototype's generations).  The ghost state has two layers:

* the *fixed* layer (`MachFixedGS`), allocated once for the whole run: the
  generation counter (`genAuth`, with the persistent lower bounds `genBorn`
  and `genDead`), the started-generations counter (`startAuth`/`genStarted`)
  and the era *registry*, a ghost map from generation numbers to the ghost
  names of that generation's era;
* the *era* layer (`EraGS`), re-minted at every power-on: one register ghost
  map per hart, the memory heap, and the memory-model mirrors -- the top of
  the store order and each hart's data view, instruction view and read
  watermark (monotone counters, so their lower bounds are persistent
  receipts), the author log (persistent elements: "the store at timestamp
  `t` is agent `h`'s") and the reservation map (one fully owned element per
  hart).  A power loss simply abandons it.

`MachGS` is the *ambient* instance a proof is stated at: the fixed layer, one
era and its generation number.  All the register/memory resources are stated
at the ambient era; `genCert` is the persistent certificate that the ambient
generation was born, was started, and runs the ambient era.

`stateInterp` (`powerInterp`) ties the fixed ghosts to the global state and,
while the power is on, holds the current era's interpretation: every hart's
register map agrees pointwise with its register file, the memory heap is
exactly the machine's byte histories, the mirrors are at the machine's
values, and the memory-model step invariant `mmOk` holds (the Rocq
prototype's `mm_ok`/`itv_ok`/`hr_ok`/`resv_ok`).
-/
import MachCSL.Lang
import Iris.BI.Lib.GenHeap
import Iris.BI.Lib.MonoNat
import Iris.Instances.Lib.GhostMap
import Iris.Instances.Lib.GhostVar
import Iris.ProgramLogic.WeakestPre

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open LeanRV64D

/-! ## Ghost state -/

/-- Register cells carry the register together with its (dependently typed) value. -/
abbrev RegVal := (r : Register) × RegisterType r

/-- The finite-map functor used for the register ghost maps (keyed by register
index) and the era registry (keyed by generation). -/
abbrev RegMapF := fun V => Std.ExtTreeMap Nat V compare

/-- The finite-map functor of the byte memory (`Mem = MemF (BitVec 8)`). -/
abbrev MemF := fun V => Std.ExtTreeMap PAddr V compare

/-- The finite-map functor of the held-lock sets (keyed by lock name). -/
abbrev StrMapF := fun V => Std.ExtTreeMap String V compare

/-- A spinlock's state: free, or held by a hart (with whether `lk->cpu` is
set yet). -/
abbrev LockState := Option (CPU × Bool)

/-- The key of register `r` in a hart's ghost map. -/
def regIdx (r : Register) : Nat := r.ctorIdx

theorem regIdx_injective : Function.Injective regIdx := by
  intro a b h
  have := congrArg Register.ofNat h
  simpa [regIdx, Register.ofNat_ctorIdx] using this

/-- The reservation map's values: a hart's reservation and its pending
acquire bit. -/
abbrev ResvVal := Option Resv × Bool

/-- One era's ghost names: a register map per hart, the memory heap, and the
memory-model mirrors. -/
structure EraGS (GF : BundledGFunctors) where
  regName : CPU → GName
  mem : genHeapGS PAddr Hist GF MemF
  /-- each hart's data view (floor), a monotone counter -/
  viewName : CPU → GName
  /-- each hart's instruction view, a monotone counter -/
  iviewName : CPU → GName
  /-- each hart's read watermark, a monotone counter -/
  rviewName : CPU → GName
  /-- the top of the store order, a monotone counter -/
  topName : GName
  /-- the author log: timestamp ↦ author, persistent elements -/
  authName : GName
  /-- the reservation map: hart ↦ (reservation, acquire bit), owned elements -/
  resvName : GName
  /-- each hart's held-lock set (an authority; each held lock's invariant
  keeps the matching element) -/
  lockSetName : CPU → GName

/-- The functors the machine needs (for adequacy: what a `BundledGFunctors`
must contain). -/
class MachGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGpreS GF where
  reg_pre : GhostMapG GF Nat RegVal RegMapF
  mem_pre : genHeapPreS PAddr Hist GF MemF
  mono_pre : MonoNatG GF
  registry_pre : GhostMapG GF Nat (EraGS GF) RegMapF
  auth_pre : GhostMapG GF Nat Agent RegMapF
  resv_pre : GhostMapG GF Nat ResvVal RegMapF
  dirty_pre : GhostMapG GF Nat CPU RegMapF
  lockset_pre : GhostMapG GF String Unit StrMapF
  lock_pre : GhostVarG GF (LockState × Nat)

attribute [reducible, instance] MachGpreS.reg_pre
attribute [reducible, instance] MachGpreS.mem_pre
attribute [reducible, instance] MachGpreS.mono_pre
attribute [reducible, instance] MachGpreS.registry_pre
attribute [reducible, instance] MachGpreS.auth_pre
attribute [reducible, instance] MachGpreS.resv_pre
attribute [reducible, instance] MachGpreS.dirty_pre
attribute [reducible, instance] MachGpreS.lockset_pre
attribute [reducible, instance] MachGpreS.lock_pre

/-- The fixed layer: allocated once, survives every power cycle. -/
class MachFixedGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  -- not an instance on purpose to avoid diamonds with IrisGS_gen
  [invGS : InvGS_gen hlc GF]
  reg : GhostMapG GF Nat RegVal RegMapF
  memPre : genHeapPreS PAddr Hist GF MemF
  mono : MonoNatG GF
  registry : GhostMapG GF Nat (EraGS GF) RegMapF
  /-- the author log's functor -/
  authG : GhostMapG GF Nat Agent RegMapF
  /-- the reservation map's functor -/
  resvG : GhostMapG GF Nat ResvVal RegMapF
  /-- the contexts' dirty sets' functor (`MachCSL.Ctx`): timestamp ↦ the hart
  that authored the store -/
  dirtyG : GhostMapG GF Nat CPU RegMapF
  /-- the held-lock sets' functor -/
  lockSetG : GhostMapG GF String Unit StrMapF
  /-- the spinlock state ghost variables' functor (`MachCSL.Lock`) -/
  lockG : GhostVarG GF (LockState × Nat)
  /-- the generation counter -/
  genName : GName
  /-- the started-generations counter -/
  startName : GName
  /-- the era registry: generation ↦ its era's ghost names -/
  registryName : GName

attribute [reducible, instance] MachFixedGS.reg
attribute [reducible, instance] MachFixedGS.memPre
attribute [reducible, instance] MachFixedGS.mono
attribute [reducible, instance] MachFixedGS.registry
attribute [reducible, instance] MachFixedGS.authG
attribute [reducible, instance] MachFixedGS.resvG
attribute [reducible, instance] MachFixedGS.dirtyG
attribute [reducible, instance] MachFixedGS.lockSetG
attribute [reducible, instance] MachFixedGS.lockG

/-- The ambient instance: the fixed layer, one era (its register names and
memory heap, spelled out as fields so the heap can be an instance), and the
era's generation. -/
class MachGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [fixed : MachFixedGS hlc GF]
  /-- the register-map ghost name of each hart -/
  regName : CPU → GName
  /-- the memory heap -/
  mem : genHeapGS PAddr Hist GF MemF
  viewName : CPU → GName
  iviewName : CPU → GName
  rviewName : CPU → GName
  topName : GName
  authName : GName
  resvName : GName
  lockSetName : CPU → GName
  gen : Nat

attribute [reducible, instance] MachGS.fixed
attribute [reducible, instance] MachGS.mem

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The ambient era. -/
@[reducible] def MachGS.era [MachGS hlc GF] : EraGS GF :=
  ⟨MachGS.regName (hlc := hlc) (GF := GF), MachGS.mem (hlc := hlc) (GF := GF),
   MachGS.viewName (hlc := hlc) (GF := GF), MachGS.iviewName (hlc := hlc) (GF := GF),
   MachGS.rviewName (hlc := hlc) (GF := GF), MachGS.topName (hlc := hlc) (GF := GF),
   MachGS.authName (hlc := hlc) (GF := GF), MachGS.resvName (hlc := hlc) (GF := GF),
   MachGS.lockSetName (hlc := hlc) (GF := GF)⟩

/-- The register-map ghost name of hart `cpu` in the ambient era. -/
def regName [MachGS hlc GF] (cpu : CPU) : GName := MachGS.regName (hlc := hlc) (GF := GF) cpu

/-- The ambient generation. -/
def genId [MachGS hlc GF] : Nat := MachGS.gen (hlc := hlc) (GF := GF)

/-! ## Register points-to -/

/-- Register `r` holds `v`, in the register map named `γ`. -/
def regPointsToAt [MachFixedGS hlc GF] (γ : GName) (r : Register) (dq : DFrac)
    (v : RegisterType r) : IProp GF :=
  ghost_map_elem γ dq (regIdx r) (⟨r, v⟩ : RegVal)

/-- Hart `cpu`'s register `r` holds `v` (in the ambient era). -/
def regPointsTo [MachGS hlc GF] (cpu : CPU) (r : Register) (dq : DFrac) (v : RegisterType r) :
    IProp GF :=
  regPointsToAt (regName (hlc := hlc) (GF := GF) cpu) r dq v

notation:50 r:50 " ↦ᵣ[" cpu "]{" dq "} " v:50 => regPointsTo cpu r dq v
notation:50 r:50 " ↦ᵣ[" cpu "] " v:50 => regPointsTo cpu r (DFrac.own 1) v
notation:50 r:50 " ↦ᵣ[" cpu "]□ " v:50 => regPointsTo cpu r DFrac.discard v

/-- History points-to: iris-lean's `gen_heap` `↦` over the byte histories,
spelled `↦ₕ`.  The raw fact under every memory resource of `MachCSL.Ctx`. -/
notation:50 a:50 " ↦ₕ{" dq "} " hs:50 => pointsTo (L := PAddr) (V := Hist) (H := MemF) a dq hs
notation:50 a:50 " ↦ₕ " hs:50 => pointsTo (L := PAddr) (V := Hist) (H := MemF) a (DFrac.own 1) hs
notation:50 a:50 " ↦ₕ□ " hs:50 => pointsTo (L := PAddr) (V := Hist) (H := MemF) a DFrac.discard hs

/-! ## Era interpretation -/

/-- The register ghost map `m` agrees with the register file `f`. -/
def regAgree (m : RegMapF RegVal) (f : RegFile) : Prop :=
  ∀ r : Register, get? m (regIdx r) = some ⟨r, f r⟩

/-- One hart's register interpretation, at the register map named `γ`. -/
def regInterpAt [MachFixedGS hlc GF] (γ : GName) (f : RegFile) : IProp GF := iprop%
  ∃ m : RegMapF RegVal, (γ ↪●MAP m) ∗ ⌜regAgree m f⌝

/-- One hart's register interpretation, in the ambient era. -/
def regInterp [MachGS hlc GF] (cpu : CPU) (f : RegFile) : IProp GF :=
  regInterpAt (regName (hlc := hlc) (GF := GF) cpu) f

/-! ## The memory-model mirrors -/

/-- `authMapAux l b`: the author log `l` as a map, timestamp `b + i + 1` ↦
`l[i]`. -/
def authMapAux : List Agent → Nat → RegMapF Agent
  | [], _ => ∅
  | a :: l, b => insert (authMapAux l (b + 1)) (b + 1) a

/-- The author log as a map: timestamp ↦ author. -/
def authMap (log : List Agent) : RegMapF Agent := authMapAux log 0

theorem authMapAux_get? : ∀ (l : List Agent) (b t : Nat),
    get? (authMapAux l b) t = if b < t ∧ t ≤ b + l.length then l[t - b - 1]? else none
  | [], b, t => by
    simp only [authMapAux, List.length_nil, Nat.add_zero]
    rw [if_neg (by omega)]
    rfl
  | a :: l, b, t => by
    simp only [authMapAux, List.length_cons]
    by_cases h : t = b + 1
    · subst h
      rw [LawfulPartialMap.get?_insert_eq rfl, if_pos (by omega)]
      simp
    · rw [LawfulPartialMap.get?_insert_ne (Ne.symm h), authMapAux_get? l (b + 1) t]
      by_cases h1 : b + 1 < t ∧ t ≤ b + 1 + l.length
      · rw [if_pos h1, if_pos (by omega)]
        have : t - b - 1 = (t - (b + 1) - 1) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
      · rw [if_neg h1, if_neg (by omega)]

theorem authMap_get? (log : List Agent) (t : Nat) :
    get? (authMap log) t = if 1 ≤ t ∧ t ≤ log.length then log[t - 1]? else none := by
  unfold authMap
  rw [authMapAux_get?]
  simp only [Nat.zero_add, Nat.sub_zero]
  by_cases h : 1 ≤ t ∧ t ≤ log.length
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem authMap_snoc (log : List Agent) (h : Agent) :
    authMap (log ++ [h]) = insert (authMap log) (log.length + 1) h := by
  apply LawfulPartialMap.equiv_iff_eq.mp
  intro t
  rw [authMap_get?]
  by_cases ht : t = log.length + 1
  · subst ht
    rw [LawfulPartialMap.get?_insert_eq rfl, if_pos (by simp)]
    simp
  · rw [LawfulPartialMap.get?_insert_ne (Ne.symm ht), authMap_get?]
    simp only [List.length_append, List.length_singleton]
    by_cases h1 : 1 ≤ t ∧ t ≤ log.length
    · rw [if_pos (by omega), if_pos h1]
      rw [List.getElem?_append_left (by omega)]
    · rw [if_neg (by omega), if_neg h1]

theorem authMap_nil : authMap [] = (∅ : RegMapF Agent) := rfl

/-- `resvMapAux σ k`: the reservation map of the harts below `k`. -/
def resvMapAux (σ : MState) : Nat → RegMapF ResvVal
  | 0 => ∅
  | k + 1 =>
    if h : k < NCPU then insert (resvMapAux σ k) k (σ.resv ⟨k, h⟩, (σ.hr ⟨k, h⟩).acq)
    else resvMapAux σ k

/-- The reservation map: hart ↦ (its reservation, its pending acquire bit). -/
def resvMap (σ : MState) : RegMapF ResvVal := resvMapAux σ NCPU

theorem resvMapAux_get? (σ : MState) : ∀ (k j : Nat),
    get? (resvMapAux σ k) j =
      if h : j < k ∧ j < NCPU then some (σ.resv ⟨j, h.2⟩, (σ.hr ⟨j, h.2⟩).acq) else none
  | 0, j => by
    simp only [resvMapAux]
    rw [dif_neg (by omega)]
    rfl
  | k + 1, j => by
    simp only [resvMapAux]
    split
    · by_cases hj : j = k
      · subst hj
        rw [LawfulPartialMap.get?_insert_eq rfl, dif_pos ⟨by omega, by assumption⟩]
      · rw [LawfulPartialMap.get?_insert_ne (Ne.symm hj), resvMapAux_get? σ k j]
        by_cases h1 : j < k ∧ j < NCPU
        · rw [dif_pos h1, dif_pos ⟨by omega, h1.2⟩]
        · rw [dif_neg h1, dif_neg (by omega)]
    · rw [resvMapAux_get? σ k j]
      by_cases h1 : j < k ∧ j < NCPU
      · rw [dif_pos h1, dif_pos ⟨by omega, h1.2⟩]
      · rw [dif_neg h1, dif_neg (by omega)]

theorem resvMap_get? (σ : MState) (c : CPU) :
    get? (resvMap σ) c.val = some (σ.resv c, (σ.hr c).acq) := by
  unfold resvMap
  rw [resvMapAux_get?, dif_pos ⟨c.isLt, c.isLt⟩]

theorem resvMap_get?_ge (σ : MState) (j : Nat) (h : NCPU ≤ j) : get? (resvMap σ) j = none := by
  unfold resvMap
  rw [resvMapAux_get?, dif_neg (by omega)]

/-- Two states with the same reservations and acquire bits have the same map. -/
theorem resvMap_congr (σ σ' : MState) (h : ∀ c, σ'.resv c = σ.resv c ∧ (σ'.hr c).acq = (σ.hr c).acq) :
    resvMap σ' = resvMap σ := by
  apply LawfulPartialMap.equiv_iff_eq.mp
  intro j
  by_cases hj : j < NCPU
  · have := resvMap_get? σ ⟨j, hj⟩
    have := resvMap_get? σ' ⟨j, hj⟩
    simp_all
  · rw [resvMap_get?_ge σ j (by omega), resvMap_get?_ge σ' j (by omega)]

/-- Updating one hart's entry. -/
theorem resvMap_upd (σ σ' : MState) (cpu : CPU) (r : Option Resv) (b : Bool)
    (hc : σ'.resv cpu = r ∧ (σ'.hr cpu).acq = b)
    (h : ∀ c, c ≠ cpu → σ'.resv c = σ.resv c ∧ (σ'.hr c).acq = (σ.hr c).acq) :
    resvMap σ' = insert (resvMap σ) cpu.val (r, b) := by
  apply LawfulPartialMap.equiv_iff_eq.mp
  intro j
  by_cases hj : j = cpu.val
  · subst hj
    rw [LawfulPartialMap.get?_insert_eq rfl, resvMap_get?, hc.1, hc.2]
  · rw [LawfulPartialMap.get?_insert_ne (Ne.symm hj)]
    by_cases hlt : j < NCPU
    · have hne : (⟨j, hlt⟩ : CPU) ≠ cpu := fun heq => hj (congrArg Fin.val heq)
      rw [resvMap_get? σ ⟨j, hlt⟩, resvMap_get? σ' ⟨j, hlt⟩, (h _ hne).1, (h _ hne).2]
    · rw [resvMap_get?_ge σ j (by omega), resvMap_get?_ge σ' j (by omega)]

/-- The memory-model step invariant (the Rocq prototype's `mm_ok`, `itv_ok`,
`hr_ok` and `resv_ok`): every history is well formed against the author log,
every view and read-side position is at or below the top, and every
outstanding reservation still agrees with the top of memory. -/
def mmOk (σ : MState) : Prop :=
  (∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H → histOk σ.log H) ∧
  (∀ c, σ.tv c ≤ σ.top ∧ σ.itv c ≤ σ.top ∧ (σ.hr c).bound σ.top) ∧
  (∀ c r, σ.resv c = some r → ∀ (a : PAddr) (v : BitVec 8), r[a]? = some v →
    (σ.mem[a]?).bind Hist.top = some v)

theorem mmOk_afterLoad (σ : MState) (cpu : CPU) (pa : PAddr) (n tvn : Nat) (htv : tvn ≤ σ.top)
    (h : mmOk σ) : mmOk (σ.afterLoad cpu pa n tvn) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun c => ?_, h3⟩
  obtain ⟨a1, a2, a3, a4⟩ := h2 c
  simp only [MState.top] at *
  by_cases hc : c = cpu
  · subst hc
    simp only [MState.afterLoad, updCpu, if_true]
    refine ⟨a1, a2, ?_, ?_⟩
    · simp only [HRead.afterLoad]; omega
    · intro a
      simp only [HRead.afterLoad]
      split
      · exact htv
      · exact a4 a
  · simp only [MState.afterLoad, updCpu, hc, if_false]
    exact ⟨a1, a2, a3, a4⟩

theorem mmOk_fence (σ : MState) (cpu : CPU) (b : barrier_kind) (h : mmOk σ) : mmOk (σ.fence cpu b) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun c => ?_, h3⟩
  obtain ⟨a1, a2, a3, a4⟩ := h2 c
  obtain ⟨b1, b2, b3, b4⟩ := h2 cpu
  have hpub := ownPub_le (hartAgent cpu) σ.log
  simp only [MState.top] at *
  by_cases hc : c = cpu
  · subst hc
    simp only [MState.fence, updCpu, if_true]
    refine ⟨fencePost_le _ _ _ _ _ _ b1 b3 hpub, ?_, a3, a4⟩
    split
    · exact Nat.max_le.2 ⟨b2, fencePost_le _ _ _ _ _ _ b1 b3 hpub⟩
    · exact b2
  · simp only [MState.fence, updCpu, hc, if_false]
    exact ⟨a1, a2, a3, a4⟩

theorem mmOk_store (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (excl : Bool)
    (hno : ¬ othersReserve σ.resv cpu pa n) (h : mmOk σ) : mmOk (σ.store cpu pa n w excl) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a H hget
    exact FlatMem.writeBytes_histOk σ.mem σ.log pa w (hartAgent cpu) h1 a H hget
  · intro c
    obtain ⟨a1, a2, a3, a4⟩ := h2 c
    simp only [MState.top] at *
    by_cases hc : c = cpu
    · subst hc
      simp only [MState.store, updCpu, if_true, List.length_append, List.length_singleton]
      refine ⟨?_, by omega, ?_, ?_⟩
      · split <;> omega
      · simp only [HRead.clearAcq]; omega
      · intro a; simp only [HRead.clearAcq]; have := a4 a; omega
    · simp only [MState.store, updCpu, hc, if_false, List.length_append, List.length_singleton]
      exact ⟨by omega, by omega, by omega, fun a => by have := a4 a; omega⟩
  · intro c r hr a v hav
    simp only [MState.store, updCpu] at hr ⊢
    by_cases hc : c = cpu
    · subst hc
      simp at hr
    · simp only [hc, if_false] at hr
      have hno' : ∀ j, j < n → a ≠ pa + BitVec.ofNat 64 j := by
        intro j hj heq
        apply hno
        refine ⟨c, hc, r, hr, j, hj, ?_⟩
        rw [← heq, hav]; rfl
      rw [FlatMem.writeBytes_get?_notin _ _ _ _ _ _ hno']
      exact h3 c r hr a v hav

/-- A booted machine satisfies the step invariant. -/
theorem mmOk_boot (σ : MState) (image : Mem) (h : bootFacts σ image) : mmOk σ := by
  obtain ⟨hmem, hlog, hhart, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a H hget
    rw [hmem, imgFlat_get?] at hget
    cases hi : image[a]? with
    | none => rw [hi] at hget; simp at hget
    | some v =>
      rw [hi] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      subst hget
      refine ⟨List.pairwise_singleton _ _, fun e he => ?_⟩
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨Nat.zero_le _, Or.inl rfl⟩
  · intro c
    obtain ⟨h1, h2, h3, _⟩ := hhart c
    rw [h1, h2, h3]
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ => Nat.zero_le _⟩
  · intro c r hr
    rw [(hhart c).2.2.2] at hr
    cases hr

/-- Hart `cpu`'s view mirrors at the machine `σ`: data view, instruction
view, read watermark. -/
def hartViewsAt [MachFixedGS hlc GF] (E : EraGS GF) (σ : MState) (cpu : CPU) : IProp GF := iprop%
  MonoNat.auth_own (E.viewName cpu) (DFrac.own 1) (.ofNat (σ.tv cpu)) ∗
  MonoNat.auth_own (E.iviewName cpu) (DFrac.own 1) (.ofNat (σ.itv cpu)) ∗
  MonoNat.auth_own (E.rviewName cpu) (DFrac.own 1) (.ofNat (σ.hr cpu).rv)

theorem hartViewsAt_cases [MachFixedGS hlc GF] (E : EraGS GF) (σ : MState) (cpu : CPU) :
    hartViewsAt E σ cpu ⊢@{IProp GF}
      MonoNat.auth_own (E.viewName cpu) (DFrac.own 1) (.ofNat (σ.tv cpu)) ∗
      MonoNat.auth_own (E.iviewName cpu) (DFrac.own 1) (.ofNat (σ.itv cpu)) ∗
      MonoNat.auth_own (E.rviewName cpu) (DFrac.own 1) (.ofNat (σ.hr cpu).rv) := by
  unfold hartViewsAt; iintro H; iexact H

theorem hartViewsAt_intro [MachFixedGS hlc GF] (E : EraGS GF) (σ : MState) (cpu : CPU) :
    MonoNat.auth_own (E.viewName cpu) (DFrac.own 1) (.ofNat (σ.tv cpu)) ∗
      MonoNat.auth_own (E.iviewName cpu) (DFrac.own 1) (.ofNat (σ.itv cpu)) ∗
      MonoNat.auth_own (E.rviewName cpu) (DFrac.own 1) (.ofNat (σ.hr cpu).rv) ⊢@{IProp GF}
    hartViewsAt E σ cpu := by
  unfold hartViewsAt; iintro H; iexact H

/-- Era `E`'s memory-model mirrors at the machine `σ`. -/
def memModelAt [MachFixedGS hlc GF] (E : EraGS GF) (σ : MState) : IProp GF := iprop%
  MonoNat.auth_own E.topName (DFrac.own 1) (.ofNat σ.top) ∗
  (E.authName ↪●MAP authMap σ.log) ∗
  ([∗list] cpu ∈ cpus, hartViewsAt E σ cpu) ∗
  (E.resvName ↪●MAP resvMap σ) ∗
  ⌜mmOk σ⌝

/-- `cpus` lists every hart at its own index. -/
theorem cpus_get? (cpu : CPU) : cpus[cpu.val]? = some cpu := by
  simp [cpus, cpu.isLt]; exact Fin.ext rfl

theorem cpus_get?_ne {k : Nat} {y : CPU} (hk : cpus[k]? = some y) (cpu : CPU) (hne : k ≠ cpu.val) :
    y ≠ cpu := by
  rintro rfl
  apply hne
  simp only [cpus] at hk
  rw [List.getElem?_eq_some_iff] at hk
  obtain ⟨hlt, heq⟩ := hk
  have := congrArg Fin.val heq
  simp at this
  omega

/-- Era `E`'s interpretation of the machine `σ`. -/
def eraInterp [MachFixedGS hlc GF] (E : EraGS GF) (σ : MState) : IProp GF := iprop%
  ([∗list] cpu ∈ cpus, regInterpAt (E.regName cpu) (σ.regs cpu)) ∗
  genHeapInterp (G := E.mem) σ.mem ∗
  memModelAt E σ

/-! ## The generation ghosts -/

section fixed
variable [MachFixedGS hlc GF]

/-- The generation counter, pinned to the state's `gen`. -/
def genAuth (n : Nat) : IProp GF :=
  MonoNat.auth_own (MachFixedGS.genName (hlc := hlc) (GF := GF)) (DFrac.own 1) (.ofNat n)

/-- Generation `gen` has been reached (persistent): the birth certificate. -/
def genBorn (gen : Nat) : IProp GF :=
  MonoNat.lb_own (MachFixedGS.genName (hlc := hlc) (GF := GF)) (.ofNat gen)

/-- Generation `gen` has passed (persistent): the death certificate.
`PowerOff` bumps the counter, so a generation once passed is dead forever. -/
def genDead (gen : Nat) : IProp GF :=
  MonoNat.lb_own (MachFixedGS.genName (hlc := hlc) (GF := GF)) (.ofNat (gen + 1))

/-- How many generations have been started: the current one counts once it
is powered on. -/
def startCount (g : GState) : Nat := g.gen + (if g.pow then 1 else 0)

/-- The started-generations counter, pinned to `startCount`. -/
def startAuth (n : Nat) : IProp GF :=
  MonoNat.auth_own (MachFixedGS.startName (hlc := hlc) (GF := GF)) (DFrac.own 1) (.ofNat n)

/-- Generation `gen`'s `PowerOn` has happened (persistent). -/
def genStarted (gen : Nat) : IProp GF :=
  MonoNat.lb_own (MachFixedGS.startName (hlc := hlc) (GF := GF)) (.ofNat (gen + 1))

/-- Generation `gen` runs era `E` (persistent registry element). -/
def eraRegistered (gen : Nat) (E : EraGS GF) : IProp GF :=
  ghost_map_elem (MachFixedGS.registryName (hlc := hlc) (GF := GF)) DFrac.discard gen E

/-- The certificate a generation-`gen` thread of era `E` carries: born,
started, and registered.  Persistent. -/
def genCertAt (gen : Nat) (E : EraGS GF) : IProp GF := iprop%
  genBorn gen ∗ genStarted gen ∗ eraRegistered gen E

instance (gen : Nat) : Persistent (PROP := IProp GF) (genBorn gen) := by
  unfold genBorn; infer_instance
instance (gen : Nat) : Persistent (PROP := IProp GF) (genDead gen) := by
  unfold genDead; infer_instance
instance (gen : Nat) : Persistent (PROP := IProp GF) (genStarted gen) := by
  unfold genStarted; infer_instance
instance (gen : Nat) (E : EraGS GF) : Persistent (PROP := IProp GF) (eraRegistered gen E) := by
  unfold eraRegistered; infer_instance
instance (gen : Nat) (E : EraGS GF) : Persistent (PROP := IProp GF) (genCertAt gen E) := by
  unfold genCertAt; infer_instance

/-- The registry holds exactly the started generations. -/
def registryOk (R : RegMapF (EraGS GF)) (n : Nat) : Prop :=
  ∀ k, (get? R k).isSome ↔ k < n

/-- The current era's interpretation, present exactly while the power is on. -/
def eraCur (R : RegMapF (EraGS GF)) (g : GState) : IProp GF :=
  match g.pow with
  | true => iprop(∃ E, ⌜get? R g.gen = some E⌝ ∗ eraInterp E g.m)
  | false => iprop(True)

/-- The state interpretation: the fixed ghosts pinned to the state, and the
current era's interpretation while powered. -/
def powerInterp (g : GState) : IProp GF := iprop%
  genAuth g.gen ∗ startAuth (startCount g) ∗
  ∃ R : RegMapF (EraGS GF),
    (MachFixedGS.registryName (hlc := hlc) (GF := GF) ↪●MAP R) ∗ ⌜registryOk R (startCount g)⌝ ∗
    eraCur R g

instance : StateInterp GState Obs GF where
  stateInterp g _ _ _ := powerInterp g

theorem stateInterp_eq (g : GState) (ns : Nat) (κs : List Obs) (nt : Nat) :
    stateInterp (GF := GF) g ns κs nt = powerInterp g := rfl

instance instIrisGS : IrisGS_gen hlc Expr GF where
  invGS := MachFixedGS.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    let := @MachFixedGS.invGS hlc GF _
    iintro $

/-! ### Facts the counters give against their certificates -/

theorem genAuth_born (n gen : Nat) : ⊢@{IProp GF} genAuth n -∗ genBorn gen -∗ ⌜gen ≤ n⌝ := by
  unfold genAuth genBorn
  iintro Ha Hb
  ihave %H := MonoNat.auth_lb_own_valid $$ Ha Hb
  ipureintro
  have := H.2
  simpa [MaxNat.le_toNat] using this

theorem genAuth_dead (n gen : Nat) : ⊢@{IProp GF} genAuth n -∗ genDead gen -∗ ⌜gen < n⌝ := by
  unfold genAuth genDead
  iintro Ha Hb
  ihave %H := MonoNat.auth_lb_own_valid $$ Ha Hb
  ipureintro
  have := H.2
  simp only [MaxNat.le_toNat] at this
  omega

theorem startAuth_started (n gen : Nat) :
    ⊢@{IProp GF} startAuth n -∗ genStarted gen -∗ ⌜gen < n⌝ := by
  unfold startAuth genStarted
  iintro Ha Hb
  ihave %H := MonoNat.auth_lb_own_valid $$ Ha Hb
  ipureintro
  have := H.2
  simp only [MaxNat.le_toNat] at this
  omega

/-- The registry pins the era a generation runs. -/
theorem eraRegistered_lookup (R : RegMapF (EraGS GF)) (gen : Nat) (E : EraGS GF) :
    ⊢@{IProp GF} (MachFixedGS.registryName (hlc := hlc) (GF := GF) ↪●MAP R) -∗
      eraRegistered gen E -∗ ⌜get? R gen = some E⌝ := by
  unfold eraRegistered
  iintro HR HE
  ihave %H := ghost_map_lookup $$ HR HE
  ipureintro
  exact H

/-- A generation below the counter is dead. -/
theorem genAuth_get_dead (n gen : Nat) (h : gen < n) : genAuth n ⊢@{IProp GF} genDead gen := by
  unfold genAuth genDead
  iintro Ha
  ihave #Hlb := MonoNat.lb_own_get $$ Ha
  iapply MonoNat.lb_own_le _ _ _ (by simp only [MaxNat.le_toNat]; omega) $$ Hlb

/-- `PowerOff` bumps the generation. -/
theorem genAuth_bump (n : Nat) : genAuth n ⊢@{IProp GF} |==> genAuth (n + 1) := by
  unfold genAuth
  iintro Ha
  imod MonoNat.own_update _ (.ofNat n) (.ofNat (n + 1)) (by simp only [MaxNat.le_toNat]; omega)
    $$ Ha with ⟨Ha, _⟩
  imodintro
  iexact Ha

/-- `PowerOn` starts generation `n`: bump the counter and keep the certificate. -/
theorem startAuth_bump (n : Nat) :
    startAuth n ⊢@{IProp GF} |==> (startAuth (n + 1) ∗ genStarted n) := by
  unfold startAuth genStarted
  iintro Ha
  imod MonoNat.own_update _ (.ofNat n) (.ofNat (n + 1)) (by simp only [MaxNat.le_toNat]; omega)
    $$ Ha with ⟨Ha, Hlb⟩
  imodintro
  iframe Ha Hlb

/-- `PowerOn` registers the new era. -/
theorem registry_insert (R : RegMapF (EraGS GF)) (gen : Nat) (E : EraGS GF)
    (h : get? R gen = none) :
    (MachFixedGS.registryName (hlc := hlc) (GF := GF) ↪●MAP R) ⊢@{IProp GF}
      |==> ((MachFixedGS.registryName (hlc := hlc) (GF := GF) ↪●MAP insert R gen E) ∗
        eraRegistered gen E) := by
  unfold eraRegistered
  iintro HR
  imod ghost_map_insert_persist gen E h $$ HR with ⟨HR, HE⟩
  imodintro
  iframe HR HE

/-- The current generation is born. -/
theorem genAuth_get_born (n : Nat) : genAuth n ⊢@{IProp GF} genBorn n := by
  unfold genAuth genBorn
  iintro Ha
  iapply MonoNat.lb_own_get $$ Ha

end fixed

/-- The ambient generation's certificate. -/
def genCert [MachGS hlc GF] : IProp GF :=
  genCertAt (genId (hlc := hlc) (GF := GF)) (MachGS.era (hlc := hlc) (GF := GF))

instance [MachGS hlc GF] : Persistent (PROP := IProp GF) genCert := by
  unfold genCert; infer_instance

theorem genCert_parts [MachGS hlc GF] :
    genCert ⊢@{IProp GF}
      genBorn (genId (hlc := hlc) (GF := GF)) ∗ genStarted (genId (hlc := hlc) (GF := GF)) ∗
      eraRegistered (genId (hlc := hlc) (GF := GF)) (MachGS.era (hlc := hlc) (GF := GF)) := by
  unfold genCert genCertAt
  iintro H
  iexact H

/-! ## Bridge lemmas: ghost state vs. machine state -/

theorem regVal_inj {r : Register} {v w : RegisterType r}
    (h : (⟨r, v⟩ : RegVal) = ⟨r, w⟩) : v = w := by
  cases h; rfl

section fixed
variable [MachFixedGS hlc GF]

/-- Reading: a register cell pins the register file's value. -/
theorem reg_valid_at (γ : GName) (f : RegFile) (r : Register) (dq : DFrac) (v : RegisterType r) :
    regInterpAt γ f ∗ regPointsToAt γ r dq v ⊢@{IProp GF} ⌜f r = v⌝ := by
  unfold regInterpAt regPointsToAt
  iintro ⟨⟨%m, Hauth, %Hag⟩, Hr⟩
  ihave %Hlook := ghost_map_lookup $$ Hauth Hr
  ipureintro
  have := Hag r
  rw [Hlook] at this
  exact (regVal_inj (Option.some.inj this)).symm

/-- Writing: update a fully owned cell together with the register file. -/
theorem reg_update_at (γ : GName) (f : RegFile) (r : Register) (v w : RegisterType r) :
    regInterpAt γ f ∗ regPointsToAt γ r (DFrac.own 1) v ⊢@{IProp GF}
      |==> (regInterpAt γ (f.set r w) ∗ regPointsToAt γ r (DFrac.own 1) w) := by
  unfold regInterpAt regPointsToAt
  iintro ⟨⟨%m, Hauth, %Hag⟩, Hr⟩
  imod ghost_map_update (⟨r, w⟩ : RegVal) $$ Hauth Hr with ⟨Hauth, Hr⟩
  imodintro
  iframe Hr
  iexists _
  iframe Hauth
  ipureintro
  intro r'
  by_cases h : r' = r
  · subst h
    simp [LawfulPartialMap.get?_insert_eq]
  · rw [LawfulPartialMap.get?_insert_ne (fun h' => h (regIdx_injective h').symm)]
    rw [Hag r', RegFile.set_other _ _ _ _ h]

end fixed

section ambient
variable [MachGS hlc GF]

theorem reg_valid (cpu : CPU) (f : RegFile) (r : Register) (dq : DFrac) (v : RegisterType r) :
    regInterp cpu f ∗ r ↦ᵣ[cpu]{dq} v ⊢@{IProp GF} ⌜f r = v⌝ := by
  unfold regInterp regPointsTo
  exact reg_valid_at _ f r dq v

theorem reg_update (cpu : CPU) (f : RegFile) (r : Register) (v w : RegisterType r) :
    regInterp cpu f ∗ r ↦ᵣ[cpu] v ⊢@{IProp GF}
      |==> (regInterp cpu (f.set r w) ∗ r ↦ᵣ[cpu] w) := by
  unfold regInterp regPointsTo
  exact reg_update_at _ f r v w

end ambient

end MachCSL
