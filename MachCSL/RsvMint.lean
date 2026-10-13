/-
MachCSL: THE RESERVATION AT THE `PowerOn` MINT (W8-β′, plan rev 30 [R26.2-alt]).

The static regions of the fixed record (`MachFixedGS.rsvStatic`) are
reserved by the mint itself: the era's registry `rsvName` is allocated over
the whole list (`rsvRegMap`, base ↦ index: `staticIn`, `rsvExact`), and every
reserved byte's history -- the image's -- is split out of the fresh heap's
cells (`memCellsRaw_rsv_split`) into two halves, one kept by the state
interpretation (`rsvHalvesAt`), one handed to the boot client
(`rsvHalvesC`, at the exact image histories).  What is left is the heap's
cells at the other bytes (`rsvErase`).  Registered from timestamp 0, never
released.
-/
import MachCSL.Resources

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Iris.Std Std

variable {hlc : HasLC} {GF : BundledGFunctors}

/-! ## The registry's map -/

/-- Region base ↦ index, from index `i` on. -/
def rsvRegMapAux : List RsvRegion → Nat → RegMapF Agent
  | [], _ => ∅
  | R :: rs, i => insert (rsvRegMapAux rs (i + 1)) R.base.toNat i

/-- The registry the mint allocates. -/
def rsvRegMap (rs : List RsvRegion) : RegMapF Agent := rsvRegMapAux rs 0

theorem rsvRegMapAux_exact : ∀ (rs : List RsvRegion) (i k j : Nat),
    get? (rsvRegMapAux rs i) k = some j → i ≤ j ∧ ∃ R, rs[j - i]? = some R ∧ R.base.toNat = k
  | [], i, k, j, h => by simp [rsvRegMapAux, LawfulPartialMap.get?_empty] at h
  | R0 :: rs, i, k, j, h => by
    simp only [rsvRegMapAux] at h
    by_cases hk : R0.base.toNat = k
    · subst hk
      rw [LawfulPartialMap.get?_insert_eq rfl] at h
      obtain rfl := Option.some.inj h
      exact ⟨Nat.le_refl _, R0, by simp, rfl⟩
    · rw [LawfulPartialMap.get?_insert_ne hk] at h
      obtain ⟨hij, R, hR, hb⟩ := rsvRegMapAux_exact rs (i + 1) k j h
      refine ⟨by omega, R, ?_, hb⟩
      have e : j - i = (j - (i + 1)) + 1 := by omega
      rw [e, List.getElem?_cons_succ]
      exact hR

theorem rsvRegMapAux_static : ∀ (rs : List RsvRegion) (i : Nat), (rs.map (fun R => R.base.toNat)).Nodup →
    ∀ (j : Nat) (R : RsvRegion), rs[j]? = some R → get? (rsvRegMapAux rs i) R.base.toNat = some (j + i)
  | [], _, _, j, R, h => by simp at h
  | R0 :: rs, i, hnd, j, R, h => by
    simp only [rsvRegMapAux]
    rw [List.map_cons, List.nodup_cons] at hnd
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [LawfulPartialMap.get?_insert_eq rfl]
      simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hne : R0.base.toNat ≠ R.base.toNat := by
        intro he
        exact hnd.1 (he ▸ List.mem_map.2 ⟨R, List.mem_of_getElem? h, rfl⟩)
      rw [LawfulPartialMap.get?_insert_ne hne, rsvRegMapAux_static rs (i + 1) hnd.2 j R h]
      congr 1
      omega

-- `RsvRegion.base_mem` moved to `MachCSL.Reserved` (W8 (f2-ctx)).

theorem rsvBases_nodup : ∀ {rs : List RsvRegion}, (rsvBytes rs).Nodup →
    (rs.map (fun R => R.base.toNat)).Nodup
  | [], _ => List.nodup_nil
  | R0 :: rs, hnd => by
    unfold rsvBytes at hnd
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨_, hnd2, hdis⟩ := hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, rsvBases_nodup hnd2⟩
    intro hm
    obtain ⟨R, hR, hb⟩ := List.mem_map.1 hm
    have heq : R.base = R0.base := BitVec.eq_of_toNat_eq hb
    exact hdis R0.base R0.base_mem R0.base (List.mem_flatMap.2 ⟨R, hR, heq ▸ R.base_mem⟩) rfl

theorem rsvRegMap_staticIn {rs : List RsvRegion} (hnd : (rsvBytes rs).Nodup) :
    staticIn rs (rsvRegMap rs) := by
  intro i R hi
  have := rsvRegMapAux_static rs 0 (rsvBases_nodup hnd) i R hi
  simpa [rsvRegMap] using this

theorem rsvRegMap_exact (rs : List RsvRegion) : rsvExact rs (rsvRegMap rs) := by
  intro k i h
  obtain ⟨_, R, hR, hb⟩ := rsvRegMapAux_exact rs 0 k i h
  exact ⟨R, by simpa using hR, hb⟩

/-! ## The heap's cells, reserved bytes split out -/

/-- The heap map without the reserved bytes. -/
def rsvErase (rs : List RsvRegion) (m : MemF Hist) : MemF Hist :=
  (rsvBytes rs).foldl (fun m a => delete m a) m

theorem foldl_delete_get? : ∀ (l : List PAddr) (m : MemF Hist) (a : PAddr),
    get? (l.foldl (fun m b => delete m b) m) a = if a ∈ l then none else get? m a
  | [], m, a => by simp
  | b :: l, m, a => by
    simp only [List.foldl_cons]
    rw [foldl_delete_get? l (delete m b) a]
    by_cases ha : a ∈ l
    · simp [ha]
    · simp only [ha, if_false, List.mem_cons, false_or]
      by_cases hab : a = b
      · subst hab; simp [LawfulPartialMap.get?_delete_eq]
      · simp only [hab, if_false]
        exact LawfulPartialMap.get?_delete_ne (Ne.symm hab)

theorem rsvErase_get? (rs : List RsvRegion) (m : MemF Hist) (a : PAddr) :
    get? (rsvErase rs m) a = if a ∈ rsvBytes rs then none else get? m a :=
  foldl_delete_get? _ m a

-- The erased map is read through `rsvErase_get?` only.
attribute [irreducible] rsvErase

section fixed
variable [MachFixedGS hlc GF]

/-- Split a list of distinct present bytes out of a heap map's big-sep. -/
theorem bigSepM_split_list (Φ : PAddr → Hist → IProp GF) : ∀ (l : List PAddr) (m : MemF Hist), l.Nodup →
    (∀ a ∈ l, (get? m a).isSome) →
    ([∗map] a ↦ H ∈ m, Φ a H) ⊢@{IProp GF}
      ([∗map] a ↦ H ∈ l.foldl (fun m b => delete m b) m, Φ a H) ∗
      [∗list] a ∈ l, Φ a ((get? m a).getD [])
  | [], m, _, _ => by
    simp only [List.foldl_nil]
    iintro H
    iframe H
    exact BigSepL.bigSepL_nil_intro
  | a :: l, m, hnd, hin => by
    rw [List.nodup_cons] at hnd
    obtain ⟨H0, hH0⟩ := Option.isSome_iff_exists.1 (hin a List.mem_cons_self)
    refine (BigSepM.bigSepM_delete (Φ := Φ) hH0).1.trans ?_
    have hin' : ∀ b ∈ l, (get? (delete m a) b).isSome := by
      intro b hb
      have hne : b ≠ a := fun h => hnd.1 (h ▸ hb)
      rw [LawfulPartialMap.get?_delete_ne (Ne.symm hne)]
      exact hin b (List.mem_cons_of_mem _ hb)
    iintro ⟨H0, Hrest⟩
    icases bigSepM_split_list Φ l (delete m a) hnd.2 hin' $$ Hrest with ⟨Hrest, Hl⟩
    simp only [List.foldl_cons]
    iframe Hrest
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · rw [hH0, Option.getD_some]; iexact H0
    · iapply BigSepL.bigSepL_mono _ $$ Hl
      intro k b hk
      have hb : b ∈ l := List.mem_of_getElem? hk
      have hne : b ≠ a := fun h => hnd.1 (h ▸ hb)
      rw [LawfulPartialMap.get?_delete_ne (Ne.symm hne)]

/-- An era's byte cell in two halves. -/
theorem eraPointsTo_split (E : EraGS) (a : PAddr) (H : Hist) :
    pointsTo (G := E.mem) a (DFrac.own 1) H ⊢@{IProp GF}
      pointsTo (G := E.mem) a (DFrac.own (1 : Qp).half) H ∗
      pointsTo (G := E.mem) a (DFrac.own (1 : Qp).half) H := by
  unfold pointsTo
  have h := (ghost_map_elem_fractional (GF := GF) (K := PAddr) (V := Hist) (H := MemF)
    E.heapName a H).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

/-- The client's half of one region's bytes, at the histories of `m`. -/
def rsvRegionHalfC (E : EraGS) (R : RsvRegion) (m : MemF Hist) : IProp GF := iprop%
  [∗list] w ∈ R.words, [∗list] j ∈ List.range w.2,
    pointsTo (G := E.mem) (w.1 + BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half)
      ((get? m (w.1 + BitVec.ofNat 64 j)).getD [])

/-- The client's halves of the reserved bytes, at the histories of `m`. -/
def rsvHalvesC (E : EraGS) (rs : List RsvRegion) (m : MemF Hist) : IProp GF := iprop%
  [∗list] R ∈ rs, rsvRegionHalfC E R m

/-- The reserved bytes' own cells, regrouped per region and word. -/
theorem rsvBytes_bigSepL (Φ : PAddr → IProp GF) (rs : List RsvRegion) :
    ([∗list] a ∈ rsvBytes rs, Φ a) =
      [∗list] R ∈ rs, [∗list] w ∈ R.words, [∗list] j ∈ List.range w.2, Φ (w.1 + BitVec.ofNat 64 j) := by
  unfold rsvBytes RsvRegion.bytes
  rw [BigSepL.bigSepL_flatMap]
  congr 1
  funext _ R
  rw [BigSepL.bigSepL_flatMap]
  congr 1
  funext _ w
  unfold wordBytes
  rw [BigSepL.bigSepL_map]

/-- **The mint's split**: a fully owned heap map whose reserved bytes are all
present becomes the cells of the other bytes, the interpretation's halves
and the client's halves. -/
theorem memCellsRaw_rsv_split (E : EraGS) (rs : List RsvRegion) (m : MemF Hist)
    (Φ : PAddr → Hist → IProp GF)
    (hnd : (rsvBytes rs).Nodup) (hin : ∀ a ∈ rsvBytes rs, (get? m a).isSome)
    (hΦ : ∀ a ∈ rsvBytes rs, Φ a ((get? m a).getD []) ⊢ pointsTo (G := E.mem) a (DFrac.own 1) ((get? m a).getD [])) :
    ([∗map] a ↦ H ∈ m, Φ a H) ⊢@{IProp GF}
      ([∗map] a ↦ H ∈ rsvErase rs m, Φ a H) ∗
      rsvHalvesAt E rs ∗ rsvHalvesC E rs m := by
  refine (bigSepM_split_list Φ (rsvBytes rs) m hnd hin).trans ?_
  refine (sep_mono_right (BigSepL.bigSepL_mono (fun {_ a} hk => hΦ a (List.mem_of_getElem? hk)))).trans ?_
  rw [rsvBytes_bigSepL (fun a => pointsTo (G := E.mem) a (DFrac.own 1) ((get? m a).getD [])) rs]
  iintro ⟨Hrest, Hb⟩
  unfold rsvErase
  iframe Hrest
  unfold rsvHalvesAt rsvHalvesC rsvRegionHalfC
  iapply BigSepL.bigSepL_sep_eqv.1
  iapply BigSepL.bigSepL_mono _ $$ Hb
  intro _ R _
  iintro HR
  iapply BigSepL.bigSepL_sep_eqv.1
  iapply BigSepL.bigSepL_mono _ $$ HR
  intro _ w _
  iintro Hw
  ihave Hw := BigSepL.bigSepL_mono_of_forall (Ψ := fun _ (j : Nat) =>
      iprop(pointsTo (G := E.mem) (w.1 + BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half)
          ((get? m (w.1 + BitVec.ofNat 64 j)).getD []) ∗
        pointsTo (G := E.mem) (w.1 + BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half)
          ((get? m (w.1 + BitVec.ofNat 64 j)).getD [])))
    (fun {_ j} => eraPointsTo_split E _ _) $$ Hw
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hw with ⟨H1, H2⟩
  iframe H2
  unfold rsvWordHalfAt
  iexists (fun j => (get? m (w.1 + BitVec.ofNat 64 j)).getD [])
  iexact H1

end fixed

end MachCSL
