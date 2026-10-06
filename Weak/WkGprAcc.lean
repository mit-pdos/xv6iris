/-
Weak: **the two-cell register-file accessor** (M4 batch 4).

Rocq: `iris/WkGprAcc.v` @ xxvzwolszwmp (1cc222280).

Rocq header (verbatim, Rocq vocabulary):

    WkGprAcc.v — the TWO-CELL [gpr_file] accessor (M4 batch 4)

    [WpGpr.gpr_file_lookup_acc]/[gpr_file_insert_acc] extract ONE register
    cell; a whole-function chain that feeds a CELL-based leaf taking two GPR
    cells at once (the c.sdsp/c.ldsp memory leaves: base [sp] plus the
    data/destination register) needs both out simultaneously, and the
    single-cell wand cannot be iterated (the remainder is not exposed as a
    file).  This is the two-key accessor, proved once over [rf_to_gmap]'s
    map algebra.  The wand takes both cells back at ARBITRARY values, so it
    serves read-read (c.sdsp: apply at the unchanged values) and read-write
    (c.ldsp: apply at the reloaded destination) sites alike.

    New file rather than a [WpGpr.v] edit: the batch-4 units are new-files-
    only (concurrent agents build against the existing [.vo] tree).

**Deviations from Rocq.**

1. Retargeted at Lean's register file (`MachCSL.gprFile cpu m`, a big separating conjunction over
   `gprIdxs = [x1 .. x31]` of full cells `gpr cpu i (DFrac.own 1) (m i)`; Rocq: `gpr_file f` over
   `rf_to_gmap f` with cells `gpr_pt i (f i)`).  The register map is `RegMap` (Rocq `regfile`),
   update is `RegMap.set` (Rocq `<[i := _]>` on the map), and Lean's `gprFile_acc` likewise.
2. Two extra premises `i ≠ 0#5`, `j ≠ 0#5`: Lean's file does not own `x0` (Rocq's `rf_to_gmap`
   domain is the regidx type itself).  Every consumer names `sp`/`ra`/data registers.
3. The proof goes through iris-lean's `bigSepL_delete_cond` twice (Rocq: `big_sepM_delete` twice
   over the map, then `big_sepM_insert` twice).

**Drift:** Rocq 08-09 `WpGpr.gpr_file` → Lean `MachCSL.gprFile` (`MachCSL/KCtx.lean`).

**Name map** (Rocq → Lean): `gpr_file_acc_2`→`gprFile_acc_2` (the tree's `gprFile_acc` spelling).

**Not ported:** none.  (`Print Assumptions` ↦ the CI axiom audit.)

**Statements checked** (by hand against Rocq): `gprFile_acc_2`.
-/
import MachCSL.KCtx

namespace Weak

open Iris Iris.BI Iris.ProofMode MachCSL

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- Register `i ≠ x0` sits at slot `i.toNat - 1` of the file's index list. -/
theorem gprIdxs_slot (i : BitVec 5) (hi : i ≠ 0#5) : gprIdxs[i.toNat - 1]? = some i := by
  have h0 : i.toNat ≠ 0 := fun h => hi (BitVec.eq_of_toNat_eq h)
  have := i.isLt
  rw [gprIdxs_get _ (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The register at slot `k` of the index list is the one numbered `k + 1`. -/
theorem gprIdxs_slot_inv (k : Nat) (y : BitVec 5) (hk : gprIdxs[k]? = some y) :
    y.toNat = k + 1 := by
  have hk' : k < 31 := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hk
    simpa [gprIdxs] using hlt
  rw [gprIdxs_get _ hk'] at hk
  have := congrArg (fun x => (x.getD 0#5).toNat) hk
  simp only [Option.getD_some, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- The file with the cells of two DISTINCT slots removed: the frame both directions share. -/
private def gprRest (cpu : CPU) (m : RegMap) (ki kj : Nat) : IProp GF :=
  bigSepL (fun k y => if k = kj then emp else if k = ki then emp else gpr cpu y (DFrac.own 1) (m y))
    gprIdxs

/-- The file splits into two distinct cells and the shared frame. -/
private theorem gprFile_split2 (cpu : CPU) (m : RegMap) (i j : BitVec 5)
    (hi : i ≠ 0#5) (hj : j ≠ 0#5) (hij : i ≠ j) :
    gprFile (GF := GF) cpu m ⊣⊢
      gpr cpu i (DFrac.own 1) (m i) ∗ gpr cpu j (DFrac.own 1) (m j) ∗
        gprRest cpu m (i.toNat - 1) (j.toNat - 1) := by
  have hki := gprIdxs_slot i hi
  have hkj := gprIdxs_slot j hj
  have hne : j.toNat - 1 ≠ i.toNat - 1 := by
    intro h
    apply hij
    apply BitVec.eq_of_toNat_eq
    have h0 : i.toNat ≠ 0 := fun h => hi (BitVec.eq_of_toNat_eq h)
    have h0' : j.toNat ≠ 0 := fun h => hj (BitVec.eq_of_toNat_eq h)
    omega
  unfold gprFile gprRest
  refine (BigSepL.bigSepL_delete_cond (Φ := fun _ y => gpr cpu y (DFrac.own 1) (m y)) hki).trans
    (sep_congr_right ?_)
  refine (BigSepL.bigSepL_delete_cond
    (Φ := fun k y => if k = i.toNat - 1 then emp else gpr cpu y (DFrac.own 1) (m y)) hkj).trans ?_
  simp only [hne, if_false]
  exact .rfl

/-- **The two-cell accessor** (Rocq `gpr_file_acc_2`): take two distinct registers out of the
file, and put them back at any values. -/
theorem gprFile_acc_2 (cpu : CPU) (m : RegMap) (i j : BitVec 5)
    (hi : i ≠ 0#5) (hj : j ≠ 0#5) (hij : i ≠ j) :
    gprFile (GF := GF) cpu m ⊢
      gpr cpu i (DFrac.own 1) (m i) ∗ gpr cpu j (DFrac.own 1) (m j) ∗
        (∀ wi wj,
          gpr cpu i (DFrac.own 1) wi -∗ gpr cpu j (DFrac.own 1) wj -∗
            gprFile cpu ((m.set j wj).set i wi)) := by
  have hji : j ≠ i := fun h => hij h.symm
  -- the frame is the same for the updated map: its slots hold neither `i` nor `j`
  have hrest : ∀ wi wj : BitVec 64,
      gprRest (GF := GF) cpu ((m.set j wj).set i wi) (i.toNat - 1) (j.toNat - 1) =
        gprRest cpu m (i.toNat - 1) (j.toNat - 1) := by
    intro wi wj
    unfold gprRest
    refine Iris.Algebra.BigOpL.bigOpL_eq fun {k y} hk => ?_
    have hy := gprIdxs_slot_inv k y hk
    by_cases h1 : k = j.toNat - 1
    · simp only [h1, if_true]
    · by_cases h2 : k = i.toNat - 1
      · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
      · have hyi : y ≠ i := by
          intro e; subst e
          have : y.toNat ≠ 0 := fun h => hi (BitVec.eq_of_toNat_eq h)
          omega
        have hyj : y ≠ j := by
          intro e; subst e
          have : y.toNat ≠ 0 := fun h => hj (BitVec.eq_of_toNat_eq h)
          omega
        simp only [h1, h2, if_false, RegMap.set_other _ _ _ _ hyi, RegMap.set_other _ _ _ _ hyj]
  iintro H
  icases (gprFile_split2 cpu m i j hi hj hij).1 $$ H with ⟨Hi, Hj, Hr⟩
  iframe Hi
  iframe Hj
  iintro %wi %wj Hi Hj
  iapply (gprFile_split2 cpu ((m.set j wj).set i wi) i j hi hj hij).2
  rw [hrest wi wj, RegMap.set_same, RegMap.set_other _ _ _ _ hji, RegMap.set_same]
  isplitl [Hi]
  · iexact Hi
  isplitl [Hj]
  · iexact Hj
  · iexact Hr

end Weak
