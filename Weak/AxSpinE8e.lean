/-
Weak: **PHASE 5, stage 2: the `Hinj` DEGENERACY FINDING** (historical: fixed by the canonical
restriction in AxSpinE6).

Rocq: `iris/AxSpinE8e.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`wpd_mycpu`'s OLD per-call premise (inherited from the old `AxSpinE6.Xx_ret`)
  `Hinj : ∀ v p2 p1 pte, ptree_maps T (svpn_of v) p2 p1 pte → uint (fetch_pa pte v) = pret → v = ret`
quantified over EVERY 64-bit `v`, but `svpn_of v` reads only bits 38..12 and `fetch_pa pte v`
only bits 11..0 (plus the PTE).  So `v` and its non-canonical twin `v + 2^63` satisfy the
antecedent together and `Hinj` forces both to equal `ret`: `hinjUnmapped` — the OLD `Hinj`
implies that NO VA translates to `pret` under `T`; in particular (`hinjRetUnmapped`) `ret` itself
cannot.  Rocq fixed this by restricting `Hinj` to Sv39-canonical VAs (`AxSpinE6.va_canon`).  The
lemmas are about the OLD shape, stated inline (not through `XxRet`); they say nothing about the
current premises.

## Stage C / Q20' status

Every declaration of the Rocq file is a pure bit-vector / page-table fact about the stated
(inline) premise shape, and every one is TRUE under Stage C: nothing here mentions fetch rows,
row pins, stuckness or `XxRet`.  The design note (`notes/weak-port-q20-offrow.md` §C.2 item 3)
calls E8e's finding MOOT under Q20' Option V (the Lean `XxRet` has no `Hinj` at all) — so the
file is consumer-less as a FINDING, but the arithmetic lemmas `svpnUnsigned`, `lo11Unsigned`,
`zShift39` are used by Rocq `AxSpinE8f` (`hinj8`), hence everything is ported.  No stuck twin
exists in this file; NOTHING is dropped.

## Deviations from Rocq

1. TYPES: `mword 64` ↦ `BitVec 64`; `Z_to_bv 64 z` ↦ `BitVec.ofInt 64 z`; `bv_unsigned x` ↦
   `(x.toNat : Int)` (the arithmetic lemmas stay over `Int`, as Rocq's `Z`); `uint (fetch_pa pte v)`
   ↦ `paZ (AxSpinE6.fetchPa pte v)`; `svpn_of` ↦ `WeakKpt.svpnOf`; `ptree_maps` ↦
   `AxPtProt.ptreeMaps`; `subrange_vec_dec x 11 0` ↦ `Sail.BitVec.extractLsb x 11 0`; Rocq's
   `0 ≤ x < 2^64` ↦ `0 ≤ x ∧ x < 2^64`.
2. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `twin` `twin`, `twin_unsigned` `twinUnsigned`, `z_twin_ne` `zTwinNe`,
`z_twin_mod` `zTwinMod`, `z_shift39` `zShift39`, `twin_ne` `twinNe`, `svpn_unsigned`
`svpnUnsigned`, `lo11_unsigned` `lo11Unsigned`, `twin_svpn` `twinSvpn`, `twin_lo` `twinLo`,
`twin_fetch_pa` `twinFetchPa`, `hinj_unmapped` `hinjUnmapped`, `hinj_ret_unmapped`
`hinjRetUnmapped`.  No Lean-only declarations.

**Dropped:** none.  Rocq 13 definitions/lemmas, Lean 13.
-/
import Weak.AxSpinE6

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `twin`: the non-canonical twin (bit 63 flipped, bits 0..62 kept). -/
def twin (v : BitVec 64) : BitVec 64 := BitVec.ofInt 64 ((v.toNat : Int) + 2 ^ 63)

theorem twinUnsigned (v : BitVec 64) :
    ((twin v).toNat : Int) = ((v.toNat : Int) + 2 ^ 63) % 2 ^ 64 := by
  unfold twin
  rw [BitVec.toNat_ofInt]
  have h : (0 : Int) ≤ ((v.toNat : Int) + 2 ^ 63) % ((2 ^ 64 : Nat) : Int) :=
    Int.emod_nonneg _ (by decide)
  rw [Int.toNat_of_nonneg h]
  rfl

theorem zTwinNe (x : Int) : 0 ≤ x ∧ x < 2 ^ 64 → (x + 2 ^ 63) % 2 ^ 64 ≠ x := by
  intro Hr H
  omega

theorem zTwinMod (x m : Int) : 0 < m → 2 ^ 64 % m = 0 → 2 ^ 63 % m = 0 → 0 ≤ x ∧ x < 2 ^ 64 →
    ((x + 2 ^ 63) % 2 ^ 64) % m = x % m := by
  intro _ H64 H63 _
  rw [Int.emod_emod_of_dvd _ (Int.dvd_of_emod_eq_zero H64), Int.add_emod, H63, Int.add_zero,
    Int.emod_emod]

theorem zShift39 (a : Int) : (a / 4096) % 134217728 = (a % 549755813888) / 4096 := by
  omega

theorem twinNe (v : BitVec 64) : twin v ≠ v := by
  intro H
  have h1 := twinUnsigned v
  rw [H] at h1
  have hlt := v.isLt
  exact zTwinNe (v.toNat : Int) ⟨by omega, by omega⟩ h1.symm

/-- Rocq `svpn_unsigned`: `svpn_of` reads bits 38..12 only. -/
theorem svpnUnsigned (a : BitVec 64) :
    ((WeakKpt.svpnOf a).toNat : Int) = ((a.toNat : Int) / 4096) % 134217728 := by
  simp only [WeakKpt.svpnOf, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Functions.pagesize_bits]
  omega

theorem lo11Unsigned (x : BitVec 64) :
    ((Sail.BitVec.extractLsb x 11 0).toNat : Int) = (x.toNat : Int) % 4096 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem twinSvpn (v : BitVec 64) : WeakKpt.svpnOf (twin v) = WeakKpt.svpnOf v := by
  apply BitVec.eq_of_toNat_eq
  have h1 := svpnUnsigned (twin v)
  have h2 := svpnUnsigned v
  rw [zShift39] at h1 h2
  rw [twinUnsigned v] at h1
  have hlt := v.isLt
  have hm := zTwinMod (v.toNat : Int) 549755813888 (by decide) (by decide) (by decide)
    ⟨by omega, by omega⟩
  rw [hm] at h1
  omega

theorem twinLo (v : BitVec 64) :
    Sail.BitVec.extractLsb (twin v) 11 0 = Sail.BitVec.extractLsb v 11 0 := by
  apply BitVec.eq_of_toNat_eq
  have h1 := lo11Unsigned (twin v)
  have h2 := lo11Unsigned v
  rw [twinUnsigned v] at h1
  have hlt := v.isLt
  have hm := zTwinMod (v.toNat : Int) 4096 (by decide) (by decide) (by decide)
    ⟨by omega, by omega⟩
  rw [hm] at h1
  omega

theorem twinFetchPa (pte v : BitVec 64) :
    AxSpinE6.fetchPa pte (twin v) = AxSpinE6.fetchPa pte v := by
  unfold AxSpinE6.fetchPa
  rw [show Sail.BitVec.extractLsb (twin v) (Functions.pagesize_bits - 1) 0
      = Sail.BitVec.extractLsb v (Functions.pagesize_bits - 1) 0 from twinLo v]

/-- Rocq `hinj_unmapped` (THE FINDING): the OLD (all-VA) `Hinj` forces `pret` to be unmapped. -/
theorem hinjUnmapped (T : PTree) (ret : BitVec 64) (pret : Int) :
    (∀ v p2 p1 pte, AxPtProt.ptreeMaps T (WeakKpt.svpnOf v) p2 p1 pte →
      paZ (AxSpinE6.fetchPa pte v) = pret → v = ret) →
    ∀ v p2 p1 pte, AxPtProt.ptreeMaps T (WeakKpt.svpnOf v) p2 p1 pte →
      paZ (AxSpinE6.fetchPa pte v) ≠ pret := by
  intro Hinj v p2 p1 pte Hm Hpa
  have E1 := Hinj v p2 p1 pte Hm Hpa
  have E2 := Hinj (twin v) p2 p1 pte (by rw [twinSvpn]; exact Hm) (by rw [twinFetchPa]; exact Hpa)
  exact twinNe v (E2.trans E1.symm)

/-- Rocq `hinj_ret_unmapped`: in particular the return VA cannot fetch from the pinned return
PA. -/
theorem hinjRetUnmapped (T : PTree) (ret : BitVec 64) (pret : Int) :
    (∀ v p2 p1 pte, AxPtProt.ptreeMaps T (WeakKpt.svpnOf v) p2 p1 pte →
      paZ (AxSpinE6.fetchPa pte v) = pret → v = ret) →
    ¬ ∃ p2 p1 pte, AxPtProt.ptreeMaps T (WeakKpt.svpnOf ret) p2 p1 pte ∧
      paZ (AxSpinE6.fetchPa pte ret) = pret := by
  intro Hinj ⟨p2, p1, pte, Hm, Hpa⟩
  exact hinjUnmapped T ret pret Hinj ret p2 p1 pte Hm Hpa

end Weak
