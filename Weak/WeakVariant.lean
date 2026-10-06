/-
Weak: **the variant lattice of a kernel-PT leaf window under weak execution**
(batch-6 P1).

Rocq: `iris/WeakVariant.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

THE RACY SURFACE of a kernel-table translation is ONE 8-byte leaf window: every
message ever appended to it is an A/D variant `pteSetAD w0 a d` of the canonical
leaf `w0`, and A/D are bits 6/7 -- both in BYTE 0 of the little-endian word.  This
file is the PURE layer that turns those two facts into the lemmas the weak
absorption theorem (P4) consumes:

  §1  BYTE STABILITY: a variant agrees with `w0` on bytes 1-7, and ANY per-byte
      mixture of variant bytes assembles back to a variant (the load-mixture
      lemma) -- so a weak read that picks a different message per byte still
      returns a variant.  §1b: the walker discriminator's correspondence (a
      model write-back is `adShaped`).
  §2  THE VALUE-PINNED BYTE: a byte all of whose log values agree behaves SC.
  §3  THE VALUE-CLOSURE PREDICATE `wlogVariants log a8 w0`, its monotonicity
      under appends, its preservation across a CAS-model write-back, and the
      collapse of `WeakRacy.wadm` / `WeakInterp.wreadOk` at the window: the read
      word IS a variant (7 bytes pinned + byte 0 enumerated).
  §4  BIT-MONOTONICITY UNDER THE CAS DISCIPLINE: if every window write is
      fresh-derived (`wbyteFreshDerived`), the A/D bits are monotone along the
      log and the latest word dominates every readable variant (`pteAdLe`);
      whether `update_PTE_Bits` FIRES is decided by the latest word alone
      (`updatePTEBitsFiresMono` / `updatePTEBitsFiresLatest`).
  §5  the `wlat8` bundle tied to §4's pure premise `wwinLatest`.

THE COVER PREMISE `wwinCovered` is the pure shadow of the per-hart receipt: the
hart's read floor already covers a write to every window byte, which bars the
era-initial image from every admissible read.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below).  No Rocq name of this file is in the
   duplicated-name table.  VOCABULARY (`Weak/WeakWord8.lean` deviation 1): `mword 64`
   / `bv 64` ↦ `BitVec 64`, `bv (8 * 8)` ↦ `BitVec (8 * 8)` (= `BitVec 64` by
   conversion), `mword 1` ↦ `BitVec 1`, `'b"1"` ↦ `1#1`, `mword_of_int 0` ↦ `0#1`,
   `Z.testbit (bv_unsigned b) i` ↦ `b.toNat.testBit i` (the spelling of
   `WeakPromise.adByte0`), `eq_vec x 'b"0"` ↦ `x == 0#1`, `nth_byte w j` ↦
   `nthByte (n := 8) w j`, `acc_addr` ↦ `WeakInterp.accAddr`, `pa_z` ↦ `paZ`,
   `wm_log s` ↦ `s.wmLog`, `w_vrNew (wm_ws s)` ↦ `s.wmWs.wVrNew`, `l !! i` ↦ `l[i]?`,
   `l !!! i` ↦ `l[i]!`, `is_Some o` ↦ `o.isSome = true`, `(1 <= j < 8)%nat` ↦
   `1 ≤ j ∧ j < 8`, `pte_set_ad` ↦ `MachCSL.pteSetAD`.  Statement shapes (WeakWord8
   deviation 2): Rocq `A -∗ B -∗ C` is `A ⊢ B -∗ C`.
2. `nth_byte_testbit` / `nth_byte0_testbit`: Rocq states them at any width `bv m`;
   MachCSL's `nthByte` is only defined at `BitVec (8 * m)`, so they are stated there.
3. O2 (the i-cache arm, `WeakInterp` header).  Rocq's `ak_coh` arm of `wbyte_ok` was
   "`t` is the global latest", which the cover premise refutes at `t = 0`; the Lean
   `akIfetch` arm is `ifetchByteOk`'s window `¬ writesIn log a t (max t itv)`, which
   the data-view cover does NOT refute (it does not see `wmItv`).  So
   `wbyteOkNotInit` and every lemma built on it carry the extra premise
   `ak.akIfetch = false` (placed just before the cover premise): `wbyteOkNotInit`,
   `wbyteOkPinnedValMsgs`, `wbyteOkVariant`, `wadmVariant`, `wreadOkVariant`,
   `wadmVariantBytes`, `wlogVariantsPinnedByte`, `wadmPteAdLeLatest`.  Every consumer
   reads a page-table window by a walk (`AK_ttw`, `akIfetch = false`) or a plain /
   exclusive load.  `wwinLatestVariant` and §5 are unchanged.
4. THE `PtAdBits` WRITE-BACK LEMMAS are not in the Lean tree (`notes/weak-port-map.md`
   §3; the architecture note puts them in `Weak/`, not `MachCSL/`).  The ones this
   file uses are proved here, file-qualified `PtAdBits.*` so that a later
   `Weak/PtAdBits.lean` port can take them over: `PtAdBits.updatePTEBitsSetAd`,
   `PtAdBits.updatePTEBitsA1`, `PtAdBits.updatePTEBitsNe`, `PtAdBits.pteCanon`,
   `PtAdBits.pteCanonSetAd`.  `pte_set_ad_absorb` is `MachCSL.pteSetAD_pteSetAD` and
   `mword1_cases` is `MachCSL.bv1_cases`; `pte_set_ad_testbit` is not needed (the
   bit facts are closed by `bv_decide` per concrete byte/bit).
5. Lean-only helper: `updatePTEBitsEq`, the model's `update_PTE_Bits` at 64 bits
   restated over `pteGetA`/`pteGetD`/`pteSetAD`/`MachCSL.accWrites` (the case split
   on the access kind, once; Rocq unfolds the body in each proof).  `pteGetA` /
   `pteGetD` are declared in §0 (Rocq §4a), before the `PtAdBits` helpers use them.
6. Rocq `Local` lemmas (`mword1_zero_iff`, `eq_vec1_zero_true`, `mw1_ne_mw0`,
   `writes_in_to_len`, `log_byte_variant`, `fires_mono_core`) are ordinary theorems.
7. §5: `Context {!riscvGS Σ, !weakGS Σ}` is `[WeakGS GF]` (the SC instance is unused,
   `WeakGhost` deviation 10 convention).  `wm_img σ` ↦ `σ.wmImg`.

**Rocq → Lean name map.**  `nth_byte_testbit` ↦ `nthByteTestbit`; `nth_byte0_testbit`
↦ `nthByte0Testbit`; `mword1_zero_iff` ↦ `mword1ZeroIff`; `eq_vec1_zero_true` ↦
`eqVec1ZeroTrue`; `mw1_ne_mw0` ↦ `mw1NeMw0`; `pte_set_ad_nth_byte_high` ↦
`pteSetAdNthByteHigh`; `pte_variant_mix` ↦ `pteVariantMix`; `ad_byte0_pte_set_ad` ↦
`adByte0PteSetAd`; `ad_shaped_of_pte_set_ad` ↦ `adShapedOfPteSetAd`;
`ad_shaped_of_update_PTE_Bits` ↦ `adShapedOfUpdatePTEBits`; `readable_pinned_val` ↦
`readablePinnedVal`; `wbyte_ok_pinned_val` ↦ `wbyteOkPinnedVal`; `writes_in_to_len` ↦
`writesInToLen`; `wbyte_ok_not_init` ↦ `wbyteOkNotInit`; `log_byte_msg` ↦ `logByteMsg`;
`wbyte_ok_pinned_val_msgs` ↦ `wbyteOkPinnedValMsgs`; `wmsg_variant` ↦ `wmsgVariant`;
`wlog_variants` ↦ `wlogVariants`; `wlog_variants_nil` ↦ `wlogVariantsNil`;
`wlog_variants_lookup` ↦ `wlogVariantsLookup`; `wmsg_variant_untouched` ↦
`wmsgVariantUntouched`; `wlog_variants_app` ↦ `wlogVariantsApp`; `wmsg_variant_write`
↦ `wmsgVariantWrite`; `update_PTE_Bits_variant` ↦ `updatePTEBitsVariant`;
`wlog_variants_writeback` ↦ `wlogVariantsWriteback`; `wwin_covered` ↦ `wwinCovered`;
`log_byte_variant` ↦ `logByteVariant`; `wbyte_ok_variant` ↦ `wbyteOkVariant`;
`wadm_variant` ↦ `wadmVariant`; `wread_ok_variant` ↦ `wreadOkVariant`;
`wadm_variant_bytes` ↦ `wadmVariantBytes`; `wlog_variants_pinned_byte` ↦
`wlogVariantsPinnedByte`; `ad_bits_le` ↦ `adBitsLe`; `ad_bits_le_refl` ↦
`adBitsLeRefl`; `ad_bits_le_trans` ↦ `adBitsLeTrans`; `pte_getA` ↦ `pteGetA`;
`pte_getD` ↦ `pteGetD`; `pte_getA_testbit` ↦ `pteGetATestbit`; `pte_getD_testbit` ↦
`pteGetDTestbit`; `pte_getA_set_ad` ↦ `pteGetASetAd`; `pte_getD_set_ad` ↦
`pteGetDSetAd`; `pte_getA_zero_iff` ↦ `pteGetAZeroIff`; `pte_getD_zero_iff` ↦
`pteGetDZeroIff`; `pte_ad_le` ↦ `pteAdLe`; `pte_ad_le_refl` ↦ `pteAdLeRefl`;
`pte_ad_le_trans` ↦ `pteAdLeTrans`; `pte_ad_le_byte0` ↦ `pteAdLeByte0`;
`pte_ad_le_of_byte0` ↦ `pteAdLeOfByte0`; `update_PTE_Bits_shape` ↦
`updatePTEBitsShape`; `update_PTE_Bits_ad_ge` ↦ `updatePTEBitsAdGe`; `fires_mono_core`
↦ `firesMonoCore`; `update_PTE_Bits_fires_mono` ↦ `updatePTEBitsFiresMono`;
`update_PTE_Bits_fires_latest` ↦ `updatePTEBitsFiresLatest`; `writes_le_latest_ts` ↦
`writesLeLatestTs`; `log_byte_take` ↦ `logByteTake`; `wbyte_fresh_derived` ↦
`wbyteFreshDerived`; `wbyte_fresh_derived_mono` ↦ `wbyteFreshDerivedMono`;
`wbyte_fresh_derived_latest` ↦ `wbyteFreshDerivedLatest`; `wbyte_fresh_derived_app` ↦
`wbyteFreshDerivedApp`; `wbyte_fresh_derived_writeback` ↦ `wbyteFreshDerivedWriteback`;
`wwin_latest` ↦ `wwinLatest`; `wwin_latest_variant` ↦ `wwinLatestVariant`;
`wadm_pte_ad_le_latest` ↦ `wadmPteAdLeLatest`; `wlat8_win_latest` ↦ `wlat8WinLatest`;
`wlat8_variant` ↦ `wlat8Variant`.  (`PtAdBits.v`: `pte_canon` ↦ `PtAdBits.pteCanon`,
`pte_canon_set_ad` ↦ `PtAdBits.pteCanonSetAd`, `update_PTE_Bits_set_ad` ↦
`PtAdBits.updatePTEBitsSetAd`, `update_PTE_Bits_A1` ↦ `PtAdBits.updatePTEBitsA1`,
`update_PTE_Bits_ne` ↦ `PtAdBits.updatePTEBitsNe`.)

**Dropped.**  Nothing.
-/
import Weak.WeakWord8
import Weak.WeakRacy
import Weak.WeakInterpProj
import Weak.WeakPromise
import MachCSL.Pte
import MachCSL.Wp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. The byte/testbit kit -/

/-- Bit `i` of byte `j` is bit `8j+i` of the word. -/
theorem nthByteTestbit {m : Nat} (w : BitVec (8 * m)) (j i : Nat) :
    i < 8 → (nthByte w j).toNat.testBit i = w.toNat.testBit (8 * j + i) := by
  intro hi
  rw [BitVec.testBit_toNat, BitVec.testBit_toNat]
  simp [nthByte, hi]

/-- ... and byte 0 in particular reads the word's own low bits. -/
theorem nthByte0Testbit {m : Nat} (w : BitVec (8 * m)) (i : Nat) :
    i < 8 → (nthByte w 0).toNat.testBit i = w.toNat.testBit i := by
  intro hi
  rw [nthByteTestbit w 0 i hi, Nat.mul_zero, Nat.zero_add]

/-- A 1-bit word is zero exactly when its bit 0 is clear. -/
theorem mword1ZeroIff (x : BitVec 1) : x = 0#1 ↔ x.toNat.testBit 0 = false := by
  rcases bv1_cases x with rfl | rfl <;> decide

theorem eqVec1ZeroTrue (x : BitVec 1) : (x == 0#1) = true ↔ x = 0#1 := by
  rcases bv1_cases x with rfl | rfl <;> decide

theorem mw1NeMw0 : (1#1 : BitVec 1) ≠ 0#1 := by decide

/-- The two flag getters, spelled exactly as the model's update path reads them
(`update_PTE_Bits`'s `pte_flags` projections).  (Rocq §4a; deviation 5.) -/
def pteGetA (w : BitVec 64) : BitVec 1 :=
  _get_PTE_Flags_A (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0))
def pteGetD (w : BitVec 64) : BitVec 1 :=
  _get_PTE_Flags_D (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0))

/-- Lean-only (deviation 5): the model's `update_PTE_Bits` at 64 bits, over the getters. -/
theorem updatePTEBitsEq (w : BitVec 64) (acc : MemoryAccessType mem_payload) :
    update_PTE_Bits w acc =
      if ((pteGetD w == 0#1) && accWrites acc) || ((pteGetA w == 0#1) && !is_prefetch_access acc)
      then some (pteSetAD w 1#1 (if (pteGetD w == 0#1) && accWrites acc then 1#1 else pteGetD w))
      else none := by
  cases acc with
  | CacheAccess c => cases c <;> rfl
  | _ => rfl

/-! ### The `PtAdBits` write-back lemmas this file uses (deviation 4) -/

/-- The A/D-canonical form: A and D zeroed. -/
def PtAdBits.pteCanon (w : BitVec 64) : BitVec 64 := pteSetAD w 0#1 0#1

theorem PtAdBits.pteCanonSetAd (w : BitVec 64) (a d : BitVec 1) :
    PtAdBits.pteCanon (pteSetAD w a d) = PtAdBits.pteCanon w := by
  unfold PtAdBits.pteCanon; exact pteSetAD_pteSetAD w a d 0#1 0#1

theorem pteGetASetAd (w : BitVec 64) (a d : BitVec 1) : pteGetA (pteSetAD w a d) = a :=
  A_of_pteSetAD w a d

theorem pteGetDSetAd (w : BitVec 64) (a d : BitVec 1) : pteGetD (pteSetAD w a d) = d :=
  D_of_pteSetAD w a d

/-- The exact shape of a fired update: A is set to 1, D is set to 1 or kept.  (Rocq §4b;
stated here because the `PtAdBits` lemmas below are its corollaries.) -/
theorem updatePTEBitsShape (w w' : BitVec 64) (acc : MemoryAccessType mem_payload) :
    update_PTE_Bits w acc = some w' →
    ∃ d : BitVec 1, w' = pteSetAD w 1#1 d ∧ (d = 1#1 ∨ d = pteGetD w) := by
  intro h
  rw [updatePTEBitsEq] at h
  split at h
  · injection h with h
    subst h
    refine ⟨_, rfl, ?_⟩
    split
    · exact .inl rfl
    · exact .inr rfl
  · cases h

/-- The write-back word is an A/D variant of the walked leaf. -/
theorem PtAdBits.updatePTEBitsSetAd (w w' : BitVec 64) (acc : MemoryAccessType mem_payload) :
    update_PTE_Bits w acc = some w' → ∃ a d : BitVec 1, w' = pteSetAD w a d := by
  intro h
  obtain ⟨d, hw, _⟩ := updatePTEBitsShape w w' acc h
  exact ⟨1#1, d, hw⟩

/-- A is always driven to 1. -/
theorem PtAdBits.updatePTEBitsA1 (w w' : BitVec 64) (acc : MemoryAccessType mem_payload) :
    update_PTE_Bits w acc = some w' → ∃ d : BitVec 1, w' = pteSetAD w 1#1 d := by
  intro h
  obtain ⟨d, hw, _⟩ := updatePTEBitsShape w w' acc h
  exact ⟨d, hw⟩

/-- The write-back always changes the word it read. -/
theorem PtAdBits.updatePTEBitsNe (w w' : BitVec 64) (acc : MemoryAccessType mem_payload) :
    update_PTE_Bits w acc = some w' → w' ≠ w := by
  intro h heq
  rw [updatePTEBitsEq] at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    have hA := pteGetASetAd w 1#1
      (if (pteGetD w == 0#1) && accWrites acc then 1#1 else pteGetD w)
    have hD := pteGetDSetAd w 1#1
      (if (pteGetD w == 0#1) && accWrites acc then 1#1 else pteGetD w)
    rw [heq] at hA hD
    revert hc hA hD
    generalize pteGetD w = D
    generalize pteGetA w = A
    generalize accWrites acc = x
    generalize is_prefetch_access acc = y
    revert D A x y
    decide
  · cases h

/-! ## 1. Byte stability: variants agree on bytes 1–7 -/

/-- Bytes 1–7 of a variant are the base word's own — A/D live in byte 0. -/
theorem pteSetAdNthByteHigh (w : BitVec 64) (a d : BitVec 1) (j : Nat) :
    1 ≤ j ∧ j < 8 → nthByte (n := 8) (pteSetAD w a d) j = nthByte (n := 8) w j := by
  rintro ⟨h1, h8⟩
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  all_goals
    simp only [nthByte, pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange,
      Sail.BitVec.updateSubrange', BitVec.extractLsb, _update_PTE_Flags_A, _update_PTE_Flags_D]
    bv_decide

/-- THE LOAD-MIXTURE LEMMA.  A word whose every byte is SOME variant's byte is itself a
variant — byte 0 fixes the `(a, d)`, bytes 1–7 are pinned. -/
theorem pteVariantMix (w0 : BitVec 64) (w : BitVec (8 * 8)) :
    (∀ j : Nat, j < 8 → ∃ a d : BitVec 1, nthByte w j = nthByte (n := 8) (pteSetAD w0 a d) j) →
    ∃ a d : BitVec 1, w = pteSetAD w0 a d := by
  intro hb
  obtain ⟨a, d, h0⟩ := hb 0 (by omega)
  refine ⟨a, d, bv_eq_of_bytes (n := 8) w (pteSetAD w0 a d) fun j hj => ?_⟩
  rcases j with _ | j
  · exact h0
  · obtain ⟨a', d', hj'⟩ := hb (j + 1) hj
    rw [hj', pteSetAdNthByteHigh w0 a' d' (j + 1) ⟨by omega, hj⟩,
      pteSetAdNthByteHigh w0 a d (j + 1) ⟨by omega, hj⟩]

/-! ## 1b. The walker discriminator's correspondence (layer2 §13, W2a)

`WeakPromise.adShaped` classifies a conditional write's WRITTEN BYTES against the bytes
its reservation read.  The model returns `some w'` from `update_PTE_Bits w acc` only with
`w' = pteSetAD w 1 d` and `w' ≠ w`, and those two facts are exactly the byte-list shape
`adShaped` asks for.  The `w' ≠ w` half excludes the SOFTWARE-RMW false positive. -/

/-- Byte 0 of an A-driving variant is A/D-shaped against the base's byte 0, PROVIDED the
words differ. -/
theorem adByte0PteSetAd (w : BitVec 64) (d : BitVec 1) :
    pteSetAD w 1#1 d ≠ w →
    adByte0 (nthByte (n := 8) w 0) (nthByte (n := 8) (pteSetAD w 1#1 d) 0) := by
  intro hne
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.testBit_toNat, nthByte, pteSetAD, Sail.BitVec.extractLsb,
      Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.extractLsb,
      _update_PTE_Flags_A, _update_PTE_Flags_D]
    bv_decide
  · intro i hi
    obtain rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    all_goals
      simp only [BitVec.testBit_toNat, nthByte, pteSetAD, Sail.BitVec.extractLsb,
        Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.extractLsb,
        _update_PTE_Flags_A, _update_PTE_Flags_D]
      bv_decide
  · intro h0
    apply hne
    simp only [nthByte, pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange,
      Sail.BitVec.updateSubrange', BitVec.extractLsb, _update_PTE_Flags_A,
      _update_PTE_Flags_D] at h0 ⊢
    bv_decide

/-- THE CORRESPONDENCE: a write-back word, split into bytes by the tree's own convention
(`WeakInterpProj.wbytes`), is `adShaped` against a reservation whose column read the
pre-image word. -/
theorem adShapedOfPteSetAd (img : Image) (log : List Wmsg) (base : Int) (rts : List Nat)
    (w w' : BitVec 64) (d : BitVec 1) :
    rts.length = 8 →
    (∀ j : Nat, j < 8 → resReadByte img log base rts j = some (nthByte (n := 8) w j)) →
    w' = pteSetAD w 1#1 d →
    w' ≠ w →
    adShaped img log base rts (WeakInterpProj.wbytes 8 w') := by
  intro hlen hread hw' hne
  subst hw'
  refine ⟨by rw [wbytesLength, hlen], fun j hj => ?_, nthByte (n := 8) w 0,
    nthByte (n := 8) (pteSetAD w 1#1 d) 0, wbytesLookupGen 8 _ 0 (by omega),
    hread 0 (by omega), adByte0PteSetAd w d hne⟩
  rw [wbytesLength] at hj
  rw [wbytesLookupGen 8 _ j hj.2, hread j hj.2]
  exact congrArg some (pteSetAdNthByteHigh w 1#1 d j hj)

/-- ... and the packaging straight off the model's own update function. -/
theorem adShapedOfUpdatePTEBits (img : Image) (log : List Wmsg) (base : Int) (rts : List Nat)
    (w w' : BitVec 64) (acc : MemoryAccessType mem_payload) :
    rts.length = 8 →
    (∀ j : Nat, j < 8 → resReadByte img log base rts j = some (nthByte (n := 8) w j)) →
    update_PTE_Bits w acc = some w' →
    adShaped img log base rts (WeakInterpProj.wbytes 8 w') := by
  intro hlen hread hup
  obtain ⟨d, hw'⟩ := PtAdBits.updatePTEBitsA1 w w' acc hup
  exact adShapedOfPteSetAd img log base rts w w' d hlen hread hw'
    (PtAdBits.updatePTEBitsNe w w' acc hup)

/-! ## 2. The value-pinned byte: unanimity makes a byte SC -/

/-- If every timestamp that holds a value for `a` holds `v`, any admissible read of `a`
returns `v`.  Stated at `WeakMem` altitude. -/
theorem readablePinnedVal (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int)
    (v : BitVec 8) (t : Nat) :
    (∀ (t' : Nat) (b : BitVec 8), logByte img log t' a = some b → b = v) →
    readable img log ws vpre a t →
    logByte img log t a = some v := by
  rintro hv ⟨hs, _⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
  rw [hb, hv t b hb]

/-- ... and at the interpreter's `wbyteOk`. -/
theorem wbyteOkPinnedVal (s : Wmstate) (ak : AkInfo) (a : Int) (v : BitVec 8) (t : Nat)
    (b : BitVec 8) :
    (∀ (t' : Nat) (b' : BitVec 8), logByte (wimg s) s.wmLog t' a = some b' → b' = v) →
    wbyteOk s ak a t b → b = v := by
  rintro hv ⟨hb, _⟩
  exact hv t b hb

/-- A cover premise turns "some writer is below the hart's floor" into "the whole log has a
writer". -/
theorem writesInToLen (log : List Wmsg) (a : Int) (V : Nat) :
    writesIn log a 0 V → writesIn log a 0 log.length := fun h =>
  writesInMonoHi log a 0 _ _ (Nat.min_le_right _ _) (writesInClip log a 0 V h)

/-- THE IMAGE-EXCLUSION LEMMA: with the hart's read floor covering a write to `a`, NO
admissible non-fetch read returns the era-initial image (deviation 3). -/
theorem wbyteOkNotInit (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (b : BitVec 8) :
    ak.akIfetch = false →
    writesIn s.wmLog a 0 s.wmWs.wVrNew →
    wbyteOk s ak a t b → t ≠ 0 := by
  rintro hif hcov ⟨_, hadm⟩
  rw [hif] at hadm
  simp only [Bool.false_eq_true, ↓reduceIte] at hadm
  exact readableNotInit _ _ _ _ _ _ hadm.1
    (writesInMonoHi _ _ _ _ _ (loadVpreVrNew _ _) hcov)

/-- The source of a non-initial value is a log MESSAGE. -/
theorem logByteMsg (img : Image) (log : List Wmsg) (t : Nat) (a : Int) (v : BitVec 8) :
    logByte img log t a = some v →
    t = 0 ∨ ∃ (i : Nat) (m : Wmsg), t = i + 1 ∧ log[i]? = some m ∧ msgByte m a = some v := by
  intro h
  cases t with
  | zero => exact .inl rfl
  | succ i =>
    right
    rw [logByteS] at h
    cases hm : log[i]? with
    | none => rw [hm] at h; cases h
    | some m =>
      rw [hm] at h
      exact ⟨i, m, rfl, hm, h⟩

/-- The message-unanimity form of the pinned byte: if every LOG MESSAGE writes `v` at `a`
and the image is excluded by the cover, every admissible read returns `v`. -/
theorem wbyteOkPinnedValMsgs (s : Wmstate) (ak : AkInfo) (a : Int) (v : BitVec 8) (t : Nat)
    (b : BitVec 8) :
    (∀ m : Wmsg, m ∈ s.wmLog → ∀ b' : BitVec 8, msgByte m a = some b' → b' = v) →
    ak.akIfetch = false →
    writesIn s.wmLog a 0 s.wmWs.wVrNew →
    wbyteOk s ak a t b → b = v := by
  intro hv hif hcov hok
  have hne := wbyteOkNotInit s ak a t b hif hcov hok
  rcases logByteMsg _ _ _ _ _ hok.1 with hz | ⟨i, m, rfl, hm, hmb⟩
  · exact absurd hz hne
  · exact hv m (List.mem_of_getElem? hm) b hmb

/-! ## 3. The value-closure predicate and the `wadm` collapse -/

/-- One message writes only variant bytes into the window at `a8`: ONE `(a, d)` such that
every window byte the message writes is that variant's byte. -/
def wmsgVariant (a8 : Int) (w0 : BitVec 64) (m : Wmsg) : Prop :=
  ∃ a d : BitVec 1, ∀ j : Nat, j < 8 → ∀ b : BitVec 8,
    msgByte m (a8 + (j : Int)) = some b → b = nthByte (n := 8) (pteSetAD w0 a d) j

/-- THE VALUE-CLOSURE PREDICATE: every message of the log is a variant writer. -/
def wlogVariants (log : List Wmsg) (a8 : Int) (w0 : BitVec 64) : Prop :=
  ∀ m : Wmsg, m ∈ log → wmsgVariant a8 w0 m

theorem wlogVariantsNil (a8 : Int) (w0 : BitVec 64) : wlogVariants [] a8 w0 := by
  intro m hm
  simp at hm

theorem wlogVariantsLookup (log : List Wmsg) (a8 : Int) (w0 : BitVec 64) (i : Nat) (m : Wmsg) :
    wlogVariants log a8 w0 → log[i]? = some m → wmsgVariant a8 w0 m :=
  fun hv hm => hv m (List.mem_of_getElem? hm)

/-- A message disjoint from the window is vacuously a variant writer. -/
theorem wmsgVariantUntouched (a8 : Int) (w0 : BitVec 64) (m : Wmsg) :
    (∀ j : Nat, j < 8 → msgByte m (a8 + (j : Int)) = none) → wmsgVariant a8 w0 m := by
  intro hno
  refine ⟨0#1, 0#1, fun j hj b hb => ?_⟩
  rw [hno j hj] at hb
  cases hb

/-- Monotonicity under appends whose new messages are variant writers. -/
theorem wlogVariantsApp (log ms : List Wmsg) (a8 : Int) (w0 : BitVec 64) :
    wlogVariants log a8 w0 →
    (∀ m : Wmsg, m ∈ ms → wmsgVariant a8 w0 m) →
    wlogVariants (log ++ ms) a8 w0 := by
  intro hlog hms m hm
  rcases List.mem_append.1 hm with h | h
  · exact hlog m h
  · exact hms m h

/-- An appended whole-window write whose value is a variant. -/
theorem wmsgVariantWrite (tid : Option Nat) (k : WmClass) (pa : PAddr) (v : BitVec (8 * 8))
    (a8 : Int) (w0 : BitVec 64) :
    paZ pa = a8 →
    (∃ a d : BitVec 1, v = pteSetAD w0 a d) →
    wmsgVariant a8 w0 (wwriteMsg tid k pa 8 v) := by
  rintro rfl ⟨a, d, hv⟩
  refine ⟨a, d, fun j hj b hb => ?_⟩
  have hab := wwriteMsgByte tid k pa 8 v j hj
  unfold WeakInterp.accAddr at hab
  rw [hab] at hb
  injection hb with hb
  subst hb hv
  rfl

/-- `update_PTE_Bits` of a variant is a variant — the absorption law at the log's
altitude. -/
theorem updatePTEBitsVariant (w0 fresh w' : BitVec 64) (acc : MemoryAccessType mem_payload) :
    (∃ a d : BitVec 1, fresh = pteSetAD w0 a d) →
    update_PTE_Bits fresh acc = some w' →
    ∃ a d : BitVec 1, w' = pteSetAD w0 a d := by
  rintro ⟨a0, d0, rfl⟩ hup
  obtain ⟨a, d, hw'⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hup
  exact ⟨a, d, by rw [hw', pteSetAD_pteSetAD]⟩

/-- THE PRESERVATION LEMMA for a CAS-model write-back: the appended message writes
`update_PTE_Bits fresh`, and `fresh` is itself a variant. -/
theorem wlogVariantsWriteback (tid : Option Nat) (k : WmClass) (pa : PAddr)
    (acc : MemoryAccessType mem_payload) (log : List Wmsg) (a8 : Int)
    (w0 fresh w' : BitVec 64) (v : BitVec (8 * 8)) :
    paZ pa = a8 →
    (∃ a d : BitVec 1, fresh = pteSetAD w0 a d) →
    update_PTE_Bits fresh acc = some w' →
    v = w' →
    wlogVariants log a8 w0 →
    wlogVariants (log ++ [wwriteMsg tid k pa 8 v]) a8 w0 := by
  intro hpa hf hup hv hlog
  apply wlogVariantsApp _ _ _ _ hlog
  intro m hm
  rw [List.mem_singleton] at hm
  subst hm
  apply wmsgVariantWrite tid k pa v a8 w0 hpa
  obtain ⟨a, d, hw'⟩ := updatePTEBitsVariant w0 fresh w' acc hf hup
  exact ⟨a, d, by rw [hv]; exact hw'⟩

/-! ### The collapse at the window -/

/-- The cover premise for a whole window — the pure shadow of the receipt: the hart's read
floor covers a write to every window byte. -/
def wwinCovered (s : Wmstate) (ra : PAddr) : Prop :=
  ∀ j : Nat, j < 8 → writesIn s.wmLog (WeakInterp.accAddr ra j) 0 s.wmWs.wVrNew

/-- A non-initial window byte value is a variant byte. -/
theorem logByteVariant (s : Wmstate) (ra : PAddr) (w0 : BitVec 64) (j t : Nat) (b : BitVec 8) :
    j < 8 →
    wlogVariants s.wmLog (paZ ra) w0 →
    t ≠ 0 →
    logByte (wimg s) s.wmLog t (WeakInterp.accAddr ra j) = some b →
    ∃ a d : BitVec 1, b = nthByte (n := 8) (pteSetAD w0 a d) j := by
  intro hj hvar hne hb
  rcases logByteMsg _ _ _ _ _ hb with hz | ⟨i, m, rfl, hm, hmb⟩
  · exact absurd hz hne
  · obtain ⟨a, d, hv⟩ := wlogVariantsLookup _ _ _ _ _ hvar hm
    exact ⟨a, d, hv j hj b hmb⟩

/-- One admissible byte of the window is a variant byte. -/
theorem wbyteOkVariant (s : Wmstate) (ak : AkInfo) (ra : PAddr) (w0 : BitVec 64) (j t : Nat)
    (b : BitVec 8) :
    j < 8 →
    wlogVariants s.wmLog (paZ ra) w0 →
    ak.akIfetch = false →
    wwinCovered s ra →
    wbyteOk s ak (WeakInterp.accAddr ra j) t b →
    ∃ a d : BitVec 1, b = nthByte (n := 8) (pteSetAD w0 a d) j := by
  intro hj hvar hif hcov hok
  have hne := wbyteOkNotInit s ak _ t b hif (hcov j hj) hok
  exact logByteVariant s ra w0 j t b hj hvar hne hok.1

/-- THE `wadm` COLLAPSE: `WeakRacy`'s per-byte admissibility at the window implies the read
word is a variant of the canonical leaf. -/
theorem wadmVariant (s : Wmstate) (rak : AkInfo) (ra : PAddr) (w0 : BitVec 64)
    (w : BitVec (8 * 8)) :
    wlogVariants s.wmLog (paZ ra) w0 →
    rak.akIfetch = false →
    wwinCovered s ra →
    wadm s rak ra 8 w →
    ∃ a d : BitVec 1, w = pteSetAD w0 a d := by
  intro hvar hif hcov hadm
  apply pteVariantMix
  intro j hj
  obtain ⟨t, hok⟩ := hadm j hj
  exact wbyteOkVariant s rak ra w0 j t _ hj hvar hif hcov hok

/-- ... the same collapse against `WeakInterp`'s read/assemble shape. -/
theorem wreadOkVariant (s : Wmstate) (ak : AkInfo) (ra : PAddr) (w0 : BitVec 64)
    (ts : List Nat) (w : BitVec (8 * 8)) :
    wlogVariants s.wmLog (paZ ra) w0 →
    ak.akIfetch = false →
    wwinCovered s ra →
    wreadOk s ak ra 8 ts w →
    ∃ a d : BitVec 1, w = pteSetAD w0 a d := by
  rintro hvar hif hcov ⟨_, hbytes⟩
  apply pteVariantMix
  intro j hj
  exact wbyteOkVariant s ak ra w0 j ts[j]! _ hj hvar hif hcov (hbytes j hj)

/-- The per-byte reading of the collapse. -/
theorem wadmVariantBytes (s : Wmstate) (rak : AkInfo) (ra : PAddr) (w0 : BitVec 64)
    (w : BitVec (8 * 8)) :
    wlogVariants s.wmLog (paZ ra) w0 →
    rak.akIfetch = false →
    wwinCovered s ra →
    wadm s rak ra 8 w →
    (∀ j : Nat, 1 ≤ j ∧ j < 8 → nthByte w j = nthByte (n := 8) w0 j) ∧
    (∃ a d : BitVec 1, nthByte w 0 = nthByte (n := 8) (pteSetAD w0 a d) 0) := by
  intro hvar hif hcov hadm
  obtain ⟨a, d, hw⟩ := wadmVariant s rak ra w0 w hvar hif hcov hadm
  subst hw
  exact ⟨fun j hj => pteSetAdNthByteHigh w0 a d j hj, a, d, rfl⟩

/-- Bytes 1–7 through the closure: every admissible read of a high window byte returns the
CANONICAL byte. -/
theorem wlogVariantsPinnedByte (s : Wmstate) (ak : AkInfo) (ra : PAddr) (w0 : BitVec 64)
    (j t : Nat) (b : BitVec 8) :
    1 ≤ j ∧ j < 8 →
    wlogVariants s.wmLog (paZ ra) w0 →
    ak.akIfetch = false →
    wwinCovered s ra →
    wbyteOk s ak (WeakInterp.accAddr ra j) t b →
    b = nthByte (n := 8) w0 j := by
  intro hj hvar hif hcov hok
  obtain ⟨a, d, hb⟩ := wbyteOkVariant s ak ra w0 j t b hj.2 hvar hif hcov hok
  rw [hb]
  exact pteSetAdNthByteHigh w0 a d j hj

/-! ## 4. Bit-monotonicity under the CAS discipline -/

/-! ### 4a. The A/D order, at byte and word altitude -/

/-- "`b'`'s A/D bits dominate `b`'s" — the order on variant BYTES. -/
def adBitsLe (b b' : BitVec 8) : Prop :=
  (b.toNat.testBit 6 = true → b'.toNat.testBit 6 = true) ∧
  (b.toNat.testBit 7 = true → b'.toNat.testBit 7 = true)

theorem adBitsLeRefl (b : BitVec 8) : adBitsLe b b := ⟨id, id⟩

theorem adBitsLeTrans (b1 b2 b3 : BitVec 8) :
    adBitsLe b1 b2 → adBitsLe b2 b3 → adBitsLe b1 b3 := by
  rintro ⟨ha1, hd1⟩ ⟨ha2, hd2⟩
  exact ⟨fun h => ha2 (ha1 h), fun h => hd2 (hd1 h)⟩

theorem pteGetATestbit (w : BitVec 64) : (pteGetA w).toNat.testBit 0 = w.toNat.testBit 6 := by
  simp only [BitVec.testBit_toNat, pteGetA, _get_PTE_Flags_A, Mk_PTE_Flags,
    Sail.BitVec.extractLsb, BitVec.extractLsb]
  bv_decide

theorem pteGetDTestbit (w : BitVec 64) : (pteGetD w).toNat.testBit 0 = w.toNat.testBit 7 := by
  simp only [BitVec.testBit_toNat, pteGetD, _get_PTE_Flags_D, Mk_PTE_Flags,
    Sail.BitVec.extractLsb, BitVec.extractLsb]
  bv_decide

theorem pteGetAZeroIff (w : BitVec 64) : pteGetA w = 0#1 ↔ w.toNat.testBit 6 = false := by
  rw [← pteGetATestbit]; exact mword1ZeroIff (pteGetA w)

theorem pteGetDZeroIff (w : BitVec 64) : pteGetD w = 0#1 ↔ w.toNat.testBit 7 = false := by
  rw [← pteGetDTestbit]; exact mword1ZeroIff (pteGetD w)

/-- The order on variant WORDS: same canonical form, A/D bits only grow. -/
def pteAdLe (w w' : BitVec 64) : Prop :=
  PtAdBits.pteCanon w = PtAdBits.pteCanon w' ∧
  (pteGetA w' = 0#1 → pteGetA w = 0#1) ∧
  (pteGetD w' = 0#1 → pteGetD w = 0#1)

theorem pteAdLeRefl (w : BitVec 64) : pteAdLe w w := ⟨rfl, id, id⟩

theorem pteAdLeTrans (w1 w2 w3 : BitVec 64) : pteAdLe w1 w2 → pteAdLe w2 w3 → pteAdLe w1 w3 := by
  rintro ⟨hc1, ha1, hd1⟩ ⟨hc2, ha2, hd2⟩
  exact ⟨hc1.trans hc2, fun h => ha1 (ha2 h), fun h => hd1 (hd2 h)⟩

/-- The byte-0 projection of the word order ... -/
theorem pteAdLeByte0 (w w' : BitVec 64) :
    pteAdLe w w' → adBitsLe (nthByte (n := 8) w 0) (nthByte (n := 8) w' 0) := by
  rintro ⟨_, hA, hD⟩
  rw [adBitsLe, nthByte0Testbit (m := 8) w 6 (by omega), nthByte0Testbit (m := 8) w' 6 (by omega),
    nthByte0Testbit (m := 8) w 7 (by omega), nthByte0Testbit (m := 8) w' 7 (by omega)]
  refine ⟨fun h6 => ?_, fun h7 => ?_⟩
  · cases E : w'.toNat.testBit 6
    · have h := (pteGetAZeroIff w).1 (hA ((pteGetAZeroIff w').2 E))
      rw [h] at h6; cases h6
    · rfl
  · cases E : w'.toNat.testBit 7
    · have h := (pteGetDZeroIff w).1 (hD ((pteGetDZeroIff w').2 E))
      rw [h] at h7; cases h7
    · rfl

/-- ... and its converse for two VARIANTS of one base. -/
theorem pteAdLeOfByte0 (w0 w w' : BitVec 64) :
    (∃ a d : BitVec 1, w = pteSetAD w0 a d) →
    (∃ a d : BitVec 1, w' = pteSetAD w0 a d) →
    adBitsLe (nthByte (n := 8) w 0) (nthByte (n := 8) w' 0) →
    pteAdLe w w' := by
  rintro ⟨a, d, hw⟩ ⟨a', d', hw'⟩ hle
  rw [adBitsLe, nthByte0Testbit (m := 8) w 6 (by omega), nthByte0Testbit (m := 8) w' 6 (by omega),
    nthByte0Testbit (m := 8) w 7 (by omega), nthByte0Testbit (m := 8) w' 7 (by omega)] at hle
  obtain ⟨h6, h7⟩ := hle
  refine ⟨?_, fun hA' => ?_, fun hD' => ?_⟩
  · rw [hw, hw', PtAdBits.pteCanonSetAd, PtAdBits.pteCanonSetAd]
  · apply (pteGetAZeroIff w).2
    have h' := (pteGetAZeroIff w').1 hA'
    exact Bool.eq_false_iff.2 fun hE => by rw [h6 hE] at h'; cases h'
  · apply (pteGetDZeroIff w).2
    have h' := (pteGetDZeroIff w').1 hD'
    exact Bool.eq_false_iff.2 fun hE => by rw [h7 hE] at h'; cases h'

/-! ### 4b. `update_PTE_Bits` only ORs bits, and firing is monotone

(`updatePTEBitsShape` is in §0, deviation 5.) -/

/-- A fired update only ORs the A/D bits: the pre-word is `pteAdLe` the written word. -/
theorem updatePTEBitsAdGe (w w' : BitVec 64) (acc : MemoryAccessType mem_payload) :
    update_PTE_Bits w acc = some w' → pteAdLe w w' := by
  intro hup
  obtain ⟨d, hw', hd⟩ := updatePTEBitsShape w w' acc hup
  subst hw'
  refine ⟨PtAdBits.pteCanonSetAd w 1#1 d ▸ rfl, fun hA' => ?_, fun hD' => ?_⟩
  · rw [pteGetASetAd] at hA'
    exact absurd hA' mw1NeMw0
  · rw [pteGetDSetAd] at hD'
    rcases hd with hd | hd
    · rw [hd] at hD'; exact absurd hD' mw1NeMw0
    · rw [← hd]; exact hD'

/-- The boolean core of firing monotonicity. -/
theorem firesMonoCore (dD dD' dA dA' : BitVec 1) (sd sa : Bool) :
    ((dD' == 0#1) = true → (dD == 0#1) = true) →
    ((dA' == 0#1) = true → (dA == 0#1) = true) →
    ((dD' == 0#1) && sd || (dA' == 0#1) && sa) = true →
    ((dD == 0#1) && sd || (dA == 0#1) && sa) = true := by
  revert dD dD' dA dA' sd sa
  decide

/-- WHETHER THE UPDATE FIRES IS MONOTONE DOWNWARD in the A/D order. -/
theorem updatePTEBitsFiresMono (w w' : BitVec 64) (acc : MemoryAccessType mem_payload) :
    pteAdLe w w' →
    (update_PTE_Bits w' acc).isSome = true →
    (update_PTE_Bits w acc).isSome = true := by
  rintro ⟨_, hA, hD⟩ hx
  rw [updatePTEBitsEq] at hx ⊢
  split at hx
  · rename_i hg
    have hg' := firesMonoCore (pteGetD w) (pteGetD w') (pteGetA w) (pteGetA w') _ _
      (fun h => (eqVec1ZeroTrue _).2 (hD ((eqVec1ZeroTrue _).1 h)))
      (fun h => (eqVec1ZeroTrue _).2 (hA ((eqVec1ZeroTrue _).1 h))) hg
    rw [if_pos hg']
    rfl
  · cases hx

/-- With the stale read below the fresh word, "a write-back happens" ⟺ "the FRESH word
needs bits". -/
theorem updatePTEBitsFiresLatest (wr wl : BitVec 64) (acc : MemoryAccessType mem_payload) :
    pteAdLe wr wl →
    ((update_PTE_Bits wr acc).isSome = true ∧ (update_PTE_Bits wl acc).isSome = true ↔
      (update_PTE_Bits wl acc).isSome = true) := by
  intro hle
  exact ⟨fun h => h.2, fun h => ⟨updatePTEBitsFiresMono wr wl acc hle h, h⟩⟩

/-! ### 4c. The fresh-derived log and its monotonicity -/

/-- A timestamp that writes `a` is at or below the latest writer. -/
theorem writesLeLatestTs (img : Image) (log : List Wmsg) (a : Int) (t : Nat) :
    (logByte img log t a).isSome = true → t ≤ latestTs log a := by
  intro hs
  rcases Nat.lt_or_ge (latestTs log a) t with hlt | hle
  · exfalso
    apply latestTsTop log a
    exact (writesInLogByte img log a _ _).2 ⟨t, hlt, logByteBounded img log t a hs, hs⟩
  · exact hle

/-- `logByte` restricted to a prefix agrees with the full log below the cut. -/
theorem logByteTake (img : Image) (log : List Wmsg) (i t : Nat) (a : Int) :
    t ≤ i → i ≤ log.length → logByte img (log.take i) t a = logByte img log t a := by
  intro ht hi
  have h := logByteApp img (log.take i) (log.drop i) t a (by rw [List.length_take]; omega)
  rw [List.take_append_drop] at h
  exact h.symm

/-- THE CAS DISCIPLINE, as a predicate on the log: every message writing byte `a` wrote a
value that DOMINATES the latest value at its own append time. -/
def wbyteFreshDerived (img : Image) (log : List Wmsg) (a : Int) : Prop :=
  ∀ (i : Nat) (m : Wmsg) (b : BitVec 8),
    log[i]? = some m → msgByte m a = some b →
    ∃ bf : BitVec 8,
      logByte img (log.take i) (latestTs (log.take i) a) a = some bf ∧ adBitsLe bf b

/-- THE BIT-MONOTONICITY THEOREM: under the CAS discipline the A/D bits of byte `a` are
monotone along the log. -/
theorem wbyteFreshDerivedMono (img : Image) (log : List Wmsg) (a : Int) :
    wbyteFreshDerived img log a →
    ∀ (t' t : Nat) (b b' : BitVec 8),
      t ≤ t' →
      logByte img log t a = some b →
      logByte img log t' a = some b' →
      adBitsLe b b' := by
  intro hfd t'
  induction t' using Nat.strongRecOn with
  | ind t' ih =>
  intro t b b' hle hb hb'
  by_cases hne : t = t'
  · subst hne
    rw [hb] at hb'
    injection hb' with hb'
    subst hb'
    exact adBitsLeRefl b
  · have hlt : t < t' := by omega
    obtain ⟨i', rfl⟩ : ∃ i', t' = i' + 1 := ⟨t' - 1, by omega⟩
    rw [logByteS] at hb'
    cases hm' : log[i']? with
    | none => rw [hm'] at hb'; cases hb'
    | some m' =>
      rw [hm'] at hb'
      change msgByte m' a = some b' at hb'
      obtain ⟨bf, hbf, hfb'⟩ := hfd i' m' b' hm' hb'
      have hi' : i' < log.length := lookup_lt_Some hm'
      have htsp : latestTs (log.take i') a ≤ i' := by
        have := latestTsLe (log.take i') a
        rw [List.length_take] at this
        omega
      have hbf' : logByte img log (latestTs (log.take i') a) a = some bf := by
        rw [← logByteTake img log i' _ a htsp (by omega)]; exact hbf
      have hbp : logByte img (log.take i') t a = some b := by
        rw [logByteTake img log i' t a (by omega) (by omega)]; exact hb
      have htle : t ≤ latestTs (log.take i') a :=
        writesLeLatestTs img (log.take i') a t (by rw [hbp]; rfl)
      exact adBitsLeTrans b bf b' (ih _ (by omega) t b bf htle hb hbf') hfb'

/-- ... hence the LATEST word dominates every value in the log. -/
theorem wbyteFreshDerivedLatest (img : Image) (log : List Wmsg) (a : Int) (t : Nat)
    (b bl : BitVec 8) :
    wbyteFreshDerived img log a →
    logByte img log t a = some b →
    logByte img log (latestTs log a) a = some bl →
    adBitsLe b bl := by
  intro hfd hb hbl
  exact wbyteFreshDerivedMono img log a hfd (latestTs log a) t b bl
    (writesLeLatestTs img log a t (by rw [hb]; rfl)) hb hbl

/-- Preservation of the discipline across an append: the new message's byte must dominate
the CURRENT latest value. -/
theorem wbyteFreshDerivedApp (img : Image) (log : List Wmsg) (m : Wmsg) (a : Int) :
    wbyteFreshDerived img log a →
    (∀ b : BitVec 8, msgByte m a = some b →
      ∃ bf : BitVec 8, logByte img log (latestTs log a) a = some bf ∧ adBitsLe bf b) →
    wbyteFreshDerived img (log ++ [m]) a := by
  intro hfd hnew i m0 b hi hb
  by_cases hlt : i < log.length
  · rw [lookup_app_l hlt] at hi
    obtain ⟨bf, hbf, hle⟩ := hfd i m0 b hi hb
    refine ⟨bf, ?_, hle⟩
    rw [List.take_append_of_le_length (by omega)]
    exact hbf
  · have hieq : i = log.length := by
      have := lookup_lt_Some hi
      simp only [List.length_append, List.length_singleton] at this
      omega
    subst hieq
    rw [list_lookup_middle rfl] at hi
    injection hi with hi
    subst hi
    obtain ⟨bf, hbf, hle⟩ := hnew b hb
    refine ⟨bf, ?_, hle⟩
    have htk : (log ++ [m]).take log.length = log := by simp
    rw [htk]
    exact hbf

/-- The CAS write-back instance of the append premise, at the window's byte 0. -/
theorem wbyteFreshDerivedWriteback (img : Image) (log : List Wmsg) (tid : Option Nat)
    (k : WmClass) (pa : PAddr) (acc : MemoryAccessType mem_payload) (fresh w' : BitVec 64)
    (v : BitVec (8 * 8)) :
    logByte img log (latestTs log (paZ pa)) (paZ pa) = some (nthByte (n := 8) fresh 0) →
    update_PTE_Bits fresh acc = some w' →
    v = w' →
    wbyteFreshDerived img log (paZ pa) →
    wbyteFreshDerived img (log ++ [wwriteMsg tid k pa 8 v]) (paZ pa) := by
  intro hlat hup hv hfd
  apply wbyteFreshDerivedApp img log _ _ hfd
  intro b hb
  have hb0 : msgByte (wwriteMsg tid k pa 8 v) (paZ pa) = some (nthByte v 0) := by
    have h := wwriteMsgByte tid k pa 8 v 0 (by omega)
    rwa [WeakInterp.accAddr0] at h
  rw [hb0] at hb
  injection hb with hb
  subst hb hv
  exact ⟨nthByte (n := 8) fresh 0, hlat, pteAdLeByte0 _ _ (updatePTEBitsAdGe fresh v acc hup)⟩

/-! ### 4d. The window-level capstone -/

/-- The latest window word, byte by byte — exactly what the invariant's 8 `γlat` elements
say. -/
def wwinLatest (s : Wmstate) (ra : PAddr) (wl : BitVec (8 * 8)) : Prop :=
  ∀ j : Nat, j < 8 →
    ∃ t : Nat, latestVal (wimg s) s.wmLog (WeakInterp.accAddr ra j) t (nthByte wl j)

/-- The latest window word is a variant. -/
theorem wwinLatestVariant (s : Wmstate) (ra : PAddr) (w0 : BitVec 64) (wl : BitVec (8 * 8)) :
    wlogVariants s.wmLog (paZ ra) w0 →
    wwinCovered s ra →
    wwinLatest s ra wl →
    ∃ a d : BitVec 1, wl = pteSetAD w0 a d := by
  intro hvar hcov hlat
  apply pteVariantMix
  intro j hj
  obtain ⟨t, hlv⟩ := hlat j hj
  have hne : t ≠ 0 := by
    rintro rfl
    exact hlv.2 (writesInToLen _ _ _ (hcov j hj))
  exact logByteVariant s ra w0 j t _ hj hvar hne hlv.1

/-- THE CAPSTONE: under the closure, the CAS discipline and the receipt's cover, EVERY
admissible (non-fetch) read of the window is a variant BELOW the latest word. -/
theorem wadmPteAdLeLatest (s : Wmstate) (rak : AkInfo) (ra : PAddr) (w0 : BitVec 64)
    (w wl : BitVec (8 * 8)) :
    wlogVariants s.wmLog (paZ ra) w0 →
    wbyteFreshDerived (wimg s) s.wmLog (paZ ra) →
    rak.akIfetch = false →
    wwinCovered s ra →
    wwinLatest s ra wl →
    wadm s rak ra 8 w →
    pteAdLe w wl := by
  intro hvar hfd hif hcov hlat hadm
  obtain ⟨aw, dw, hw⟩ := wadmVariant s rak ra w0 w hvar hif hcov hadm
  obtain ⟨al, dl, hwl⟩ := wwinLatestVariant s ra w0 wl hvar hcov hlat
  obtain ⟨t0, hok0⟩ := hadm 0 (by omega)
  have hb0 := hok0.1
  obtain ⟨tl, hlv⟩ := hlat 0 (by omega)
  have htl := latestValTs _ _ _ _ _ hlv
  have hbl := hlv.1
  rw [WeakInterp.accAddr0] at hb0 htl hbl
  have hble : adBitsLe (nthByte w 0) (nthByte wl 0) :=
    wbyteFreshDerivedMono (wimg s) s.wmLog (paZ ra) hfd tl t0 _ _
      (by rw [← htl]; exact writesLeLatestTs _ _ _ _ (by rw [hb0]; rfl)) hb0 hbl
  exact pteAdLeOfByte0 w0 w wl ⟨aw, dw, hw⟩ ⟨al, dl, hwl⟩ hble

/-! ## 5. The window's γlat elements, tied to §4's pure premises

The bundle itself is `WeakWord8.wlat8`; NOTHING is re-defined here. -/

section wlat8
variable {GF : BundledGFunctors} [WeakGS GF]

/-- The bundle IS the latest window word — §4d's `wwinLatest` premise, straight out of
`wlatInterp`. -/
theorem wlat8WinLatest (σ : Wmstate) (ea : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 64) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢ wlat8 (GF := GF) ea dq t w -∗ ⌜wwinLatest σ ea w⌝ := by
  have hl : ∀ (a : Int) (v : BitVec 8), wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatPointsto (GF := GF) a dq t v -∗ ⌜latestVal (imgZ σ.wmImg) σ.wmLog a t v⌝ :=
    fun a v => wand_intro (wlatLookup σ.wmImg σ.wmLog a dq t v)
  unfold wlat8
  iintro Hi ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases keepPure (hl _ _) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (hl _ _) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (hl _ _) $$ Hi H2 with ⟨%E2, Hi, -⟩
  icases keepPure (hl _ _) $$ Hi H3 with ⟨%E3, Hi, -⟩
  icases keepPure (hl _ _) $$ Hi H4 with ⟨%E4, Hi, -⟩
  icases keepPure (hl _ _) $$ Hi H5 with ⟨%E5, Hi, -⟩
  icases keepPure (hl _ _) $$ Hi H6 with ⟨%E6, Hi, -⟩
  ihave %E7 := hl _ _ $$ Hi H7
  ipureintro
  intro j hj
  refine ⟨t, ?_⟩
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  · exact E0
  · exact E1
  · exact E2
  · exact E3
  · exact E4
  · exact E5
  · exact E6
  · exact E7
  · omega

/-- ... and hence, under the closure + cover, a variant of the canonical leaf. -/
theorem wlat8Variant (σ : Wmstate) (ea : PAddr) (dq : DFrac) (t : Nat) (w0 : BitVec 64)
    (w : BitVec 64) :
    wlogVariants σ.wmLog (paZ ea) w0 →
    wwinCovered σ ea →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat8 (GF := GF) ea dq t w -∗ ⌜∃ a d : BitVec 1, w = pteSetAD w0 a d⌝ := by
  intro hvar hcov
  iintro Hi Hw
  ihave %hlat := wlat8WinLatest σ ea dq t w $$ Hi Hw
  ipureintro
  exact wwinLatestVariant σ ea w0 w hvar hcov hlat

end wlat8

end Weak
