/-
Weak: **W-SCO (A) — the instruction fetch** (plan rev 36 §C W-SCO (A) (1)(c): `fetch`, both
halfwords; the two places the walk is PRECISE about a value [R32.1][R33.1]).  Lean-only.

Under the boot register filter (`pma_regions = bootPMA`, `htif_tohost_base = none`):
* `pmaFetchRam`: a PMA region of `bootPMA` that admits an instruction fetch lies in RAM
  (`[0x8000_0000, 0x8800_0000)`; both I/O regions are non-executable and `override_PMA` keeps
  `executable`), so the fetch's physical address is not a device address;
* `fpWithinMmioRam`: `within_mmio_readable` answers `false` at a RAM address (`within_clint` /
  `within_sig` by constant arithmetic, the HTIF window by `htif_tohost_base = none`), so the
  fetch reaches `read_ram`, not `htif_load`;
* `goodCheckedMemReadIF`: `checked_mem_read (InstructionFetch ())` returns `Ok` only after a RAM
  instruction-fetch read (phase `fetch`), and continues at phase `fetch`;
* `goodFetch`: `fetch ()` returns `F_Base w` only at phase `fetch` (both arms: the 4-byte read,
  and the two halfword reads of a 4-byte instruction at `pc ≡ 2 (mod 4)` — the first halfword's
  read already moves to `fetch`; the second halfword's translation and read are relaxed
  footprints at phase `fetch`).
-/
import Weak.SailCycleOrderGood
import Weak.SailCycleOrderAllDecode

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp
open SailCycleOrderK SailCycleOrderGW

theorem leUOfToNatInt {n : Nat} (x y : BitVec n) (h : zopz0zIzJ_u x y = true) : x ≤ y := by
  unfold zopz0zIzJ_u at h
  simp only [decide_eq_true_eq, BitVec.toNatInt, Int.ofNat_eq_natCast, Int.ofNat_le] at h
  rw [BitVec.le_def]; exact h

theorem rangeSubsetRam (a s : BitVec 64)
    (h : range_subset a s 0x80000000#64 0x08000000#64 = true) : 0x80000000#64 ≤ a := by
  unfold range_subset at h
  simp only [Bool.and_eq_true] at h
  have h1 := leUOfToNatInt _ _ h.1
  have h2 := leUOfToNatInt _ _ h.2.1
  have h3 := leUOfToNatInt _ _ h.2.2
  bv_decide

/-- An instruction-fetch-admitting region of the boot PMA table lies in RAM. -/
theorem pmaFetchRam (pa : physaddr) (w : Nat) (r : PMA_Region) (pbmt : page_based_mem_type)
    (hm : matching_pma_region bootPMA pa w = some r)
    (hx : (override_PMA r.attributes pbmt).executable = true) :
    0x80000000 ≤ (bits_of_physaddr pa).toNat := by
  have hx' : r.attributes.executable = true := by
    unfold override_PMA at hx; split at hx <;> exact hx
  unfold matching_pma_region bootPMA at hm
  simp only [matching_pma_region_bits_range] at hm
  split at hm
  · simp only [Option.some.injEq] at hm; subst hm; simp at hx'
  · split at hm
    · simp only [Option.some.injEq] at hm; subst hm; simp at hx'
    · split at hm
      · rename_i h3
        have := rangeSubsetRam _ _ h3
        have h4 : (0x80000000#64).toNat ≤ (zero_extend (m := 64) (bits_of_physaddr pa)).toNat :=
          this
        simpa [zero_extend, Sail.BitVec.zeroExtend] using h4
      · simp at hm

theorem pmaClose (v : List PMA_Region) (hv : Rboot .pma_regions v) (pa : physaddr) (w : Nat)
    (r : PMA_Region) (pbmt : page_based_mem_type) (hm : matching_pma_region v pa w = some r)
    (hx : ¬Functions.not (override_PMA r.attributes pbmt).executable = true) :
    0x80000000 ≤ (bits_of_physaddr pa).toNat := by
  have hv' : v = bootPMA := hv
  subst hv'
  exact pmaFetchRam pa w r pbmt hm (by simpa [Functions.not] using hx)

-- The PMA check of an instruction fetch answers `Ok` only at a RAM address [R32.1].
set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpPmaCheckIF (pa : physaddr) (w : Nat) (pbmt : page_based_mem_type) (rc : Bool) :
    fp (fun r => ∀ i, r = .Ok i → 0x80000000 ≤ (bits_of_physaddr pa).toNat)
      (pmaCheck pa w (.InstructionFetch ()) pbmt rc) := by
  fp_walk_v
  all_goals (apply pmaClose <;> assumption)

-- The PMA-with-PMP check of an instruction fetch answers `Ok` only at a RAM address.
set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpCheckPmaIF (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr)
    (w : Nat) (rc : Bool) :
    fp (fun r => ∀ i, r = .Ok i → 0x80000000 ≤ (bits_of_physaddr pa).toNat)
      (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt priv pa w rc) := by
  fp_walk_v
  all_goals simp_all

theorem splitPos (w : Nat) (hw : 0 < w) (q p : Int) (hp : 0 < p)
    (h : (w == (q * p).toNat) = true) : 1 ≤ q := by
  have h' : w = (q * p).toNat := by simpa using h
  by_cases hq : 1 ≤ q
  · exact hq
  · exfalso
    have h1 : q * p ≤ 0 * p := Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hp)
    rw [Int.zero_mul] at h1
    omega

theorem pow2Pos (e : Int) : (0 : Int) < (2 : Int) ^ e := by
  show (0 : Int) < (2 : Int) ^ e.toNat
  exact Int.pow_pos (by decide)

-- `split_misaligned` of a positive width performs at least one access.
set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpSplitMisaligned (pa : physaddr) (w : Nat) (hw : 0 < w) (e : Nat)
    (sp : Splittability) :
    fp (fun p => 1 ≤ p.1) (split_misaligned pa w e sp) := by
  fp_walk_v
  all_goals first
    | (exact splitPos w hw _ _ (pow2Pos _) ‹_›)
    | omega
    | (simp only at *; omega)

theorem clintNotRam (a : BitVec 64) (w : Nat)
    (h : ((BitVec.toNatInt plat_clint_base ≤b BitVec.toNatInt a) &&
      ((BitVec.toNatInt a + (w : Int)) ≤b (BitVec.toNatInt plat_clint_base + BitVec.toNatInt plat_clint_size))) = true) :
    a.toNat < 0x80000000 := by
  have hb : BitVec.toNatInt plat_clint_base = 33554432 := by decide
  have hs : BitVec.toNatInt plat_clint_size = 786432 := by decide
  rw [hb, hs] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, BitVec.toNatInt, Int.ofNat_eq_natCast] at h
  omega

-- `within_mmio_readable` answers `false` at a RAM address [R33.1] (CLINT below RAM, no SiFive
-- test device, the HTIF window disabled by `htif_tohost_base = none`).
set_option maxHeartbeats 40000000 in
theorem fpWithinMmioRam (pa : physaddr) (w : Nat) (h : 0x80000000 ≤ (bits_of_physaddr pa).toNat) :
    fp (fun r => r = false) (within_mmio_readable pa w) := by
  fp_walk_v
  all_goals first
    | rfl
    | (exfalso; have := clintNotRam _ _ ‹_›; simp only [bits_of_physaddr] at h; omega)
    | (simp only [Rboot] at *; contradiction)

/-- The phase lemma of `within_mmio_readable` at a RAM address (phase-neutral, answers `false`). -/
@[g_reg] theorem gWithinMmioRam (pa : physaddr) (w : Nat) (h : 0x80000000 ≤ (bits_of_physaddr pa).toNat)
    (ph : Ph) :
    good (fun _ _ => True) Rboot (fun p r => p = ph ∧ r = false) ph (within_mmio_readable pa w) :=
  fpGood _ _ _ (fpWithinMmioRam pa w h) _ ph (fun _ hx => ⟨rfl, hx⟩)

theorem addInt0 (b : BitVec 64) (s : Int) : BitVec.addInt b ((↑(Int.toNat 0) : Int) * s) = b := by
  simp [BitVec.addInt]

theorem ramShift0 (pa : physaddr) (s : Int) (h : 0x80000000 ≤ (bits_of_physaddr pa).toNat) :
    0x80000000 ≤
      (bits_of_physaddr (physaddr.Physaddr (BitVec.addInt (bits_of_physaddr pa) ((↑(Int.toNat 0) : Int) * s)))).toNat := by
  rw [addInt0]; exact h

theorem devShift0 (pa : physaddr) (s : Int) (h : 0x80000000 ≤ (bits_of_physaddr pa).toNat) :
    devAddr (BitVec.addInt (bits_of_physaddr pa) ((↑(Int.toNat 0) : Int) * s)) = false := by
  rw [addInt0]
  simp only [devAddr, devBound, decide_eq_false_iff_not]
  omega

theorem ramShiftOk (pa : physaddr) (s : Int) (x : Phys_Mem_Access_Info)
    (h : ∀ i, (Result.Ok x : Result Phys_Mem_Access_Info ExceptionType) = Result.Ok i →
      0x80000000 ≤ (bits_of_physaddr pa).toNat) :
    0x80000000 ≤
      (bits_of_physaddr (physaddr.Physaddr (BitVec.addInt (bits_of_physaddr pa) ((↑(Int.toNat 0) : Int) * s)))).toNat :=
  ramShift0 pa s (h x rfl)

theorem devShiftOk (pa : physaddr) (s : Int) (x : Phys_Mem_Access_Info)
    (h : ∀ i, (Result.Ok x : Result Phys_Mem_Access_Info ExceptionType) = Result.Ok i →
      0x80000000 ≤ (bits_of_physaddr pa).toNat) :
    devAddr (BitVec.addInt (bits_of_physaddr pa) ((↑(Int.toNat 0) : Int) * s)) = false :=
  devShift0 pa s (h x rfl)

theorem dropOkFetch {k : Type} (r : Result (k × Unit) (physaddr × ExceptionType)) (p : Ph)
    (ha : ∀ v, r = .Ok v → p = .fetch) (b : k) (h : MemoryOpResult_drop_meta r = .Ok b) :
    p = .fetch := by
  cases r with
  | Ok v => exact ha _ rfl
  | Err e => cases h

set_option maxHeartbeats 40000000 in
/-- **The instruction-fetch read** [R32.1][R33.1]: `checked_mem_read (InstructionFetch ())`
answers `Ok` only after a RAM instruction-fetch read (phase `fetch`), from any phase. -/
@[g_reg] theorem gCheckedMemReadIF (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr)
    (w : Nat) (hw : 0 < w) (meta' : Bool) (ph : Ph) :
    good (fun _ _ => True) Rboot (fun p r => ∀ v, r = .Ok v → p = .fetch) ph
      (checked_mem_read (.InstructionFetch ()) pbmt priv pa w false false false meta') := by
  good_walk_v
  all_goals first
    | (exfalso; omega)
    | (apply devShiftOk; assumption)
    | (apply ramShiftOk; assumption)

set_option maxHeartbeats 40000000 in
@[g_reg] theorem gMemReadIF (pbmt : page_based_mem_type) (pa : physaddr) (w : Nat) (hw : 0 < w)
    (ph : Ph) :
    good (fun _ _ => True) Rboot (fun p r => ∀ v, r = .Ok v → p = .fetch) ph
      (mem_read (.InstructionFetch ()) pbmt pa w false false false) := by
  good_walk_v
  all_goals (apply dropOkFetch <;> assumption)

set_option maxHeartbeats 40000000 in
@[g_reg] theorem gFetchBytes (fs gs : BitVec 64) (w : Nat) (hw : 0 < w) (ph : Ph) :
    good (fun _ _ => True) Rboot (fun p r => ∀ b, r = .FetchBytes_Success b → p = .fetch) ph
      (fetch_bytes fs gs w) := by
  good_walk_v

set_option maxHeartbeats 40000000 in
@[g_reg] theorem gFetch :
    good (fun _ _ => True) Rboot (fun p fr => ∀ w, fr = .F_Base w → p = .fetch) .instr (fetch ()) := by
  good_walk_v

end SailCycleOrderFp
end Weak
