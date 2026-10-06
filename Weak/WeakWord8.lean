/-
Weak: **the `↦w₈` tower** (M4-prep).

Rocq: `iris/WeakWord8.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

THE EIGHT-BYTE TWIN of `WeakInstr`'s `↦w₄` tower and of `WeakStore`'s store-window
update.  Everything the weak layer owned so far was FOUR bytes wide -- the lock
word, the `started` flag -- but the kernel's own data is mostly eight (`lk->cpu`,
`lk->name`, every pointer, every `uint64`).  This file supplies the eight-byte
tower.

WHERE THE WIDTH-GENERIC PIECES LIVE: they moved down to the files whose width-4
statements they generalise -- `WeakStore.winsw` / `winswLookupIn` /
`winswLookupOut` / `wlatAgreeStoreW` (the `n`-fold window insert and its pure
update), `WeakInstr.wptByteFlatPin` / `wlatByteFlatGen` (the one-byte
flat/pinned bridges), and the `WeakInstr.wPLoadW` … `wQAmoAqW` family.  Every
eight-fold lemma below is eight applications of one of these.

  §2  `wlat8` -- the bare objective element bundle (the `wlat4` twin), and `wpt8`
      / `↦w₈` -- the owned eight-byte points-to, carrying 8-alignment and
      wrap-freedom exactly as `wpt4` does.  Eight explicit `∗`s, not a big
      separating conjunction.
  §3  the algebra: `wpt8Facts`, `wpt8Split`, `wpt8Agree`, `wpt8FlatPin`,
      `wpt8Flat`, `wpt8Pinned`, `wpt8Mono`, the seams `wpt8AtElems` /
      `wlat8Wpt8`, and `wlat8FlatGen`.
  §4  the store window at width 8: `wins8`, `wlatAgreeStore8`, `wlat8StorePrim`
      / `wlat8StoreGen` / `wlat8Store`, `wpt8Store`, and the owned altitude
      (`wpt8Own`, §4c).
  §5  the leaves: `wPLoad8` / `wPMem8` and `wwpLd8` / `wwpLd8Carry`; the store
      side `wVStore8` / `wQStore8` / `wwpSw8Post`; the acquire `wwpAmoswapDAqInv`
      (the `WeakInstr.wwpAmoswapWAqInv` twin); and the φ exporters.

Nothing here mentions `riscvStep`.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below).  Vocabulary as `Weak/WeakStore.lean`
   deviation 1: `S (length l)` ↦ `l.length + 1`, `acc_addr` ↦
   `WeakInterp.accAddr`, `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `N.to_nat 8` ↦
   `8`, `fin_to_nat c` ↦ `c.val`, `nth_byte w j` ↦ `nthByte (n := 8) w j` at
   `w : BitVec 64`, `wflat … !! a = Some v` ↦ `wflatMem … a = some v`, `m !! k` ↦
   `get? m k`, `⊑` ↦ `≤`, `monPred_at R V` ↦ `R.monPred_at V`, `DfracOwn 1` ↦
   `DFrac.own 1`, `bv 64` ↦ `BitVec 64`, `bv (8 * 8)` ↦ `BitVec (8 * 8)`.
2. STATEMENT SHAPES (WeakStore deviation 3): Rocq `A -∗ B -∗ C` (`A -∗ B ==∗ C`)
   is `A ⊢ B -∗ C` (`A ⊢ B -∗ |==> C`); Rocq `P ⊢ Q` stays.
3. `wQ_store8` / `wQ_amo_aq8` take `v : BitVec 64` (= `BitVec (8 * 8)` by
   `rfl`) as in Rocq; the width-generic `wQStoreW` is stated at `BitVec (8 * n)`
   (WeakInstr deviation 6).
4. `↦w₈ₒ`: Rocq's notation uses the ambient `cpu_id`; Lean has no ambient hart,
   so it is `a ↦w₈ₒ[c] w` (`wpt8Own c a w`), as WeakStore deviation 6.
5. `wlat8_store`'s `acc_wf a 8` premise is kept (unused, as in Rocq).
6. Lean-only helpers: `wpt8_at` / `wpt8Own_at` (the definitional decode of a held
   bundle, by `rfl`), `wlat8Unfold` (one `wlat8` unfolded, by `rfl`),
   `wins8Unfold` (the insert chain `wins8` is, by `rfl`), `bigSepL8` (the
   eight-element `[∗list]` unrolled, by `rfl`).
7. Rocq's `Print Assumptions` (§6) has no Lean counterpart (the lint bans axioms
   tree-wide).

**Rocq → Lean name map.**  `wlat8` `wlat8`, `wlat8_own` `wlat8Own`,
`wlat8_objective` `wlat8_objective`, `wlat8_timeless` `wlat8_timeless`, `wpt8`
`wpt8`, `wpt8_own` `wpt8Own`, `wpt8_own_of_wpt8` `wpt8OwnOfWpt8`,
`wpt8_own_facts` `wpt8OwnFacts`, `wpt8_own_mono` `wpt8OwnMono`,
`wpt8_persistent` `wpt8_persistent`, `wpt8_timeless` `wpt8_timeless`,
`wpt8_facts` `wpt8Facts`, `wpt8_split` `wpt8Split`, `wpt8_agree` `wpt8Agree`,
`wpt8_flat_pin` `wpt8FlatPin`, `wpt8_flat` `wpt8Flat`, `wpt8_pinned`
`wpt8Pinned`, `wpt8_mono` `wpt8Mono`, `wpt8_at_elems` `wpt8AtElems`,
`wlat8_wpt8` `wlat8Wpt8`, `wlat8_flat_gen` `wlat8FlatGen`, `wins8` `wins8`,
`wins8_winsw` `wins8Winsw`, `wins8_lookup_in` `wins8LookupIn`,
`wins8_lookup_out` `wins8LookupOut`, `wlat_agree_store8` `wlatAgreeStore8`,
`wlat8_store_prim` `wlat8StorePrim`, `wlat8_store_prim_own`
`wlat8StorePrimOwn`, `wlat8_store_gen` `wlat8StoreGen`, `wlat8_store`
`wlat8Store`, `wpt8_store` `wpt8Store`, `wpt8_own_at_elems` `wpt8OwnAtElems`,
`wlat8_own_wpt8_own` `wlat8OwnWpt8Own`, `wpt8_store_own` `wpt8StoreOwn`,
`wpt8_own_flat_pin` `wpt8OwnFlatPin`, `wpt8_own_flat` `wpt8OwnFlat`,
`wpt8_own_pinned` `wpt8OwnPinned`, `wP_load_w_4` `wPLoadW4`, `wP_mem_w_4`
`wPMemW4`, `wV_store_w_4` `wVStoreW4`, `wV_amo_aq_w_4` `wVAmoAqW4`,
`wV_load_w_4` `wVLoadW4`, `wQ_load_w_4` `wQLoadW4`, `wQ_store_w_4`
`wQStoreW4`, `wQ_amo_aq_w_4` `wQAmoAqW4`, `wP_load8` `wPLoad8`, `wP_mem8`
`wPMem8`, `wV_store8` `wVStore8`, `wV_amo_aq8` `wVAmoAq8`, `wQ_store8`
`wQStore8`, `wQ_amo_aq8` `wQAmoAq8`, `wQ_store8_wV` `wQStore8WV`,
`wQ_amo_aq8_store` `wQAmoAq8Store`, `wQ_amo_aq8_gain` `wQAmoAq8Gain`,
`wQ_amo_aq8_excl` `wQAmoAq8Excl`, `wwp_ld8` `wwpLd8`, `wwp_ld8_own`
`wwpLd8Own`, `wwp_sd8_pmem_own` `wwpSd8PmemOwn`, `wwp_ld8_own_carry`
`wwpLd8OwnCarry`, `wwp_ld8_carry` `wwpLd8Carry`, `wwp_sd8_pmem` `wwpSd8Pmem`,
`wwp_sw8_post` `wwpSw8Post`, `wwp_amoswap_d_aq_inv` `wwpAmoswapDAqInv`,
`nv_ok_wpt8` `nvOkWpt8`, `nv_ok_wpt8_own` `nvOkWpt8Own`, `nv_free_wlat8`
`nvFreeWlat8`, `nv_ok_wlat8_own` `nvOkWlat8Own`.  Notations: `a ↦w₈{dq} w`
kept; `a ↦w₈ₒ w` ↦ `a ↦w₈ₒ[c] w`.

**Not ported:** nothing -- every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakStore

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wcds

/-! ## 2. The two eight-byte bundles -/

section word8
variable {GF : BundledGFunctors} [WeakGS GF]

/-- THE BARE ELEMENT BUNDLE -- an `IProp`, hence OBJECTIVE. -/
def wlat8 (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 64) : IProp GF :=
  iprop(wlatPointsto (GF := GF) (WeakInterp.accAddr a 0) dq t (nthByte (n := 8) w 0) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr a 1) dq t (nthByte (n := 8) w 1) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr a 2) dq t (nthByte (n := 8) w 2) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr a 3) dq t (nthByte (n := 8) w 3) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr a 4) dq t (nthByte (n := 8) w 4) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr a 5) dq t (nthByte (n := 8) w 5) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr a 6) dq t (nthByte (n := 8) w 6) ∗
    wlatPointsto (GF := GF) (WeakInterp.accAddr a 7) dq t (nthByte (n := 8) w 7))

/-- THE OWNED EIGHT-BYTE ELEMENT BUNDLE (the `WeakStore.wlat4Own` twin). -/
def wlat8Own (c : CPU) (a : PAddr) (t : Nat) (w : BitVec 64) : IProp GF :=
  iprop(wlatElem (GF := GF) (WeakInterp.accAddr a 0) (DFrac.own 1) t (nthByte (n := 8) w 0) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 0) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 1) (DFrac.own 1) t (nthByte (n := 8) w 1) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 1) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 2) (DFrac.own 1) t (nthByte (n := 8) w 2) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 2) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 3) (DFrac.own 1) t (nthByte (n := 8) w 3) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 3) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 4) (DFrac.own 1) t (nthByte (n := 8) w 4) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 4) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 5) (DFrac.own 1) t (nthByte (n := 8) w 5) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 5) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 6) (DFrac.own 1) t (nthByte (n := 8) w 6) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 6) ∗
    wlatElem (GF := GF) (WeakInterp.accAddr a 7) (DFrac.own 1) t (nthByte (n := 8) w 7) ∗
      wownSt (GF := GF) c (WeakInterp.accAddr a 7))

instance wlat8_objective (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 64) :
    Objective (iprop(⎡wlat8 (GF := GF) a dq t w⎤) : VProp GF) := by
  infer_instance

instance wlat8_timeless (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 64) :
    Timeless (wlat8 (GF := GF) a dq t w) := by
  unfold wlat8; infer_instance

/-- THE OWNED EIGHT-BYTE POINTS-TO: 8-alignment, wrap-freedom, eight weak bytes. -/
def wpt8 (a : PAddr) (dq : DFrac) (w : BitVec 64) : VProp GF :=
  iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝ ∗ ⌜accWf a 8⌝ ∗
    (WeakInterp.accAddr a 0 ↦w{dq} nthByte (n := 8) w 0) ∗
    (WeakInterp.accAddr a 1 ↦w{dq} nthByte (n := 8) w 1) ∗
    (WeakInterp.accAddr a 2 ↦w{dq} nthByte (n := 8) w 2) ∗
    (WeakInterp.accAddr a 3 ↦w{dq} nthByte (n := 8) w 3) ∗
    (WeakInterp.accAddr a 4 ↦w{dq} nthByte (n := 8) w 4) ∗
    (WeakInterp.accAddr a 5 ↦w{dq} nthByte (n := 8) w 5) ∗
    (WeakInterp.accAddr a 6 ↦w{dq} nthByte (n := 8) w 6) ∗
    (WeakInterp.accAddr a 7 ↦w{dq} nthByte (n := 8) w 7))

def wpt8Own (c : CPU) (a : PAddr) (w : BitVec 64) : VProp GF :=
  iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝ ∗ ⌜accWf a 8⌝ ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 0) (nthByte (n := 8) w 0) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 1) (nthByte (n := 8) w 1) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 2) (nthByte (n := 8) w 2) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 3) (nthByte (n := 8) w 3) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 4) (nthByte (n := 8) w 4) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 5) (nthByte (n := 8) w 5) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 6) (nthByte (n := 8) w 6) ∗
    wptOwnH (GF := GF) c (WeakInterp.accAddr a 7) (nthByte (n := 8) w 7))

/-- The definitional decode of a held bundle (Lean-only). -/
theorem wpt8_at (a : PAddr) (dq : DFrac) (w : BitVec 64) (ws : Wstate) :
    vwpHold (wpt8 (GF := GF) a dq w) ws ⊣⊢
      iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝ ∗ ⌜accWf a 8⌝ ∗
        vwpHold (WeakInterp.accAddr a 0 ↦w{dq} nthByte (n := 8) w 0 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 1 ↦w{dq} nthByte (n := 8) w 1 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 2 ↦w{dq} nthByte (n := 8) w 2 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 3 ↦w{dq} nthByte (n := 8) w 3 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 4 ↦w{dq} nthByte (n := 8) w 4 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 5 ↦w{dq} nthByte (n := 8) w 5 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 6 ↦w{dq} nthByte (n := 8) w 6 : VProp GF) ws ∗
        vwpHold (WeakInterp.accAddr a 7 ↦w{dq} nthByte (n := 8) w 7 : VProp GF) ws) := .rfl

/-- The definitional decode of a held owned bundle (Lean-only). -/
theorem wpt8Own_at (c : CPU) (a : PAddr) (w : BitVec 64) (ws : Wstate) :
    vwpHold (wpt8Own (GF := GF) c a w) ws ⊣⊢
      iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝ ∗ ⌜accWf a 8⌝ ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 0) (nthByte (n := 8) w 0)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 1) (nthByte (n := 8) w 1)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 2) (nthByte (n := 8) w 2)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 3) (nthByte (n := 8) w 3)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 4) (nthByte (n := 8) w 4)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 5) (nthByte (n := 8) w 5)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 6) (nthByte (n := 8) w 6)) ws ∗
        vwpHold (wptOwnH (GF := GF) c (WeakInterp.accAddr a 7) (nthByte (n := 8) w 7)) ws) :=
  .rfl

theorem wpt8OwnOfWpt8 (c : CPU) (a : PAddr) (w : BitVec 64) :
    wpt8 (GF := GF) a (DFrac.own 1) w ⊢ wpt8Own c a w := by
  unfold wpt8 wpt8Own
  iintro ⟨%h1, %h2, H0, H1, H2, H3, H4, H5, H6, H7⟩
  isplitr
  · ipureintro; exact h1
  isplitr
  · ipureintro; exact h2
  isplitl [H0]
  · iapply wptOwnH_of_wpt c _ _; iexact H0
  isplitl [H1]
  · iapply wptOwnH_of_wpt c _ _; iexact H1
  isplitl [H2]
  · iapply wptOwnH_of_wpt c _ _; iexact H2
  isplitl [H3]
  · iapply wptOwnH_of_wpt c _ _; iexact H3
  isplitl [H4]
  · iapply wptOwnH_of_wpt c _ _; iexact H4
  isplitl [H5]
  · iapply wptOwnH_of_wpt c _ _; iexact H5
  isplitl [H6]
  · iapply wptOwnH_of_wpt c _ _; iexact H6
  · iapply wptOwnH_of_wpt c _ _; iexact H7

theorem wpt8OwnFacts (c : CPU) (a : PAddr) (w : BitVec 64) :
    wpt8Own (GF := GF) c a w ⊢ ⌜is_aligned_paddr (.Physaddr a) 8 = true ∧ accWf a 8⌝ := by
  unfold wpt8Own
  iintro ⟨%h1, %h2, -⟩
  ipureintro
  exact ⟨h1, h2⟩

theorem wpt8OwnMono (c : CPU) (a : PAddr) (w : BitVec 64) (ws ws' : Wstate) :
    wsLe ws ws' → vwpHold (wpt8Own (GF := GF) c a w) ws ⊢ vwpHold (wpt8Own (GF := GF) c a w) ws' :=
  fun h => vwpHold_mono _ h

instance wpt8_persistent (a : PAddr) (w : BitVec 64) :
    Persistent (wpt8 (GF := GF) a DFrac.discard w) := by
  unfold wpt8; infer_instance

instance wpt8_timeless (a : PAddr) (q : Qp) (w : BitVec 64) :
    Timeless (wpt8 (GF := GF) a (DFrac.own q) w) := by
  unfold wpt8; infer_instance

/-! ## 3. The algebra -/

theorem wpt8Facts (a : PAddr) (dq : DFrac) (w : BitVec 64) :
    wpt8 (GF := GF) a dq w ⊢ ⌜is_aligned_paddr (.Physaddr a) 8 = true ∧ accWf a 8⌝ := by
  unfold wpt8
  iintro ⟨%h1, %h2, -⟩
  ipureintro
  exact ⟨h1, h2⟩

/-- FRACTION SPLIT / JOIN, byte by byte from `wpt_split`. -/
theorem wpt8Split (a : PAddr) (q1 q2 : Qp) (w : BitVec 64) :
    wpt8 (GF := GF) a (DFrac.own (q1 + q2)) w ⊣⊢
      iprop(wpt8 (GF := GF) a (DFrac.own q1) w ∗ wpt8 (GF := GF) a (DFrac.own q2) w) := by
  unfold wpt8
  constructor
  · iintro ⟨%hal, %hacc, H0, H1, H2, H3, H4, H5, H6, H7⟩
    icases (wpt_split _ q1 q2 _).mp $$ H0 with ⟨A0, B0⟩
    icases (wpt_split _ q1 q2 _).mp $$ H1 with ⟨A1, B1⟩
    icases (wpt_split _ q1 q2 _).mp $$ H2 with ⟨A2, B2⟩
    icases (wpt_split _ q1 q2 _).mp $$ H3 with ⟨A3, B3⟩
    icases (wpt_split _ q1 q2 _).mp $$ H4 with ⟨A4, B4⟩
    icases (wpt_split _ q1 q2 _).mp $$ H5 with ⟨A5, B5⟩
    icases (wpt_split _ q1 q2 _).mp $$ H6 with ⟨A6, B6⟩
    icases (wpt_split _ q1 q2 _).mp $$ H7 with ⟨A7, B7⟩
    isplitl [A0 A1 A2 A3 A4 A5 A6 A7]
    · isplitr
      · ipureintro; exact hal
      isplitr
      · ipureintro; exact hacc
      iframe A0 A1 A2 A3 A4 A5 A6 A7
    · isplitr
      · ipureintro; exact hal
      isplitr
      · ipureintro; exact hacc
      iframe B0 B1 B2 B3 B4 B5 B6 B7
  · iintro ⟨⟨%hal, %hacc, A0, A1, A2, A3, A4, A5, A6, A7⟩,
      ⟨-, -, B0, B1, B2, B3, B4, B5, B6, B7⟩⟩
    isplitr
    · ipureintro; exact hal
    isplitr
    · ipureintro; exact hacc
    isplitl [A0 B0]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A0 B0
    isplitl [A1 B1]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A1 B1
    isplitl [A2 B2]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A2 B2
    isplitl [A3 B3]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A3 B3
    isplitl [A4 B4]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A4 B4
    isplitl [A5 B5]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A5 B5
    isplitl [A6 B6]
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A6 B6
    · iapply (wpt_split _ q1 q2 _).mpr; iframe A7 B7

theorem wpt8Agree (a : PAddr) (dq1 : DFrac) (w1 : BitVec 64) (dq2 : DFrac) (w2 : BitVec 64) :
    iprop(wpt8 (GF := GF) a dq1 w1 ∗ wpt8 (GF := GF) a dq2 w2) ⊢ (⌜w1 = w2⌝ : VProp GF) := by
  unfold wpt8
  iintro ⟨⟨-, -, A0, A1, A2, A3, A4, A5, A6, A7⟩, ⟨-, -, B0, B1, B2, B3, B4, B5, B6, B7⟩⟩
  ihave %E0 := wpt_agree _ dq1 _ dq2 _ $$ [A0 B0]
  · iframe A0 B0
  ihave %E1 := wpt_agree _ dq1 _ dq2 _ $$ [A1 B1]
  · iframe A1 B1
  ihave %E2 := wpt_agree _ dq1 _ dq2 _ $$ [A2 B2]
  · iframe A2 B2
  ihave %E3 := wpt_agree _ dq1 _ dq2 _ $$ [A3 B3]
  · iframe A3 B3
  ihave %E4 := wpt_agree _ dq1 _ dq2 _ $$ [A4 B4]
  · iframe A4 B4
  ihave %E5 := wpt_agree _ dq1 _ dq2 _ $$ [A5 B5]
  · iframe A5 B5
  ihave %E6 := wpt_agree _ dq1 _ dq2 _ $$ [A6 B6]
  · iframe A6 B6
  ihave %E7 := wpt_agree _ dq1 _ dq2 _ $$ [A7 B7]
  · iframe A7 B7
  ipureintro
  apply bvEqOfBytes (n := 8) w1 w2
  intro j hj
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

/-- THE FLAT + PINNED FACTS over the window, in one pass. -/
theorem wpt8FlatPin (σ : Wmstate) (a : PAddr) (dq : DFrac) (w : BitVec 64) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8 (GF := GF) a dq w) σ.wmWs -∗
        ⌜accWf a 8 ∧
         ∀ j : Nat, j < 8 →
           wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j) ∧
           pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf
  iintro Hi Hpt
  icases (wpt8_at a dq w σ.wmWs).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases keepPure (wptByteFlatPin σ a 8 dq _ 0 hwf hacc (by omega)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wptByteFlatPin σ a 8 dq _ 1 hwf hacc (by omega)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wptByteFlatPin σ a 8 dq _ 2 hwf hacc (by omega)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  icases keepPure (wptByteFlatPin σ a 8 dq _ 3 hwf hacc (by omega)) $$ Hi H3 with ⟨%E3, Hi, -⟩
  icases keepPure (wptByteFlatPin σ a 8 dq _ 4 hwf hacc (by omega)) $$ Hi H4 with ⟨%E4, Hi, -⟩
  icases keepPure (wptByteFlatPin σ a 8 dq _ 5 hwf hacc (by omega)) $$ Hi H5 with ⟨%E5, Hi, -⟩
  icases keepPure (wptByteFlatPin σ a 8 dq _ 6 hwf hacc (by omega)) $$ Hi H6 with ⟨%E6, Hi, -⟩
  ihave %E7 := wptByteFlatPin σ a 8 dq _ 7 hwf hacc (by omega) $$ Hi H7
  ipureintro
  refine ⟨hacc, ?_⟩
  intro j hj
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

/-- WHAT THE FLAT PROJECTION HOLDS over the window. -/
theorem wpt8Flat (σ : Wmstate) (a : PAddr) (dq : DFrac) (w : BitVec 64) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8 (GF := GF) a dq w) σ.wmWs -∗
        ⌜∀ j : Nat, j < 8 →
           wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt8FlatPin σ a dq w hwf $$ Hi Hpt
  ipureintro
  exact fun j hj => (h.2 j hj).1

/-- ... and that the window is PINNED for this hart. -/
theorem wpt8Pinned (σ : Wmstate) (a : PAddr) (dq : DFrac) (w : BitVec 64) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8 (GF := GF) a dq w) σ.wmWs -∗
        ⌜∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt8FlatPin σ a dq w hwf $$ Hi Hpt
  ipureintro
  exact fun j hj => (h.2 j hj).2

/-- MONOTONICITY across a step. -/
theorem wpt8Mono (a : PAddr) (dq : DFrac) (w : BitVec 64) (ws ws' : Wstate) :
    wsLe ws ws' → vwpHold (wpt8 (GF := GF) a dq w) ws ⊢ vwpHold (wpt8 (GF := GF) a dq w) ws' :=
  fun h => vwpHold_mono _ h

/-- THE DECODE OF AN OWNED BUNDLE: eight elements at eight independent timestamps. -/
theorem wpt8AtElems (a : PAddr) (dq : DFrac) (w : BitVec 64) (ws : Wstate) :
    vwpHold (wpt8 (GF := GF) a dq w) ws ⊢
      iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝ ∗ ⌜accWf a 8⌝ ∗
        ∃ t0 t1 t2 t3 t4 t5 t6 t7 : Nat,
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 0) dq t0 (nthByte (n := 8) w 0) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 1) dq t1 (nthByte (n := 8) w 1) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 2) dq t2 (nthByte (n := 8) w 2) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 3) dq t3 (nthByte (n := 8) w 3) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 4) dq t4 (nthByte (n := 8) w 4) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 5) dq t5 (nthByte (n := 8) w 5) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 6) dq t6 (nthByte (n := 8) w 6) ∗
          wlatPointsto (GF := GF) (WeakInterp.accAddr a 7) dq t7 (nthByte (n := 8) w 7)) := by
  iintro Hpt
  icases (wpt8_at a dq w ws).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (wpt_at _ dq _ ws).mp $$ H0 with ⟨%t0, H0, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H1 with ⟨%t1, H1, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H2 with ⟨%t2, H2, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H3 with ⟨%t3, H3, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H4 with ⟨%t4, H4, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H5 with ⟨%t5, H5, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H6 with ⟨%t6, H6, -⟩
  icases (wpt_at _ dq _ ws).mp $$ H7 with ⟨%t7, H7, -⟩
  isplitr
  · ipureintro; exact hal
  isplitr
  · ipureintro; exact hacc
  iexists t0, t1, t2, t3, t4, t5, t6, t7
  iframe H0 H1 H2 H3 H4 H5 H6 H7

/-- ... and the converse seam: an element bundle whose timestamp the floor covers IS an
owned eight-byte points-to. -/
theorem wlat8Wpt8 (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 64) (ws : Wstate) :
    is_aligned_paddr (.Physaddr a) 8 = true →
    accWf a 8 →
    (∀ j : Nat, j < 8 → t ≤ flr (wsView ws) (WeakInterp.accAddr a j)) →
    wlat8 (GF := GF) a dq t w ⊢ vwpHold (wpt8 (GF := GF) a dq w) ws := by
  intro hal hacc hfl
  refine BIBase.Entails.trans ?_ (wpt8_at a dq w ws).mpr
  unfold wlat8
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  isplitr
  · ipureintro; exact hal
  isplitr
  · ipureintro; exact hacc
  isplitl [H0]
  · iapply wpt_at_intro _ dq _ t ws (hfl 0 (by omega)); iexact H0
  isplitl [H1]
  · iapply wpt_at_intro _ dq _ t ws (hfl 1 (by omega)); iexact H1
  isplitl [H2]
  · iapply wpt_at_intro _ dq _ t ws (hfl 2 (by omega)); iexact H2
  isplitl [H3]
  · iapply wpt_at_intro _ dq _ t ws (hfl 3 (by omega)); iexact H3
  isplitl [H4]
  · iapply wpt_at_intro _ dq _ t ws (hfl 4 (by omega)); iexact H4
  isplitl [H5]
  · iapply wpt_at_intro _ dq _ t ws (hfl 5 (by omega)); iexact H5
  isplitl [H6]
  · iapply wpt_at_intro _ dq _ t ws (hfl 6 (by omega)); iexact H6
  · iapply wpt_at_intro _ dq _ t ws (hfl 7 (by omega)); iexact H7

/-- READING THE WORD OUT OF THE ELEMENTS, with no ownership and no view hypothesis. -/
theorem wlat8FlatGen (σ : Wmstate) (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 64) :
    wlogWf σ.wmLog → accWf a 8 →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat8 (GF := GF) a dq t w -∗
        ⌜(∀ j : Nat, j < 8 →
            wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)) ∧
          (∀ j : Nat, j < 8 → latestTs σ.wmLog (WeakInterp.accAddr a j) = t)⌝ := by
  intro hwf hacc
  unfold wlat8
  iintro Hi ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases keepPure (wlatByteFlatGen σ a 8 dq t _ 0 hwf hacc (by omega)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ a 8 dq t _ 1 hwf hacc (by omega)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ a 8 dq t _ 2 hwf hacc (by omega)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ a 8 dq t _ 3 hwf hacc (by omega)) $$ Hi H3 with ⟨%E3, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ a 8 dq t _ 4 hwf hacc (by omega)) $$ Hi H4 with ⟨%E4, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ a 8 dq t _ 5 hwf hacc (by omega)) $$ Hi H5 with ⟨%E5, Hi, -⟩
  icases keepPure (wlatByteFlatGen σ a 8 dq t _ 6 hwf hacc (by omega)) $$ Hi H6 with ⟨%E6, Hi, -⟩
  ihave %E7 := wlatByteFlatGen σ a 8 dq t _ 7 hwf hacc (by omega) $$ Hi H7
  ipureintro
  have hall : ∀ j : Nat, j < 8 →
      wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j) ∧
      latestTs σ.wmLog (WeakInterp.accAddr a j) = t := by
    intro j hj
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
  exact ⟨fun j hj => (hall j hj).1, fun j hj => (hall j hj).2⟩

end word8

notation:50 a:50 " ↦w₈{" dq "} " w:50 => wpt8 a dq w

/-! ## 4. The store window at width 8 -/

def wins8 (a : PAddr) (T : Nat) (v : BitVec 64) (mm : GMapF Int (Nat × BitVec 8)) :
    GMapF Int (Nat × BitVec 8) :=
  winsw (m := 8) a T v 8 mm

theorem wins8Winsw (a : PAddr) (T : Nat) (v : BitVec 64) (mm : GMapF Int (Nat × BitVec 8)) :
    wins8 a T v mm = winsw (m := 8) a T v 8 mm := rfl

/-- The insert chain eight successive `ghost_map_update`s leave behind (Lean-only). -/
theorem wins8Unfold (a : PAddr) (T : Nat) (v : BitVec 64) (mm : GMapF Int (Nat × BitVec 8)) :
    wins8 a T v mm =
      insert (insert (insert (insert (insert (insert (insert (insert mm
        (WeakInterp.accAddr a 0) (T, nthByte (n := 8) v 0))
        (WeakInterp.accAddr a 1) (T, nthByte (n := 8) v 1))
        (WeakInterp.accAddr a 2) (T, nthByte (n := 8) v 2))
        (WeakInterp.accAddr a 3) (T, nthByte (n := 8) v 3))
        (WeakInterp.accAddr a 4) (T, nthByte (n := 8) v 4))
        (WeakInterp.accAddr a 5) (T, nthByte (n := 8) v 5))
        (WeakInterp.accAddr a 6) (T, nthByte (n := 8) v 6))
        (WeakInterp.accAddr a 7) (T, nthByte (n := 8) v 7) := rfl

theorem wins8LookupIn (a : PAddr) (T : Nat) (v : BitVec 64) (mm : GMapF Int (Nat × BitVec 8))
    (j : Nat) :
    j < 8 → get? (wins8 a T v mm) (WeakInterp.accAddr a j) = some (T, nthByte (n := 8) v j) :=
  fun hj => winswLookupIn a T v 8 mm j hj

theorem wins8LookupOut (a : PAddr) (T : Nat) (v : BitVec 64) (mm : GMapF Int (Nat × BitVec 8))
    (z : Int) : ¬ (paZ a ≤ z ∧ z < paZ a + 8) → get? (wins8 a T v mm) z = get? mm z := by
  intro hout
  apply winswLookupOut
  intro j hj heq
  apply hout
  subst heq
  unfold WeakInterp.accAddr
  omega

/-- THE EIGHT-BYTE WINDOW UPDATE, pure: the `n := 8` instance. -/
theorem wlatAgreeStore8 (img : Image) (log : List Wmsg) (tid : Option Nat) (k : WmClass)
    (a : PAddr) (v : BitVec 64) (mm : GMapF Int (Nat × BitVec 8)) :
    wlatAgree img log mm →
    wlatAgree img (log ++ [wwriteMsg tid k a 8 v]) (wins8 a (log.length + 1) v mm) :=
  wlatAgreeStoreW img log tid k a 8 v mm

section store8
variable {GF : BundledGFunctors} [WeakGS GF]

/-- The eight-element `[∗list]`, unrolled (Lean-only). -/
theorem bigSepL8 {PROP : Type _} [BI PROP] {A : Type _} (Φ : A → PROP)
    (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    ([∗list] x ∈ [x0, x1, x2, x3, x4, x5, x6, x7], Φ x) ⊣⊢
      iprop(Φ x0 ∗ Φ x1 ∗ Φ x2 ∗ Φ x3 ∗ Φ x4 ∗ Φ x5 ∗ Φ x6 ∗ Φ x7 ∗ emp) := .rfl

/-- The definitional unfolding of one `wlat8` (Lean-only). -/
theorem wlat8Unfold (a : PAddr) (dq : DFrac) (t : Nat) (w : BitVec 64) :
    wlat8 (GF := GF) a dq t w =
      iprop(wlatPointsto (GF := GF) (WeakInterp.accAddr a 0) dq t (nthByte (n := 8) w 0) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 1) dq t (nthByte (n := 8) w 1) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 2) dq t (nthByte (n := 8) w 2) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 3) dq t (nthByte (n := 8) w 3) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 4) dq t (nthByte (n := 8) w 4) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 5) dq t (nthByte (n := 8) w 5) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 6) dq t (nthByte (n := 8) w 6) ∗
        wlatPointsto (GF := GF) (WeakInterp.accAddr a 7) dq t (nthByte (n := 8) w 7)) := rfl

/-- THE PRIMITIVE.  Eight full-fraction elements over the window, at arbitrary
pre-timestamps and pre-values, one eight-byte message appended. -/
theorem wlat8StorePrim (tid : Option Nat) (k : WmClass) (σ : Wmstate) (a : PAddr) (v : BitVec 64)
    (t0 t1 t2 t3 t4 t5 t6 t7 : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    k ≠ .WCplain →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 0) (DFrac.own 1) t0 b0 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 1) (DFrac.own 1) t1 b1 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 2) (DFrac.own 1) t2 b2 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 3) (DFrac.own 1) t3 b3 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 4) (DFrac.own 1) t4 b4 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 5) (DFrac.own 1) t5 b5 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 6) (DFrac.own 1) t6 b6 -∗
      wlatPointsto (GF := GF) (WeakInterp.accAddr a 7) (DFrac.own 1) t7 b7 -∗
        |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid k a 8 v]) ∗
          wlat8 (GF := GF) a (DFrac.own 1) (σ.wmLog.length + 1) v) := by
  intro hk
  unfold wlatInterp wlatPointsto wlat8 wlatElem wclean wcdsEl
  iintro ⟨%mm, %mc, Hauth, %hag, Hc, %hagc⟩ ⟨H0, C0⟩ ⟨H1, C1⟩ ⟨H2, C2⟩ ⟨H3, C3⟩
    ⟨H4, C4⟩ ⟨H5, C5⟩ ⟨H6, C6⟩ ⟨H7, C7⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 0) $$ Hauth H0 with ⟨Hauth, H0⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 1) $$ Hauth H1 with ⟨Hauth, H1⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 2) $$ Hauth H2 with ⟨Hauth, H2⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 3) $$ Hauth H3 with ⟨Hauth, H3⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 4) $$ Hauth H4 with ⟨Hauth, H4⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 5) $$ Hauth H5 with ⟨Hauth, H5⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 6) $$ Hauth H6 with ⟨Hauth, H6⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 7) $$ Hauth H7 with ⟨Hauth, H7⟩
  -- T2-0: the window's eight bytes are pinned CLEAN by the very fragments handed in
  icombine Hc C0 gives %K0
  icombine Hc C1 gives %K1
  icombine Hc C2 gives %K2
  icombine Hc C3 gives %K3
  icombine Hc C4 gives %K4
  icombine Hc C5 gives %K5
  icombine Hc C6 gives %K6
  icombine Hc C7 gives %K7
  imodintro
  isplitl [Hauth Hc]
  · iexists _, mc
    iframe Hauth Hc
    isplit
    · ipureintro
      rw [← wins8Unfold]
      exact wlatAgreeStore8 _ _ tid k a v mm hag
    · ipureintro
      refine wcdsAgreeNonplain8 _ tid k a v mc WClean hk rfl ?_ hagc
      intro j hj
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
      · exact K0
      · exact K1
      · exact K2
      · exact K3
      · exact K4
      · exact K5
      · exact K6
      · exact K7
      · omega
  · unfold wlatPointsto wlatElem wclean wcdsEl
    iframe H0 C0 H1 C1 H2 C2 H3 C3 H4 C4 H5 C5 H6 C6 H7 C7

/-- THE OWNED PRIMITIVE at width 8 -- the `wlat4StorePrimOwn` twin. -/
theorem wlat8StorePrimOwn (c : CPU) (k : WmClass) (σ : Wmstate) (a : PAddr) (v : BitVec 64)
    (t0 t1 t2 t3 t4 t5 t6 t7 : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlatElem (GF := GF) (WeakInterp.accAddr a 0) (DFrac.own 1) t0 b0 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 0) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 1) (DFrac.own 1) t1 b1 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 1) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 2) (DFrac.own 1) t2 b2 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 2) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 3) (DFrac.own 1) t3 b3 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 3) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 4) (DFrac.own 1) t4 b4 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 4) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 5) (DFrac.own 1) t5 b5 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 5) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 6) (DFrac.own 1) t6 b6 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 6) -∗
      wlatElem (GF := GF) (WeakInterp.accAddr a 7) (DFrac.own 1) t7 b7 -∗
        wownSt (GF := GF) c (WeakInterp.accAddr a 7) -∗
        |==> (wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg (some c.val) k a 8 v]) ∗
          wlat8Own (GF := GF) c a (σ.wmLog.length + 1) v) := by
  unfold wlatInterp wlat8Own wlatElem
  iintro ⟨%mm, %mc, Hauth, %hag, Hc, %hagc⟩ H0 C0 H1 C1 H2 C2 H3 C3 H4 C4 H5 C5 H6 C6 H7 C7
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 0) $$ Hauth H0 with ⟨Hauth, H0⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 1) $$ Hauth H1 with ⟨Hauth, H1⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 2) $$ Hauth H2 with ⟨Hauth, H2⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 3) $$ Hauth H3 with ⟨Hauth, H3⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 4) $$ Hauth H4 with ⟨Hauth, H4⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 5) $$ Hauth H5 with ⟨Hauth, H5⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 6) $$ Hauth H6 with ⟨Hauth, H6⟩
  imod ghost_map_update (σ.wmLog.length + 1, nthByte (n := 8) v 7) $$ Hauth H7 with ⟨Hauth, H7⟩
  imod wcdsStoreList c (wwriteMsg (some c.val) k a 8 v) σ.wmLog
      [WeakInterp.accAddr a 0, WeakInterp.accAddr a 1, WeakInterp.accAddr a 2,
        WeakInterp.accAddr a 3, WeakInterp.accAddr a 4, WeakInterp.accAddr a 5,
        WeakInterp.accAddr a 6, WeakInterp.accAddr a 7] mc rfl (wwriteMsgZs8 _ _ a v) hagc
      $$ Hc [C0 C1 C2 C3 C4 C5 C6 C7]
      with ⟨%mc', Hc, %hagc', Hl⟩
  · iapply (bigSepL8 (fun z => wownSt (GF := GF) c z) _ _ _ _ _ _ _ _).2
    iframe C0 C1 C2 C3 C4 C5 C6 C7
  icases (bigSepL8 (fun z => wownSt (GF := GF) c z) _ _ _ _ _ _ _ _).1 $$ Hl with
    ⟨C0, C1, C2, C3, C4, C5, C6, C7, -⟩
  imodintro
  isplitl [Hauth Hc]
  · iexists _, mc'
    iframe Hauth Hc
    isplit
    · ipureintro
      rw [← wins8Unfold]
      exact wlatAgreeStore8 _ _ _ k a v mm hag
    · ipureintro
      exact hagc'
  · iframe H0 C0 H1 C1 H2 C2 H3 C3 H4 C4 H5 C5 H6 C6 H7 C7

/-- THE BUNDLE UPDATE at an explicitly described post-state. -/
theorem wlat8StoreGen (tid : Option Nat) (k : WmClass) (σ σ' : Wmstate) (a : PAddr) (t : Nat)
    (w v : BitVec 64) :
    k ≠ .WCplain →
    σ'.wmImg = σ.wmImg →
    σ'.wmLog = σ.wmLog ++ [wwriteMsg tid k a 8 v] →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat8 (GF := GF) a (DFrac.own 1) t w -∗
        |==> (wlatInterp (GF := GF) σ'.wmImg σ'.wmLog ∗
          wlat8 (GF := GF) a (DFrac.own 1) (σ.wmLog.length + 1) v) := by
  intro hk himg hlog
  rw [himg, hlog]
  rw [wlat8Unfold a _ t w]
  iintro Hi ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  iapply wlat8StorePrim tid k σ a v t t t t t t t t _ _ _ _ _ _ _ _ hk
    $$ Hi H0 H1 H2 H3 H4 H5 H6 H7

/-- ... and at the interpreter's OWN write post-state.  `accWf` is kept, unused. -/
theorem wlat8Store (tid : Option Nat) (σ : Wmstate) (ak : AkInfo) (a : PAddr) (t : Nat)
    (w : BitVec 64) (v : BitVec (8 * 8)) :
    ak.akLatest = true →
    accWf a 8 →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat8 (GF := GF) a (DFrac.own 1) t w -∗
        |==> (wlatInterp (GF := GF) (wwritePost tid σ ak a 8 v).wmImg
            (wwritePost tid σ ak a 8 v).wmLog ∗
          wlat8 (GF := GF) a (DFrac.own 1) (σ.wmLog.length + 1) v) := by
  intro hlt _
  exact wlat8StoreGen tid (wmClassOf ak σ.wmWs) σ (wwritePost tid σ ak a 8 v) a t w v
    (by simp [wmClassOf, hlt]) (wwritePostImg tid σ ak a 8 v) (wwritePostLog tid σ ak a 8 v)

/-- THE STORE RULE FOR THE BUNDLE, owned altitude. -/
theorem wpt8Store (tid : Option Nat) (σ : Wmstate) (ak : AkInfo) (a : PAddr) (w : BitVec 64)
    (v : BitVec (8 * 8)) :
    ak.akLatest = true →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8 (GF := GF) a (DFrac.own 1) w) σ.wmWs -∗
        |==> (wlatInterp (GF := GF) (wwritePost tid σ ak a 8 v).wmImg
            (wwritePost tid σ ak a 8 v).wmLog ∗
          vwpHold (wpt8 (GF := GF) a (DFrac.own 1) v) (wwritePost tid σ ak a 8 v).wmWs) := by
  intro hlt
  rw [wwritePostImg tid σ ak a 8 v, wwritePostLog tid σ ak a 8 v]
  iintro Hi Hpt
  icases wpt8AtElems a _ w σ.wmWs $$ Hpt with
    ⟨%hal, %hacc, %t0, %t1, %t2, %t3, %t4, %t5, %t6, %t7, H0, H1, H2, H3, H4, H5, H6, H7⟩
  imod wlat8StorePrim tid (wmClassOf ak σ.wmWs) σ a v t0 t1 t2 t3 t4 t5 t6 t7 _ _ _ _ _ _ _ _
      (by simp [wmClassOf, hlt]) $$ Hi H0 H1 H2 H3 H4 H5 H6 H7 with ⟨Hi, Hl⟩
  imodintro
  iframe Hi
  iapply wlat8Wpt8 a _ (σ.wmLog.length + 1) v _ hal hacc
    (fun j hj => flrWwritePost tid σ ak a 8 v j hj)
  iexact Hl

/-! ### 4c. THE OWNED ALTITUDE at width 8 -/

theorem wpt8OwnAtElems (c : CPU) (a : PAddr) (w : BitVec 64) (ws : Wstate) :
    vwpHold (wpt8Own (GF := GF) c a w) ws ⊢
      iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝ ∗ ⌜accWf a 8⌝ ∗
        ∃ t0 t1 t2 t3 t4 t5 t6 t7 : Nat,
          wlatElem (GF := GF) (WeakInterp.accAddr a 0) (DFrac.own 1) t0 (nthByte (n := 8) w 0) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 0) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 1) (DFrac.own 1) t1 (nthByte (n := 8) w 1) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 1) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 2) (DFrac.own 1) t2 (nthByte (n := 8) w 2) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 2) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 3) (DFrac.own 1) t3 (nthByte (n := 8) w 3) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 3) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 4) (DFrac.own 1) t4 (nthByte (n := 8) w 4) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 4) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 5) (DFrac.own 1) t5 (nthByte (n := 8) w 5) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 5) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 6) (DFrac.own 1) t6 (nthByte (n := 8) w 6) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 6) ∗
          wlatElem (GF := GF) (WeakInterp.accAddr a 7) (DFrac.own 1) t7 (nthByte (n := 8) w 7) ∗
            wownSt (GF := GF) c (WeakInterp.accAddr a 7)) := by
  iintro Hpt
  icases (wpt8Own_at c a w ws).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H0 with ⟨%t0, H0, S0, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H1 with ⟨%t1, H1, S1, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H2 with ⟨%t2, H2, S2, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H3 with ⟨%t3, H3, S3, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H4 with ⟨%t4, H4, S4, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H5 with ⟨%t5, H5, S5, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H6 with ⟨%t6, H6, S6, -⟩
  icases (wptOwnH_at c _ _ ws).mp $$ H7 with ⟨%t7, H7, S7, -⟩
  isplitr
  · ipureintro; exact hal
  isplitr
  · ipureintro; exact hacc
  iexists t0, t1, t2, t3, t4, t5, t6, t7
  iframe H0 S0 H1 S1 H2 S2 H3 S3 H4 S4 H5 S5 H6 S6 H7 S7

theorem wlat8OwnWpt8Own (c : CPU) (a : PAddr) (t : Nat) (w : BitVec 64) (ws : Wstate) :
    is_aligned_paddr (.Physaddr a) 8 = true →
    accWf a 8 →
    (∀ j : Nat, j < 8 → t ≤ flr (wsView ws) (WeakInterp.accAddr a j)) →
    wlat8Own (GF := GF) c a t w ⊢ vwpHold (wpt8Own (GF := GF) c a w) ws := by
  intro hal hacc hfl
  refine BIBase.Entails.trans ?_ (wpt8Own_at c a w ws).mpr
  unfold wlat8Own
  iintro ⟨H0, S0, H1, S1, H2, S2, H3, S3, H4, S4, H5, S5, H6, S6, H7, S7⟩
  isplitr
  · ipureintro; exact hal
  isplitr
  · ipureintro; exact hacc
  isplitl [H0 S0]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 0 (by omega)); iframe H0 S0
  isplitl [H1 S1]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 1 (by omega)); iframe H1 S1
  isplitl [H2 S2]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 2 (by omega)); iframe H2 S2
  isplitl [H3 S3]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 3 (by omega)); iframe H3 S3
  isplitl [H4 S4]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 4 (by omega)); iframe H4 S4
  isplitl [H5 S5]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 5 (by omega)); iframe H5 S5
  isplitl [H6 S6]
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 6 (by omega)); iframe H6 S6
  · iapply wptOwnH_at_intro c _ _ t ws (hfl 7 (by omega)); iframe H7 S7

theorem wpt8StoreOwn (c : CPU) (σ : Wmstate) (ak : AkInfo) (a : PAddr) (w : BitVec 64)
    (v : BitVec (8 * 8)) :
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8Own (GF := GF) c a w) σ.wmWs -∗
        |==> (wlatInterp (GF := GF) (wwritePost (some c.val) σ ak a 8 v).wmImg
            (wwritePost (some c.val) σ ak a 8 v).wmLog ∗
          vwpHold (wpt8Own (GF := GF) c a v) (wwritePost (some c.val) σ ak a 8 v).wmWs) := by
  rw [wwritePostImg (some c.val) σ ak a 8 v, wwritePostLog (some c.val) σ ak a 8 v]
  iintro Hi Hpt
  icases wpt8OwnAtElems c a w σ.wmWs $$ Hpt with
    ⟨%hal, %hacc, %t0, %t1, %t2, %t3, %t4, %t5, %t6, %t7,
      H0, S0, H1, S1, H2, S2, H3, S3, H4, S4, H5, S5, H6, S6, H7, S7⟩
  imod wlat8StorePrimOwn c (wmClassOf ak σ.wmWs) σ a v t0 t1 t2 t3 t4 t5 t6 t7 _ _ _ _ _ _ _ _
      $$ Hi H0 S0 H1 S1 H2 S2 H3 S3 H4 S4 H5 S5 H6 S6 H7 S7 with ⟨Hi, Hl⟩
  imodintro
  iframe Hi
  iapply wlat8OwnWpt8Own c a (σ.wmLog.length + 1) v _ hal hacc
    (fun j hj => flrWwritePost (some c.val) σ ak a 8 v j hj)
  iexact Hl

theorem wpt8OwnFlatPin (c : CPU) (σ : Wmstate) (a : PAddr) (w : BitVec 64) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8Own (GF := GF) c a w) σ.wmWs -∗
        ⌜accWf a 8 ∧ ∀ j : Nat, j < 8 →
          wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j) ∧
          pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf
  iintro Hi Hpt
  icases (wpt8Own_at c a w σ.wmWs).mp $$ Hpt with ⟨%hal, %hacc, H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 8 _ 0 hwf hacc (by omega)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 8 _ 1 hwf hacc (by omega)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 8 _ 2 hwf hacc (by omega)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 8 _ 3 hwf hacc (by omega)) $$ Hi H3 with ⟨%E3, Hi, -⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 8 _ 4 hwf hacc (by omega)) $$ Hi H4 with ⟨%E4, Hi, -⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 8 _ 5 hwf hacc (by omega)) $$ Hi H5 with ⟨%E5, Hi, -⟩
  icases keepPure (wptOwnHByteFlatPin c σ a 8 _ 6 hwf hacc (by omega)) $$ Hi H6 with ⟨%E6, Hi, -⟩
  ihave %E7 := wptOwnHByteFlatPin c σ a 8 _ 7 hwf hacc (by omega) $$ Hi H7
  ipureintro
  refine ⟨hacc, ?_⟩
  intro j hj
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

theorem wpt8OwnFlat (c : CPU) (σ : Wmstate) (a : PAddr) (w : BitVec 64) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8Own (GF := GF) c a w) σ.wmWs -∗
        ⌜∀ j : Nat, j < 8 →
          wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt8OwnFlatPin c σ a w hwf $$ Hi Hpt
  ipureintro
  exact fun j hj => (h.2 j hj).1

theorem wpt8OwnPinned (c : CPU) (σ : Wmstate) (a : PAddr) (w : BitVec 64) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8Own (GF := GF) c a w) σ.wmWs -∗
        ⌜∀ j : Nat, j < 8 → pinnedRead σ (WeakInterp.accAddr a j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt8OwnFlatPin c σ a w hwf $$ Hi Hpt
  ipureintro
  exact fun j hj => (h.2 j hj).2

end store8

notation:50 a:50 " ↦w₈ₒ[" c "] " w:50 => wpt8Own c a w

/-! ## 5. The leaves

THE SUBSUMPTION CHECKS: `WeakInstr`'s width-4 families are the `n := 4` instances of
its width-generic family, on the nose. -/

theorem wPLoadW4 (ea : PAddr) : wPLoadW 4 ea = wPLoad ea := rfl
theorem wPMemW4 (ea : PAddr) : wPMemW 4 ea = wPMem ea := rfl
theorem wVStoreW4 (ea : PAddr) : wVStoreW 4 ea = wVStore ea := rfl
theorem wVAmoAqW4 (ea : PAddr) : wVAmoAqW 4 ea = wVAmoAq ea := rfl
theorem wVLoadW4 (ea : PAddr) : wVLoadW 4 ea = wVLoad ea := rfl
theorem wQLoadW4 (ea : PAddr) : wQLoadW 4 ea = wQLoad ea := rfl
theorem wQStoreW4 (tid : Option Nat) (ea : PAddr) (v : BitVec 32) :
    wQStoreW 4 tid ea v = wQStore tid ea v := rfl
theorem wQAmoAqW4 (tid : Option Nat) (ea : PAddr) (v : BitVec 32) :
    wQAmoAqW 4 tid ea v = wQAmoAq tid ea v := rfl

/-! The width-8 names. -/

def wPLoad8 (ea : PAddr) : Wmstate → Prop := wPLoadW 8 ea
def wPMem8 (ea : PAddr) : Wmstate → Prop := wPMemW 8 ea
def wVStore8 (ea : PAddr) : Wmstate → Wstate → Prop := wVStoreW 8 ea
def wVAmoAq8 (ea : PAddr) : Wmstate → Wstate → Prop := wVAmoAqW 8 ea
def wQStore8 (tid : Option Nat) (ea : PAddr) (v : BitVec 64) : Wmstate → Wmstate → Prop :=
  wQStoreW 8 tid ea v
def wQAmoAq8 (tid : Option Nat) (ea : PAddr) (v : BitVec 64) : Wmstate → Wmstate → Prop :=
  wQAmoAqW 8 tid ea v

theorem wQStore8WV (tid : Option Nat) (ea : PAddr) (v : BitVec 64) (σ σ' : Wmstate) :
    wQStore8 tid ea v σ σ' → wVStore8 ea σ σ'.wmWs :=
  fun h => h.2.2.2

theorem wQAmoAq8Store (tid : Option Nat) (ea : PAddr) (v : BitVec 64) (σ σ' : Wmstate) :
    wQAmoAq8 tid ea v σ σ' → wQStore8 tid ea v σ σ' :=
  fun h => h.1

theorem wQAmoAq8Gain (tid : Option Nat) (ea : PAddr) (v : BitVec 64) (σ σ' : Wmstate) :
    wQAmoAq8 tid ea v σ σ' → wVAmoAq8 ea σ σ'.wmWs :=
  fun h => h.2.1

theorem wQAmoAq8Excl (tid : Option Nat) (ea : PAddr) (v : BitVec 64) (σ σ' : Wmstate) :
    wQAmoAq8 tid ea v σ σ' → σ'.wmLog = σ.wmLog ++ [wwriteMsg tid .WCexcl ea 8 v] :=
  fun h => h.2.2

section leaves8
variable {GF : BundledGFunctors} [WeakGS GF]

/-! ### 5a. `ld` -- the plain 8-byte LOAD, owned form -/

theorem wwpLd8 (σ : Wmstate) (ea : PAddr) (dq : DFrac) (w : BitVec 64) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8 (GF := GF) ea dq w) σ.wmWs -∗
        ⌜wPLoad8 ea σ ∧
         ∀ j : Nat, j < 8 →
           wflatMem σ.wmImg σ.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt8FlatPin σ ea dq w hwf $$ Hi Hpt
  ipureintro
  obtain ⟨hacc, hall⟩ := h
  exact ⟨⟨hacc, fun j hj => (hall j hj).2⟩, fun j hj => (hall j hj).1⟩

/-- The OWNED twin. -/
theorem wwpLd8Own (c : CPU) (σ : Wmstate) (ea : PAddr) (w : BitVec 64) :
    wlogWf σ.wmLog →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      vwpHold (wpt8Own (GF := GF) c ea w) σ.wmWs -∗
        ⌜wPLoad8 ea σ ∧
         ∀ j : Nat, j < 8 →
           wflatMem σ.wmImg σ.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)⌝ := by
  intro hwf
  iintro Hi Hpt
  ihave %h := wpt8OwnFlatPin c σ ea w hwf $$ Hi Hpt
  ipureintro
  obtain ⟨hacc, hall⟩ := h
  exact ⟨⟨hacc, fun j hj => (hall j hj).2⟩, fun j hj => (hall j hj).1⟩

theorem wwpSd8PmemOwn (c : CPU) (σ : Wmstate) (ea : PAddr) (w : BitVec 64) :
    vwpHold (wpt8Own (GF := GF) c ea w) σ.wmWs ⊢ ⌜wPMem8 ea σ⌝ := by
  iintro Hpt
  icases (wpt8Own_at c ea w σ.wmWs).mp $$ Hpt with ⟨-, %hacc, -⟩
  ipureintro
  exact hacc

theorem wwpLd8OwnCarry (c : CPU) (σ σ' : Wmstate) (t : ExecSt) (ea : PAddr) (w : BitVec 64) :
    wstepPost σ σ' t →
    vwpHold (wpt8Own (GF := GF) c ea w) σ.wmWs ⊢ vwpHold (wpt8Own (GF := GF) c ea w) σ'.wmWs :=
  fun hp => wpt8OwnMono c ea w _ _ (wstepPostWsLe σ σ' t hp)

/-- ... and the frame: the loaded doubleword survives the step. -/
theorem wwpLd8Carry (σ σ' : Wmstate) (t : ExecSt) (ea : PAddr) (dq : DFrac) (w : BitVec 64) :
    wstepPost σ σ' t →
    vwpHold (wpt8 (GF := GF) ea dq w) σ.wmWs ⊢ vwpHold (wpt8 (GF := GF) ea dq w) σ'.wmWs :=
  fun hp => wpt8Mono ea dq w _ _ (wstepPostWsLe σ σ' t hp)

/-! ### 5b. `sd` -- the 8-byte STORE -/

theorem wwpSd8Pmem (σ : Wmstate) (ea : PAddr) (dq : DFrac) (w : BitVec 64) :
    vwpHold (wpt8 (GF := GF) ea dq w) σ.wmWs ⊢ ⌜wPMem8 ea σ⌝ := by
  iintro Hpt
  icases (wpt8_at ea dq w σ.wmWs).mp $$ Hpt with ⟨-, %hacc, -⟩
  ipureintro
  exact hacc

/-- The store's own post-view, in the form the next instruction consumes. -/
theorem wwpSw8Post (σ : Wmstate) (ws' : Wstate) (ea : PAddr) :
    wVStore8 ea σ ws' →
    ∀ j : Nat, j < 8 →
      viewByte (WeakInterp.accAddr ea j) (σ.wmLog.length + 1) ≤ wsView ws' :=
  fun hQ j hj => (viewByte_le _ _ _).mpr (hQ j hj)

/-! ### 5c. `amoswap.d.aq` -- the eight-byte ACQUIRE, invariant form -/

theorem wwpAmoswapDAqInv (R : VProp GF) (σ : Wmstate) (ws' : Wstate) (ea : PAddr) (dq : DFrac)
    (t : Nat) (w : BitVec 64) :
    wlogWf σ.wmLog →
    accWf ea 8 →
    wVAmoAq8 ea σ ws' →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wlat8 (GF := GF) ea dq t w -∗
      R.monPred_at (viewScl t) -∗
        ⌜wPMem8 ea σ⌝ ∗
        ⌜∀ j : Nat, j < 8 →
           wflatMem σ.wmImg σ.wmLog (ea + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)⌝ ∗
        ⌜viewScl t ≤ wsView ws'⌝ ∗
        vwpHold R ws' := by
  intro hwf hacc hQ
  iintro Hi Hl HR
  ihave %h := wlat8FlatGen σ ea dq t w hwf hacc $$ Hi Hl
  obtain ⟨hflat, hts⟩ := h
  have hscl : viewScl t ≤ wsView ws' := by
    have := hQ 0 (by omega)
    rw [hts 0 (by omega)] at this
    exact this
  isplitr
  · ipureintro; exact hacc
  isplitr
  · ipureintro; exact hflat
  isplitr
  · ipureintro; exact hscl
  iapply vwpHold_intro (viewScl t) R ws' hscl
  iexact HR

/-! ### The φ exporters at width 8 -/

theorem nvOkWpt8 (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (dq : DFrac) (w : BitVec 64) (ws : Wstate) :
    wlatInterp (GF := GF) img log ⊢
      vwpHold (wpt8 (GF := GF) a dq w) ws -∗
        ⌜∀ j : Nat, j < 8 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  iintro Hi Hpt
  icases wpt8AtElems a dq w ws $$ Hpt with
    ⟨-, -, %t0, %t1, %t2, %t3, %t4, %t5, %t6, %t7, H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H3 with ⟨%E3, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H4 with ⟨%E4, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H5 with ⟨%E5, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfPointsto img log c _ dq _ _)) $$ Hi H6 with ⟨%E6, Hi, -⟩
  ihave %E7 := wand_intro (nvOkOfPointsto img log c _ dq _ _) $$ Hi H7
  ipureintro
  intro j hj
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

theorem nvOkWpt8Own (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (w : BitVec 64) (ws : Wstate) :
    wlatInterp (GF := GF) img log ⊢
      vwpHold (wpt8Own (GF := GF) c a w) ws -∗
        ⌜∀ j : Nat, j < 8 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  iintro Hi Hpt
  icases wpt8OwnAtElems c a w ws $$ Hpt with
    ⟨-, -, %t0, %t1, %t2, %t3, %t4, %t5, %t6, %t7,
      -, S0, -, S1, -, S2, -, S3, -, S4, -, S5, -, S6, -, S7⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S2 with ⟨%E2, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S3 with ⟨%E3, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S4 with ⟨%E4, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S5 with ⟨%E5, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S6 with ⟨%E6, Hi, -⟩
  ihave %E7 := wand_intro (nvOkOfOwnSt img log c _) $$ Hi S7
  ipureintro
  intro j hj
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

/-- The `nvFree` form off a PLAIN eight-byte bundle (agent-independent). -/
theorem nvFreeWlat8 (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) (dq : DFrac)
    (t : Nat) (w : BitVec 64) :
    wlatInterp (GF := GF) img log ⊢
      wlat8 (GF := GF) a dq t w -∗
        ⌜∀ j : Nat, j < 8 → nvFree log (WeakInterp.accAddr a j)⌝ := by
  unfold wlat8
  iintro Hi ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases keepPure (wand_intro (nvFreeOfPointsto img log _ dq _ _)) $$ Hi H0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvFreeOfPointsto img log _ dq _ _)) $$ Hi H1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvFreeOfPointsto img log _ dq _ _)) $$ Hi H2 with ⟨%E2, Hi, -⟩
  icases keepPure (wand_intro (nvFreeOfPointsto img log _ dq _ _)) $$ Hi H3 with ⟨%E3, Hi, -⟩
  icases keepPure (wand_intro (nvFreeOfPointsto img log _ dq _ _)) $$ Hi H4 with ⟨%E4, Hi, -⟩
  icases keepPure (wand_intro (nvFreeOfPointsto img log _ dq _ _)) $$ Hi H5 with ⟨%E5, Hi, -⟩
  icases keepPure (wand_intro (nvFreeOfPointsto img log _ dq _ _)) $$ Hi H6 with ⟨%E6, Hi, -⟩
  ihave %E7 := wand_intro (nvFreeOfPointsto img log _ dq _ _) $$ Hi H7
  ipureintro
  intro j hj
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

theorem nvOkWlat8Own (c : CPU) (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr)
    (t : Nat) (w : BitVec 64) :
    wlatInterp (GF := GF) img log ⊢
      wlat8Own (GF := GF) c a t w -∗
        ⌜∀ j : Nat, j < 8 → nvOk log c (WeakInterp.accAddr a j)⌝ := by
  unfold wlat8Own
  iintro Hi ⟨-, S0, -, S1, -, S2, -, S3, -, S4, -, S5, -, S6, -, S7⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S0 with ⟨%E0, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S1 with ⟨%E1, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S2 with ⟨%E2, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S3 with ⟨%E3, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S4 with ⟨%E4, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S5 with ⟨%E5, Hi, -⟩
  icases keepPure (wand_intro (nvOkOfOwnSt img log c _)) $$ Hi S6 with ⟨%E6, Hi, -⟩
  ihave %E7 := wand_intro (nvOkOfOwnSt img log c _) $$ Hi S7
  ipureintro
  intro j hj
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

end leaves8

end Weak
