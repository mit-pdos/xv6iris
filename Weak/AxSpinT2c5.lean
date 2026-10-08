/-
Weak: **THEOREM 2 / certificate (a′): THE INITIAL TEXT + PAGE-TABLE IMAGE `σX`** and the
image / text / translation premises of `allocpidOpen` (AxSpinT2b) on it — the eight text
premises, `textFixed` for A, B, C, `AxSpinApA.MapOk` (the page table `AxSpinT2pt.tX` maps every
aligned data word the segment touches VA = PA, load / store / AMO), the graph-image facts
(`lk->cpu` = 0, nextpid = 1) and the 16-alignment of the frames.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §C.6 (in ../xv6iris-lbthm2).

## What this file proves

§1 THE IMAGE.  `σX`: memory = the kernel text `[_entry, etext)` and the three table pages of
`tX`, read off `AxSpinT2c1.imgByte` (so it agrees with the graph image `AxSpinT2c1.img`), NOTHING
else — AxSpinT2b's VACUITY TRAP: `textFixed G i (imgS σi)` pins every read of hart `i` inside
`σi`'s domain to `σi`'s byte, so the data (nextpid, pid_lock, cpus, proc[], the stacks) must
not be in `σX` (it is in the GRAPH image only).
§2 PAGES.  `slot0All` (every L0 slot of `tX` is in `σX`), the fetch pages `pageX0` / `pageX1`
(`AxSpinTextCerts.pageOk σX tX` for pages 0x80000 / 0x80001) and the generic data-page facts
(`chkRW`, `updRW`, `canonLow`, `paLow`, `ofIntToNat`).
§3 TEXT.  `acquireTextX`, `mycpuTextX`, `pushOffTextX`, `holdingTextX`, `popOffTextX`,
`releaseTextX`, `allocpidTextX`, `tailTextX` — every conjunct by one of AxSpinTextCerts'
constructors on `pageX0` / `pageX1`, residual by `decide +kernel` over the image.
§4 `textFixedX` — `textFixed (gtAdGd (gT3 E)) h (imgS σX)` for h ∈ {0, 1, 2}, every `E`
(`σX` agrees with the graph image; no read of the literal rows touches `σX`'s domain,
`readsOffLit`).
§5 `mapOkX` — `AxSpinApA.MapOk σX tX i S p` for ANY hart `i < NCPU`, frame base in `stack0` and
slot in `proc[]` (in particular (a′)'s three harts, `mapOk3`): every touched data word lies in
pages 0x8000a .. 0x80018 of the identity map.
§5b `tlbExactW` — `tlbExact tX tlbW` (the TLB conjunct of `ctrlOkS` in `entryOk`; the other
`ctrlOkSW` conjuncts of `regsE` are NOT proved here).
§6 IMAGE PREMISES.  `imgClb` (AxSpinT2b `Himgc`: `lk->cpu` is 0 in the graph image), `imgNp`
(`Himgn` at `n0 = 1`), `alA`/`alB` (`HalA`/`HalB`, from `AxSpinT2c1.sZAl`).

## Pins / honesty
* `σX`'s registers / devices are AxSpinE8f's `σ8`'s; the text premises read only the memory.
* The data map is `tX`'s (A = D = 1 preset, design §A.5 HAD scope); `MapOk` is proved for the
  identity pages KERNBASE .. `end` (the Rng ranges lie in pages 0x8000a .. 0x80018).

Reused: `AxSpinTextCerts.pageOk`/`textAtA`/`textAtU`/`text4A`/`text4U`, `AxSpinApA.MapOk`/
`Rng`/`tailText`, `dataAtS` (AxDataX3), `textFixed`/`imgBytes` (AxSymEngine), `imgOf`
(AxSpineOk), `AxSpinT2pt.*`, `AxSpinT2c1.*`, tactic `ax_epi_ledger_krfl` (AxEpiLedger).
Names: Lean-only, in the namespace `Weak.AxSpinT2c5` (file-qualified).
-/
import Weak.AxSpinT2c1
import Weak.AxSpinApA
import Weak.AxSpinTextCerts

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2c1

namespace AxSpinT2c5

/-! # 1. The image -/

/-- The image's domain: the kernel text and the three table pages. -/
def inImg (n : Nat) : Bool :=
  (decide (KernelSyms.«_entry» ≤ n) && decide (n < KernelSyms.«etext»)) ||
  (decide (ptL0 * 4096 ≤ n) && decide (n < (ptRoot + 1) * 4096))

/-- The image memory. -/
def memX : BMap := fun a =>
  if inImg a.toNat then some (BitVec.ofNat 8 (imgByte a.toNat)) else none

/-- THE INITIAL IMAGE (text + page tables). -/
def σX : ExecSt := ⟨AxSpinE8f.σ8.regs, memX, AxSpinE8f.σ8.dev⟩

/-! # 2. Pages -/

theorem ofIntToNat (a : Int) (h0 : 0 ≤ a) (h1 : a < 18446744073709551616) :
    (BitVec.ofInt 64 a).toNat = a.toNat := by
  rw [BitVec.toNat_ofInt]
  have h2 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  rw [h2, Int.emod_eq_of_lt h0 h1]

/-- Every L0 slot of `tX` is in the image. -/
theorem slot0All : ∀ j, j < nPages →
    WeakWalkEff.ptSlotMem σX (uPteAddr (uNextBase p1X) (BitVec.ofNat 9 j)) (leafAt j) := by
  unfold WeakWalkEff.ptSlotMem BytesAt
  decide +kernel

theorem slot2X : WeakWalkEff.ptSlotMem σX (AxPtProt.ptAddr2 tX (AxSpinT2pt.vpnOf 0)) p2X := by
  unfold WeakWalkEff.ptSlotMem BytesAt
  decide +kernel

theorem slot1X : WeakWalkEff.ptSlotMem σX (AxPtProt.ptAddr1 p2X (AxSpinT2pt.vpnOf 0)) p1X := by
  unfold WeakWalkEff.ptSlotMem BytesAt
  decide +kernel

theorem addr2Eq (j : Nat) (hj : j < nPages) :
    AxPtProt.ptAddr2 tX (AxSpinT2pt.vpnOf j) = AxPtProt.ptAddr2 tX (AxSpinT2pt.vpnOf 0) := by
  unfold AxPtProt.ptAddr2
  rw [(tXBits j hj).1, (tXBits 0 (by decide)).1]

theorem addr1Eq (j : Nat) (hj : j < nPages) :
    AxPtProt.ptAddr1 p2X (AxSpinT2pt.vpnOf j) = AxPtProt.ptAddr1 p2X (AxSpinT2pt.vpnOf 0) := by
  unfold AxPtProt.ptAddr1
  rw [(tXBits j hj).2.1, (tXBits 0 (by decide)).2.1]

theorem addr0Eq (j : Nat) (hj : j < nPages) :
    AxPtProt.ptAddr0 p1X (AxSpinT2pt.vpnOf j) = uPteAddr (uNextBase p1X) (BitVec.ofNat 9 j) := by
  unfold AxPtProt.ptAddr0
  rw [(tXBits j hj).2.2.1]

/-- The fetch checks of a text leaf (`R X`, A = D = 1). -/
theorem chkRX (w : BitVec 64) (h1 : Sail.BitVec.extractLsb w 7 0 = 0xCB#8)
    (h2 : ext_bits_of_PTE w = 0#10) :
    ∀ mxr dosum : Bool, pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum w := by
  intro mxr dosum
  unfold pteCheckOk
  rw [h1, h2]
  intro s
  cases mxr <;> cases dosum <;> ax_epi_ledger_krfl

/-- The data checks of a data leaf (`R W`, A = D = 1), load / store / AMO. -/
theorem chkRW (w : BitVec 64) (h1 : Sail.BitVec.extractLsb w 7 0 = 0xC7#8)
    (h2 : ext_bits_of_PTE w = 0#10) (acc : MemoryAccessType mem_payload)
    (hacc : acc = .Load .Data ∨ acc = .Store .Data ∨ acc = accAmo true) :
    ∀ mxr dosum : Bool, pteCheckOk acc .Supervisor mxr dosum w := by
  intro mxr dosum
  unfold pteCheckOk
  rw [h1, h2]
  intro s
  rcases hacc with rfl | rfl | rfl <;> cases mxr <;> cases dosum <;> ax_epi_ledger_krfl

/-- No A / D write-back on a preset leaf. -/
theorem updPreset (w : BitVec 64) (f : BitVec 8) (h1 : Sail.BitVec.extractLsb w 7 0 = f)
    (hf : f = 0xCB#8 ∨ f = 0xC7#8) (acc : MemoryAccessType mem_payload)
    (hacc : acc = .InstructionFetch () ∨ acc = .Load .Data ∨ acc = .Store .Data ∨
      acc = accAmo true) :
    update_PTE_Bits w acc = none := by
  unfold update_PTE_Bits
  rw [h1]
  rcases hf with rfl | rfl <;> rcases hacc with rfl | rfl | rfl | rfl <;> rfl

/-- Sv39 canonicality below 2^38. -/
theorem canonLow (va : BitVec 64) (h : va.toNat < 274877906944) :
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false := by
  have h' : va < 274877906944#64 :=
    BitVec.lt_def.2 (by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
  show (va != BitVec.signExtend 64 (BitVec.extractLsb 38 0 va)) = false
  revert h'
  bv_decide

/-- The PA of an identity-mapped VA below 2^56. -/
theorem paLow (va : BitVec 64) (h : va.toNat < 72057594037927936) :
    zero_extend (m := 64) (BitVec.ofNat 44 (va.toNat / 4096) +++
      Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = va := by
  have e : BitVec.ofNat 44 (va.toNat / 4096) = BitVec.extractLsb' 12 44 va := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
      Nat.reducePow]
  rw [e]
  have h' : va < 72057594037927936#64 :=
    BitVec.lt_def.2 (by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
  show BitVec.setWidth 64 (BitVec.extractLsb' 12 44 va ++ BitVec.extractLsb 11 0 va) = va
  revert h'
  bv_decide

theorem ppnAll : ∀ j, j < nPages → ppn0 (leafAt j) = BitVec.ofNat 44 (kbase + j) := by
  decide +kernel

/-- A fetch page of `tX` in `σX` (AxSpinTextCerts' page premise). -/
theorem pageXOf (j : Nat) (hj : j < textPages) :
    AxSpinTextCerts.pageOk σX tX (AxSpinT2pt.vpnOf j) p2X p1X (leafAt j) := by
  have hj' : j < nPages := by unfold textPages at hj; unfold nPages; omega
  obtain ⟨-, -, -, -, hfl, hext, -, -, hpb⟩ := tXBits j hj'
  rw [if_pos hj] at hfl
  refine ⟨tXMaps j hj', ?_, ?_, ?_, chkRX _ hfl hext, updPreset _ _ hfl (.inl rfl) _ (.inl rfl),
    hpb⟩
  · rw [addr2Eq j hj']; exact slot2X
  · rw [addr1Eq j hj']; exact slot1X
  · rw [addr0Eq j hj']; exact slot0All j hj'

theorem pageX0 : AxSpinTextCerts.pageOk σX tX (AxSpinT2pt.vpnOf 0) p2X p1X (leafAt 0) :=
  pageXOf 0 (by decide)
theorem pageX1 : AxSpinTextCerts.pageOk σX tX (AxSpinT2pt.vpnOf 1) p2X p1X (leafAt 1) :=
  pageXOf 1 (by decide)

/-! # 3. Text -/

/-- One text conjunct: the fitting constructor on page 0x80000 or 0x80001. -/
local macro "ax_t2c5_txt" : tactic => `(tactic|
  first
  | exact AxSpinTextCerts.textAtA pageX0 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.textAtU pageX0 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4U pageX0 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4A pageX0 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.textAtA pageX1 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.textAtU pageX1 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4U pageX1 _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4A pageX1 _ _ (by decide +kernel))

/-- Split a conjunction of text facts and close each. -/
local macro "ax_t2c5_all" : tactic => `(tactic|
  (repeat' apply And.intro) <;> ax_t2c5_txt)

theorem pushOffTextX : pushOffText σX tX := by unfold pushOffText; ax_t2c5_all
theorem popOffTextX : popOffText σX tX := by unfold popOffText; ax_t2c5_all
theorem acquireTextX : acquireText σX tX := by unfold acquireText; ax_t2c5_all
theorem holdingTextX : holdingText σX tX := by unfold holdingText; ax_t2c5_all
theorem releaseTextX : releaseText σX tX := by unfold releaseText; ax_t2c5_all
theorem mycpuTextX : mycpuText σX tX := by unfold mycpuText; ax_t2c5_all
theorem allocpidTextX : allocpidText σX tX := by unfold allocpidText; ax_t2c5_all
theorem tailTextX : AxSpinApA.tailText σX tX := by unfold AxSpinApA.tailText; ax_t2c5_all

/-! # 4. `textFixed` -/

/-- No read of a row touches the image's domain. -/
def readsOffB (row : List Lbl) : Bool :=
  row.all fun lb =>
    match aidentRd (aident lb) with
    | some (_, base, n) => (imgBytes (imgS σX) base n).isNone
    | none => true

theorem readsOffLit : (List.range 3).all (fun h => readsOffB (rowL h)) = true := by
  decide +kernel

theorem imgAgree (E : List (List Eitem)) (a : Int) (b : BitVec 8) :
    imgS σX a = some b → (gtAdGd (gT3 E)).gdG.gxImg a = some b := by
  intro h
  unfold imgS imgOf at h
  split at h
  · rename_i ha
    show some (img a) = some b
    unfold σX memX at h
    simp only at h
    split at h
    · rw [ofIntToNat a ha.1 ha.2] at h
      exact h
    · cases h
  · cases h

/-- **`textFixed`** for hart `h` of (a′) at every emission (AxSpinT2b `HfixA`/`HfixB`). -/
theorem textFixedX (E : List (List Eitem)) (h : Agent) (hh : h < 3) :
    textFixed (gtAdGd (gT3 E)) h (imgS σX) := by
  refine ⟨imgAgree E, ?_⟩
  intro k lb aq base n vs hk hr hi
  rw [growG3] at hk
  have H := List.all_eq_true.1 (List.all_eq_true.1 readsOffLit h (List.mem_range.2 hh)) lb
    (List.mem_of_getElem? hk)
  rw [hr] at H
  simp only [hi, Option.isNone_some] at H
  cases H

/-! # 5. `MapOk` -/

set_option maxHeartbeats 1000000 in
/-- One aligned data word on an identity data page of `tX`. -/
theorem dataPage (acc : MemoryAccessType mem_payload)
    (hacc : acc = .Load .Data ∨ acc = .Store .Data ∨ acc = accAmo true) (a : Int) (w : Nat)
    (hw : w = 4 ∨ w = 8) (hal : a % (w : Int) = 0) (hlo : 0x80007000 ≤ a)
    (hhi : a + w ≤ 0x80024000) :
    dataAtS σX tX acc (BitVec.ofInt 64 a) w (BitVec.ofInt 64 a) := by
  have hva := ofIntToNat a (by omega) (by omega)
  have hsv := svpnToNat (BitVec.ofInt 64 a) (by rw [hva]; omega)
  have hj : a.toNat / 4096 - kbase < nPages := by
    have e1 : kbase = 0x80000 := rfl
    have e2 : nPages = 0x24 := rfl
    rw [e1, e2]; omega
  have hj7 : ¬ a.toNat / 4096 - kbase < textPages := by
    have e1 : kbase = 0x80000 := rfl
    have e3 : textPages = 7 := rfl
    rw [e1, e3]; omega
  have hv : WeakKpt.svpnOf (BitVec.ofInt 64 a) = AxSpinT2pt.vpnOf (a.toNat / 4096 - kbase) := by
    apply BitVec.eq_of_toNat_eq
    rw [hsv, hva]
    unfold AxSpinT2pt.vpnOf
    rw [BitVec.toNat_ofNat]
    have e1 : kbase = 0x80000 := rfl
    rw [e1]
    show _ = (0x80000 + (a.toNat / 4096 - 0x80000)) % 134217728
    omega
  obtain ⟨-, -, -, -, hfl, hext, -, -, hpb⟩ := tXBits _ hj
  rw [if_neg hj7] at hfl
  unfold dataAtS
  rw [hv]
  refine ⟨p2X, p1X, leafAt (a.toNat / 4096 - kbase), tXMaps _ hj, ?_, ?_, ?_,
    chkRW _ hfl hext acc hacc, updPreset _ _ hfl (.inr rfl) acc (.inr hacc), hpb, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [addr2Eq _ hj]; exact slot2X
  · rw [addr1Eq _ hj]; exact slot1X
  · rw [addr0Eq _ hj]; exact slot0All _ hj
  · exact canonLow _ (by rw [hva]; omega)
  · rw [ppnAll _ hj]
    have e1 : kbase = 0x80000 := rfl
    have hk : kbase + (a.toNat / 4096 - kbase) = (BitVec.ofInt 64 a).toNat / 4096 := by
      rw [hva, e1]; omega
    rw [hk]
    exact paLow _ (by rw [hva]; omega)
  · unfold inRam ramBase ramEnd
    rw [hva]; omega
  · unfold is_aligned_vaddr
    simp only [beq_iff_eq, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega), hva]
    rcases hw with rfl | rfl <;> omega
  · unfold is_aligned_paddr
    simp only [beq_iff_eq, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega), hva]
    rcases hw with rfl | rfl <;> omega

/-- **`MapOk`** for any hart / frame / slot of the layout family (AxSpinT2b `HmapA`/`HmapB`). -/
theorem mapOkX (i : Agent) (hi : i < NCPU) (S p : Int)
    (hS : (KernelSyms.«stack0» : Int) + 80 ≤ S ∧ S ≤ (KernelSyms.«stack0» : Int) + 0x8000)
    (hp : ∃ m : Nat, m < 64 ∧ p = (KernelSyms.«proc» : Int) + 376 * (m : Int)) :
    AxSpinApA.MapOk σX tX i S p := by
  intro acc a w hacc hw hal hR
  obtain ⟨v1, v2, v3, v4, v5, -, -, -⟩ := AxSpinT2a.symV
  obtain ⟨m, hm, rfl⟩ := hp
  have hc : ((cpuOf i).val : Int) = (i : Int) := by rw [cpuOfNat i hi]
  have hi8 : (i : Int) < 8 := by have := Int.ofNat_lt.2 hi; exact this
  unfold AxSpinApA.Rng cpuZ at hR
  simp only [AxSpinT2a.zNp, AxSpinT2a.zLk] at hR
  rw [v1, v2, v3, v4, hc] at hR
  rw [v5] at hS
  have hw' : (w : Int) = 4 ∨ (w : Int) = 8 := by rcases hw with rfl | rfl <;> simp
  exact dataPage acc hacc a w hw hal (by omega) (by omega)

/-- `MapOk` for the three harts of (a′). -/
theorem mapOk3 (h : Agent) (hh : h < 3) : AxSpinApA.MapOk σX tX h (sZ h) (AxSpinT2a.pEx h) := by
  have hL := layHyp3
  match h, hh with
  | 0, _ => exact mapOkX 0 (by decide) _ _ (hL.stk 0 (.inl rfl)) (hL.slot 0 (.inl rfl))
  | 1, _ => exact mapOkX 1 (by decide) _ _ (hL.stk 1 (.inr (.inl rfl))) (hL.slot 1 (.inr (.inl rfl)))
  | 2, _ => exact mapOkX 2 (by decide) _ _ (hL.stk 2 (.inr (.inr rfl))) (hL.slot 2 (.inr (.inr rfl)))
  | n + 3, hh => exact absurd hh (Nat.not_lt.2 (Nat.le_add_left 3 n))

/-! # 5b. The warm TLB in `ctrlOkS`'s form -/

/-- The preset entries are the walker's fill entries (`uWalkEntry`). -/
theorem tlbEntUwe (j : Nat) (hj : j < nPages) :
    tlbEnt j = uWalkEntry (AxSpinT2pt.vpnOf j) p2X p1X (leafAt j) 0#16 := by
  have H : ∀ j, j < nPages →
      AxSpinE8f.entEqB (tlbEnt j) (uWalkEntry (AxSpinT2pt.vpnOf j) p2X p1X (leafAt j) 0#16) =
        true := by
    decide +kernel
  exact AxSpinE8f.entEqBSound _ _ (H j hj)

/-- **`tlbExact tX tlbW`** (the TLB conjunct of `ctrlOkS`, hence of AxSpinT2a's `entryOk`): every
entry of the warm TLB is the fill entry of a page `tX` maps, at that page's slot. -/
theorem tlbExactW : tlbExact tX tlbW := by
  intro vpn' ent h
  have hlt : tlb_hash 39 vpn' < 2 ^ 6 := by rw [tlbHash_eq]; exact tlbHash_lt vpn'
  rw [getElem!_pos tlbW _ hlt] at h
  simp only [tlbW, Vector.getElem_ofFn] at h
  split at h
  · rename_i hn
    obtain rfl := Option.some.inj h
    refine ⟨AxSpinT2pt.vpnOf (tlb_hash 39 vpn'), p2X, p1X, leafAt (tlb_hash 39 vpn'),
      tXMaps _ hn, ?_, tlbEntUwe _ hn⟩
    rw [tlbHash_eq (AxSpinT2pt.vpnOf _), (tXWalk _ hn).1]
  · cases h

/-! # 6. Image premises -/

/-- AxSpinT2b `Himgc`: `lk->cpu` is 0 in the graph image. -/
theorem imgClb (E : List (List Eitem)) (L : Xlay) (hL : L.xlLk = AxSpinT2a.zLk) :
    ∀ a, a ∈ clb L → (gT3 E).gtG.gxImg a = some b0 := by
  intro a ha
  unfold clb at ha
  rw [hL, inClr] at ha
  have hz : AxSpinT2a.zLk = 0x80012500 := rfl
  rw [hz] at ha
  obtain ⟨j, hj, rfl⟩ : ∃ j : Nat, j < 8 ∧ a = 0x80012500 + 16 + (j : Int) :=
    ⟨(a - (0x80012500 + 16)).toNat, by omega, by omega⟩
  show some (img _) = some b0
  revert j
  decide +kernel

/-- AxSpinT2b `Himgn` at `n0 = 1`: nextpid's bytes hold 1 in the graph image. -/
theorem imgNp (E : List (List Eitem)) (L : Xlay) (hL : L.xlNp = AxSpinT2a.zNp) :
    ∀ (j : Nat) a v, (npb L)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 1))[j]? = some v → (gT3 E).gtG.gxImg a = some v := by
  intro j a v h1 h2
  unfold npb at h1
  rw [hL] at h1
  have hlen : j < 4 := by
    have := (List.getElem?_eq_some_iff.1 h1).1
    unfold clRange at this
    simpa using this
  show some (img a) = some v
  have hz : AxSpinT2a.zNp = 0x8000a384 := rfl
  rw [hz] at h1
  match j, hlen with
  | 0, _ =>
    rw [show (clRange 0x8000a384 4)[0]? = some 0x8000a384 from by decide +kernel] at h1
    rw [show (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 1))[0]? = some 1#8 from by
      decide +kernel] at h2
    cases h1; cases h2; decide +kernel
  | 1, _ =>
    rw [show (clRange 0x8000a384 4)[1]? = some 0x8000a385 from by decide +kernel] at h1
    rw [show (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 1))[1]? = some 0#8 from by
      decide +kernel] at h2
    cases h1; cases h2; decide +kernel
  | 2, _ =>
    rw [show (clRange 0x8000a384 4)[2]? = some 0x8000a386 from by decide +kernel] at h1
    rw [show (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 1))[2]? = some 0#8 from by
      decide +kernel] at h2
    cases h1; cases h2; decide +kernel
  | 3, _ =>
    rw [show (clRange 0x8000a384 4)[3]? = some 0x8000a387 from by decide +kernel] at h1
    rw [show (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 1))[3]? = some 0#8 from by
      decide +kernel] at h2
    cases h1; cases h2; decide +kernel

/-- AxSpinT2b `HalA` / `HalB`. -/
theorem al3 (h : Agent) : sZ h % 16 = 0 := sZAl h

end AxSpinT2c5

end Weak
