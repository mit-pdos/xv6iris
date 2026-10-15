/-
THE BOOT CARVE AND THE RESERVED REGIONS (W8-β′).

`MachCSL.powerBootRes` hands the boot client the cells of every UNRESERVED
byte (`memCells E (rsvErase KernelRsv.static σ.mem)`) and its HALVES of the
reserved ones (`rsvHalvesC`, at the image's histories); the state
interpretation keeps the other halves.  This file is the carve's side:

* `bootRan_rsvErase`: a window holding no reserved byte is the same window
  of the full image (`rsvOff`, decided region by region);
* `bootRan_lockHole`: a window around one static lock is the full image's,
  less the lock's two words (`rsvOnly`);
* `bootRsv_wordHalf`: a reserved `.bss` word's half, at its image history,
  is the half word at zero (at any context, `MachCSL.histByte_img_ctx`);
* `bootRsvHalves`: xv6's halves, by group (singleton locks, harts, `proc[i].lock`).
-/
import Xv6.BootCarve
import Xv6.KernelRsv
import MachCSL.RsvMint
import MachCSL.Lock

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL

/-- No reserved byte lies in a hart's save area `[cpus[c] + 8, cpus[c] + 120)`. -/
theorem xv6Rsv_ctx_check :
    (List.finRange NCPU).all (fun c => (rsvBytes xv6RsvStatic).all (fun a =>
      !(decide (MachCSL.KernelSyms.«cpus» + 128 * c.val + 8 ≤ a.toNat ∧
        a.toNat < MachCSL.KernelSyms.«cpus» + 128 * c.val + 120)))) = true := by
  decide +kernel

theorem xv6Rsv_ctx_off (c : CPU) (a : PAddr) (ha : a ∈ rsvBytes (KernelRsv.static)) :
    ¬ (MachCSL.KernelSyms.«cpus» + 128 * c.val + 8 ≤ a.toNat ∧
      a.toNat < MachCSL.KernelSyms.«cpus» + 128 * c.val + 120) := by
  have h1 := List.all_eq_true.1 xv6Rsv_ctx_check c (List.mem_finRange c)
  have h2 := List.all_eq_true.1 h1 a ha
  simp at h2
  omega

/-! ## Window checks, region by region

A region's bytes lie in `[base, base + span)` (`regionBytes_span`), so whether
a window `[lo, hi)` holds reserved bytes is decided per region (`rsvOff`: none;
`rsvOnly`: only one region's), by evaluation. -/

/-- The extent of a region's kind (`sizeof (struct cpu)`, `sizeof (struct spinlock)`). -/
def rsvSpan : RsvKind → Nat
  | .cpu _ => 128
  | .lock _ => 24
  | .pub _ => 4
  | .slots _ _ => 0
  | .roots _ _ => 0
  | .uroots _ _ => 0
  | .freeHead _ _ => 0
  | .racy _ _ _ _ _ => 0
  | .stack _ => 0
  | .kstacks _ _ => 0

theorem regionBytes_span (R : RsvRegion) (hR : R.base.toNat + rsvSpan R.kind ≤ 2 ^ 64) (a : PAddr)
    (ha : a ∈ R.bytes) : R.base.toNat ≤ a.toNat ∧ a.toNat < R.base.toNat + rsvSpan R.kind := by
  obtain ⟨b, k⟩ := R
  cases k with
  | slots _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | roots _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | uroots _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | freeHead _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | racy _ _ _ _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | stack _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | kstacks _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | pub w =>
    simp only [rsvSpan] at hR ⊢
    simp only [RsvRegion.bytes, RsvRegion.words, wordBytes, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    bv_omega
  | _ =>
    simp only [rsvSpan] at hR ⊢ <;>
    simp only [RsvRegion.bytes, RsvRegion.words, wordBytes, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append, List.mem_map, List.mem_range] at ha <;>
    rcases ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> bv_omega

/-- The bytes of a lock region. -/
theorem lockBytes_cases (L cb : BitVec 64) (hw : L.toNat + 24 ≤ 2 ^ 64) (a : PAddr)
    (ha : a ∈ (⟨L, .lock cb⟩ : RsvRegion).bytes) :
    (L.toNat ≤ a.toNat ∧ a.toNat < L.toNat + 4) ∨ (L.toNat + 16 ≤ a.toNat ∧ a.toNat < L.toNat + 24) := by
  simp only [RsvRegion.bytes, RsvRegion.words, wordBytes, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_append, List.mem_map, List.mem_range] at ha
  rcases ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · left; bv_omega
  · right; bv_omega

/-- A footprint-free region (a `.slots` registry entry, W8 (f2-ctx)) has no
bytes. -/
theorem regionBytes_span0 (R : RsvRegion) (h0 : rsvSpan R.kind = 0) (a : PAddr) (ha : a ∈ R.bytes) : False := by
  obtain ⟨b, k⟩ := R
  cases k with
  | slots _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | roots _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | uroots _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | freeHead _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | racy _ _ _ _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | stack _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | kstacks _ _ => simp [RsvRegion.bytes, RsvRegion.words] at ha
  | _ => simp [rsvSpan] at h0

/-- No region of `rs` meets `[lo, hi)`. -/
def rsvOff (rs : List RsvRegion) (lo hi : Nat) : Bool :=
  rs.all (fun R => decide (rsvSpan R.kind = 0) || (decide (R.base.toNat + rsvSpan R.kind ≤ 2 ^ 64) &&
    (decide (R.base.toNat + rsvSpan R.kind ≤ lo) || decide (hi ≤ R.base.toNat))))

theorem rsvOff_sound {rs : List RsvRegion} {lo hi : Nat} (h : rsvOff rs lo hi = true) :
    ∀ a ∈ rsvBytes rs, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) := by
  intro a ha
  obtain ⟨R, hR, haR⟩ := List.mem_flatMap.1 ha
  have := List.all_eq_true.1 h R hR
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h0 | this
  · exact (regionBytes_span0 R h0 a haR).elim
  have hs := regionBytes_span R this.1 a haR
  omega

/-- Only `R0` of `rs` meets `[lo, hi)`. -/
def rsvOnly (rs : List RsvRegion) (R0 : RsvRegion) (lo hi : Nat) : Bool :=
  rs.all (fun R => decide (R = R0) || decide (rsvSpan R.kind = 0) ||
    (decide (R.base.toNat + rsvSpan R.kind ≤ 2 ^ 64) &&
    (decide (R.base.toNat + rsvSpan R.kind ≤ lo) || decide (hi ≤ R.base.toNat))))

theorem rsvOnly_sound {rs : List RsvRegion} {R0 : RsvRegion} {lo hi : Nat} (h : rsvOnly rs R0 lo hi = true) :
    ∀ a ∈ rsvBytes rs, lo ≤ a.toNat ∧ a.toNat < hi → a ∈ R0.bytes := by
  intro a ha hlh
  obtain ⟨R, hR, haR⟩ := List.mem_flatMap.1 ha
  have := List.all_eq_true.1 h R hR
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with (rfl | h0) | ⟨h1, h2⟩
  · exact haR
  · exact (regionBytes_span0 R h0 a haR).elim
  · have hs := regionBytes_span R h1 a haR
    omega

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A window holding no reserved byte is the window of the full map. -/
theorem bootRan_rsvErase (rs : List RsvRegion) (m : MemF Hist) (lo hi : Nat)
    (h : ∀ a ∈ rsvBytes rs, ¬ (lo ≤ a.toNat ∧ a.toNat < hi)) :
    bootRan (GF := GF) (rsvErase rs m) lo hi = bootRan m lo hi := by
  unfold bootRan bcRanMem
  congr 1
  apply LawfulPartialMap.equiv_iff_eq.mp
  intro a
  rw [LawfulPartialMap.get?_filter, LawfulPartialMap.get?_filter, rsvErase_get?]
  by_cases ha : a ∈ rsvBytes rs
  · have hn := h a ha
    rw [if_pos ha]
    cases hm : get? m a with
    | none => rfl
    | some H =>
      simp only [Option.bind_none, Option.bind_some, bcRanIn]
      rw [if_neg (by simpa using hn)]
  · rw [if_neg ha]

/-- xv6's case: a window no region meets (`rsvOff`, by evaluation). -/
theorem bootRan_rsvErase_off (m : MemF Hist) (lo hi : Nat) (h : rsvOff KernelRsv.static lo hi = true) :
    bootRan (GF := GF) (rsvErase KernelRsv.static m) lo hi = bootRan m lo hi :=
  bootRan_rsvErase _ m lo hi (rsvOff_sound h)

/-- **A reserved `.bss` word's half, at its image history, is the half word
at zero** (any context). -/
theorem bootRsv_wordHalf [CurCtx] (va : PAddr) (n A : Nat) (hva : va.toNat = A) (hn : 0 < n)
    (hlo : MachCSL.KernelSyms.«_bss» ≤ A) (hend : A + n ≤ MachCSL.KernelSyms.«end») (hal : A % n = 0) :
    kmapStatic (GF := GF) ⊢
      ([∗list] j ∈ List.range n, pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem)
        (va + BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half)
        ((get? (M := MemF) (imgFlat bootImage) (va + BitVec.ofNat 64 j)).getD [])) -∗
      wordPointsTo va n (DFrac.own (1 : Qp).half) 0#(8 * n) := by
  have hb : MachCSL.KernelSyms.«_bss» = 0x8000a400 := rfl
  have he : MachCSL.KernelSyms.«end» = 0x80023b10 := rfl
  have hram : inRam va n := by unfold inRam ramBase ramEnd; omega
  have hrw : kmapClass (vpnOf va).toNat = some .rw := bc_kmapClass_rw _ (by omega) (by omega)
  iintro #Hk H
  ihave Hid := kmapStatic_rw _ hrw $$ Hk
  iapply wordPointsTo_intro_id va n _ _ hram (by rw [hva]; exact hal) $$ Hid
  unfold bytesPointsTo ctxBytes
  iapply BigSepL.bigSepL_mono _ $$ H
  intro _ j hj
  have hjn : j < n := List.mem_range.1 (List.mem_of_getElem? hj)
  have ht : (va + BitVec.ofNat 64 j).toNat = A + j := by
    rw [BitVec.toNat_add, hva, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  have hr1 : inRam (va + BitVec.ofNat 64 j) 1 := by unfold inRam ramBase ramEnd; omega
  have hz := bootImage_wf.bss (va + BitVec.ofNat 64 j) (by omega) (by omega)
  have hg : get? (M := MemF) (imgFlat bootImage) (va + BitVec.ofNat 64 j) = some [⟨0, 0, 0#8⟩] :=
    bc_imgFlat_get bootImage _ _ hr1 hz
  rw [hg, Option.getD_some, show nthByte (0#(8 * n)) j = 0#8 by simp [nthByte]]
  exact histByte_img_ctx curCtx _ _ 0 _

/-- A window of the erased map holding no reserved byte is the full map's. -/
theorem bootRan_rsvErase_le (m : MemF Hist) (lo hi : Nat)
    (h : ∀ a ∈ rsvBytes (KernelRsv.static), ¬ (lo ≤ a.toNat ∧ a.toNat < hi)) :
    bootRan (GF := GF) (rsvErase KernelRsv.static m) lo hi ⊢ bootRan m lo hi := by
  rw [bootRan_rsvErase _ m lo hi h]

theorem bootRan_rsvErase_off_le (m : MemF Hist) (lo hi : Nat) (h : rsvOff KernelRsv.static lo hi = true) :
    bootRan (GF := GF) (rsvErase KernelRsv.static m) lo hi ⊢ bootRan m lo hi := by
  rw [bootRan_rsvErase_off m lo hi h]

/-- Every hart's registration, from the list `powerBootRes` names. -/
theorem xv6CpuRsvIn (h : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) (c : CPU) :
    cpuRsvIn (hlc := hlc) (GF := GF) c :=
  ⟨rsvCpuIdx c, by rw [h]; exact xv6RsvStatic_cpu c⟩

/-- **`bootCarve_image` over the erased map** (W8-β′): the read-only window
holds no reserved byte, so it is the full image's. -/
theorem bootCarve_imageR :
    kmapStatic (GF := GF) ∗ bootRaw (rsvErase KernelRsv.static (imgFlat bootImage)) ⊢@{IProp GF}
      |==> ((kernelText ∗ kernelData ∗ kmapStatic) ∗
        bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) bcRoHi ramEnd) := by
  have h1 : bcRoLo ≤ bcRoHi := by decide
  have h2 : bcRoHi ≤ ramEnd := by decide
  have h3 : ramEnd ≤ 2 ^ 64 := by decide
  iintro ⟨#Hk, H⟩
  ihave H := bootRaw_ran (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage)) $$ H
  icases (bootRan_split (GF := GF) _ 0 bcRoLo (2 ^ 64) (by omega) (by unfold bcRoLo ramBase; omega)).1
    $$ H with ⟨-, H⟩
  icases (bootRan_split (GF := GF) _ bcRoLo bcRoHi (2 ^ 64) h1 (by omega)).1 $$ H with ⟨Hro, H⟩
  icases (bootRan_split (GF := GF) _ bcRoHi ramEnd (2 ^ 64) h2 h3).1 $$ H with ⟨Hown, -⟩
  ihave Hro := bootRan_rsvErase_off_le (imgFlat bootImage) bcRoLo bcRoHi (by decide +kernel) $$ Hro
  ihave Hro := bootRan_persist (GF := GF) (imgFlat bootImage) bcRoLo bcRoHi $$ Hro
  imod Hro with #Hro
  ihave Ht := kernelText_intro (GF := GF) $$ [Hk Hro]
  · iframe Hk Hro
  ihave Hd := kernelData_intro (GF := GF) $$ Hro
  imodintro
  iframe Ht Hd Hk Hown

/-- **A window around ONE static lock** (W8-β′): the erased window is the
full map's, less the lock's two words (`[L, L+4)`, `[L+16, L+24)`). -/
theorem bootRan_lockHole (m : MemF Hist) (L cb : BitVec 64) (lo hi : Nat)
    (hlo : lo ≤ L.toNat) (hhi : L.toNat + 24 ≤ hi) (hw : L.toNat + 24 ≤ 2 ^ 64)
    (h : rsvOnly KernelRsv.static ⟨L, .lock cb⟩ lo hi = true) :
    bootRan (GF := GF) (rsvErase KernelRsv.static m) lo hi ⊢
      bootRan m lo L.toNat ∗ bootRan m (L.toNat + 4) (L.toNat + 16) ∗ bootRan m (L.toNat + 24) hi := by
  have hs := rsvOnly_sound h
  have hb := lockBytes_cases L cb hw
  iintro H
  icases (bootRan_split (GF := GF) _ lo L.toNat hi hlo (by omega)).1 $$ H with ⟨H0, H⟩
  icases (bootRan_split (GF := GF) _ L.toNat (L.toNat + 4) hi (by omega) (by omega)).1 $$ H with ⟨-, H⟩
  icases (bootRan_split (GF := GF) _ (L.toNat + 4) (L.toNat + 16) hi (by omega) (by omega)).1 $$ H with ⟨H1, H⟩
  icases (bootRan_split (GF := GF) _ (L.toNat + 16) (L.toNat + 24) hi (by omega) (by omega)).1 $$ H with ⟨-, H2⟩
  ihave H0 := bootRan_rsvErase_le m lo L.toNat
    (fun a ha hlh => by have := hb a (hs a ha ⟨hlh.1, by omega⟩); omega) $$ H0
  ihave H1 := bootRan_rsvErase_le m (L.toNat + 4) (L.toNat + 16)
    (fun a ha hlh => by have := hb a (hs a ha ⟨by omega, by omega⟩); omega) $$ H1
  ihave H2 := bootRan_rsvErase_le m (L.toNat + 24) hi
    (fun a ha hlh => by have := hb a (hs a ha ⟨by omega, hlh.2⟩); omega) $$ H2
  iframe H0 H1 H2

/-- **A reserved word's half, at an image history of zero bytes, is the
word's half CELL over the image tail** (no entry yet; the lock layer's form). -/
theorem bootRsv_wordCellH0 (pa : PAddr) (n : Nat)
    (hg : ∀ j, j < n → get? (M := MemF) (imgFlat bootImage) (pa + BitVec.ofNat 64 j) = some [⟨0, 0, 0#8⟩]) :
    ([∗list] j ∈ List.range n, pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem)
        (pa + BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half)
        ((get? (M := MemF) (imgFlat bootImage) (pa + BitVec.ofNat 64 j)).getD [])) ⊢
      wordCellH (GF := GF) pa n [] := by
  refine .trans ?_ (wordCellH_intro pa n [] (fun j => (get? (M := MemF) (imgFlat bootImage) (pa + BitVec.ofNat 64 j)).getD []) ?_)
  · unfold histBytes
    simp only [WordHist.hist, List.map_nil, List.nil_append]
    exact .rfl
  · intro j hj
    show ∃ e H, (get? (M := MemF) (imgFlat bootImage) (pa + BitVec.ofNat 64 j)).getD [] = e :: H ∧ e.v = nthByte 0 j ∧ e.t = 0
    rw [hg j hj]
    exact ⟨_, _, rfl, by simp [nthByte], rfl⟩

/-- **A reserved `.bss` word's half, at its image history, is the word's
half CELL over the image tail** (no entry yet; the lock layer's form). -/
theorem bootRsv_wordCellH (pa : PAddr) (n A : Nat) (hva : pa.toNat = A)
    (hlo : MachCSL.KernelSyms.«_bss» ≤ A) (hend : A + n ≤ MachCSL.KernelSyms.«end») :
    ([∗list] j ∈ List.range n, pointsTo (G := (MachGS.era (hlc := hlc) (GF := GF)).mem)
        (pa + BitVec.ofNat 64 j) (DFrac.own (1 : Qp).half)
        ((get? (M := MemF) (imgFlat bootImage) (pa + BitVec.ofNat 64 j)).getD [])) ⊢
      wordCellH (GF := GF) pa n [] := by
  have hb : MachCSL.KernelSyms.«_bss» = 0x8000a400 := rfl
  have he : MachCSL.KernelSyms.«end» = 0x80023b10 := rfl
  refine bootRsv_wordCellH0 pa n (fun j hj => ?_)
  have ht : (pa + BitVec.ofNat 64 j).toNat = A + j := by
    rw [BitVec.toNat_add, hva, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  have hr1 : inRam (pa + BitVec.ofNat 64 j) 1 := by unfold inRam ramBase ramEnd; omega
  have hz := bootImage_wf.bss (pa + BitVec.ofNat 64 j) (by omega) (by omega)
  exact bc_imgFlat_get bootImage _ _ hr1 hz

/-- **A static lock's halves, at an image of zero bytes, are its two half
cells** (W8-β′). -/
theorem bootRsv_lockHalves0 (lk : PAddr)
    (hg4 : ∀ j, j < 4 → get? (M := MemF) (imgFlat bootImage) (lk + BitVec.ofNat 64 j) = some [⟨0, 0, 0#8⟩])
    (hg8 : ∀ j, j < 8 → get? (M := MemF) (imgFlat bootImage) (lk + 16#64 + BitVec.ofNat 64 j) =
      some [⟨0, 0, 0#8⟩]) :
    rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR lk) (imgFlat bootImage) ⊢
      wordCellH (GF := GF) lk 4 [] ∗ wordCellH (lk + 16#64) 8 [] := by
  dsimp only [rsvRegionHalfC, xv6LockR, RsvRegion.words]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, -⟩
  isplitl [H1]
  · iapply bootRsv_wordCellH0 lk 4 hg4 $$ H1
  · iapply bootRsv_wordCellH0 (lk + 16#64) 8 hg8 $$ H2

/-- **A static lock's halves, at the image, are its two half cells** (W8-β′). -/
theorem bootRsv_lockHalves (lk : PAddr) (L : Nat) (hlk : lk.toNat = L)
    (hlo : MachCSL.KernelSyms.«_bss» ≤ L) (hend : L + 24 ≤ MachCSL.KernelSyms.«end») :
    rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR lk) (imgFlat bootImage) ⊢
      wordCellH (GF := GF) lk 4 [] ∗ wordCellH (lk + 16#64) 8 [] := by
  have he : MachCSL.KernelSyms.«end» = 0x80023b10 := rfl
  have h16 : (lk + 16#64).toNat = L + 16 := by
    rw [BitVec.toNat_add, hlk]; simp only [BitVec.toNat_ofNat]; omega
  dsimp only [rsvRegionHalfC, xv6LockR, RsvRegion.words]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, -⟩
  isplitl [H1]
  · iapply bootRsv_wordCellH lk 4 L hlk hlo (by omega) $$ H1
  · iapply bootRsv_wordCellH (lk + 16#64) 8 (L + 16) h16 (by omega) (by omega) $$ H2

/-- **A static lock's 24-byte window** (W8-β′), as the boot carve hands it on:
the erased window (the lock's two words are not in it), the client's halves
of those words, and which list the era reserved. -/
def bootLockWin (lk : BitVec 64) (L : Nat) : IProp GF := iprop%
  ⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static⌝ ∗
  bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) L (L + 24) ∗
  rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR lk) (imgFlat bootImage)

theorem bootLockWin_intro (lk : BitVec 64) (L : Nat)
    (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    bootRan (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage)) L (L + 24) ∗
      rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR lk) (imgFlat bootImage) ⊢
      bootLockWin lk L := by
  unfold bootLockWin
  iintro ⟨H, Hh⟩
  iframe H Hh
  ipureintro; exact heq

/-- **The proc table's window** (W8-β′), as the boot carve hands it on: the
erased window (every `proc[i].lock`'s two words are out of it), the client's
halves of those words, and which list the era reserved. -/
def bootProcWin : IProp GF := iprop%
  ⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static⌝ ∗
  bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) MachCSL.KernelSyms.«proc»
    (MachCSL.KernelSyms.«proc» + 376 * 64) ∗
  ([∗list] i ∈ List.range 64, rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (rsvProcLk i))
    (imgFlat bootImage))

theorem bootProcWin_intro (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    bootRan (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage)) MachCSL.KernelSyms.«proc»
        (MachCSL.KernelSyms.«proc» + 376 * 64) ∗
      ([∗list] i ∈ List.range 64, rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (rsvProcLk i))
        (imgFlat bootImage)) ⊢ bootProcWin := by
  unfold bootProcWin
  iintro ⟨H, Hh⟩
  iframe H Hh
  ipureintro; exact heq

/-- **The buffers' window** (W8-β′), as the boot carve hands it on: the erased
`[bcache + 24, bcache + 24 + 1112 * 30)` (every buffer's sleeplock's inner
lock's two words are out of it), the client's halves of those words, and
which list the era reserved. -/
def bootBufsWin : IProp GF := iprop%
  ⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static⌝ ∗
  bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) (MachCSL.KernelSyms.«bcache» + 24)
    (MachCSL.KernelSyms.«bcache» + 24 + 1112 * 30) ∗
  ([∗list] i ∈ List.range 30, rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (rsvBufLk i))
    (imgFlat bootImage))

theorem bootBufsWin_intro (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    bootRan (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage)) (MachCSL.KernelSyms.«bcache» + 24)
        (MachCSL.KernelSyms.«bcache» + 24 + 1112 * 30) ∗
      ([∗list] i ∈ List.range 30, rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (rsvBufLk i))
        (imgFlat bootImage)) ⊢ bootBufsWin := by
  unfold bootBufsWin
  iintro ⟨H, Hh⟩
  iframe H Hh
  ipureintro; exact heq

/-- **The inodes' window** (W8-β′): the erased `[itable + 24, itable + 0x1aa8)`
(every inode's sleeplock's inner lock's two words are out of it), the
client's halves of those words, and which list the era reserved. -/
def bootInodesWin : IProp GF := iprop%
  ⌜MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static⌝ ∗
  bootRan (rsvErase KernelRsv.static (imgFlat bootImage)) (MachCSL.KernelSyms.«itable» + 24)
    (MachCSL.KernelSyms.«itable» + 0x1aa8) ∗
  ([∗list] k ∈ List.range 50, rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (rsvInodeLk k))
    (imgFlat bootImage))

theorem bootInodesWin_intro (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static) :
    bootRan (GF := GF) (rsvErase KernelRsv.static (imgFlat bootImage)) (MachCSL.KernelSyms.«itable» + 24)
        (MachCSL.KernelSyms.«itable» + 0x1aa8) ∗
      ([∗list] k ∈ List.range 50, rsvRegionHalfC (MachGS.era (hlc := hlc) (GF := GF)) (xv6LockR (rsvInodeLk k))
        (imgFlat bootImage)) ⊢ bootInodesWin := by
  unfold bootInodesWin
  iintro ⟨H, Hh⟩
  iframe H Hh
  ipureintro; exact heq

/-- xv6's client halves of the singleton regions before `cpus` (the locks, and
`started`), one by one. -/
def bootPreHalves (E : EraGS) (m : MemF Hist) : IProp GF := iprop%
  rsvRegionHalfC E (xv6LockR (rsvUartLk 0)) m ∗ rsvRegionHalfC E (xv6LockR (rsvUartLk 1)) m ∗
  rsvRegionHalfC E xv6StartedR m ∗ rsvRegionHalfC E (xv6LockR KA.«cons») m ∗ rsvRegionHalfC E (xv6LockR KA.«pr») m ∗
  rsvRegionHalfC E (xv6LockR KA.«kmem») m ∗
  rsvRegionHalfC E (xv6LockR KA.«pid_lock») m ∗ rsvRegionHalfC E (xv6LockR KA.«wait_lock») m

/-- xv6's client halves of the locks after `proc`, by group. -/
def bootPostHalves (E : EraGS) (m : MemF Hist) : IProp GF := iprop%
  rsvRegionHalfC E (xv6LockR KA.«tickslock») m ∗ rsvRegionHalfC E (xv6LockR KA.«bcache») m ∗
  ([∗list] i ∈ List.range 30, rsvRegionHalfC E (xv6LockR (rsvBufLk i)) m) ∗
  rsvRegionHalfC E (xv6LockR KA.«itable») m ∗
  ([∗list] k ∈ List.range 50, rsvRegionHalfC E (xv6LockR (rsvInodeLk k)) m) ∗
  rsvRegionHalfC E (xv6LockR KA.«log») m ∗
  rsvRegionHalfC E (xv6LockR KA.«ftable») m ∗ rsvRegionHalfC E (xv6LockR rsvDiskLk) m

/-- **xv6's client halves, by group** (`xv6RsvStatic_eq`): the singleton locks
before `cpus`, one region per hart, one per `proc[i].lock`, the singleton
locks after `proc`. -/
theorem bootRsvHalves (E : EraGS) (m : MemF Hist) :
    rsvHalvesC (GF := GF) E KernelRsv.static m ⊢
      bootPreHalves E m ∗
      ([∗list] c ∈ cpus, rsvRegionHalfC E ⟨cpuAddr c, .cpu c⟩ m) ∗
      ([∗list] i ∈ List.range 64, rsvRegionHalfC E (xv6LockR (rsvProcLk i)) m) ∗
      bootPostHalves E m := by
  have hc : ([∗list] R ∈ xv6CpuRegions, rsvRegionHalfC (GF := GF) E R m) ⊢
      [∗list] c ∈ cpus, rsvRegionHalfC E ⟨cpuAddr c, .cpu c⟩ m := by
    unfold xv6CpuRegions; rw [BigSepL.bigSepL_map]
  have hp : ([∗list] R ∈ xv6ProcLockRegions, rsvRegionHalfC (GF := GF) E R m) ⊢
      [∗list] i ∈ List.range 64, rsvRegionHalfC E (xv6LockR (rsvProcLk i)) m := by
    unfold xv6ProcLockRegions; rw [BigSepL.bigSepL_map]
  have hq : ([∗list] R ∈ xv6PreLockRegions, rsvRegionHalfC (GF := GF) E R m) ⊢ bootPreHalves E m := by
    unfold xv6PreLockRegions bootPreHalves
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H3, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H4, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H5, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H6, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H7, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H8, -⟩
    iframe H1 H2 H3 H4 H5 H6 H7 H8
  have hb : ([∗list] R ∈ xv6BufLockRegions, rsvRegionHalfC (GF := GF) E R m) ⊢
      [∗list] i ∈ List.range 30, rsvRegionHalfC E (xv6LockR (rsvBufLk i)) m := by
    unfold xv6BufLockRegions; rw [BigSepL.bigSepL_map]
  have hi : ([∗list] R ∈ xv6InodeLockRegions, rsvRegionHalfC (GF := GF) E R m) ⊢
      [∗list] k ∈ List.range 50, rsvRegionHalfC E (xv6LockR (rsvInodeLk k)) m := by
    unfold xv6InodeLockRegions; rw [BigSepL.bigSepL_map]
  have hr : ([∗list] R ∈ xv6PostLockRegions, rsvRegionHalfC (GF := GF) E R m) ⊢ bootPostHalves E m := by
    unfold xv6PostLockRegions bootPostHalves
    iintro H
    icases BigSepL.bigSepL_append.1 $$ H with ⟨H12, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H12 with ⟨H1, H12⟩
    icases BigSepL.bigSepL_cons.1 $$ H12 with ⟨H2, -⟩
    icases BigSepL.bigSepL_append.1 $$ H with ⟨Hb, H⟩
    icases BigSepL.bigSepL_append.1 $$ H with ⟨H3, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H3 with ⟨H3, -⟩
    icases BigSepL.bigSepL_append.1 $$ H with ⟨Hi, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H4, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H5, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H6, -⟩
    ihave Hb := hb $$ Hb
    ihave Hi := hi $$ Hi
    iframe H1 H2 Hb H3 Hi H4 H5 H6
  unfold rsvHalvesC
  show iprop([∗list] R ∈ xv6RsvStatic, rsvRegionHalfC E R m) ⊢ _
  rw [xv6RsvStatic_eq]
  iintro H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨Hq, H⟩
  icases BigSepL.bigSepL_append.1 $$ H with ⟨Hc, H⟩
  icases BigSepL.bigSepL_append.1 $$ H with ⟨Hp, Hr⟩
  ihave Hq := hq $$ Hq
  ihave Hc := hc $$ Hc
  ihave Hp := hp $$ Hp
  ihave Hr := hr $$ Hr
  iframe Hq Hc Hp Hr

end

end Xv6
