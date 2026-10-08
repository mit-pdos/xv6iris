/-
Weak: **CONSTRAINT E — the S-mode 4-byte fetch arm**: an S-mode instance of
`SpineFetch4T` (`SpineFetch4TS`) at the kernel regime `ctrlOkS` for the text predicate
`textAt4S`.

Rocq: `iris/AxDataX6.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`textAt4S pc w32`: `pc` is 4-aligned (Lean: or 2-aligned, deviation 6), its page is mapped by the image tree `T` (three slots in
the image, the leaf passes the fetch check with A preset), the image holds a word `w32` at the
translated pa in RAM, and its low half is NOT compressed.  Then the fetch returns `F_Base w32`
through the TLB hit / miss walk (`SpineFetch4TS`), so `X_fence_S` / `X_amo_S` / the 4-byte
control leaves can take `SpineFetch4TS` for their fetch premise.  `execAFetchBase4SGen` is the
`execA` replay of `SmodeCore.exec_fetch_F_Base_4_S_gen` (twin of `AxSpineOk3`'s
`execAFetchRVC4SGen`).

## Deviations from Rocq

1. SPELLING as `AxSpineOk6` deviation 1 (`mword n` ↦ `BitVec n`, `register_lookup r rs` ↦
   `rs r`, `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem`, `ptree_maps`/`pt_addr*` ↦ `AxPtProt.*`,
   `svpn_of` ↦ `WeakKpt.svpnOf`, the image byte window ↦ `BytesAt σi pa 4 w32`,
   `uint pa + 4 ≤ 2^64` ↦ `paZ pa + 4 ≤ 2 ^ 64`, `s.(mem) !! pa_add pa j = Some (nth_byte w j)`
   ↦ `BytesAt s1 pa 4 w`); the `satp0` hypotheses take `AxSpineOk6.sptFetchS`'s shapes.
2. `addr_is_ram pa ∧ addr_is_ram (pa_add pa 3)` ↦ `inRam pa 4` (`AxSpineOk6` deviation 4).
3. The Ltac `nseip` is dropped (pin tests are decided; `AxSpineOk3` deviation 5).
4. Section variables `σi T satp0` and hypotheses `Hmode Hasid Hppn` are explicit arguments
   (`textAt4S` takes `σi T`; `SpineFetch4TS` takes all six).
5. The `execA` replay's premise list is `AxSpineOk3.execAFetchRVC4SGen`'s (Lean PMP / PMA
   spellings); the last premise is `isRVC (extractLsb w 15 0) = false`.
6. Q22 (owner ruling, Lean only): KERNEL DRIFT puts many of this tree's 4-byte words at
   `pc ≡ 2 (mod 4)` (mycpu+0x0e/+0x12, push_off, pop_off+0x16, acquire+0x12, release's lock
   words, ...), where Rocq's `text_at4_S` (4-aligned only) is unsatisfiable.  `textAt4S` is
   GENERALISED IN PLACE (same name and arity, mirroring `textAtS`): the conjunct
   `is_aligned_vaddr pc 4` becomes `(access pc 0 != 0#1) = false`, and `is_aligned_paddr pa 4`
   becomes `if is_aligned_vaddr pc 4 then is_aligned_paddr pa 4 else (access pc 1 != 0#1) ∧
   is_aligned_paddr pa 2 ∧ pc[11:1] ≠ 0x7ff` (the last: pc does not straddle its page —
   provisional owner ruling Q22a — so ONE `ptreeMaps` serves both halfword translations).  The
   2-aligned arm is the model's two-halfword fetch: `execAFetchBase2SGen` (the `execA` twin of
   `ExecSC5.execFetchFBase2SGen`, two translations `s → s1 → s2`).  `SpineFetch4TS`'s statement
   is unchanged; its proof case-splits on the alignment (the 2-arm translates `pc` then
   `pc + 2` through `AxDataX6.trS`).  Lean-only helpers: `AxDataX6.addInt2`, `svpnOfAdd2`,
   `canonAdd2`, `paAdd2` (bv_decide), `alignedPaddrMod`, `alignedPaddr2Add2`, `inRamHi`,
   `bytesAtLo`, `bytesAtHi`, `execAFetch2Base`, `trS`.

**Rocq → Lean name map.**  `execA_fetch_Base_4_S_gen` `execAFetchBase4SGen`, `text_at4_S`
`textAt4S`, `SpineFetch4T_S` `SpineFetch4TS`.  None is in the duplicated-name table.
Lean-only (Q22, deviation 6): `execAFetchBase2SGen` and the `AxDataX6.*` helpers listed there.

**Dropped:** the Ltac `nseip` (deviation 3); `Print Assumptions`.  Rocq 3 definitions/lemmas,
Lean 3 + 12 Lean-only.
-/
import Weak.AxSymCtl2
import Weak.AxSpineOk6
import Weak.WeakFunnel

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `execA_fetch_Base_4_S_gen`: a 4-aligned non-compressed S-mode fetch at `execA`. -/
theorem execAFetchBase4SGen (va pa : BitVec 64) (w : BitVec 32) (s s1 : ExecSt)
    (region : PMA_Region) (hpc : s.regs .PC = va)
    (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = true)
    (htr : execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s1.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s1.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s1.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
      (to_bits (l := 64) 4).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s1.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s1.regs .pma_regions) (.Physaddr pa) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr pa) 4 = true)
    (hx : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : exec (within_clint (.Physaddr pa) 4) s1 = some (false, s1))
    (hsig : exec (within_sig (.Physaddr pa) 4) s1 = some (false, s1))
    (hh : exec (within_htif_readable (.Physaddr pa) 4) s1 = some (false, s1))
    (hdev : devAddr pa = false) (hwf : paZ pa + 4 ≤ 2 ^ 64) (hb : BytesAt s1 pa 4 w)
    (hpriv : s1.regs .cur_privilege = .Supervisor)
    (hrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    execA (fetch ()) s = some (.F_Base w, s1) := by
  have hfb := AxSpineOk3.execAFetchBytesOk va va pa 4 .PBMT_PMA w s s1 htr
    (execAMemReadFetch4S .PBMT_PMA pa region w s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf hb hpriv)
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execACatchEarlyReturn]
  simp (config := { decide := true }) only [execARBind, execARLiftR, execARReturnRFwd,
    readReg, PreSail.readReg, PreSail.emit, execA, hpc, bit0ClearOfAligned4 va hvalign,
    bit1ClearOfAligned4 va hvalign, hvalign, execACurrentlyEnabledZiccif, hfb, hrvc, ↓reduceIte,
    Bool.false_eq_true, Functions.not, Nat.reduceMul, BitVec.setWidth_eq]

/-! # Q22: the 2-aligned (two-halfword) arm -/

/-- (Lean-only, Q22) `addInt pc 2` is `pc + 2`. -/
theorem AxDataX6.addInt2 (pc : BitVec 64) : Sail.BitVec.addInt pc 2 = pc + 2#64 := rfl

/-- (Lean-only, Q22) a pc that does not straddle its page shares its Sv39 page with `pc + 2`. -/
theorem AxDataX6.svpnOfAdd2 (pc : BitVec 64)
    (h : (Sail.BitVec.extractLsb pc 11 1 != 0x7ff#11) = true) :
    WeakKpt.svpnOf (Sail.BitVec.addInt pc 2) = WeakKpt.svpnOf pc := by
  rw [AxDataX6.addInt2]
  change (BitVec.extractLsb 11 1 pc != 0x7ff#11) = true at h
  show BitVec.setWidth 27 (BitVec.extractLsb 38 12 (BitVec.extractLsb 38 0 (pc + 2#64))) =
    BitVec.setWidth 27 (BitVec.extractLsb 38 12 (BitVec.extractLsb 38 0 pc))
  revert h
  bv_decide

/-- (Lean-only, Q22) `pc + 2` is canonical when `pc` is and does not straddle its page. -/
theorem AxDataX6.canonAdd2 (pc : BitVec 64)
    (hc : (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false)
    (h : (Sail.BitVec.extractLsb pc 11 1 != 0x7ff#11) = true) :
    (Sail.BitVec.addInt pc 2 != sign_extend (m := 64) (Sail.BitVec.extractLsb (Sail.BitVec.addInt pc 2) 38 0))
      = false := by
  rw [AxDataX6.addInt2]
  change (pc != BitVec.signExtend 64 (BitVec.extractLsb 38 0 pc)) = false at hc
  change (BitVec.extractLsb 11 1 pc != 0x7ff#11) = true at h
  show (pc + 2#64 != BitVec.signExtend 64 (BitVec.extractLsb 38 0 (pc + 2#64))) = false
  revert hc h
  bv_decide

/-- (Lean-only, Q22) the physical address of `pc + 2` is two past `pc`'s (same page). -/
theorem AxDataX6.paAdd2 (q : BitVec 44) (pc : BitVec 64)
    (h : (Sail.BitVec.extractLsb pc 11 1 != 0x7ff#11) = true) :
    zero_extend (m := 64) (q +++ Sail.BitVec.extractLsb (Sail.BitVec.addInt pc 2) (Functions.pagesize_bits - 1) 0)
      = zero_extend (m := 64) (q +++ Sail.BitVec.extractLsb pc (Functions.pagesize_bits - 1) 0) + 2#64 := by
  rw [AxDataX6.addInt2]
  change (BitVec.extractLsb 11 1 pc != 0x7ff#11) = true at h
  show BitVec.setWidth 64 (q ++ BitVec.extractLsb 11 0 (pc + 2#64)) =
    BitVec.setWidth 64 (q ++ BitVec.extractLsb 11 0 pc) + 2#64
  revert h
  bv_decide

/-- (Lean-only, Q22) an aligned physical address is a multiple of the width. -/
theorem AxDataX6.alignedPaddrMod (a : BitVec 64) (w : Nat) (hw : 0 < w)
    (ha : is_aligned_paddr (.Physaddr a) w = true) : a.toNat % w = 0 := by
  unfold is_aligned_paddr at ha
  simp only [beq_iff_eq, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast] at ha
  have : Int.tmod (a.toNat : Int) (w : Int) = ((a.toNat % w : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]; push_cast; rfl
  omega

/-- (Lean-only, Q22) the high half of a 2-aligned RAM word is 2-aligned. -/
theorem AxDataX6.alignedPaddr2Add2 (pa : BitVec 64) (hram : inRam pa 4)
    (h : is_aligned_paddr (.Physaddr pa) 2 = true) :
    is_aligned_paddr (.Physaddr (pa + 2#64)) 2 = true := by
  have hm := AxDataX6.alignedPaddrMod pa 2 (by decide) h
  apply is_aligned_paddr_of _ 2 (by decide)
  have h2 := hram.2
  unfold ramEnd at h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- (Lean-only, Q22) a RAM word's two halves are RAM halfwords. -/
theorem AxDataX6.inRamHi (pa : BitVec 64) (h : inRam pa 4) : inRam pa 2 ∧ inRam (pa + 2#64) 2 := by
  obtain ⟨h1, h2⟩ := h
  unfold ramBase at h1
  unfold ramEnd at h2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    (try simp only [ramBase, ramEnd, BitVec.toNat_add, BitVec.toNat_ofNat]) <;> omega

/-- (Lean-only, Q22) the low half of a word's bytes. -/
theorem AxDataX6.bytesAtLo (s : ExecSt) (pa : BitVec 64) (w : BitVec 32) (h : BytesAt s pa 4 w) :
    BytesAt s pa 2 (Sail.BitVec.extractLsb w 15 0) := by
  intro j hj
  rw [nthByteLo w j hj]
  exact h j (by omega)

/-- (Lean-only, Q22) the high half of a word's bytes. -/
theorem AxDataX6.bytesAtHi (s : ExecSt) (pa : BitVec 64) (w : BitVec 32) (h : BytesAt s pa 4 w) :
    BytesAt s (pa + 2#64) 2 (Sail.BitVec.extractLsb w 31 16) := by
  intro j hj
  rw [nthByteHi w j hj]
  have e : pa + 2#64 + BitVec.ofNat 64 j = pa + BitVec.ofNat 64 (2 + j) := by
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact h (2 + j) (by omega)

/-- (Lean-only, Q22) the `execA` twin of `execFetch2Base`: a 2-aligned fetch whose two halfword
reads succeed and whose low half is not compressed. -/
theorem AxDataX6.execAFetch2Base (pc : BitVec 64) (lo hi : BitVec 16) (s s1 s2 : ExecSt)
    (hpc : s.regs .PC = pc)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false)
    (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hzca : execA (currentlyEnabled .Ext_Zca) s = some (true, s))
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hfb1 : execA (fetch_bytes pc pc 2) s = some (.FetchBytes_Success lo, s1))
    (hnr : isRVC lo = false) (hpc1 : s1.regs .PC = pc)
    (hfb2 : execA (fetch_bytes pc (Sail.BitVec.addInt pc 2) 2) s1 = some (.FetchBytes_Success hi, s2)) :
    execA (fetch ()) s = some (.F_Base (hi ++ lo), s2) := by
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execACatchEarlyReturn]
  simp (config := { decide := true }) only [execARBind, execARLiftR, execARReturnRFwd,
    readReg, PreSail.readReg, PreSail.emit, execA, hpc, hbit0, hbit1, hvalign, hzca, hfb1, hnr,
    hpc1, hfb2, ↓reduceIte, Bool.false_eq_true, Functions.not, Bool.not_true]

/-- (Lean-only, Q22) the `execA` twin of `ExecSC5.execFetchFBase2SGen`: a 2-aligned
non-compressed S-mode fetch — two translations `s → s1 → s2` and two 2-byte fetch reads (the
premise bundle of `execAFetchRVC2SGen`, at `s1`/`pal` and at `s2`/`pah`). -/
theorem execAFetchBase2SGen (va pal pah : BitVec 64) (w : BitVec 32) (s s1 s2 : ExecSt)
    (regl regh : PMA_Region) (hpc : s.regs .PC = va) (hpc1 : s1.regs .PC = va)
    (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hbit0 : (Sail.BitVec.access va 0 != 0#1) = false)
    (hbit1 : (Sail.BitVec.access va 1 != 0#1) = true)
    (hvalign4 : is_aligned_vaddr (.Virtaddr va) 4 = false)
    (htr1 : execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pal, .PBMT_PMA, ()), s1))
    (htr2 : execA (translateAddr (.Virtaddr (Sail.BitVec.addInt va 2)) (.InstructionFetch ())) s1
      = some (.Ok (.Physaddr pah, .PBMT_PMA, ()), s2))
    (hAl : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s1.regs .pmpcfg_n)[0]!) = .TOR)
    (hltl : zopz0zKzJ_u (zeros (n := 64)) (s1.regs .pmpaddr_n)[0]! = false)
    (hrl : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s1.regs .pmpaddr_n)[0]!.toNat * 4) pal.toNat
      (to_bits (l := 64) 2).toNat = .PMP_Match)
    (hXl : (_get_Pmpcfg_ent_X (s1.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hml : matching_pma_region (s1.regs .pma_regions) (.Physaddr pal) 2 = some regl)
    (hall : is_aligned_paddr (.Physaddr pal) 2 = true)
    (hxl : (override_PMA regl.attributes .PBMT_PMA).executable = true)
    (hcl : exec (within_clint (.Physaddr pal) 2) s1 = some (false, s1))
    (hsigl : exec (within_sig (.Physaddr pal) 2) s1 = some (false, s1))
    (hhl : exec (within_htif_readable (.Physaddr pal) 2) s1 = some (false, s1))
    (hdevl : devAddr pal = false) (hwfl : paZ pal + 2 ≤ 2 ^ 64)
    (hbl : BytesAt s1 pal 2 (Sail.BitVec.extractLsb w 15 0))
    (hprivl : s1.regs .cur_privilege = .Supervisor)
    (hAh : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s2.regs .pmpcfg_n)[0]!) = .TOR)
    (hlth : zopz0zKzJ_u (zeros (n := 64)) (s2.regs .pmpaddr_n)[0]! = false)
    (hrh : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s2.regs .pmpaddr_n)[0]!.toNat * 4) pah.toNat
      (to_bits (l := 64) 2).toNat = .PMP_Match)
    (hXh : (_get_Pmpcfg_ent_X (s2.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hmh : matching_pma_region (s2.regs .pma_regions) (.Physaddr pah) 2 = some regh)
    (halh : is_aligned_paddr (.Physaddr pah) 2 = true)
    (hxh : (override_PMA regh.attributes .PBMT_PMA).executable = true)
    (hch : exec (within_clint (.Physaddr pah) 2) s2 = some (false, s2))
    (hsigh : exec (within_sig (.Physaddr pah) 2) s2 = some (false, s2))
    (hhh : exec (within_htif_readable (.Physaddr pah) 2) s2 = some (false, s2))
    (hdevh : devAddr pah = false) (hwfh : paZ pah + 2 ≤ 2 ^ 64)
    (hbh : BytesAt s2 pah 2 (Sail.BitVec.extractLsb w 31 16))
    (hprivh : s2.regs .cur_privilege = .Supervisor)
    (hnot : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    execA (fetch ()) s = some (.F_Base w, s2) := by
  have hfb1 := AxSpineOk3.execAFetchBytesOk va va pal 2 .PBMT_PMA (Sail.BitVec.extractLsb w 15 0)
    s s1 htr1 (execAMemReadFetch2S .PBMT_PMA pal regl _ s1 hAl hltl hrl hXl hml hall hxl hcl hsigl
      hhl hdevl hwfl hbl hprivl)
  have hfb2 := AxSpineOk3.execAFetchBytesOk va (Sail.BitVec.addInt va 2) pah 2 .PBMT_PMA
    (Sail.BitVec.extractLsb w 31 16) s1 s2 htr2 (execAMemReadFetch2S .PBMT_PMA pah regh _ s2 hAh
      hlth hrh hXh hmh halh hxh hch hsigh hhh hdevh hwfh hbh hprivh)
  rw [AxDataX6.execAFetch2Base va _ _ s s1 s2 hpc hbit0 hbit1 (execACurrentlyEnabledZca s hmisaC)
    hvalign4 hfb1 hnot hpc1 hfb2]
  congr
  simp only [Sail.BitVec.extractLsb, Nat.reduceMul, BitVec.setWidth_eq]
  bv_decide

/-- Rocq `text_at4_S pc w32`: `pc` holds the 4-byte (non-compressed) instruction word `w32`
(deviation 2).  Q22 (deviation 6): BOTH alignments, mirroring `textAtS` — a 4-aligned `pc`
(Rocq's only case) needs a 4-aligned `pa`; a `pc ≡ 2 (mod 4)` is the model's two-halfword path
and needs a 2-aligned `pa` and a `pc` that does not straddle its page (`pc[11:1] ≠ 0x7ff`). -/
def textAt4S (σi : ExecSt) (T : PTree) (pc : BitVec 64) (w32 : BitVec 32) : Prop :=
  ∃ (p2 p1 w pa : BitVec 64),
    AxPtProt.ptreeMaps T (WeakKpt.svpnOf pc) p2 p1 w ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w ∧
    (∀ mxr dosum : Bool, pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum w) ∧
    update_PTE_Bits w (.InstructionFetch ()) = none ∧
    ptePbmt0 w ∧
    (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
    zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb pc (Functions.pagesize_bits - 1) 0)
      = pa ∧
    (Sail.BitVec.access pc 0 != 0#1) = false ∧
    isRVC (Sail.BitVec.extractLsb w32 15 0) = false ∧
    inRam pa 4 ∧
    (if is_aligned_vaddr (.Virtaddr pc) 4 then is_aligned_paddr (.Physaddr pa) 4 = true
     else (Sail.BitVec.access pc 1 != 0#1) = true ∧ is_aligned_paddr (.Physaddr pa) 2 = true ∧
       (Sail.BitVec.extractLsb pc 11 1 != 0x7ff#11) = true) ∧
    BytesAt σi pa 4 w32

/-- (Lean-only, Q22) THE IMAGE TRANSLATION at a regime state whose memory is the image's: the
result is the image pa, the state is unchanged or TLB-filled, the regime and the memory are kept. -/
theorem AxDataX6.trS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (σ : ExecSt) (hc : ctrlOkS T satp0 σ.regs) (hmem : σ.mem = σi.mem)
    (va w pa p2 p1 : BitVec 64)
    (hmaps : AxPtProt.ptreeMaps T (WeakKpt.svpnOf va) p2 p1 w)
    (hs2 : WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) p2)
    (hs1 : WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf va)) p1)
    (hs0 : WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) w)
    (hchk : ∀ mxr dosum : Bool, pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum w)
    (hupd : update_PTE_Bits w (.InstructionFetch ()) = none) (hpb : ptePbmt0 w)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hout : zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)
      = pa) :
    ∃ σ', execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) σ
        = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), σ') ∧
      (σ' = σ ∨ ∃ v : RegisterType .tlb, σ' = σ.setReg .tlb v) ∧
      ctrlOkS T satp0 σ'.regs ∧ σ'.mem = σi.mem := by
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, -, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have heff := execEffectivePrivilegeFetch (σ.regs .mstatus) .Supervisor σ
  have hss := execIsShadowStackFetch σ
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have tr : ∀ a v, WeakWalkEff.ptSlotMem σi a v → WeakWalkEff.ptSlotMem σ a v := by
    intro a v ⟨hb, h1, h2⟩
    exact ⟨fun j hj => by rw [hmem]; exact hb j hj, h1, h2⟩
  obtain ⟨σ', htr, hσ'⟩ := execATranslateAddrImg (.InstructionFetch ()) .Supervisor T.base va w pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx (tr _ _ hs2)
    (tr _ _ hs1) (tr _ _ hs0) hmisa hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR
    hcov hpmar
  refine ⟨σ', htr, ?_, ?_, ?_⟩
  · rcases hσ' with rfl | rfl
    · left; rfl
    · right; exact ⟨_, rfl⟩
  · rcases hσ' with rfl | rfl
    · exact hc
    · exact ctrlOkSTlbFill T satp0 σ.regs _ p2 p1 w _ hc hmaps rfl
  · rcases hσ' with rfl | rfl <;> exact hmem

/-- Rocq `SpineFetch4T_S`: THE 4-BYTE FETCH FIELD at the S-mode regime (Q22: both alignments;
the 2-aligned arm translates twice, `pc` then `pc + 2`, through the same page). -/
theorem SpineFetch4TS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) :
    SpineFetch4T (imgS σi) (ctrlOkS T satp0) (textAt4S σi T) := by
  intro t pc w32 hc hPC
    ⟨p2, p1, w, pa, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, hb0, hnRVC, hram, hal,
      hbytes⟩
  let σ : ExecSt := ⟨t.regs, σi.mem, t.dev⟩
  have hc0 := hc
  obtain ⟨-, -, hmisa, -⟩ := hc0
  obtain ⟨σ1, htr1, hfr1, hc1, hm1⟩ := AxDataX6.trS σi T satp0 hmode hasid hppn σ hc rfl pc w pa
    p2 p1 hmaps hs2 hs1 hs0 hchk hupd hpb hcanon hout
  have hc10 := hc1
  obtain ⟨hpriv1, -, -, -, -, -, -, -, -, -, -, -, hA1, hord1, hX1, -, -⟩ := hc10
  have hb1w : BytesAt σ1 pa 4 w32 := fun j hj => by rw [hm1]; exact hbytes j hj
  have key : ∃ σ2 : ExecSt, execA (fetch ()) σ = some (.F_Base w32, σ2) ∧
      (σ2 = σ ∨ ∃ v : RegisterType .tlb, σ2 = σ.setReg .tlb v) ∧ ctrlOkS T satp0 σ2.regs := by
    cases hal4 : is_aligned_vaddr (.Virtaddr pc) 4
    · rw [hal4] at hal
      simp only [Bool.false_eq_true, ↓reduceIte] at hal
      obtain ⟨hb1, halp, hns⟩ := hal
      have hv2 := AxDataX6.svpnOfAdd2 pc hns
      obtain ⟨σ2, htr2, hfr2, hc2, hm2⟩ := AxDataX6.trS σi T satp0 hmode hasid hppn σ1 hc1 hm1
        (Sail.BitVec.addInt pc 2) w (pa + 2#64) p2 p1 (by rw [hv2]; exact hmaps)
        (by rw [hv2]; exact hs2) (by rw [hv2]; exact hs1) (by rw [hv2]; exact hs0) hchk hupd hpb
        (AxDataX6.canonAdd2 pc hcanon hns) (by rw [AxDataX6.paAdd2 _ pc hns, hout])
      have hc20 := hc2
      obtain ⟨hpriv2, -, -, -, -, -, -, -, -, -, -, -, hA2, hord2, hX2, -, -⟩ := hc20
      have hb2w : BytesAt σ2 pa 4 w32 := fun j hj => by rw [hm2]; exact hbytes j hj
      obtain ⟨hraml, hramh⟩ := AxDataX6.inRamHi pa hram
      obtain ⟨regl, hrl, hml, hxl, hcll, hsigl, hhl, hdevl, hwfl⟩ :=
        ramFetchFacts T satp0 σ1 pa 2 hc1 (by decide) (by decide) (by decide) hraml
      obtain ⟨regh, hrh, hmh, hxh, hclh, hsigh, hhh, hdevh, hwfh⟩ :=
        ramFetchFacts T satp0 σ2 (pa + 2#64) 2 hc2 (by decide) (by decide) (by decide) hramh
      have hmC : (_get_Misa_C (σ.regs .misa) == 1#1) = true := by
        show (_get_Misa_C (t.regs .misa) == 1#1) = true
        rw [hmisa]; decide
      have hpc1 : σ1.regs .PC = pc := by
        rcases hfr1 with rfl | ⟨v, rfl⟩
        · exact hPC
        · show (t.regs.set .tlb v) .PC = pc
          rw [RegFile.set_other _ _ _ _ (by decide)]
          exact hPC
      refine ⟨σ2, execAFetchBase2SGen pc pa (pa + 2#64) w32 σ σ1 σ2 regl regh hPC hpc1 hmC hb0 hb1
        hal4 htr1 htr2 hA1 hord1 hrl hX1 hml halp hxl hcll hsigl hhl hdevl hwfl
        (AxDataX6.bytesAtLo _ _ _ hb1w) hpriv1 hA2 hord2 hrh hX2 hmh
        (AxDataX6.alignedPaddr2Add2 pa hram halp) hxh hclh hsigh hhh hdevh hwfh
        (AxDataX6.bytesAtHi _ _ _ hb2w) hpriv2 hnRVC, ?_, hc2⟩
      rcases hfr1 with rfl | ⟨v1, rfl⟩ <;> rcases hfr2 with rfl | ⟨v2, rfl⟩
      · left; rfl
      · right; exact ⟨v2, rfl⟩
      · right; exact ⟨v1, rfl⟩
      · right; exact ⟨v2, ExecSt.setReg_setReg_same _ _ _ _⟩
    · rw [hal4] at hal
      simp only [↓reduceIte] at hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFacts T satp0 σ1 pa 4 hc1 (by decide) (by decide) (by decide) hram
      exact ⟨σ1, execAFetchBase4SGen pc pa w32 σ σ1 region hPC hal4 htr1 hA1 hord1 hrange hX1 hm
        hal hx hcl hsig hh hdev hwf hb1w hpriv1 hnRVC, hfr1, hc1⟩
  obtain ⟨σ2, hf, hfr, hc2⟩ := key
  refine ⟨⟨σ2.regs, t.mem, t.dev⟩, ?_, hc2, ?_⟩
  · rcases hfr with rfl | ⟨v, rfl⟩
    · left; rfl
    · right; exact ⟨v, rfl⟩
  · have hE := execAEvA (fetch ()) σ _ σ2 hf t rfl
    refine EvAMono (imgS σi) _ _ _ _ (fetch ()) t (fun _ _ hf => hf) ?_ hE
    rintro x ⟨r', m', d'⟩ ⟨rfl, hr, hm1, hd1⟩
    exact ⟨rfl, by simp only at hr hm1 hd1; subst hr hm1 hd1; rfl⟩

end Weak
