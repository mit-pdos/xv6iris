/-
Weak: **CONSTRAINT E — the S-mode 4-byte fetch arm**: an S-mode instance of
`SpineFetch4T` (`SpineFetch4TS`) at the kernel regime `ctrlOkS` for the text predicate
`textAt4S`.

Rocq: `iris/AxDataX6.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`textAt4S pc w32`: `pc` is 4-aligned, its page is mapped by the image tree `T` (three slots in
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

**Rocq → Lean name map.**  `execA_fetch_Base_4_S_gen` `execAFetchBase4SGen`, `text_at4_S`
`textAt4S`, `SpineFetch4T_S` `SpineFetch4TS`.  None is in the duplicated-name table; no
Lean-only declarations.

**Dropped:** the Ltac `nseip` (deviation 3); `Print Assumptions`.  Rocq 3 definitions/lemmas,
Lean 3.
-/
import Weak.AxSymCtl2
import Weak.AxSpineOk6

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

/-- Rocq `text_at4_S pc w32`: `pc` holds the 4-byte (non-compressed) instruction word `w32`
(deviation 2). -/
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
    is_aligned_vaddr (.Virtaddr pc) 4 = true ∧
    isRVC (Sail.BitVec.extractLsb w32 15 0) = false ∧
    inRam pa 4 ∧ is_aligned_paddr (.Physaddr pa) 4 = true ∧
    BytesAt σi pa 4 w32

/-- Rocq `SpineFetch4T_S`: THE 4-BYTE FETCH FIELD at the S-mode regime. -/
theorem SpineFetch4TS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) :
    SpineFetch4T (imgS σi) (ctrlOkS T satp0) (textAt4S σi T) := by
  intro t pc w32 hc hPC
    ⟨p2, p1, w, pa, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, hal4, hnRVC, hram, halp,
      hbytes⟩
  let σ : ExecSt := ⟨t.regs, σi.mem, t.dev⟩
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, -, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have heff := execEffectivePrivilegeFetch (σ.regs .mstatus) .Supervisor σ
  have hss := execIsShadowStackFetch σ
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    show WeakKpt.pmaAllowsPteRead (t.regs .pma_regions)
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have hs2' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 := hs2
  have hs1' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 := hs1
  have hs0' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w := hs0
  obtain ⟨σ', htr, hσ'⟩ := execATranslateAddrImg (.InstructionFetch ()) .Supervisor T.base pc w pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx hs2' hs1' hs0' hmisa
    hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR hcov hpmar
  have hc' : ctrlOkS T satp0 σ'.regs := by
    rcases hσ' with rfl | rfl
    · exact hc
    · exact ctrlOkSTlbFill T satp0 t.regs _ p2 p1 w _ hc hmaps rfl
  have hmem' : σ'.mem = σi.mem := by rcases hσ' with rfl | rfl <;> rfl
  have hc'0 := hc'
  obtain ⟨hpriv', -, -, -, -, -, -, -, -, -, -, -, hA', hord', hX', -, -⟩ := hc'0
  have hf : execA (fetch ()) σ = some (.F_Base w32, σ') := by
    obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
      ramFetchFacts T satp0 σ' pa 4 hc' (by decide) (by decide) (by decide) hram
    exact execAFetchBase4SGen pc pa w32 σ σ' region hPC hal4 htr hA' hord' hrange hX' hm halp hx
      hcl hsig hh hdev hwf (by intro j hj; rw [hmem']; exact hbytes j hj) hpriv' hnRVC
  refine ⟨⟨σ'.regs, t.mem, t.dev⟩, ?_, hc', ?_⟩
  · rcases hσ' with rfl | rfl
    · left; rfl
    · right; exact ⟨_, rfl⟩
  · have hE := execAEvA (fetch ()) σ _ σ' hf t rfl
    refine EvAMono (imgS σi) _ _ _ _ (fetch ()) t (fun _ _ hf => hf) ?_ hE
    rintro x ⟨r', m', d'⟩ ⟨rfl, hr, hm1, hd1⟩
    exact ⟨rfl, by simp only at hr hm1 hd1; subst hr hm1 hd1; rfl⟩

end Weak
