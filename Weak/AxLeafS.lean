/-
Weak: **S-mode X LEAVES for xv6's lock code, part 1 (PURE): the DATA-SIDE REGIME and the AMO
certificate with an EXACT post.**

Rocq: `iris/AxLeafS.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 THE DATA-SIDE REGIME.  `ctrlOkS` (AxSpineOk6) is the FETCH regime: it records PMP R/X only.
Stores and AMOs need the PMP W bit (`pmpW`); the regime for every lock leaf is
`ctrlOkSW = ctrlOkS ∧ pmpW`.  The atomic PMA grant is not a new regime fact (the RAM region of
the boot PMA grants it — `ramAmoFacts` extracts it).  Generic transfer: `SpineOkTAnd` /
`SpineFetch4TAnd` / `SpineOkIAnd` — a spine at `C` gives the spine at `C ∧ P` for any side
predicate `P` that depends only on `dregs` (`pDep`: not a pin, not a `ctrlFree` register, not
the TLB, not mcycle / mtime / mip, not a trap-entry register).  The tick field is REPLAYED
through `sptTickFrame` (only `C`'s stability under `tickFrame` is used).  Instances:
`SpineOkTSW`, `SpineFetch4TSW`, and the SIE-agnostic twin `ctrlOkSIW = ctrlOkSI ∧ pmpW` with
`SpineOkISIW`.
§2 THE AMO.  `amoFactsS`: `amoFacts` discharged at every state of `ctrlOkSW` for an aligned
4-byte RAM pa.  `CertExecuteAMOSWAPX`: `AxDataX7.CertExecuteAMOSWAP` with the post SHARPENED to
exact values — read bytes `vs` demonic, written bytes `wrb w (amoStv w rs2)`, rd :=
`amoLdv w vs`, final state `wrOpt (some (rd, amoLdv w vs))` of the post-walk state.
`CertXTAmoswapS`: the TLB-framed whole-execute certificate (`CertXT`) for `amoswap.w{.aq}` at
`ctrlOkSW`, from `dataAtS` for the Atomic access.

## Deviations from Rocq

1. SPELLING as AxDataX3/X4/X7 (`mword n` ↦ `BitVec n`, `register_lookup r rs` ↦ `rs r`,
   `seip_reg` ↦ `AxRunClose.pinReg`, `In r dregs` ↦ `r ∈ dregs`, `uint` ↦ `toNat` / `paZ`,
   `gpr_val` ↦ `gprVal`, `zeros' 64` ↦ `zeros (n := 64)`, `img_S` ↦ `imgS`, `trap_st` ↦
   `trapSt`, `MState s1.(sregs) t.(mem) t.(mdev)` ↦ `⟨s1.regs, t.mem, t.dev⟩`, `Cert` ↦
   `AxCert.Cert`, `CS d b r` ↦ `⟨d, b, r⟩`); satp hypotheses take `AxSpineOk6.sptFetchS`'s
   shapes; section variables / hypotheses are explicit arguments (each declaration takes those
   it uses, as Rocq's section discharge).
2. RAM: `addr_is_ram pa ∧ addr_is_ram (pa_add pa 3)` ↦ `inRam pa 4` (AxDataX3 deviation 2);
   `pma_allows_all` ↦ `rs .pma_regions = bootPMA` (AxSpineOk6 deviation 2), so `ramAmoFacts`'s
   region is `ramRegion` and the atomic grant is a closed computation.
3. WIDTHS (AxDataX7 deviation 2): `0 < w → w ≤ 8` ↦ `vmemWidth w`; `amoStv` is
   `sign_extend (m := 8 * w) (trunc (m := w * 8) v)` and `amoLdv` is
   `sign_extend (m := 64) (rrv w vs)` (no autocast: `rrv` is already `BitVec (8 * w)`).
   `CertExecuteAMOSWAPX` keeps Rocq's `rd.toNat ≠ 0` premise (unused: the Lean rd write is one
   uniform step, AxDataX7 deviation 3).
4. `amoFactsS` uses `ExecSC4.execWithinMmioWritableFalse` (Rocq unfolds `or_boolM` /
   `and_boolM`, which the Lean model does not have).  `accAmo` is an `abbrev` (it must unfold
   when matched against the model's literal access).
5. The Ltac `nseipL` and the section notations `EvM` / `CP` / `CM` are not ported (written out).

**Rocq → Lean name map.**  `dregs` `dregs`, `P_dep` `pDep`, `pmpW_dep` `pmpWDep`,
`dregs_not_seip` `dregsNotSeip`, `dregs_not_free` `dregsNotFree`, `P_seip` `pSeip`, `P_frame`
`pFrame`, `P_tlb_frame` `pTlbFrame`, `P_tick` `pTick`, `P_trap` `pTrap`, `SpineOkT_and`
`SpineOkTAnd`, `SpineFetch4T_and` `SpineFetch4TAnd`, `SpineOkI_and` `SpineOkIAnd`,
`tick_frame_ctrl_S` `tickFrameCtrlS`, `SpineOkT_SW` `SpineOkTSW`, `SpineFetch4T_SW`
`SpineFetch4TSW`, `ctrl_ok_SIW` `ctrlOkSIW`, `SpineOkI_SIW` `SpineOkISIW`, `ctrl_ok_SW_SIW`
`ctrlOkSWSIW`, `amo_stv` `amoStv`, `amo_ldv` `amoLdv`, `acc_amo` `accAmo`, `ram_amo_facts`
`ramAmoFacts`, `exec_transform_effective_address_amo_S` `execTransformEffectiveAddressAmoS`,
`amo_facts_S` `amoFactsS`, `Cert_execute_AMOSWAP_x` `CertExecuteAMOSWAPX`, `ow_amo` `owAmo`,
`CertXT_amoswap_S` `CertXTAmoswapS`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 28 definitions/lemmas + 3 Ltacs; Lean 28).  **Not ported:** the Ltacs
`nseipL`, `a_use`, `a_useT` (deviation 5; AxDataX7.cRUse / cRUseT) and the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxIntr3
import Weak.AxSpineOk7
import Weak.AxDataX4
import Weak.AxDataX6
import Weak.AxDataX7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The data-side regime -/

/-- Rocq `dregs`: the registers a side predicate may depend on. -/
def dregs : List Register := [.pmpcfg_n, .pma_regions]

/-- Rocq `P_dep`. -/
def pDep (P : RegFile → Prop) : Prop :=
  ∀ rs rs', (∀ r, r ∈ dregs → rs' r = rs r) → P rs → P rs'

/-- Rocq `pmpW_dep`. -/
theorem pmpWDep : pDep pmpW := by
  intro rs rs' hag h
  unfold pmpW at h ⊢
  rw [hag .pmpcfg_n (by simp [dregs])]
  exact h

/-- Rocq `dregs_not_seip`. -/
theorem dregsNotSeip (r : Register) : r ∈ dregs → ¬ AxRunClose.pinReg r := by
  intro hr hp
  simp only [dregs, List.mem_cons, List.not_mem_nil, or_false] at hr
  unfold AxRunClose.pinReg at hp
  rcases hr with rfl | rfl <;> rcases hp with h | h <;> cases h

/-- Rocq `dregs_not_free`. -/
theorem dregsNotFree (r r' : Register) : ctrlFree r → r' ∈ dregs → r' ≠ r := by
  intro hf hin e
  subst e
  rcases hf with rfl | rfl | rfl | rfl | hg
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · have h : ∀ x ∈ dregs, x ∉ uxaGprs := by decide
    exact h _ hin hg

section andSec
variable (P : RegFile → Prop) (HP : pDep P)
include HP

/-- Rocq `P_seip`. -/
theorem pSeip (rs rs' : RegFile) : P rs → regsAgree AxRunClose.pinReg rs' rs → P rs' :=
  fun hp hag => HP rs rs' (fun r hr => hag r (dregsNotSeip r hr)) hp

/-- Rocq `P_frame`. -/
theorem pFrame (rs : RegFile) (r : Register) (v : RegisterType r) :
    ctrlFree r → P rs → P (rs.set r v) :=
  fun hf hp => HP rs _ (fun r' hr' => RegFile.set_other _ _ _ _ (dregsNotFree r r' hf hr')) hp

/-- Rocq `P_tlb_frame`. -/
theorem pTlbFrame (t t1 : ExecSt) : tlbFrame t t1 → P t.regs → P t1.regs := by
  intro hfr hp
  refine HP t.regs t1.regs (fun r hr => tlbFrameLookup t t1 r hfr ?_) hp
  have h : ∀ x ∈ dregs, x ≠ .tlb := by decide
  exact h r hr

/-- Rocq `P_tick`. -/
theorem pTick (t t' : ExecSt) : tickFrame t t' → P t.regs → P t'.regs := by
  intro hf hp
  refine HP t.regs t'.regs (fun r hr => ?_) hp
  have h : ∀ x ∈ dregs, x ≠ .mcycle ∧ x ≠ .mtime ∧ x ≠ .mip := by decide
  obtain ⟨h1, h2, h3⟩ := h r hr
  exact hf r h1 h2 h3

/-- Rocq `P_trap`. -/
theorem pTrap (t : ExecSt) (ip : InterruptType) : P t.regs → P (trapSt t ip).regs := by
  intro hp
  refine HP t.regs _ (fun r hr => ?_) hp
  have h : ∀ x ∈ dregs, x ≠ .mstatus ∧ x ≠ .elp ∧ x ≠ .scause ∧ x ≠ .stval ∧ x ≠ .sepc ∧
      x ≠ .cur_privilege ∧ x ≠ .nextPC := by decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h r hr
  exact trapStOther t ip r h1 h2 h3 h4 h5 h6 h7

end andSec

/-- Rocq `SpineOkT_and`. -/
theorem SpineOkTAnd (img : Image) (C P : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (HP : pDep P) (HCtick : ∀ t t', tickFrame t t' → C t.regs → C t'.regs) :
    SpineOkT img C textAt → SpineOkT img (fun rs => C rs ∧ P rs) textAt := by
  intro Hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rs rs' ⟨hc, hp⟩ hag
    exact ⟨Hs.sptSeip rs rs' hc hag, pSeip P HP rs rs' hp hag⟩
  · intro rs ⟨hc, _⟩
    exact Hs.sptHart rs hc
  · intro rs r v hf ⟨hc, hp⟩
    exact ⟨Hs.sptFrame rs r v hf hc, pFrame P HP rs r v hf hp⟩
  · intro t ⟨hc, _⟩
    exact Hs.sptInc t hc
  · intro t ⟨hc, _⟩
    exact Hs.sptDisp t hc
  · intro t pc h ⟨hc, hp⟩ hpc htx
    obtain ⟨t1, hfr, hc1, hE⟩ := Hs.sptFetch t pc h hc hpc htx
    exact ⟨t1, hfr, ⟨hc1, pTlbFrame P HP t t1 hfr hp⟩, hE⟩
  · intro t ⟨hc, _⟩
    exact Hs.sptLpad t hc
  · intro t ⟨hc, _⟩
    exact Hs.sptZca t hc
  · intro t ⟨hc, hp⟩
    refine EvAMono img _ _ _ _ _ t (fun _ _ h => h) ?_ (sptTickFrame img t)
    intro _ t' hf
    exact ⟨⟨HCtick _ _ hf hc, pTick P HP _ _ hf hp⟩, tickFrameKeep t t' hf⟩

/-- Rocq `SpineFetch4T_and`. -/
theorem SpineFetch4TAnd (img : Image) (C P : RegFile → Prop) (HP : pDep P)
    (textAt4 : BitVec 64 → BitVec 32 → Prop) :
    SpineFetch4T img C textAt4 → SpineFetch4T img (fun rs => C rs ∧ P rs) textAt4 := by
  intro Hf t pc w ⟨hc, hp⟩ hpc htx
  obtain ⟨t1, hfr, hc1, hE⟩ := Hf t pc w hc hpc htx
  exact ⟨t1, hfr, ⟨hc1, pTlbFrame P HP t t1 hfr hp⟩, hE⟩

/-- Rocq `SpineOkI_and`. -/
theorem SpineOkIAnd (img : Image) (C P : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (HP : pDep P) (HCtick : ∀ t t', tickFrame t t' → C t.regs → C t'.regs) :
    SpineOkI img C textAt → SpineOkI img (fun rs => C rs ∧ P rs) textAt := by
  intro Hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rs rs' ⟨hc, hp⟩ hag
    exact ⟨Hs.spiSeip rs rs' hc hag, pSeip P HP rs rs' hp hag⟩
  · intro rs ⟨hc, _⟩
    exact Hs.spiHart rs hc
  · intro rs r v hf ⟨hc, hp⟩
    exact ⟨Hs.spiFrame rs r v hf hc, pFrame P HP rs r v hf hp⟩
  · intro t ⟨hc, _⟩
    exact Hs.spiInc t hc
  · intro t ⟨hc, _⟩
    exact Hs.spiDisp t hc
  · intro t ip ⟨hc, _⟩ hon
    exact Hs.spiTrap t ip hc hon
  · intro t ip ⟨hc, hp⟩
    exact ⟨Hs.spiTrapOk t ip hc, pTrap P HP t ip hp⟩
  · intro t pc h ⟨hc, hp⟩ hpc htx
    obtain ⟨t1, hfr, hc1, hE⟩ := Hs.spiFetch t pc h hc hpc htx
    exact ⟨t1, hfr, ⟨hc1, pTlbFrame P HP t t1 hfr hp⟩, hE⟩
  · intro t ⟨hc, _⟩
    exact Hs.spiLpad t hc
  · intro t ⟨hc, _⟩
    exact Hs.spiZca t hc
  · intro t ⟨hc, hp⟩
    refine EvAMono img _ _ _ _ _ t (fun _ _ h => h) ?_ (sptTickFrame img t)
    intro _ t' hf
    exact ⟨⟨HCtick _ _ hf hc, pTick P HP _ _ hf hp⟩, hf⟩

/-- Rocq `tick_frame_ctrl_S`: `ctrlOkS` survives the tick frame. -/
theorem tickFrameCtrlS (T : PTree) (satp0 : BitVec 64) (t t' : ExecSt) :
    tickFrame t t' → ctrlOkS T satp0 t.regs → ctrlOkS T satp0 t'.regs := by
  intro hag hc
  have hc1 : ∀ r ∈ ctrlRegs, r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip := by decide
  refine ctrlOkSAgree T satp0 t.regs t'.regs (fun r hin => ?_) hc
  obtain ⟨h1, h2, h3⟩ := hc1 r hin
  exact hag r h1 h2 h3

section regime
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `SpineOkT_SW`: THE S-MODE KERNEL DATA REGIME (SIE = 0): the spine. -/
theorem SpineOkTSW (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) :
    SpineOkT (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) :=
  SpineOkTAnd _ (ctrlOkS T satp0) pmpW _ pmpWDep (tickFrameCtrlS T satp0)
    (spineOkTS σi T satp0 hmode hasid hppn)

/-- Rocq `SpineFetch4T_SW`. -/
theorem SpineFetch4TSW (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) :
    SpineFetch4T (imgS σi) (ctrlOkSW T satp0) (textAt4S σi T) :=
  SpineFetch4TAnd _ (ctrlOkS T satp0) pmpW pmpWDep _ (SpineFetch4TS σi T satp0 hmode hasid hppn)

/-- Rocq `ctrl_ok_SIW`: THE SIE-AGNOSTIC DATA REGIME. -/
def ctrlOkSIW (rs : RegFile) : Prop := ctrlOkSI T satp0 rs ∧ pmpW rs

/-- Rocq `SpineOkI_SIW`. -/
theorem SpineOkISIW (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) :
    SpineOkI (imgS σi) (ctrlOkSIW T satp0) (textAtS σi T) :=
  SpineOkIAnd _ (ctrlOkSI T satp0) pmpW _ pmpWDep (tickFrameCtrl T satp0)
    (spineOkIS σi T satp0 hmode hasid hppn)

/-- Rocq `ctrl_ok_SW_SIW`. -/
theorem ctrlOkSWSIW (rs : RegFile) : ctrlOkSW T satp0 rs → ctrlOkSIW T satp0 rs :=
  fun ⟨hc, hW⟩ => ⟨ctrlOkSSI T satp0 rs hc, hW⟩

end regime

/-! # 2. The AMO -/

/-- Rocq `amo_stv`: the value an AMOSWAP of width `w` stores (rs2's low `w` bytes). -/
def amoStv (w : Nat) (v : BitVec 64) : BitVec (8 * w) :=
  sign_extend (m := 8 * w) (trunc (m := w * 8) v)

/-- Rocq `amo_ldv`: the value written to rd (the sign-extended read value). -/
def amoLdv (w : Nat) (vs : List (BitVec 8)) : BitVec 64 :=
  sign_extend (m := 64) (rrv w vs)

/-- Rocq `acc_amo`. -/
abbrev accAmo (aq : Bool) : MemoryAccessType mem_payload := .Atomic (.AMOSWAP, aq, false, .Data, .Data)

/-- Rocq `ram_amo_facts`: the RAM region facts of an AMO, including the ATOMIC GRANT. -/
theorem ramAmoFacts (T : PTree) (satp0 : BitVec 64) (s : ExecSt) (pa : BitVec 64) :
    ctrlOkS T satp0 s.regs → inRam pa 4 →
    ∃ region,
      pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
        (to_bits (l := 64) 4).toNat = .PMP_Match ∧
      matching_pma_region (s.regs .pma_regions) (.Physaddr pa) 4 = some region ∧
      (override_PMA region.attributes .PBMT_PMA).readable = true ∧
      (override_PMA region.attributes .PBMT_PMA).writable = true ∧
      pma_allows_atomic_op (override_PMA region.attributes .PBMT_PMA).atomic_support .AMOSWAP 4
        = true ∧
      exec (within_clint (.Physaddr pa) 4) s = some (false, s) ∧
      exec (within_sig (.Physaddr pa) 4) s = some (false, s) ∧
      exec (within_htif_readable (.Physaddr pa) 4) s = some (false, s) ∧
      exec (within_htif_writable (.Physaddr pa) 4) s = some (false, s) ∧
      devAddr pa = false := by
  intro hc hram
  obtain ⟨region, hrange, hm, hrd, hwr, hcl, hsig, hhr, hhw, hdev⟩ :=
    ramDataFacts T satp0 s pa 4 hc (by decide) (by decide) hram
  have hm' : matching_pma_region (s.regs .pma_regions) (.Physaddr pa) 4 = some ramRegion := by
    rw [hc.2.2.2.2.2.2.1]
    exact matching_pma_ram pa 4 hram (by omega) (by omega)
  have hreg : region = ramRegion := by
    rw [hm'] at hm
    exact (Option.some.inj hm).symm
  subst hreg
  refine ⟨ramRegion, hrange, hm, hrd, hwr, ?_, hcl, hsig, hhr, hhw, hdev⟩
  first
  | rfl
  | decide +kernel

/-- Rocq `exec_transform_effective_address_amo_S`. -/
theorem execTransformEffectiveAddressAmoS (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4) (aq : Bool) (ea : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Supervisor) (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2)
    (hsatp : s.regs .satp = satp0)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hmxr : (_get_Mstatus_MXR (s.regs .mstatus) == 0#1) = true)
    (hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (s.regs .menvcfg)) = .PMM_Disabled) :
    exec (transform_effective_address (.Virtaddr ea) (accAmo aq)) s = some (.Virtaddr ea, s) := by
  have hgen : exec (transform_effective_address (.Virtaddr ea) (accAmo aq)) s
      = some (pm_transform_VA (.Virtaddr ea) 0, s) := by
    unfold transform_effective_address
    exec_run [hcp, execEffectivePrivilegeAmoS _ aq false s hmprv, execGetPmlenAmoS aq false s hmxr hpmm,
      execTranslationModeSSv39 satp0 s hsxl hsatp hmode]
    rfl
  rw [hgen, AxDataX3.pmTransformVA0]

/-- Rocq `amo_facts_S`: `amoFacts` at every state of the data regime. -/
theorem amoFactsS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (aq : Bool) (t1 : ExecSt)
    (pa : BitVec 64) :
    ctrlOkSW T satp0 t1.regs → inRam pa 4 → is_aligned_paddr (.Physaddr pa) 4 = true →
    amoFacts σi (accAmo aq) .PBMT_PMA 4 pa t1 ∧ devAddr pa = false := by
  intro ⟨hc, hW⟩ hram hal
  let s : ExecSt := tσ σi t1
  obtain ⟨region, hrange, hm, hrd, hwr, hamo, hcl, hsig, hhr, hhw, hdev⟩ :=
    ramAmoFacts T satp0 s pa hc hram
  have hc0 := hc
  obtain ⟨hpriv, -, -, -, -, -, -, hms, -, -, -, -, hA, hord, -, hR, -⟩ := hc0
  obtain ⟨hMPRV, -⟩ := hms
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hdev⟩
  · rw [hpriv]
    have he := execEffectivePrivilegeAmoS (t1.regs .mstatus) aq false s hMPRV
    to_a he
    exact he
  · have hcp : exec (check_pma_with_pmp_priority (accAmo aq) .PBMT_PMA .Supervisor (.Physaddr pa) 4
        true) s = some (.Ok pmaOkAligned, s) := by
      unfold check_pma_with_pmp_priority
      rw [execBindSome _ _ _ _ _ (execPmaCheckRamAmo4 pa .PBMT_PMA region aq false s hm hal hrd hwr
        hamo)]
      rfl
    to_a hcp
    exact hcp
  · have hp := execPmpCheckSupervisorGrantAmo pa 4 aq false s hA hord hrange hR hW
    to_a hp
    exact hp
  · exact execAMmioFalse pa 4 s hcl hsig hhr
  · have hmm := execWithinMmioWritableFalse pa 4 s hcl hsig hhw
    to_a hmm
    exact hmm

/-! ## The sharpened AMOSWAP execute -/

section amox
variable (img : Image) (dok : Int → Nat → Prop) (σ : ExecSt) (himg : img = imgOf σ)
include himg

/-- Rocq `Cert_execute_AMOSWAP_x` (deviation 3). -/
theorem CertExecuteAMOSWAPX (aq : Bool) (rs2 rs1 rd : BitVec 5) (w : Nat) (va pa : BitVec 64)
    (Q : Cst → ExecutionResult → ExecSt → Prop) (r : Bool) (t s1 : ExecSt) :
    vmemWidth w → rd.toNat ≠ 0 →
    execA (get_transformed_data_addr (.Regidx rs1) (zeros (n := 64)) (accAmo aq) w) (tσ σ t)
      = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (translateAddr (.Virtaddr va) (accAmo aq)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    amoFacts σ (accAmo aq) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ →
    devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CRmw aq false vs (AxDataX.wrb w (amoStv w (gprVal s1.regs rs2))) (wcls akXc r), .BInf,
          false⟩
        RETIRE_SUCCESS (wrOpt (some (rd, amoLdv w vs)) ⟨s1.regs, t.mem, t.dev⟩)) →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨.CPend, .BInf, r⟩
      (execute (.AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, w, .Regidx rd))) t := by
  intro hw _hrd hgta hal htr hf hdev hdok hq
  show AxCert.Cert img dok .DKRmw _ Q _
    (execute_AMO .AMOSWAP aq false (.Regidx rs2) (.Regidx rs1) w (.Regidx rd)) t
  unfold execute_AMO
  apply CertCatchEarlyReturn
  have hw0 := hw
  rcases hw0 with rfl | rfl | rfl | rfl
  all_goals
    simp only [Bool.and_false]
    ax_cert4_go
    refine AxDataX7.cRUse himg (a := ()) rfl ?_
    ax_cert4_go
    refine AxDataX7.cRUse himg hgta ?_
    ax_cert4_go
    simp only [hal, Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    ax_cert4_go
    refine AxDataX7.cRUseT himg htr ?_
    ax_cert4_go
    refine AxCert4.cFactLift (CertMemWriteEaX img dok σ himg _ .PBMT_PMA _ pa
      (fun s' x t' => s' = ⟨.CPend, .BInf, r⟩ ∧ x = .Ok () ∧ t' = ⟨s1.regs, t.mem, t.dev⟩)
      .CPend r _ hf ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxCert4.cFactLift (CertMemReadX img dok σ himg _ .PBMT_PMA _ pa hw aq
      (fun s' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧ s' = ⟨.CRmwR aq vs, .BInf, r⟩ ∧
        x = .Ok (rrv _ vs) ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) r _ hf hdev hdok
      (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxCert4.cRUse (rf0EvA img _ _ (rf0RXBits rs2) _ _ _ (execRXBitsGpr rs2 _)) ?_
    ax_cert4_go
    refine AxCert4.cFactLift (CertMemWriteValueX img dok σ himg _ .PBMT_PMA _ pa hw _
      (fun s' x t' => s' = ⟨.CRmw aq false vs (AxDataX.wrb _ (amoStv _ (gprVal s1.regs rs2)))
          (wcls akXc r), .BInf, false⟩ ∧
        x = .Ok true ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) aq vs r _ hf hdev hdok ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxCert4.cRUse (rf0EvA img _ _ (rf0WXBits rd _) _ _ _ (execWXBitsGpr rd _ _)) ?_
    ax_cert4_go
    exact .cRet _ _ _ (hq vs hvs)

end amox

/-! ## The TLB-framed whole-execute certificate for `amoswap.w{.aq}` -/

/-- Rocq `ow_amo`. -/
def owAmo (rd : BitVec 5) (s : Cst) : Option (BitVec 5 × BitVec 64) :=
  match s.csD with
  | .CRmw _ _ rvs _ _ => some (rd, amoLdv 4 rvs)
  | _ => none

/-- Rocq `CertXT_amoswap_S`: THE AMO X-CERTIFICATE at every state of `ctrlOkSW` at `pc`, the
boundary's rs1 the (VA) lock address whose page the image tree maps for an Atomic access:
exclusive read DEMONIC (`vs`, 4 bytes), exclusive write of `wrb 4 (amoStv 4 rs2)`,
rd := `amoLdv 4 vs`, TLB possibly filled. -/
theorem CertXTAmoswapS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (rs : RegFile) (pc : BitVec 64) (aq : Bool) (rs2 rs1 rd : BitVec 5) (va pa : BitVec 64)
    (r : Bool) :
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + zeros (n := 64) →
    dataAtS σi T (accAmo aq) va 4 pa → dok (paZ pa) 4 →
    CertXT (imgS σi) dok .DKRmw (ctrlOkSW T satp0) rs pc
      (.AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd))
      (owAmo rd) ⟨.CPend, .BInf, r⟩
      (fun s => ∃ vs, s = ⟨.CRmw aq false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))
          (wcls akXc r), .BInf, false⟩ ∧ vs.length = 4) := by
  intro hrd hva hda hdok t ⟨hc, hW⟩ _ _ hag
  have hva' : va = gprVal t.regs rs1 + zeros (n := 64) := by
    rw [gprValAgree _ _ _ hag]; exact hva
  have hc0 := hc
  obtain ⟨hpriv, -, -, hmenv, -, -, -, hms, -, -, hsatp, -⟩ := hc0
  obtain ⟨hMPRV, hSXL, hMXR, -⟩ := hms
  let σ : ExecSt := tσ σi t
  have heff : exec (effectivePrivilege (accAmo aq) (t.regs .mstatus) .Supervisor) σ
      = some (.Supervisor, σ) := execEffectivePrivilegeAmoS _ aq false σ hMPRV
  have hss : exec (is_shadow_stack_access (accAmo aq)) σ = some (false, σ) :=
    execIsShadowStackAmo aq false σ
  obtain ⟨s1, htr, -, -, hfr, hc1⟩ :=
    dataTranslateS σi T satp0 hmode hasid hppn (accAmo aq) t va 4 pa hc hda heff hss
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hram, hal, hpal⟩ := hda
  have hW1 : pmpW s1.regs := AxDataX4.pmpWTlbFrame t s1.regs t.mem t.dev hW hfr
  obtain ⟨haf, hdev⟩ := amoFactsS σi T satp0 aq ⟨s1.regs, t.mem, t.dev⟩ pa ⟨hc1, hW1⟩ hram hpal
  have hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (σ.regs .menvcfg)) = .PMM_Disabled := by
    show pmm_mode_backwards (_get_MEnvcfg_PMM (t.regs .menvcfg)) = .PMM_Disabled
    rw [hmenv]
    first
    | rfl
    | decide +kernel
  have hg : exec (get_transformed_data_addr (.Regidx rs1) (zeros (n := 64)) (accAmo aq) 4) σ
      = some (.Ext_DataAddr_OK (.Virtaddr va), σ) := by
    unfold get_transformed_data_addr
    rw [execBindSome _ _ _ _ _ (execExtDataGetAddrGpr rs1 _ (accAmo aq) 4 σ)]
    dsimp only
    rw [execBindSome _ _ _ _ _ (execTransformEffectiveAddressAmoS satp0 hmode aq _ σ hpriv hSXL
      hsatp hMPRV hMXR hpmm)]
    rw [hva']
    rfl
  to_a hg
  refine CertExecuteAMOSWAPX (imgS σi) dok σi rfl aq rs2 rs1 rd 4 va pa _ r t s1
    (Or.inr (Or.inr (Or.inl rfl))) hrd hg hal htr haf hdev hdok ?_
  intro vs hvs
  have hsame : gprVal s1.regs rs2 = gprVal rs rs2 := by
    rw [← gprValAgree _ _ _ hag]
    exact AxSpineOk5.tlbFrameXget t ⟨s1.regs, t.mem, t.dev⟩ hfr rs2
  refine ⟨rfl, ⟨vs, ?_, hvs⟩, ⟨s1.regs, t.mem, t.dev⟩, hfr, ⟨hc1, hW1⟩, rfl⟩
  rw [hsame]

end Weak
