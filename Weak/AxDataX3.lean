/-
Weak: **THE SYMBOLIC S-MODE DATA-SIDE TRANSLATION** — every premise of `AxDataX2`'s data-chain
lemmas (`rdPre` / `wrPre`) discharged at EVERY state of the S-mode kernel regime
`AxSpineOk6.ctrlOkS`, for a data access whose page is mapped by the image tree (`dataAtS`).

Rocq: `iris/AxDataX3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`dataAtS σi T acc va w pa`: the data address `va`'s page is mapped by `T` (three slots in the
image `σi`), the leaf passes `acc`'s check with A/D PRESET (`update_PTE_Bits = none`: no hardware
write-back — the mutable-PT / Svadu case is constraint A, see AxDataX5's PTE channel), `pa` is the
translation, the access is aligned and inside RAM.  `rdPreS` / `wrPreS`: from `ctrlOkS` at `t`,
`dataAtS`, and the effective address being `rs1 + imm`, the whole data-side premise set holds with
the walk's output state `s1` = `t`'s image state with at most the TLB filled (hit / miss,
`AxSpineOk4.execATranslateAddrImg`), and `ctrlOkS` still holds after.  Stores need the PMP W bit
(`pmpW`) — `ctrlOkS` (the FETCH regime) only records R/X.

## Deviations from Rocq

1. SPELLING as `AxSpineOk6` deviation 1 (`mword n` ↦ `BitVec n`, `register_lookup r rs` ↦ `rs r`,
   `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem`, `ptree_maps`/`pt_addr*` ↦ `AxPtProt.*`, `svpn_of` ↦
   `WeakKpt.svpnOf`, `eq_vec x y = b` ↦ `(x == y) = b`, `vec_access_dec v 0` ↦ `v[0]!`,
   `uint` ↦ `toNat` / `paZ`); `bits_of_virtaddr (Virtaddr va)` ↦ `va`; `PPN_of_PTE` ↦ `ppn0`
   (as `textAtS`); `add_vec (gpr_val rs rs1) (sign_extend' 64 imm)` ↦
   `gprVal t.regs rs1 + sign_extend (m := 64) imm`; `init_ext_ptw` ↦ `()`; the `satp0`
   hypotheses take `AxSpineOk6.sptFetchS`'s shapes.
2. `addr_is_ram pa ∧ addr_is_ram (pa_add pa (Z.to_nat (w - 1)))` ↦ `inRam pa w` (`AxSpineOk6`
   deviation 4), in `dataAtS`, `ramDataFacts`, `rdFactsS`, `wrFactsS`.  Widths are `Nat`
   (`AxDataX` deviation 4), `1 ≤ w ≤ 8` is `1 ≤ w → w ≤ 8 →`.
3. `pma_allows_all` ↦ `rs .pma_regions = bootPMA` (`AxSpineOk6` deviation 2): `ramDataFacts`'s
   region is `ramRegion`, its readable / writable bits by the Lean-only
   `AxDataX3.ramRegionReadable` / `AxDataX3.ramRegionWritable`; the `within_htif_writable` fact by
   the Lean-only `AxDataX3.execWithinHtifWNone` (Rocq `within_htif_writable_false`).
4. The Ltac `nseip3` is dropped (pin tests are decided; `AxSpineOk3` deviation 5).
5. Section variables `σi T satp0 dok` and hypotheses `Hmode Hasid Hppn` are explicit arguments
   (each declaration takes those it uses, in the section order).
6. `wrFactsS` uses `ExecSC4.execWithinMmioWritableFalse` for `within_mmio_writable` (Rocq: unfolds
   it through `or_boolM` / `and_boolM`, which the Lean model does not have).

**Rocq → Lean name map.**  `data_at_S` `dataAtS`, `pmpW` `pmpW`, `data_translate_S`
`dataTranslateS`, `ram_data_facts` `ramDataFacts`, `rd_facts_S` `rdFactsS`, `rd_pre_S` `rdPreS`,
`wr_facts_S` `wrFactsS`, `wr_pre_S` `wrPreS`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxDataX3.ramRegionReadable`, `AxDataX3.ramRegionWritable`,
`AxDataX3.execWithinHtifWNone`, `AxDataX3.toBitsSmall`, `AxDataX3.pmTransformVA0`.

**Dropped:** the Ltac `nseip3` (deviation 4).  Rocq 8 definitions/lemmas, Lean 8 + 5 Lean-only.
-/
import Weak.AxDataX2
import Weak.AxSpineOk6
import Weak.ExecSC7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `data_at_S` (deviations 1–2). -/
def dataAtS (σi : ExecSt) (T : PTree) (acc : MemoryAccessType mem_payload)
    (va : BitVec 64) (w : Nat) (pa : BitVec 64) : Prop :=
  ∃ (p2 p1 pte : BitVec 64),
    AxPtProt.ptreeMaps T (WeakKpt.svpnOf va) p2 p1 pte ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) p2 ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf va)) p1 ∧
    WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) pte ∧
    (∀ mxr dosum : Bool, pteCheckOk acc .Supervisor mxr dosum pte) ∧
    update_PTE_Bits pte acc = none ∧
    ptePbmt0 pte ∧
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false ∧
    zero_extend (m := 64) (ppn0 pte +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0)
      = pa ∧
    inRam pa w ∧
    is_aligned_vaddr (.Virtaddr va) w = true ∧ is_aligned_paddr (.Physaddr pa) w = true

/-- Rocq `pmpW`: the kernel PMP entry 0 grants W. -/
def pmpW (rs : RegFile) : Prop :=
  (_get_Pmpcfg_ent_W (rs .pmpcfg_n)[0]! == 1#1) = true

/-- (Lean-only, deviation 3) the RAM region is readable. -/
theorem AxDataX3.ramRegionReadable :
    (override_PMA ramRegion.attributes .PBMT_PMA).readable = true := by
  first
  | rfl
  | decide +kernel

/-- (Lean-only, deviation 3) the RAM region is writable. -/
theorem AxDataX3.ramRegionWritable :
    (override_PMA ramRegion.attributes .PBMT_PMA).writable = true := by
  first
  | rfl
  | decide +kernel

/-- (Lean-only, deviation 3; Rocq `within_htif_writable_false`). -/
theorem AxDataX3.execWithinHtifWNone (pa : BitVec 64) (n : Nat) (s : ExecSt)
    (h : s.regs .htif_tohost_base = none) :
    exec (within_htif_writable (.Physaddr pa) n) s = some (false, s) := by
  unfold within_htif_writable
  exec_run [h]

/-- (Lean-only) small widths survive `to_bits`. -/
theorem AxDataX3.toBitsSmall (w : Nat) (h1 : 1 ≤ w) (h8 : w ≤ 8) :
    (to_bits (l := 64) w).toNat = w := by
  have hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 := by omega
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- (Lean-only; Rocq `pm_transform_VA_0`) the zero pointer-masking transform is the identity. -/
theorem AxDataX3.pmTransformVA0 (v : BitVec 64) : pm_transform_VA (.Virtaddr v) 0 = .Virtaddr v := by
  simp only [pm_transform_VA, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, Functions.xlen]
  congr 1
  bv_decide

/-- Rocq `data_translate_S`: the walk at the image state, either access class. -/
theorem dataTranslateS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (acc : MemoryAccessType mem_payload) (t : ExecSt) (va : BitVec 64) (w : Nat) (pa : BitVec 64) :
    ctrlOkS T satp0 t.regs → dataAtS σi T acc va w pa →
    exec (effectivePrivilege acc (t.regs .mstatus) .Supervisor) (tσ σi t)
      = some (.Supervisor, tσ σi t) →
    exec (is_shadow_stack_access acc) (tσ σi t) = some (false, tσ σi t) →
    ∃ s1, execA (translateAddr (.Virtaddr va) acc) (tσ σi t)
            = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) ∧
          s1.mem = σi.mem ∧ s1.dev = t.dev ∧
          tlbFrame t ⟨s1.regs, t.mem, t.dev⟩ ∧ ctrlOkS T satp0 s1.regs := by
  intro hc hda heff hss
  obtain ⟨p2, p1, pte, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, -⟩ := hda
  let σ : ExecSt := tσ σi t
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, -, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    show WeakKpt.pmaAllowsPteRead (t.regs .pma_regions)
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have hs2' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) p2 := hs2
  have hs1' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf va)) p1 := hs1
  have hs0' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) pte := hs0
  obtain ⟨σ', htr, hσ'⟩ := execATranslateAddrImg acc .Supervisor T.base va pte pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx hs2' hs1' hs0' hmisa
    hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR hcov hpmar
  refine ⟨σ', htr, ?_, ?_, ?_, ?_⟩
  · rcases hσ' with rfl | rfl <;> rfl
  · rcases hσ' with rfl | rfl <;> rfl
  · rcases hσ' with rfl | rfl
    · left; rfl
    · right; exact ⟨_, rfl⟩
  · rcases hσ' with rfl | rfl
    · exact hc
    · exact ctrlOkSTlbFill T satp0 t.regs _ p2 p1 pte _ hc hmaps rfl

/-- Rocq `ram_data_facts`: the register-only RAM-access facts at a regime state, for the data pa. -/
theorem ramDataFacts (T : PTree) (satp0 : BitVec 64) (s : ExecSt) (pa : BitVec 64) (w : Nat) :
    ctrlOkS T satp0 s.regs → 1 ≤ w → w ≤ 8 → inRam pa w →
    ∃ region,
      pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
        (to_bits (l := 64) w).toNat = .PMP_Match ∧
      matching_pma_region (s.regs .pma_regions) (.Physaddr pa) w = some region ∧
      (override_PMA region.attributes .PBMT_PMA).readable = true ∧
      (override_PMA region.attributes .PBMT_PMA).writable = true ∧
      exec (within_clint (.Physaddr pa) w) s = some (false, s) ∧
      exec (within_sig (.Physaddr pa) w) s = some (false, s) ∧
      exec (within_htif_readable (.Physaddr pa) w) s = some (false, s) ∧
      exec (within_htif_writable (.Physaddr pa) w) s = some (false, s) ∧
      devAddr pa = false := by
  intro hc hw1 hw8 hram
  obtain ⟨-, -, -, -, hhtif, -, hpma, -, -, -, -, -, -, -, -, -, hcov⟩ := hc
  refine ⟨ramRegion, ?_, ?_, AxDataX3.ramRegionReadable, AxDataX3.ramRegionWritable,
    execWithinClintRam pa w s hram, execWithinSigFalse pa w s, execWithinHtifNone pa w s hhtif,
    AxDataX3.execWithinHtifWNone pa w s hhtif, devAddrRam pa w hram⟩
  · have hz : (zeros (n := 64)).toNat = 0 := rfl
    rw [hz, AxDataX3.toBitsSmall w hw1 hw8]
    exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by omega) (by have := hram.2; omega)
  · rw [hpma]; exact matching_pma_ram pa w hram (by omega) (by omega)

/-- Rocq `rd_facts_S`. -/
theorem rdFactsS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (t1 : ExecSt) (pa : BitVec 64)
    (w : Nat) :
    ctrlOkS T satp0 t1.regs → 1 ≤ w → w ≤ 8 → inRam pa w →
    is_aligned_paddr (.Physaddr pa) w = true →
    rdFacts σi (.Load .Data) .PBMT_PMA w pa t1 ∧ devAddr pa = false := by
  intro hc hw1 hw8 hram hal
  let s : ExecSt := tσ σi t1
  obtain ⟨region, hrange, hm, hrd, -, hcl, hsig, hh, -, hdev⟩ :=
    ramDataFacts T satp0 s pa w hc hw1 hw8 hram
  have hc0 := hc
  obtain ⟨hpriv, -, -, -, -, -, -, hms, -, -, -, -, hA, hord, -, hR, -⟩ := hc0
  obtain ⟨hMPRV, -⟩ := hms
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hdev⟩
  · rw [hpriv]
    have he := execEffectivePrivilegeLoadS (t1.regs .mstatus) s hMPRV
    to_a he
    exact he
  · have hcp : exec (check_pma_with_pmp_priority (.Load .Data) .PBMT_PMA .Supervisor (.Physaddr pa) w
        false) s = some (.Ok pmaOkAligned, s) := by
      unfold check_pma_with_pmp_priority
      rw [execBindSome _ _ _ _ _ (execPmaCheckRamLoadG w pa .PBMT_PMA region s hm hal hrd)]
      rfl
    to_a hcp
    exact hcp
  · have hp := execPmpCheckSupervisorGrantLoadData pa w s hA hord hrange hR
    to_a hp
    exact hp
  · exact execAMmioFalse pa w s hcl hsig hh

/-- Rocq `rd_pre_S`. -/
theorem rdPreS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (imm : BitVec 12) (rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64) (t : ExecSt) :
    ctrlOkS T satp0 t.regs → dataAtS σi T (.Load .Data) va w pa → vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal t.regs rs1 + sign_extend (m := 64) imm → dok (paZ pa) w →
    ∃ s1, rdPre dok σi imm rs1 w va pa .Sv39 t s1 ∧
      tlbFrame t ⟨s1.regs, t.mem, t.dev⟩ ∧ ctrlOkS T satp0 s1.regs := by
  intro hc hda hvw hw1 hw8 hva hdok
  have hc0 := hc
  obtain ⟨hpriv, -, -, hmenv, -, -, -, hms, -, -, hsatp, -⟩ := hc0
  obtain ⟨hMPRV, hSXL, hMXR, -⟩ := hms
  let σ : ExecSt := tσ σi t
  have heff : exec (effectivePrivilege (.Load .Data) (t.regs .mstatus) .Supervisor) σ
      = some (.Supervisor, σ) := execEffectivePrivilegeLoadS _ σ hMPRV
  have hss : exec (is_shadow_stack_access (.Load .Data)) σ = some (false, σ) := rfl
  obtain ⟨s1, htr, -, -, hfr, hc1⟩ :=
    dataTranslateS σi T satp0 hmode hasid hppn (.Load .Data) t va w pa hc hda heff hss
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hram, hal, hpal⟩ := hda
  refine ⟨s1, ?_, hfr, hc1⟩
  obtain ⟨hrf, hdev⟩ := rdFactsS σi T satp0 ⟨s1.regs, t.mem, t.dev⟩ pa w hc1 hw1 hw8 hram hpal
  refine ⟨hw8, ?_, hvw, hal, ?_, ?_, htr, hrf, hdev, hdok⟩
  · have hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (σ.regs .menvcfg)) = .PMM_Disabled := by
      show pmm_mode_backwards (_get_MEnvcfg_PMM (t.regs .menvcfg)) = .PMM_Disabled
      rw [hmenv]
      first
      | rfl
      | decide +kernel
    have hg : exec (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Load .Data) w) σ
        = some (.Ext_DataAddr_OK (.Virtaddr va), σ) := by
      unfold get_transformed_data_addr
      rw [execBindSome _ _ _ _ _ (execExtDataGetAddrGpr rs1 _ (.Load .Data) w σ)]
      dsimp only
      rw [execBindSome _ _ _ _ _ (execTransformEffectiveAddressLoadS _ satp0 σ hpriv hSXL hsatp hmode
        hMPRV hMXR hpmm)]
      rw [AxDataX3.pmTransformVA0, hva]
      rfl
    to_a hg
    exact hg
  · rw [hpriv]
    to_a heff
    exact heff
  · have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
    to_a htm
    exact htm

/-- Rocq `wr_facts_S`. -/
theorem wrFactsS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (t1 : ExecSt) (pa : BitVec 64)
    (w : Nat) :
    ctrlOkS T satp0 t1.regs → pmpW t1.regs → 1 ≤ w → w ≤ 8 → inRam pa w →
    is_aligned_paddr (.Physaddr pa) w = true →
    wrFacts σi (.Store .Data) .PBMT_PMA w pa t1 ∧ devAddr pa = false := by
  intro hc hW hw1 hw8 hram hal
  let s : ExecSt := tσ σi t1
  obtain ⟨region, hrange, hm, -, hwr, hcl, hsig, -, hh, hdev⟩ :=
    ramDataFacts T satp0 s pa w hc hw1 hw8 hram
  have hc0 := hc
  obtain ⟨hpriv, -, -, -, -, -, -, hms, -, -, -, -, hA, hord, -, -, -⟩ := hc0
  obtain ⟨hMPRV, -⟩ := hms
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hdev⟩
  · rw [hpriv]
    have he := execEffectivePrivilegeStoreS (t1.regs .mstatus) s hMPRV
    to_a he
    exact he
  · have hcp : exec (check_pma_with_pmp_priority (.Store .Data) .PBMT_PMA .Supervisor (.Physaddr pa) w
        false) s = some (.Ok pmaOkAligned, s) := by
      unfold check_pma_with_pmp_priority
      rw [execBindSome _ _ _ _ _ (execPmaCheckRamStoreG w pa .PBMT_PMA region s hm hal hwr)]
      rfl
    to_a hcp
    exact hcp
  · have hp := execPmpCheckSupervisorGrantStore pa w s hA hord hrange hW
    to_a hp
    exact hp
  · have hmm := execWithinMmioWritableFalse pa w s hcl hsig hh
    to_a hmm
    exact hmm

/-- Rocq `wr_pre_S`. -/
theorem wrPreS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop)
    (imm : BitVec 12) (rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64) (t : ExecSt) :
    ctrlOkS T satp0 t.regs → pmpW t.regs → dataAtS σi T (.Store .Data) va w pa → vmemWidth w →
    1 ≤ w → w ≤ 8 →
    va = gprVal t.regs rs1 + sign_extend (m := 64) imm → dok (paZ pa) w →
    ∃ s1, wrPre dok σi imm rs1 w va pa .Sv39 t s1 ∧
      tlbFrame t ⟨s1.regs, t.mem, t.dev⟩ ∧ ctrlOkS T satp0 s1.regs := by
  intro hc hW hda hvw hw1 hw8 hva hdok
  have hc0 := hc
  obtain ⟨hpriv, -, -, hmenv, -, -, -, hms, -, -, hsatp, -⟩ := hc0
  obtain ⟨hMPRV, hSXL, hMXR, -⟩ := hms
  let σ : ExecSt := tσ σi t
  have heff : exec (effectivePrivilege (.Store .Data) (t.regs .mstatus) .Supervisor) σ
      = some (.Supervisor, σ) := execEffectivePrivilegeStoreS _ σ hMPRV
  have hss : exec (is_shadow_stack_access (.Store .Data)) σ = some (false, σ) := rfl
  obtain ⟨s1, htr, -, -, hfr, hc1⟩ :=
    dataTranslateS σi T satp0 hmode hasid hppn (.Store .Data) t va w pa hc hda heff hss
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hram, hal, hpal⟩ := hda
  refine ⟨s1, ?_, hfr, hc1⟩
  have hW1 : pmpW s1.regs := by
    rcases hfr with heq | ⟨v, heq⟩
    · have hr : s1.regs = t.regs := by have h' := congrArg ExecSt.regs heq; exact h'
      rw [hr]; exact hW
    · have hr : s1.regs = (t.setReg .tlb v).regs := by
        have h' := congrArg ExecSt.regs heq; exact h'
      rw [hr]
      unfold pmpW
      simp (disch := decide) only [ExecSt.setReg_regs, RegFile.set_other]
      exact hW
  obtain ⟨hwf, hdev⟩ := wrFactsS σi T satp0 ⟨s1.regs, t.mem, t.dev⟩ pa w hc1 hW1 hw1 hw8 hram hpal
  refine ⟨hw8, ?_, hvw, hal, ?_, ?_, htr, hwf, hdev, hdok⟩
  · have hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (σ.regs .menvcfg)) = .PMM_Disabled := by
      show pmm_mode_backwards (_get_MEnvcfg_PMM (t.regs .menvcfg)) = .PMM_Disabled
      rw [hmenv]
      first
      | rfl
      | decide +kernel
    have hg : exec (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Store .Data) w) σ
        = some (.Ext_DataAddr_OK (.Virtaddr va), σ) := by
      unfold get_transformed_data_addr
      rw [execBindSome _ _ _ _ _ (execExtDataGetAddrGpr rs1 _ (.Store .Data) w σ)]
      dsimp only
      rw [execBindSome _ _ _ _ _ (execTransformEffectiveAddressStoreS _ satp0 σ hpriv hSXL hsatp hmode
        hMPRV hMXR hpmm)]
      rw [hva]
      rfl
    to_a hg
    exact hg
  · rw [hpriv]
    to_a heff
    exact heff
  · have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
    to_a htm
    exact htm

end Weak
