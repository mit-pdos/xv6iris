/-
Weak: **the 8-byte M-mode STORE at `execEff`** (M4 batch 1): the `execEff`
mirror of `ExecSC8.execExecuteSTORE8Gpr`, whose trace is ONE element,
`[.WEwrite ⟨false, false, false⟩ pa 8 vrs2]` -- the data write, and nothing else.

Rocq: `iris/WeakLeafEff8s.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakEffSkel` reduced a weak-memory leaf's
remaining obligation to TWO `execEff` facts -- the fetch's and the `execute`'s --
joined by `WeakEffSkel.execEffRiscvStepBase`.  This file is the second of those
for the 8-byte M-mode store.  Every other step of the `execute` (the register
reads, the address transform, the privilege and PMP/PMA checks, the misalignment
split, the one-turn split loop) is register-only and contributes the EMPTY
trace, which is the whole content of the statements: `WeakEff.wcertStoreGen`
needs `nowriteTrace` of the surroundings, which `quietTrace`
(`execEffQuietOfEmpty`) does not give, so the SC chain is mirrored step by step.
The PMP walk and the three MMIO-window probes enter as `execEff` premises
(`hpmpEff`, `hc`, `hsig`, `hh`), in the shape of their SC originals with `exec`
replaced by `execEff` and the empty trace attached.  The only memory-touching
step is `execEffWriteRamPlain8`, where the trace element is born; its access
kind `AK_explicit {AV_plain, AS_normal}` classifies to `⟨false, false, false⟩`.

Conventions: as `Weak/ExecSC*.lean` (GPRs `s.gpr i`; `register_lookup r s.(sregs)`
↦ `s.regs r`; `eq_vec x 'b"1"` ↦ `(x == 1#1)`; `MState s.(sregs) (write_bytes
s.(mem) pa n v) s.(mdev)` ↦ `s.setMem (bmWrite s.mem pa n v)`; `dev_addr pa =
false` ↦ `devAddr pa = false`; `tt` ↦ `()`) and `Weak/WeakLeafEffCommon.lean`'s
(`M X` ↦ `SailM X`, `catch_early_return` ↦ `SailME.run`, loops lean-sail's
`untilFuelM`).

**Deviations from Rocq.**
1. The proofs are NOT replays of the Rocq scripts bind by bind: each lemma is
   closed by `simp` over the `execEff`/`execREff` kit (the Lean-only tactics
   `eff8s_run` / `eff8s_mem`, the eff twins of `ExecSC.exec_run` /
   `ExecSC4.exec_mem`), following the Lean SC proofs (`ExecSC2/4/8`) of the
   same statements.  The statements are the Rocq ones.
2. Section `Let`s are inlined, as in `ExecSC8` (its deviation 2): Rocq's
   `pa := zero_extend' 64 (add_vec_int a (0 * 8))` is `a`; Rocq's `ea`, `a8`,
   `pa` of sections `VWgeff`/`ExecStoreGeff` are all `s.gpr rs1 + offset`
   (`offset := sign_extend' 64 imm` ↦ `sign_extend (m := 64) imm`); `vrs2` is
   `s.gpr rs2`.  Section hypotheses are theorem premises, in Rocq's order.
3. `exec_eff_translateAddr_identity_store`'s physical address is stated as in
   `ExecSC2.execTranslateAddrIdentityStore`
   (`zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))`).
4. `exec_eff_mem_write_ea` keeps Rocq's premise order; its `register_lookup
   cur_privilege` premise is `hcp`.  `exec_eff_mem_write_value_8` keeps Rocq's
   `m` and `register_lookup mstatus s.(sregs) = m`.
5. The access kind `AkInfo false false false` is the structure literal
   `⟨false, false, false⟩` (`akIfetch`, `akLatest`, `akSync`).
6. Rocq §7's `Print Assumptions` is not a declaration (no Lean twin).
7. The Rocq "pure" lemmas reused verbatim (`autocast_subrange_id`,
   `misaligned_order_1`) are the Lean simp facts `ExecSC8.extractStore8` /
   `misaligned_order` reduction.

**Rocq → Lean name map.**  `exec_eff_write_ram_plain_8` `execEffWriteRamPlain8`,
`exec_eff_pmaCheck_ram_store` `execEffPmaCheckRamStore`,
`exec_eff_effectivePrivilege_store` `execEffEffectivePrivilegeStore`,
`exec_eff_is_shadow_stack_store` `execEffIsShadowStackStore`,
`exec_eff_checked_mem_write_ram_store` `execEffCheckedMemWriteRamStore`,
`exec_eff_mem_write_ea` `execEffMemWriteEa`, `exec_eff_mem_write_value_8`
`execEffMemWriteValue8`, `exec_eff_translateAddr_identity_store`
`execEffTranslateAddrIdentityStore`, `exec_eff_vmem_write_addr_8`
`execEffVmemWriteAddr8`, `exec_eff_is_pmm_applicable_store`
`execEffIsPmmApplicableStore`, `exec_eff_get_pmlen_store`
`execEffGetPmlenStore`, `exec_eff_transform_effective_address_store`
`execEffTransformEffectiveAddressStore`, `exec_eff_vmem_write_8_gpr`
`execEffVmemWrite8Gpr`, `exec_eff_execute_STORE_8_gpr`
`execEffExecuteSTORE8Gpr`.  Section `Let`s (`pa`, `ea`, `a8`, `offset`, `vrs2`):
inlined (deviation 2).  Lean-only: the tactics `eff8s_run`, `eff8s_mem`.

**Dropped:** nothing (14 Rocq `Lemma`s; Lean 14 theorems + 2 tactics).
-/
import Weak.WeakLeafEffCommon
import Weak.ExecSC8

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- The `execEff` twin of `exec_run` (Lean-only): the base and early-return kits. -/
syntax "eff8s_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| eff8s_run) => `(tactic| eff8s_run [])
  | `(tactic| eff8s_run [$ls,*]) => `(tactic| simp (config := { decide := true }) only [execEffBindEq,
      readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff, effThen,
      execEffReturnm, ↓reduceIte, ite_true, ite_false, Bool.false_eq_true, assert, PreSail.assert,
      execREffBindEq, execREffLiftR, execREffReturnR, execREffThrow, decide_false, decide_true,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, List.nil_append,
      List.append_nil, $ls,*])

/-- The `execEff` twin of `exec_mem` (Lean-only): plus the split loop's closed
arithmetic. -/
syntax "eff8s_mem" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| eff8s_mem [$ls,*]) => `(tactic| eff8s_run [pmaOkAligned, execEffSplitMisalignedUnsplit,
      untilFuelM, untilFuelM.go, misaligned_order, bits_of_physaddr, Int.reduceToNat, Int.reduceMul,
      Int.reduceAdd, Int.reduceSub, Int.cast_ofNat_Int, Int.natCast_zero, Int.toNat_natCast,
      Int.zero_mul, addIntZero, $ls,*])

/-! ## 1. THE ONE MEMORY-TOUCHING STEP -/

/-- Rocq `exec_eff_write_ram_plain_8`: the only place in the 8-byte STORE where a
trace element is born. -/
theorem execEffWriteRamPlain8 (addr : BitVec 64) (data : BitVec 64) (s : ExecSt)
    (hdev : devAddr addr = false) :
    execEff (write_ram .Write_plain (.Physaddr addr) 8 data ()) s =
      some (true, s.setMem (bmWrite s.mem addr 8 data), [.WEwrite ⟨false, false, false⟩ addr 8 data]) := by
  have hm : mmioAcc addr 8 = false := by simp [mmioAcc, hdev]
  unfold write_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write PreSail.sail_mem_write
  eff8s_run [hm, Weff.cons]
  rfl

/-! ## 2. The register-only checks on the store path -/

/-- Rocq `exec_eff_pmaCheck_ram_store`. -/
theorem execEffPmaCheckRamStore (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true) :
    execEff (pmaCheck (.Physaddr addr) 8 (.Store .Data) pbmt false) s = some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hw (execEffIsMagApplicableStoreData 8 s) hal

/-- Rocq `exec_eff_effectivePrivilege_store`. -/
theorem execEffEffectivePrivilegeStore (m : BitVec 64) (s : ExecSt)
    (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    execEff (effectivePrivilege (.Store .Data) m .Machine) s = some (.Machine, s, []) := by
  unfold effectivePrivilege
  simp only [h, Bool.and_false, Bool.false_eq_true, ↓reduceIte, execEffReturnm]

/-- Rocq `exec_eff_is_shadow_stack_store`. -/
theorem execEffIsShadowStackStore (s : ExecSt) :
    execEff (is_shadow_stack_access (.Store .Data)) s = some (false, s, []) := rfl

/-! ## 3. `checked_mem_write` and `mem_write_value` -/

/-- Rocq `exec_eff_checked_mem_write_ram_store`: the PMP walk and the three
MMIO-window probes arrive as `execEff` premises. -/
theorem execEffCheckedMemWriteRamStore (pbmt : page_based_mem_type) (addr : BitVec 64)
    (region : PMA_Region) (data : BitVec 64) (s : ExecSt)
    (hpmpEff : execEff (pmpCheck (.Physaddr addr) 8 (.Store .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hc : execEff (within_clint (.Physaddr addr) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 8) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr addr) 8) s = some (false, s, []))
    (hdev : devAddr addr = false) :
    execEff (checked_mem_write (.Physaddr addr) 8 data (.Store .Data) pbmt .Machine () false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 8 data), [.WEwrite ⟨false, false, false⟩ addr 8 data]) := by
  have hpma := execEffPmaCheckRamStore addr pbmt region s hm hal hw
  have hmm : execEff (within_mmio_writable (.Physaddr addr) 8) s = some (false, s, []) := by
    unfold within_mmio_writable
    eff8s_run [hc, hsig, hh]
  have hw1 : ∀ (d : BitVec (8 * 8)), execEff (write_ram .Write_plain (.Physaddr addr) 8 d ()) s =
      some (true, s.setMem (bmWrite s.mem addr 8 d), [.WEwrite ⟨false, false, false⟩ addr 8 d]) :=
    fun d => execEffWriteRamPlain8 addr d s hdev
  unfold checked_mem_write check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  eff8s_mem [hpma]
  eff8s_mem [hpmpEff, hmm, write_kind_of_flags, hw1]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  congr <;> simp only [Sail.BitVec.extractLsb] <;> bv_decide

/-- Rocq `exec_eff_mem_write_ea`: the effective-address announcement, a state AND
trace no-op. -/
theorem execEffMemWriteEa (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (s : ExecSt)
    (hpmpEff : execEff (pmpCheck (.Physaddr addr) 8 (.Store .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    execEff (mem_write_ea (.Physaddr addr) 8 (.Store .Data) pbmt false false false) s =
      some (.Ok (), s, []) := by
  have hpma := execEffPmaCheckRamStore addr pbmt region s hm hal hw
  have hep : execEff (effectivePrivilege (.Store .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s, []) := by rw [hcp]; exact execEffEffectivePrivilegeStore _ s hmprv
  unfold mem_write_ea check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  eff8s_mem [hep, hpma]
  eff8s_mem [write_kind_of_flags, hpmpEff]

/-- Rocq `exec_eff_mem_write_value_8`. -/
theorem execEffMemWriteValue8 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 64) (m : BitVec 64) (s : ExecSt)
    (hpmpEff : execEff (pmpCheck (.Physaddr addr) 8 (.Store .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hc : execEff (within_clint (.Physaddr addr) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 8) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr addr) 8) s = some (false, s, []))
    (hdev : devAddr addr = false) (hms : s.regs .mstatus = m)
    (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    execEff (mem_write_value (.Physaddr addr) 8 data (.Store .Data) pbmt false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 8 data), [.WEwrite ⟨false, false, false⟩ addr 8 data]) := by
  have hep : execEff (effectivePrivilege (.Store .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s, []) := by rw [hcp, hms]; exact execEffEffectivePrivilegeStore _ s hmprv
  have h := execEffCheckedMemWriteRamStore pbmt addr region data s hpmpEff hm hal hw hc hsig hh hdev
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  eff8s_run [hep, h]

/-! ## 4. `translateAddr` at M-mode, and `vmem_write_addr` -/

/-- Rocq `exec_eff_translateAddr_identity_store` (deviation 3). -/
theorem execEffTranslateAddrIdentityStore (a : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    execEff (translateAddr (.Virtaddr a) (.Store .Data)) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s, []) := by
  unfold translateAddr
  rw [execEffCatchEarlyReturn]
  eff8s_run [hcp, execEffEffectivePrivilegeStore _ s hmprv, execEffTranslationModeM,
    execEffIsShadowStackStore]

set_option simprocs false in
/-- Rocq `exec_eff_vmem_write_addr_8` (section `SWeff`; deviation 2: Rocq's `pa`
is `a`): the one point where the write's trace crosses out of the loop. -/
theorem execEffVmemWriteAddr8 (a : BitVec 64) (data : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (halign : is_aligned_vaddr (.Virtaddr a) 8 = true)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmpEff : execEff (pmpCheck (.Physaddr a) 8 (.Store .Data) .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr a) 8 = some region)
    (hpalign : is_aligned_paddr (.Physaddr a) 8 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : execEff (within_clint (.Physaddr a) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr a) 8) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr a) 8) s = some (false, s, []))
    (hdev : devAddr a = false) :
    execEff (vmem_write_addr (.Virtaddr a) 8 data (.Store .Data) false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem a 8 data), [.WEwrite ⟨false, false, false⟩ a 8 data]) := by
  have hsp := splitOnPageBoundaryAlignedEq a 8 (by simp [vmemWidth]) halign
  have hsc' : (false == is_store_conditional (.Store .Data : MemoryAccessType mem_payload)) = true := rfl
  have htr := execEffTranslateAddrIdentityStore a s hpriv hmprv
  rw [translateIdentityEq] at htr
  have hep : execEff (effectivePrivilege (.Store .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s, []) := by rw [hpriv]; exact execEffEffectivePrivilegeStore _ s hmprv
  have hea := execEffMemWriteEa .PBMT_PMA a region s hpmpEff hmatch hpalign hwrite hpriv hmprv
  have hwv : ∀ d : BitVec 64, d = data →
      execEff (mem_write_value (.Physaddr a) 8 d (.Store .Data) .PBMT_PMA false false false) s =
        some (.Ok true, s.setMem (bmWrite s.mem a 8 data), [.WEwrite ⟨false, false, false⟩ a 8 data]) := by
    intro d hd
    rw [hd]
    exact execEffMemWriteValue8 .PBMT_PMA a region data _ s hpmpEff hmatch hpalign hwrite hc hsig hh hdev
      rfl hmprv hpriv
  unfold vmem_write_addr
  simp only [bits_of_virtaddr, hsp, pure_bind]
  rw [execEffCatchEarlyReturn]
  eff8s_run [halign, Functions.not, hep, execEffTranslationModeM, htr, hsc']
  dsimp only [iteNoSplitBare, Int.toNat_natCast]
  eff8s_run [hea]
  rw [hwv _ (extractFull8 data)]
  rfl

/-! ## 5. The address transform, and `vmem_write` over an arbitrary rs1 -/

/-- Rocq `exec_eff_is_pmm_applicable_store`. -/
theorem execEffIsPmmApplicableStore (s : ExecSt) :
    execEff (is_pmm_applicable (.Store .Data) .Machine) s = some (true, s, []) := rfl

/-- Rocq `exec_eff_get_pmlen_store`. -/
theorem execEffGetPmlenStore (s : ExecSt)
    (h : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    execEff (get_pmlen (.Store .Data) .Machine) s = some (0, s, []) := by
  unfold get_pmlen get_pmm
  eff8s_run [execEffIsPmmApplicableStore, h]

/-- Rocq `exec_eff_transform_effective_address_store`. -/
theorem execEffTransformEffectiveAddressStore (ea : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    execEff (transform_effective_address (.Virtaddr ea) (.Store .Data)) s =
      some (pm_transform_PA (.Virtaddr ea) 0, s, []) := by
  unfold transform_effective_address
  eff8s_run [hcp, execEffEffectivePrivilegeStore _ s hmprv, execEffGetPmlenStore s hpmm,
    execEffTranslationModeM]
  rfl

/-- Rocq `exec_eff_vmem_write_8_gpr` (section `VWgeff`; deviation 2: Rocq's `ea`,
`a8`, `pa` are `s.gpr rs1 + offset`). -/
theorem execEffVmemWrite8Gpr (rs1 : BitVec 5) (offset data : BitVec 64) (region : PMA_Region)
    (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + offset)) 8 = true)
    (hpmpEff : execEff (pmpCheck (.Physaddr (s.gpr rs1 + offset)) 8 (.Store .Data) .Machine) s =
      some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + offset)) 8 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + offset)) 8 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : execEff (within_clint (.Physaddr (s.gpr rs1 + offset)) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (s.gpr rs1 + offset)) 8) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr (s.gpr rs1 + offset)) 8) s = some (false, s, []))
    (hdev : devAddr (s.gpr rs1 + offset) = false) :
    execEff (vmem_write (.Regidx rs1) offset 8 data (.Store .Data) false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem (s.gpr rs1 + offset) 8 data),
        [.WEwrite ⟨false, false, false⟩ (s.gpr rs1 + offset) 8 data]) := by
  have hgta : execEff (get_transformed_data_addr (.Regidx rs1) offset (.Store .Data) 8) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s, []) := by
    unfold get_transformed_data_addr
    eff8s_run [execEffExtDataGetAddrGpr,
      execEffTransformEffectiveAddressStore _ s hcp hmprv hpmm, pmTransformPA0]
  unfold vmem_write
  rw [execEffCatchEarlyReturn]
  eff8s_run [hgta, execEffVmemWriteAddr8 _ data region s halign hcp hmprv hpmpEff hmatch hpalign hwrite
    hc hsig hh hdev]

/-! ## 6. THE DELIVERABLE: the 8-byte STORE's `execute`, at `execEff` -/

/-- Rocq `exec_eff_execute_STORE_8_gpr` (section `ExecStoreGeff`; deviation 2):
the trace is the ONE element born in §1. -/
theorem execEffExecuteSTORE8Gpr (rs2 rs1 : BitVec 5) (imm : BitVec 12) (region : PMA_Region)
    (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 = true)
    (hpmpEff : execEff (pmpCheck (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 (.Store .Data)
      .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions)
      (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : execEff (within_clint (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8) s =
      some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8) s =
      some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8) s =
      some (false, s, []))
    (hdev : devAddr (s.gpr rs1 + sign_extend (m := 64) imm) = false) :
    execEff (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8))) s =
      some (RETIRE_SUCCESS,
        s.setMem (bmWrite s.mem (s.gpr rs1 + sign_extend (m := 64) imm) 8 (s.gpr rs2)),
        [.WEwrite ⟨false, false, false⟩ (s.gpr rs1 + sign_extend (m := 64) imm) 8 (s.gpr rs2)]) := by
  show execEff (execute_STORE imm (.Regidx rs2) (.Regidx rs1) 8) s = _
  unfold execute_STORE
  eff8s_run [execEffRXBitsGpr, extractStore8, execEffVmemWrite8Gpr rs1 _ (s.gpr rs2) region s hcp hmprv
    hpmm halign hpmpEff hmatch hpalign hwrite hc hsig hh hdev]

end Weak
