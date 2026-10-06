/-
Weak: **M4 batch 1, the 8-byte M-mode LOAD at `execEff`** -- the `execEff` twin
of `ExecSC8.execExecuteLOAD8Gpr`, whose trace is exactly ONE element, the data
read `[.WEread ⟨false, false, false⟩ pa 8]` (`read_ram .Read_plain` issues the
explicit plain-normal access kind, whose `classify` is `AkInfo false false false`).

Rocq: `iris/WeakLeafEff8.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakEffSkel` reduced a weak-memory leaf's
remaining obligation to two `execEff` facts (the fetch's and the `execute`'s);
this file is the `execute` one for the LOAD-8 shape.  Every step of the chain
below `read_ram` (`effectivePrivilege`, `split_misaligned`, `pmaCheck`, the
`within_*` probes, `translateAddr`, the one-turn loop, `transform_effective_address`,
`get_pmlen`, `ext_data_get_addr`, `wX_bits`) is REGISTER-ONLY, so each of its
`execEff` facts carries the EMPTY trace; the empty trace is established by replaying
the SC scripts at `execEff` (not by `WeakEff.execEffQuietOfEmpty`, which can only
conclude `quietTrace` -- a zero-width access is invisible to `exec` -- while the
certificates need `nowriteTrace`).  Two premises are taken as hypotheses, in their
`execEff` form with the empty trace: the M-mode `pmpCheck` reduction and the three
`within_*` probes.  Nothing reduces a model function by computation beyond the
closed guards, as in the SC originals.

Conventions: as `Weak/ExecSC*.lean` and `Weak/WeakLeafEffCommon.lean` (GPRs
`s.gpr i` / `s.setGpr i v`; `register_lookup r s.(sregs)` ↦ `s.regs r`;
`eq_vec x 'b"1"` ↦ `x == 1#1`; `dev_addr pa = false` ↦ `devAddr pa = false`; the
byte window ↦ `BytesAt s pa 8 w`; `M X` ↦ `SailM X`; `catch_early_return` ↦
`SailME.run`).

**Deviations from Rocq.**
1. Rocq's `pa := zero_extend' 64 (add_vec_int a (0 * 8))`, `a8 := zero_extend' 64
   (subrange_vec_dec ea 63 0)` are the address itself (`ExecSC8` deviation 2): in
   `execEffVmemReadAddr8` the physical address is `a`, in `execEffVmemRead8Gpr` /
   `execEffExecuteLOAD8Gpr` it is the effective address `s.gpr rs1 + offset` (resp.
   `s.gpr rs1 + sign_extend imm`); Rocq's `data2` (the full-width update of the zero
   accumulator) is the read value `v`.  The `Section` hypotheses are theorem
   premises (same list, same `execEff` forms).
2. `exec_eff_execute_LOAD_8_gpr`: the result state is `s.setGpr rd (extend_value
   false v)` (equal to Rocq's plain `set_reg` under the kept premise `rd.toNat ≠ 0`,
   the ExecSC convention).
3. Rocq's `within_mmio_readable` fact (an inline `assert` of
   `exec_eff_checked_mem_read_ram_load`) is the Lean-only lemma
   `execEffWithinMmioReadableFalse`; the generic aligned no-split arm of
   `vmem_read_addr` is the Lean-only `execEffVmemReadAddrAligned8` (the `execEff`
   twin of `ExecSC8.execVmemReadAddrAligned8`, needed because the Lean model uses
   the access width in TYPES); the effective address of `get_transformed_data_addr`
   (Rocq's inline `Hgta`) is the Lean-only `execEffGetTransformedDataAddrLoad`.
4. The scripts normalise with the Lean-only tactics `exec_eff_run` / `exec_eff_mem`
   (the `execEff`/`execREff` twins of `exec_run` / `exec_mem`) instead of replaying
   each bind lemma.
5. `exec_eff_mem_read_load`'s `m` and `register_lookup mstatus s.(sregs) = m` are
   kept (`s.regs .mstatus = m`).
6. Rocq's `Print Assumptions` is not a declaration.

**Rocq → Lean name map.**  `exec_eff_effectivePrivilege_load`
`execEffEffectivePrivilegeLoad`, `exec_eff_is_shadow_stack_load`
`execEffIsShadowStackLoad`, `exec_eff_read_ram_plain_8` `execEffReadRamPlain8`,
`exec_eff_pmaCheck_ram_load` `execEffPmaCheckRamLoad`,
`exec_eff_checked_mem_read_ram_load` `execEffCheckedMemReadRamLoad`,
`exec_eff_mem_read_load` `execEffMemReadLoad`, `exec_eff_translateAddr_identity_load`
`execEffTranslateAddrIdentityLoad`, `exec_eff_vmem_read_addr_8`
`execEffVmemReadAddr8`, `exec_eff_is_pmm_applicable_load`
`execEffIsPmmApplicableLoad`, `exec_eff_get_pmlen_load` `execEffGetPmlenLoad`,
`exec_eff_transform_effective_address_load` `execEffTransformEffectiveAddressLoad`,
`exec_eff_vmem_read_8_gpr` `execEffVmemRead8Gpr`, `exec_eff_execute_LOAD_8_gpr`
`execEffExecuteLOAD8Gpr`.  Lean-only: the tactics `exec_eff_run`, `exec_eff_mem`,
`execEffWithinMmioReadableFalse`, `execEffVmemReadAddrAligned8`,
`execEffGetTransformedDataAddrLoad`.

**Dropped:** nothing (13 Rocq `Lemma`s; 13 Lean theorems plus the Lean-only items).
-/
import Weak.WeakLeafEffCommon
import Weak.ExecSC8

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- `exec_eff_steps` plus the early-return kit and the closed-guard reductions (the
`execEff` twin of `exec_run`; Lean-only). -/
syntax "exec_eff_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| exec_eff_run) => `(tactic| exec_eff_run [List.nil_append])
  | `(tactic| exec_eff_run [$ls,*]) => `(tactic| simp (config := { decide := true }) only
      [execEffBindEq, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff,
      effThen, Weff.cons, execEffReturnm, ↓reduceIte, ite_true, ite_false, Bool.false_eq_true, assert,
      PreSail.assert, execREffBindEq, execREffLiftR, execREffReturnR, execREffThrow, decide_false,
      decide_true, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, List.nil_append,
      List.append_nil, List.cons_append, $ls,*])

/-- The physical-access normaliser at `execEff` (the twin of `exec_mem`; Lean-only). -/
syntax "exec_eff_mem" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| exec_eff_mem [$ls,*]) => `(tactic| exec_eff_run [pmaOkAligned,
      execEffSplitMisalignedUnsplit, untilFuelM, untilFuelM.go, misaligned_order, bits_of_physaddr,
      Int.reduceToNat, Int.reduceMul, Int.reduceAdd, Int.reduceSub, Int.cast_ofNat_Int,
      Int.natCast_zero, Int.toNat_natCast, Int.zero_mul, addIntZero, $ls,*])

/-! ## 1. The register-only leaves of the LOAD chain -/

/-- Rocq `exec_eff_effectivePrivilege_load`. -/
theorem execEffEffectivePrivilegeLoad (m : BitVec 64) (s : ExecSt)
    (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    execEff (effectivePrivilege (.Load .Data) m .Machine) s = some (.Machine, s, []) := by
  unfold effectivePrivilege
  simp only [h, Bool.and_false, Bool.false_eq_true, ↓reduceIte, execEffReturnm]

/-- Rocq `exec_eff_is_shadow_stack_load`. -/
theorem execEffIsShadowStackLoad (s : ExecSt) :
    execEff (is_shadow_stack_access (.Load .Data)) s = some (false, s, []) := rfl

/-! ## 2. THE ONE MEMORY-TOUCHING STEP: `read_ram`, where the trace is born -/

/-- Rocq `exec_eff_read_ram_plain_8`. -/
theorem execEffReadRamPlain8 (addr w : BitVec 64) (s : ExecSt) (hdev : devAddr addr = false)
    (hb : BytesAt s addr 8 w) :
    execEff (read_ram .Read_plain (.Physaddr addr) 8 false) s =
      some ((w, default_meta), s, [.WEread ⟨false, false, false⟩ addr 8]) := by
  have hr : bmRead s.mem addr 8 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  exec_eff_run [hm, hr]
  rfl

/-! ## 3. Up through `mem_read`: the trace's one element rides the binds -/

/-- Rocq `exec_eff_pmaCheck_ram_load`. -/
theorem execEffPmaCheckRamLoad (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true) :
    execEff (pmaCheck (.Physaddr addr) 8 (.Load .Data) pbmt false) s = some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hr (execEffIsMagApplicableLoadData 8 s) hal

/-- Rocq's inline `Hmmio` (deviation 3): the three device-window probes make the
access a RAM access. -/
theorem execEffWithinMmioReadableFalse (addr : BitVec 64) (n : Nat) (s : ExecSt)
    (hc : execEff (within_clint (.Physaddr addr) n) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) n) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) n) s = some (false, s, [])) :
    execEff (within_mmio_readable (.Physaddr addr) n) s = some (false, s, []) := by
  unfold within_mmio_readable
  exec_eff_run [hc, hsig, hh]

/-- Rocq `exec_eff_checked_mem_read_ram_load`. -/
theorem execEffCheckedMemReadRamLoad (pbmt : page_based_mem_type) (addr : BitVec 64)
    (region : PMA_Region) (w : BitVec 64) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 8 (.Load .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true)
    (hc : execEff (within_clint (.Physaddr addr) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 8) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 8) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 8 w) :
    execEff (checked_mem_read (.Load .Data) pbmt .Machine (.Physaddr addr) 8 false false false false) s =
      some (.Ok (w, default_meta), s, [.WEread ⟨false, false, false⟩ addr 8]) := by
  have hpma := execEffPmaCheckRamLoad addr pbmt region s hm hal hr
  have hmm := execEffWithinMmioReadableFalse addr 8 s hc hsig hh
  have hrr := execEffReadRamPlain8 addr w s hdev hb
  unfold checked_mem_read check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  exec_eff_mem [hpma]
  exec_eff_mem [hpmp, hmm, hrr, read_kind_of_flags]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  congr
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  bv_decide

/-- Rocq `exec_eff_mem_read_load` (deviation 5). -/
theorem execEffMemReadLoad (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w m : BitVec 64) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 8 (.Load .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true)
    (hc : execEff (within_clint (.Physaddr addr) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 8) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 8) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 8 w) (hms : s.regs .mstatus = m)
    (hmprv : (_get_Mstatus_MPRV m == 1#1) = false) (hpriv : s.regs .cur_privilege = .Machine) :
    execEff (mem_read (.Load .Data) pbmt (.Physaddr addr) 8 false false false) s =
      some (.Ok w, s, [.WEread ⟨false, false, false⟩ addr 8]) := by
  have hck := execEffCheckedMemReadRamLoad pbmt addr region w s hpmp hm hal hr hc hsig hh hdev hb
  unfold mem_read mem_read_priv mem_read_priv_meta
  exec_eff_run [hms, hpriv, execEffEffectivePrivilegeLoad m s hmprv, hck]
  rfl

/-! ## 4. `translateAddr` (Bare, M-mode) and `vmem_read_addr`'s page split -/

/-- Rocq `exec_eff_translateAddr_identity_load`. -/
theorem execEffTranslateAddrIdentityLoad (a : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    execEff (translateAddr (.Virtaddr a) (.Load .Data)) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s, []) := by
  unfold translateAddr
  rw [execEffCatchEarlyReturn]
  exec_eff_run [hcp, execEffEffectivePrivilegeLoad _ s hmprv, execEffTranslationModeM,
    execEffIsShadowStackLoad]

set_option simprocs false in
/-- The `execEff` twin of `ExecSC8.execVmemReadAddrAligned8` (deviation 3): an
aligned 8-byte in-page read is one translation and one physical read, whose trace
is the whole trace. -/
theorem execEffVmemReadAddrAligned8 (va pa : BitVec 64) (acc : MemoryAccessType mem_payload)
    (aq rl : Bool) (p : Privilege) (mode : SATPMode) (pbmt : page_based_mem_type) (w : BitVec 64)
    (s s1 : ExecSt) (es : List Weff) (hal : is_aligned_vaddr (.Virtaddr va) 8 = true)
    (hep : execEff (effectivePrivilege acc (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (p, s, []))
    (hmode : execEff (translationMode p) s = some (mode, s, []))
    (htr : execEff (translateAddr (.Virtaddr va) acc) s = some (.Ok (.Physaddr pa, pbmt, ()), s1, []))
    (hmr : execEff (mem_read acc pbmt (.Physaddr pa) 8 aq rl false) s1 = some (.Ok w, s1, es)) :
    execEff (vmem_read_addr (.Virtaddr va) 8 acc aq rl false) s = some (.Ok w, s1, es) := by
  have hsp := splitOnPageBoundaryAlignedEq va 8 (by simp [vmemWidth]) hal
  cases mode <;>
  · unfold vmem_read_addr translate_and_read_value
    simp only [bits_of_virtaddr, hsp, pure_bind]
    rw [execEffCatchEarlyReturn]
    exec_eff_run [hal, Functions.not, hep, hmode, htr]
    dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57,
      Int.toNat_natCast]
    exec_eff_run [hmr]
    exact congrArg (fun x => some (Result.Ok x, s1, es)) (uszFull8 w)

/-- Rocq `exec_eff_vmem_read_addr_8` (section `SEff`; deviation 1: `pa` is `a`). -/
theorem execEffVmemReadAddr8 (a v : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (halign : is_aligned_vaddr (.Virtaddr a) 8 = true)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmp : execEff (pmpCheck (.Physaddr a) 8 (.Load .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr a) 8 = some region)
    (hpalign : is_aligned_paddr (.Physaddr a) 8 = true)
    (hr : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : execEff (within_clint (.Physaddr a) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr a) 8) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr a) 8) s = some (false, s, []))
    (hdev : devAddr a = false) (hb : BytesAt s a 8 v) :
    execEff (vmem_read_addr (.Virtaddr a) 8 (.Load .Data) false false false) s =
      some (.Ok v, s, [.WEread ⟨false, false, false⟩ a 8]) := by
  have htr := execEffTranslateAddrIdentityLoad a s hpriv hmprv
  rw [translateIdentityEq] at htr
  have hep : execEff (effectivePrivilege (.Load .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s, []) := by rw [hpriv]; exact execEffEffectivePrivilegeLoad _ s hmprv
  exact execEffVmemReadAddrAligned8 a a _ false false .Machine .Bare .PBMT_PMA v s s _ halign hep
    (execEffTranslationModeM s) htr
    (execEffMemReadLoad .PBMT_PMA a region v _ s hpmp hm hpalign hr hc hsig hh hdev hb rfl hmprv hpriv)

/-! ## 5. The address-formation leaves -/

/-- Rocq `exec_eff_is_pmm_applicable_load`. -/
theorem execEffIsPmmApplicableLoad (s : ExecSt) :
    execEff (is_pmm_applicable (.Load .Data) .Machine) s = some (true, s, []) := rfl

/-- Rocq `exec_eff_get_pmlen_load`. -/
theorem execEffGetPmlenLoad (s : ExecSt)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    execEff (get_pmlen (.Load .Data) .Machine) s = some (0, s, []) := by
  unfold get_pmlen get_pmm
  exec_eff_run [execEffIsPmmApplicableLoad, hpmm]

/-- Rocq `exec_eff_transform_effective_address_load`. -/
theorem execEffTransformEffectiveAddressLoad (ea : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    execEff (transform_effective_address (.Virtaddr ea) (.Load .Data)) s =
      some (pm_transform_PA (.Virtaddr ea) 0, s, []) := by
  unfold transform_effective_address
  exec_eff_run [hcp, execEffEffectivePrivilegeLoad _ s hmprv, execEffGetPmlenLoad s hpmm,
    execEffTranslationModeM]
  rfl

/-! ## 6. THE DELIVERABLE: `vmem_read` and the LOAD-8 `execute`, at `execEff` -/

/-- Rocq's inline `Hgta` of `exec_eff_vmem_read_8_gpr` (deviation 3). -/
theorem execEffGetTransformedDataAddrLoad (rs1 : BitVec 5) (offset : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    execEff (get_transformed_data_addr (.Regidx rs1) offset (.Load .Data) 8) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s, []) := by
  unfold get_transformed_data_addr
  exec_eff_run [execEffExtDataGetAddrGpr, execEffTransformEffectiveAddressLoad _ s hcp hmprv hpmm,
    pmTransformPA0]

/-- Rocq `exec_eff_vmem_read_8_gpr` (section `VRgEff`; deviation 1). -/
theorem execEffVmemRead8Gpr (rs1 : BitVec 5) (offset v : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + offset)) 8 = true)
    (hpmp : execEff (pmpCheck (.Physaddr (s.gpr rs1 + offset)) 8 (.Load .Data) .Machine) s =
      some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + offset)) 8 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + offset)) 8 = true)
    (hr : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : execEff (within_clint (.Physaddr (s.gpr rs1 + offset)) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (s.gpr rs1 + offset)) 8) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr (s.gpr rs1 + offset)) 8) s = some (false, s, []))
    (hdev : devAddr (s.gpr rs1 + offset) = false) (hb : BytesAt s (s.gpr rs1 + offset) 8 v) :
    execEff (vmem_read (.Regidx rs1) offset 8 (.Load .Data) false false false) s =
      some (.Ok v, s, [.WEread ⟨false, false, false⟩ (s.gpr rs1 + offset) 8]) := by
  unfold vmem_read
  rw [execEffCatchEarlyReturn]
  exec_eff_run [execEffGetTransformedDataAddrLoad rs1 offset s hcp hmprv hpmm,
    execEffVmemReadAddr8 _ v region s halign hcp hmprv hpmp hm hpalign hr hc hsig hh hdev hb]

/-- Rocq `exec_eff_execute_LOAD_8_gpr` (section `ExecLoadGEff`; deviations 1, 2). -/
theorem execEffExecuteLOAD8Gpr (rs1 rd : BitVec 5) (imm : BitVec 12) (v : BitVec 64) (region : PMA_Region)
    (s : ExecSt) (_hrd : rd.toNat ≠ 0)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 = true)
    (hpmp : execEff (pmpCheck (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 (.Load .Data)
      .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 =
      some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 = true)
    (hr : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : execEff (within_clint (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8) s =
      some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8) s =
      some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8) s =
      some (false, s, []))
    (hdev : devAddr (s.gpr rs1 + sign_extend (m := 64) imm) = false)
    (hb : BytesAt s (s.gpr rs1 + sign_extend (m := 64) imm) 8 v) :
    execEff (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (extend_value false v),
        [.WEread ⟨false, false, false⟩ (s.gpr rs1 + sign_extend (m := 64) imm) 8]) := by
  show execEff (execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 8) s = _
  unfold execute_LOAD
  exec_eff_run [execEffVmemRead8Gpr rs1 _ v region s hcp hmprv hpmm halign hpmp hm hpalign hr hc hsig hh
    hdev hb, execEffWXBitsGpr]

end Weak
