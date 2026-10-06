/-
Weak: **`amoswap.w.aq` at width 4, M-mode** (M4 batch 1) -- the SC lemma AND
its `execEff` mirror.  This is THE LOCK INSTRUCTION: xv6's `acquire()` spells
its test-and-set as `amoswap.w.aq`, i.e.
`AMO (AMOSWAP, aq := true, rl := false, rs2, rs1, width := 4, rd)`.

Rocq: `iris/WeakLeafAmo4.v` @ xxvzwolszwmp.

The Rocq header, in substance.
* HALF A (§§1-3) is a NEW SC LEMMA, `execExecuteAMOSWAP4Gpr`: the M-mode
  clone of the S-mode AMO chain (`Weak/ExecSC10.lean`), translation the
  identity (`Bare`), the PMP grant from the all-`OFF` entries.  The
  privilege-independent leaves (`execPmaCheckRamAmo4`, `execReadRamResacq4`,
  `execWriteRamCond4`, `execIsShadowStackAmo`) are reused; `mem_write_ea`
  resolves the effective privilege and runs the full PMA/PMP check, so it
  gets an M-mode clone.
* HALF B (§§4-8) is the `execEff` mirror, `execEffExecuteAMOSWAP4Gpr`, whose
  trace is exactly TWO ADJACENT elements -- the read then the write.
* THE TWO ACCESS KINDS, read off the model.  `execute_AMO` issues its read as
  `mem_read access pbmt addr width aq (aq && rl) true` and its write as
  `mem_write_value … (aq && rl) rl true`; at `aq = true`, `rl = false` the
  read kind is `Read_RISCV_reserved_acquire`, i.e.
  `AK_explicit {AV_exclusive, AS_rel_or_acq}`, classified
  `⟨false, true, true⟩` (not an ifetch, latest, SYNCHRONISING: what
  `WeakEff.wcertAmoAqGen` demands of the read); the write kind is
  `Write_RISCV_conditional`, `AK_explicit {AV_exclusive, AS_normal}`,
  classified `⟨false, true, false⟩`.
* WHY THE REGISTER-ONLY PREFIX IS MIRRORED, NOT DETECTED: every step outside
  the two memory operations is register-only, so each `execEff` fact carries
  the EMPTY trace; `WeakEff.execEffQuietOfEmpty` would only give a quiet trace
  (which admits a zero-width write), while `wcertAmoAqGen` needs `nowriteTrace`
  of the surroundings.  So the honest premise is the empty trace, by replay.
* HYPOTHESES: in the SC half the PMP grant is the M-mode all-`OFF` premise;
  in the `execEff` half it is the abstract
  `execEff (pmpCheck (.Physaddr pa) 4 acc .Machine) s = some (none, s, [])`
  (dischargeable by `WeakPmpEff.execEffPmpCheckMachineNone`), and the four
  MMIO-window probes are taken in their `execEff` form with the empty trace.

**Deviations from Rocq.**
1. Conventions as `Weak/ExecSC*.lean` and `Weak/WeakLeafEffCommon.lean`
   (`register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1" = b` ↦
   `(x == 1#1) = b`; GPRs `s.gpr i` / `s.setGpr i v` -- Rocq's `set_reg … rd`
   under `uint rd ≠ 0` is `setGpr rd`, the premise kept; `dev_addr pa = false`
   ↦ `devAddr pa = false`; the byte window ↦ `BytesAt s pa 4 w`;
   `MState s.(sregs) (write_bytes s.(mem) pa 4 v) s.(mdev)` ↦
   `s.setMem (bmWrite s.mem pa 4 v)`; `AkInfo false true true` ↦
   `⟨false, true, true⟩`; `Defs.monadR R exception X` ↦ `SailME R X`).
2. The sections `ExecAmoM4` / `ExecAmoM4Eff`: hypotheses are premises; the
   `Let`s are the Lean-only defs `amoM4Ea` (`s.gpr rs1 + zeros`), `amoM4A8`
   (the address `pm_transform_PA` returns, Rocq
   `zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0)`), `amoM4Pa`
   (`zero_extend (m := 64) a8`) and `amoM4Store` (Rocq `storeval`,
   `sign_extend (m := 32) (trunc (m := 32) (s.gpr rs2))`); Rocq's
   `vrs2` is `s.gpr rs2` (inlined).  The loaded value written to `rd` is
   `sign_extend (m := 64) w` (Rocq's `autocast`).
3. The SC memory operations are instances of `ExecSC4`'s generic one-piece
   lemmas (`execCheckedMemReadRam`, `execCheckedMemWriteRam`,
   `execMemWriteEaRam`, `execMemWriteValueRam`), as `ExecSC10` does for S-mode;
   the `within_mmio_*` facts come from `ExecSC4.execWithinMmio*False`.
4. The Lean model's `execute_AMO` has no `and_boolM`: the CAS guard is an
   inline `if op == AMOCAS then … else pure false`, reduced by the peel.
5. `exec_eff_write_ram_cond_4` is the width-4 instance of the Lean-only
   `execEffWriteRamCond` (any width); the `execEff` memory lemmas are proved
   by a `simp` peel (the local tactic `amo_eff_mem`) rather than one rewrite
   per bind; the MMIO windows by the Lean-only `WeakLeafAmo4.execEffWithinMmioReadableFalse`
   / `WeakLeafAmo4.execEffWithinMmioWritableFalse` (Rocq inlines them as `Hmmio`).
6. `exec_eff_amo_writeback` is stated on the Lean shape of the tail,
   `liftM (wX_bits (.Regidx rd) v) >>= fun _ => pure RETIRE_SUCCESS`.
7. Rocq §9's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_effectivePrivilege_amo_M`
`execEffectivePrivilegeAmoM`, `exec_translateAddr_identity_amo_M`
`execTranslateAddrIdentityAmoM`, `exec_is_pmm_applicable_amo_M`
`execIsPmmApplicableAmoM`, `exec_get_pmlen_amo_M` `execGetPmlenAmoM`,
`exec_transform_effective_address_amo_M` `execTransformEffectiveAddressAmoM`,
`exec_checked_mem_read_ram_amo_4_M` `execCheckedMemReadRamAmo4M`,
`exec_mem_read_amo_4_M` `execMemReadAmo4M`, `exec_mem_write_ea_amo_4_M`
`execMemWriteEaAmo4M`, `exec_checked_mem_write_ram_amo_4_M`
`execCheckedMemWriteRamAmo4M`, `exec_mem_write_value_amo_4_M`
`execMemWriteValueAmo4M`, `exec_execute_AMOSWAP_4_gpr`
`execExecuteAMOSWAP4Gpr`, `exec_eff_read_ram_resacq_4` `execEffReadRamResacq4`,
`exec_eff_write_ram_cond_4` `execEffWriteRamCond4`,
`exec_eff_effectivePrivilege_amo_M` `execEffEffectivePrivilegeAmoM`,
`exec_eff_is_shadow_stack_amo` `execEffIsShadowStackAmo`,
`exec_eff_translateAddr_identity_amo_M` `execEffTranslateAddrIdentityAmoM`,
`exec_eff_is_pmm_applicable_amo_M` `execEffIsPmmApplicableAmoM`,
`exec_eff_get_pmlen_amo_M` `execEffGetPmlenAmoM`,
`exec_eff_transform_effective_address_amo_M`
`execEffTransformEffectiveAddressAmoM`, `exec_eff_pmaCheck_ram_amo_4`
`execEffPmaCheckRamAmo4`, `exec_eff_mem_write_ea_amo_4_M`
`execEffMemWriteEaAmo4M`, `exec_eff_checked_mem_read_ram_amo_4_M`
`execEffCheckedMemReadRamAmo4M`, `exec_eff_mem_read_amo_4_M`
`execEffMemReadAmo4M`, `exec_eff_checked_mem_write_ram_amo_4_M`
`execEffCheckedMemWriteRamAmo4M`, `exec_eff_mem_write_value_amo_4_M`
`execEffMemWriteValueAmo4M`, `exec_eff_amo_writeback` `execEffAmoWriteback`,
`exec_eff_execute_AMOSWAP_4_gpr` `execEffExecuteAMOSWAP4Gpr`.  Section `Let`s:
`ea` `amoM4Ea`, `a8` `amoM4A8`, `pa` `amoM4Pa`, `storeval` `amoM4Store`.
Lean-only: the tactic `amo_eff_mem`, `execEffWriteRamCond`,
`WeakLeafAmo4.execEffWithinMmioReadableFalse`, `WeakLeafAmo4.execEffWithinMmioWritableFalse`.

**Dropped:** nothing (27 Rocq `Lemma`s + 4 `Let`s; Lean 27 theorems + 4 defs,
plus the Lean-only items above).
-/
import Weak.WeakLeafEffCommon
import Weak.WeakPmpEff
import Weak.ExecSC4
import Weak.ExecSC5

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## HALF A -- THE SC LEMMA -/

/-! ### 1. The M-mode privilege leaves of the AMO chain -/

/-- Rocq `exec_effectivePrivilege_amo_M`. -/
theorem execEffectivePrivilegeAmoM (m : BitVec 64) (s : ExecSt)
    (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    exec (effectivePrivilege (.Atomic (.AMOSWAP, true, false, .Data, .Data)) m .Machine) s =
      some (.Machine, s) :=
  execEffectivePrivilegeMprv0 _ m _ s h

/-- Rocq `exec_translateAddr_identity_amo_M`. -/
theorem execTranslateAddrIdentityAmoM (a : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    exec (translateAddr (.Virtaddr a) (.Atomic (.AMOSWAP, true, false, .Data, .Data))) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s) :=
  execTranslateAddrIdentityAcc a _ s hcp hmprv (execIsShadowStackAmo true false s)

/-- Rocq `exec_is_pmm_applicable_amo_M`. -/
theorem execIsPmmApplicableAmoM (s : ExecSt) :
    exec (is_pmm_applicable (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (true, s) := rfl

/-- Rocq `exec_get_pmlen_amo_M`. -/
theorem execGetPmlenAmoM (s : ExecSt)
    (h : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    exec (get_pmlen (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s = some (0, s) := by
  unfold get_pmlen get_pmm
  exec_run [execIsPmmApplicableAmoM, h]

/-- Rocq `exec_transform_effective_address_amo_M`. -/
theorem execTransformEffectiveAddressAmoM (ea : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    exec (transform_effective_address (.Virtaddr ea) (.Atomic (.AMOSWAP, true, false, .Data, .Data))) s =
      some (pm_transform_PA (.Virtaddr ea) 0, s) := by
  unfold transform_effective_address
  exec_run [hcp, execEffectivePrivilegeAmoM _ s hmprv, execGetPmlenAmoM s hpmm, execTranslationModeM]
  rfl

/-! ### 2. The M-mode memory operations of the AMO (deviation 3) -/

/-- Rocq `exec_checked_mem_read_ram_amo_4_M`. -/
theorem execCheckedMemReadRamAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt)
    (hpmp : exec (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    exec (checked_mem_read (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt .Machine (.Physaddr addr) 4
      true false true false) s = some (.Ok (w, default_meta), s) :=
  execCheckedMemReadRam _ pbmt _ addr 4 true false true .Read_RISCV_reserved_acquire w s (by simp [vmemWidth])
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨true, false, rfl, rfl, rfl, rfl, rfl⟩))))
    (execPmaCheckRamAmo4 addr pbmt region true false s hm hal hrd hwr ha) hpmp
    (execWithinMmioReadableFalse addr 4 s hc hsig hh)
    (execReadRam _ addr 4 w s (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hdev hb)

/-- Rocq `exec_mem_read_amo_4_M`. -/
theorem execMemReadAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (m : BitVec 64) (s : ExecSt)
    (hpmp : exec (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w)
    (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    exec (mem_read (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt (.Physaddr addr) 4 true false true) s =
      some (.Ok w, s) := by
  have hck := execCheckedMemReadRamAmo4M pbmt addr region w s hpmp hm hal hrd hwr ha hc hsig hh hdev hb
  unfold mem_read
  exec_run [hcp, hms, execEffectivePrivilegeAmoM m s hmprv,
    execMemReadPriv _ _ _ _ _ _ _ _ w s (by decide) hck]
  simp only [Nat.reduceMul, BitVec.setWidth_eq]

/-- Rocq `exec_mem_write_ea_amo_4_M`. -/
theorem execMemWriteEaAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (m : BitVec 64) (s : ExecSt)
    (hpmp : exec (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    exec (mem_write_ea (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt false false true) s =
      some (.Ok (), s) :=
  execMemWriteEaRam _ pbmt .Machine addr 4 false false true s (by simp [vmemWidth]) ⟨_, rfl⟩
    (by rw [hcp, hms]; exact execEffectivePrivilegeAmoM _ s hmprv)
    (execPmaCheckRamAmo4 addr pbmt region true false s hm hal hrd hwr ha) hpmp

/-- Rocq `exec_checked_mem_write_ram_amo_4_M`. -/
theorem execCheckedMemWriteRamAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 32) (s : ExecSt)
    (hpmp : exec (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) :
    exec (checked_mem_write (.Physaddr addr) 4 data (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt
      .Machine () false false true) s = some (.Ok true, s.setMem (bmWrite s.mem addr 4 data)) :=
  execCheckedMemWriteRam _ pbmt _ addr 4 data false false true .Write_RISCV_conditional s (by simp [vmemWidth])
    (Or.inr ⟨rfl, rfl, rfl, rfl⟩) (execPmaCheckRamAmo4 addr pbmt region true false s hm hal hrd hwr ha) hpmp
    (execWithinMmioWritableFalse addr 4 s hc hsig hh) hdev

/-- Rocq `exec_mem_write_value_amo_4_M`. -/
theorem execMemWriteValueAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 32) (m : BitVec 64) (s : ExecSt)
    (hpmp : exec (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false)
    (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    exec (mem_write_value (.Physaddr addr) 4 data (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt
      false false true) s = some (.Ok true, s.setMem (bmWrite s.mem addr 4 data)) :=
  execMemWriteValueRam _ pbmt .Machine addr 4 data false false true s
    (by rw [hcp, hms]; exact execEffectivePrivilegeAmoM _ s hmprv)
    (execCheckedMemWriteRamAmo4M pbmt addr region data s hpmp hm hal hrd hwr ha hc hsig hh hdev)

/-! ### 3. THE SC DELIVERABLE: `amoswap.w.aq` at M-mode, width 4 (deviation 2) -/

/-- Rocq section `Let ea`: the base, from `rs1` (offset zero). -/
def amoM4Ea (rs1 : BitVec 5) (s : ExecSt) : BitVec 64 := s.gpr rs1 + zeros (n := 64)

/-- Rocq section `Let a8`: the (pointer-masking-free) virtual address. -/
def amoM4A8 (rs1 : BitVec 5) (s : ExecSt) : BitVec 64 :=
  bits_of_virtaddr (pm_transform_PA (.Virtaddr (amoM4Ea rs1 s)) 0)

/-- Rocq section `Let pa`: the physical address (the identity translation). -/
def amoM4Pa (rs1 : BitVec 5) (s : ExecSt) : BitVec 64 := zero_extend (m := 64) (amoM4A8 rs1 s)

/-- Rocq section `Let storeval`: the truncated, re-sign-extended `rs2`. -/
def amoM4Store (rs2 : BitVec 5) (s : ExecSt) : BitVec 32 :=
  sign_extend (m := 32) (trunc (m := 32) (s.gpr rs2))

set_option simprocs false in
/-- **THE SC DELIVERABLE.**  Rocq `exec_execute_AMOSWAP_4_gpr`. -/
theorem execExecuteAMOSWAP4Gpr (rs2 rs1 rd : BitVec 5) (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (_hrd : rd.toNat ≠ 0)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (amoM4A8 rs1 s)) 4 = true)
    (hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr (amoM4Pa rs1 s)) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (amoM4Pa rs1 s)) 4 = true)
    (hrd : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hwr : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes .PBMT_PMA).atomic_support .AMOSWAP 4 = true)
    (hc : exec (within_clint (.Physaddr (amoM4Pa rs1 s)) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr (amoM4Pa rs1 s)) 4) s = some (false, s))
    (hhr : exec (within_htif_readable (.Physaddr (amoM4Pa rs1 s)) 4) s = some (false, s))
    (hhw : exec (within_htif_writable (.Physaddr (amoM4Pa rs1 s)) 4) s = some (false, s))
    (hdev : devAddr (amoM4Pa rs1 s) = false)
    (hb : BytesAt s (amoM4Pa rs1 s) 4 w) :
    exec (execute (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd))) s =
      some (RETIRE_SUCCESS, (s.setMem (bmWrite s.mem (amoM4Pa rs1 s) 4 (amoM4Store rs2 s))).setGpr rd
        (sign_extend (m := 64) w)) := by
  have hpmpc := execPmpCheckMachineNone (.Physaddr (amoM4Pa rs1 s)) 4
    (.Atomic (.AMOSWAP, true, false, .Data, .Data)) s hpmp
  have hea := execMemWriteEaAmo4M .PBMT_PMA (amoM4Pa rs1 s) region (s.regs .mstatus) s hpmpc hm hpalign
    hrd hwr ha rfl hmprv hcp
  have hgta : exec (get_transformed_data_addr (.Regidx rs1) (zeros (n := 64))
      (.Atomic (.AMOSWAP, true, false, .Data, .Data)) 4) s =
      some (.Ext_DataAddr_OK (.Virtaddr (amoM4A8 rs1 s)), s) := by
    unfold get_transformed_data_addr
    exec_run [execExtDataGetAddrGpr, execTransformEffectiveAddressAmoM _ s hcp hmprv hpmm]
    rfl
  have htr : exec (translateAddr (.Virtaddr (amoM4A8 rs1 s)) (.Atomic (.AMOSWAP, true, false, .Data, .Data))) s =
      some (.Ok (.Physaddr (amoM4Pa rs1 s), .PBMT_PMA, init_ext_ptw), s) :=
    execTranslateAddrIdentityAmoM _ s hcp hmprv
  show exec (execute_AMO .AMOSWAP true false (.Regidx rs2) (.Regidx rs1) 4 (.Regidx rd)) s = _
  unfold execute_AMO
  rw [execCatchEarlyReturn]
  exec_run [hgta, halign, Functions.not, htr, hea]
  erw [execMemReadAmo4M .PBMT_PMA (amoM4Pa rs1 s) region w (s.regs .mstatus) s hpmpc hm hpalign hrd hwr ha
    hc hsig hhr hdev hb rfl hmprv hcp]
  exec_run [execRXBitsGpr]
  erw [execMemWriteValueAmo4M .PBMT_PMA (amoM4Pa rs1 s) region _ (s.regs .mstatus) s hpmpc hm hpalign hrd hwr
    ha hc hsig hhw hdev rfl hmprv hcp]
  exec_run [execWXBitsGpr]
  have e : BitVec.setWidth (4 * 8) w = w := BitVec.setWidth_eq w
  rw [e]
  rfl

/-! ## HALF B -- THE `execEff` MIRROR -/

/-- The physical-access normaliser at `execEff` (Lean-only, deviation 5): the
`eff_run` peel plus the closed integer arithmetic of the split-access loops
(`ExecSC4`'s `exec_mem`, instrumented). -/
syntax "amo_eff_mem" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| amo_eff_mem [$ls,*]) => `(tactic| eff_run [Weff.cons, pmaOkAligned,
      execEffSplitMisalignedUnsplit, untilFuelM, untilFuelM.go, misaligned_order, bits_of_physaddr,
      Int.reduceToNat, Int.reduceMul, Int.reduceAdd, Int.reduceSub, Int.cast_ofNat_Int, Int.natCast_zero,
      Int.toNat_natCast, Int.zero_mul, addIntZero, List.cons_append, $ls,*])

/-! ### 5. THE TWO MEMORY-TOUCHING STEPS, where the two trace elements are born -/

/-- Rocq `exec_eff_read_ram_resacq_4`: the acquiring reserved read emits
`WEread ⟨false, true, true⟩` -- not an ifetch, latest, SYNCHRONISING. -/
theorem execEffReadRamResacq4 (addr : BitVec 64) (w : BitVec 32) (s : ExecSt)
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    execEff (read_ram .Read_RISCV_reserved_acquire (.Physaddr addr) 4 false) s =
      some ((w, default_meta), s, [.WEread ⟨false, true, true⟩ addr 4]) := by
  have hr : bmRead s.mem addr 4 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  eff_run [hm, hr, Weff.cons]
  rfl

/-- The conditional write at any width (Lean-only, deviation 5): it stores the
bytes and emits `WEwrite ⟨false, true, false⟩` -- exclusive, not synchronising. -/
theorem execEffWriteRamCond (addr : BitVec 64) (n : Nat) (data : BitVec (8 * n)) (s : ExecSt)
    (hdev : devAddr addr = false) :
    execEff (write_ram .Write_RISCV_conditional (.Physaddr addr) n data ()) s =
      some (true, s.setMem (bmWrite s.mem addr n data), [.WEwrite ⟨false, true, false⟩ addr n data]) := by
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold write_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write PreSail.sail_mem_write
  eff_run [hm, Weff.cons]
  rfl

/-- Rocq `exec_eff_write_ram_cond_4`. -/
theorem execEffWriteRamCond4 (addr : BitVec 64) (data : BitVec 32) (s : ExecSt)
    (hdev : devAddr addr = false) :
    execEff (write_ram .Write_RISCV_conditional (.Physaddr addr) 4 data ()) s =
      some (true, s.setMem (bmWrite s.mem addr 4 data), [.WEwrite ⟨false, true, false⟩ addr 4 data]) :=
  execEffWriteRamCond addr 4 data s hdev

/-! ### 6. The register-only checks, mirrored at the empty trace -/

/-- Rocq `exec_eff_effectivePrivilege_amo_M`. -/
theorem execEffEffectivePrivilegeAmoM (m : BitVec 64) (s : ExecSt)
    (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    execEff (effectivePrivilege (.Atomic (.AMOSWAP, true, false, .Data, .Data)) m .Machine) s =
      some (.Machine, s, []) := by
  unfold effectivePrivilege
  simp only [h, Bool.and_false, Bool.false_eq_true, ↓reduceIte, execEffReturnm]

/-- Rocq `exec_eff_is_shadow_stack_amo`. -/
theorem execEffIsShadowStackAmo (s : ExecSt) :
    execEff (is_shadow_stack_access (.Atomic (.AMOSWAP, true, false, .Data, .Data))) s =
      some (false, s, []) := rfl

/-- Rocq `exec_eff_translateAddr_identity_amo_M`. -/
theorem execEffTranslateAddrIdentityAmoM (a : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    execEff (translateAddr (.Virtaddr a) (.Atomic (.AMOSWAP, true, false, .Data, .Data))) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s, []) := by
  unfold translateAddr
  rw [execEffCatchEarlyReturn]
  eff_run [hcp, execEffEffectivePrivilegeAmoM _ s hmprv, execEffTranslationModeM, execEffIsShadowStackAmo]

/-- Rocq `exec_eff_is_pmm_applicable_amo_M`. -/
theorem execEffIsPmmApplicableAmoM (s : ExecSt) :
    execEff (is_pmm_applicable (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (true, s, []) := rfl

/-- Rocq `exec_eff_get_pmlen_amo_M`. -/
theorem execEffGetPmlenAmoM (s : ExecSt)
    (h : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    execEff (get_pmlen (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s = some (0, s, []) := by
  unfold get_pmlen get_pmm
  eff_run [execEffIsPmmApplicableAmoM, h]

/-- Rocq `exec_eff_transform_effective_address_amo_M`. -/
theorem execEffTransformEffectiveAddressAmoM (ea : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    execEff (transform_effective_address (.Virtaddr ea) (.Atomic (.AMOSWAP, true, false, .Data, .Data))) s =
      some (pm_transform_PA (.Virtaddr ea) 0, s, []) := by
  unfold transform_effective_address
  eff_run [hcp, execEffEffectivePrivilegeAmoM _ s hmprv, execEffGetPmlenAmoM s hpmm, execEffTranslationModeM]
  rfl

/-- Rocq `exec_eff_pmaCheck_ram_amo_4` (the eff mirror of `ExecSC3.execPmaCheckRamAmo4`). -/
theorem execEffPmaCheckRamAmo4 (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true) :
    execEff (pmaCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt true) s =
      some (.Ok pmaOkAligned, s, []) := by
  have hall : ((override_PMA region.attributes pbmt).readable && ((override_PMA region.attributes pbmt).writable &&
      pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4)) = true := by
    rw [hrd, hwr, ha]; rfl
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hall (execEffIsMagApplicableAmo .AMOSWAP true false 4 s) hal

/-- The three device-window probes make the read a RAM access, at `execEff`
(Lean-only; Rocq's inline `Hmmio`). -/
theorem WeakLeafAmo4.execEffWithinMmioReadableFalse (addr : BitVec 64) (n : Nat) (s : ExecSt)
    (hc : execEff (within_clint (.Physaddr addr) n) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) n) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) n) s = some (false, s, [])) :
    execEff (within_mmio_readable (.Physaddr addr) n) s = some (false, s, []) := by
  unfold within_mmio_readable
  eff_run [hc, hsig, hh]

/-- The write twin (Lean-only). -/
theorem WeakLeafAmo4.execEffWithinMmioWritableFalse (addr : BitVec 64) (n : Nat) (s : ExecSt)
    (hc : execEff (within_clint (.Physaddr addr) n) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) n) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr addr) n) s = some (false, s, [])) :
    execEff (within_mmio_writable (.Physaddr addr) n) s = some (false, s, []) := by
  unfold within_mmio_writable
  eff_run [hc, hsig, hh]

/-- Rocq `exec_eff_mem_write_ea_amo_4_M`: register-only, so the trace stays empty. -/
theorem execEffMemWriteEaAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (m : BitVec 64) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    execEff (mem_write_ea (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt
      false false true) s = some (.Ok (), s, []) := by
  have hpma := execEffPmaCheckRamAmo4 addr pbmt region s hm hal hrd hwr ha
  have hep : execEff (effectivePrivilege (.Atomic (.AMOSWAP, true, false, .Data, .Data)) (s.regs .mstatus)
      (s.regs .cur_privilege)) s = some (.Machine, s, []) := by
    rw [hcp, hms]; exact execEffEffectivePrivilegeAmoM _ s hmprv
  unfold mem_write_ea check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  amo_eff_mem [hep, hpma]
  amo_eff_mem [write_kind_of_flags, hpmp]

/-! ### 7. `mem_read` and `mem_write_value` at `execEff` -/

/-- Rocq `exec_eff_checked_mem_read_ram_amo_4_M`: the first trace element. -/
theorem execEffCheckedMemReadRamAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    execEff (checked_mem_read (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt .Machine (.Physaddr addr) 4
      true false true false) s = some (.Ok (w, default_meta), s, [.WEread ⟨false, true, true⟩ addr 4]) := by
  have hpma := execEffPmaCheckRamAmo4 addr pbmt region s hm hal hrd hwr ha
  have hmm := WeakLeafAmo4.execEffWithinMmioReadableFalse addr 4 s hc hsig hh
  have hrr := execEffReadRamResacq4 addr w s hdev hb
  unfold checked_mem_read check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  amo_eff_mem [hpma]
  amo_eff_mem [hpmp, hmm, hrr, read_kind_of_flags]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  congr
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  bv_decide

/-- Rocq `exec_eff_mem_read_amo_4_M`. -/
theorem execEffMemReadAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (m : BitVec 64) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w)
    (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    execEff (mem_read (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt (.Physaddr addr) 4 true false true) s =
      some (.Ok w, s, [.WEread ⟨false, true, true⟩ addr 4]) := by
  have hck := execEffCheckedMemReadRamAmo4M pbmt addr region w s hpmp hm hal hrd hwr ha hc hsig hh hdev hb
  unfold mem_read mem_read_priv mem_read_priv_meta
  eff_run [hcp, hms, execEffEffectivePrivilegeAmoM m s hmprv, hck]
  simp only [Nat.reduceMul]
  rfl

/-- Rocq `exec_eff_checked_mem_write_ram_amo_4_M`: the second trace element. -/
theorem execEffCheckedMemWriteRamAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 32) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) :
    execEff (checked_mem_write (.Physaddr addr) 4 data (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt
      .Machine () false false true) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 4 data), [.WEwrite ⟨false, true, false⟩ addr 4 data]) := by
  have hpma := execEffPmaCheckRamAmo4 addr pbmt region s hm hal hrd hwr ha
  have hmm := WeakLeafAmo4.execEffWithinMmioWritableFalse addr 4 s hc hsig hh
  have hw : ∀ k (d : BitVec (8 * k)), execEff (write_ram .Write_RISCV_conditional (.Physaddr addr) k d ()) s =
      some (true, s.setMem (bmWrite s.mem addr k d), [.WEwrite ⟨false, true, false⟩ addr k d]) :=
    fun k d => execEffWriteRamCond addr k d s hdev
  unfold checked_mem_write check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  amo_eff_mem [hpma]
  amo_eff_mem [hpmp, hmm, write_kind_of_flags, hw]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  have hd : ∀ x : BitVec 32, Sail.BitVec.extractLsb x 31 0 = x := by
    intro x; simp only [Sail.BitVec.extractLsb]; bv_decide
  simp only [hd]

/-- Rocq `exec_eff_mem_write_value_amo_4_M`. -/
theorem execEffMemWriteValueAmo4M (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 32) (m : BitVec 64) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .Machine) s =
      some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false)
    (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    execEff (mem_write_value (.Physaddr addr) 4 data (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt
      false false true) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 4 data), [.WEwrite ⟨false, true, false⟩ addr 4 data]) := by
  have hck := execEffCheckedMemWriteRamAmo4M pbmt addr region data s hpmp hm hal hrd hwr ha hc hsig hh hdev
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  eff_run [hcp, hms, execEffEffectivePrivilegeAmoM m s hmprv, hck]

/-- Rocq `exec_eff_amo_writeback` (deviation 6): the `rd` write-back and the
`RETIRE_SUCCESS`, register-only, over an ARBITRARY post-write state. -/
theorem execEffAmoWriteback (rd : BitVec 5) (v : BitVec 64) (st : ExecSt) (_hrd : rd.toNat ≠ 0) :
    execREff ((liftM (wX_bits (.Regidx rd) v) : SailME ExecutionResult Unit) >>= fun _ =>
      (pure RETIRE_SUCCESS : SailME ExecutionResult ExecutionResult)) st =
      some (.inr RETIRE_SUCCESS, st.setGpr rd v, []) := by
  rw [execREffLiftRSeq _ _ _ _ _ (execEffWXBitsGpr rd v st)]
  rfl

/-! ### 8. THE DELIVERABLE: `amoswap.w.aq` at `execEff`, TWO ADJACENT EVENTS -/

set_option simprocs false in
/-- **THE DELIVERABLE.**  Rocq `exec_eff_execute_AMOSWAP_4_gpr`: the
acquire-flavoured read of the OLD word immediately followed by the exclusive
write of the NEW one, nothing between them -- the shape
`WeakEff.wcertAmoAqGen` consumes. -/
theorem execEffExecuteAMOSWAP4Gpr (rs2 rs1 rd : BitVec 5) (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (_hrd : rd.toNat ≠ 0)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (amoM4A8 rs1 s)) 4 = true)
    (hpmp : execEff (pmpCheck (.Physaddr (amoM4Pa rs1 s)) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data))
      .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr (amoM4Pa rs1 s)) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (amoM4Pa rs1 s)) 4 = true)
    (hrd : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hwr : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes .PBMT_PMA).atomic_support .AMOSWAP 4 = true)
    (hc : execEff (within_clint (.Physaddr (amoM4Pa rs1 s)) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (amoM4Pa rs1 s)) 4) s = some (false, s, []))
    (hhr : execEff (within_htif_readable (.Physaddr (amoM4Pa rs1 s)) 4) s = some (false, s, []))
    (hhw : execEff (within_htif_writable (.Physaddr (amoM4Pa rs1 s)) 4) s = some (false, s, []))
    (hdev : devAddr (amoM4Pa rs1 s) = false)
    (hb : BytesAt s (amoM4Pa rs1 s) 4 w) :
    execEff (execute (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd))) s =
      some (RETIRE_SUCCESS, (s.setMem (bmWrite s.mem (amoM4Pa rs1 s) 4 (amoM4Store rs2 s))).setGpr rd
        (sign_extend (m := 64) w),
        [.WEread ⟨false, true, true⟩ (amoM4Pa rs1 s) 4,
         .WEwrite ⟨false, true, false⟩ (amoM4Pa rs1 s) 4 (amoM4Store rs2 s)]) := by
  have hea := execEffMemWriteEaAmo4M .PBMT_PMA (amoM4Pa rs1 s) region (s.regs .mstatus) s hpmp hm hpalign
    hrd hwr ha rfl hmprv hcp
  have hgta : execEff (get_transformed_data_addr (.Regidx rs1) (zeros (n := 64))
      (.Atomic (.AMOSWAP, true, false, .Data, .Data)) 4) s =
      some (.Ext_DataAddr_OK (.Virtaddr (amoM4A8 rs1 s)), s, []) := by
    unfold get_transformed_data_addr
    eff_run [execEffExtDataGetAddrGpr, execEffTransformEffectiveAddressAmoM _ s hcp hmprv hpmm]
    rfl
  have htr : execEff (translateAddr (.Virtaddr (amoM4A8 rs1 s))
      (.Atomic (.AMOSWAP, true, false, .Data, .Data))) s =
      some (.Ok (.Physaddr (amoM4Pa rs1 s), .PBMT_PMA, init_ext_ptw), s, []) :=
    execEffTranslateAddrIdentityAmoM _ s hcp hmprv
  show execEff (execute_AMO .AMOSWAP true false (.Regidx rs2) (.Regidx rs1) 4 (.Regidx rd)) s = _
  unfold execute_AMO
  rw [execEffCatchEarlyReturn]
  eff_run [hgta, halign, Functions.not, htr, hea]
  erw [execEffMemReadAmo4M .PBMT_PMA (amoM4Pa rs1 s) region w (s.regs .mstatus) s hpmp hm hpalign hrd hwr ha
    hc hsig hhr hdev hb rfl hmprv hcp]
  eff_run [execEffRXBitsGpr]
  erw [execEffMemWriteValueAmo4M .PBMT_PMA (amoM4Pa rs1 s) region _ (s.regs .mstatus) s hpmp hm hpalign hrd
    hwr ha hc hsig hhw hdev rfl hmprv hcp]
  eff_run [execEffWXBitsGpr]
  have e : BitVec.setWidth (4 * 8) w = w := BitVec.setWidth_eq w
  rw [e]
  rfl

end Weak
