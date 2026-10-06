/-
Weak: counters and callbacks, the CSR leaves and `csrw`/`csrr`/`csrrci`
executions, JALR, the S-mode effective address, the S-mode interrupt trap, the
read-frame congruence.

Rocq: `iris/MinstretInv.v`, `iris/WpGprMret.v`, `iris/WpGprCsrrA.v`,
`iris/WpGprCsrwA.v`, `iris/WpGprCsrwB.v`, `iris/WpGprCsrwCommon.v`,
`iris/WpGprCsrrCommon.v`, `iris/WpSconfCsr.v`, `iris/WpPushOffCsr.v`,
`iris/WpMmodeLeafBase.v` (`exec_execute_JALR_ret_zca`), `iris/UservecExitPt.v`,
`iris/WpIntrCore.v`, `iris/WpSmodeGpr.v` (`exec_transform_effective_address_load_S`),
`iris/UservecPt.v`, `iris/RiscvTryStep.v` (`execR_returnm_fwd`),
`iris/WpDecodeBridge.v` @ xxvzwolszwmp.

**Conventions (all `Weak/ExecSC*.lean` files; the deviations every statement shares).**
Statements are about `Weak.exec` over the LEAN model (sail-riscv `070832a1`,
`-D SYMBOLIC`: announce events silent), not Rocq's `exec` over the Coq model.
* GPRs: Rocq `if uint i =? 0 then zero_reg else register_lookup (R_bitvector_64
  (gpr_of_Z (uint i))) s.(sregs)` ↦ `s.gpr i`; Rocq `if uint rd =? 0 then s else
  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)` ↦
  `s.setGpr rd v` (`Weak/ExecSC.lean`).  Where Rocq has a `uint rd ≠ 0` premise and a
  plain `set_reg`, the premise is kept and the result is `setGpr` (equal under it).
* Spelling: `register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1" = b` ↦
  `(x == 1#1) = b`; `vec_access_dec v i` ↦ `v[i]!`; `vec_update_dec v i x` ↦
  `vectorUpdate v i x`; `uint x` ↦ `x.toNat`; `Z` widths/indices ↦ `Nat`;
  `mword n` ↦ `BitVec n`; `tt` ↦ `()`; `zeros' n` ↦ `zeros (n := n)`.
* Memory: `dev_addr pa = false` ↦ `devAddr pa = false`; Rocq's byte window
  `∀ j < n, s.(mem) !! pa_add pa j = Some (nth_byte w j)` ↦ `BytesAt s pa n w`;
  `MState s.(sregs) (write_bytes s.(mem) pa n v) s.(mdev)` ↦
  `s.setMem (bmWrite s.mem pa n v)`.  An ifetch is a RAM read in `exec`
  (`Weak/Exec.lean`), so the fetch facts read the byte map (`AK_ifetch` plays no role).
* `hartSupports` is pure in Lean: Rocq `exec (hartSupports X) s = Some (true, s)` ↦
  `hartSupports .X = true`; Rocq's fuelled `_rec_currentlyEnabled` facts are stated on
  `currentlyEnabled`.  Rocq loops (`foreach_ZM_up'`, `untilMT`) ↦ lean-sail's `IntRange`
  `forIn` and `untilFuelM`.
* Rocq section hypotheses become theorem premises; section `Let`s become `def`s or are
  inlined; premise bundles that several statements share are `structure`s
  (`FetchM4`, `FetchM2`, `FetchS`, `MemM8`, `AmoS4`), each field a Rocq hypothesis.

**Deviations from Rocq.**
1. The CSR program equations are MachCSL's (`MachCSL.WpCsrFacts`, `MachCSL.WpCsrS`);
   CSR numbers are literals (`0x300#12` for `csr_mstatus`, …).  `check_CSR` in Lean
   includes the Smstateen gate `stateen_allows_CSR_access` (Rocq's has it too).
2. `exec_write_CSR_stimecmp` / `exec_execute_csrw_stimecmp`: `∃ mp` for the timer's
   `mip` (as Rocq).  `exec_tick_clock`: `∃ c t p` (as Rocq).
3. `exec_execute_csrrci_sstatus`: the legalisation of `mstatus` is evaluated through
   MachCSL's `legalize_mstatus` walk, which needs the platform `misa`
   (`s.regs .misa = misaC`, for Rocq's `misa.S`/`misa.U` bits) and a nominal `MPP`
   (`extractLsb' 11 2 m ≠ 2#2`); `legalize_sstatus_val` is MachCSL's `mstatusLegalize`
   of the lifted value.
4. `exec_handle_interrupt_S`: Rocq's section `Let`s `s1 … s9` are `trapSupS9`.
5. `exec_goodb_congr`: `goodb` is defined over Lean's `Outcome` events (the same
   silent set as Rocq's).
6. JALR: the target is `BitVec.update (s.gpr rs1 + sign_extend imm) 0 0#1`.

**Name map (Rocq → Lean).**  MinstretInv: `exec_should_inc_mcycle_Some` ↦
`execShouldIncMcycleSome`, `exec_tick_clock` ↦ `execTickClock`.  WpGprMret:
`exec_long_csr_write_mstatus` ↦ `execLongCsrWriteMstatus`.  WpGprCsrrA:
`mstatus_rdval` ↦ `mstatusRdval`, `exec_read_CSR_mstatus` ↦ `execReadCSRMstatus`.
WpGprCsrwA: `mepc_val` ↦ `mepcVal`, `exec_write_CSR_mepc` ↦ `execWriteCSRMepc`,
`exec_write_CSR_mcounteren` ↦ `execWriteCSRMcounteren`, `menvcfg_cbie` ↦
`menvcfgCbie`, `menvcfg_legalized` ↦ `menvcfgLegalized`, `exec_write_CSR_menvcfg` ↦
`execWriteCSRMenvcfg`, `exec_execute_csrw_mcounteren_full` ↦
`execExecuteCsrwMcounterenFull`.  WpGprCsrwB: `mideleg_legalized` ↦
`midelegLegalized`, `exec_write_CSR_mideleg` ↦ `execWriteCSRMideleg`,
`exec_execute_csrw_mideleg` ↦ `execExecuteCsrwMideleg`, `stimecmp_legalized` ↦
`stimecmpLegalized`, `exec_write_CSR_stimecmp` ↦ `execWriteCSRStimecmp`,
`exec_is_stimecmp_accessible_M` ↦ `execIsStimecmpAccessibleM`,
`exec_is_CSR_accessible_stimecmp` ↦ `execIsCSRAccessibleStimecmp`,
`exec_execute_csrw_stimecmp` ↦ `execExecuteCsrwStimecmp`.  WpGprCsrwCommon:
`exec_check_CSR_csrw_p` ↦ `execCheckCSRCsrwP`, `exec_check_CSR_csrw` ↦
`execCheckCSRCsrw`, `exec_check_CSR_result_csrw` ↦ `execCheckCSRResultCsrw`,
`exec_doCSR_csrw_p` ↦ `execDoCSRCsrwP`, `sstatus_read` ↦ `sstatusRead`,
`sstatus_write_val` ↦ `sstatusWriteVal`, `legalize_sstatus_val` ↦
`legalizeSstatusVal`.  WpGprCsrrCommon: `exec_check_CSR_read_p` ↦ `execCheckCSRReadP`,
`exec_check_CSR_result_read_p` ↦ `execCheckCSRResultReadP`.  WpSconfCsr:
`exec_execute_csrr_sstatus` ↦ `execExecuteCsrrSstatus`.  WpPushOffCsr:
`exec_execute_csrrci_sstatus` ↦ `execExecuteCsrrciSstatus`.  WpMmodeLeafBase:
`exec_execute_JALR_ret_zca` ↦ `execExecuteJALRRetZca`.  UservecExitPt:
`exec_execute_JALR_link_zca` ↦ `execExecuteJALRLinkZca`.  WpIntrCore: `stvec_base` ↦
`stvecBase`, `exec_track_trap_S` ↦ `execTrackTrapS`, `exec_handle_interrupt_S` ↦
`execHandleInterruptS`.  WpSmodeGpr: `exec_transform_effective_address_load_S` ↦
`execTransformEffectiveAddressLoadS`.  UservecPt:
`exec_transform_effective_address_store_S` ↦ `execTransformEffectiveAddressStoreS`.
RiscvTryStep: `execR_returnm_fwd` ↦ `execRReturnmFwd`.  WpDecodeBridge: `goodb` ↦
`goodb`, `exec_goodb_congr` ↦ `execGoodbCongr`.  Lean-only:
`ExecSt.setReg_setReg_same`, `ExecSt.setReg_self`, `readMipVal`, `execReadMip`,
`execCsrNameWriteCallbackMip`, `tickShapeLift`, `tickShape1..4`,
`execCurrentlyEnabledSscofpmf`, `execCurrentlyEnabledHs`, `execClintDispatch`,
`execCheckCSRResultOk`, `execExecuteCSRRegCsrw`, `execCheckCSRResultCsrwM`,
`regidxNeZreg`, `execCheckCSRResultSstatusS`, `execLegalizeMstatus`,
`execExecuteJALRZca`, `trapSupS9`.

**Dropped**: none of the names the weak tier uses.
-/
import Weak.ExecSC6
import MachCSL.WpCsrFacts
import MachCSL.WpCsrS

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 0. Register-file algebra -/

theorem ExecSt.setReg_setReg_same (s : ExecSt) (r : Register) (v w : RegisterType r) :
    (s.setReg r v).setReg r w = s.setReg r w := by
  cases s
  simp only [ExecSt.setReg, ExecSt.mk.injEq, and_true]
  funext r'
  by_cases h : r' = r
  · subst h; simp [RegFile.set, BootRegs.set]
  · simp [RegFile.set, BootRegs.set, h]

theorem ExecSt.setReg_self (s : ExecSt) (r : Register) : s.setReg r (s.regs r) = s := by
  cases s
  simp only [ExecSt.setReg, ExecSt.mk.injEq, and_true]
  funext r'
  by_cases h : r' = r
  · subst h; simp [RegFile.set, BootRegs.set]
  · simp [RegFile.set, BootRegs.set, h]

/-! ## 1. Counters and callbacks (Rocq `MinstretInv`, `WpGprMret`, `WpIntrCore`) -/

/-- Rocq `MinstretInv.exec_should_inc_mcycle_Some`. -/
theorem execShouldIncMcycleSome (priv : Privilege) (s : ExecSt) :
    ∃ b : Bool, exec (should_inc_mcycle priv) s = some (b, s) := by
  unfold should_inc_mcycle
  exec_run
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Rocq `WpGprMret.exec_long_csr_write_mstatus`. -/
theorem execLongCsrWriteMstatus (V : BitVec 64) (s : ExecSt) :
    exec (long_csr_write_callback "mstatus" "mstatush" V) s = some ((), s) := by
  unfold long_csr_write_callback csr_name_write_callback
  exec_run
  rfl

/-- The value `read_mip IncludePlatformInterrupts` reads. -/
def readMipVal (s : ExecSt) : BitVec 64 :=
  Mk_Minterrupts (s.regs .mip ||| _update_Minterrupts_SEI
    (_update_Minterrupts_MEI (Mk_Minterrupts (zeros (n := 64))) (s.regs .sig_meip))
    (if (_get_Misa_S (s.regs .misa) == 1#1) = true then s.regs .sig_seip else 0#1))

theorem execReadMip (s : ExecSt) : exec (read_mip .IncludePlatformInterrupts) s = some (readMipVal s, s) := by
  unfold read_mip external_interrupts_pending readMipVal
  cases h : (_get_Misa_S (s.regs .misa) == 1#1) <;> exec_run [execCurrentlyEnabledS, h]

theorem execCsrNameWriteCallbackMip (v : BitVec 64) (s : ExecSt) :
    exec (csr_name_write_callback "mip" v) s = some ((), s) := rfl

theorem tickShapeLift {L : ExecSt} {R : BitVec 64 → BitVec 64 → BitVec 64 → ExecSt}
    (h : ∃ c t p, L = R c t p) : ∃ c t p, (some ((), L) : Option (Unit × ExecSt)) = some ((), R c t p) := by
  obtain ⟨c, t, p, e⟩ := h; exact ⟨c, t, p, by rw [e]⟩

theorem tickShape1 (s : ExecSt) (T P : BitVec 64) :
    ∃ c t p, (s.setReg .mtime T).setReg .mip P = ((s.setReg .mcycle c).setReg .mtime t).setReg .mip p :=
  ⟨s.regs .mcycle, T, P, by rw [ExecSt.setReg_self]⟩

theorem tickShape2 (s : ExecSt) (T P P' : BitVec 64) :
    ∃ c t p, ((s.setReg .mtime T).setReg .mip P).setReg .mip P' =
      ((s.setReg .mcycle c).setReg .mtime t).setReg .mip p :=
  ⟨s.regs .mcycle, T, P', by rw [ExecSt.setReg_self, ExecSt.setReg_setReg_same]⟩

theorem tickShape3 (s : ExecSt) (C T P : BitVec 64) :
    ∃ c t p, ((s.setReg .mcycle C).setReg .mtime T).setReg .mip P =
      ((s.setReg .mcycle c).setReg .mtime t).setReg .mip p := ⟨C, T, P, rfl⟩

theorem tickShape4 (s : ExecSt) (C T P P' : BitVec 64) :
    ∃ c t p, (((s.setReg .mcycle C).setReg .mtime T).setReg .mip P).setReg .mip P' =
      ((s.setReg .mcycle c).setReg .mtime t).setReg .mip p := ⟨C, T, P', by rw [ExecSt.setReg_setReg_same]⟩

/-- Rocq `MinstretInv.exec_tick_clock`. -/
theorem execTickClock (s : ExecSt) :
    ∃ c t p : BitVec 64, exec (tick_clock ()) s =
      some ((), ((s.setReg .mcycle c).setReg .mtime t).setReg .mip p) := by
  obtain ⟨b, hb⟩ := execShouldIncMcycleSome (s.regs .cur_privilege) s
  unfold tick_clock clint_dispatch get_config_print_clint
  cases b <;> exec_run [hb, execCurrentlyEnabledSstc] <;>
  repeat' (split <;> (try exec_run [execCsrNameWriteCallbackMip, execReadMip]))
  all_goals first
  | exact tickShapeLift (tickShape2 s _ _ _)
  | exact tickShapeLift (tickShape1 s _ _)
  | exact tickShapeLift (tickShape4 s _ _ _ _)
  | exact tickShapeLift (tickShape3 s _ _ _)

/-! ## 2. CSR leaves (Rocq `WpGprCsrwA`, `WpGprCsrwB`, `WpGprCsrrA`, `WpGprCsrwCommon`,
`WpGprCsrrCommon`) -/

/-- Rocq `WpGprCsrrA.mstatus_rdval`. -/
def mstatusRdval (s : ExecSt) : BitVec 64 := Sail.BitVec.extractLsb (s.regs .mstatus) 63 0

/-- Rocq `WpGprCsrrA.exec_read_CSR_mstatus`. -/
theorem execReadCSRMstatus (s : ExecSt) : exec (read_CSR 0x300#12) s = some (mstatusRdval s, s) := by
  rw [read_CSR_mstatus]; rfl

/-- Rocq `WpGprCsrwA.mepc_val`. -/
def mepcVal (v : BitVec 64) : BitVec 64 := BitVec.update v 0 0#1

/-- Rocq `WpGprCsrwA.exec_write_CSR_mepc`. -/
theorem execWriteCSRMepc (v : BitVec 64) (s : ExecSt) :
    exec (write_CSR 0x341#12 v) s = some (.Ok (mepcVal v), s.setReg .mepc (mepcVal v)) := by
  rw [write_CSR_mepc]
  unfold set_xepc legalize_xepc
  simp only [hartSupportsZca, ↓reduceIte]
  rfl

/-- Rocq `WpGprCsrwA.exec_write_CSR_mcounteren`. -/
theorem execWriteCSRMcounteren (v : BitVec 64) (s : ExecSt) :
    exec (write_CSR 0x306#12 v) s =
      some (.Ok (zero_extend (m := 64) (legalize_mcounteren (s.regs .mcounteren) v)),
        s.setReg .mcounteren (legalize_mcounteren (s.regs .mcounteren) v)) := by
  rw [write_CSR_mcounteren]; rfl

/-- Rocq `WpGprCsrwB.mideleg_legalized`. -/
def midelegLegalized (_o v : BitVec 64) : BitVec 64 :=
  let v := Mk_Minterrupts (v &&& plat_mideleg_delegatable_bits)
  _update_Minterrupts_SSI (_update_Minterrupts_STI (_update_Minterrupts_SEI
    (_update_Minterrupts_LCOFI v (_get_Minterrupts_LCOFI v)) (_get_Minterrupts_SEI v))
    (_get_Minterrupts_STI v)) (_get_Minterrupts_SSI v)

theorem execCurrentlyEnabledSscofpmf (s : ExecSt) : exec (currentlyEnabled .Ext_Sscofpmf) s = some (true, s) := by
  rw [currentlyEnabled]
  have h1 : hartSupports .Ext_Sscofpmf = true := by decide +kernel
  simp only [h1, ↓reduceIte]
  rw [currentlyEnabled]
  have h2 : hartSupports .Ext_Zihpm = true := by decide +kernel
  simp only [h2, ↓reduceIte, execCurrentlyEnabledZicsr]

/-- Rocq `WpGprCsrwB.exec_write_CSR_mideleg`. -/
theorem execWriteCSRMideleg (v : BitVec 64) (s : ExecSt) (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    exec (write_CSR 0x303#12 v) s =
      some (.Ok (midelegLegalized (s.regs .mideleg) v),
        s.setReg .mideleg (midelegLegalized (s.regs .mideleg) v)) := by
  rw [write_CSR_mideleg]
  unfold legalize_mideleg
  exec_run [execCurrentlyEnabledSscofpmf, execCurrentlyEnabledS, hS]
  rfl

/-- Rocq `WpGprCsrwA.menvcfg_cbie`. -/
def menvcfgCbie (v : BitVec 64) : BitVec 2 :=
  if (_get_MEnvcfg_CBIE (Mk_MEnvcfg v) != 0b10#2) = true then _get_MEnvcfg_CBIE (Mk_MEnvcfg v) else 0b00#2

/-- Rocq `WpGprCsrwA.menvcfg_legalized`. -/
def menvcfgLegalized (o v : BitVec 64) : BitVec 64 :=
  let v' := Mk_MEnvcfg v
  _update_MEnvcfg_PBMTE (_update_MEnvcfg_ADUE (_update_MEnvcfg_PMM (_update_MEnvcfg_STCE (_update_MEnvcfg_CBIE
    (_update_MEnvcfg_CBCFE (_update_MEnvcfg_CBZE (_update_MEnvcfg_SSE (_update_MEnvcfg_LPE (_update_MEnvcfg_FIOM o
      (if sys_enable_writable_fiom then _get_MEnvcfg_FIOM v' else 0#1))
      (_get_MEnvcfg_LPE v')) (_get_MEnvcfg_SSE v')) (_get_MEnvcfg_CBZE v')) (_get_MEnvcfg_CBCFE v'))
      (menvcfgCbie v)) (_get_MEnvcfg_STCE v'))
      (if (true && is_supported_pmm .PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM v'))) = true
       then _get_MEnvcfg_PMM v' else _get_MEnvcfg_PMM o))
    (_get_MEnvcfg_ADUE v')) (_get_MEnvcfg_PBMTE v')

theorem execCurrentlyEnabledHs (e : extension) (h : hartSupports e = true)
    (hc : currentlyEnabled e = pure (hartSupports e)) (s : ExecSt) :
    exec (currentlyEnabled e) s = some (true, s) := by
  rw [hc, h]; rfl

/-- Rocq `WpGprCsrwA.exec_write_CSR_menvcfg`. -/
theorem execWriteCSRMenvcfg (v : BitVec 64) (s : ExecSt) (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    exec (write_CSR 0x30A#12 v) s =
      some (.Ok (menvcfgLegalized (s.regs .menvcfg) v), s.setReg .menvcfg (menvcfgLegalized (s.regs .menvcfg) v)) := by
  have hZb : exec (currentlyEnabled .Ext_Zicboz) s = some (true, s) :=
    execCurrentlyEnabledHs _ (by decide +kernel) (by rw [currentlyEnabled]) s
  have hZm : exec (currentlyEnabled .Ext_Zicbom) s = some (true, s) :=
    execCurrentlyEnabledHs _ (by decide +kernel) (by rw [currentlyEnabled]) s
  have hSm : exec (currentlyEnabled .Ext_Smnpm) s = some (true, s) :=
    execCurrentlyEnabledHs _ (by decide +kernel) (by rw [currentlyEnabled]) s
  have hPb : exec (currentlyEnabled .Ext_Svpbmt) s = some (true, s) := by
    rw [currentlyEnabled]
    have : hartSupports .Ext_Svpbmt = true := by decide +kernel
    simp only [this, ↓reduceIte, execCurrentlyEnabledSv39 s hS]
  rw [write_CSR_menvcfg]
  unfold legalize_menvcfg legalize_xenvcfg_cbie menvcfgLegalized menvcfgCbie
  have hzl : hartSupports .Ext_Zicfilp = true := by decide +kernel
  have hzs : hartSupports .Ext_Zicfiss = true := by decide +kernel
  cases h1 : (_get_MEnvcfg_CBIE (Mk_MEnvcfg v) != 2#2) <;>
  cases h2 : is_supported_pmm .PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM (Mk_MEnvcfg v))) <;>
  exec_run [hzl, hzs, hZb, hZm, hSm, hPb, execCurrentlyEnabledSstc, execCurrentlyEnabledSvadu, h1, h2,
    sys_enable_writable_fiom, xenvcfg_cbie_reserved_behavior] <;> rfl

/-- Rocq `WpGprCsrwB.stimecmp_legalized`. -/
def stimecmpLegalized (prev v : BitVec 64) : BitVec 64 := Sail.BitVec.updateSubrange prev 63 0 v

/-- The timer recomputation moves only `mip`. -/
theorem execClintDispatch (s : ExecSt) : ∃ mp : BitVec 64, exec (clint_dispatch false) s = some ((), s.setReg .mip mp) := by
  unfold clint_dispatch get_config_print_clint
  exec_run [execCurrentlyEnabledSstc, execCsrNameWriteCallbackMip, execReadMip, execIte]
  repeat' split
  all_goals first
  | exact ⟨_, rfl⟩
  | exact ⟨_, by simp only [ExecSt.setReg_setReg_same]; rfl⟩

/-- Rocq `WpGprCsrwB.exec_write_CSR_stimecmp`: the write, then the timer's `mip`
recomputation (some value). -/
theorem execWriteCSRStimecmp (v : BitVec 64) (s : ExecSt) :
    ∃ mp : BitVec 64, exec (write_CSR 0x14D#12 v) s =
      some (.Ok (Sail.BitVec.extractLsb (stimecmpLegalized (s.regs .stimecmp) v) 63 0),
        (s.setReg .stimecmp (stimecmpLegalized (s.regs .stimecmp) v)).setReg .mip mp) := by
  rw [write_CSR_stimecmp]
  obtain ⟨mp, h⟩ := execClintDispatch (s.setReg .stimecmp (stimecmpLegalized (s.regs .stimecmp) v))
  unfold stimecmpLegalized at h ⊢
  exec_run [h]
  exact ⟨mp, rfl⟩

/-- Rocq `WpGprCsrwB.exec_is_stimecmp_accessible_M`. -/
theorem execIsStimecmpAccessibleM (s : ExecSt) (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    exec (is_stimecmp_accessible .Machine) s = some (true, s) := by
  unfold is_stimecmp_accessible
  exec_run [execCurrentlyEnabledS, hS, execCurrentlyEnabledSstc]

/-- Rocq `WpGprCsrwCommon.exec_check_CSR_csrw_p`. -/
theorem execCheckCSRCsrwP (p : Privilege) (csr : BitVec 12) (s : ExecSt)
    (hpriv : exec (check_CSR_priv csr p) s = some (true, s)) (hacc : check_CSR_access csr .CSRWrite = true)
    (hcsr : exec (is_CSR_accessible csr p .CSRWrite) s = some (true, s))
    (hst : exec (stateen_allows_CSR_access csr p .CSRWrite) s = some (true, s)) :
    exec (check_CSR csr p .CSRWrite) s = some (true, s) := by
  unfold check_CSR
  exec_run [hpriv, hacc, hcsr, hst]

/-- Rocq `WpGprCsrwCommon.exec_check_CSR_csrw`. -/
theorem execCheckCSRCsrw (csr : BitVec 12) (s : ExecSt)
    (hpriv : exec (check_CSR_priv csr .Machine) s = some (true, s)) (hacc : check_CSR_access csr .CSRWrite = true)
    (hcsr : exec (is_CSR_accessible csr .Machine .CSRWrite) s = some (true, s))
    (hst : exec (stateen_allows_CSR_access csr .Machine .CSRWrite) s = some (true, s)) :
    exec (check_CSR csr .Machine .CSRWrite) s = some (true, s) :=
  execCheckCSRCsrwP _ csr s hpriv hacc hcsr hst

/-- Rocq `WpGprCsrrCommon.exec_check_CSR_read_p`. -/
theorem execCheckCSRReadP (p : Privilege) (csr : BitVec 12) (s : ExecSt)
    (hpriv : exec (check_CSR_priv csr p) s = some (true, s)) (hacc : check_CSR_access csr .CSRRead = true)
    (hcsr : exec (is_CSR_accessible csr p .CSRRead) s = some (true, s))
    (hst : exec (stateen_allows_CSR_access csr p .CSRRead) s = some (true, s)) :
    exec (check_CSR csr p .CSRRead) s = some (true, s) := by
  unfold check_CSR
  exec_run [hpriv, hacc, hcsr, hst]

/-- The shared core of Rocq `exec_check_CSR_result_csrw(_p)` / `exec_check_CSR_result_read_p`. -/
theorem execCheckCSRResultOk (p : Privilege) (csr : BitVec 12) (a : CSRAccessType) (s : ExecSt)
    (h : exec (check_CSR csr p a) s = some (true, s)) :
    exec (check_CSR_result csr p a) s = some (.CSR_Check_OK (), s) := by
  unfold check_CSR_result
  exec_run [h]

/-- Rocq `WpGprCsrwCommon.exec_check_CSR_result_csrw`. -/
theorem execCheckCSRResultCsrw (csr : BitVec 12) (s : ExecSt)
    (h : exec (check_CSR csr .Machine .CSRWrite) s = some (true, s)) :
    exec (check_CSR_result csr .Machine .CSRWrite) s = some (.CSR_Check_OK (), s) :=
  execCheckCSRResultOk _ _ _ s h

/-- Rocq `WpGprCsrrCommon.exec_check_CSR_result_read_p`. -/
theorem execCheckCSRResultReadP (p : Privilege) (csr : BitVec 12) (s : ExecSt)
    (h : exec (check_CSR csr p .CSRRead) s = some (true, s)) :
    exec (check_CSR_result csr p .CSRRead) s = some (.CSR_Check_OK (), s) :=
  execCheckCSRResultOk _ _ _ s h

/-- Rocq `WpGprCsrwCommon.exec_doCSR_csrw_p`: a `csrw` (rd = x0) of a checked CSR other
than `mip`/`sip`. -/
theorem execDoCSRCsrwP (p : Privilege) (csr : BitVec 12) (v : BitVec 64) (s s' : ExecSt) (cfinal : BitVec 64)
    (hcp : s.regs .cur_privilege = p)
    (hchk : exec (check_CSR_result csr p .CSRWrite) s = some (.CSR_Check_OK (), s))
    (hext : ext_check_CSR csr p .CSRWrite = true) (h344 : (csr == 0x344#12) = false)
    (h144 : (csr == 0x144#12) = false)
    (hw : exec (write_CSR csr v) s = some (.Ok cfinal, s'))
    (hcb : exec (csr_id_write_callback csr cfinal) s' = some ((), s')) :
    exec (doCSR csr v zreg .CSRRW .CSRWrite) s = some (RETIRE_SUCCESS, s') := by
  have h344' : csr ≠ 0x344#12 := by simpa using h344
  have h144' : csr ≠ 0x144#12 := by simpa using h144
  unfold doCSR
  have hz : exec (wX_bits zreg (zeros (n := 64))) s' = some ((), s') := rfl
  exec_run [hcp, hchk, hext, Functions.not, hw, hz, hcb]

/-- `csrw csr, rs1` is `doCSR` of the source register as a pure write. -/
theorem execExecuteCSRRegCsrw (csr : BitVec 12) (rs1 : BitVec 5) (s : ExecSt) :
    exec (execute_CSRReg csr (.Regidx rs1) zreg .CSRRW) s =
      exec (doCSR csr (s.gpr rs1) zreg .CSRRW .CSRWrite) s := by
  unfold execute_CSRReg
  exec_run [execRXBitsGpr]
  rfl

/-- The `check_CSR_result` of an M-mode `csrw` whose CSR is accessible and not stateen-gated. -/
theorem execCheckCSRResultCsrwM (csr : BitVec 12) (s : ExecSt)
    (hpriv : check_CSR_priv csr .Machine = pure true) (hacc : check_CSR_access csr .CSRWrite = true)
    (hcsr : exec (is_CSR_accessible csr .Machine .CSRWrite) s = some (true, s))
    (hst : stateen_allows_CSR_access csr .Machine .CSRWrite = pure true) :
    exec (check_CSR_result csr .Machine .CSRWrite) s = some (.CSR_Check_OK (), s) :=
  execCheckCSRResultOk _ _ _ s (execCheckCSRCsrwP _ csr s (by rw [hpriv]; rfl) hacc hcsr (by rw [hst]; rfl))

/-- Rocq `WpGprCsrwB.exec_execute_csrw_mideleg`: `csrw mideleg, rs1` in M-mode. -/
theorem execExecuteCsrwMideleg (rs1 : BitVec 5) (s : ExecSt) (_hrs1 : rs1.toNat ≠ 0)
    (hcp : s.regs .cur_privilege = .Machine) (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    exec (execute_CSRReg 0x303#12 (.Regidx rs1) zreg .CSRRW) s =
      some (RETIRE_SUCCESS, s.setReg .mideleg (midelegLegalized (s.regs .mideleg) (s.gpr rs1))) := by
  rw [execExecuteCSRRegCsrw]
  have hacc : is_CSR_accessible 0x303#12 .Machine .CSRWrite = currentlyEnabled .Ext_S := by csr_dispatch_eq
  exact execDoCSRCsrwP _ _ _ s _ _ hcp
    (execCheckCSRResultCsrwM _ s (by csr_dispatch_eq) (by decide)
      (by rw [hacc, execCurrentlyEnabledS, hS]) (by csr_dispatch_eq))
    (by decide) (by decide) (by decide) (execWriteCSRMideleg _ s hS) rfl

/-- Rocq `WpGprCsrwA.exec_execute_csrw_mcounteren_full`. -/
theorem execExecuteCsrwMcounterenFull (rs1 : BitVec 5) (s : ExecSt) (_hrs1 : rs1.toNat ≠ 0)
    (hcp : s.regs .cur_privilege = .Machine) (hU : (_get_Misa_U (s.regs .misa) == 1#1) = true) :
    exec (execute_CSRReg 0x306#12 (.Regidx rs1) zreg .CSRRW) s =
      some (RETIRE_SUCCESS, s.setReg .mcounteren (legalize_mcounteren (s.regs .mcounteren) (s.gpr rs1))) := by
  rw [execExecuteCSRRegCsrw]
  have hacc : is_CSR_accessible 0x306#12 .Machine .CSRWrite = currentlyEnabled .Ext_U := by csr_dispatch_eq
  exact execDoCSRCsrwP _ _ _ s _ _ hcp
    (execCheckCSRResultCsrwM _ s (by csr_dispatch_eq) (by decide)
      (by rw [hacc, execCurrentlyEnabledU s hU]) (by csr_dispatch_eq))
    (by decide) (by decide) (by decide) (execWriteCSRMcounteren _ s) rfl

/-- Rocq `WpGprCsrwB.exec_is_CSR_accessible_stimecmp`. -/
theorem execIsCSRAccessibleStimecmp (s : ExecSt) (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    exec (is_CSR_accessible 0x14D#12 .Machine .CSRWrite) s = some (true, s) := by
  have hacc : is_CSR_accessible 0x14D#12 .Machine .CSRWrite = is_stimecmp_accessible .Machine := by
    csr_dispatch_eq
  rw [hacc, execIsStimecmpAccessibleM s hS]

/-- Rocq `WpGprCsrwB.exec_execute_csrw_stimecmp`. -/
theorem execExecuteCsrwStimecmp (rs1 : BitVec 5) (s : ExecSt) (_hrs1 : rs1.toNat ≠ 0)
    (hcp : s.regs .cur_privilege = .Machine) (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    ∃ mp : BitVec 64, exec (execute_CSRReg 0x14D#12 (.Regidx rs1) zreg .CSRRW) s =
      some (RETIRE_SUCCESS,
        (s.setReg .stimecmp (stimecmpLegalized (s.regs .stimecmp) (s.gpr rs1))).setReg .mip mp) := by
  obtain ⟨mp, hw⟩ := execWriteCSRStimecmp (s.gpr rs1) s
  refine ⟨mp, ?_⟩
  rw [execExecuteCSRRegCsrw]
  exact execDoCSRCsrwP _ _ _ s _ _ hcp
    (execCheckCSRResultCsrwM _ s (by csr_dispatch_eq) (by decide) (execIsCSRAccessibleStimecmp s hS)
      (by csr_dispatch_eq))
    (by decide) (by decide) (by decide) hw rfl

/-! ## 3. `sstatus` (Rocq `WpSconfCsr`, `WpPushOffCsr`, `WpGprCsrwCommon`) -/

/-- A non-`x0` index is not `zreg`. -/
theorem regidxNeZreg (rd : BitVec 5) (hrd : rd.toNat ≠ 0) : (regidx.Regidx rd == zreg) = false := by
  rcases uxa_bv5_cases rd with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact absurd rfl hrd

/-- Rocq `WpGprCsrwCommon.sstatus_read`. -/
def sstatusRead (ms : BitVec 64) : BitVec 64 := Sail.BitVec.extractLsb (lower_mstatus ms) 63 0

/-- Rocq `WpGprCsrwCommon.sstatus_write_val`. -/
def sstatusWriteVal (ms : BitVec 64) (imm5 : BitVec 5) : BitVec 64 :=
  sstatusRead ms &&& ~~~(zero_extend (m := 64) imm5)

/-- Rocq `WpGprCsrwCommon.legalize_sstatus_val` (MachCSL's `mstatusLegalize`). -/
def legalizeSstatusVal (m v : BitVec 64) : BitVec 64 :=
  mstatusLegalize m (lift_sstatus m (Mk_Sstatus (zero_extend (m := 64) v)))

/-- The `check_CSR_result` of an S-mode `sstatus` access. -/
theorem execCheckCSRResultSstatusS (a : CSRAccessType) (s : ExecSt) (hacc : check_CSR_access 0x100#12 a = true)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    exec (check_CSR_result 0x100#12 .Supervisor a) s = some (.CSR_Check_OK (), s) := by
  have hc : is_CSR_accessible 0x100#12 .Supervisor a = currentlyEnabled .Ext_S := by
    cases a <;> csr_dispatch_eq
  have hst : stateen_allows_CSR_access 0x100#12 .Supervisor a = pure true := by cases a <;> csr_dispatch_eq
  apply execCheckCSRResultOk
  unfold check_CSR
  rw [hc, hst]
  have hp : check_CSR_priv 0x100#12 .Supervisor = pure true := by csr_dispatch_eq
  exec_run [hp, hacc, execCurrentlyEnabledS, hS]

/-- Rocq `WpSconfCsr.exec_execute_csrr_sstatus`: `csrr rd, sstatus` in S-mode. -/
theorem execExecuteCsrrSstatus (rd : BitVec 5) (m : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Supervisor) (hm : s.regs .mstatus = m)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) (hrd : rd.toNat ≠ 0) :
    exec (execute (.CSRReg (0x100#12, .Regidx 0#5, .Regidx rd, .CSRRS))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (sstatusRead m)) := by
  have hz : (regidx.Regidx rd == zreg) = false := regidxNeZreg rd hrd
  have hz0 : (regidx.Regidx 0#5 == zreg) = true := rfl
  show exec (execute_CSRReg 0x100#12 (.Regidx 0#5) (.Regidx rd) .CSRRS) s = _
  unfold execute_CSRReg doCSR
  have hc := execCheckCSRResultSstatusS .CSRRead s rfl hS
  exec_run [hz, hz0, execRXBitsGpr, hcp, csr_access_type, hc, read_CSR_sstatus, hm, execWXBitsGpr]
  rfl

/-- `legalize_mstatus` at the platform `misa`, with a nominal `MPP` (MachCSL's walk,
through `execOfRunRead`). -/
theorem execLegalizeMstatus (o L : BitVec 64) (s : ExecSt) (hmisa : s.regs .misa = misaC)
    (hmpp : BitVec.extractLsb' 11 2 L ≠ 2#2) :
    exec (legalize_mstatus o L) s = some (mstatusLegalize o L, s) := by
  have h3 : ∀ x : BitVec 2, x ≠ 2#2 → x = 0#2 ∨ x = 1#2 ∨ x = 3#2 := by decide
  have hw : runRead drefMisa (legalize_mstatus o L) = some (mstatusLegalize o L, true) := by
    rcases h3 _ hmpp with hm | hm | hm
    · exact legalize_mstatus_walk0 o L hm
    · exact legalize_mstatus_walk1 o L hm
    · exact legalize_mstatus_walk3 o L hm
  refine execOfRunRead drefMisa _ s _ true ?_ hw
  intro r v hv
  unfold drefMisa at hv
  split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
  subst hv
  exact hmisa

/-- Rocq `WpPushOffCsr.exec_execute_csrrci_sstatus`: `csrrci rd, sstatus, imm5` in S-mode
whose legalised write leaves `mstatus` as it was. Deviation: the platform `misa` (MachCSL's
legalisation walk reads it) for Rocq's `misa.S`/`misa.U` bits, and a nominal `MPP`. -/
theorem execExecuteCsrrciSstatus (imm5 rd : BitVec 5) (m : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Supervisor) (hm : s.regs .mstatus = m) (hmisa : s.regs .misa = misaC)
    (himm : (imm5 == 0#5) = false) (hrd : rd.toNat ≠ 0) (hmpp : BitVec.extractLsb' 11 2 m ≠ 2#2)
    (hleg : legalizeSstatusVal m (sstatusWriteVal m imm5) = m) :
    exec (execute (.CSRImm (0x100#12, imm5, .Regidx rd, .CSRRC))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (sstatusRead m)) := by
  have hz : (regidx.Regidx rd == zreg) = false := regidxNeZreg rd hrd
  have hS : (_get_Misa_S (s.regs .misa) == 1#1) = true := by rw [hmisa]; decide
  have himm' : (imm5 == zeros (n := 5)) = false := himm
  have hL := execLegalizeMstatus m (lift_sstatus m (Mk_Sstatus (zero_extend (m := 64) (sstatusWriteVal m imm5)))) s
    hmisa (by rw [lift_sstatus_mpp]; exact hmpp)
  unfold legalizeSstatusVal at hleg
  rw [hleg] at hL
  show exec (execute_CSRImm 0x100#12 imm5 (.Regidx rd) .CSRRC) s = _
  unfold execute_CSRImm doCSR
  have hc := execCheckCSRResultSstatusS .CSRReadWrite s rfl hS
  have hcb : ∀ v st, exec (csr_id_write_callback 0x100#12 v) st = some ((), st) := fun _ _ => rfl
  unfold sstatusWriteVal sstatusRead at hL
  subst hm
  exec_run [hz, himm', hcp, csr_access_type, hc, read_CSR_sstatus, execWXBitsGpr, write_CSR_sstatus,
    legalize_sstatus, hL, hcb, ExecSt.setReg_self]
  rfl

/-! ## 4. JALR, trap tracking, the S-mode effective address (Rocq `WpMmodeLeafBase`,
`UservecExitPt`, `WpIntrCore`, `WpSmodeGpr`, `UservecPt`, `RiscvTryStep`) -/

/-- Rocq `RiscvTryStep.execR_returnm_fwd` (the model's `returnm` is `pure`). -/
theorem execRReturnmFwd {R X : Type} (x : X) (s : ExecSt) : execR (pure x : SailME R X) s = some (.inr x, s) :=
  rfl

/-- `JALR` with `Zicfilp` off and `Zca` on: the link written, `nextPC` the cleared target. -/
theorem execExecuteJALRZca (imm : BitVec 12) (rs1 rd : BitVec 5) (s : ExecSt)
    (hzic : exec (currentlyEnabled .Ext_Zicfilp) s = some (false, s))
    (hzca : exec (currentlyEnabled .Ext_Zca) s = some (true, s))
    (halign : (Sail.BitVec.access (BitVec.update (s.gpr rs1 + sign_extend (m := 64) imm) 0 0#1) 0 == 0#1) = true) :
    exec (execute_JALR imm (.Regidx rs1) (.Regidx rd)) s =
      some (RETIRE_SUCCESS, (s.setReg .nextPC (BitVec.update (s.gpr rs1 + sign_extend (m := 64) imm) 0 0#1)).setGpr
        rd (s.regs .nextPC)) := by
  unfold execute_JALR update_elp_state get_next_pc
  exec_run [hzic, execRXBitsGpr, execJumpToZca _ s halign hzca, RETIRE_SUCCESS, execWXBitsGpr]

/-- Rocq `WpMmodeLeafBase.exec_execute_JALR_ret_zca` (`rd = x0`: no link). -/
theorem execExecuteJALRRetZca (imm : BitVec 12) (rs1 rdz : BitVec 5) (s : ExecSt) (_hrs1 : rs1.toNat ≠ 0)
    (hrdz : rdz.toNat = 0)
    (hzic : exec (currentlyEnabled .Ext_Zicfilp) s = some (false, s))
    (hzca : exec (currentlyEnabled .Ext_Zca) s = some (true, s))
    (halign : (Sail.BitVec.access (BitVec.update (s.gpr rs1 + sign_extend (m := 64) imm) 0 0#1) 0 == 0#1) = true) :
    exec (execute_JALR imm (.Regidx rs1) (.Regidx rdz)) s =
      some (RETIRE_SUCCESS, s.setReg .nextPC (BitVec.update (s.gpr rs1 + sign_extend (m := 64) imm) 0 0#1)) := by
  rw [execExecuteJALRZca imm rs1 rdz s hzic hzca halign]
  have : rdz = 0#5 := BitVec.eq_of_toNat_eq hrdz
  subst this
  rfl

/-- Rocq `UservecExitPt.exec_execute_JALR_link_zca` (`rd ≠ x0`: the link written). -/
theorem execExecuteJALRLinkZca (imm : BitVec 12) (rs1 rdz : BitVec 5) (s : ExecSt) (_hrs1 : rs1.toNat ≠ 0)
    (_hrdz : rdz.toNat ≠ 0)
    (hzic : exec (currentlyEnabled .Ext_Zicfilp) s = some (false, s))
    (hzca : exec (currentlyEnabled .Ext_Zca) s = some (true, s))
    (halign : (Sail.BitVec.access (BitVec.update (s.gpr rs1 + sign_extend (m := 64) imm) 0 0#1) 0 == 0#1) = true) :
    exec (execute_JALR imm (.Regidx rs1) (.Regidx rdz)) s =
      some (RETIRE_SUCCESS, (s.setReg .nextPC (BitVec.update (s.gpr rs1 + sign_extend (m := 64) imm) 0 0#1)).setGpr
        rdz (s.regs .nextPC)) :=
  execExecuteJALRZca imm rs1 rdz s hzic hzca halign

/-- Rocq `WpIntrCore.exec_track_trap_S`. -/
theorem execTrackTrapS (isI : Bool) (cause : BitVec 6) (s : ExecSt) :
    exec (track_trap .Supervisor isI cause) s = some ((), s) := by
  unfold track_trap
  exec_run [execLongCsrWriteMstatus]
  rfl

/-- Rocq `WpSmodeGpr.exec_transform_effective_address_load_S`. -/
theorem execTransformEffectiveAddressLoadS (ea satp0 : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Supervisor) (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2)
    (hsatp : s.regs .satp = satp0) (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hmxr : (_get_Mstatus_MXR (s.regs .mstatus) == 0#1) = true)
    (hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (s.regs .menvcfg)) = .PMM_Disabled) :
    exec (transform_effective_address (.Virtaddr ea) (.Load .Data)) s = some (pm_transform_VA (.Virtaddr ea) 0, s) := by
  unfold transform_effective_address get_pmlen get_pmm is_pmm_applicable
  exec_run [hcp, execEffectivePrivilegeLoadS _ s hmprv, hmxr, hpmm,
    execTranslationModeSSv39 satp0 s hsxl hsatp hmode]
  rfl

/-- Rocq `UservecPt.exec_transform_effective_address_store_S`. -/
theorem execTransformEffectiveAddressStoreS (ea satp0 : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Supervisor) (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2)
    (hsatp : s.regs .satp = satp0) (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hmxr : (_get_Mstatus_MXR (s.regs .mstatus) == 0#1) = true)
    (hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (s.regs .menvcfg)) = .PMM_Disabled) :
    exec (transform_effective_address (.Virtaddr ea) (.Store .Data)) s = some (.Virtaddr ea, s) := by
  unfold transform_effective_address get_pmlen get_pmm is_pmm_applicable
  exec_run [hcp, execEffectivePrivilegeStoreS _ s hmprv, hmxr, hpmm,
    execTranslationModeSSv39 satp0 s hsxl hsatp hmode]
  simp only [pm_transform_VA, sign_extend, Sail.BitVec.extractLsb, Sail.BitVec.signExtend, Functions.xlen,
    Option.some.injEq, Prod.mk.injEq, and_true, virtaddr.Virtaddr.injEq]
  bv_decide

/-! ## 5. The S-mode interrupt trap (Rocq `WpIntrCore` section `TrapReduce`) -/

/-- Rocq `WpIntrCore.stvec_base`. -/
def stvecBase (v : BitVec 64) : BitVec 64 := _get_Mtvec_Base v ++ 0b00#2

/-- Rocq's `s9` of section `TrapReduce`: the model's exact write order of an S-mode
interrupt trap. -/
def trapSupS9 (s : ExecSt) (i : InterruptType) (pc0 ms_v sc_old : BitVec 64) (elp_v : BitVec 1) : ExecSt :=
  let ms_e := Sail.BitVec.updateSubrange ms_v 23 23 elp_v
  let s1e := (s.setReg .mstatus ms_e).setReg .elp (landing_pad_bits_backwards .NO_LP_EXPECTED)
  let c1 := Sail.BitVec.updateSubrange sc_old (64 - 1) (64 - 1) (bool_to_bit (trapCause_is_interrupt (.Interrupt i)))
  let c2 := Sail.BitVec.updateSubrange c1 (64 - 2) 0
    (zero_extend (m := 64 - 1) (trapCause_bits_forwards (.Interrupt i)))
  let ms_a := Sail.BitVec.updateSubrange ms_e 5 5 (_get_Mstatus_SIE ms_e)
  let ms_b := Sail.BitVec.updateSubrange ms_a 1 1 0#1
  let ms_c := Sail.BitVec.updateSubrange ms_b 8 8 1#1
  ((((((((s1e.setReg .scause c1).setReg .scause c2).setReg .mstatus ms_a).setReg .mstatus ms_b).setReg .mstatus
    ms_c).setReg .stval (zeros (n := 64))).setReg .sepc pc0).setReg .cur_privilege .Supervisor)

/-- Rocq `WpIntrCore.exec_handle_interrupt_S`. -/
theorem execHandleInterruptS (s : ExecSt) (i : InterruptType) (pc0 ms_v sc_old stvec_v : BitVec 64)
    (elp_v : BitVec 1) (hpriv : s.regs .cur_privilege = .Supervisor) (hms : s.regs .mstatus = ms_v)
    (hsc : s.regs .scause = sc_old) (hstvec : s.regs .stvec = stvec_v) (help : s.regs .elp = elp_v)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = .TV_Direct) (hpc : s.regs .PC = pc0) :
    exec (handle_interrupt i .Supervisor) s =
      some ((), (trapSupS9 s i pc0 ms_v sc_old elp_v).setReg .nextPC (stvecBase stvec_v)) := by
  subst hms hsc hstvec help hpc
  unfold handle_interrupt trap_handler zicfilp_preserve_elp_on_trap reset_elp get_config_print_exception
    get_config_print_interrupt prepare_trap_vector tval
  exec_run [hartSupportsZicfilp, execTrackTrapS]
  simp (config := { decide := true }) only [ExecSt.setReg_regs, RegFile.set_other, RegFile.set_same,
    execCurrentlyEnabledS, hS, hpriv, execBind, exec, execReturnm, ↓reduceIte]
  exec_run [execTrackTrapS, tvec_addr]
  simp (config := { decide := true }) only [ExecSt.setReg_regs, RegFile.set_other, RegFile.set_same, htvd]
  exec_run [execSetNextPc]
  rfl

/-! ## 6. The read-frame congruence (Rocq `WpDecodeBridge`) -/

/-- Rocq `WpDecodeBridge.goodb`: `m`, run from `s`, reads only `D`-registers and does
nothing but silent events. -/
def goodb (D : Register → Bool) {X : Type} : SailM X → ExecSt → Bool
  | .pure _, _ => true
  | .impure (.error _) _, _ => false
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => D r && goodb D (k (s.regs r)) s
    | .instrAnnounce _ _, k => goodb D (k ()) s
    | .branchAnnounce _ _, k => goodb D (k ()) s
    | .barrier _, k => goodb D (k ()) s
    | .cacheOp _, k => goodb D (k ()) s
    | .tlbi _, k => goodb D (k ()) s
    | .takeException _, k => goodb D (k ()) s
    | .returnException _, k => goodb D (k ()) s
    | .translationStart _, k => goodb D (k ()) s
    | .translationEnd _, k => goodb D (k ()) s
    | .cycleCount, k => goodb D (k ()) s
    | .message _, k => goodb D (k ()) s
    | .getCycleCount, k => goodb D (k (0 : Nat)) s
    | _, _ => false

/-- Rocq `WpDecodeBridge.exec_goodb_congr`. -/
theorem execGoodbCongr (D : Register → Bool) {X : Type} (m : SailM X) :
    ∀ (s1 s2 : ExecSt), (∀ r, D r = true → s1.regs r = s2.regs r) → goodb D m s1 = true →
      ∃ x, exec m s1 = some (x, s1) ∧ exec m s2 = some (x, s2) := by
  induction m with
  | pure x => intro s1 s2 _ _; exact ⟨x, rfl, rfl⟩
  | impure call k ih =>
    intro s1 s2 hag hg
    cases call with
    | error e => simp [goodb] at hg
    | ok o =>
      cases o <;> simp only [goodb] at hg <;> first
        | (obtain ⟨x, h1, h2⟩ := ih _ s1 s2 hag hg; exact ⟨x, h1, h2⟩)
        | (simp at hg; done)
        | skip
      case regRead r =>
        simp only [Bool.and_eq_true] at hg
        obtain ⟨x, h1, h2⟩ := ih _ s1 s2 hag hg.2
        refine ⟨x, h1, ?_⟩
        show exec (k (s2.regs r)) s2 = _
        rw [← hag r hg.1]
        exact h2

end Weak
