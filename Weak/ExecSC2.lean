/-
Weak: privilege/translation/pointer-masking leaves, RAM reads and writes,
the split/MAG leaves, the extension gates, and the `IntRange` loop kit under `execR`.

Rocq: `iris/RiscvFetchExec.v`, `iris/WpLoad.v`, `iris/WpMmodeLeafBase.v`,
`iris/WpSmodeGpr.v`, `iris/WpAmo.v`, `iris/UserPtTree.v`, `iris/SmodePte.v`,
`iris/RiscvExtras.v`, `iris/WpDecode.v`, `iris/WpGprCsrwB.v`, `iris/CommonWalk.v`,
`iris/RiscvTryStep.v` (the parts named below) @ xxvzwolszwmp.

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
1. `execTranslateAddrIdentityAcc` is the shared core of the load/store identity
   translations (any non-shadow-stack access at Machine with `MPRV` clear).
2. `exec_read_ram_*` / `exec_write_ram_*` are instances of `execReadRam` /
   `execWriteRam` (any of the read/write kinds the model maps to a RAM access).
3. `exec_assert_exp'_true` is about Lean's `assert true msg` (Rocq's returned a proof).
4. `exec_split_on_page_boundary_aligned`: `vmem_width` is `vmemWidth` (`Nat`); the
   result is `(((w : Int), 0), s)`.
5. `execR_foreach_ZM_up'_const/_allow` are about lean-sail's `forIn` over an
   `IntRange` of step 1 (`execRForInConst/Allow`), with the body as `Int → Unit → …`.
6. `MISA_C` is `misaC`; `exec_currentlyEnabled_Svnapot` assumes `s.regs .misa = misaC`.

**Name map (Rocq → Lean).**  RiscvFetchExec: `exec_effectivePrivilege_fetch` ↦
`execEffectivePrivilegeFetch`, `exec_is_shadow_stack_fetch` ↦
`execIsShadowStackFetch`, `exec_translationMode_M` ↦ `execTranslationModeM`,
`exec_translateAddr_identity` ↦ `execTranslateAddrIdentity`, `exec_read_ram_plain_4`
↦ `execReadRamPlain4`, `exec_read_ram_plain_2` ↦ `execReadRamPlain2`,
`exec_hartSupports_Zca` ↦ `hartSupportsZca`, `exec_rec_cE_C_misa` ↦
`execCurrentlyEnabledC`, `exec_currentlyEnabled_S` ↦ `execCurrentlyEnabledS`,
`exec_currentlyEnabled_Zca` ↦ `execCurrentlyEnabledZca`,
`exec_currentlyEnabled_Ziccif` ↦ `execCurrentlyEnabledZiccif`, `MISA_C` ↦ `misaC`.
WpLoad: `exec_effectivePrivilege_load` ↦ `execEffectivePrivilegeLoad`,
`exec_is_shadow_stack_load` ↦ `execIsShadowStackLoad`,
`exec_translateAddr_identity_load` ↦ `execTranslateAddrIdentityLoad`,
`exec_transform_effective_address_load` ↦ `execTransformEffectiveAddressLoad`,
`exec_read_ram_plain_8` ↦ `execReadRamPlain8`, `exec_read_ram_resv_8` ↦
`execReadRamResv8`.  WpMmodeLeafBase: `exec_effectivePrivilege_store` ↦
`execEffectivePrivilegeStore`, `exec_is_shadow_stack_store` ↦
`execIsShadowStackStore`, `exec_translateAddr_identity_store` ↦
`execTranslateAddrIdentityStore`, `exec_is_pmm_applicable_store` ↦
`execIsPmmApplicableStore`, `exec_get_pmlen_store` ↦ `execGetPmlenStore`,
`exec_transform_effective_address_store` ↦ `execTransformEffectiveAddressStore`,
`exec_write_ram_plain_8` ↦ `execWriteRamPlain8`, `exec_write_ram_cond_8` ↦
`execWriteRamCond8`, `exec_get_xLPE_S` ↦ `execGetXLPES`, `exec_cE_zicfilp_false` ↦
`execCEZicfilpFalse`.  WpSmodeGpr: `exec_effectivePrivilege_load_S` ↦
`execEffectivePrivilegeLoadS`, `exec_effectivePrivilege_store_S` ↦
`execEffectivePrivilegeStoreS`.  WpAmo: `exec_effectivePrivilege_amo_S` ↦
`execEffectivePrivilegeAmoS`, `exec_is_shadow_stack_amo` ↦ `execIsShadowStackAmo`,
`exec_get_pmlen_amo_S` ↦ `execGetPmlenAmoS`, `exec_read_ram_resacq_4` ↦
`execReadRamResacq4`, `exec_write_ram_cond_4` ↦ `execWriteRamCond4`.  UserPtTree:
`u_acc` ↦ `uAcc`, `exec_is_shadow_stack_u_acc` ↦ `execIsShadowStackUAcc`,
`exec_effectivePrivilege_mprv0` ↦ `execEffectivePrivilegeMprv0`.  SmodePte:
`exec_translationMode_S_sv39` ↦ `execTranslationModeSSv39`.  RiscvExtras:
`exec_split_misaligned_unsplit` ↦ `execSplitMisalignedUnsplit`,
`exec_assert_exp'_true` ↦ `execAssertExpTrue`, `exec_is_mag_applicable_{load,store}_
{pte,data}` ↦ `execIsMagApplicable{Load,Store}{Pte,Data}`,
`exec_split_on_page_boundary_intra` ↦ `execSplitOnPageBoundaryIntra`, `vmem_width` ↦
`vmemWidth`, `exec_split_on_page_boundary_aligned` ↦ `execSplitOnPageBoundaryAligned`.
WpDecode: `exec_hartSupports_Zicfilp` ↦ `hartSupportsZicfilp`,
`exec_rec_cE_Zicsr_any` ↦ `execCurrentlyEnabledZicsr`.  WpGprCsrwB:
`exec_hartSupports_Sv48` ↦ `hartSupportsSv48`, `exec_currentlyEnabled_Svbare` ↦
`execCurrentlyEnabledSvbare`.  CommonWalk: `exec_currentlyEnabled_Svnapot` ↦
`execCurrentlyEnabledSvnapot`, `exec_currentlyEnabled_Svadu` ↦
`execCurrentlyEnabledSvadu`.  RiscvTryStep: `execR_foreach_ZM_up'_const` ↦
`execRForInConst`, `execR_foreach_ZM_up'_allow` ↦ `execRForInAllow`.  Lean-only:
`BytesAt`, `execReadRam`, `execWriteRam`, `execTranslateAddrIdentityAcc`,
`execGetPmlenLoad`, `isAlignedVaddrMod`, `pageMask64`, `andLowZero`,
`splitOnPageBoundaryAlignedEq`, `execCurrentlyEnabledSv39`, `execRForInFirstEarly`.

**Dropped**: none of the names the weak tier uses.
-/
import Weak.ExecSC
import MachCSL.UByteFrame
import MachCSL.WpPmpDefs

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. Effective privilege, shadow-stack test, translation mode -/

/-- Rocq `RiscvFetchExec.exec_effectivePrivilege_fetch`. -/
theorem execEffectivePrivilegeFetch (m : BitVec 64) (p : Privilege) (s : ExecSt) :
    exec (effectivePrivilege (.InstructionFetch ()) m p) s = some (p, s) := rfl

/-- Rocq `UserPtTree.exec_effectivePrivilege_mprv0`: `MPRV` clear, the privilege itself. -/
theorem execEffectivePrivilegeMprv0 (acc : MemoryAccessType mem_payload) (m : BitVec 64) (pr : Privilege)
    (s : ExecSt) (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    exec (effectivePrivilege acc m pr) s = some (pr, s) := by
  unfold effectivePrivilege
  simp only [h, Bool.and_false, Bool.false_eq_true, ↓reduceIte, execReturnm]

/-- Rocq `WpLoad.exec_effectivePrivilege_load`. -/
theorem execEffectivePrivilegeLoad (m : BitVec 64) (s : ExecSt) (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    exec (effectivePrivilege (.Load .Data) m .Machine) s = some (.Machine, s) :=
  execEffectivePrivilegeMprv0 _ m _ s h

/-- Rocq `WpMmodeLeafBase.exec_effectivePrivilege_store`. -/
theorem execEffectivePrivilegeStore (m : BitVec 64) (s : ExecSt) (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    exec (effectivePrivilege (.Store .Data) m .Machine) s = some (.Machine, s) :=
  execEffectivePrivilegeMprv0 _ m _ s h

/-- Rocq `WpSmodeGpr.exec_effectivePrivilege_load_S`. -/
theorem execEffectivePrivilegeLoadS (m : BitVec 64) (s : ExecSt) (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    exec (effectivePrivilege (.Load .Data) m .Supervisor) s = some (.Supervisor, s) :=
  execEffectivePrivilegeMprv0 _ m _ s h

/-- Rocq `WpSmodeGpr.exec_effectivePrivilege_store_S`. -/
theorem execEffectivePrivilegeStoreS (m : BitVec 64) (s : ExecSt) (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    exec (effectivePrivilege (.Store .Data) m .Supervisor) s = some (.Supervisor, s) :=
  execEffectivePrivilegeMprv0 _ m _ s h

/-- Rocq `WpAmo.exec_effectivePrivilege_amo_S`. -/
theorem execEffectivePrivilegeAmoS (m : BitVec 64) (aq rl : Bool) (s : ExecSt)
    (h : (_get_Mstatus_MPRV m == 1#1) = false) :
    exec (effectivePrivilege (.Atomic (.AMOSWAP, aq, rl, .Data, .Data)) m .Supervisor) s =
      some (.Supervisor, s) :=
  execEffectivePrivilegeMprv0 _ m _ s h

/-- Rocq `RiscvFetchExec.exec_is_shadow_stack_fetch`. -/
theorem execIsShadowStackFetch (s : ExecSt) :
    exec (is_shadow_stack_access (.InstructionFetch ())) s = some (false, s) := rfl
/-- Rocq `WpLoad.exec_is_shadow_stack_load`. -/
theorem execIsShadowStackLoad (s : ExecSt) : exec (is_shadow_stack_access (.Load .Data)) s = some (false, s) :=
  rfl
/-- Rocq `WpMmodeLeafBase.exec_is_shadow_stack_store`. -/
theorem execIsShadowStackStore (s : ExecSt) :
    exec (is_shadow_stack_access (.Store .Data)) s = some (false, s) := rfl
/-- Rocq `WpAmo.exec_is_shadow_stack_amo`. -/
theorem execIsShadowStackAmo (aq rl : Bool) (s : ExecSt) :
    exec (is_shadow_stack_access (.Atomic (.AMOSWAP, aq, rl, .Data, .Data))) s = some (false, s) := rfl

/-- Rocq `UserPtTree.u_acc`: the access kinds a user-tier walk issues. -/
def uAcc (acc : MemoryAccessType mem_payload) : Prop :=
  acc = .InstructionFetch () ∨ acc = .Load .Data ∨ acc = .Store .Data

/-- Rocq `UserPtTree.exec_is_shadow_stack_u_acc`. -/
theorem execIsShadowStackUAcc (acc : MemoryAccessType mem_payload) (s : ExecSt) (h : uAcc acc) :
    exec (is_shadow_stack_access acc) s = some (false, s) := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- Rocq `RiscvFetchExec.exec_translationMode_M`. -/
theorem execTranslationModeM (s : ExecSt) : exec (translationMode .Machine) s = some (.Bare, s) := rfl

/-- Rocq `SmodePte.exec_translationMode_S_sv39`. -/
theorem execTranslationModeSSv39 (satp0 : BitVec 64) (s : ExecSt)
    (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2) (hsatp : s.regs .satp = satp0)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4) :
    exec (translationMode .Supervisor) s = some (.Sv39, s) := by
  unfold translationMode
  simp only [show (Privilege.Supervisor == Privilege.Machine) = false from rfl, Bool.false_eq_true,
    ↓reduceIte, execBind, execArchitectureSupervisor s hsxl]
  exec_run [hsatp, hmode, assert, PreSail.assert]
  rfl

/-- Rocq `RiscvFetchExec.exec_translateAddr_identity`: at Machine, a fetch
translates to itself. -/
theorem execTranslateAddrIdentity (a : BitVec 64) (s : ExecSt) (hcp : s.regs .cur_privilege = .Machine) :
    exec (translateAddr (.Virtaddr a) (.InstructionFetch ())) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s) := by
  unfold translateAddr
  rw [execCatchEarlyReturn]
  exec_run [execRBind, execRLiftR, hcp, execEffectivePrivilegeFetch, execTranslationModeM,
    execIsShadowStackFetch]

/-- The data twin of `execTranslateAddrIdentity` (Rocq `WpLoad.exec_translateAddr_identity_load`,
`WpMmodeLeafBase.exec_translateAddr_identity_store`), for any non-shadow-stack access. -/
theorem execTranslateAddrIdentityAcc (a : BitVec 64) (acc : MemoryAccessType mem_payload) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hss : exec (is_shadow_stack_access acc) s = some (false, s)) :
    exec (translateAddr (.Virtaddr a) acc) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s) := by
  unfold translateAddr
  rw [execCatchEarlyReturn]
  exec_run [execRBind, execRLiftR, hcp, execEffectivePrivilegeMprv0 acc _ _ s hmprv, execTranslationModeM,
    hss]

/-- Rocq `WpLoad.exec_translateAddr_identity_load`. -/
theorem execTranslateAddrIdentityLoad (a : BitVec 64) (s : ExecSt) (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    exec (translateAddr (.Virtaddr a) (.Load .Data)) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s) :=
  execTranslateAddrIdentityAcc a _ s hcp hmprv (execIsShadowStackLoad s)

/-- Rocq `WpMmodeLeafBase.exec_translateAddr_identity_store`. -/
theorem execTranslateAddrIdentityStore (a : BitVec 64) (s : ExecSt) (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    exec (translateAddr (.Virtaddr a) (.Store .Data)) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s) :=
  execTranslateAddrIdentityAcc a _ s hcp hmprv (execIsShadowStackStore s)

/-! ## 2. Pointer masking -/

/-- Rocq `WpMmodeLeafBase.exec_is_pmm_applicable_store`. -/
theorem execIsPmmApplicableStore (s : ExecSt) :
    exec (is_pmm_applicable (.Store .Data) .Machine) s = some (true, s) := rfl

/-- Rocq `WpMmodeLeafBase.exec_get_pmlen_store`. -/
theorem execGetPmlenStore (s : ExecSt)
    (h : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    exec (get_pmlen (.Store .Data) .Machine) s = some (0, s) := by
  unfold get_pmlen get_pmm
  exec_run [execIsPmmApplicableStore, h]

/-- The load twin (used by Rocq `WpLoad.exec_transform_effective_address_load`). -/
theorem execGetPmlenLoad (s : ExecSt)
    (h : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    exec (get_pmlen (.Load .Data) .Machine) s = some (0, s) := by
  unfold get_pmlen get_pmm
  have : exec (is_pmm_applicable (.Load .Data) .Machine) s = some (true, s) := rfl
  exec_run [this, h]

/-- Rocq `WpAmo.exec_get_pmlen_amo_S`. -/
theorem execGetPmlenAmoS (aq rl : Bool) (s : ExecSt)
    (hmxr : (_get_Mstatus_MXR (s.regs .mstatus) == 0#1) = true)
    (h : pmm_mode_backwards (_get_MEnvcfg_PMM (s.regs .menvcfg)) = .PMM_Disabled) :
    exec (get_pmlen (.Atomic (.AMOSWAP, aq, rl, .Data, .Data)) .Supervisor) s = some (0, s) := by
  unfold get_pmlen get_pmm is_pmm_applicable
  cases aq <;> cases rl <;> exec_run [hmxr, h]

/-- Rocq `WpMmodeLeafBase.exec_transform_effective_address_store`. -/
theorem execTransformEffectiveAddressStore (ea : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    exec (transform_effective_address (.Virtaddr ea) (.Store .Data)) s =
      some (pm_transform_PA (.Virtaddr ea) 0, s) := by
  unfold transform_effective_address
  exec_run [hcp, execEffectivePrivilegeStore _ s hmprv, execGetPmlenStore s hpmm, execTranslationModeM]
  rfl

/-- Rocq `WpLoad.exec_transform_effective_address_load`. -/
theorem execTransformEffectiveAddressLoad (ea : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled) :
    exec (transform_effective_address (.Virtaddr ea) (.Load .Data)) s =
      some (pm_transform_PA (.Virtaddr ea) 0, s) := by
  unfold transform_effective_address
  exec_run [hcp, execEffectivePrivilegeLoad _ s hmprv, execGetPmlenLoad s hpmm, execTranslationModeM]
  rfl

/-! ## 3. RAM reads and writes (Rocq `RiscvFetchExec`, `WpLoad`, `WpMmodeLeafBase`, `WpAmo`) -/

/-- The Rocq byte-window premise `∀ j < n, s.(mem) !! (pa_add addr j) = Some (nth_byte w j)`. -/
def BytesAt (s : ExecSt) (addr : BitVec 64) (n : Nat) (w : BitVec (8 * n)) : Prop :=
  ∀ j, j < n → s.mem (addr + BitVec.ofNat 64 j) = some (nthByte w j)

/-- Any read kind of `n ≥ 1` RAM bytes reads the window (the common core of the
Rocq `exec_read_ram_*` facts). -/
theorem execReadRam (rk : read_kind) (addr : BitVec 64) (n : Nat) (w : BitVec (8 * n)) (s : ExecSt)
    (hrk : rk = .Read_plain ∨ rk = .Read_ifetch ∨ rk = .Read_ttw ∨ rk = .Read_RISCV_reserved ∨
      rk = .Read_RISCV_reserved_acquire)
    (hdev : devAddr addr = false) (hb : BytesAt s addr n w) :
    exec (read_ram rk (.Physaddr addr) n false) s = some ((w, default_meta), s) := by
  have hr : bmRead s.mem addr n = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  rcases hrk with rfl | rfl | rfl | rfl | rfl <;>
  · unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
    exec_run [hm, hr]

/-- Rocq `RiscvFetchExec.exec_read_ram_plain_4`. -/
theorem execReadRamPlain4 (addr : BitVec 64) (w : BitVec 32) (s : ExecSt) (hdev : devAddr addr = false)
    (hb : BytesAt s addr 4 w) : exec (read_ram .Read_plain (.Physaddr addr) 4 false) s = some ((w, default_meta), s) :=
  execReadRam _ addr 4 w s (Or.inl rfl) hdev hb
/-- Rocq `RiscvFetchExec.exec_read_ram_plain_2`. -/
theorem execReadRamPlain2 (addr : BitVec 64) (w : BitVec 16) (s : ExecSt) (hdev : devAddr addr = false)
    (hb : BytesAt s addr 2 w) : exec (read_ram .Read_plain (.Physaddr addr) 2 false) s = some ((w, default_meta), s) :=
  execReadRam _ addr 2 w s (Or.inl rfl) hdev hb
/-- Rocq `WpLoad.exec_read_ram_plain_8`. -/
theorem execReadRamPlain8 (addr : BitVec 64) (w : BitVec 64) (s : ExecSt) (hdev : devAddr addr = false)
    (hb : BytesAt s addr 8 w) : exec (read_ram .Read_plain (.Physaddr addr) 8 false) s = some ((w, default_meta), s) :=
  execReadRam _ addr 8 w s (Or.inl rfl) hdev hb
/-- Rocq `WpLoad.exec_read_ram_resv_8`. -/
theorem execReadRamResv8 (addr : BitVec 64) (w : BitVec 64) (s : ExecSt) (hdev : devAddr addr = false)
    (hb : BytesAt s addr 8 w) :
    exec (read_ram .Read_RISCV_reserved (.Physaddr addr) 8 false) s = some ((w, default_meta), s) :=
  execReadRam _ addr 8 w s (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hdev hb
/-- Rocq `WpAmo.exec_read_ram_resacq_4`. -/
theorem execReadRamResacq4 (addr : BitVec 64) (w : BitVec 32) (s : ExecSt) (hdev : devAddr addr = false)
    (hb : BytesAt s addr 4 w) :
    exec (read_ram .Read_RISCV_reserved_acquire (.Physaddr addr) 4 false) s = some ((w, default_meta), s) :=
  execReadRam _ addr 4 w s (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hdev hb

/-- A plain or conditional RAM write stores the bytes (the common core of the Rocq
`exec_write_ram_*` facts; deviation: the Lean answer is `.Ok (some true)`, so the
write reports `true` as in Rocq). -/
theorem execWriteRam (wk : write_kind) (addr : BitVec 64) (n : Nat) (data : BitVec (8 * n)) (s : ExecSt)
    (hwk : wk = .Write_plain ∨ wk = .Write_RISCV_conditional) (hdev : devAddr addr = false) :
    exec (write_ram wk (.Physaddr addr) n data ()) s = some (true, s.setMem (bmWrite s.mem addr n data)) := by
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  rcases hwk with rfl | rfl <;>
  · unfold write_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write PreSail.sail_mem_write
    exec_run [hm]

/-- Rocq `WpMmodeLeafBase.exec_write_ram_plain_8`. -/
theorem execWriteRamPlain8 (addr : BitVec 64) (data : BitVec 64) (s : ExecSt) (hdev : devAddr addr = false) :
    exec (write_ram .Write_plain (.Physaddr addr) 8 data ()) s =
      some (true, s.setMem (bmWrite s.mem addr 8 data)) :=
  execWriteRam _ addr 8 data s (Or.inl rfl) hdev
/-- Rocq `WpMmodeLeafBase.exec_write_ram_cond_8`. -/
theorem execWriteRamCond8 (addr : BitVec 64) (data : BitVec 64) (s : ExecSt) (hdev : devAddr addr = false) :
    exec (write_ram .Write_RISCV_conditional (.Physaddr addr) 8 data ()) s =
      some (true, s.setMem (bmWrite s.mem addr 8 data)) :=
  execWriteRam _ addr 8 data s (Or.inr rfl) hdev
/-- Rocq `WpAmo.exec_write_ram_cond_4`. -/
theorem execWriteRamCond4 (addr : BitVec 64) (data : BitVec 32) (s : ExecSt) (hdev : devAddr addr = false) :
    exec (write_ram .Write_RISCV_conditional (.Physaddr addr) 4 data ()) s =
      some (true, s.setMem (bmWrite s.mem addr 4 data)) :=
  execWriteRam _ addr 4 data s (Or.inr rfl) hdev

/-! ## 4. Small model leaves (Rocq `RiscvExtras`) -/

/-- Rocq `RiscvExtras.exec_split_misaligned_unsplit`. -/
theorem execSplitMisalignedUnsplit (addr : BitVec 64) (width g : Nat) (s : ExecSt) :
    exec (split_misaligned (.Physaddr addr) width g .CannotSplit) s = some (((1 : Int), (width : Int)), s) := rfl

/-- Rocq `RiscvExtras.exec_assert_exp'_true` (Lean's `assert`; the Rocq
`assert_exp'` returned a proof). -/
theorem execAssertExpTrue (msg : String) (s : ExecSt) : exec (assert true msg) s = some ((), s) := rfl

/-- Rocq `RiscvExtras.exec_is_mag_applicable_load_pte`. -/
theorem execIsMagApplicableLoadPte (width : Nat) (s : ExecSt) :
    exec (is_mag_applicable_access (.Load .PageTableEntry) width) s = some (false, s) := rfl
/-- Rocq `RiscvExtras.exec_is_mag_applicable_store_pte`. -/
theorem execIsMagApplicableStorePte (width : Nat) (s : ExecSt) :
    exec (is_mag_applicable_access (.Store .PageTableEntry) width) s = some (false, s) := rfl
/-- Rocq `RiscvExtras.exec_is_mag_applicable_store_data`. -/
theorem execIsMagApplicableStoreData (width : Nat) (s : ExecSt) :
    exec (is_mag_applicable_access (.Store .Data) width) s = some (width ≤b Functions.xlen_bytes, s) := rfl
/-- Rocq `RiscvExtras.exec_is_mag_applicable_load_data`. -/
theorem execIsMagApplicableLoadData (width : Nat) (s : ExecSt) :
    exec (is_mag_applicable_access (.Load .Data) width) s = some (width ≤b Functions.xlen_bytes, s) := rfl

/-- Rocq `RiscvExtras.exec_split_on_page_boundary_intra`. -/
theorem execSplitOnPageBoundaryIntra {n : Nat} (addr : BitVec n) (width : Nat) (s : ExecSt)
    (h : ((addr &&& Sail.BitVec.updateSubrange (ones (n := Sail.BitVec.length addr) : BitVec n) (Functions.pagesize_bits -i 1) 0
          (zeros (n := ((12 -i 1) -i (0 -i 1))))) ==
        ((BitVec.subInt (BitVec.addInt addr width) 1) &&& Sail.BitVec.updateSubrange
          (ones (n := Sail.BitVec.length addr) : BitVec n) (Functions.pagesize_bits -i 1) 0
          (zeros (n := ((12 -i 1) -i (0 -i 1)))))) = true) :
    exec (split_on_page_boundary addr width) s = some (((width : Int), (0 : Int)), s) := by
  unfold split_on_page_boundary
  simp only [h, ↓reduceIte, execReturnm]

/-- Rocq `RiscvExtras.vmem_width`. -/
def vmemWidth (w : Nat) : Prop := w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8

/-- An aligned virtual address is a multiple of the width. -/
theorem isAlignedVaddrMod (a : BitVec 64) (w : Nat) (hw : 0 < w)
    (ha : is_aligned_vaddr (.Virtaddr a) w = true) : a.toNat % w = 0 := by
  unfold is_aligned_vaddr at ha
  simp only [beq_iff_eq, BitVec.toNatInt, Int.ofNat_eq_natCast] at ha
  have : Int.tmod (a.toNat : Int) (w : Int) = ((a.toNat % w : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]; push_cast; rfl
  omega

/-- The page mask `split_on_page_boundary` builds at 64 bits. -/
theorem pageMask64 : (Sail.BitVec.updateSubrange (ones (n := Sail.BitVec.length (0#64))) (Functions.pagesize_bits -i 1) 0
    (zeros (n := ((12 -i 1) -i (0 -i 1))))) = 0xFFFFFFFFFFFFF000#64 := by decide +kernel

theorem andLowZero (a : BitVec 64) (k : Nat) (hk : k < 64) (h : a.toNat % 2 ^ k = 0) :
    a &&& BitVec.ofNat 64 (2 ^ k - 1) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h2 : (2 ^ k - 1) % 2 ^ 64 = 2 ^ k - 1 := by
    apply Nat.mod_eq_of_lt
    have : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [h2, Nat.and_two_pow_sub_one_eq_mod]
  simpa using h

/-- The program form of `execSplitOnPageBoundaryAligned`. -/
theorem splitOnPageBoundaryAlignedEq (a : BitVec 64) (w : Nat) (hw : vmemWidth w)
    (ha : is_aligned_vaddr (.Virtaddr a) w = true) :
    split_on_page_boundary a w = (pure ((w : Int), (0 : Int)) : SailM (Int × Int)) := by
  have h : ((a &&& Sail.BitVec.updateSubrange (ones (n := Sail.BitVec.length a) : BitVec 64)
        (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) ==
      ((BitVec.subInt (BitVec.addInt a w) 1) &&& Sail.BitVec.updateSubrange
        (ones (n := Sail.BitVec.length a) : BitVec 64) (Functions.pagesize_bits -i 1) 0
        (zeros (n := ((12 -i 1) -i (0 -i 1)))))) = true := by
    have hm := pageMask64
    simp only [Sail.BitVec.length] at hm ⊢
    rw [hm]
    simp only [Sail.BitVec.addInt, Sail.BitVec.subInt, beq_iff_eq]
    rcases hw with rfl | rfl | rfl | rfl
    · have : BitVec.ofInt 64 ((1 : Nat) : Int) = 1#64 := by decide
      rw [this]; bv_decide
    · have h := andLowZero a 1 (by decide) (isAlignedVaddrMod a 2 (by decide) ha)
      have : BitVec.ofInt 64 ((2 : Nat) : Int) = 2#64 := by decide
      rw [this]; simp only [Nat.reducePow, Nat.reduceSub] at h; bv_decide
    · have h := andLowZero a 2 (by decide) (isAlignedVaddrMod a 4 (by decide) ha)
      have : BitVec.ofInt 64 ((4 : Nat) : Int) = 4#64 := by decide
      rw [this]; simp only [Nat.reducePow, Nat.reduceSub] at h; bv_decide
    · have h := andLowZero a 3 (by decide) (isAlignedVaddrMod a 8 (by decide) ha)
      have : BitVec.ofInt 64 ((8 : Nat) : Int) = 8#64 := by decide
      rw [this]; simp only [Nat.reducePow, Nat.reduceSub] at h; bv_decide
  unfold split_on_page_boundary
  simp only [h, ↓reduceIte]

/-- Rocq `RiscvExtras.exec_split_on_page_boundary_aligned`. -/
theorem execSplitOnPageBoundaryAligned (a : BitVec 64) (w : Nat) (s : ExecSt) (hw : vmemWidth w)
    (ha : is_aligned_vaddr (.Virtaddr a) w = true) :
    exec (split_on_page_boundary a w) s = some (((w : Int), (0 : Int)), s) := by
  apply execSplitOnPageBoundaryIntra
  have hm := pageMask64
  simp only [Sail.BitVec.length] at hm ⊢
  rw [hm]
  simp only [Sail.BitVec.addInt, Sail.BitVec.subInt, beq_iff_eq]
  rcases hw with rfl | rfl | rfl | rfl
  · have : BitVec.ofInt 64 ((1 : Nat) : Int) = 1#64 := by decide
    rw [this]; bv_decide
  · have h := andLowZero a 1 (by decide) (isAlignedVaddrMod a 2 (by decide) ha)
    have : BitVec.ofInt 64 ((2 : Nat) : Int) = 2#64 := by decide
    rw [this]; simp only [Nat.reducePow, Nat.reduceSub] at h; bv_decide
  · have h := andLowZero a 2 (by decide) (isAlignedVaddrMod a 4 (by decide) ha)
    have : BitVec.ofInt 64 ((4 : Nat) : Int) = 4#64 := by decide
    rw [this]; simp only [Nat.reducePow, Nat.reduceSub] at h; bv_decide
  · have h := andLowZero a 3 (by decide) (isAlignedVaddrMod a 8 (by decide) ha)
    have : BitVec.ofInt 64 ((8 : Nat) : Int) = 8#64 := by decide
    rw [this]; simp only [Nat.reducePow, Nat.reduceSub] at h; bv_decide

/-! ## 5. Extension gates (Rocq `RiscvFetchExec`, `WpDecode`, `WpGprCsrwB`, `CommonWalk`,
`WpMmodeLeafBase`) -/

/-- Rocq `exec_hartSupports_Zca` (Lean's `hartSupports` is pure; ExecLib deviation 2). -/
theorem hartSupportsZca : hartSupports .Ext_Zca = true := by decide +kernel
/-- Rocq `WpDecode.exec_hartSupports_Zicfilp` -- FLIPPED 2026-11-04: the hart has no Zicfilp
(model/sail-config-rv64d.json, owner ruling [OWN.P9]); Rocq's was `true`. -/
theorem hartSupportsZicfilp : hartSupports .Ext_Zicfilp = false := by decide +kernel
/-- Rocq `WpGprCsrwB.exec_hartSupports_Sv48`. -/
theorem hartSupportsSv48 : hartSupports .Ext_Sv48 = true := by decide +kernel

/-- Rocq `WpDecode.exec_rec_cE_Zicsr_any` (Lean has no `_rec_currentlyEnabled`
fuel: the fact is about `currentlyEnabled` itself). -/
theorem execCurrentlyEnabledZicsr (s : ExecSt) : exec (currentlyEnabled .Ext_Zicsr) s = some (true, s) := by
  rw [currentlyEnabled]
  have : hartSupports .Ext_Zicsr = true := by decide +kernel
  simp only [this, execReturnm]

/-- Rocq `RiscvFetchExec.exec_rec_cE_C_misa` (on `currentlyEnabled`, no fuel). -/
theorem execCurrentlyEnabledC (s : ExecSt) :
    exec (currentlyEnabled .Ext_C) s = some (_get_Misa_C (s.regs .misa) == 1#1, s) := by
  rw [currentlyEnabled]
  have : hartSupports .Ext_C = true := by decide +kernel
  simp only [this, ↓reduceIte]
  exec_run

/-- Rocq `RiscvFetchExec.exec_currentlyEnabled_S`. -/
theorem execCurrentlyEnabledS (s : ExecSt) :
    exec (currentlyEnabled .Ext_S) s = some (_get_Misa_S (s.regs .misa) == 1#1, s) := by
  rw [currentlyEnabled]
  have : hartSupports .Ext_S = true := by decide +kernel
  simp only [this, ↓reduceIte]
  exec_run
  cases (_get_Misa_S (s.regs .misa) == 1#1)
  · rfl
  · simp only [↓reduceIte, execCurrentlyEnabledZicsr]

/-- Rocq `RiscvFetchExec.exec_currentlyEnabled_Zca`. -/
theorem execCurrentlyEnabledZca (s : ExecSt) (hc : (_get_Misa_C (s.regs .misa) == 1#1) = true) :
    exec (currentlyEnabled .Ext_Zca) s = some (true, s) := by
  rw [currentlyEnabled]
  simp only [hartSupportsZca, ↓reduceIte, execBind, execCurrentlyEnabledC, hc, Bool.true_or, execReturnm]

/-- Rocq `RiscvFetchExec.exec_currentlyEnabled_Ziccif`. -/
theorem execCurrentlyEnabledZiccif (s : ExecSt) : exec (currentlyEnabled .Ext_Ziccif) s = some (true, s) := by
  rw [currentlyEnabled]
  have : hartSupports .Ext_Ziccif = true := by decide +kernel
  simp only [this, execReturnm]

/-- Rocq `WpGprCsrwB.exec_currentlyEnabled_Svbare`. -/
theorem execCurrentlyEnabledSvbare (s : ExecSt) (h : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    exec (currentlyEnabled .Ext_Svbare) s = some (true, s) := by
  rw [currentlyEnabled, execCurrentlyEnabledS, h]

/-- The Sv39 gate under `S`. -/
theorem execCurrentlyEnabledSv39 (s : ExecSt) (h : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    exec (currentlyEnabled .Ext_Sv39) s = some (true, s) := by
  rw [currentlyEnabled]
  have : hartSupports .Ext_Sv39 = true := by decide +kernel
  simp only [this, ↓reduceIte, execCurrentlyEnabledS, h]

/-- Rocq `RiscvFetchExec.MISA_C`: the `misa` value of the platform. -/
def misaC : BitVec 64 := 0x8000000000141105#64

/-- Rocq `CommonWalk.exec_currentlyEnabled_Svnapot`. -/
theorem execCurrentlyEnabledSvnapot (s : ExecSt) (h : s.regs .misa = misaC) :
    exec (currentlyEnabled .Ext_Svnapot) s = some (true, s) := by
  rw [currentlyEnabled]
  have : hartSupports .Ext_Svnapot = true := by decide +kernel
  have hs : (_get_Misa_S (s.regs .misa) == 1#1) = true := by rw [h]; decide
  simp only [this, ↓reduceIte, execCurrentlyEnabledSv39 s hs]

/-- Rocq `CommonWalk.exec_currentlyEnabled_Svadu`. -/
theorem execCurrentlyEnabledSvadu (s : ExecSt) : exec (currentlyEnabled .Ext_Svadu) s = some (true, s) := by
  rw [currentlyEnabled]
  have : hartSupports .Ext_Svadu = true := by decide +kernel
  simp only [this, execReturnm]

/-- Rocq `WpMmodeLeafBase.exec_get_xLPE_S`. -/
theorem execGetXLPES (s : ExecSt) (h : _get_MEnvcfg_LPE (s.regs .menvcfg) = 0#1) :
    exec (get_xLPE .Supervisor) s = some (false, s) := by
  unfold get_xLPE
  exec_run [h]
  rfl

/-- Rocq `WpMmodeLeafBase.exec_cE_zicfilp_false`. -/
theorem execCEZicfilpFalse (s : ExecSt) (hcp : s.regs .cur_privilege = .Machine)
    (hm : bool_bit_backwards (_get_Seccfg_MLPE (s.regs .mseccfg)) = false) :
    exec (currentlyEnabled .Ext_Zicfilp) s = some (false, s) := by
  -- (since 2026-11-04 the gate is `false` without reading anything; `hcp`/`hm` are no longer needed)
  rw [currentlyEnabled]
  simp only [execBind, execCurrentlyEnabledZicsr, ↓reduceIte, hartSupportsZicfilp, Bool.false_eq_true]
  rfl

/-! ## 6. lean-sail's integer-range loops under `execR` (Rocq `RiscvTryStep`'s
`execR_foreach_ZM_up'_*`) -/

/-- Rocq `RiscvTryStep.execR_foreach_ZM_up'_allow` (Lean's loops are lean-sail's
`IntRange` `forIn`, step 1): a unit-state loop whose every iteration yields or
returns `r` early, without moving the state, either finishes or returns `r`. -/
theorem execRForInAllow {R : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s : ExecSt) (r : R)
    (hf : ∀ i, i ∈ range → execR (f i ()) s = some (.inr (.yield ()), s) ∨
      execR (f i ()) s = some (.inl r, s)) :
    execR (forIn range () f) s = some (.inr (), s) ∨ execR (forIn range () f) s = some (.inl r, s) := by
  show execR (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _ ∨
    execR (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0),
      (range.stop - i + 1).toNat = n →
      execR (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inr (), s) ∨
      execR (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inl r, s) from
    H _ _ _ rfl
  intro n
  induction n with
  | zero =>
    intro i hs hn
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    exact Or.inl rfl
  | succ n ih =>
    intro i hs hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      rw [execRBind]
      rcases hf i h with e | e
      · rw [e]
        have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
          simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
          rw [hstep]
          omega
        exact ih _ _ hn'
      · rw [e]; exact Or.inr rfl
    · simp only [dif_neg h]
      exact Or.inl rfl

/-- Rocq `RiscvTryStep.execR_foreach_ZM_up'_const`: a loop whose every
iteration yields without moving the state finishes. -/
theorem execRForInConst {R : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s : ExecSt)
    (hf : ∀ i, i ∈ range → execR (f i ()) s = some (.inr (.yield ()), s)) :
    execR (forIn range () f) s = some (.inr (), s) := by
  show execR (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0),
      (range.stop - i + 1).toNat = n →
      execR (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inr (), s) from
    H _ _ _ rfl
  intro n
  induction n with
  | zero =>
    intro i hs hn
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    rfl
  | succ n ih =>
    intro i hs hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      rw [execRBind, hf i h]
      have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
        simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
        rw [hstep]
        omega
      exact ih _ _ hn'
    · simp only [dif_neg h]
      rfl

/-- A loop whose first iteration returns early returns (Rocq's
`unroll_foreach_ZM_up'` + `execR_bind` step of `exec_pmpCheck_machine_tor0`). -/
theorem execRForInFirstEarly {R : Type} (range : IntRange) (f : Int → Unit → SailME R (ForInStep Unit))
    (s s' : ExecSt) (r : R) (h0 : range.start ∈ range)
    (hf : execR (f range.start ()) s = some (.inl r, s')) :
    execR (forIn range () f) s = some (.inl r, s') := by
  show execR (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _
  rw [IntRange.loop_unfold]
  simp only [dif_pos h0]
  rw [execRBind, hf]

end Weak
