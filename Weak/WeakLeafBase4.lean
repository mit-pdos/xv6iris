/-
Weak: **M4 batch 1, the WIDTH-4 M-mode LOAD/STORE shape, SC and at `execEff`** --
the `lw`/`lwu`/`sw` (and `c.lw`/`c.sw`/`c.lwsp`/`c.swsp`, which decode to
`LOAD … 4` / `STORE … 4`) twins of the width-8 chains of `Weak/ExecSC8.lean`,
`Weak/WeakLeafEff8.lean` and `Weak/WeakLeafEff8s.lean`.

Rocq: `iris/WeakLeafBase4.v` @ xxvzwolszwmp.

The Rocq header, in substance.
* HALF A is a NEW SC library, the width-4 twin of the 8-byte chain: `pmaCheck`,
  `checked_mem_read`/`checked_mem_write`, `mem_read`/`mem_write_ea`/`mem_write_value`,
  `vmem_read_addr`/`vmem_write_addr`, `vmem_read`/`vmem_write` and the two headline
  lemmas `execExecuteLOAD4Gpr` / `execExecuteSTORE4Gpr`.  Width-independent leaves are
  reused (`ExecSC2/3/4`: `execReadRamPlain4`, `execCheckedMemReadRam`,
  `execCheckedMemWriteRam`, `execMemWriteEaRam`, `execMemWriteValueRam`,
  `execPmpCheckMachineNone`, the effective-privilege / identity-translation /
  address-transform leaves).  What is width-DEPENDENT is stated afresh: the alignment
  premise, and the cast identities (`data2Id4`, `autocastSubrangeId4`).  The
  ASYMMETRY: at width 8 the STORE's `subrange rs2 63 0` is the whole register; at
  width 4 it is a genuine truncation, so the stored value is
  `Sail.BitVec.extractLsb (s.gpr rs2) 31 0`.  The LOAD's result is
  `extend_value u v` with `u` the `is_unsigned` bit (`lw` and `lwu` alike).
* HALF B is the `execEff` mirror: each `execute`'s trace is exactly ONE element,
  `[.WEread ⟨false, false, false⟩ pa 4]` (LOAD) / `[.WEwrite ⟨false, false, false⟩ pa 4 v]`
  (STORE) -- `Read_plain`/`Write_plain` classify to `AkInfo false false false`.
  Everything else is register-only and carries the EMPTY trace, established by
  replaying the SC proofs at `execEff` (not by `WeakEff.execEffQuietOfEmpty`, which
  only gives `quietTrace`; the certificates need `nowriteTrace`).
* Two premises are hypotheses in HALF B, in `execEff` form with the empty trace: the
  M-mode `pmpCheck` reduction and the three `within_*` MMIO-window probes.  HALF A
  keeps the SC forms (all-`OFF` PMP entries, `exec (within_* …) s = some (false, s)`).

Conventions: as `Weak/ExecSC*.lean` and `Weak/WeakLeafEffCommon.lean` (GPRs `s.gpr i`
/ `s.setGpr i v`; `register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1"` ↦
`(x == 1#1)`; `vec_access_dec v i` ↦ `v[i]!`; `dev_addr pa = false` ↦ `devAddr pa = false`;
the byte window ↦ `BytesAt s pa 4 w`; `MState s.(sregs) (write_bytes s.(mem) pa 4 v)
s.(mdev)` ↦ `s.setMem (bmWrite s.mem pa 4 v)`; `AkInfo false false false` ↦
`⟨false, false, false⟩`; `mword n`/`bv n` ↦ `BitVec n`; `tt` ↦ `()`).

**Deviations from Rocq.**
1. Section `Let`s are inlined, as in `ExecSC8` (its deviation 2): Rocq's
   `pa := zero_extend' 64 (add_vec_int a (0 * 4))` is `a`; Rocq's `ea`, `a4`, `pa` of
   the `*Gpr` sections are all `s.gpr rs1 + offset` (`offset := sign_extend' 64 imm` ↦
   `sign_extend (m := 64) imm`); Rocq's `data2` (the full-width update of the zero
   accumulator) is the read value `v` (the identity being `data2Id4`); Rocq's `vw4` is
   `Sail.BitVec.extractLsb (s.gpr rs2) 31 0`.  Section hypotheses are theorem premises
   in Rocq's order (flat, not bundled as `ExecSC8.MemM8`).
2. `exec_execute_LOAD_4_gpr` and its eff twin: the result state is
   `s.setGpr rd (extend_value u v)` (equal to Rocq's plain `set_reg` under the kept
   premise `rd.toNat ≠ 0`, the ExecSC convention).
3. `data2_id_4` is stated on the Lean spelling
   `Sail.BitVec.updateSubrange (zeros (n := 32)) (8*(0+1)*4-1) (8*0*4) v = v`;
   `autocast_subrange_id_4` on the shape the Lean `execute_STORE` produces
   (`BitVec.setWidth (8*4) (extractLsb d ((4:Int)*8-1).toNat 0) = extractLsb d 31 0`).
4. The model's access width is used in TYPES, so the aligned no-split arms of
   `vmem_read_addr`/`vmem_write_addr` are the Lean-only `execVmemReadAddrAligned4`,
   `execVmemWriteAddrAligned4`, `execEffVmemReadAddrAligned4` (twins of the `*8` ones of
   `ExecSC8`/`WeakLeafEff8`), with the Lean-only cast facts `uszFull4` (Rocq
   `usvd_zeros_full_32`) and `extractFull4` (Rocq `subrange_full_32`).  The effective
   address of `get_transformed_data_addr` (Rocq's inline `Hgta`) is proved inline.
5. The proofs are not bind-by-bind replays: as in `WeakLeafEff8`/`WeakLeafEff8s`
   (their deviations 4 / 1) each is a `simp` peel (`exec_run`/`exec_mem` for SC,
   `exec_eff_run`/`exec_eff_mem`/`eff8s_run`/`eff8s_mem` for `execEff`), and the SC
   memory leaves are instances of `ExecSC4`'s generic one-piece lemmas.
6. Rocq's `Local` lemmas are ported as ordinary theorems.  Rocq's `Print Assumptions`
   commands are not declarations.

**Rocq → Lean name map.**  `avi0_mul4` `WeakLeafBase4.avi0Mul4` (duplicated name),
`exec_split_on_page_boundary_aligned4` `execSplitOnPageBoundaryAligned4`,
`exec_eff_split_on_page_boundary_aligned4` `execEffSplitOnPageBoundaryAligned4`,
`exec_pmaCheck_ram_load_4` `execPmaCheckRamLoad4`, `exec_checked_mem_read_ram_load_4`
`execCheckedMemReadRamLoad4`, `exec_mem_read_load_4` `execMemReadLoad4`,
`exec_vmem_read_addr_4` `execVmemReadAddr4`, `exec_vmem_read_4_gpr` `execVmemRead4Gpr`,
`data2_id_4` `data2Id4`, `exec_execute_LOAD_4_gpr` `execExecuteLOAD4Gpr`,
`exec_write_ram_plain_4` `execWriteRamPlain4`, `exec_pmaCheck_ram_store_4`
`execPmaCheckRamStore4`, `exec_checked_mem_write_ram_store_4` `execCheckedMemWriteRamStore4`,
`exec_mem_write_ea_4` `execMemWriteEa4`, `exec_mem_write_value_4` `execMemWriteValue4`,
`exec_vmem_write_addr_4` `execVmemWriteAddr4`, `exec_vmem_write_4_gpr` `execVmemWrite4Gpr`,
`autocast_subrange_id_4` `autocastSubrangeId4`, `exec_execute_STORE_4_gpr`
`execExecuteSTORE4Gpr`, `exec_eff_read_ram_plain_4` `WeakLeafBase4.execEffReadRamPlain4`
(duplicated name), `exec_eff_pmaCheck_ram_load_4` `execEffPmaCheckRamLoad4`,
`exec_eff_checked_mem_read_ram_load_4` `execEffCheckedMemReadRamLoad4`,
`exec_eff_mem_read_load_4` `execEffMemReadLoad4`, `exec_eff_vmem_read_addr_4`
`execEffVmemReadAddr4`, `exec_eff_vmem_read_4_gpr` `execEffVmemRead4Gpr`,
`exec_eff_execute_LOAD_4_gpr` `execEffExecuteLOAD4Gpr`, `exec_eff_write_ram_plain_4`
`execEffWriteRamPlain4`, `exec_eff_pmaCheck_ram_store_4` `execEffPmaCheckRamStore4`,
`exec_eff_checked_mem_write_ram_store_4` `execEffCheckedMemWriteRamStore4`,
`exec_eff_mem_write_ea_4` `execEffMemWriteEa4`, `exec_eff_mem_write_value_4`
`execEffMemWriteValue4`, `exec_eff_vmem_write_addr_4` `execEffVmemWriteAddr4`,
`exec_eff_vmem_write_4_gpr` `execEffVmemWrite4Gpr`, `exec_eff_execute_STORE_4_gpr`
`execEffExecuteSTORE4Gpr`.  Section `Let`s: inlined (deviation 1).  Lean-only:
`uszFull4`, `extractFull4`, `execVmemReadAddrAligned4`, `execVmemWriteAddrAligned4`,
`execEffVmemReadAddrAligned4`.

**Dropped:** nothing (34 Rocq `Lemma`s, 3 of them `Local`; 34 Lean theorems plus the
5 Lean-only items).
-/
import Weak.WeakLeafEff8
import Weak.WeakLeafEff8s

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 0. The split-loop address and the page split at width 4 -/

/-- Rocq `avi0_mul4` (a Rocq `Local` restatement): the single split's address. -/
theorem WeakLeafBase4.avi0Mul4 (a : BitVec 64) : Sail.BitVec.addInt a (0 * 4) = a := by
  simp [Sail.BitVec.addInt]

/-- Rocq `exec_split_on_page_boundary_aligned4` (Rocq `Local`). -/
theorem execSplitOnPageBoundaryAligned4 (a : BitVec 64) (s : ExecSt)
    (ha : is_aligned_vaddr (.Virtaddr a) 4 = true) :
    exec (split_on_page_boundary a 4) s = some ((((4 : Nat) : Int), (0 : Int)), s) :=
  execSplitOnPageBoundaryAligned a 4 s (by simp [vmemWidth]) ha

/-- Rocq `exec_eff_split_on_page_boundary_aligned4` (Rocq `Local`). -/
theorem execEffSplitOnPageBoundaryAligned4 (a : BitVec 64) (s : ExecSt)
    (ha : is_aligned_vaddr (.Virtaddr a) 4 = true) :
    execEff (split_on_page_boundary a 4) s = some ((((4 : Nat) : Int), (0 : Int)), s, []) :=
  execEffSplitOnPageBoundaryAligned a 4 s (by simp [vmemWidth]) ha

/-! ## HALF A(i): the width-4 LOAD chain (SC) -/

/-- Rocq `exec_pmaCheck_ram_load_4`. -/
theorem execPmaCheckRamLoad4 (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true) :
    exec (pmaCheck (.Physaddr addr) 4 (.Load .Data) pbmt false) s = some (.Ok pmaOkAligned, s) :=
  execPmaCheckRamLoadG 4 addr pbmt region s hm hal hr

/-- Rocq `exec_checked_mem_read_ram_load_4`. -/
theorem execCheckedMemReadRamLoad4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt)
    (hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    exec (checked_mem_read (.Load .Data) pbmt .Machine (.Physaddr addr) 4 false false false false) s =
      some (.Ok (w, default_meta), s) :=
  execCheckedMemReadRam (.Load .Data) pbmt .Machine addr 4 false false false .Read_plain w s
    (by simp [vmemWidth]) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    (execPmaCheckRamLoad4 addr pbmt region s hm hal hr)
    (execPmpCheckMachineNone _ 4 _ s hpmp) (execWithinMmioReadableFalse addr 4 s hc hsig hh)
    (execReadRamPlain4 addr w s hdev hb)

/-- Rocq `exec_mem_read_load_4`. -/
theorem execMemReadLoad4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (m : BitVec 64) (s : ExecSt)
    (hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) (hms : s.regs .mstatus = m)
    (hmprv : (_get_Mstatus_MPRV m == 1#1) = false) (hpriv : s.regs .cur_privilege = .Machine) :
    exec (mem_read (.Load .Data) pbmt (.Physaddr addr) 4 false false false) s = some (.Ok w, s) := by
  have hck := execCheckedMemReadRamLoad4 pbmt addr region w s hpmp hm hal hr hc hsig hh hdev hb
  have hep : exec (effectivePrivilege (.Load .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s) := by rw [hpriv, hms]; exact execEffectivePrivilegeLoad _ s hmprv
  unfold mem_read
  exec_run [hep, execMemReadPriv _ _ _ _ _ _ _ _ w s (by decide) hck]
  simp only [Nat.reduceMul, BitVec.setWidth_eq]

/-- The full-width accumulator write of a 4-byte access (Lean-only; the twin of
`ExecSC8.uszFull8`, and the content of Rocq `usvd_zeros_full_32`). -/
theorem uszFull4 (w : BitVec 32) :
    (Sail.BitVec.updateSubrange (zeros (n := (8 * ((4 : Nat) : Int)).toNat)) (8 * ((4 : Nat) : Int) - 1).toNat 0
      (BitVec.setWidth ((8 * ((4 : Nat) : Int) - 1).toNat - 0 + 1) w) : BitVec 32) = w := by
  show Sail.BitVec.updateSubrange (zeros (n := 32)) 31 0 (BitVec.setWidth 32 w) = w
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.setWidth_eq, zeros]
  bv_decide

set_option simprocs false in
/-- An aligned 4-byte in-page read: no split, one translation, one physical read
(Lean-only; the width-4 twin of `ExecSC8.execVmemReadAddrAligned8`). -/
theorem execVmemReadAddrAligned4 (va pa : BitVec 64) (acc : MemoryAccessType mem_payload)
    (aq rl : Bool) (p : Privilege) (mode : SATPMode) (pbmt : page_based_mem_type) (w : BitVec 32)
    (s s1 : ExecSt) (hal : is_aligned_vaddr (.Virtaddr va) 4 = true)
    (hep : exec (effectivePrivilege acc (s.regs .mstatus) (s.regs .cur_privilege)) s = some (p, s))
    (hmode : exec (translationMode p) s = some (mode, s))
    (htr : exec (translateAddr (.Virtaddr va) acc) s = some (.Ok (.Physaddr pa, pbmt, ()), s1))
    (hmr : exec (mem_read acc pbmt (.Physaddr pa) 4 aq rl false) s1 = some (.Ok w, s1)) :
    exec (vmem_read_addr (.Virtaddr va) 4 acc aq rl false) s = some (.Ok w, s1) := by
  have hsp := splitOnPageBoundaryAlignedEq va 4 (by simp [vmemWidth]) hal
  cases mode <;>
  · unfold vmem_read_addr translate_and_read_value
    simp only [bits_of_virtaddr, hsp, pure_bind]
    rw [execCatchEarlyReturn]
    exec_run [hal, Functions.not, hep, hmode, htr]
    dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57, Int.toNat_natCast]
    exec_run [hmr]
    exact congrArg (fun x => some (Result.Ok x, s1)) (uszFull4 w)

/-- Rocq `exec_vmem_read_addr_4` (section `S4`; Rocq's `pa` is `a`). -/
theorem execVmemReadAddr4 (a : BitVec 64) (v : BitVec 32) (region : PMA_Region) (s : ExecSt)
    (halign : is_aligned_vaddr (.Virtaddr a) 4 = true)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr a) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr a) 4 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : exec (within_clint (.Physaddr a) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr a) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr a) 4) s = some (false, s))
    (hdev : devAddr a = false) (hb : BytesAt s a 4 v) :
    exec (vmem_read_addr (.Virtaddr a) 4 (.Load .Data) false false false) s = some (.Ok v, s) := by
  have htr := execTranslateAddrIdentityLoad a s hpriv hmprv
  rw [translateIdentityEq] at htr
  have hep : exec (effectivePrivilege (.Load .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s) := by rw [hpriv]; exact execEffectivePrivilegeLoad _ s hmprv
  exact execVmemReadAddrAligned4 a a _ false false .Machine .Bare .PBMT_PMA v s s halign hep
    (execTranslationModeM s) htr
    (execMemReadLoad4 .PBMT_PMA a region v _ s hpmp hmatch hpalign hread hc hsig hh hdev hb rfl hmprv hpriv)

/-- Rocq `exec_vmem_read_4_gpr` (section `VRg4`; Rocq's `ea`, `a4`, `pa` are
`s.gpr rs1 + offset`, Rocq's `data2` is `v`). -/
theorem execVmemRead4Gpr (rs1 : BitVec 5) (offset : BitVec 64) (v : BitVec 32) (region : PMA_Region)
    (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + offset)) 4 = true)
    (hpmp : ∀ j : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[j]!) = .OFF)
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + offset)) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + offset)) 4 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : exec (within_clint (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s))
    (hdev : devAddr (s.gpr rs1 + offset) = false) (hb : BytesAt s (s.gpr rs1 + offset) 4 v) :
    exec (vmem_read (.Regidx rs1) offset 4 (.Load .Data) false false false) s = some (.Ok v, s) := by
  have hgta : exec (get_transformed_data_addr (.Regidx rs1) offset (.Load .Data) 4) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s) := by
    unfold get_transformed_data_addr
    exec_run [execExtDataGetAddrGpr, execTransformEffectiveAddressLoad _ s hcp hmprv hpmm, pmTransformPA0]
  unfold vmem_read
  rw [execCatchEarlyReturn]
  exec_run [hgta, execVmemReadAddr4 _ v region s halign hcp hmprv hpmp hmatch hpalign hread hc hsig hh hdev hb]

/-- Rocq `data2_id_4`: writing all 32 bits of `v` into a zero word is the identity. -/
theorem data2Id4 (v : BitVec 32) :
    (Sail.BitVec.updateSubrange (zeros (n := 32)) (8 * (0 + 1) * 4 - 1) (8 * 0 * 4) v : BitVec 32) = v := by
  show Sail.BitVec.updateSubrange (zeros (n := 32)) 31 0 v = v
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  bv_decide

/-- Rocq `exec_execute_LOAD_4_gpr` (section `ExecLoadG4`): `lw` and `lwu` alike
(the `is_unsigned` bit `u` is free); the result is `s.setGpr rd (extend_value u v)`. -/
theorem execExecuteLOAD4Gpr (rs1 rd : BitVec 5) (imm : BitVec 12) (u : Bool) (v : BitVec 32)
    (region : PMA_Region) (s : ExecSt) (_hrd : rd.toNat ≠ 0)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = true)
    (hpmp : ∀ j : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[j]!) = .OFF)
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 =
      some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : exec (within_clint (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s = some (false, s))
    (hdev : devAddr (s.gpr rs1 + sign_extend (m := 64) imm) = false)
    (hb : BytesAt s (s.gpr rs1 + sign_extend (m := 64) imm) 4 v) :
    exec (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (extend_value u v)) := by
  show exec (execute_LOAD imm (.Regidx rs1) (.Regidx rd) u 4) s = _
  unfold execute_LOAD
  exec_run [execVmemRead4Gpr rs1 _ v region s hcp hmprv hpmm halign hpmp hmatch hpalign hread hc hsig hh hdev hb,
    execWXBitsGpr]

/-! ## HALF A(ii): the width-4 STORE chain (SC) -/

/-- Rocq `exec_write_ram_plain_4`. -/
theorem execWriteRamPlain4 (addr : BitVec 64) (data : BitVec 32) (s : ExecSt) (hdev : devAddr addr = false) :
    exec (write_ram .Write_plain (.Physaddr addr) 4 data ()) s =
      some (true, s.setMem (bmWrite s.mem addr 4 data)) :=
  execWriteRam _ addr 4 data s (Or.inl rfl) hdev

/-- Rocq `exec_pmaCheck_ram_store_4`. -/
theorem execPmaCheckRamStore4 (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true) :
    exec (pmaCheck (.Physaddr addr) 4 (.Store .Data) pbmt false) s = some (.Ok pmaOkAligned, s) :=
  execPmaCheckRamStoreG 4 addr pbmt region s hm hal hw

/-- Rocq `exec_checked_mem_write_ram_store_4`. -/
theorem execCheckedMemWriteRamStore4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 32) (s : ExecSt)
    (hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) :
    exec (checked_mem_write (.Physaddr addr) 4 data (.Store .Data) pbmt .Machine () false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 4 data)) :=
  execCheckedMemWriteRam _ pbmt _ addr 4 data false false false .Write_plain s (by simp [vmemWidth])
    (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (execPmaCheckRamStore4 addr pbmt region s hm hal hw)
    (execPmpCheckMachineNone _ 4 _ s hpmp) (execWithinMmioWritableFalse addr 4 s hc hsig hh) hdev

/-- Rocq `exec_mem_write_ea_4`. -/
theorem execMemWriteEa4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    exec (mem_write_ea (.Physaddr addr) 4 (.Store .Data) pbmt false false false) s = some (.Ok (), s) :=
  execMemWriteEaRam _ pbmt .Machine addr 4 false false false s (by simp [vmemWidth]) ⟨_, rfl⟩
    (by rw [hcp]; exact execEffectivePrivilegeStore _ s hmprv)
    (execPmaCheckRamStore4 addr pbmt region s hm hal hw) (execPmpCheckMachineNone _ 4 _ s hpmp)

/-- Rocq `exec_mem_write_value_4`. -/
theorem execMemWriteValue4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 32) (m : BitVec 64) (s : ExecSt)
    (hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    exec (mem_write_value (.Physaddr addr) 4 data (.Store .Data) pbmt false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 4 data)) :=
  execMemWriteValueRam _ pbmt .Machine addr 4 data false false false s
    (by rw [hcp, hms]; exact execEffectivePrivilegeStore _ s hmprv)
    (execCheckedMemWriteRamStore4 pbmt addr region data s hpmp hm hal hw hc hsig hh hdev)

/-- The full-width extraction of a 4-byte store's data (Lean-only; Rocq `subrange_full_32`). -/
theorem extractFull4 (data : BitVec 32) :
    (BitVec.setWidth (8 * 4) (Sail.BitVec.extractLsb data (8 * ((4 : Nat) : Int) - 1).toNat 0) : BitVec 32) =
      data := by
  show BitVec.setWidth 32 (Sail.BitVec.extractLsb data 31 0) = data
  simp only [Sail.BitVec.extractLsb]
  bv_decide

set_option simprocs false in
/-- An aligned 4-byte in-page write of a non-conditional store (Lean-only; the width-4
twin of `ExecSC8.execVmemWriteAddrAligned8`). -/
theorem execVmemWriteAddrAligned4 (va pa : BitVec 64) (data : BitVec 32) (acc : MemoryAccessType mem_payload)
    (aq rl : Bool) (p : Privilege) (mode : SATPMode) (pbmt : page_based_mem_type) (s s1 s2 : ExecSt)
    (hal : is_aligned_vaddr (.Virtaddr va) 4 = true) (hsc : is_store_conditional acc = false)
    (hep : exec (effectivePrivilege acc (s.regs .mstatus) (s.regs .cur_privilege)) s = some (p, s))
    (hmode : exec (translationMode p) s = some (mode, s))
    (htr : exec (translateAddr (.Virtaddr va) acc) s = some (.Ok (.Physaddr pa, pbmt, ()), s1))
    (hea : exec (mem_write_ea (.Physaddr pa) 4 acc pbmt aq rl false) s1 = some (.Ok (), s1))
    (hwv : ∀ d : BitVec 32, d = data →
      exec (mem_write_value (.Physaddr pa) 4 d acc pbmt aq rl false) s1 = some (.Ok true, s2)) :
    exec (vmem_write_addr (.Virtaddr va) 4 data acc aq rl false) s = some (.Ok true, s2) := by
  have hsp := splitOnPageBoundaryAlignedEq va 4 (by simp [vmemWidth]) hal
  have hsc' : (false == is_store_conditional acc) = true := by rw [hsc]; rfl
  cases mode <;>
  · unfold vmem_write_addr
    simp only [bits_of_virtaddr, hsp, pure_bind]
    rw [execCatchEarlyReturn]
    exec_run [hal, Functions.not, hep, hmode, htr, hsc']
    dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57, Int.toNat_natCast]
    exec_run [hea]
    rw [hwv _ (extractFull4 data)]
    rfl

/-- Rocq `exec_vmem_write_addr_4` (section `SW4`; Rocq's `pa` is `a`). -/
theorem execVmemWriteAddr4 (a : BitVec 64) (data : BitVec 32) (region : PMA_Region) (s : ExecSt)
    (halign : is_aligned_vaddr (.Virtaddr a) 4 = true)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr a) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr a) 4 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : exec (within_clint (.Physaddr a) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr a) 4) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr a) 4) s = some (false, s))
    (hdev : devAddr a = false) :
    exec (vmem_write_addr (.Virtaddr a) 4 data (.Store .Data) false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem a 4 data)) := by
  have htr := execTranslateAddrIdentityStore a s hpriv hmprv
  rw [translateIdentityEq] at htr
  have hep : exec (effectivePrivilege (.Store .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s) := by rw [hpriv]; exact execEffectivePrivilegeStore _ s hmprv
  exact execVmemWriteAddrAligned4 a a data _ false false .Machine .Bare .PBMT_PMA s s _ halign rfl hep
    (execTranslationModeM s) htr
    (execMemWriteEa4 .PBMT_PMA a region s hpmp hmatch hpalign hwrite hpriv hmprv)
    (fun d hd => by
      subst hd
      exact execMemWriteValue4 .PBMT_PMA a region d _ s hpmp hmatch hpalign hwrite hc hsig hh hdev
        rfl hmprv hpriv)

/-- Rocq `exec_vmem_write_4_gpr` (section `VWg4`; Rocq's `ea`, `a4`, `pa` are
`s.gpr rs1 + offset`). -/
theorem execVmemWrite4Gpr (rs1 : BitVec 5) (offset : BitVec 64) (data : BitVec 32) (region : PMA_Region)
    (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + offset)) 4 = true)
    (hpmp : ∀ j : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[j]!) = .OFF)
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + offset)) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + offset)) 4 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : exec (within_clint (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s))
    (hdev : devAddr (s.gpr rs1 + offset) = false) :
    exec (vmem_write (.Regidx rs1) offset 4 data (.Store .Data) false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem (s.gpr rs1 + offset) 4 data)) := by
  have hgta : exec (get_transformed_data_addr (.Regidx rs1) offset (.Store .Data) 4) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s) := by
    unfold get_transformed_data_addr
    exec_run [execExtDataGetAddrGpr, execTransformEffectiveAddressStore _ s hcp hmprv hpmm, pmTransformPA0]
  unfold vmem_write
  rw [execCatchEarlyReturn]
  exec_run [hgta, execVmemWriteAddr4 _ data region s halign hcp hmprv hpmp hmatch hpalign hwrite hc hsig hh hdev]

/-- Rocq `autocast_subrange_id_4`: at width 4 the store's `subrange` is a genuine
truncation, so all that is stripped is the width cast. -/
theorem autocastSubrangeId4 (d : BitVec 64) :
    (BitVec.setWidth (8 * 4) (Sail.BitVec.extractLsb d (((4 : Nat) : Int) * 8 - 1).toNat 0) : BitVec 32) =
      (Sail.BitVec.extractLsb d 31 0 : BitVec 32) := by
  show BitVec.setWidth 32 (Sail.BitVec.extractLsb d 31 0) = _
  exact BitVec.setWidth_eq _

/-- Rocq `exec_execute_STORE_4_gpr` (section `ExecStoreG4`; Rocq's `vw4` is
`Sail.BitVec.extractLsb (s.gpr rs2) 31 0`). -/
theorem execExecuteSTORE4Gpr (rs2 rs1 : BitVec 5) (imm : BitVec 12) (region : PMA_Region) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = true)
    (hpmp : ∀ j : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[j]!) = .OFF)
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 =
      some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : exec (within_clint (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s = some (false, s))
    (hdev : devAddr (s.gpr rs1 + sign_extend (m := 64) imm) = false) :
    exec (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 4))) s =
      some (RETIRE_SUCCESS, s.setMem (bmWrite s.mem (s.gpr rs1 + sign_extend (m := 64) imm) 4
        (Sail.BitVec.extractLsb (s.gpr rs2) 31 0 : BitVec 32))) := by
  show exec (execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4) s = _
  unfold execute_STORE
  exec_run [execRXBitsGpr, autocastSubrangeId4,
    execVmemWrite4Gpr rs1 _ _ region s hcp hmprv hpmm halign hpmp hmatch hpalign hwrite hc hsig hh hdev]

/-! ## HALF B(i): the width-4 LOAD at `execEff` -/

/-- Rocq `exec_eff_read_ram_plain_4`: where the LOAD's one trace element is born. -/
theorem WeakLeafBase4.execEffReadRamPlain4 (addr : BitVec 64) (w : BitVec 32) (s : ExecSt)
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    execEff (read_ram .Read_plain (.Physaddr addr) 4 false) s =
      some ((w, default_meta), s, [.WEread ⟨false, false, false⟩ addr 4]) := by
  have hr : bmRead s.mem addr 4 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  exec_eff_run [hm, hr]
  rfl

/-- Rocq `exec_eff_pmaCheck_ram_load_4`. -/
theorem execEffPmaCheckRamLoad4 (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true) :
    execEff (pmaCheck (.Physaddr addr) 4 (.Load .Data) pbmt false) s = some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hr (execEffIsMagApplicableLoadData 4 s) hal

/-- Rocq `exec_eff_checked_mem_read_ram_load_4`. -/
theorem execEffCheckedMemReadRamLoad4 (pbmt : page_based_mem_type) (addr : BitVec 64)
    (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.Load .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    execEff (checked_mem_read (.Load .Data) pbmt .Machine (.Physaddr addr) 4 false false false false) s =
      some (.Ok (w, default_meta), s, [.WEread ⟨false, false, false⟩ addr 4]) := by
  have hpma := execEffPmaCheckRamLoad4 addr pbmt region s hm hal hr
  have hmm := execEffWithinMmioReadableFalse addr 4 s hc hsig hh
  have hrr := WeakLeafBase4.execEffReadRamPlain4 addr w s hdev hb
  unfold checked_mem_read check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  exec_eff_mem [hpma]
  exec_eff_mem [hpmp, hmm, hrr, read_kind_of_flags]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  congr
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  bv_decide

/-- Rocq `exec_eff_mem_read_load_4`. -/
theorem execEffMemReadLoad4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (m : BitVec 64) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.Load .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) (hms : s.regs .mstatus = m)
    (hmprv : (_get_Mstatus_MPRV m == 1#1) = false) (hpriv : s.regs .cur_privilege = .Machine) :
    execEff (mem_read (.Load .Data) pbmt (.Physaddr addr) 4 false false false) s =
      some (.Ok w, s, [.WEread ⟨false, false, false⟩ addr 4]) := by
  have hck := execEffCheckedMemReadRamLoad4 pbmt addr region w s hpmp hm hal hr hc hsig hh hdev hb
  unfold mem_read mem_read_priv mem_read_priv_meta
  exec_eff_run [hms, hpriv, execEffEffectivePrivilegeLoad m s hmprv, hck]
  rfl

set_option simprocs false in
/-- The `execEff` twin of `execVmemReadAddrAligned4` (Lean-only). -/
theorem execEffVmemReadAddrAligned4 (va pa : BitVec 64) (acc : MemoryAccessType mem_payload)
    (aq rl : Bool) (p : Privilege) (mode : SATPMode) (pbmt : page_based_mem_type) (w : BitVec 32)
    (s s1 : ExecSt) (es : List Weff) (hal : is_aligned_vaddr (.Virtaddr va) 4 = true)
    (hep : execEff (effectivePrivilege acc (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (p, s, []))
    (hmode : execEff (translationMode p) s = some (mode, s, []))
    (htr : execEff (translateAddr (.Virtaddr va) acc) s = some (.Ok (.Physaddr pa, pbmt, ()), s1, []))
    (hmr : execEff (mem_read acc pbmt (.Physaddr pa) 4 aq rl false) s1 = some (.Ok w, s1, es)) :
    execEff (vmem_read_addr (.Virtaddr va) 4 acc aq rl false) s = some (.Ok w, s1, es) := by
  have hsp := splitOnPageBoundaryAlignedEq va 4 (by simp [vmemWidth]) hal
  cases mode <;>
  · unfold vmem_read_addr translate_and_read_value
    simp only [bits_of_virtaddr, hsp, pure_bind]
    rw [execEffCatchEarlyReturn]
    exec_eff_run [hal, Functions.not, hep, hmode, htr]
    dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57,
      Int.toNat_natCast]
    exec_eff_run [hmr]
    exact congrArg (fun x => some (Result.Ok x, s1, es)) (uszFull4 w)

/-- Rocq `exec_eff_vmem_read_addr_4` (section `SEff4`; Rocq's `pa` is `a`). -/
theorem execEffVmemReadAddr4 (a : BitVec 64) (v : BitVec 32) (region : PMA_Region) (s : ExecSt)
    (halign : is_aligned_vaddr (.Virtaddr a) 4 = true)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmp : execEff (pmpCheck (.Physaddr a) 4 (.Load .Data) .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr a) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr a) 4 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : execEff (within_clint (.Physaddr a) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr a) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr a) 4) s = some (false, s, []))
    (hdev : devAddr a = false) (hb : BytesAt s a 4 v) :
    execEff (vmem_read_addr (.Virtaddr a) 4 (.Load .Data) false false false) s =
      some (.Ok v, s, [.WEread ⟨false, false, false⟩ a 4]) := by
  have htr := execEffTranslateAddrIdentityLoad a s hpriv hmprv
  rw [translateIdentityEq] at htr
  have hep : execEff (effectivePrivilege (.Load .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s, []) := by rw [hpriv]; exact execEffEffectivePrivilegeLoad _ s hmprv
  exact execEffVmemReadAddrAligned4 a a _ false false .Machine .Bare .PBMT_PMA v s s _ halign hep
    (execEffTranslationModeM s) htr
    (execEffMemReadLoad4 .PBMT_PMA a region v _ s hpmp hmatch hpalign hread hc hsig hh hdev hb rfl hmprv hpriv)

/-- Rocq `exec_eff_vmem_read_4_gpr` (section `VRgEff4`; Rocq's `ea`, `a4`, `pa` are
`s.gpr rs1 + offset`, Rocq's `data2` is `v`). -/
theorem execEffVmemRead4Gpr (rs1 : BitVec 5) (offset : BitVec 64) (v : BitVec 32) (region : PMA_Region)
    (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + offset)) 4 = true)
    (hpmp : execEff (pmpCheck (.Physaddr (s.gpr rs1 + offset)) 4 (.Load .Data) .Machine) s =
      some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + offset)) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + offset)) 4 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : execEff (within_clint (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s, []))
    (hdev : devAddr (s.gpr rs1 + offset) = false) (hb : BytesAt s (s.gpr rs1 + offset) 4 v) :
    execEff (vmem_read (.Regidx rs1) offset 4 (.Load .Data) false false false) s =
      some (.Ok v, s, [.WEread ⟨false, false, false⟩ (s.gpr rs1 + offset) 4]) := by
  have hgta : execEff (get_transformed_data_addr (.Regidx rs1) offset (.Load .Data) 4) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s, []) := by
    unfold get_transformed_data_addr
    exec_eff_run [execEffExtDataGetAddrGpr, execEffTransformEffectiveAddressLoad _ s hcp hmprv hpmm,
      pmTransformPA0]
  unfold vmem_read
  rw [execEffCatchEarlyReturn]
  exec_eff_run [hgta,
    execEffVmemReadAddr4 _ v region s halign hcp hmprv hpmp hmatch hpalign hread hc hsig hh hdev hb]

/-- Rocq `exec_eff_execute_LOAD_4_gpr` (section `ExecLoadGEff4`): the trace is the
ONE plain read; `u` is free (`lw` and `lwu`). -/
theorem execEffExecuteLOAD4Gpr (rs1 rd : BitVec 5) (imm : BitVec 12) (u : Bool) (v : BitVec 32)
    (region : PMA_Region) (s : ExecSt) (_hrd : rd.toNat ≠ 0)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = true)
    (hpmp : execEff (pmpCheck (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 (.Load .Data)
      .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 =
      some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hc : execEff (within_clint (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s =
      some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s =
      some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s =
      some (false, s, []))
    (hdev : devAddr (s.gpr rs1 + sign_extend (m := 64) imm) = false)
    (hb : BytesAt s (s.gpr rs1 + sign_extend (m := 64) imm) 4 v) :
    execEff (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (extend_value u v),
        [.WEread ⟨false, false, false⟩ (s.gpr rs1 + sign_extend (m := 64) imm) 4]) := by
  show execEff (execute_LOAD imm (.Regidx rs1) (.Regidx rd) u 4) s = _
  unfold execute_LOAD
  exec_eff_run [execEffVmemRead4Gpr rs1 _ v region s hcp hmprv hpmm halign hpmp hmatch hpalign hread hc hsig
    hh hdev hb, execEffWXBitsGpr]

/-! ## HALF B(ii): the width-4 STORE at `execEff` -/

/-- Rocq `exec_eff_write_ram_plain_4`: where the STORE's one trace element is born. -/
theorem execEffWriteRamPlain4 (addr : BitVec 64) (data : BitVec 32) (s : ExecSt)
    (hdev : devAddr addr = false) :
    execEff (write_ram .Write_plain (.Physaddr addr) 4 data ()) s =
      some (true, s.setMem (bmWrite s.mem addr 4 data), [.WEwrite ⟨false, false, false⟩ addr 4 data]) := by
  have hm : mmioAcc addr 4 = false := by simp [mmioAcc, hdev]
  unfold write_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write PreSail.sail_mem_write
  eff8s_run [hm, Weff.cons]
  rfl

/-- Rocq `exec_eff_pmaCheck_ram_store_4`. -/
theorem execEffPmaCheckRamStore4 (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true) :
    execEff (pmaCheck (.Physaddr addr) 4 (.Store .Data) pbmt false) s = some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hw (execEffIsMagApplicableStoreData 4 s) hal

/-- Rocq `exec_eff_checked_mem_write_ram_store_4`. -/
theorem execEffCheckedMemWriteRamStore4 (pbmt : page_based_mem_type) (addr : BitVec 64)
    (region : PMA_Region) (data : BitVec 32) (s : ExecSt)
    (hpmpEff : execEff (pmpCheck (.Physaddr addr) 4 (.Store .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) :
    execEff (checked_mem_write (.Physaddr addr) 4 data (.Store .Data) pbmt .Machine () false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 4 data), [.WEwrite ⟨false, false, false⟩ addr 4 data]) := by
  have hpma := execEffPmaCheckRamStore4 addr pbmt region s hm hal hw
  have hmm : execEff (within_mmio_writable (.Physaddr addr) 4) s = some (false, s, []) := by
    unfold within_mmio_writable
    eff8s_run [hc, hsig, hh]
  have hw1 : ∀ (d : BitVec (8 * 4)), execEff (write_ram .Write_plain (.Physaddr addr) 4 d ()) s =
      some (true, s.setMem (bmWrite s.mem addr 4 d), [.WEwrite ⟨false, false, false⟩ addr 4 d]) :=
    fun d => execEffWriteRamPlain4 addr d s hdev
  unfold checked_mem_write check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  eff8s_mem [hpma]
  eff8s_mem [hpmpEff, hmm, write_kind_of_flags, hw1]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  have hd : ∀ x : BitVec 32, Sail.BitVec.extractLsb x 31 0 = x := by
    intro x; simp only [Sail.BitVec.extractLsb]; bv_decide
  simp only [hd]

/-- Rocq `exec_eff_mem_write_ea_4`: the announcement, a state AND trace no-op. -/
theorem execEffMemWriteEa4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (s : ExecSt)
    (hpmpEff : execEff (pmpCheck (.Physaddr addr) 4 (.Store .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    execEff (mem_write_ea (.Physaddr addr) 4 (.Store .Data) pbmt false false false) s =
      some (.Ok (), s, []) := by
  have hpma := execEffPmaCheckRamStore4 addr pbmt region s hm hal hw
  have hep : execEff (effectivePrivilege (.Store .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s, []) := by rw [hcp]; exact execEffEffectivePrivilegeStore _ s hmprv
  unfold mem_write_ea check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  eff8s_mem [hep, hpma]
  eff8s_mem [write_kind_of_flags, hpmpEff]

/-- Rocq `exec_eff_mem_write_value_4`. -/
theorem execEffMemWriteValue4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 32) (m : BitVec 64) (s : ExecSt)
    (hpmpEff : execEff (pmpCheck (.Physaddr addr) 4 (.Store .Data) .Machine) s = some (none, s, []))
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hms : s.regs .mstatus = m)
    (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    execEff (mem_write_value (.Physaddr addr) 4 data (.Store .Data) pbmt false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 4 data), [.WEwrite ⟨false, false, false⟩ addr 4 data]) := by
  have hep : execEff (effectivePrivilege (.Store .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s, []) := by rw [hcp, hms]; exact execEffEffectivePrivilegeStore _ s hmprv
  have h := execEffCheckedMemWriteRamStore4 pbmt addr region data s hpmpEff hm hal hw hc hsig hh hdev
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  eff8s_run [hep, h]

set_option simprocs false in
/-- Rocq `exec_eff_vmem_write_addr_4` (section `SWeff4`; Rocq's `pa` is `a`). -/
theorem execEffVmemWriteAddr4 (a : BitVec 64) (data : BitVec 32) (region : PMA_Region) (s : ExecSt)
    (halign : is_aligned_vaddr (.Virtaddr a) 4 = true)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmpEff : execEff (pmpCheck (.Physaddr a) 4 (.Store .Data) .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr a) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr a) 4 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : execEff (within_clint (.Physaddr a) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr a) 4) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr a) 4) s = some (false, s, []))
    (hdev : devAddr a = false) :
    execEff (vmem_write_addr (.Virtaddr a) 4 data (.Store .Data) false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem a 4 data), [.WEwrite ⟨false, false, false⟩ a 4 data]) := by
  have hsp := splitOnPageBoundaryAlignedEq a 4 (by simp [vmemWidth]) halign
  have hsc' : (false == is_store_conditional (.Store .Data : MemoryAccessType mem_payload)) = true := rfl
  have htr := execEffTranslateAddrIdentityStore a s hpriv hmprv
  rw [translateIdentityEq] at htr
  have hep : execEff (effectivePrivilege (.Store .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s, []) := by rw [hpriv]; exact execEffEffectivePrivilegeStore _ s hmprv
  have hea := execEffMemWriteEa4 .PBMT_PMA a region s hpmpEff hmatch hpalign hwrite hpriv hmprv
  have hwv : ∀ d : BitVec 32, d = data →
      execEff (mem_write_value (.Physaddr a) 4 d (.Store .Data) .PBMT_PMA false false false) s =
        some (.Ok true, s.setMem (bmWrite s.mem a 4 data), [.WEwrite ⟨false, false, false⟩ a 4 data]) := by
    intro d hd
    rw [hd]
    exact execEffMemWriteValue4 .PBMT_PMA a region data _ s hpmpEff hmatch hpalign hwrite hc hsig hh hdev
      rfl hmprv hpriv
  unfold vmem_write_addr
  simp only [bits_of_virtaddr, hsp, pure_bind]
  rw [execEffCatchEarlyReturn]
  eff8s_run [halign, Functions.not, hep, execEffTranslationModeM, htr, hsc']
  dsimp only [iteNoSplitBare, Int.toNat_natCast]
  eff8s_run [hea]
  rw [hwv _ (extractFull4 data)]
  rfl

/-- Rocq `exec_eff_vmem_write_4_gpr` (section `VWgeff4`; Rocq's `ea`, `a4`, `pa` are
`s.gpr rs1 + offset`). -/
theorem execEffVmemWrite4Gpr (rs1 : BitVec 5) (offset : BitVec 64) (data : BitVec 32) (region : PMA_Region)
    (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + offset)) 4 = true)
    (hpmpEff : execEff (pmpCheck (.Physaddr (s.gpr rs1 + offset)) 4 (.Store .Data) .Machine) s =
      some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (s.gpr rs1 + offset)) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + offset)) 4 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : execEff (within_clint (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr (s.gpr rs1 + offset)) 4) s = some (false, s, []))
    (hdev : devAddr (s.gpr rs1 + offset) = false) :
    execEff (vmem_write (.Regidx rs1) offset 4 data (.Store .Data) false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem (s.gpr rs1 + offset) 4 data),
        [.WEwrite ⟨false, false, false⟩ (s.gpr rs1 + offset) 4 data]) := by
  have hgta : execEff (get_transformed_data_addr (.Regidx rs1) offset (.Store .Data) 4) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s, []) := by
    unfold get_transformed_data_addr
    eff8s_run [execEffExtDataGetAddrGpr,
      execEffTransformEffectiveAddressStore _ s hcp hmprv hpmm, pmTransformPA0]
  unfold vmem_write
  rw [execEffCatchEarlyReturn]
  eff8s_run [hgta, execEffVmemWriteAddr4 _ data region s halign hcp hmprv hpmpEff hmatch hpalign hwrite
    hc hsig hh hdev]

/-- Rocq `exec_eff_execute_STORE_4_gpr` (section `ExecStoreGeff4`; Rocq's `vw4` is
`Sail.BitVec.extractLsb (s.gpr rs2) 31 0`): the trace is the ONE plain write. -/
theorem execEffExecuteSTORE4Gpr (rs2 rs1 : BitVec 5) (imm : BitVec 12) (region : PMA_Region)
    (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = true)
    (hpmpEff : execEff (pmpCheck (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 (.Store .Data)
      .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions)
      (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = some region)
    (hpalign : is_aligned_paddr (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hc : execEff (within_clint (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s =
      some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s =
      some (false, s, []))
    (hh : execEff (within_htif_writable (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 4) s =
      some (false, s, []))
    (hdev : devAddr (s.gpr rs1 + sign_extend (m := 64) imm) = false) :
    execEff (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 4))) s =
      some (RETIRE_SUCCESS,
        s.setMem (bmWrite s.mem (s.gpr rs1 + sign_extend (m := 64) imm) 4
          (Sail.BitVec.extractLsb (s.gpr rs2) 31 0 : BitVec 32)),
        [.WEwrite ⟨false, false, false⟩ (s.gpr rs1 + sign_extend (m := 64) imm) 4
          (Sail.BitVec.extractLsb (s.gpr rs2) 31 0 : BitVec 32)]) := by
  show execEff (execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4) s = _
  unfold execute_STORE
  eff8s_run [execEffRXBitsGpr, autocastSubrangeId4, execEffVmemWrite4Gpr rs1 _ _ region s hcp hmprv
    hpmm halign hpmpEff hmatch hpalign hwrite hc hsig hh hdev]

end Weak
