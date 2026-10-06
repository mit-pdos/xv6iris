/-
Weak: the aligned no-split arm of `vmem_read_addr`/`vmem_write_addr`, the
M-mode 8-byte load/store chain, the PTE write-back.

Rocq: `iris/WpLoad.v` (`exec_vmem_read_addr_8`), `iris/WpMmodeLeafBase.v` (sections
`VRg`, `ExecLoadG`, `SW`, `VWg`, `ExecStoreG`), `iris/PtTreeAdue.v`
(`exec_write_pte_conditional_ram`) @ xxvzwolszwmp.

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
1. The model's access width `if do_split then in_page else width` is used in TYPES;
   the closed condition is removed by `dsimp` with the `rfl` facts `iteNoSplit*`
   (MachCSL's `umm_ite_nosplit` recipe), with the default simprocs off.
2. Rocq's `a8`/`pa` (`zero_extend (subrange ea 63 0)`, `+ 0*8`) are the effective
   address itself (`s.gpr rs1 + offset`); Rocq's `data2` (the full-width update of
   the zero accumulator) is the read value `v`.
3. Section premises bundled as `MemM8` (Machine, MPRV clear, all-OFF PMP, PMA region,
   aligned, CLINT/SIG clear, RAM).
4. `exec_write_pte_conditional_ram`: Rocq derives the PMP range match and the
   device-window facts from `addr_is_ram a`, `addr_is_ram (a+7)`,
   `ram_base + ram_size ≤ pmpaddr0 * 4` and `htif_tohost_base = None`; here they are
   the premises themselves (the PMP range match, the Lean `within_*` tests).

**Name map (Rocq → Lean).**  WpLoad: `exec_vmem_read_addr_8` ↦ `execVmemReadAddr8`.
WpMmodeLeafBase: `exec_vmem_read_8_gpr` ↦ `execVmemRead8Gpr`,
`exec_execute_LOAD_8_gpr` ↦ `execExecuteLOAD8Gpr`, `exec_vmem_write_addr_8` ↦
`execVmemWriteAddr8`, `exec_vmem_write_8_gpr` ↦ `execVmemWrite8Gpr`,
`exec_execute_STORE_8_gpr` ↦ `execExecuteSTORE8Gpr`.  PtTreeAdue:
`exec_write_pte_conditional_ram` ↦ `execWritePteConditionalRam`.  Lean-only:
`iteNoSplit{Bare,Sv32,Sv39,Sv48,Sv57}`, `uszFull8`, `extractFull8`, `extractStore8`,
`execVmemReadAddrAligned8`, `execVmemWriteAddrAligned8`, `MemM8`,
`translateIdentityEq`, `pmTransformPA0`, `execGetTransformedDataAddrM`.

**Dropped**: none of the names the weak tier uses.
-/
import Weak.ExecSC7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The no-split arm of `vmem_read_addr` / `vmem_write_addr`

The model computes the access width as `if do_split then in_page else width` and
uses it in TYPES (`BitVec (8 * width)`), so the closed condition is removed by
`dsimp` with these `rfl` facts (as MachCSL's `umm_ite_nosplit`), with the default
simprocs off (they rewrite the widths inside types). -/

theorem iteNoSplitBare {α : Type} (a b : α) :
    (if (SATPMode.Bare != SATPMode.Bare && (0 : Int) >b 0) = true then a else b) = b := rfl
theorem iteNoSplitSv32 {α : Type} (a b : α) :
    (if (SATPMode.Sv32 != SATPMode.Bare && (0 : Int) >b 0) = true then a else b) = b := rfl
theorem iteNoSplitSv39 {α : Type} (a b : α) :
    (if (SATPMode.Sv39 != SATPMode.Bare && (0 : Int) >b 0) = true then a else b) = b := rfl
theorem iteNoSplitSv48 {α : Type} (a b : α) :
    (if (SATPMode.Sv48 != SATPMode.Bare && (0 : Int) >b 0) = true then a else b) = b := rfl
theorem iteNoSplitSv57 {α : Type} (a b : α) :
    (if (SATPMode.Sv57 != SATPMode.Bare && (0 : Int) >b 0) = true then a else b) = b := rfl

/-- The full-width accumulator write of an 8-byte access. -/
theorem uszFull8 (w : BitVec 64) :
    (Sail.BitVec.updateSubrange (zeros (n := (8 * ((8 : Nat) : Int)).toNat)) (8 * ((8 : Nat) : Int) - 1).toNat 0
      (BitVec.setWidth ((8 * ((8 : Nat) : Int) - 1).toNat - 0 + 1) w) : BitVec 64) = w := by
  show Sail.BitVec.updateSubrange (zeros (n := 64)) 63 0 (BitVec.setWidth 64 w) = w
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.setWidth_eq, zeros]
  bv_decide

set_option simprocs false in
/-- An aligned 8-byte in-page read: no split, one translation, one physical read. -/
theorem execVmemReadAddrAligned8 (va pa : BitVec 64) (acc : MemoryAccessType mem_payload)
    (aq rl : Bool) (p : Privilege) (mode : SATPMode) (pbmt : page_based_mem_type) (w : BitVec 64)
    (s s1 : ExecSt) (hal : is_aligned_vaddr (.Virtaddr va) 8 = true)
    (hep : exec (effectivePrivilege acc (s.regs .mstatus) (s.regs .cur_privilege)) s = some (p, s))
    (hmode : exec (translationMode p) s = some (mode, s))
    (htr : exec (translateAddr (.Virtaddr va) acc) s = some (.Ok (.Physaddr pa, pbmt, ()), s1))
    (hmr : exec (mem_read acc pbmt (.Physaddr pa) 8 aq rl false) s1 = some (.Ok w, s1)) :
    exec (vmem_read_addr (.Virtaddr va) 8 acc aq rl false) s = some (.Ok w, s1) := by
  have hsp := splitOnPageBoundaryAlignedEq va 8 (by simp [vmemWidth]) hal
  cases mode <;>
  · unfold vmem_read_addr translate_and_read_value
    simp only [bits_of_virtaddr, hsp, pure_bind]
    rw [execCatchEarlyReturn]
    exec_run [hal, Functions.not, hep, hmode, htr]
    dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57, Int.toNat_natCast]
    exec_run [hmr]
    exact congrArg (fun x => some (Result.Ok x, s1)) (uszFull8 w)

theorem extractFull8 (data : BitVec 64) :
    (BitVec.setWidth (8 * 8) (Sail.BitVec.extractLsb data (8 * ((8 : Nat) : Int) - 1).toNat 0) : BitVec 64) = data := by
  show BitVec.setWidth 64 (Sail.BitVec.extractLsb data 63 0) = data
  simp only [Sail.BitVec.extractLsb]
  bv_decide

set_option simprocs false in
/-- An aligned 8-byte in-page write of a non-conditional store: no split, one
translation, the announcement, the value. -/
theorem execVmemWriteAddrAligned8 (va pa : BitVec 64) (data : BitVec 64) (acc : MemoryAccessType mem_payload)
    (aq rl : Bool) (p : Privilege) (mode : SATPMode) (pbmt : page_based_mem_type) (s s1 s2 : ExecSt)
    (hal : is_aligned_vaddr (.Virtaddr va) 8 = true) (hsc : is_store_conditional acc = false)
    (hep : exec (effectivePrivilege acc (s.regs .mstatus) (s.regs .cur_privilege)) s = some (p, s))
    (hmode : exec (translationMode p) s = some (mode, s))
    (htr : exec (translateAddr (.Virtaddr va) acc) s = some (.Ok (.Physaddr pa, pbmt, ()), s1))
    (hea : exec (mem_write_ea (.Physaddr pa) 8 acc pbmt aq rl false) s1 = some (.Ok (), s1))
    (hwv : ∀ d : BitVec 64, d = data →
      exec (mem_write_value (.Physaddr pa) 8 d acc pbmt aq rl false) s1 = some (.Ok true, s2)) :
    exec (vmem_write_addr (.Virtaddr va) 8 data acc aq rl false) s = some (.Ok true, s2) := by
  have hsp := splitOnPageBoundaryAlignedEq va 8 (by simp [vmemWidth]) hal
  have hsc' : (false == is_store_conditional acc) = true := by rw [hsc]; rfl
  cases mode <;>
  · unfold vmem_write_addr
    simp only [bits_of_virtaddr, hsp, pure_bind]
    rw [execCatchEarlyReturn]
    exec_run [hal, Functions.not, hep, hmode, htr, hsc']
    dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57, Int.toNat_natCast]
    exec_run [hea]
    rw [hwv _ (extractFull8 data)]
    rfl

/-! ## 2. The M-mode 8-byte load/store chain (Rocq `WpLoad`, `WpMmodeLeafBase`) -/

/-- The Machine-mode premises of Rocq's 8-byte RAM access sections (`VRg`, `SW`, `VWg`, ...)
at the physical address `pa`, minus the direction-specific PMA bit. -/
structure MemM8 (pa : BitVec 64) (region : PMA_Region) (s : ExecSt) : Prop where
  hcp : s.regs .cur_privilege = .Machine
  hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false
  hpmp : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF
  hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr pa) 8 = some region
  hpalign : is_aligned_paddr (.Physaddr pa) 8 = true
  hc : exec (within_clint (.Physaddr pa) 8) s = some (false, s)
  hsig : exec (within_sig (.Physaddr pa) 8) s = some (false, s)
  hdev : devAddr pa = false

theorem translateIdentityEq (a : BitVec 64) : zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a)) = a :=
  fetchPa_eq a

/-- Rocq `WpLoad.exec_vmem_read_addr_8`. -/
theorem execVmemReadAddr8 (a : BitVec 64) (v : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (H : MemM8 a region s) (halign : is_aligned_vaddr (.Virtaddr a) 8 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hh : exec (within_htif_readable (.Physaddr a) 8) s = some (false, s)) (hb : BytesAt s a 8 v) :
    exec (vmem_read_addr (.Virtaddr a) 8 (.Load .Data) false false false) s = some (.Ok v, s) := by
  have htr := execTranslateAddrIdentityLoad a s H.hcp H.hmprv
  rw [translateIdentityEq] at htr
  have hep : exec (effectivePrivilege (.Load .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s) := by rw [H.hcp]; exact execEffectivePrivilegeLoad _ s H.hmprv
  have hck := execCheckedMemReadRam (.Load .Data) .PBMT_PMA .Machine a 8 false false false .Read_plain v s
    (by simp [vmemWidth]) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
    (execPmaCheckRamLoadG 8 a .PBMT_PMA region s H.hmatch H.hpalign hread)
    (execPmpCheckMachineNone _ 8 _ s H.hpmp) (execWithinMmioReadableFalse a 8 s H.hc H.hsig hh)
    (execReadRam _ a 8 v s (Or.inl rfl) H.hdev hb)
  have hmr : exec (mem_read (.Load .Data) .PBMT_PMA (.Physaddr a) 8 false false false) s = some (.Ok v, s) := by
    unfold mem_read
    exec_run [hep, execMemReadPriv _ _ _ _ _ _ _ _ v s (by decide) hck]
    simp only [Nat.reduceMul, BitVec.setWidth_eq]
  exact execVmemReadAddrAligned8 a a _ false false .Machine .Bare .PBMT_PMA v s s halign hep
    (execTranslationModeM s) htr hmr

/-- Rocq `WpMmodeLeafBase.exec_vmem_write_addr_8` (section `SW`). -/
theorem execVmemWriteAddr8 (a : BitVec 64) (data : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (H : MemM8 a region s) (halign : is_aligned_vaddr (.Virtaddr a) 8 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hh : exec (within_htif_writable (.Physaddr a) 8) s = some (false, s)) :
    exec (vmem_write_addr (.Virtaddr a) 8 data (.Store .Data) false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem a 8 data)) := by
  have htr := execTranslateAddrIdentityStore a s H.hcp H.hmprv
  rw [translateIdentityEq] at htr
  have hep : exec (effectivePrivilege (.Store .Data) (s.regs .mstatus) (s.regs .cur_privilege)) s =
      some (.Machine, s) := by rw [H.hcp]; exact execEffectivePrivilegeStore _ s H.hmprv
  exact execVmemWriteAddrAligned8 a a data _ false false .Machine .Bare .PBMT_PMA s s _ halign rfl hep
    (execTranslationModeM s) htr
    (execMemWriteEa .PBMT_PMA a region s H.hpmp H.hmatch H.hpalign hwrite H.hcp H.hmprv)
    (fun d hd => by
      subst hd
      exact execMemWriteValue8 .PBMT_PMA a region d _ s H.hpmp H.hmatch H.hpalign hwrite H.hc H.hsig hh H.hdev
        rfl H.hmprv H.hcp)

theorem pmTransformPA0 (ea : BitVec 64) : pm_transform_PA (.Virtaddr ea) 0 = .Virtaddr ea := by
  simp only [pm_transform_PA, zero_extend, Sail.BitVec.extractLsb, Sail.BitVec.zeroExtend, Functions.xlen,
    virtaddr.Virtaddr.injEq]
  bv_decide

/-- The effective address of an M-mode access through `rs1 + offset`. -/
theorem execGetTransformedDataAddrM (rs1 : BitVec 5) (offset : BitVec 64) (acc : MemoryAccessType mem_payload)
    (s : ExecSt) (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (hacc : acc = .Load .Data ∨ acc = .Store .Data) :
    exec (get_transformed_data_addr (.Regidx rs1) offset acc 8) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s) := by
  unfold get_transformed_data_addr
  rcases hacc with rfl | rfl
  · exec_run [execExtDataGetAddrGpr, execTransformEffectiveAddressLoad _ s hcp hmprv hpmm, pmTransformPA0]
  · exec_run [execExtDataGetAddrGpr, execTransformEffectiveAddressStore _ s hcp hmprv hpmm, pmTransformPA0]

/-- Rocq `WpMmodeLeafBase.exec_vmem_read_8_gpr` (section `VRg`; Rocq's `data2` is `v`). -/
theorem execVmemRead8Gpr (rs1 : BitVec 5) (offset v : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (H : MemM8 (s.gpr rs1 + offset) region s)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + offset)) 8 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hh : exec (within_htif_readable (.Physaddr (s.gpr rs1 + offset)) 8) s = some (false, s))
    (hb : BytesAt s (s.gpr rs1 + offset) 8 v) :
    exec (vmem_read (.Regidx rs1) offset 8 (.Load .Data) false false false) s = some (.Ok v, s) := by
  unfold vmem_read
  rw [execCatchEarlyReturn]
  exec_run [execGetTransformedDataAddrM rs1 offset _ s H.hcp H.hmprv hpmm (Or.inl rfl),
    execVmemReadAddr8 _ v region s H halign hread hh hb]

/-- Rocq `WpMmodeLeafBase.exec_execute_LOAD_8_gpr` (section `ExecLoadG`). -/
theorem execExecuteLOAD8Gpr (rs1 rd : BitVec 5) (imm : BitVec 12) (v : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (_hrd : rd.toNat ≠ 0) (H : MemM8 (s.gpr rs1 + sign_extend (m := 64) imm) region s)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 = true)
    (hread : (override_PMA region.attributes .PBMT_PMA).readable = true)
    (hh : exec (within_htif_readable (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8) s = some (false, s))
    (hb : BytesAt s (s.gpr rs1 + sign_extend (m := 64) imm) 8 v) :
    exec (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (extend_value false v)) := by
  show exec (execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 8) s = _
  unfold execute_LOAD
  exec_run [execVmemRead8Gpr rs1 _ v region s H hpmm halign hread hh hb, execWXBitsGpr]

/-- Rocq `WpMmodeLeafBase.exec_vmem_write_8_gpr` (section `VWg`), for any stored value. -/
theorem execVmemWrite8Gpr (rs1 : BitVec 5) (offset data : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (H : MemM8 (s.gpr rs1 + offset) region s)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + offset)) 8 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hh : exec (within_htif_writable (.Physaddr (s.gpr rs1 + offset)) 8) s = some (false, s)) :
    exec (vmem_write (.Regidx rs1) offset 8 data (.Store .Data) false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem (s.gpr rs1 + offset) 8 data)) := by
  unfold vmem_write
  rw [execCatchEarlyReturn]
  exec_run [execGetTransformedDataAddrM rs1 offset _ s H.hcp H.hmprv hpmm (Or.inr rfl),
    execVmemWriteAddr8 _ data region s H halign hwrite hh]

theorem extractStore8 (d : BitVec 64) :
    (BitVec.setWidth (8 * 8) (Sail.BitVec.extractLsb d (((8 : Nat) : Int) * 8 - 1).toNat 0) : BitVec 64) = d := by
  show BitVec.setWidth 64 (Sail.BitVec.extractLsb d 63 0) = d
  simp only [Sail.BitVec.extractLsb]
  bv_decide

/-- Rocq `WpMmodeLeafBase.exec_execute_STORE_8_gpr` (section `ExecStoreG`). -/
theorem execExecuteSTORE8Gpr (rs2 rs1 : BitVec 5) (imm : BitVec 12) (region : PMA_Region) (s : ExecSt)
    (H : MemM8 (s.gpr rs1 + sign_extend (m := 64) imm) region s)
    (hpmm : pmm_mode_backwards (_get_Seccfg_PMM (s.regs .mseccfg)) = .PMM_Disabled)
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8 = true)
    (hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true)
    (hh : exec (within_htif_writable (.Physaddr (s.gpr rs1 + sign_extend (m := 64) imm)) 8) s = some (false, s)) :
    exec (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8))) s =
      some (RETIRE_SUCCESS, s.setMem (bmWrite s.mem (s.gpr rs1 + sign_extend (m := 64) imm) 8 (s.gpr rs2))) := by
  show exec (execute_STORE imm (.Regidx rs2) (.Regidx rs1) 8) s = _
  unfold execute_STORE
  exec_run [execRXBitsGpr, execVmemWrite8Gpr rs1 _ _ region s H hpmm halign hwrite hh]
  rw [extractStore8]

/-- Rocq `PtTreeAdue.exec_write_pte_conditional_ram`: the A/D write-back of an S-mode walk.
Deviation: Rocq derives the PMP range match and the device-window facts from
`addr_is_ram a`, `addr_is_ram (a+7)`, `ram_base + ram_size ≤ pmpaddr0 * 4` and
`htif_tohost_base = None`; here they are the premises themselves (the Lean model's
`within_*` tests, the PMP range match). -/
theorem execWritePteConditionalRam (a w' : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (hal : is_aligned_paddr (.Physaddr a) 8 = true)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hW : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr a) 8 = some region)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_write = true)
    (hc : exec (within_clint (.Physaddr a) 8) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr a) 8) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr a) 8) s = some (false, s))
    (hdev : devAddr a = false) :
    exec (write_pte_conditional (.Physaddr a) 8 w') s = some (.Ok true, s.setMem (bmWrite s.mem a 8 w')) := by
  unfold write_pte_conditional mem_write_value_priv mem_write_value_priv_meta
  have hck := execCheckedMemWriteRam (.Store .PageTableEntry) .PBMT_PMA .Supervisor a 8 w' false false true
    .Write_RISCV_conditional s (by simp [vmemWidth]) (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
    (execPmaCheckRamWpteRoc a _ region true s hm hal hpte)
    (execPmpCheckSupervisorGrantWpte a 8 s hA hlt hr hW) (execWithinMmioWritableFalse a 8 s hc hsig hh) hdev
  simp only [Nat.reduceMul, BitVec.setWidth_eq]
  exec_run [hck, default_meta]

end Weak
