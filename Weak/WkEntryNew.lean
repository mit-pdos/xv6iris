/-
Weak: **the weak-tier `_entry` boot chain** (M4 batch 4: the vertical-slice validation on the
M-mode tier).

Rocq: `iris/WkEntryNew.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The weak twin of `WpEntryNew.wp_entry`: the xv6 kernel's
`_entry` sequence -- 8 instructions at `0x80000000` up to and including the `jal` into
`start()` -- as ONE WP theorem over the WEAK machine, with the SC statement's spellings
swapped per the porting guide: `kernel_text` ↦ `wkernelText kbs` (+ the pure coverage premise
`WkEntryEff.wkbCovers kbs`); `entry_ld_ea ↦ₚ₈{dq} v_stack0` ↦ `vwpHold (wpt8 entryLdEa dq
v_stack0) ws` paired with this hart's `hartWs` cell, the continuation binding the post-boot
view `ws'` with `⌜wsLe ws ws'⌝`; everything else -- the config bundle, `pc_is`, `gpr_file`,
`mhartid`, the `m_jal` output file -- is unchanged.

Composition: the seven register-only instructions go through `WeakFunnel.wwpInstr` at
`P := wPEff (fetch trace)` / `Q := wQPure` with `WeakEff.wcertNowrite` as the certificate and
`WkEntryEff`'s `execEff` mirrors (trace `[]`) feeding both the funnel's `exec` fact and the
fetch-arm lemmas' premise (c); the one memory instruction (`ld sp, imm(sp)`) goes through §1's
`wwpLd8LeafSame` -- the `WeakLeafLd8` leaf restated for the rd = rs1 register shape (one GPR
cell), reusing that file's certificate (`wcertLoad8Base4`), execute lemma (`execEffLd8At`)
and `wPEff` half (`wPEffLd8`).  All four fetch-alignment arms occur: F_Base@4 (auipc, ld,
mul), F_RVC@4 (c.lui, c.add), F_Base@2 (csrr, jal), F_RVC@2 (c.addi).

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WkEntryEff.lean` deviation 1 and `Weak/WeakLeafLd8.lean` deviations
   1-5 (`register_lookup r s.(sregs)` ↦ `s.regs r`, `set_reg` ↦ `ExecSt.setReg`, the GPR write
   `set_reg (R_bitvector_64 (gpr_of_Z (uint rd)))` ↦ `ExecSt.setGpr rd`, the GPR cell
   `R_bitvector_64 (gpr_of_Z (uint r)) ↦ᵣ x` ↦ `MachCSL.gpr cpu r (DFrac.own 1) x`,
   `regval_into_reg v` ↦ `v`, `add_vec_int` ↦ `BitVec.addInt`, `uint r <> 0` ↦
   `r.toNat ≠ 0`, `addr_is_ram` windows ↦ `inRam a n`, `GEN`/`CID` ↦ explicit `gen`/`cpu`,
   `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`).  `gpr_file m` over a Rocq `regfile` ↦
   `MachCSL.gprFile cpu m` over a `RegMap` (`<[Regidx i := v]> m` ↦ `m.set i v`, `m !!! Regidx
   i` ↦ `m i`); `regidx_bits rd_clui` etc. ↦ the Lean-only bit fields `WkEntryNew.rdCluiB`,
   `rsdCaddiB`, `rsdCaddB`, `rs2CaddB`.
2. THE CONFIG INTERFACE (owner decision Q3; `Weak/WeakFunnel.lean` deviation 7): Rocq
   `mmode_config dq` ∗ `pmpcfg_n ↦ᵣ{dq} pmpcfg0` ↦ `mConf cpu dq c ∗ clockCells cpu`
   (`pmpcfg0 := c.pmpcfg`), with the extra premise `MConf.mok c`; `pmp_all_off` ↦
   `pmpAllOff`.  `wwpLd8LeafSame` keeps Rocq's `DfracOwn q` as an arbitrary `dq`.
3. O2 (owner decision; `Weak/WeakFetchEff.lean` deviation 2): every fetch trace element is
   `.WEread WeakFetchEff.wakIfetch …` (Rocq `wak_plain`); the fetch-arm lemmas' extra
   `fetchPin` obligation is discharged from the text bytes (`winstrTextPinned`,
   `WeakAcquire.fetchPinOfText`).
4. THE KERNEL IMAGE (`Weak/WkEntryEff.lean` deviation 6): the `ld` is the Lean image's
   `ld sp, 1000(sp)` (`WkEntryEff.wLd = 0x3e813103`; Rocq `0x20813103`, imm 520), so
   `entryLdEa` is the Lean image's address.  The SC vocabulary of `CodeEntryAux` /
   `WpEntryNew` (`pc_e0..pc_e7`, `pc_start`, `entry_sp1`, `entry_ld_ea`, the `pc_eK_eK+1`
   arithmetic, `jal_aligned`, `reg_ld_auipc`, `m_auipc … m_jal`) has no Lean twin and is
   restated here, file-qualified (`WkEntryNew.*`); `pc_eK` is `BitVec.ofInt 64` of the same
   `KernelSyms` offset.
5. THE DECODE FACTS: Rocq's generated catalogue `KernelDecode*.kd_*` (no Lean twin,
   architecture C.5) ↦ the read-only-walk recipe of `Weak/AxSfence.lean` deviation 3:
   `WkEntryNew.execAnyCfg` splits `cfgOk` and runs `Weak.execOfRunRead` on `MachCSL.drefM`
   and on the supervisor map without `mseccfg` (`WkEntryNew.drefS0`, = `AxSfence.drefSf`);
   each walk is closed by `kernel_rfl`.
6. PROOF STRUCTURE: Rocq's one-`Qed` chain inlines the register-only funnel block seven
   times.  Lean factors it as the Lean-only generic leaf `WkEntryNew.wwpRegLeaf` (the block
   with the instruction, its fetch arm, its destination cell, one extra GPR read `ra`, and one
   extra owned resource `X` -- the `mhartid` cell for `csrr` -- as parameters), fed by the
   Lean-only per-arm `wPEff` dischargers `WkEntryNew.armBase4`/`armRvc4`/`armBase2`/`armRvc2`
   and the per-instruction `execEff` facts `WkEntryNew.regExecE0`/`E2`…`E7`.  The leaf
   threads the GPR file (`gprFile`) itself: Rocq's `gpr_file_lookup_acc` /
   `gpr_file_insert_acc` steps are inside it.  The statement of `wwpEntry` is Rocq's.
7. `ram_win8` (Rocq Ltac) ↦ the macro `wk_new_ram_win8`; the Lean leaves take the window form
   `inRam ea 8` (closed by `decide +kernel`), so the macro is exercised by an `example` only.
   `vm_compute` ↦ `decide +kernel` (closed Boolean / `BitVec` facts) and `kernel_rfl` (walks).

**Rocq → Lean name map.**  `jal_sexec_facts` `jalSexecFacts`, `wwp_ld8_leaf_same`
`wwpLd8LeafSame`, `ram_win8` (Ltac) `wk_new_ram_win8` (macro), `wwp_entry` `wwpEntry` (none in
the duplicated-name table).  Lean-only stand-ins for Rocq SC definitions (file-qualified):
`WkEntryNew.pcE0..pcE7`, `pcStart`, `entrySp1`, `entryLdEa`, `pcE0E1 … pcE6E7`, `pcE7Start`,
`jalAligned`, `regLdAuipc`, `mAuipc`, `mLd`, `mClui`, `mCsrr`, `mCaddi`, `mMul`, `mCadd`,
`mJal`, `rdCluiB`, `rsdCaddiB`, `rsdCaddB`, `rs2CaddB`.  Lean-only helpers (file-qualified):
`WkEntryNew.drefS0`, `execAnyCfg`, `decBase`, `decRvc`, the 16 walks `walkE0M`/`walkE0S` …
`walkE7M`/`walkE7S` (Rocq's `kd_*` / `KernelDecode*` facts, deviation 5), `setRegIdem`,
`gprPre`, `RegExec`, `ConfC`, `confExec`, `fetchInWindow1`, `fetchInWindow2`, `fetchFresh1`,
`fetchFresh2`, `armBase4`, `armRvc4`, `armBase2`, `armRvc2`, `regExecE0`, `regExecE2` …
`regExecE7`, `mMulEq` (Rocq's in-proof `change … with (m_mul …)`), `pcIsSplit`, `readNone`,
`readMhartid`, `wwpRegLeaf`.

**Dropped:** nothing (Rocq: 3 `Lemma`s + 1 `Ltac`; Lean: the 3 theorems + the macro (with one
`example`) + 79 Lean-only declarations listed above).
-/
import Weak.WkEntryEff
import Weak.WeakLeafLd8
import MachCSL.KCtx
import MachCSL.HwConfig

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open WkEntryEff

/-! ## 0. The JAL successor register frame -/

/-- Rocq `jal_sexec_facts`: `WeakLeafWin.loadSexecFacts`' twin for the JAL successor, whose
tower carries a SECOND `nextPC` write (the jump target) before the link-register write. -/
theorem jalSexecFacts (s0 : ExecSt) (b : Bool) (npc target : BitVec 64) (rd : BitVec 5)
    (link : BitVec 64) :
    let sExec :=
      (((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg .nextPC target).setGpr rd link
    sExec.regs .hart_state = s0.regs .hart_state ∧
    sExec.regs .minstret_increment = b ∧
    sExec.mem = s0.mem ∧
    sExec.dev = s0.dev ∧
    sExec.regs .nextPC = target := by
  intro sExec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide),
      setLookupNe .hart_state .nextPC _ _ (by decide)]
    leaf_peel .hart_state
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide),
      setLookupNe .minstret_increment .nextPC _ _ (by decide),
      setLookupNe .minstret_increment .nextPC _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  · rw [WeakLeafWin.setGprMem]; rfl
  · rw [WeakLeafWin.setGprDev]; rfl
  · rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]

/-! ## 0b. The `_entry` SC vocabulary (Lean-only stand-ins, deviation 4) -/

/-- Rocq `pc_e0` (AUIPC). -/
def WkEntryNew.pcE0 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«_entry» : Int) + 0x0)
/-- Rocq `pc_e1` (LOAD). -/
def WkEntryNew.pcE1 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«_entry» : Int) + 0x4)
/-- Rocq `pc_e2` (C.LUI). -/
def WkEntryNew.pcE2 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«_entry» : Int) + 0x8)
/-- Rocq `pc_e3` (CSRRS). -/
def WkEntryNew.pcE3 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«_entry» : Int) + 0xa)
/-- Rocq `pc_e4` (C.ADDI). -/
def WkEntryNew.pcE4 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«_entry» : Int) + 0xe)
/-- Rocq `pc_e5` (MUL). -/
def WkEntryNew.pcE5 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«_entry» : Int) + 0x10)
/-- Rocq `pc_e6` (C.ADD). -/
def WkEntryNew.pcE6 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«_entry» : Int) + 0x14)
/-- Rocq `pc_e7` (JAL). -/
def WkEntryNew.pcE7 : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«_entry» : Int) + 0x16)
/-- Rocq `pc_start`. -/
def WkEntryNew.pcStart : BitVec 64 := BitVec.ofInt 64 (KernelSyms.«start» : Int)

/-- Rocq `entry_sp1`: the value AUIPC writes to sp. -/
def WkEntryNew.entrySp1 : BitVec 64 := WkEntryNew.pcE0 + auipcOff immAuipc
/-- Rocq `entry_ld_ea`: the load effective address (deviation 4: the Lean image's). -/
def WkEntryNew.entryLdEa : BitVec 64 := WkEntryNew.entrySp1 + sign_extend (m := 64) immLd

/-- Rocq `regidx_bits rd_clui`. -/
def WkEntryNew.rdCluiB : BitVec 5 := hLui.extractLsb' 7 5
/-- Rocq `regidx_bits rsd_caddi`. -/
def WkEntryNew.rsdCaddiB : BitVec 5 := WkEntryEff.hAddi.extractLsb' 7 5
/-- Rocq `regidx_bits rsd_cadd`. -/
def WkEntryNew.rsdCaddB : BitVec 5 := WkEntryEff.hAdd.extractLsb' 7 5
/-- Rocq `regidx_bits rs2_cadd`. -/
def WkEntryNew.rs2CaddB : BitVec 5 := WkEntryEff.hAdd.extractLsb' 2 5

section pcs
open WkEntryNew

/-- Rocq `pc_e0_e1`. -/
theorem WkEntryNew.pcE0E1 : BitVec.addInt pcE0 4 = pcE1 := by decide +kernel
/-- Rocq `pc_e1_e2`. -/
theorem WkEntryNew.pcE1E2 : BitVec.addInt pcE1 4 = pcE2 := by decide +kernel
/-- Rocq `pc_e2_e3`. -/
theorem WkEntryNew.pcE2E3 : BitVec.addInt pcE2 2 = pcE3 := by decide +kernel
/-- Rocq `pc_e3_e4`. -/
theorem WkEntryNew.pcE3E4 : BitVec.addInt pcE3 4 = pcE4 := by decide +kernel
/-- Rocq `pc_e4_e5`. -/
theorem WkEntryNew.pcE4E5 : BitVec.addInt pcE4 2 = pcE5 := by decide +kernel
/-- Rocq `pc_e5_e6`. -/
theorem WkEntryNew.pcE5E6 : BitVec.addInt pcE5 4 = pcE6 := by decide +kernel
/-- Rocq `pc_e6_e7`. -/
theorem WkEntryNew.pcE6E7 : BitVec.addInt pcE6 2 = pcE7 := by decide +kernel
/-- Rocq `pc_e7_start`. -/
theorem WkEntryNew.pcE7Start : pcE7 + sign_extend (m := 64) immJal = pcStart := by decide +kernel
/-- Rocq `jal_aligned`. -/
theorem WkEntryNew.jalAligned :
    is_aligned_paddr (.Physaddr (pcE7 + sign_extend (m := 64) immJal)) 4 = true := by
  decide +kernel
/-- Rocq `reg_ld_auipc`: `i_ld` and `i_auipc` are both sp. -/
theorem WkEntryNew.regLdAuipc : iLd = iAuipc := by decide +kernel

end pcs

/-- Rocq `m_auipc`. -/
def WkEntryNew.mAuipc (m : RegMap) : RegMap := m.set iAuipc WkEntryNew.entrySp1
/-- Rocq `m_ld`. -/
def WkEntryNew.mLd (m : RegMap) (vStack0 : BitVec 64) : RegMap :=
  (WkEntryNew.mAuipc m).set iLd vStack0
/-- Rocq `m_clui`. -/
def WkEntryNew.mClui (m : RegMap) (vStack0 : BitVec 64) : RegMap :=
  (WkEntryNew.mLd m vStack0).set WkEntryNew.rdCluiB (luival (sign_extend (m := 20) immClui))
/-- Rocq `m_csrr`. -/
def WkEntryNew.mCsrr (m : RegMap) (vStack0 mhartidIn : BitVec 64) : RegMap :=
  (WkEntryNew.mClui m vStack0).set iRdCsrr mhartidIn
/-- Rocq `m_caddi`. -/
def WkEntryNew.mCaddi (m : RegMap) (vStack0 mhartidIn : BitVec 64) : RegMap :=
  (WkEntryNew.mCsrr m vStack0 mhartidIn).set WkEntryNew.rsdCaddiB
    (WkEntryNew.mCsrr m vStack0 mhartidIn WkEntryNew.rsdCaddiB + sign_extend (m := 64) immCaddi)
/-- Rocq `m_mul`. -/
def WkEntryNew.mMul (m : RegMap) (vStack0 mhartidIn : BitVec 64) : RegMap :=
  (WkEntryNew.mCaddi m vStack0 mhartidIn).set iMulRd
    (mult_to_bits_half (l := 64) mulopMul.signed_rs1 mulopMul.signed_rs2
      (WkEntryNew.mCaddi m vStack0 mhartidIn iMulRs1) (WkEntryNew.mCaddi m vStack0 mhartidIn iMulRs2)
      mulopMul.result_part)
/-- Rocq `m_cadd`. -/
def WkEntryNew.mCadd (m : RegMap) (vStack0 mhartidIn : BitVec 64) : RegMap :=
  (WkEntryNew.mMul m vStack0 mhartidIn).set WkEntryNew.rsdCaddB
    (WkEntryNew.mMul m vStack0 mhartidIn WkEntryNew.rsdCaddB +
      WkEntryNew.mMul m vStack0 mhartidIn WkEntryNew.rs2CaddB)
/-- Rocq `m_jal`. -/
def WkEntryNew.mJal (m : RegMap) (vStack0 mhartidIn : BitVec 64) : RegMap :=
  (WkEntryNew.mCadd m vStack0 mhartidIn).set iJal (BitVec.addInt WkEntryNew.pcE7 4)

/-! ## 0c. The decode facts (deviation 5) -/

/-- The supervisor-mode reference map without `mseccfg` (Lean-only; `AxSfence.drefSf`). -/
def WkEntryNew.drefS0 : (r : Register) → Option (RegisterType r)
  | .cur_privilege => some Privilege.Supervisor
  | .misa => some 0x800000000014112D#64
  | .menvcfg => some menvcfgS
  | _ => none

/-- Lean-only: a read-only walk evaluated on both reference maps is a decode fact at every
state the funnel's decode premise admits. -/
theorem WkEntryNew.execAnyCfg {X : Type} (m : SailM X) (x : X)
    (hM : runRead drefM m = some (x, true)) (hS : runRead WkEntryNew.drefS0 m = some (x, true))
    (t : ExecSt) (hm : t.regs .misa = misaC) (hc : cfgOk t) : exec m t = some (x, t) := by
  rcases hc with ⟨hp, hsec⟩ | ⟨hp, henv⟩
  · refine execOfRunRead drefM _ t _ true ?_ hM
    intro r v hv
    unfold drefM at hv
    split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv <;> subst hv
    · exact hp
    · exact hm
    · exact hsec
  · refine execOfRunRead WkEntryNew.drefS0 _ t _ true ?_ hS
    intro r v hv
    unfold WkEntryNew.drefS0 at hv
    split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv <;> subst hv
    · exact hp
    · exact hm
    · exact henv

/-- Lean-only: the `winstr` decode field of a full word. -/
theorem WkEntryNew.decBase (w : BitVec 32) (i : instruction)
    (hM : runRead drefM (ext_decode w) = some (i, true))
    (hS : runRead WkEntryNew.drefS0 (ext_decode w) = some (i, true)) :
    winstrDec (.F_Base w) i := by
  intro t _ _ _ hm hc
  simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
  exact WkEntryNew.execAnyCfg _ _ hM hS t hm hc

/-- Lean-only: the `winstr` decode field of a compressed halfword. -/
theorem WkEntryNew.decRvc (h : BitVec 16) (i0 i : instruction)
    (hM : runRead drefM (ext_decode_compressed h) = some (i0, true))
    (hS : runRead WkEntryNew.drefS0 (ext_decode_compressed h) = some (i0, true))
    (hl : is_lpad_instruction i0 = false)
    (hexp : ∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)) :
    winstrDec (.F_RVC h) i := by
  intro t _ _ _ hm hc
  simp only [fetchIsRvc, ↓reduceIte]
  exact ⟨i0, WkEntryNew.execAnyCfg _ _ hM hS t hm hc, hl, hexp⟩

/-! The read-only decode walks of the eight `_entry` words on both reference maps (Lean-only;
Rocq `KernelDecode*.kd_*`, deviation 5). -/

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

theorem WkEntryNew.walkE0M : runRead drefM (ext_decode wAuipc) =
    some (.UTYPE (immAuipc, .Regidx iAuipc, .AUIPC), true) := by kernel_rfl
theorem WkEntryNew.walkE0S : runRead WkEntryNew.drefS0 (ext_decode wAuipc) =
    some (.UTYPE (immAuipc, .Regidx iAuipc, .AUIPC), true) := by kernel_rfl
theorem WkEntryNew.walkE1M : runRead drefM (ext_decode wLd) =
    some (.LOAD (immLd, .Regidx iLd, .Regidx iLd, false, 8), true) := by kernel_rfl
theorem WkEntryNew.walkE1S : runRead WkEntryNew.drefS0 (ext_decode wLd) =
    some (.LOAD (immLd, .Regidx iLd, .Regidx iLd, false, 8), true) := by kernel_rfl
theorem WkEntryNew.walkE2M : runRead drefM (ext_decode_compressed hLui) =
    some (.C_LUI (immClui, rdClui), true) := by kernel_rfl
theorem WkEntryNew.walkE2S : runRead WkEntryNew.drefS0 (ext_decode_compressed hLui) =
    some (.C_LUI (immClui, rdClui), true) := by kernel_rfl
theorem WkEntryNew.walkE3M : runRead drefM (ext_decode wCsrr) =
    some (.CSRReg (csrCsrr, zreg, .Regidx iRdCsrr, .CSRRS), true) := by kernel_rfl
theorem WkEntryNew.walkE3S : runRead WkEntryNew.drefS0 (ext_decode wCsrr) =
    some (.CSRReg (csrCsrr, zreg, .Regidx iRdCsrr, .CSRRS), true) := by kernel_rfl
theorem WkEntryNew.walkE4M : runRead drefM (ext_decode_compressed hAddi) =
    some (.C_ADDI (immCaddi, rsdCaddi), true) := by kernel_rfl
theorem WkEntryNew.walkE4S : runRead WkEntryNew.drefS0 (ext_decode_compressed hAddi) =
    some (.C_ADDI (immCaddi, rsdCaddi), true) := by kernel_rfl
theorem WkEntryNew.walkE5M : runRead drefM (ext_decode wMul) =
    some (.MUL (.Regidx iMulRs2, .Regidx iMulRs1, .Regidx iMulRd, mulopMul), true) := by kernel_rfl
theorem WkEntryNew.walkE5S : runRead WkEntryNew.drefS0 (ext_decode wMul) =
    some (.MUL (.Regidx iMulRs2, .Regidx iMulRs1, .Regidx iMulRd, mulopMul), true) := by kernel_rfl
theorem WkEntryNew.walkE6M : runRead drefM (ext_decode_compressed hAdd) =
    some (.C_ADD (rsdCadd, rs2Cadd), true) := by kernel_rfl
theorem WkEntryNew.walkE6S : runRead WkEntryNew.drefS0 (ext_decode_compressed hAdd) =
    some (.C_ADD (rsdCadd, rs2Cadd), true) := by kernel_rfl
theorem WkEntryNew.walkE7M : runRead drefM (ext_decode wJal) =
    some (.JAL (immJal, .Regidx iJal), true) := by kernel_rfl
theorem WkEntryNew.walkE7S : runRead WkEntryNew.drefS0 (ext_decode wJal) =
    some (.JAL (immJal, .Regidx iJal), true) := by kernel_rfl

end walks

/-! ## 0d. Pure helpers of the register-only funnel block (Lean-only, deviation 6) -/

/-- Lean-only: a second write of the same register at the same value is the first. -/
theorem WkEntryNew.setRegIdem (s : ExecSt) (r : Register) (v : RegisterType r) :
    (s.setReg r v).setReg r v = s.setReg r v := by
  cases s
  simp only [ExecSt.setReg, ExecSt.mk.injEq, and_true]
  exact RegFile.set_eq_self _ _ _ (RegFile.set_same _ _ _)

/-- Lean-only: a GPR read through the funnel's two pre-writes. -/
theorem WkEntryNew.gprPre (s : ExecSt) (b : Bool) (npc : BitVec 64) (i : BitVec 5) :
    ((s.setReg .minstret_increment b).setReg .nextPC npc).gpr i = s.gpr i := by
  rw [WeakLeafLw4.gprSetNe _ _ _ _ (by decide), WeakLeafLw4.gprSetNe _ _ _ _ (by decide)]

/-- Lean-only: the `execute` fact of a register-only instruction writing (after a possible
second `nextPC` write `tgt`) one GPR `rd`, stated over every state whose `PC`, `rd`, `ra` and
`Rx`-registers have the given values. -/
def WkEntryNew.RegExec (i : instruction) (pc npc tgt : BitVec 64) (rd ra : BitVec 5)
    (rdv rav v : BitVec 64) (Rx : RegFile → Prop) : Prop :=
  ∀ (s : ExecSt) (b : Bool), Rx s.regs → s.regs .PC = pc → s.gpr rd = rdv → s.gpr ra = rav →
    s.regs .cur_privilege = .Machine →
    execEff (execute i) ((s.setReg .minstret_increment b).setReg .nextPC npc) =
      some (RETIRE_SUCCESS,
        (((s.setReg .minstret_increment b).setReg .nextPC npc).setReg .nextPC tgt).setGpr rd v, [])

/-- Lean-only: the fetch-arm lemmas' premise (c), at the confined state. -/
def WkEntryNew.ConfC (σ : Wmstate) (W : GSet PAddr) (i : instruction) (npc : BitVec 64) : Prop :=
  ∀ b : Bool, ∃ sExec : ExecSt,
    execEff (execute i)
      (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg .nextPC
        npc) = some (.Retire_Success (), sExec, []) ∧
    sExec.regs .hart_state = .HART_ACTIVE () ∧
    sExec.regs .minstret_increment = b ∧
    bmDomSub sExec.mem W

/-- Lean-only: premise (c) off the state-generic `execute` fact (Rocq's in-proof `Hc`). -/
theorem WkEntryNew.confExec (σ : Wmstate) (W : GSet PAddr) (i : instruction) (pc npc tgt : BitVec 64)
    (rd ra : BitVec 5) (rdv rav v : BitVec 64) (Rx : RegFile → Prop)
    (hexe : WkEntryNew.RegExec i pc npc tgt rd ra rdv rav v Rx) (hRx : Rx σ.wmRegs)
    (lpc : σ.wmRegs .PC = pc) (hrd : (wflatSt σ).gpr rd = rdv) (hra : (wflatSt σ).gpr ra = rav)
    (lpriv : σ.wmRegs .cur_privilege = .Machine) (lhart : σ.wmRegs .hart_state = .HART_ACTIVE ()) :
    WkEntryNew.ConfC σ W i npc := by
  intro b
  have hrd' : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr rd = rdv := by
    unfold ExecSt.gpr at hrd ⊢; exact hrd
  have hra' : (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).gpr ra = rav := by
    unfold ExecSt.gpr at hra ⊢; exact hra
  obtain ⟨F1, F2, F3, -, -⟩ :=
    jalSexecFacts (⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt) b npc tgt rd v
  exact ⟨_, hexe _ b hRx lpc hrd' hra' lpriv, by rw [F1]; exact lhart, F2,
    by rw [F3]; exact wmemRestrictDom σ W⟩

/-- Lean-only: a one-element fetch of at most 4 bytes at `pc` stays in `pc`'s window. -/
theorem WkEntryNew.fetchInWindow1 (pc : BitVec 64) (ak : AkInfo) (n : Nat) (hn : n ≤ 4) :
    fetchInWindow pc [.WEread ak pc n] := by
  intro ak' pa n' hin _ j hj
  simp only [List.mem_singleton, Weff.WEread.injEq] at hin
  obtain ⟨rfl, rfl, rfl⟩ := hin
  exact ⟨j, by omega, rfl⟩

/-- Lean-only: the two-halfword fetch stays in `pc`'s window. -/
theorem WkEntryNew.fetchInWindow2 (pc : BitVec 64) (ak : AkInfo) (hacc : accWf pc 4) :
    fetchInWindow pc [.WEread ak pc 2, .WEread ak (BitVec.addInt pc 2) 2] := by
  intro ak' pa n hin _ j hj
  exact weffsTouchFetch2 ak pc (WeakInterp.accAddr pa j) hacc ⟨_, hin, j, hj, rfl⟩

/-- Lean-only: a one-element trace is fetch-fresh. -/
theorem WkEntryNew.fetchFresh1 (e : Weff) : fetchFresh [e] := by
  simp [fetchFresh]

/-- Lean-only: a two-read trace is fetch-fresh. -/
theorem WkEntryNew.fetchFresh2 (ak : AkInfo) (p q : PAddr) (n k : Nat) :
    fetchFresh [.WEread ak p n, .WEread ak q k] := by
  simp [fetchFresh, weffWrites]

/-! ## 0e. The four fetch arms' `wPEff` dischargers (Lean-only, deviation 6) -/

section arms
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Lean-only: the `F_Base`-at-4 arm (`wPEffOfLeafBase` at `es_x := []`, the window
`wwin pc pc 0`, the reference state `dstateM`). -/
theorem WkEntryNew.armBase4 (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (w : BitVec 32)
    (i : instruction) (pmp : RegisterType .pmpcfg_n) :
    pmpAllOff pmp →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    goodb0 dM (ext_decode w) dstateM = true →
    exec (ext_decode w) dstateM = some (i, dstateM) →
    is_lpad_instruction i = false →
    wlogWf σ.wmLog → σ.wmRegs .PC = pc → wcfgRegs σ pmp →
    WkEntryNew.ConfC σ (wwin pc pc 0) i (BitVec.addInt pc 4) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_Base w) -∗
        ⌜wPEff (some cid) [.WEread WeakFetchEff.wakIfetch pc 4] σ⌝ := by
  intro hpmp hal4 hgood hdec hlpad hwf lpc hcfg hc
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  iintro Hlat #Hbs
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  ihave %htp := winstrTextPinned σ pc _ hwf $$ Hlat Hbs
  ipureintro
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  obtain ⟨-, hram, w', ⟨hww, hnotRVC⟩, htext0⟩ := hfok
  subst hww
  have h := wPEffOfLeafBase cid σ (wwin pc pc 0) pc w i [] dM dstateM hwf
    (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
    (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
    (fetchPinOfText σ pc _ (WkEntryNew.fetchInWindow1 pc _ 4 (by omega)) (WkEntryNew.fetchFresh1 _)
      (fun j hj => (htp j hj).2))
    lpc Lpriv (by rw [Lpmpc]; exact fun k => (hpmp k).2) Lpma Lhtif Lhart LmisaS LmIE Lelp hal4 hram
    (wwinConfText σ pc pc 0 w htext0) hnotRVC (agreeMRegs σ.wmRegs Lpriv Lsec Lmisa) dMMi hgood hdec
    hlpad hc
  rw [List.append_nil] at h
  exact h

/-- Lean-only: the `F_RVC`-at-4 arm. -/
theorem WkEntryNew.armRvc4 (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (h : BitVec 16)
    (i0 i : instruction) (pmp : RegisterType .pmpcfg_n) :
    pmpAllOff pmp →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    goodb0 dM (ext_decode_compressed h) dstateM = true →
    exec (ext_decode_compressed h) dstateM = some (i0, dstateM) →
    (∀ s : ExecSt, goodb0 dNone (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)) →
    wlogWf σ.wmLog → σ.wmRegs .PC = pc → wcfgRegs σ pmp →
    WkEntryNew.ConfC σ (wwin pc pc 0) i (BitVec.addInt pc 2) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
        ⌜wPEff (some cid) [.WEread WeakFetchEff.wakIfetch pc 4] σ⌝ := by
  intro hpmp hal4 hgood hdec hgood0 hexp hwf lpc hcfg hc
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  iintro Hlat #Hbs
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  ihave %htp := winstrTextPinned σ pc _ hwf $$ Hlat Hbs
  ipureintro
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  obtain ⟨-, hram, w, ⟨hsub, hrvc⟩, htext0⟩ := hfok
  have hr := wPEffOfLeafRvc4 cid σ (wwin pc pc 0) pc h w i0 i [] dM dNone dstateM hwf
    (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
    (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
    (fetchPinOfText σ pc _ (WkEntryNew.fetchInWindow1 pc _ 4 (by omega)) (WkEntryNew.fetchFresh1 _)
      (fun j hj => (htp j hj).2))
    lpc Lpriv (by rw [Lpmpc]; exact fun k => (hpmp k).2) Lpma Lhtif Lhart LmisaS (misaCOfVal _ Lmisa)
    LmIE Lelp hal4 hram (wwinConfText σ pc pc 0 w htext0) hsub hrvc
    (agreeMRegs σ.wmRegs Lpriv Lsec Lmisa) dMMi hgood hdec hgood0 hexp hc
  rw [List.append_nil] at hr
  exact hr

/-- Lean-only: the `F_Base`-at-2 arm (the two-halfword fetch). -/
theorem WkEntryNew.armBase2 (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (w : BitVec 32)
    (i : instruction) (pmp : RegisterType .pmpcfg_n) :
    pmpAllOff pmp →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    goodb0 dM (ext_decode w) dstateM = true →
    exec (ext_decode w) dstateM = some (i, dstateM) →
    is_lpad_instruction i = false →
    wlogWf σ.wmLog → σ.wmRegs .PC = pc → wcfgRegs σ pmp →
    WkEntryNew.ConfC σ (wwin pc pc 0) i (BitVec.addInt pc 4) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_Base w) -∗
        ⌜wPEff (some cid) [.WEread WeakFetchEff.wakIfetch pc 2,
          .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2] σ⌝ := by
  intro hpmp hal2 hal4 hgood hdec hlpad hwf lpc hcfg hc
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  iintro Hlat #Hbs
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  ihave %htp := winstrTextPinned σ pc _ hwf $$ Hlat Hbs
  ipureintro
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  obtain ⟨-, hram, w', ⟨hww, hnotRVC⟩, htext0⟩ := hfok
  subst hww
  have h := wPEffOfLeafBase2 cid σ (wwin pc pc 0) pc w i [] dM dstateM hwf
    (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
    (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
    (fetchPinOfText σ pc _ (WkEntryNew.fetchInWindow2 pc _ haccpc) (WkEntryNew.fetchFresh2 _ _ _ _ _)
      (fun j hj => (htp j hj).2))
    lpc Lpriv (by rw [Lpmpc]; exact fun k => (hpmp k).2) Lpma Lhtif Lhart LmisaS (misaCOfVal _ Lmisa)
    LmIE Lelp hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hnotRVC
    (agreeMRegs σ.wmRegs Lpriv Lsec Lmisa) dMMi hgood hdec hlpad hc
  rw [List.append_nil] at h
  exact h

/-- Lean-only: the `F_RVC`-at-2 arm. -/
theorem WkEntryNew.armRvc2 (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (h : BitVec 16)
    (i0 i : instruction) (pmp : RegisterType .pmpcfg_n) :
    pmpAllOff pmp →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    goodb0 dM (ext_decode_compressed h) dstateM = true →
    exec (ext_decode_compressed h) dstateM = some (i0, dstateM) →
    (∀ s : ExecSt, goodb0 dNone (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)) →
    wlogWf σ.wmLog → σ.wmRegs .PC = pc → wcfgRegs σ pmp →
    WkEntryNew.ConfC σ (wwin pc pc 0) i (BitVec.addInt pc 2) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_RVC h) -∗
        ⌜wPEff (some cid) [.WEread WeakFetchEff.wakIfetch pc 2] σ⌝ := by
  intro hpmp hal2 hal4 hgood hdec hgood0 hexp hwf lpc hcfg hc
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  iintro Hlat #Hbs
  ihave %haccpc := winstrBytesAccWf pc (.F_RVC h) $$ Hbs
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  ihave %htp := winstrTextPinned σ pc _ hwf $$ Hlat Hbs
  ipureintro
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  obtain ⟨-, hram, w, ⟨hsub, hrvc⟩, htext0⟩ := hfok
  have hr := wPEffOfLeafRvc2 cid σ (wwin pc pc 0) pc h w i0 i [] dM dNone dstateM hwf
    (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
    (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
    (fetchPinOfText σ pc _ (WkEntryNew.fetchInWindow1 pc _ 2 (by omega)) (WkEntryNew.fetchFresh1 _)
      (fun j hj => (htp j hj).2))
    lpc Lpriv (by rw [Lpmpc]; exact fun k => (hpmp k).2) Lpma Lhtif Lhart LmisaS (misaCOfVal _ Lmisa)
    LmIE Lelp hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hsub hrvc
    (agreeMRegs σ.wmRegs Lpriv Lsec Lmisa) dMMi hgood hdec hgood0 hexp hc
  rw [List.append_nil] at hr
  exact hr

end arms

/-! ## 0f. The seven `execute` facts (Lean-only, deviation 6) -/

section regexec
open WkEntryNew

/-- AUIPC sp, at `pc_e0`. -/
theorem WkEntryNew.regExecE0 (rdv rav : BitVec 64) :
    RegExec (.UTYPE (immAuipc, .Regidx iAuipc, .AUIPC)) pcE0 (BitVec.addInt pcE0 4) pcE1
      iAuipc iAuipc rdv rav entrySp1 (fun _ => True) := by
  intro s b _ hpc _ _ _
  have hp : ((s.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pcE0 4)).regs .PC = pcE0 := by
    leaf_peel .PC; exact hpc
  rw [execEffExecuteUTYPEAUIPCGpr, ← pcE0E1, setRegIdem, hp]
  rfl

/-- C.LUI a0 (expanded), at `pc_e2`. -/
theorem WkEntryNew.regExecE2 (rdv rav : BitVec 64) :
    RegExec (.UTYPE (sign_extend (m := 20) immClui, .Regidx rdCluiB, .LUI)) pcE2
      (BitVec.addInt pcE2 2) pcE3 rdCluiB rdCluiB rdv rav (luival (sign_extend (m := 20) immClui))
      (fun _ => True) := by
  intro s b _ _ _ _ _
  rw [execEffExecuteUTYPELUIGpr, ← pcE2E3, setRegIdem]

/-- CSRRS a1, mhartid, at `pc_e3`. -/
theorem WkEntryNew.regExecE3 (h rdv rav : BitVec 64) :
    RegExec (.CSRReg (csrCsrr, zreg, .Regidx iRdCsrr, .CSRRS)) pcE3 (BitVec.addInt pcE3 4) pcE4
      iRdCsrr iRdCsrr rdv rav h (fun f => f .mhartid = h) := by
  intro s b hRx _ _ _ hpriv
  have hp : ((s.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pcE3 4)).regs
      .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hm : ((s.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pcE3 4)).regs
      .mhartid = h := by
    leaf_peel .mhartid; exact hRx
  rw [execEffExecuteCSRRegGpr iRdCsrr _ (by decide) hp, ← pcE3E4, setRegIdem, hm]

/-- C.ADDI a1 (expanded), at `pc_e4`. -/
theorem WkEntryNew.regExecE4 (rdv rav : BitVec 64) :
    RegExec (.ITYPE (sign_extend (m := 12) immCaddi, .Regidx rsdCaddiB, .Regidx rsdCaddiB, .ADDI)) pcE4
      (BitVec.addInt pcE4 2) pcE5 rsdCaddiB rsdCaddiB rdv rav (rdv + sign_extend (m := 64) immCaddi)
      (fun _ => True) := by
  intro s b _ _ hrd _ _
  rw [execEffExecuteITYPEADDIGpr, ← pcE4E5, setRegIdem]
  unfold gprAddiVal
  rw [gprPre, hrd, show sign_extend (m := 64) (sign_extend (m := 12) immCaddi) =
    sign_extend (m := 64) immCaddi from by decide +kernel]

/-- MUL a0, a0, a1, at `pc_e5`. -/
theorem WkEntryNew.regExecE5 (rdv rav : BitVec 64) :
    RegExec (.MUL (.Regidx iMulRs2, .Regidx iMulRs1, .Regidx iMulRd, mulopMul)) pcE5
      (BitVec.addInt pcE5 4) pcE6 iMulRd iMulRs2 rdv rav
      (mult_to_bits_half (l := 64) mulopMul.signed_rs1 mulopMul.signed_rs2 rdv rav mulopMul.result_part)
      (fun _ => True) := by
  intro s b _ _ hrd hra _
  rw [execEffExecuteMULGpr iMulRs2 iMulRs1 iMulRd _ (by decide +kernel), ← pcE5E6, setRegIdem]
  unfold gprMulVal
  rw [gprPre, gprPre, show iMulRs1 = iMulRd from by decide +kernel, hrd, hra]

/-- C.ADD sp, a0 (expanded), at `pc_e6`. -/
theorem WkEntryNew.regExecE6 (rdv rav : BitVec 64) :
    RegExec (.RTYPE (.Regidx rs2CaddB, .Regidx rsdCaddB, .Regidx rsdCaddB, .ADD)) pcE6
      (BitVec.addInt pcE6 2) pcE7 rsdCaddB rs2CaddB rdv rav (rdv + rav) (fun _ => True) := by
  intro s b _ _ hrd hra _
  rw [execEffExecuteRTYPEADDGpr, ← pcE6E7, setRegIdem]
  unfold gprRdVal
  rw [gprPre, gprPre, hrd, hra]

/-- JAL ra, start, at `pc_e7`. -/
theorem WkEntryNew.regExecE7 (rdv rav : BitVec 64) :
    RegExec (.JAL (immJal, .Regidx iJal)) pcE7 (BitVec.addInt pcE7 4) pcStart iJal iJal rdv rav
      (BitVec.addInt pcE7 4) (fun _ => True) := by
  intro s b _ hpc _ _ _
  have hp : ((s.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pcE7 4)).regs .PC = pcE7 := by
    leaf_peel .PC; exact hpc
  have hn : ((s.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pcE7 4)).regs .nextPC =
      BitVec.addInt pcE7 4 := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  rw [execEffExecuteJALGpr immJal iJal ((s.setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pcE7 4)) (by decide +kernel) (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel), hp, hn, pcE7Start]

/-- Rocq's in-proof `m_mul` conversion: `i_mul_rs1` is `i_mul_rd` (a0). -/
theorem WkEntryNew.mMulEq (m : RegMap) (vStack0 mhartidIn : BitVec 64) :
    mMul m vStack0 mhartidIn = (mCaddi m vStack0 mhartidIn).set iMulRd
      (mult_to_bits_half (l := 64) mulopMul.signed_rs1 mulopMul.signed_rs2
        (mCaddi m vStack0 mhartidIn iMulRd) (mCaddi m vStack0 mhartidIn iMulRs2)
        mulopMul.result_part) := by
  unfold mMul
  rw [show iMulRs1 = iMulRd from by decide +kernel]

end regexec

/-! ## 1. THE rd = rs1 LOAD LEAF

`WeakLeafLd8.wwpLd8Leaf` takes SEPARATE `rs1`/`rd` register cells, so it cannot run `_entry`'s
`ld sp, imm(sp)` (base = destination = sp).  This is the SAME leaf -- same certificate
`wcertLoad8Base4`, same execute lemma `execEffLd8At`, same `wPEff` half `wPEffLd8`, same
window -- with the register-cell plumbing collapsed to ONE cell that is read as the base and
then overwritten with the loaded value. -/

section leafSame
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_ld8_leaf_same` (deviations 1-3). -/
theorem wwpLd8LeafSame (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rsd : BitVec 5) (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (dqv : DFrac)
    (c : MConf) (dq : DFrac) (rs1v npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt)
    (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    rsd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 8 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.LOAD (imm, .Regidx rsd, .Regidx rsd, false, 8), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.LOAD (imm, .Regidx rsd, .Regidx rsd, false, 8), dst) →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rsd (DFrac.own 1) rs1v -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8 (GF := GF) ea dqv v) ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu dq c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rsd (DFrac.own 1) v -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8 (GF := GF) ea dqv v) ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal4 hrsdnz hea hram8 hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrsdc #Hbs Hhws Hpt Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.LOAD (imm, .Regidx rsd, .Regidx rsd, false, 8)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.LOAD (imm, .Regidx rsd, .Regidx rsd, false, 8))
    (.F_Base w) (by first | rfl | decide) rfl hdecW $$ Hbs
  iapply wwpInstr gen cpu pc false (.LOAD (imm, .Regidx rsd, .Regidx rsd, false, 8)) c dq
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 8]))
    (wQFr (wQLoadW 8 ea) (some cpu.val)
      ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 8]))
    hgid haccpc hmok (fun i => (hpmp i).2)
    (wstepCertFr _ _ _ _ (wcertLoad8Base4 cpu.val pc wakPlain ea rfl)) $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  -- the ONE register the funnel does not read: this instruction's base
  icases keepPure (WeakLeafLw4.gprValid cpu _ rsd _ rs1v hrsdnz) $$ Hreg Hrsdc with ⟨%Lrsda, Hreg, Hrsdc⟩
  have Lrsd : (wflatSt σ).gpr rsd = rs1v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rsd (by decide)]
    exact Lrsda
  have hea_σ : (wflatSt σ).gpr rsd + sign_extend (m := 64) imm = ea := by rw [Lrsd]; exact hea
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree _ Lpriv Lmisa Lsec
  have lpmp_σ : pmpAllOff (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  -- ---- the certificate's precondition ----
  icases WeakLeafLw4.keepPure2 (wPEffLd8 cpu.val σ pc w rsd rsd imm ea v dqv D dst hwf Lpc0 Lpriv lpmp_σ
      Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp hal4 hnotRVC hrsdnz hea_σ hram8 hag_σ hDmi hgood hdec)
    $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  -- ---- the flat facts: the data doubleword ----
  icases keepPure (wwpLd8 σ ea dqv v hwf) $$ Hlat Hpt with ⟨%hld, Hlat, Hpt⟩
  icases keepPure (winstrUnwritten σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  icases keepPure (nvOkWpt8 cpu σ.wmImg σ.wmLog ea dqv v σ.wmWs) $$ Hlat Hpt with ⟨%hnvea, Hlat, Hpt⟩
  icases keepPure1 (wpt8Align ea dqv v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  -- ---- the run, at the FLAT state ----
  have hexf := execEffLd8At (wflatSt σ) b pc rsd rsd imm ea v hrsdnz Lpriv Lmprv Lpmm lpmp_σ Lpma Lhtif
    hea_σ halea hram8 hld.2
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rsd v
  -- ---- the two register writes the `execute` performs ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)) rsd rs1v v hrsdnz $$ Hreg Hrsdc with ⟨Hreg, Hrsdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rsd v)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, -⟩, hQeff⟩ := hQ
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  rw [hfacts.2.2.2.2]
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      apply nvHartOfWQEffOk cpu σ σ' _ hQeff hnv
      intro a ha
      rw [hQl]
      rcases weffsTouchApp _ _ a ha with ha | ha
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ pc _ a ha
        exact nvOkUnwritten _ _ _ (hunw j hj)
      · obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ ea _ a ha
        exact hnvea j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  ihave Hpt' := wwpLd8Carry σ σ' t ea dqv v ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ $$ Hpt
  iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hrsdc Hhws Hpt'
  unfold pcIs
  iframe Hpc' Hnpc

end leafSame

/-! ## 2. Small helpers for the chain -/

/-- Rocq `ram_win8`: RAM facts for an 8-byte window at a concrete address (deviation 7). -/
macro "wk_new_ram_win8" : tactic =>
  `(tactic| (intro j hj; rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    first | (exfalso; omega) | wk_entry_ram_lit))

example : ∀ j : Nat, j < 8 → inRam (WkEntryNew.entryLdEa + BitVec.ofNat 64 j) 1 := by
  wk_new_ram_win8

/-! ## 2b. THE REGISTER-ONLY FUNNEL BLOCK (Lean-only, deviation 6) -/

section regLeaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Lean-only: `pcIs` as its two cells. -/
theorem WkEntryNew.pcIsSplit (cpu : CPU) (pc : BitVec 64) :
    pcIs (GF := GF) cpu pc ⊢ Register.PC ↦ᵣ[cpu] pc ∗ Register.nextPC ↦ᵣ[cpu] pc := by
  unfold pcIs; exact .rfl

/-- Lean-only: the trivial extra resource. -/
theorem WkEntryNew.readNone (cpu : CPU) :
    ∀ (s : ExecSt) (b : Bool), regInterp (hlc := hlc) (GF := GF) cpu (s.setReg .minstret_increment b).regs ⊢
      iprop(⌜True⌝) -∗ ⌜(fun _ : RegFile => True) s.regs⌝ :=
  fun _ _ => wand_intro (pure_intro trivial)

/-- Lean-only: the `mhartid` cell (`csrr`'s operand; Rocq's in-proof `reg_valid`). -/
theorem WkEntryNew.readMhartid (cpu : CPU) (h : BitVec 64) :
    ∀ (s : ExecSt) (b : Bool), regInterp (hlc := hlc) (GF := GF) cpu (s.setReg .minstret_increment b).regs ⊢
      (Register.mhartid ↦ᵣ[cpu] h) -∗ ⌜(fun f : RegFile => f .mhartid = h) s.regs⌝ := by
  intro s b
  refine wand_intro ((reg_valid cpu _ .mhartid _ h).trans (pure_mono fun e => ?_))
  show s.regs .mhartid = h
  rw [← setMiLookup .mhartid s b (by decide)]
  exact e

/-- Lean-only: Rocq's inline register-only block of `wwp_entry` (one per instruction there),
made generic.  The instruction `i` at `pc`, fetched as `r` with trace `fe`, writes the GPR
`rd` (after a possible second `nextPC` write `tgt`) and may read the GPR `ra` and the
registers an extra owned resource `X` pins (`Rx`). -/
theorem WkEntryNew.wwpRegLeaf (gen : Nat) (cpu : CPU) (pc : BitVec 64) (isRvc : Bool)
    (i : instruction) (r : FetchResult) (fe : List Weff) (c : MConf) (dq : DFrac) (m : RegMap)
    (rd ra : BitVec 5) (npc0 npc tgt v : BitVec 64) (X : IProp GF) (Rx : RegFile → Prop)
    (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    rd ≠ 0#5 →
    ra ≠ 0#5 →
    BitVec.addInt pc (if isRvc then 2 else 4) = npc →
    fetchIsRvc r = isRvc →
    is_lpad_instruction i = false →
    winstrDec r i →
    nowriteTrace fe →
    (∀ a, weffsTouch fe a → ∃ j, j < 4 ∧ a = WeakInterp.accAddr pc j) →
    (∀ (s : ExecSt) (b : Bool),
      regInterp (hlc := hlc) (GF := GF) cpu (s.setReg .minstret_increment b).regs ⊢ X -∗ ⌜Rx s.regs⌝) →
    WkEntryNew.RegExec i pc npc tgt rd ra (m rd) (m ra) v Rx →
    (∀ σ : Wmstate, wlogWf σ.wmLog → σ.wmRegs .PC = pc → wcfgRegs σ c.pmpcfg →
      WkEntryNew.ConfC σ (wwin pc pc 0) i npc →
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
        winstrBytes (GF := GF) pc r -∗ ⌜wPEff (some cpu.val) fe σ⌝) →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gprFile cpu m -∗
      X -∗
      winstrBytes (GF := GF) pc r -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu dq c -∗
        clockCells cpu -∗
        pcIs cpu tgt -∗
        gprFile cpu (m.set rd v) -∗
        X -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hrd0 hra0 hnpc hrvc hlpad hdec hnw htouch hX hexe hP
  have hrd : rd.toNat ≠ 0 := fun h => hrd0 (BitVec.eq_of_toNat_eq h)
  have hra : ra.toNat ≠ 0 := fun h => hra0 (BitVec.eq_of_toNat_eq h)
  iintro Hm Hclk Hpc Hnpc Hfile HX #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc r $$ Hbs
  ihave #Hwi := winstrIntro (GF := GF) pc isRvc i r hlpad hrvc hdec $$ Hbs
  iapply wwpInstr gen cpu pc isRvc i c dq (wPEff (some cpu.val) fe) (wQFr wQPure (some cpu.val) fe)
    hgen haccpc hmok (fun k => (hpmp k).2) (wstepCertFr _ _ _ _ (wcertNowrite cpu.val pc fe hnw))
    $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  rw [hnpc]
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  have Lpriv : σ.wmRegs .cur_privilege = .Machine := hcfg.1
  have Lhart : σ.wmRegs .hart_state = .HART_ACTIVE () := hcfg.2.1
  -- the operand reads: `ra` (looked up and put back), then `rd` (taken out), then `X`
  icases gprFile_lookup_acc cpu m ra hra0 $$ Hfile with ⟨Hrac, Hcl⟩
  icases keepPure (WeakLeafLw4.gprValid cpu _ ra _ (m ra) hra) $$ Hreg Hrac with ⟨%Lraa, Hreg, Hrac⟩
  ihave Hfile := Hcl $$ Hrac
  icases gprFile_acc cpu m rd hrd0 $$ Hfile with ⟨Hrdc, Hfins⟩
  icases keepPure (WeakLeafLw4.gprValid cpu _ rd _ (m rd) hrd) $$ Hreg Hrdc with ⟨%Lrda, Hreg, Hrdc⟩
  icases keepPure (hX (wflatSt σ) b) $$ Hreg HX with ⟨%LRx, Hreg, HX⟩
  have Lra : (wflatSt σ).gpr ra = m ra := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b ra (by decide)]
    exact Lraa
  have Lrd : (wflatSt σ).gpr rd = m rd := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rd (by decide)]
    exact Lrda
  icases keepPure (winstrUnwritten σ pc r hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  have hc : WkEntryNew.ConfC σ (wwin pc pc 0) i npc :=
    WkEntryNew.confExec σ (wwin pc pc 0) i pc npc tgt rd ra (m rd) (m ra) v Rx hexe LRx Lpc0 Lrd Lra
      Lpriv Lhart
  icases keepPure (hP σ hwf Lpc0 hcfg hc) $$ Hlat Hbs with ⟨%HP, Hlat, -⟩
  have hexf := hexe (wflatSt σ) b LRx Lpc0 Lrd Lra Lpriv
  have hfacts := jalSexecFacts (wflatSt σ) b npc tgt rd v
  -- ---- the register writes the `execute` performs ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 npc)) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu _ .nextPC npc tgt)) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC npc).set .nextPC tgt) =
      ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC npc).setReg .nextPC tgt).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      npc).setReg .nextPC tgt) rd (m rd) v hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists (((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC npc).setReg .nextPC
    tgt).setGpr rd v)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, -⟩, hQeff⟩ := hQ
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  rw [hfacts.2.2.2.2]
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlogauth Hwsauth]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      refine nvHartOfWQEffUnwritten cpu σ σ' _ hQeff hnv (fun a ha => ?_)
      obtain ⟨j, hj, rfl⟩ := htouch a ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  ihave Hfile' := Hfins $$ %v Hrdc
  iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hfile' HX Hhws
  unfold pcIs
  iframe Hpc' Hnpc

end regLeaf

/-! ## 3. THE THEOREM: the whole weak `_entry` chain

Statement = `WpEntryNew.wp_entry` with the porting guide's spellings swapped (see the file
header); the output register file `mJal` and every register-side resource are the SC ones. -/

section entry
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]
open WkEntryNew

/-- Rocq `wwp_entry` (deviations 1-6). -/
theorem wwpEntry (gen : Nat) (cpu : CPU) (m : RegMap) (vStack0 mhartidIn : BitVec 64) (c : MConf)
    (kbs : GMapF PAddr (BitVec 8)) (ws : Wstate) (dq : DFrac) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    wkbCovers kbs →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      pcIs cpu pcE0 -∗
      gprFile cpu m -∗
      Register.mhartid ↦ᵣ[cpu] mhartidIn -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt8 (GF := GF) entryLdEa dq vStack0) ws -∗
      wkernelText (GF := GF) kbs -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) c -∗
        clockCells cpu -∗
        pcIs cpu pcStart -∗
        gprFile cpu (mJal m vStack0 mhartidIn) -∗
        Register.mhartid ↦ᵣ[cpu] mhartidIn -∗
        hartWs cpu ws' -∗
        vwpHold (wpt8 (GF := GF) entryLdEa dq vStack0) ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hcov
  iintro Hm Hclk Hpc Hfile Hmh Hhws Hpt #Htext Hcont
  -- ================= 1. AUIPC @ pcE0 (F_Base, 4-aligned) =================
  ihave #Hbs0 := winstrBytesOfText kbs pcE0 (.F_Base wAuipc) wAuipc (by decide +kernel)
    (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel) ⟨rfl, nrvcE0⟩ $$ Htext
    %(wkbWindow kbs ((KernelSyms.«_entry» : Int) + 0x0) wAuipc hcov kbE0)
  icases pcIsSplit cpu pcE0 $$ Hpc with ⟨Hpc, Hnpc⟩
  iapply wwpRegLeaf gen cpu pcE0 false (.UTYPE (immAuipc, .Regidx iAuipc, .AUIPC)) (.F_Base wAuipc)
    [.WEread WeakFetchEff.wakIfetch pcE0 4] c (DFrac.own 1) m iAuipc iAuipc pcE0
    (BitVec.addInt pcE0 4) pcE1 entrySp1 iprop(⌜True⌝) (fun _ => True) ws hgen hmok hpmp
    (by decide +kernel) (by decide +kernel) rfl rfl lpadE0 (decBase _ _ walkE0M walkE0S)
    (nowriteRead1 _ _ _) (fun a ha => weffsTouchRead14 _ _ 4 a (by omega) ha) (readNone cpu)
    (regExecE0 _ _)
    (fun σ hwf lpc hcfg hc => armBase4 cpu.val σ pcE0 wAuipc _ c.pmpcfg hpmp (by decide +kernel)
      goodE0 decE0 lpadE0 hwf lpc hcfg hc)
    $$ Hm Hclk Hpc Hnpc Hfile [] Hbs0 Hhws
  · ipureintro; trivial
  iintro %ws1 %hle1 Hm Hclk Hpc Hfile - Hhws
  ihave Hpt := wpt8Mono entryLdEa dq vStack0 ws ws1 hle1 $$ Hpt
  rw [show m.set iAuipc entrySp1 = mAuipc m from rfl]
  -- ================= 2. LOAD @ pcE1: ld sp, imm(sp) =================
  ihave #Hbs1 := winstrBytesOfText kbs pcE1 (.F_Base wLd) wLd (by decide +kernel)
    (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel) ⟨rfl, nrvcE1⟩ $$ Htext
    %(wkbWindow kbs ((KernelSyms.«_entry» : Int) + 0x4) wLd hcov kbE1)
  icases pcIsSplit cpu pcE1 $$ Hpc with ⟨Hpc, Hnpc⟩
  have hea1 : mAuipc m iLd + sign_extend (m := 64) immLd = entryLdEa := by
    unfold mAuipc
    rw [regLdAuipc, RegMap.set_same]
    rfl
  icases gprFile_acc cpu (mAuipc m) iLd (by decide +kernel) $$ Hfile with ⟨Hspc, Hfins⟩
  iapply wwpLd8LeafSame gen cpu pcE1 wLd iLd immLd entryLdEa vStack0 dq c (DFrac.own 1)
    (mAuipc m iLd) pcE1 dM dstateM ws1 hgen hmok hpmp (by decide +kernel) (by decide +kernel) hea1
    (by decide +kernel) (fun t _ _ _ hm hc => execAnyCfg _ _ walkE1M walkE1S t hm hc)
    (fun rs hp hmi hs => agreeMRegs rs hp hs hmi) dMMi goodE1 decE1
    $$ Hm Hclk Hpc Hnpc Hspc Hbs1 Hhws Hpt
  iintro %ws2 %hle2 Hm Hclk Hpc Hspc Hhws Hpt
  ihave Hfile := Hfins $$ %vStack0 Hspc
  rw [show (mAuipc m).set iLd vStack0 = mLd m vStack0 from rfl, pcE1E2]
  have hle2' : wsLe ws ws2 := wsLeTrans hle1 hle2
  -- ================= 3. C.LUI @ pcE2 (F_RVC, 4-aligned) =================
  ihave #Hbs2 := winstrBytesOfText kbs pcE2 (.F_RVC hLui) wE2 (by decide +kernel)
    (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel) ⟨subE2, rvcE2⟩ $$ Htext
    %(wkbWindow kbs ((KernelSyms.«_entry» : Int) + 0x8) wE2 hcov kbE2)
  icases pcIsSplit cpu pcE2 $$ Hpc with ⟨Hpc, Hnpc⟩
  iapply wwpRegLeaf gen cpu pcE2 true (.UTYPE (sign_extend (m := 20) immClui, .Regidx rdCluiB, .LUI))
    (.F_RVC hLui) [.WEread WeakFetchEff.wakIfetch pcE2 4] c (DFrac.own 1) (mLd m vStack0) rdCluiB
    rdCluiB pcE2 (BitVec.addInt pcE2 2) pcE3 (luival (sign_extend (m := 20) immClui)) iprop(⌜True⌝)
    (fun _ => True) ws2 hgen hmok hpmp (by decide +kernel) (by decide +kernel) rfl rfl lpadE2
    (decRvc hLui (.C_LUI (immClui, rdClui)) _ walkE2M walkE2S lpadI0E2 (fun _ => rfl))
    (nowriteRead1 _ _ _) (fun a ha => weffsTouchRead14 _ _ 4 a (by omega) ha) (readNone cpu)
    (regExecE2 _ _)
    (fun σ hwf lpc hcfg hc => armRvc4 cpu.val σ pcE2 hLui (.C_LUI (immClui, rdClui)) _ c.pmpcfg hpmp
      (by decide +kernel) goodE2 decE2 goodExpE2 (fun _ => rfl) hwf lpc hcfg hc)
    $$ Hm Hclk Hpc Hnpc Hfile [] Hbs2 Hhws
  · ipureintro; trivial
  iintro %ws3 %hle3 Hm Hclk Hpc Hfile - Hhws
  ihave Hpt := wpt8Mono entryLdEa dq vStack0 ws2 ws3 hle3 $$ Hpt
  rw [show (mLd m vStack0).set rdCluiB (luival (sign_extend (m := 20) immClui)) = mClui m vStack0
    from rfl]
  have hle3' : wsLe ws ws3 := wsLeTrans hle2' hle3
  -- ================= 4. CSRRS @ pcE3 (F_Base, 2-aligned) =================
  have hacc3 : accWf pcE3 4 := accWfOfLeb _ _ (by decide +kernel)
  ihave #Hbs3 := winstrBytesOfText kbs pcE3 (.F_Base wCsrr) wCsrr (by decide +kernel) hacc3
    (by decide +kernel) ⟨rfl, nrvcE3⟩ $$ Htext
    %(wkbWindow kbs ((KernelSyms.«_entry» : Int) + 0xa) wCsrr hcov kbE3)
  icases pcIsSplit cpu pcE3 $$ Hpc with ⟨Hpc, Hnpc⟩
  iapply wwpRegLeaf gen cpu pcE3 false (.CSRReg (csrCsrr, zreg, .Regidx iRdCsrr, .CSRRS))
    (.F_Base wCsrr)
    [.WEread WeakFetchEff.wakIfetch pcE3 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pcE3 2) 2]
    c (DFrac.own 1) (mClui m vStack0) iRdCsrr iRdCsrr pcE3 (BitVec.addInt pcE3 4) pcE4 mhartidIn
    (Register.mhartid ↦ᵣ[cpu] mhartidIn) (fun f => f .mhartid = mhartidIn) ws3 hgen hmok hpmp
    (by decide +kernel) (by decide +kernel) rfl rfl lpadE3 (decBase _ _ walkE3M walkE3S)
    (nowriteFetch2 pcE3) (fun a ha => weffsTouchFetch2 _ pcE3 a hacc3 ha) (readMhartid cpu mhartidIn)
    (regExecE3 _ _ _)
    (fun σ hwf lpc hcfg hc => armBase2 cpu.val σ pcE3 wCsrr _ c.pmpcfg hpmp (by decide +kernel)
      (by decide +kernel) goodE3 decE3 lpadE3 hwf lpc hcfg hc)
    $$ Hm Hclk Hpc Hnpc Hfile Hmh Hbs3 Hhws
  iintro %ws4 %hle4 Hm Hclk Hpc Hfile Hmh Hhws
  ihave Hpt := wpt8Mono entryLdEa dq vStack0 ws3 ws4 hle4 $$ Hpt
  rw [show (mClui m vStack0).set iRdCsrr mhartidIn = mCsrr m vStack0 mhartidIn from rfl]
  have hle4' : wsLe ws ws4 := wsLeTrans hle3' hle4
  -- ================= 5. C.ADDI @ pcE4 (F_RVC, 2-aligned) =================
  ihave #Hbs4 := winstrBytesOfText kbs pcE4 (.F_RVC hAddi) wE4 (by decide +kernel)
    (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel) ⟨subE4, rvcE4⟩ $$ Htext
    %(wkbWindow kbs ((KernelSyms.«_entry» : Int) + 0xe) wE4 hcov kbE4)
  icases pcIsSplit cpu pcE4 $$ Hpc with ⟨Hpc, Hnpc⟩
  iapply wwpRegLeaf gen cpu pcE4 true
    (.ITYPE (sign_extend (m := 12) immCaddi, .Regidx rsdCaddiB, .Regidx rsdCaddiB, .ADDI))
    (.F_RVC hAddi) [.WEread WeakFetchEff.wakIfetch pcE4 2] c (DFrac.own 1)
    (mCsrr m vStack0 mhartidIn) rsdCaddiB rsdCaddiB pcE4 (BitVec.addInt pcE4 2) pcE5
    (mCsrr m vStack0 mhartidIn rsdCaddiB + sign_extend (m := 64) immCaddi) iprop(⌜True⌝)
    (fun _ => True) ws4 hgen hmok hpmp (by decide +kernel) (by decide +kernel) rfl rfl lpadE4
    (decRvc hAddi (.C_ADDI (immCaddi, rsdCaddi)) _ walkE4M walkE4S lpadI0E4 (fun _ => rfl))
    (nowriteRead1 _ _ _) (fun a ha => weffsTouchRead14 _ _ 2 a (by omega) ha) (readNone cpu)
    (regExecE4 _ _)
    (fun σ hwf lpc hcfg hc => armRvc2 cpu.val σ pcE4 hAddi (.C_ADDI (immCaddi, rsdCaddi)) _ c.pmpcfg
      hpmp (by decide +kernel) (by decide +kernel) goodE4 decE4 goodExpE4 (fun _ => rfl) hwf lpc
      hcfg hc)
    $$ Hm Hclk Hpc Hnpc Hfile [] Hbs4 Hhws
  · ipureintro; trivial
  iintro %ws5 %hle5 Hm Hclk Hpc Hfile - Hhws
  ihave Hpt := wpt8Mono entryLdEa dq vStack0 ws4 ws5 hle5 $$ Hpt
  rw [show (mCsrr m vStack0 mhartidIn).set rsdCaddiB
      (mCsrr m vStack0 mhartidIn rsdCaddiB + sign_extend (m := 64) immCaddi) =
    mCaddi m vStack0 mhartidIn from rfl]
  have hle5' : wsLe ws ws5 := wsLeTrans hle4' hle5
  -- ================= 6. MUL @ pcE5 (F_Base, 4-aligned) =================
  ihave #Hbs5 := winstrBytesOfText kbs pcE5 (.F_Base wMul) wMul (by decide +kernel)
    (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel) ⟨rfl, nrvcE5⟩ $$ Htext
    %(wkbWindow kbs ((KernelSyms.«_entry» : Int) + 0x10) wMul hcov kbE5)
  icases pcIsSplit cpu pcE5 $$ Hpc with ⟨Hpc, Hnpc⟩
  iapply wwpRegLeaf gen cpu pcE5 false (.MUL (.Regidx iMulRs2, .Regidx iMulRs1, .Regidx iMulRd, mulopMul))
    (.F_Base wMul) [.WEread WeakFetchEff.wakIfetch pcE5 4] c (DFrac.own 1)
    (mCaddi m vStack0 mhartidIn) iMulRd iMulRs2 pcE5 (BitVec.addInt pcE5 4) pcE6
    (mult_to_bits_half (l := 64) mulopMul.signed_rs1 mulopMul.signed_rs2
      (mCaddi m vStack0 mhartidIn iMulRd) (mCaddi m vStack0 mhartidIn iMulRs2) mulopMul.result_part)
    iprop(⌜True⌝) (fun _ => True) ws5 hgen hmok hpmp (by decide +kernel) (by decide +kernel) rfl rfl
    lpadE5 (decBase _ _ walkE5M walkE5S) (nowriteRead1 _ _ _)
    (fun a ha => weffsTouchRead14 _ _ 4 a (by omega) ha) (readNone cpu) (regExecE5 _ _)
    (fun σ hwf lpc hcfg hc => armBase4 cpu.val σ pcE5 wMul _ c.pmpcfg hpmp (by decide +kernel)
      goodE5 decE5 lpadE5 hwf lpc hcfg hc)
    $$ Hm Hclk Hpc Hnpc Hfile [] Hbs5 Hhws
  · ipureintro; trivial
  iintro %ws6 %hle6 Hm Hclk Hpc Hfile - Hhws
  ihave Hpt := wpt8Mono entryLdEa dq vStack0 ws5 ws6 hle6 $$ Hpt
  rw [← mMulEq]
  have hle6' : wsLe ws ws6 := wsLeTrans hle5' hle6
  -- ================= 7. C.ADD @ pcE6 (F_RVC, 4-aligned) =================
  ihave #Hbs6 := winstrBytesOfText kbs pcE6 (.F_RVC hAdd) wE6 (by decide +kernel)
    (accWfOfLeb _ _ (by decide +kernel)) (by decide +kernel) ⟨subE6, rvcE6⟩ $$ Htext
    %(wkbWindow kbs ((KernelSyms.«_entry» : Int) + 0x14) wE6 hcov kbE6)
  icases pcIsSplit cpu pcE6 $$ Hpc with ⟨Hpc, Hnpc⟩
  iapply wwpRegLeaf gen cpu pcE6 true
    (.RTYPE (.Regidx rs2CaddB, .Regidx rsdCaddB, .Regidx rsdCaddB, .ADD))
    (.F_RVC hAdd) [.WEread WeakFetchEff.wakIfetch pcE6 4] c (DFrac.own 1)
    (mMul m vStack0 mhartidIn) rsdCaddB rs2CaddB pcE6 (BitVec.addInt pcE6 2) pcE7
    (mMul m vStack0 mhartidIn rsdCaddB + mMul m vStack0 mhartidIn rs2CaddB) iprop(⌜True⌝)
    (fun _ => True) ws6 hgen hmok hpmp (by decide +kernel) (by decide +kernel) rfl rfl lpadE6
    (decRvc hAdd (.C_ADD (rsdCadd, rs2Cadd)) _ walkE6M walkE6S lpadI0E6 (fun _ => rfl))
    (nowriteRead1 _ _ _) (fun a ha => weffsTouchRead14 _ _ 4 a (by omega) ha) (readNone cpu)
    (regExecE6 _ _)
    (fun σ hwf lpc hcfg hc => armRvc4 cpu.val σ pcE6 hAdd (.C_ADD (rsdCadd, rs2Cadd)) _ c.pmpcfg hpmp
      (by decide +kernel) goodE6 decE6 goodExpE6 (fun _ => rfl) hwf lpc hcfg hc)
    $$ Hm Hclk Hpc Hnpc Hfile [] Hbs6 Hhws
  · ipureintro; trivial
  iintro %ws7 %hle7 Hm Hclk Hpc Hfile - Hhws
  ihave Hpt := wpt8Mono entryLdEa dq vStack0 ws6 ws7 hle7 $$ Hpt
  rw [show (mMul m vStack0 mhartidIn).set rsdCaddB
      (mMul m vStack0 mhartidIn rsdCaddB + mMul m vStack0 mhartidIn rs2CaddB) =
    mCadd m vStack0 mhartidIn from rfl]
  have hle7' : wsLe ws ws7 := wsLeTrans hle6' hle7
  -- ================= 8. JAL @ pcE7 (F_Base, 2-aligned) =================
  have hacc7 : accWf pcE7 4 := accWfOfLeb _ _ (by decide +kernel)
  ihave #Hbs7 := winstrBytesOfText kbs pcE7 (.F_Base wJal) wJal (by decide +kernel) hacc7
    (by decide +kernel) ⟨rfl, nrvcE7⟩ $$ Htext
    %(wkbWindow kbs ((KernelSyms.«_entry» : Int) + 0x16) wJal hcov kbE7)
  icases pcIsSplit cpu pcE7 $$ Hpc with ⟨Hpc, Hnpc⟩
  iapply wwpRegLeaf gen cpu pcE7 false (.JAL (immJal, .Regidx iJal)) (.F_Base wJal)
    [.WEread WeakFetchEff.wakIfetch pcE7 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pcE7 2) 2]
    c (DFrac.own 1) (mCadd m vStack0 mhartidIn) iJal iJal pcE7 (BitVec.addInt pcE7 4) pcStart
    (BitVec.addInt pcE7 4) iprop(⌜True⌝) (fun _ => True) ws7 hgen hmok hpmp (by decide +kernel)
    (by decide +kernel) rfl rfl lpadE7 (decBase _ _ walkE7M walkE7S) (nowriteFetch2 pcE7)
    (fun a ha => weffsTouchFetch2 _ pcE7 a hacc7 ha) (readNone cpu) (regExecE7 _ _)
    (fun σ hwf lpc hcfg hc => armBase2 cpu.val σ pcE7 wJal _ c.pmpcfg hpmp (by decide +kernel)
      (by decide +kernel) goodE7 decE7 lpadE7 hwf lpc hcfg hc)
    $$ Hm Hclk Hpc Hnpc Hfile [] Hbs7 Hhws
  · ipureintro; trivial
  iintro %ws8 %hle8 Hm Hclk Hpc Hfile - Hhws
  ihave Hpt := wpt8Mono entryLdEa dq vStack0 ws7 ws8 hle8 $$ Hpt
  rw [show (mCadd m vStack0 mhartidIn).set iJal (BitVec.addInt pcE7 4) = mJal m vStack0 mhartidIn
    from rfl]
  iapply Hcont $$ %ws8 %(wsLeTrans hle7' hle8) Hm Hclk Hpc Hfile Hmh Hhws Hpt

end entry

end Weak
