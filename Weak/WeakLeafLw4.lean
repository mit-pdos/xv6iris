/-
Weak: **the `lw`/`lwu`-class 4-byte LOAD leaf** (M4 batch 2) -- from the M-mode
config bundle, the PC cell, the weak instruction bytes and the owned four data
bytes (`WeakInstr.wpt4`) to `WWP Loop`.  Nothing about the weak machine is left
as a premise: no certificate, no `wPEff`, no `exec`/`execEff` fact.

Rocq: `iris/WeakLeafLw4.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The width-4 replay of `WeakLeafLd8`.
* THE CERTIFICATE IS FREE: width 4 is `WeakCert`'s native width, and
  `WeakFetchEff.wcertLoadBase4` already states `wcertLoad` at the concrete
  fetch element this tree produces -- so there is no §1.
* THE SIGN FLAG IS FREE: `WeakLeafBase4.execEffExecuteLOAD4Gpr` leaves the
  `is_unsigned` bit `u` a variable, so ONE leaf covers `lw` (`u = false`) and
  `lwu` (`u = true`); the written value is `extend_value u v` (a real extension
  at width 4).
* THE RESOURCE IS `↦w₄`: `WeakInstr.wpt4` with its `wwpLw4`/`wwpLw4Carry` kit.
* THE WINDOW IS 4+4: the shared kit's `WeakLeafWin.wwin pc ea 4` with its
  lemmas and the register helpers (`leaf_peel`, `loadSexecFacts`, `wpt4Align`).
Assembled from `WeakFunnel.wwpInstr` (the funnel), `WeakFetchEff.wPEffOfLeafBase`
(the recipe), `WeakLeafBase4.execEffExecuteLOAD4Gpr` (the shape, trace
`[.WEread wakPlain ea 4]`) and `WeakInstr`'s `↦w₄` tower.  Every pure/geometry
side condition is a premise (alignment, RAM, the decode facts, `goodb0`).

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below); as
   `Weak/WeakLeafWin.lean` deviation 1 and `Weak/WeakFetchEff.lean`
   deviation 1 (`register_lookup r s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" =
   b` ↦ `(x == 1#1) = b`, `set_reg` ↦ `ExecSt.setReg`, `add_vec_int` ↦
   `BitVec.addInt`, `mword n`/`bv n` ↦ `BitVec n`, `pa_add a j` ↦
   `a + BitVec.ofNat 64 j`, `MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)`
   ↦ `⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩`, `ws_le` ↦ `wsLe`, `hart_ws` ↦
   `hartWs`, `vwp_hold` ↦ `vwpHold`).
2. GPRs (the ExecSC convention): the base operand `if uint rs1 =? 0 then
   zero_reg else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) …` is
   `s.gpr rs1` (`(wflatSt σ).gpr rs1` at a weak state); the destination write
   `set_reg … (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg x)` is
   `setGpr rd x` (equal under the kept premise `rd.toNat ≠ 0`); the GPR cells
   `R_bitvector_64 (gpr_of_Z (uint r)) ↦ᵣ x` are `MachCSL.gpr cpu r (DFrac.own 1) x`,
   read/written through the Lean-only `WeakLeafLw4.gprValid`/`WeakLeafLw4.gprUpdate`.
3. RAM / PMA / PMP (`WeakFunnel` deviation 2): `∀ j < 4, addr_is_ram (pa_add ea j)`
   ↦ `inRam ea 4`; `pma_allows_all` ↦ `pma_regions = bootPMA` (so the region is
   `ramRegion`, by `matching_pma_ram`, instead of Rocq's `pma_all_ram`
   witness); `pmp_all_off` ↦ `MachCSL.pmpAllOff`; Rocq's
   `pmp_all_off_allows_all` is inlined (`(h i).2`).  The CLINT/SIG/device side
   conditions are discharged from `inRam` (`within_clint_ram`, `devAddrRam`).
4. O2 (owner decision, `Weak/WeakFetchEff.lean` deviation 2): the fetch's trace
   element is `.WEread WeakFetchEff.wakIfetch pc 4` (Rocq `WEread wak_plain pc 4`);
   the recipe `wPEffOfLeafBase` takes the extra premises `fetchPin σ es`
   (discharged from the text bytes: `winstrTextPinned`, and `fetchFresh` of two
   reads) and `is_lpad_instruction i = false` (by computation).
5. THE CONFIG INTERFACE (owner decision Q3, `Weak/WeakFunnel.lean`
   deviation 7): Rocq `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q}
   pmpcfg0` ↦ `mConf cpu dq c ∗ clockCells cpu` (any `dq`; `pmpcfg0 :=
   c.pmpcfg`, plus the premise `MConf.mok c`); the continuation gets the same
   back.  `GenId`/`CpuId` are the explicit `gen`/`cpu`; `WWP Loop` ↦
   `wwpTriv ⊤ (WExpr.loop gen cpu)`; `pc_is` ↦ `MachCSL.pcIs`.  Because the
   clock cells are owned, the leaf hands the funnel's `mtime`/`mip` cells
   straight back (`wwpCb`'s option-A shape).
6. Rocq's decode premise `∀ t, … → exec (decode_fetch (F_Base w)) t = Some (i, t)`
   is stated over the funnel's vocabulary (`privMSU`, `misaC`, `cfgOk`,
   `decodeFetch`); the agreement premise's `agree_on D rs dst` is inlined as
   `∀ r, D r = true → rs r = dst.regs r` and `mword_of_int 0` is `0#64`.
7. Rocq's in-proof `assert (HnotRVC …)` (off `winstr_bytes`) is the Lean-only
   `WeakLeafLw4.winstrBytesNotRVC`; Rocq's `iDestruct … as %HP` (which keeps the
   spatial hypotheses) uses the Lean-only `WeakLeafLw4.keepPure2`; Rocq's
   `set_lookup_ne`-on-GPRs step is the Lean-only `WeakLeafLw4.gprSetNe`.
8. Rocq §4's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_lw4_at` `execEffLw4At`, `wP_eff_lw4`
`wPEffLw4`, `wwp_lw4_leaf` `wwpLw4Leaf` (none in the duplicated-name table).
Lean-only (file-qualified): `WeakLeafLw4.gprSetNe`, `WeakLeafLw4.gprValid`,
`WeakLeafLw4.gprUpdate`, `WeakLeafLw4.winstrBytesNotRVC`,
`WeakLeafLw4.keepPure2`.

**Dropped:** nothing (3 Rocq `Lemma`s; Lean 3 theorems + 5 Lean-only).
-/
import Weak.WeakLeafWin
import Weak.WeakLeafBase4
import Weak.WeakStore
import MachCSL.Gpr
import MachCSL.Boot

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. Lean-only helpers -/

/-- A write to a non-GPR register leaves every GPR read alone (Lean-only). -/
theorem WeakLeafLw4.gprSetNe (s : ExecSt) (r : Register) (x : RegisterType r) (i : BitVec 5)
    (h : r ∉ uxaGprs) : (s.setReg r x).gpr i = s.gpr i := by
  unfold ExecSt.gpr
  apply uxaXget_congr
  intro r' hr'
  have hne : r' ≠ r := by
    rintro rfl
    exact h hr'
  exact RegFile.set_other _ _ _ _ hne

/-- Keep the hypotheses of a two-argument pure entailment (Lean-only; Rocq's
`iDestruct … as %H` with a pure conclusion). -/
theorem WeakLeafLw4.keepPure2 {PROP : Type _} [BI PROP] {P Q R : PROP} {φ : Prop}
    (h : P ⊢ Q -∗ R -∗ ⌜φ⌝) : P ⊢ Q -∗ R -∗ ⌜φ⌝ ∗ P ∗ Q ∗ R :=
  wand_intro (wand_intro ((wand_elim (keepPure (wand_elim h))).trans (sep_mono_right sep_assoc.1)))

section helpersIris
variable {GF : BundledGFunctors} [WeakGS GF]

/-- The `F_Base` text word is not compressed (Lean-only; Rocq's in-proof
`assert`). -/
theorem WeakLeafLw4.winstrBytesNotRVC (pc : BitVec 64) (w : BitVec 32) :
    winstrBytes (GF := GF) pc (.F_Base w) ⊢ ⌜isRVC (Sail.BitVec.extractLsb w 15 0) = false⌝ := by
  unfold winstrBytes
  iintro ⟨-, -, -, %w0, %hw0, -⟩
  ipureintro
  obtain ⟨rfl, h⟩ := hw0
  exact h

end helpersIris

section helpersGpr
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A GPR cell agrees with the register file (Lean-only). -/
theorem WeakLeafLw4.gprValid (cpu : CPU) (f : RegFile) (i : BitVec 5) (dq : DFrac) (v : BitVec 64)
    (hi : i.toNat ≠ 0) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢ gpr cpu i dq v -∗ ⌜uxaXget f i = v⌝ := by
  obtain ⟨⟨n, hn⟩⟩ := i
  match n, hn, hi with
  | 0, _, hi => exact absurd rfl hi
  | 1, _, _ => exact wand_intro (reg_valid cpu f .x1 dq v)
  | 2, _, _ => exact wand_intro (reg_valid cpu f .x2 dq v)
  | 3, _, _ => exact wand_intro (reg_valid cpu f .x3 dq v)
  | 4, _, _ => exact wand_intro (reg_valid cpu f .x4 dq v)
  | 5, _, _ => exact wand_intro (reg_valid cpu f .x5 dq v)
  | 6, _, _ => exact wand_intro (reg_valid cpu f .x6 dq v)
  | 7, _, _ => exact wand_intro (reg_valid cpu f .x7 dq v)
  | 8, _, _ => exact wand_intro (reg_valid cpu f .x8 dq v)
  | 9, _, _ => exact wand_intro (reg_valid cpu f .x9 dq v)
  | 10, _, _ => exact wand_intro (reg_valid cpu f .x10 dq v)
  | 11, _, _ => exact wand_intro (reg_valid cpu f .x11 dq v)
  | 12, _, _ => exact wand_intro (reg_valid cpu f .x12 dq v)
  | 13, _, _ => exact wand_intro (reg_valid cpu f .x13 dq v)
  | 14, _, _ => exact wand_intro (reg_valid cpu f .x14 dq v)
  | 15, _, _ => exact wand_intro (reg_valid cpu f .x15 dq v)
  | 16, _, _ => exact wand_intro (reg_valid cpu f .x16 dq v)
  | 17, _, _ => exact wand_intro (reg_valid cpu f .x17 dq v)
  | 18, _, _ => exact wand_intro (reg_valid cpu f .x18 dq v)
  | 19, _, _ => exact wand_intro (reg_valid cpu f .x19 dq v)
  | 20, _, _ => exact wand_intro (reg_valid cpu f .x20 dq v)
  | 21, _, _ => exact wand_intro (reg_valid cpu f .x21 dq v)
  | 22, _, _ => exact wand_intro (reg_valid cpu f .x22 dq v)
  | 23, _, _ => exact wand_intro (reg_valid cpu f .x23 dq v)
  | 24, _, _ => exact wand_intro (reg_valid cpu f .x24 dq v)
  | 25, _, _ => exact wand_intro (reg_valid cpu f .x25 dq v)
  | 26, _, _ => exact wand_intro (reg_valid cpu f .x26 dq v)
  | 27, _, _ => exact wand_intro (reg_valid cpu f .x27 dq v)
  | 28, _, _ => exact wand_intro (reg_valid cpu f .x28 dq v)
  | 29, _, _ => exact wand_intro (reg_valid cpu f .x29 dq v)
  | 30, _, _ => exact wand_intro (reg_valid cpu f .x30 dq v)
  | 31, _, _ => exact wand_intro (reg_valid cpu f .x31 dq v)
  | k + 32, hk, _ => exact absurd hk (by omega)

/-- A full GPR cell is written together with the register file (Lean-only). -/
theorem WeakLeafLw4.gprUpdate (cpu : CPU) (s : ExecSt) (i : BitVec 5) (v0 v : BitVec 64)
    (hi : i.toNat ≠ 0) :
    regInterp (hlc := hlc) (GF := GF) cpu s.regs ⊢ gpr cpu i (DFrac.own 1) v0 -∗
      |==> (regInterp cpu (s.setGpr i v).regs ∗ gpr cpu i (DFrac.own 1) v) := by
  obtain ⟨⟨n, hn⟩⟩ := i
  match n, hn, hi with
  | 0, _, hi => exact absurd rfl hi
  | 1, _, _ => exact wand_intro (reg_update cpu s.regs .x1 v0 v)
  | 2, _, _ => exact wand_intro (reg_update cpu s.regs .x2 v0 v)
  | 3, _, _ => exact wand_intro (reg_update cpu s.regs .x3 v0 v)
  | 4, _, _ => exact wand_intro (reg_update cpu s.regs .x4 v0 v)
  | 5, _, _ => exact wand_intro (reg_update cpu s.regs .x5 v0 v)
  | 6, _, _ => exact wand_intro (reg_update cpu s.regs .x6 v0 v)
  | 7, _, _ => exact wand_intro (reg_update cpu s.regs .x7 v0 v)
  | 8, _, _ => exact wand_intro (reg_update cpu s.regs .x8 v0 v)
  | 9, _, _ => exact wand_intro (reg_update cpu s.regs .x9 v0 v)
  | 10, _, _ => exact wand_intro (reg_update cpu s.regs .x10 v0 v)
  | 11, _, _ => exact wand_intro (reg_update cpu s.regs .x11 v0 v)
  | 12, _, _ => exact wand_intro (reg_update cpu s.regs .x12 v0 v)
  | 13, _, _ => exact wand_intro (reg_update cpu s.regs .x13 v0 v)
  | 14, _, _ => exact wand_intro (reg_update cpu s.regs .x14 v0 v)
  | 15, _, _ => exact wand_intro (reg_update cpu s.regs .x15 v0 v)
  | 16, _, _ => exact wand_intro (reg_update cpu s.regs .x16 v0 v)
  | 17, _, _ => exact wand_intro (reg_update cpu s.regs .x17 v0 v)
  | 18, _, _ => exact wand_intro (reg_update cpu s.regs .x18 v0 v)
  | 19, _, _ => exact wand_intro (reg_update cpu s.regs .x19 v0 v)
  | 20, _, _ => exact wand_intro (reg_update cpu s.regs .x20 v0 v)
  | 21, _, _ => exact wand_intro (reg_update cpu s.regs .x21 v0 v)
  | 22, _, _ => exact wand_intro (reg_update cpu s.regs .x22 v0 v)
  | 23, _, _ => exact wand_intro (reg_update cpu s.regs .x23 v0 v)
  | 24, _, _ => exact wand_intro (reg_update cpu s.regs .x24 v0 v)
  | 25, _, _ => exact wand_intro (reg_update cpu s.regs .x25 v0 v)
  | 26, _, _ => exact wand_intro (reg_update cpu s.regs .x26 v0 v)
  | 27, _, _ => exact wand_intro (reg_update cpu s.regs .x27 v0 v)
  | 28, _, _ => exact wand_intro (reg_update cpu s.regs .x28 v0 v)
  | 29, _, _ => exact wand_intro (reg_update cpu s.regs .x29 v0 v)
  | 30, _, _ => exact wand_intro (reg_update cpu s.regs .x30 v0 v)
  | 31, _, _ => exact wand_intro (reg_update cpu s.regs .x31 v0 v)
  | k + 32, hk, _ => exact absurd hk (by omega)

end helpersGpr

/-! ## 1. THE CERTIFICATE -- nothing to prove

`WeakFetchEff.wcertLoadBase4` IS this leaf's certificate (at `akl := wakPlain`),
consumed directly by §3. -/

/-! ## 2. THE WINDOW AND THE `wPEff` HALF

### 2c. THE SECOND INSTANTIATION: `execEffExecuteLOAD4Gpr` at an arbitrary
`s0` with the funnel's two pre-writes on top. -/

/-- Rocq `exec_eff_lw4_at` (deviations 2, 3). -/
theorem execEffLw4At (s0 : ExecSt) (b u : Bool) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 32) :
    rd.toNat ≠ 0 →
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (s0.regs .pmpcfg_n) →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 4 = true →
    inRam ea 4 →
    (∀ j : Nat, j < 4 → s0.mem (ea + BitVec.ofNat 64 j) = some (nthByte (n := 4) v j)) →
    execEff (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4)))
      ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) =
      some (RETIRE_SUCCESS,
        ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd
          (extend_value u v),
        [.WEread wakPlain ea 4]) := by
  intro hrd lpriv lmprv lpmm lpmp lpma lhtif hea hal hram hbytes
  -- every config register, moved past the funnel's two pre-writes
  have lpriv_s : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact lpriv
  have lms_s : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .mstatus = s0.regs .mstatus := by
    leaf_peel .mstatus
  have lsec_s : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .mseccfg = s0.regs .mseccfg := by
    leaf_peel .mseccfg
  have lpmpc_s : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .pmpcfg_n = s0.regs .pmpcfg_n := by
    leaf_peel .pmpcfg_n
  have lpma_s : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .pma_regions = bootPMA := by
    leaf_peel .pma_regions; exact lpma
  have lhtif_s : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs
      .htif_tohost_base = none := by
    leaf_peel .htif_tohost_base; exact lhtif
  -- the base register
  have hea' : ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).gpr rs1 +
      sign_extend (m := 64) imm = ea := by
    rw [WeakLeafLw4.gprSetNe _ _ _ _ (by decide), WeakLeafLw4.gprSetNe _ _ _ _ (by decide)]
    exact hea
  have h := execEffExecuteLOAD4Gpr rs1 rd imm u v ramRegion
    ((s0.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) hrd lpriv_s
    (by rw [lms_s]; exact lmprv) (by rw [lsec_s]; exact lpmm)
    (by rw [hea']; exact hal)
    (by rw [hea']; exact execEffPmpCheckMachineNone _ _ _ _ (fun i => by rw [lpmpc_s]; exact (lpmp i).1))
    (by rw [hea', lpma_s]; exact matching_pma_ram ea 4 hram (by decide) (by decide))
    (by rw [hea']; exact hal)
    (by first | rfl | decide +kernel)
    (by rw [hea', within_clint_ram ea 4 hram]; rfl)
    (by
      rw [hea']
      first
      | rfl
      | (simp only [within_sig, plat_have_sig, Functions.not]; rfl))
    (by rw [hea']; exact execEffWithinHtifFalse _ 4 _ lhtif_s)
    (by rw [hea']; exact devAddrRam ea 4 hram)
    (by rw [hea']; exact hbytes)
  rw [hea'] at h
  exact h

/-! ### 2d. THE `wPEff` HALF, as a standalone lemma over the resources -/

section wPEffHalf
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `wP_eff_lw4` (deviations 2-4). -/
theorem wPEffLw4 (cid : Nat) (σ : Wmstate) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (u : Bool) (ea : PAddr) (v : BitVec 32) (dq : DFrac)
    (D : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    -- the M-mode config tower, at σ's own registers
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllOff (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (_get_Mstatus_MPRV (σ.wmRegs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (σ.wmRegs .mseccfg)) = .PMM_Disabled →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- the instruction's pure geometry
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    rd.toNat ≠ 0 →
    (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea →
    inRam ea 4 →
    -- the decode, exactly as the decode library states it
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4), dst) →
    -- the resources
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      vwpHold (wpt4 (GF := GF) ea dq v) σ.wmWs -∗
      ⌜wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 4]) σ⌝ := by
  intro hwf lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lmprv lpmm lelp hal4 hnotRVC hrd hea hram4
    hagree hDmi hgood hdec
  iintro Hlat #Hbs Hpt
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  icases keepPure (winstrBytesLookup σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure1 (wpt4Align ea dq v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  ihave %hlw := wwpLw4 σ ea dq v hwf $$ Hlat Hpt
  ipureintro
  obtain ⟨⟨haccea, hpinea⟩, hflat4⟩ := hlw
  obtain ⟨-, ⟨-, hrampc, w', ⟨hww, -⟩, htext⟩⟩ := hfok
  subst hww
  apply wPEffOfLeafBase cid σ (wwin pc ea 4) pc w (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4))
    [.WEread wakPlain ea 4] D dst hwf
    (wwinNonzero pc ea 4 (fun j hj => WeakLeafWin.inRamByte pc 4 j hrampc hj)
      (fun j hj => WeakLeafWin.inRamByte ea 4 j hram4 hj))
    (wwinPinned σ pc ea 4 haccpc haccea (fun j hj => (htp j hj).1) hpinea)
  · -- the O2 fetch pin
    refine ⟨fun ak pa n hin hif j hj => ?_, by simp [fetchFresh, weffWrites]⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, _root_.or_false,
      Weff.WEread.injEq] at hin
    rcases hin with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact (htp j hj).2
    · exact absurd hif (by decide)
  · exact lpc
  · exact lpriv
  · exact fun i => (lpmp i).2
  · exact lpma
  · exact lhtif
  · exact lhart
  · exact lmisaS
  · exact lmIE
  · exact lelp
  · exact hal4
  · exact hrampc
  · exact wwinConfText σ pc ea 4 w htext
  · exact hnotRVC
  · exact hagree
  · exact hDmi
  · exact hgood
  · exact hdec
  · first | rfl | decide
  · intro b
    have hfacts := loadSexecFacts ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 4), σ.wmDev⟩ b
      (BitVec.addInt pc 4) rd (extend_value u v)
    have hea_c : (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 4), σ.wmDev⟩ : ExecSt).gpr rs1 +
        sign_extend (m := 64) imm = ea := by
      unfold ExecSt.gpr at hea ⊢; exact hea
    have hbytes_c : ∀ j : Nat, j < 4 →
        (⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 4), σ.wmDev⟩ : ExecSt).mem (ea + BitVec.ofNat 64 j) =
          some (nthByte (n := 4) v j) :=
      wwinConfData σ pc ea 4 (k := 4) v hflat4
    have hrun := execEffLw4At ⟨σ.wmRegs, wmemRestrict σ (wwin pc ea 4), σ.wmDev⟩ b u pc rs1 rd imm ea v
      hrd lpriv lmprv lpmm lpmp lpma lhtif hea_c halea hram4 hbytes_c
    refine ⟨_, hrun, ?_, ?_, ?_⟩
    · rw [hfacts.1]; exact lhart
    · exact hfacts.2.1
    · rw [hfacts.2.2.1]; exact wmemRestrictDom σ _

end wPEffHalf

/-! ## 3. THE LEAF -/

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_lw4_leaf` (deviations 2, 3, 5, 6): `lw` at `u = false`, `lwu` at
`u = true`. -/
theorem wwpLw4Leaf (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (u : Bool) (ea : PAddr) (v : BitVec 32) (dqv : DFrac)
    (c : MConf) (dq : DFrac) (rs1v rd0 npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt)
    (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllOff c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    rs1.toNat ≠ 0 →
    rd.toNat ≠ 0 →
    rs1v + sign_extend (m := 64) imm = ea →
    inRam ea 4 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4), dst) →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      vwpHold (wpt4 (GF := GF) ea dqv v) ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu dq c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        gpr cpu rd (DFrac.own 1) (extend_value u v) -∗
        hartWs cpu ws' -∗
        vwpHold (wpt4 (GF := GF) ea dqv v) ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal4 hrs1nz hrd hea hram4 hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4)) (.F_Base w)
    (by first | rfl | decide) rfl hdecW $$ Hbs
  -- THE WHOLE config goes to the funnel: it hands the reads back
  iapply wwpInstr gen cpu pc false (.LOAD (imm, .Regidx rs1, .Regidx rd, u, 4)) c dq
    (wPEff (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 4]))
    (wQFr (wQLoad ea) (some cpu.val) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread wakPlain ea 4]))
    hgid haccpc hmok (fun i => (hpmp i).2)
    (wstepCertFr _ _ _ _ (wcertLoadBase4 cpu.val pc wakPlain ea rfl)) $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  -- the config, as the funnel read it (seam 2)
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, Lmprv, Lpmm, Lelp⟩ := hcfg
  -- the ONE register the funnel does not read: this instruction's base
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1nz) $$ Hreg Hrs1c with ⟨%Lrs1a, Hreg, Hrs1c⟩
  have Lrs1 : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafLw4.gprSetNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1a
  -- the effective address, at σ's own register file
  have hea_σ : (wflatSt σ).gpr rs1 + sign_extend (m := 64) imm = ea := by rw [Lrs1]; exact hea
  -- the agreement, at σ's registers
  have hag_σ : ∀ r, D r = true → σ.wmRegs r = dst.regs r := hagree _ Lpriv Lmisa Lsec
  have lpmp_σ : pmpAllOff (σ.wmRegs .pmpcfg_n) := by rw [Lpmpc]; exact hpmp
  -- ---- the certificate's precondition (§2d) ----
  icases WeakLeafLw4.keepPure2 (wPEffLw4 cpu.val σ pc w rs1 rd imm u ea v dqv D dst hwf Lpc0 Lpriv lpmp_σ
      Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp hal4 hnotRVC hrd hea_σ hram4 hag_σ hDmi hgood hdec)
    $$ Hlat Hbs Hpt with ⟨%HP, Hlat, -, Hpt⟩
  -- ---- the flat facts: the data word ----
  icases keepPure (wwpLw4 σ ea dqv v hwf) $$ Hlat Hpt with ⟨%hlw, Hlat, Hpt⟩
  icases keepPure (winstrUnwritten σ pc (.F_Base w) hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  icases keepPure (nvOkWpt4 cpu σ.wmImg σ.wmLog ea dqv v σ.wmWs) $$ Hlat Hpt with ⟨%hnvea, Hlat, Hpt⟩
  icases keepPure1 (wpt4Align ea dqv v σ.wmWs) $$ Hpt with ⟨%halea, Hpt⟩
  -- ---- the run, at the FLAT state ----
  have hexf := execEffLw4At (wflatSt σ) b u pc rs1 rd imm ea v hrd Lpriv Lmprv Lpmm lpmp_σ Lpma Lhtif
    hea_σ halea hram4 hlw.2
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rd (extend_value u v)
  -- ---- the two register writes the `execute` performs ----
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)) rd rd0 (extend_value u v) hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd
    (extend_value u v))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  -- the device frame (seam 1): the `execute` moved no device
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, -⟩, hQeff⟩ := hQ
  -- the hart's own view cell moves to σ''s
  imod hartWsUpdate cpu σ.wmWs σ.wmWs σ'.wmWs $$ [$Hwsauth $Hhws] with ⟨Hwsauth, Hhws⟩
  imod Hclose
  -- the PC the funnel hands back IS `pc+4`
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
  -- the config comes back WHOLE from the funnel: nothing to recombine
  ihave Hpt' := wwpLw4Carry σ σ' t ea dqv v ⟨hregs, hdevs, hmems, himgs, hlogs, hwsle, hwf', hbnd'⟩ $$ Hpt
  iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hrs1c Hrdc Hhws Hpt'
  unfold pcIs
  iframe Hpc' Hnpc

end leaf

end Weak
