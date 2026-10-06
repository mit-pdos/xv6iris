/-
Weak: **the BOOT-PATH csrw leaves: satp / sie / pmpaddr0** (M4).

Rocq: `iris/WeakLeafCsrw3.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The third register-only csrw batch, and the
last three the `start()` boot path needs.  Each section is the batch-2
register-only template with the cell and value names substituted; what
differs per CSR is only the `write_CSR` cone underneath:
* §1 satp (0x180) -- the deepest cone: `legalize_satp`'s mode dispatch runs
  `currentlyEnabled` at four Sv extensions, and `write_CSR` first asks
  `architecture Supervisor` (so the SXL fact `mstatus.SXL = 64` is a premise).
* §2 sie (0x104) -- `legalize_sie` is pure but `write_CSR` READS `mideleg`
  and WRITES `mie`.
* §3 pmpaddr0 (0x3b0) -- writes the `pmpaddr_n` VECTOR register with a value
  that reads `pmpcfg_n` for the lock check (`pmpcfg_n` is pinned by the
  funnel's `wcfgRegs`).
* §4 the three leaves.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WeakLeafCsrw.lean` deviation 1 (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `mword n` ↦ `BitVec n`, `set_reg` ↦ `ExecSt.setReg`, `uint x` ↦ `x.toNat`,
   `add_vec_int` ↦ `BitVec.addInt`, `'b"10"` ↦ `2#2`, `vec_access_dec v i` ↦
   `v[i]!`, `vec_update_dec` ↦ `Sail.vectorUpdate`); the CSR numbers are the
   literals `0x180#12` / `0x104#12` / `0x3B0#12`; the GPR operand read is
   `s.gpr rs1` (equal to Rocq's `register_lookup (R_bitvector_64 …)` under
   the kept premise `rs1.toNat ≠ 0`).
2. §1a: `hartSupports` is pure in Lean (`WeakLeafEffCommon` deviation 9), so
   `exec_eff_hartSupports_Sv48`/`_Sv57` are `hartSupports .Ext_Sv48 = true`
   etc.  Lean's `currentlyEnabled` has no fuel, so Rocq's Ltac
   `crush_rec_cE_S_eff` (discharging the fuelled `_rec_currentlyEnabled
   Ext_S`) has no counterpart: its job is one rewrite with
   `WeakLeafEffCommon.execEffCurrentlyEnabledS`.
3. The pure definitions Rocq reuses from `WpGprCsrwB` (`satp_legalized`,
   `sie_new_mie`, `pmp0_newaddr`, and the lemma `satp_ppn_mask_id`) have no
   Lean twin in the tree; they are the Lean-only (file-qualified)
   `WeakLeafCsrw3.satpLegalized`, `WeakLeafCsrw3.sieNewMie`,
   `WeakLeafCsrw3.pmp0Newaddr`, `WeakLeafCsrw3.satpPpnMaskId` (same bodies;
   `pmp0Newaddr`'s TOR index is the model's `Int` index `0 + 1`).
4. `write_CSR` is MachCSL's per-CSR equations (`write_CSR_satp`, …) instead
   of `skip_csr_false_clauses_eff` (`WeakLeafCsrw` deviation 3); the
   check-kit side goals Rocq closes by `vm_compute` are closed by
   `csr_dispatch_eq` on the closed monadic term (Lean-only
   `WeakLeafCsrw3.execEffOfEqPure`) or `decide`.
   `exec_eff_pmpReadAddrReg_0`'s result is `(s.regs .pmpaddr_n)[0]!`.
5. THE LEAVES (§4), the config interface (owner decision Q3, `WeakFunnel`
   deviation 7, `WeakFunnelCfg` deviation 2).  In Lean the written cells
   (`satp`, `mie`, `pmpaddr_n`) and the read cell `mideleg` live INSIDE
   `mConf` (Rocq: separate `↦ᵣ` cells beside `mmode_config (DfracOwn q)`), so
   a leaf that writes one cannot run through `WeakFunnel.wwpInstr` (which
   holds `mConf` across the step at fraction `dq`).  Each leaf therefore
   takes `mConf cpu (DFrac.own 1) c ∗ clockCells cpu` (Rocq `mmode_config
   (DfracOwn q) ∗ pmpcfg_n ↦ᵣ{q} pmpcfg0 ∗ <csr cells>`; `pmpcfg0 :=
   c.pmpcfg`, `satp0 := c.satp`, `mie0 := c.mie`, `mdl0 := c.mideleg`,
   `pmpaddr00 := c.pmpaddr`; `q := 1`), unbundles it (`mconf_cases`), runs
   `WeakFunnelCfg.wwpInstrConfig` at `ms0 := c.mstatus` (the premise
   `MConf.mok c` supplies MIE/MPRV), and rebuilds `mConf cpu (DFrac.own 1)
   {c with <csr> := <new value>}` (`mConf_introW`) for the continuation (Rocq:
   the same `mmode_config` plus the updated cell).  satp: Rocq's half-split
   of `mmode_config` (to read `mstatus.SXL` off the kept half) is not needed
   -- `c.mstatus` is known, and the SXL fact is the premise
   `_get_Mstatus_SXL c.mstatus = 2#2` (Rocq: read off `mmode_config`).
   Otherwise as `WeakLeafCsrw` deviation 5 (`gen`/`cpu` explicit, `WWP Loop`
   ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`, `hart_ws` ↦ `hartWs`, `pc_is` ↦
   `pcIs`, GPR cells `gpr cpu rs1 (DFrac.own 1) rs1v`, decode premises over
   the funnel's vocabulary, the `regstate` agreement premise over `RegFile`).
   The certificate is `wcertRegonly al4` (fetch elements
   `.WEread WeakFetchEff.wakIfetch …`, O2); its `fetchPin` obligation comes
   from `winstrTextPinned` (Lean-only `WeakLeafCsrw3.fetchPinRegonly`).
6. Lean-only (file-qualified) shared cores: `WeakLeafCsrw3.execEffSatpAt`,
   `WeakLeafCsrw3.execEffSieAt`, `WeakLeafCsrw3.execEffPmpaddr0At` (the
   `execute` at a pre-written state, used at the leaf's confined and flat
   states; Rocq inlines them twice per leaf), `WeakLeafCsrw3.mieOfMok`,
   `WeakLeafCsrw3.mprvOfMok`.
7. Rocq §5's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_hartSupports_Sv48`
`execEffHartSupportsSv48`, `exec_eff_hartSupports_Sv57`
`execEffHartSupportsSv57`, `crush_rec_cE_S_eff` (Ltac; deviation 2),
`exec_eff_currentlyEnabled_Svbare` `execEffCurrentlyEnabledSvbare`,
`exec_eff_currentlyEnabled_Sv39w` `execEffCurrentlyEnabledSv39w`,
`exec_eff_currentlyEnabled_Sv48w` `execEffCurrentlyEnabledSv48w`,
`exec_eff_currentlyEnabled_Sv57w` `execEffCurrentlyEnabledSv57w`,
`exec_eff_architecture_Supervisor_sxl` `execEffArchitectureSupervisorSxl`,
`exec_eff_legalize_satp_rv64` `execEffLegalizeSatpRv64`,
`exec_eff_write_CSR_satp` `execEffWriteCSRSatp`,
`exec_eff_csr_id_write_callback_satp` `execEffCsrIdWriteCallbackSatp`,
`exec_eff_is_CSR_accessible_satp` `execEffIsCSRAccessibleSatp`,
`exec_eff_execute_csrw_satp` `execEffExecuteCsrwSatp`,
`exec_eff_write_CSR_sie` `execEffWriteCSRSie`,
`exec_eff_csr_id_write_callback_sie` `execEffCsrIdWriteCallbackSie`,
`exec_eff_execute_csrw_sie` `execEffExecuteCsrwSie`,
`exec_eff_pmpWriteAddrReg_0` `execEffPmpWriteAddrReg0`,
`exec_eff_pmpReadAddrReg_0` `execEffPmpReadAddrReg0`,
`exec_eff_pmpReadAddrReg_0_ok` `execEffPmpReadAddrReg0Ok`,
`exec_eff_write_CSR_pmpaddr0` `execEffWriteCSRPmpaddr0`,
`exec_eff_csr_id_write_callback_pmpaddr0` `execEffCsrIdWriteCallbackPmpaddr0`,
`exec_eff_execute_csrw_pmpaddr0` `execEffExecuteCsrwPmpaddr0`,
`wwp_csrw_satp_leaf` `wwpCsrwSatpLeaf`, `wwp_csrw_sie_leaf` `wwpCsrwSieLeaf`,
`wwp_csrw_pmpaddr0_leaf` `wwpCsrwPmpaddr0Leaf` (none in the duplicated-name
table).  Lean-only: deviations 3, 4, 5, 6.

**Dropped:** nothing (24 Rocq `Lemma`s + 1 `Ltac`; Lean 24 theorems, the Ltac
replaced per deviation 2, plus 11 Lean-only: 3 defs + 8 theorems).
-/
import Weak.WeakLeafCsrw
import Weak.WeakLeafRegOnly
import MachCSL.WpCsrFacts
import MachCSL.MConf

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. Lean-only helpers and the pure values (deviation 3) -/

/-- A closed computation that IS `pure x` runs silently (Lean-only). -/
theorem WeakLeafCsrw3.execEffOfEqPure {X : Type} (m : SailM X) (x : X) (s : ExecSt)
    (h : m = pure x) : execEff m s = some (x, s, []) := by
  rw [h]; rfl

/-- Rocq `WpGprCsrwB.satp_legalized`. -/
def WeakLeafCsrw3.satpLegalized (prev value : BitVec 64) : BitVec 64 :=
  match satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 value)) with
  | some .Bare => Mk_Satp64 value
  | some .Sv39 => Mk_Satp64 value
  | some .Sv48 => Mk_Satp64 value
  | some .Sv57 => Mk_Satp64 value
  | some .Sv32 => prev
  | none => prev

/-- Rocq `WpGprCsrwB.sie_new_mie`. -/
def WeakLeafCsrw3.sieNewMie (mie0 mdl0 v : BitVec 64) : BitVec 64 := legalize_sie mie0 mdl0 v

/-- Rocq `WpGprCsrwB.pmp0_newaddr`. -/
def WeakLeafCsrw3.pmp0Newaddr (cfg : Vector (BitVec 8) 64) (addr : Vector (BitVec 64) 64)
    (v : BitVec 64) : Vector (BitVec 64) 64 :=
  vectorUpdate addr 0
    (pmpWriteAddr (pmpLocked (GetElem?.getElem! cfg (0 : Nat)))
      (pmpTORLocked (GetElem?.getElem! cfg ((0 : Nat) +i 1))) (GetElem?.getElem! addr (0 : Nat)) v)

/-- Rocq `WpGprCsrwB.satp_ppn_mask_id`: `legalize_satp`'s PPN narrowing is
the identity (the field is 44 bits). -/
theorem WeakLeafCsrw3.satpPpnMaskId (v : BitVec 64) :
    _update_Satp64_PPN (Mk_Satp64 v)
      (zero_extend (m := 44)
        (Sail.BitVec.extractLsb (_get_Satp64_PPN (Mk_Satp64 v))
          ((Min.min ((Functions.physaddr_bits : Int) -i (Functions.pagesize_bits : Int)) 44) -i 1)
          0)) = Mk_Satp64 v := by
  show Sail.BitVec.updateSubrange v 43 0
    (BitVec.setWidth 44 (BitVec.extractLsb' 0 44 (BitVec.extractLsb' 0 44 v))) = v
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  bv_decide

/-- `MConf.mok`'s MIE bit, in the funnel's form (Lean-only). -/
theorem WeakLeafCsrw3.mieOfMok (c : MConf) (h : MConf.mok c) :
    (_get_Mstatus_MIE c.mstatus == 1#1) = false := by
  rw [get_Mstatus_MIE_eq, h.1]; decide

/-- `MConf.mok`'s MPRV bit, in the funnel's form (Lean-only). -/
theorem WeakLeafCsrw3.mprvOfMok (c : MConf) (h : MConf.mok c) :
    (_get_Mstatus_MPRV c.mstatus == 1#1) = false := by
  rw [get_Mstatus_MPRV_eq, h.2]; decide

/-- The register-only fetch trace is pinned by the text (Lean-only). -/
theorem WeakLeafCsrw3.fetchPinRegonly (σ : Wmstate) (al4 : Bool) (pc : BitVec 64)
    (hacc : accWf pc 4) (ht : ∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pc j)) :
    fetchPin σ (regonlyEs al4 pc) := by
  refine fetchPinOfText σ pc _ (fun ak pa n hin _ j hj => ?_) ?_ ht
  · exact weffsTouchRegonly al4 pc _ hacc ⟨_, hin, j, hj, rfl⟩
  · cases al4 <;> simp [regonlyEs, fetchFresh, weffWrites]

/-! ## 1. satp (0x180) -/

/-! ### 1a. The Sv extension enablement mirrors (deviation 2) -/

/-- Rocq `exec_eff_hartSupports_Sv48`. -/
theorem execEffHartSupportsSv48 : hartSupports .Ext_Sv48 = true := by decide +kernel

/-- Rocq `exec_eff_hartSupports_Sv57`. -/
theorem execEffHartSupportsSv57 : hartSupports .Ext_Sv57 = true := by decide +kernel

/-- Rocq `exec_eff_currentlyEnabled_Svbare`. -/
theorem execEffCurrentlyEnabledSvbare (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_Svbare) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [WeakLeafEffCommon.execEffCurrentlyEnabledS, hS]

/-- Rocq `exec_eff_currentlyEnabled_Sv39w`. -/
theorem execEffCurrentlyEnabledSv39w (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_Sv39) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSv39, ↓reduceIte, WeakLeafEffCommon.execEffCurrentlyEnabledS, hS]

/-- Rocq `exec_eff_currentlyEnabled_Sv48w`. -/
theorem execEffCurrentlyEnabledSv48w (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_Sv48) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSv48, ↓reduceIte, WeakLeafEffCommon.execEffCurrentlyEnabledS, hS]

/-- Rocq `exec_eff_currentlyEnabled_Sv57w`. -/
theorem execEffCurrentlyEnabledSv57w (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_Sv57) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSv57, ↓reduceIte, WeakLeafEffCommon.execEffCurrentlyEnabledS, hS]

/-- Rocq `exec_eff_architecture_Supervisor_sxl`. -/
theorem execEffArchitectureSupervisorSxl (s : ExecSt)
    (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2) :
    execEff (architecture .Supervisor) s = some (.RV64, s, []) := by
  unfold architecture
  exec_eff_steps [hsxl]
  rfl

/-! ### 1b. legalize_satp / write_CSR / check / callback -/

/-- Rocq `exec_eff_legalize_satp_rv64`. -/
theorem execEffLegalizeSatpRv64 (prev value : BitVec 64) (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (legalize_satp .RV64 prev value) s =
      some (WeakLeafCsrw3.satpLegalized prev value, s, []) := by
  unfold legalize_satp WeakLeafCsrw3.satpLegalized
  simp only []
  rw [WeakLeafCsrw3.satpPpnMaskId]
  rcases satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 value)) with _ | sv
  · rfl
  · cases sv
    · simp only []
      rw [execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledSvbare s hS)]
      rfl
    · rfl
    · simp only []
      rw [execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledSv39w s hS)]
      rfl
    · simp only []
      rw [execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledSv48w s hS)]
      rfl
    · simp only []
      rw [execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledSv57w s hS)]
      rfl

/-- Rocq `exec_eff_write_CSR_satp`. -/
theorem execEffWriteCSRSatp (v : BitVec 64) (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (hsxl : _get_Mstatus_SXL (s.regs .mstatus) = 2#2) :
    execEff (write_CSR 0x180#12 v) s =
      some (.Ok (WeakLeafCsrw3.satpLegalized (s.regs .satp) v),
        s.setReg .satp (WeakLeafCsrw3.satpLegalized (s.regs .satp) v), []) := by
  rw [write_CSR_satp]
  rw [execEffBindNil _ _ _ _ _ (execEffArchitectureSupervisorSxl s hsxl),
    execEffBindNil _ _ _ _ _ (execEffReadReg .satp s),
    execEffBindNil _ _ _ _ _ (execEffLegalizeSatpRv64 (s.regs .satp) v s hS),
    execEffBind0Nil _ _ _ _ _ (execEffWriteReg .satp _ s),
    execEffBindNil _ _ _ _ _ (execEffReadReg .satp _)]
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_satp`. -/
theorem execEffCsrIdWriteCallbackSatp (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x180#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_is_CSR_accessible_satp`. -/
theorem execEffIsCSRAccessibleSatp (s : ExecSt) :
    execEff (is_CSR_accessible 0x180#12 .Machine .CSRWrite) s = some (true, s, []) :=
  WeakLeafCsrw3.execEffOfEqPure _ _ s (by csr_dispatch_eq)

/-! ### 1c. The end-to-end satp `execute`, trace `[]` -/

/-- Rocq `exec_eff_execute_csrw_satp` (deviation 1). -/
theorem execEffExecuteCsrwSatp (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    _get_Mstatus_SXL (s.regs .mstatus) = 2#2 →
    execEff (execute (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .satp (WeakLeafCsrw3.satpLegalized (s.regs .satp) (s.gpr rs1)), []) := by
  intro _ hpriv hS hsxl
  show execEff (execute_CSRReg 0x180#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x180#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwPure _ s (WeakLeafCsrw3.execEffOfEqPure _ _ s (by csr_dispatch_eq))
      (by decide) (execEffIsCSRAccessibleSatp s)
      (WeakLeafCsrw3.execEffOfEqPure _ _ s (by csr_dispatch_eq)))
    (by decide) (by decide) (by decide)
    (execEffWriteCSRSatp _ s hS hsxl) (execEffCsrIdWriteCallbackSatp _ _)

/-! ## 2. sie (0x104; Ext_S-gated -- WRITES `mie`, READS `mideleg`) -/

/-- Rocq `exec_eff_write_CSR_sie`. -/
theorem execEffWriteCSRSie (v : BitVec 64) (s : ExecSt) :
    execEff (write_CSR 0x104#12 v) s =
      some (.Ok (lower_mie (WeakLeafCsrw3.sieNewMie (s.regs .mie) (s.regs .mideleg) v)
          (s.regs .mideleg)),
        s.setReg .mie (WeakLeafCsrw3.sieNewMie (s.regs .mie) (s.regs .mideleg) v), []) := by
  rw [write_CSR_sie]
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .mie s),
    execEffBindNil _ _ _ _ _ (execEffReadReg .mideleg s),
    execEffBind0Nil _ _ _ _ _ (execEffWriteReg .mie _ s),
    execEffBindNil _ _ _ _ _ (execEffReadReg .mie _),
    execEffBindNil _ _ _ _ _ (execEffReadReg .mideleg _)]
  rw [setLookupNe .mideleg .mie _ _ (by decide)]
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_sie`. -/
theorem execEffCsrIdWriteCallbackSie (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x104#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_execute_csrw_sie` (deviation 1). -/
theorem execEffExecuteCsrwSie (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .mie (WeakLeafCsrw3.sieNewMie (s.regs .mie) (s.regs .mideleg) (s.gpr rs1)), []) := by
  intro _ hpriv hS
  show execEff (execute_CSRReg 0x104#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x104#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwS _ s hS (WeakLeafCsrw3.execEffOfEqPure _ _ s (by csr_dispatch_eq))
      (by decide) (by csr_dispatch_eq)
      (WeakLeafCsrw3.execEffOfEqPure _ _ s (by csr_dispatch_eq)))
    (by decide) (by decide) (by decide)
    (execEffWriteCSRSie _ s) (execEffCsrIdWriteCallbackSie _ _)

/-! ## 3. pmpaddr0 (0x3B0; pure check -- WRITES `pmpaddr_n`, READS `pmpcfg_n`) -/

/-- Rocq `exec_eff_pmpWriteAddrReg_0`. -/
theorem execEffPmpWriteAddrReg0 (v : BitVec 64) (s : ExecSt) :
    execEff (pmpWriteAddrReg 0 v) s =
      some ((), s.setReg .pmpaddr_n
        (WeakLeafCsrw3.pmp0Newaddr (s.regs .pmpcfg_n) (s.regs .pmpaddr_n) v), []) := by
  unfold pmpWriteAddrReg WeakLeafCsrw3.pmp0Newaddr
  exec_eff_steps

/-- Rocq `exec_eff_pmpReadAddrReg_0` (deviation 4). -/
theorem execEffPmpReadAddrReg0 (s : ExecSt) :
    execEff (pmpReadAddrReg 0) s = some ((s.regs .pmpaddr_n)[0]!, s, []) := by
  unfold pmpReadAddrReg
  exec_eff_steps
  generalize BitVec.access _ 1 = b
  rcases (by decide : ∀ b : BitVec 1, b = 1#1 ∨ b = 0#1) b with rfl | rfl <;> rfl

/-- Rocq `exec_eff_pmpReadAddrReg_0_ok`. -/
theorem execEffPmpReadAddrReg0Ok (s : ExecSt) :
    execEff (pmpReadAddrReg 0 >>= fun w => (pure (.Ok w) : SailM (Result (BitVec 64) Unit))) s =
      some (.Ok ((s.regs .pmpaddr_n)[0]!), s, []) := by
  rw [execEffBindNil _ _ _ _ _ (execEffPmpReadAddrReg0 s)]
  rfl

/-- Rocq `exec_eff_write_CSR_pmpaddr0`. -/
theorem execEffWriteCSRPmpaddr0 (v : BitVec 64) (s : ExecSt) :
    execEff (write_CSR 0x3B0#12 v) s =
      some (.Ok (((s.setReg .pmpaddr_n
          (WeakLeafCsrw3.pmp0Newaddr (s.regs .pmpcfg_n) (s.regs .pmpaddr_n) v)).regs .pmpaddr_n)[0]!),
        s.setReg .pmpaddr_n
          (WeakLeafCsrw3.pmp0Newaddr (s.regs .pmpcfg_n) (s.regs .pmpaddr_n) v), []) := by
  rw [write_CSR_pmpaddr0]
  rw [execEffBind0Nil _ _ _ _ _ (execEffPmpWriteAddrReg0 v s)]
  exact execEffPmpReadAddrReg0Ok _

/-- Rocq `exec_eff_csr_id_write_callback_pmpaddr0`. -/
theorem execEffCsrIdWriteCallbackPmpaddr0 (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x3B0#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_execute_csrw_pmpaddr0` (deviation 1). -/
theorem execEffExecuteCsrwPmpaddr0 (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    execEff (execute (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .pmpaddr_n
          (WeakLeafCsrw3.pmp0Newaddr (s.regs .pmpcfg_n) (s.regs .pmpaddr_n) (s.gpr rs1)), []) := by
  intro _ hpriv
  show execEff (execute_CSRReg 0x3B0#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x3B0#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwPure _ s (WeakLeafCsrw3.execEffOfEqPure _ _ s (by csr_dispatch_eq))
      (by decide) (WeakLeafCsrw3.execEffOfEqPure _ _ s (by csr_dispatch_eq))
      (WeakLeafCsrw3.execEffOfEqPure _ _ s (by csr_dispatch_eq)))
    (by decide) (by decide) (by decide)
    (execEffWriteCSRPmpaddr0 _ s) (execEffCsrIdWriteCallbackPmpaddr0 _ _)

/-! ## 4. THE LEAVES -/

/-! ### The `execute`s at a pre-written state (Lean-only, deviation 6) -/

/-- csrw satp after the funnel's two pre-writes (Lean-only). -/
theorem WeakLeafCsrw3.execEffSatpAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rs1 : BitVec 5)
    (ms0 satp0 rs1v : BitVec 64) (hrs1 : rs1.toNat ≠ 0)
    (hpriv : s0.regs .cur_privilege = .Machine) (hmisa : s0.regs .misa = misaC)
    (hms : s0.regs .mstatus = ms0) (hsxl : _get_Mstatus_SXL ms0 = 2#2)
    (hcsr : s0.regs .satp = satp0) (hg : s0.gpr rs1 = rs1v) :
    execEff (execute (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setReg .satp
        (WeakLeafCsrw3.satpLegalized satp0 rs1v), []) := by
  have hmisa' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .misa = misaC := by
    leaf_peel .misa; exact hmisa
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege =
      .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hms' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .mstatus = ms0 := by
    leaf_peel .mstatus; exact hms
  have hcsr' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .satp = satp0 := by
    leaf_peel .satp; exact hcsr
  have hg' : ((s0.setReg .minstret_increment b).setReg .nextPC x).gpr rs1 = rs1v := by
    rw [WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide), WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide)]
    exact hg
  have h := execEffExecuteCsrwSatp rs1 _ hrs1 hpriv' (by rw [hmisa']; decide)
    (by rw [hms']; exact hsxl)
  rw [hcsr', hg'] at h
  exact h

/-- csrw sie after the funnel's two pre-writes (Lean-only). -/
theorem WeakLeafCsrw3.execEffSieAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rs1 : BitVec 5)
    (mie0 mdl0 rs1v : BitVec 64) (hrs1 : rs1.toNat ≠ 0)
    (hpriv : s0.regs .cur_privilege = .Machine) (hmisa : s0.regs .misa = misaC)
    (hmie : s0.regs .mie = mie0) (hmdl : s0.regs .mideleg = mdl0) (hg : s0.gpr rs1 = rs1v) :
    execEff (execute (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setReg .mie
        (WeakLeafCsrw3.sieNewMie mie0 mdl0 rs1v), []) := by
  have hmisa' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .misa = misaC := by
    leaf_peel .misa; exact hmisa
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege =
      .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hmie' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .mie = mie0 := by
    leaf_peel .mie; exact hmie
  have hmdl' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .mideleg = mdl0 := by
    leaf_peel .mideleg; exact hmdl
  have hg' : ((s0.setReg .minstret_increment b).setReg .nextPC x).gpr rs1 = rs1v := by
    rw [WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide), WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide)]
    exact hg
  have h := execEffExecuteCsrwSie rs1 _ hrs1 hpriv' (by rw [hmisa']; decide)
  rw [hmie', hmdl', hg'] at h
  exact h

/-- csrw pmpaddr0 after the funnel's two pre-writes (Lean-only). -/
theorem WeakLeafCsrw3.execEffPmpaddr0At (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rs1 : BitVec 5)
    (pmpcfg0 : RegisterType .pmpcfg_n) (pmpaddr00 : RegisterType .pmpaddr_n) (rs1v : BitVec 64)
    (hrs1 : rs1.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hcfg : s0.regs .pmpcfg_n = pmpcfg0) (haddr : s0.regs .pmpaddr_n = pmpaddr00)
    (hg : s0.gpr rs1 = rs1v) :
    execEff (execute (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setReg .pmpaddr_n
        (WeakLeafCsrw3.pmp0Newaddr pmpcfg0 pmpaddr00 rs1v), []) := by
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege =
      .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hcfg' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .pmpcfg_n = pmpcfg0 := by
    leaf_peel .pmpcfg_n; exact hcfg
  have haddr' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .pmpaddr_n =
      pmpaddr00 := by
    leaf_peel .pmpaddr_n; exact haddr
  have hg' : ((s0.setReg .minstret_increment b).setReg .nextPC x).gpr rs1 = rs1v := by
    rw [WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide), WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide)]
    exact hg
  have h := execEffExecuteCsrwPmpaddr0 rs1 _ hrs1 hpriv'
  rw [hcfg', haddr', hg'] at h
  exact h

section leaves
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-! ### 4a. csrw satp (deviation 5) -/

/-- Rocq `wwp_csrw_satp_leaf` (deviation 5). -/
theorem wwpCsrwSatpLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (rs1v npc0 : BitVec 64) (c : MConf) (D : Register → Bool) (dst : ExecSt)
    (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    _get_Mstatus_SXL c.mstatus = 2#2 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with satp := WeakLeafCsrw3.satpLegalized c.satp rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hal2 hal4 hrs1 hsxl hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  mconf_cases Hm
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hwd : winstrDec (.F_Base w) (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW)) :=
    fun t h1 h2 h3 h4 h5 => hdecf t h1 h2 h3 h4 h5
  ihave #Hi := winstrIntro pc false (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW)) (.F_Base w)
    rfl rfl hwd $$ Hbs
  -- the config-writing funnel: certificate = register-only at either alignment
  iapply wwpInstrConfig gen cpu pc false (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW)) c.pmpcfg
    c.mstatus (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgen haccpc hpmp (WeakLeafCsrw3.mieOfMok c hmok) (WeakLeafCsrw3.mprvOfMok c hmok)
    (wstepCertFr cpu.val pc _ _ (wcertRegonly al4 cpu.val pc))
    $$ Hhw Hclk Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hpc Hi
  unfold wwpCbConfig wmstateNorg
  iintro %σ %b %mt %ip %Lpc %hcfg %Lms Hpriv Hms Hpmpc Hlat Hreg ⟨%hbnd, %hnv, %hwf, Hdev, Hlog, Hwsa⟩
    Hmt Hip
  ihave ⟨%hws, Hwsa, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsa Hhws]
  · iframe Hwsa Hhws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc _ hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hram, w', hwok, htext0⟩ := hfok
  obtain ⟨hww, -⟩ := hwok
  subst hww
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the registers the funnel does not hand over: the source and the CSR
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1) $$ Hreg Hrs1c
    with ⟨%Lrs1, Hreg, Hrs1c⟩
  have Lrs1f : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafCsrw.gprSetRegNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1
  icases keepPure (wand_intro (reg_valid cpu _ .satp _ _)) $$ Hreg Hsatp with ⟨%Lcsra, Hreg, Hsatp⟩
  have Lcsr : σ.wmRegs .satp = c.satp := by
    rw [setLookupNe _ _ _ _ (by decide)] at Lcsra; exact Lcsra
  have Lsxl : _get_Mstatus_SXL c.mstatus = 2#2 := hsxl
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := csrwSexecFactsR .satp
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4)
      (WeakLeafCsrw3.satpLegalized c.satp rs1v) (by decide) (by decide) (by decide)
    refine ⟨_, WeakLeafCsrw3.execEffSatpAt _ b' _ rs1 c.mstatus c.satp rs1v hrs1 Lpriv Lmisa Lms Lsxl
      Lcsr Lrs1f, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w
      (.CSRReg (0x180#12, .Regidx rs1, zreg, .CSRRW)) D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (WeakLeafCsrw3.fetchPinRegonly σ al4 pc haccpc (fun j hj => (htp j hj).2))
      Lpc Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp hal2 hal4 hram
      (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi hgood hdec
      rfl hc
  -- the run at the FLAT state
  have Hef := WeakLeafCsrw3.execEffSatpAt (wflatSt σ) b (BitVec.addInt pc 4) rs1 c.mstatus c.satp rs1v
    hrs1 Lpriv Lmisa Lms Lsxl Lcsr Lrs1f
  obtain ⟨-, -, -, G4, G5⟩ := csrwSexecFactsR .satp (wflatSt σ) b (BitVec.addInt pc 4)
    (WeakLeafCsrw3.satpLegalized c.satp rs1v) (by decide) (by decide) (by decide)
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu ((wflatSt σ).setReg .minstret_increment b).regs .nextPC npc0
    (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu
    ((((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC (BitVec.addInt pc 4)) .satp c.satp
    (WeakLeafCsrw3.satpLegalized c.satp rs1v))) $$ Hreg Hsatp with ⟨Hreg, Hsatp⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
    .satp (WeakLeafCsrw3.satpLegalized c.satp rs1v))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ Hef
  isplitl [Hreg]
  · rw [show ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
        .satp (WeakLeafCsrw3.satpLegalized c.satp rs1v)).regs =
        ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)).set
        .satp (WeakLeafCsrw3.satpLegalized c.satp rs1v)) from rfl]
    iexact Hreg
  isplitl [Hmt Hip]
  · iexists mt, ip
    iframe Hmt Hip
  inext
  rw [G5]
  iintro %tick %σ' %t %_hstep %hdevt %hpost %hQ Hhs Hclk HPC
  obtain ⟨-, hdevs', -, -, -, -, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, hQw⟩, hQeff⟩ := hQ
  have hdev : σ'.wmDev = σ.wmDev := by rw [hdevs', hdevt]; exact G4
  imod Hclose
  imod hartWsUpdate cpu σ.wmWs ws σ'.wmWs $$ [$Hwsa $Hhws] with ⟨Hwsa, Hhws⟩
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlog Hwsa]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      refine nvHartOfWQEffUnwritten cpu σ σ' _ hQeff hnv (fun a ha => ?_)
      obtain ⟨j, hj, rfl⟩ := weffsTouchRegonly al4 pc a haccpc ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdev, hQl]
    iframe Hdev Hlog Hwsa
  · -- rebuild the config at the written value
    ihave Hm' := mConf_introW cpu (DFrac.own 1)
      { c with satp := WeakLeafCsrw3.satpLegalized c.satp rs1v } $$ Hpriv Hhs Hms Hmie Hmideleg
      Hmedeleg Hmepc Hsatp Hmenvcfg Hmcounteren Hmtimecmp Hstimecmp Hpmpc Hpmpaddr_n Hhw
    iapply Hcont $$ %σ'.wmWs %(by rw [hws]; exact hQw) Hm' Hclk [HPC Hnpc] Hrs1c Hhws
    unfold pcIs
    iframe HPC Hnpc

/-! ### 4b. csrw sie (deviation 5): writes `mie`, reads `mideleg` -/

/-- Rocq `wwp_csrw_sie_leaf` (deviation 5). -/
theorem wwpCsrwSieLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (rs1v npc0 : BitVec 64) (c : MConf) (D : Register → Bool) (dst : ExecSt)
    (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with mie := WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hal2 hal4 hrs1 hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  mconf_cases Hm
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hwd : winstrDec (.F_Base w) (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)) :=
    fun t h1 h2 h3 h4 h5 => hdecf t h1 h2 h3 h4 h5
  ihave #Hi := winstrIntro pc false (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)) (.F_Base w)
    rfl rfl hwd $$ Hbs
  -- the config-writing funnel: certificate = register-only at either alignment
  iapply wwpInstrConfig gen cpu pc false (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)) c.pmpcfg
    c.mstatus (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgen haccpc hpmp (WeakLeafCsrw3.mieOfMok c hmok) (WeakLeafCsrw3.mprvOfMok c hmok)
    (wstepCertFr cpu.val pc _ _ (wcertRegonly al4 cpu.val pc))
    $$ Hhw Hclk Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hpc Hi
  unfold wwpCbConfig wmstateNorg
  iintro %σ %b %mt %ip %Lpc %hcfg %Lms Hpriv Hms Hpmpc Hlat Hreg ⟨%hbnd, %hnv, %hwf, Hdev, Hlog, Hwsa⟩
    Hmt Hip
  ihave ⟨%hws, Hwsa, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsa Hhws]
  · iframe Hwsa Hhws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc _ hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hram, w', hwok, htext0⟩ := hfok
  obtain ⟨hww, -⟩ := hwok
  subst hww
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the registers the funnel does not hand over: the source and the CSR
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1) $$ Hreg Hrs1c
    with ⟨%Lrs1, Hreg, Hrs1c⟩
  have Lrs1f : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafCsrw.gprSetRegNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1
  icases keepPure (wand_intro (reg_valid cpu _ .mie _ _)) $$ Hreg Hmie with ⟨%Lmiea, Hreg, Hmie⟩
  have Lmie : σ.wmRegs .mie = c.mie := by
    rw [setLookupNe _ _ _ _ (by decide)] at Lmiea; exact Lmiea
  icases keepPure (wand_intro (reg_valid cpu _ .mideleg _ _)) $$ Hreg Hmideleg
    with ⟨%Lmdla, Hreg, Hmideleg⟩
  have Lmdl : σ.wmRegs .mideleg = c.mideleg := by
    rw [setLookupNe _ _ _ _ (by decide)] at Lmdla; exact Lmdla
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := csrwSexecFactsR .mie
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4)
      (WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v) (by decide) (by decide) (by decide)
    refine ⟨_, WeakLeafCsrw3.execEffSieAt _ b' _ rs1 c.mie c.mideleg rs1v hrs1 Lpriv Lmisa Lmie Lmdl
      Lrs1f, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w
      (.CSRReg (0x104#12, .Regidx rs1, zreg, .CSRRW)) D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (WeakLeafCsrw3.fetchPinRegonly σ al4 pc haccpc (fun j hj => (htp j hj).2))
      Lpc Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp hal2 hal4 hram
      (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi hgood hdec
      rfl hc
  -- the run at the FLAT state
  have Hef := WeakLeafCsrw3.execEffSieAt (wflatSt σ) b (BitVec.addInt pc 4) rs1 c.mie c.mideleg rs1v
    hrs1 Lpriv Lmisa Lmie Lmdl Lrs1f
  obtain ⟨-, -, -, G4, G5⟩ := csrwSexecFactsR .mie (wflatSt σ) b (BitVec.addInt pc 4)
    (WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v) (by decide) (by decide) (by decide)
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu ((wflatSt σ).setReg .minstret_increment b).regs .nextPC npc0
    (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu
    ((((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC (BitVec.addInt pc 4)) .mie c.mie
    (WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v))) $$ Hreg Hmie with ⟨Hreg, Hmie⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
    .mie (WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ Hef
  isplitl [Hreg]
  · rw [show ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
        .mie (WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v)).regs =
        ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)).set
        .mie (WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v)) from rfl]
    iexact Hreg
  isplitl [Hmt Hip]
  · iexists mt, ip
    iframe Hmt Hip
  inext
  rw [G5]
  iintro %tick %σ' %t %_hstep %hdevt %hpost %hQ Hhs Hclk HPC
  obtain ⟨-, hdevs', -, -, -, -, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, hQw⟩, hQeff⟩ := hQ
  have hdev : σ'.wmDev = σ.wmDev := by rw [hdevs', hdevt]; exact G4
  imod Hclose
  imod hartWsUpdate cpu σ.wmWs ws σ'.wmWs $$ [$Hwsa $Hhws] with ⟨Hwsa, Hhws⟩
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlog Hwsa]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      refine nvHartOfWQEffUnwritten cpu σ σ' _ hQeff hnv (fun a ha => ?_)
      obtain ⟨j, hj, rfl⟩ := weffsTouchRegonly al4 pc a haccpc ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdev, hQl]
    iframe Hdev Hlog Hwsa
  · -- rebuild the config at the written value
    ihave Hm' := mConf_introW cpu (DFrac.own 1)
      { c with mie := WeakLeafCsrw3.sieNewMie c.mie c.mideleg rs1v } $$ Hpriv Hhs Hms Hmie Hmideleg
      Hmedeleg Hmepc Hsatp Hmenvcfg Hmcounteren Hmtimecmp Hstimecmp Hpmpc Hpmpaddr_n Hhw
    iapply Hcont $$ %σ'.wmWs %(by rw [hws]; exact hQw) Hm' Hclk [HPC Hnpc] Hrs1c Hhws
    unfold pcIs
    iframe HPC Hnpc

/-! ### 4c. csrw pmpaddr0 (deviation 5): writes `pmpaddr_n`; the `pmpcfg_n` it reads is
the funnel's own (`wcfgRegs`) -/

/-- Rocq `wwp_csrw_pmpaddr0_leaf` (deviation 5). -/
theorem wwpCsrwPmpaddr0Leaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (rs1v npc0 : BitVec 64) (c : MConf) (D : Register → Bool) (dst : ExecSt)
    (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with pmpaddr := WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hal2 hal4 hrs1 hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  mconf_cases Hm
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hwd : winstrDec (.F_Base w) (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)) :=
    fun t h1 h2 h3 h4 h5 => hdecf t h1 h2 h3 h4 h5
  ihave #Hi := winstrIntro pc false (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)) (.F_Base w)
    rfl rfl hwd $$ Hbs
  -- the config-writing funnel: certificate = register-only at either alignment
  iapply wwpInstrConfig gen cpu pc false (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)) c.pmpcfg
    c.mstatus (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgen haccpc hpmp (WeakLeafCsrw3.mieOfMok c hmok) (WeakLeafCsrw3.mprvOfMok c hmok)
    (wstepCertFr cpu.val pc _ _ (wcertRegonly al4 cpu.val pc))
    $$ Hhw Hclk Hhart_state Hcur_privilege Hmstatus Hpmpcfg_n Hpc Hi
  unfold wwpCbConfig wmstateNorg
  iintro %σ %b %mt %ip %Lpc %hcfg %Lms Hpriv Hms Hpmpc Hlat Hreg ⟨%hbnd, %hnv, %hwf, Hdev, Hlog, Hwsa⟩
    Hmt Hip
  ihave ⟨%hws, Hwsa, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsa Hhws]
  · iframe Hwsa Hhws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc _ hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hram, w', hwok, htext0⟩ := hfok
  obtain ⟨hww, -⟩ := hwok
  subst hww
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the registers the funnel does not hand over: the source and the CSR
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1) $$ Hreg Hrs1c
    with ⟨%Lrs1, Hreg, Hrs1c⟩
  have Lrs1f : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafCsrw.gprSetRegNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1
  icases keepPure (wand_intro (reg_valid cpu _ .pmpaddr_n _ _)) $$ Hreg Hpmpaddr_n
    with ⟨%Lcsra, Hreg, Hpmpaddr_n⟩
  have Lcsr : σ.wmRegs .pmpaddr_n = c.pmpaddr := by
    rw [setLookupNe _ _ _ _ (by decide)] at Lcsra; exact Lcsra
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := csrwSexecFactsR .pmpaddr_n
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4)
      (WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v) (by decide) (by decide) (by decide)
    refine ⟨_, WeakLeafCsrw3.execEffPmpaddr0At _ b' _ rs1 c.pmpcfg c.pmpaddr rs1v hrs1 Lpriv Lpmpc Lcsr
      Lrs1f, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w
      (.CSRReg (0x3B0#12, .Regidx rs1, zreg, .CSRRW)) D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (WeakLeafCsrw3.fetchPinRegonly σ al4 pc haccpc (fun j hj => (htp j hj).2))
      Lpc Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp hal2 hal4 hram
      (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi hgood hdec
      rfl hc
  -- the run at the FLAT state
  have Hef := WeakLeafCsrw3.execEffPmpaddr0At (wflatSt σ) b (BitVec.addInt pc 4) rs1 c.pmpcfg c.pmpaddr
    rs1v hrs1 Lpriv Lpmpc Lcsr Lrs1f
  obtain ⟨-, -, -, G4, G5⟩ := csrwSexecFactsR .pmpaddr_n (wflatSt σ) b (BitVec.addInt pc 4)
    (WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v) (by decide) (by decide) (by decide)
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu ((wflatSt σ).setReg .minstret_increment b).regs .nextPC npc0
    (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu
    ((((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC (BitVec.addInt pc 4)) .pmpaddr_n
    c.pmpaddr
    (WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v))) $$ Hreg Hpmpaddr_n with ⟨Hreg, Hpmpaddr_n⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
    .pmpaddr_n (WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ Hef
  isplitl [Hreg]
  · rw [show ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
        .pmpaddr_n (WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v)).regs =
        ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)).set
        .pmpaddr_n (WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v)) from rfl]
    iexact Hreg
  isplitl [Hmt Hip]
  · iexists mt, ip
    iframe Hmt Hip
  inext
  rw [G5]
  iintro %tick %σ' %t %_hstep %hdevt %hpost %hQ Hhs Hclk HPC
  obtain ⟨-, hdevs', -, -, -, -, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, hQw⟩, hQeff⟩ := hQ
  have hdev : σ'.wmDev = σ.wmDev := by rw [hdevs', hdevt]; exact G4
  imod Hclose
  imod hartWsUpdate cpu σ.wmWs ws σ'.wmWs $$ [$Hwsa $Hhws] with ⟨Hwsa, Hhws⟩
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlog Hwsa]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      refine nvHartOfWQEffUnwritten cpu σ σ' _ hQeff hnv (fun a ha => ?_)
      obtain ⟨j, hj, rfl⟩ := weffsTouchRegonly al4 pc a haccpc ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdev, hQl]
    iframe Hdev Hlog Hwsa
  · -- rebuild the config at the written value
    ihave Hm' := mConf_introW cpu (DFrac.own 1)
      { c with pmpaddr := WeakLeafCsrw3.pmp0Newaddr c.pmpcfg c.pmpaddr rs1v } $$ Hpriv Hhs Hms Hmie Hmideleg
      Hmedeleg Hmepc Hsatp Hmenvcfg Hmcounteren Hmtimecmp Hstimecmp Hpmpc Hpmpaddr_n Hhw
    iapply Hcont $$ %σ'.wmWs %(by rw [hws]; exact hQw) Hm' Hclk [HPC Hnpc] Hrs1c Hhws
    unfold pcIs
    iframe HPC Hnpc

end leaves

end Weak
