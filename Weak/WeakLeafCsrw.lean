/-
Weak: **the csrw-mstatus leaf on `WeakFunnelCfg.wwpInstrConfig`** (M4
batch 2).

Rocq: `iris/WeakLeafCsrw.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The SMOKE-TEST CONSUMER of the config-variant
funnel (seam 1 of the `start()` blockers): the weak twin of
`WpGprCsrwC.wp_csrw_mstatus_raw`, at the batch-2 register-only recipe -- a
certificate at `WeakEff.wcertNowrite` / `wQPure` over the fetch-only trace,
so no memory arms appear anywhere.
* §1 the `execEff` mirror of the csrw-mstatus `execute` cone, at the empty
  trace (register-only instructions need the SYNTACTIC trace-`[]` mirror).
  The `doCSR` / `execute_CSRReg` spine (`execEffDoCSRCsrwP` /
  `execEffExecuteCsrwGprP`) is CSR-GENERIC -- the later csrw-pmpcfg0 /
  csrw-stimecmp / … leaves reuse it and owe only their own `write_CSR`
  mirror.
* §2 the successor register frame for a csr-writing instruction
  (`csrwSexecFacts` -- `WeakLeafWin.loadSexecFacts` with the CSR cell in
  place of the GPR).
* §3 the leaf `wwpCsrwMstatusLeaf`: statement = `wp_csrw_mstatus_raw` under
  the porting-table swaps (`instr` ↦ `winstrBytes` + the decode premises,
  `hartWs`/`wsLe` threading), driven through `wwpInstrConfig`.

**Deviations from Rocq.**
1. VOCABULARY: the `Weak/ExecSC*.lean` conventions (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `mword n` ↦ `BitVec n`, `set_reg` ↦ `ExecSt.setReg`, `M X` ↦ `SailM X`,
   `uint x` ↦ `x.toNat`, `add_vec_int` ↦ `BitVec.addInt`); `csr_mstatus` is
   the literal `0x300#12` (ExecSC7 deviation 1); Rocq's GPR read `if uint rs1
   =? 0 then zero_reg else register_lookup (R_bitvector_64 (gpr_of_Z (uint
   rs1))) s.(sregs)` ↦ `s.gpr rs1` (so `exec_eff_execute_csrw_mstatus`'s
   `register_lookup (R_bitvector_64 …)` is `s.gpr rs1`, equal under its
   `uint rs1 ≠ 0` premise, which is kept).
2. `mstatus_legalized` (Rocq `WpGprCsrwCommon`, not in the Lean tree) is the
   Lean-only `WeakLeafCsrw.mstatusLegalized`: MachCSL's `mstatusLegalize`
   body with Rocq's `have_nom_val` choice in the `MPP` slot (so, unlike
   `ExecSC7.execLegalizeMstatus`, no nominal-`MPP` premise and Rocq's
   misa.S/misa.U premises).
3. §1d: Lean's `write_CSR` is a `match` on the CSR number, not an `if`
   chain; `exec_eff_if_false_g{,4,16}` are kept as stated (generic `if`
   lemmas) and `skip_csr_false_clauses_eff` is a macro that rewrites with
   them, discharging the guards by `decide` (Rocq `vm_compute`).  The
   `write_CSR` arm itself is MachCSL's `write_CSR_mstatus` equation.
4. `exec_eff_doCSR_csrw_p`: as `ExecSC7.execDoCSRCsrwP`, the `0x344`/`0x144`
   tests are `(csr == 0x344#12) = false`.
5. THE LEAF (§3), the config interface of `WeakFunnelCfg` (owner decision
   Q3): Rocq `hw_config -∗ minstret_inv -∗ …` ↦ `hwConfig cpu ⊢ clockCells
   cpu -∗ …`, and the continuation also receives `clockCells cpu` (owned,
   not an invariant); ambient `GenId`/`CpuId` are the explicit `gen`/`cpu`;
   `WWP Loop` is `wwpTriv ⊤ (WExpr.loop gen cpu)`; `hart_ws cpu_id` is
   `hartWs cpu`; `pc_is` is `MachCSL.pcIs cpu`; the operand cell
   `R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v` is MachCSL's
   `gpr cpu rs1 (DFrac.own 1) rs1v`; `winstr_bytes` is `winstrBytes`.
   The decode premises are as Rocq's (`decode_fetch` ↦ `decodeFetch`,
   `priv_mSU` ↦ `privMSU`, `cfg_ok` ↦ `cfgOk`, `MISA_C` ↦ `misaC`; the
   `regstate` agreement premise quantifies over `RegFile`).  The certificate's
   fetch element is `.WEread WeakFetchEff.wakIfetch pc 4` (O2, WeakFetchEff
   deviation 2); its `fetchPin` obligation (WeakFetchEff deviation 9) is
   discharged from `winstrTextPinned` (`WeakAcquire.fetchPinOfText`).
6. Rocq §4's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_legalize_mstatus`
`execEffLegalizeMstatus`, `exec_eff_if_false_g` `execEffIfFalseG`,
`exec_eff_if_false_g16` `execEffIfFalseG16`, `exec_eff_if_false_g4`
`execEffIfFalseG4`, `skip_csr_false_clauses_eff` (Ltac)
`skip_csr_false_clauses_eff` (macro), `exec_eff_write_CSR_mstatus`
`execEffWriteCSRMstatus`, `exec_eff_csr_id_write_callback_mstatus`
`execEffCsrIdWriteCallbackMstatus`, `exec_eff_check_CSR_result_csrw_mstatus`
`execEffCheckCSRResultCsrwMstatus`, `exec_eff_wX_bits_zreg`
`execEffWXBitsZreg`, `exec_eff_doCSR_csrw_p` `execEffDoCSRCsrwP`,
`exec_eff_execute_csrw_gpr_p` `execEffExecuteCsrwGprP`,
`exec_eff_execute_csrw_mstatus` `execEffExecuteCsrwMstatus`,
`csrw_sexec_facts` `csrwSexecFacts`, `wwp_csrw_mstatus_leaf`
`wwpCsrwMstatusLeaf` (none in the duplicated-name table).  Lean-only
(file-qualified): `WeakLeafCsrw.mstatusLegalized` (deviation 2),
`WeakLeafCsrw.gprSetRegNe`, `WeakLeafCsrw.execEffCsrwAt`,
`WeakLeafCsrw.fetchInWindow1`, `WeakLeafCsrw.fetchFresh1`, and one `example`
exercising `skip_csr_false_clauses_eff`.  The GPR-cell agreement is
`WeakLeafLw4.gprValid` (reused, not re-proved).

**Dropped:** nothing (13 Rocq `Lemma`s + the `Ltac`; Lean 13 theorems + the
macro + 5 Lean-only).
-/
import Weak.WeakLeafWin
import Weak.WeakFunnelCfg
import Weak.WeakLeafEffCommon
import Weak.WeakLeafLw4
import MachCSL.Gpr

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE `execEff` MIRROR OF THE csrw-mstatus CONE (trace `[]`) -/

/-! ### 1c. The legalizer -/

/-- Rocq `WpGprCsrwCommon.mstatus_legalized` (deviation 2): `legalize_mstatus o v`
with S and U present, as a pure function. -/
def WeakLeafCsrw.mstatusLegalized (o v : BitVec 64) : BitVec 64 :=
  let o' :=
    _update_Mstatus_SIE
      (_update_Mstatus_MIE
        (_update_Mstatus_SPIE
          (_update_Mstatus_MPIE
            (_update_Mstatus_SPP
              (_update_Mstatus_MPP
                (_update_Mstatus_VS
                  (_update_Mstatus_FS
                    (_update_Mstatus_XS
                      (_update_Mstatus_MPRV
                        (_update_Mstatus_SUM
                          (_update_Mstatus_MXR
                            (_update_Mstatus_TVM
                              (_update_Mstatus_TW
                                (_update_Mstatus_TSR
                                  (_update_Mstatus_SPELP
                                    (_update_Mstatus_MPELP o (_get_Mstatus_MPELP (Mk_Mstatus v)))
                                    (_get_Mstatus_SPELP (Mk_Mstatus v)))
                                  (_get_Mstatus_TSR (Mk_Mstatus v)))
                                (_get_Mstatus_TW (Mk_Mstatus v)))
                              (_get_Mstatus_TVM (Mk_Mstatus v)))
                            (_get_Mstatus_MXR (Mk_Mstatus v)))
                          (_get_Mstatus_SUM (Mk_Mstatus v)))
                        (_get_Mstatus_MPRV (Mk_Mstatus v)))
                      (extStatus_map_forwards ExtStatus.Off))
                    (legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS (Mk_Mstatus v))))
                  (legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS (Mk_Mstatus v))))
                (if haveNomVal (_get_Mstatus_MPP (Mk_Mstatus v)) then _get_Mstatus_MPP (Mk_Mstatus v)
                 else privLevel_to_bits .User))
              (_get_Mstatus_SPP (Mk_Mstatus v)))
            (_get_Mstatus_MPIE (Mk_Mstatus v)))
          (_get_Mstatus_SPIE (Mk_Mstatus v)))
        (_get_Mstatus_MIE (Mk_Mstatus v)))
      (_get_Mstatus_SIE (Mk_Mstatus v))
  let dirty :=
    (extStatus_map_backwards (_get_Mstatus_FS o') == ExtStatus.Dirty) ||
    ((extStatus_map_backwards (_get_Mstatus_XS o') == ExtStatus.Dirty) ||
      (extStatus_map_backwards (_get_Mstatus_VS o') == ExtStatus.Dirty))
  _update_Mstatus_SD o' (bool_to_bit dirty)

/-- Rocq `exec_eff_legalize_mstatus`. -/
theorem execEffLegalizeMstatus (o v : BitVec 64) (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (hU : (_get_Misa_U (s.regs .misa) == 1#1) = true) :
    execEff (legalize_mstatus o v) s = some (WeakLeafCsrw.mstatusLegalized o v, s, []) := by
  unfold legalize_mstatus WeakLeafCsrw.mstatusLegalized
  rcases hb : haveNomVal (_get_Mstatus_MPP (Mk_Mstatus v)) with _ | _ <;>
  exec_eff_steps [WeakLeafEffCommon.execEffCurrentlyEnabledS, hS, execEffCurrentlyEnabledU s hU,
    execEffVirtualMemorySupported s hS, execEffHaveNominalPrivLevel _ s hU hS, hb,
    execEffLowestSupportedPrivLevel s hU, execEffHartSupportsZicfilp]

/-! ### 1d. The CSR-dispatch peel, at `execEff` (deviation 3) -/

/-- Rocq `exec_eff_if_false_g`. -/
theorem execEffIfFalseG {X : Type} (g : Bool) (A B : SailM X) (s : ExecSt) :
    g = false → execEff (if g then A else B) s = execEff B s := by
  intro h; subst h; rfl

/-- Rocq `exec_eff_if_false_g16`. -/
theorem execEffIfFalseG16 {X : Type}
    (g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 : Bool)
    (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 B : SailM X) (s : ExecSt) :
    g1 = false → g2 = false → g3 = false → g4 = false → g5 = false → g6 = false → g7 = false →
    g8 = false → g9 = false → g10 = false → g11 = false → g12 = false → g13 = false →
    g14 = false → g15 = false → g16 = false →
    execEff (if g1 then A1 else if g2 then A2 else if g3 then A3 else if g4 then A4 else
      if g5 then A5 else if g6 then A6 else if g7 then A7 else if g8 then A8 else
      if g9 then A9 else if g10 then A10 else if g11 then A11 else if g12 then A12 else
      if g13 then A13 else if g14 then A14 else if g15 then A15 else if g16 then A16 else B) s =
      execEff B s := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  rfl

/-- Rocq `exec_eff_if_false_g4`. -/
theorem execEffIfFalseG4 {X : Type} (g1 g2 g3 g4 : Bool) (A1 A2 A3 A4 B : SailM X) (s : ExecSt) :
    g1 = false → g2 = false → g3 = false → g4 = false →
    execEff (if g1 then A1 else if g2 then A2 else if g3 then A3 else if g4 then A4 else B) s =
      execEff B s := by
  intro h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- Rocq's Ltac `skip_csr_false_clauses_eff` (deviation 3): peel every `if` whose
guard is decidably `false`. -/
macro "skip_csr_false_clauses_eff" : tactic =>
  `(tactic| simp (disch := first | decide | decide +kernel) only
      [execEffIfFalseG16, execEffIfFalseG4, execEffIfFalseG])

example (s : ExecSt) (A B : SailM Nat) :
    execEff (if (0x300#12 == 0x301#12) then A else if (0x300#12 == 0x302#12) then A else B) s =
      execEff B s := by
  skip_csr_false_clauses_eff

/-! ### 1e. `write_CSR` / check / callback, for mstatus -/

/-- Rocq `exec_eff_write_CSR_mstatus`. -/
theorem execEffWriteCSRMstatus (v : BitVec 64) (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (hU : (_get_Misa_U (s.regs .misa) == 1#1) = true) :
    execEff (write_CSR 0x300#12 v) s =
      some (.Ok (WeakLeafCsrw.mstatusLegalized (s.regs .mstatus) v),
        s.setReg .mstatus (WeakLeafCsrw.mstatusLegalized (s.regs .mstatus) v), []) := by
  rw [write_CSR_mstatus]
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .mstatus s),
    execEffBindNil _ _ _ _ _ (execEffLegalizeMstatus (s.regs .mstatus) v s hS hU),
    execEffBind0Nil _ _ _ _ _ (execEffWriteReg .mstatus _ s),
    execEffBindNil _ _ _ _ _ (execEffReadReg .mstatus _)]
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_mstatus`. -/
theorem execEffCsrIdWriteCallbackMstatus (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x300#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_check_CSR_result_csrw_mstatus`. -/
theorem execEffCheckCSRResultCsrwMstatus (s : ExecSt) :
    execEff (check_CSR_result 0x300#12 .Machine .CSRWrite) s = some (.CSR_Check_OK (), s, []) := by
  have h : check_CSR 0x300#12 .Machine .CSRWrite = (pure true : SailM Bool) := by csr_dispatch_eq
  unfold check_CSR_result
  rw [h]
  rfl

/-! ### 1f. The `doCSR` / `execute_CSRReg` spine (CSR-GENERIC) -/

/-- Rocq `exec_eff_wX_bits_zreg`. -/
theorem execEffWXBitsZreg (v : BitVec 64) (s : ExecSt) :
    execEff (wX_bits zreg v) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_doCSR_csrw_p` (deviation 4). -/
theorem execEffDoCSRCsrwP (p : Privilege) (csr : BitVec 12) (v : BitVec 64) (s s' : ExecSt)
    (cfinal : BitVec 64)
    (hcp : s.regs .cur_privilege = p)
    (hchk : execEff (check_CSR_result csr p .CSRWrite) s = some (.CSR_Check_OK (), s, []))
    (hext : ext_check_CSR csr p .CSRWrite = true) (h344 : (csr == 0x344#12) = false)
    (h144 : (csr == 0x144#12) = false)
    (hw : execEff (write_CSR csr v) s = some (.Ok cfinal, s', []))
    (hcb : execEff (csr_id_write_callback csr cfinal) s' = some ((), s', [])) :
    execEff (doCSR csr v zreg .CSRRW .CSRWrite) s = some (RETIRE_SUCCESS, s', []) := by
  have h344' : csr ≠ 0x344#12 := by simpa using h344
  have h144' : csr ≠ 0x144#12 := by simpa using h144
  unfold doCSR
  exec_eff_steps [hcp, hchk, hext, Functions.not, hw, execEffWXBitsZreg, hcb, h344', h144']

/-- Rocq `exec_eff_execute_csrw_gpr_p` (deviation 1: the GPR read is `s.gpr rs1`). -/
theorem execEffExecuteCsrwGprP (p : Privilege) (csr : BitVec 12) (rs1 : BitVec 5) (s s' : ExecSt)
    (cfinal : BitVec 64)
    (hcp : s.regs .cur_privilege = p)
    (hchk : execEff (check_CSR_result csr p .CSRWrite) s = some (.CSR_Check_OK (), s, []))
    (hext : ext_check_CSR csr p .CSRWrite = true) (h344 : (csr == 0x344#12) = false)
    (h144 : (csr == 0x144#12) = false)
    (hw : execEff (write_CSR csr (s.gpr rs1)) s = some (.Ok cfinal, s', []))
    (hcb : execEff (csr_id_write_callback csr cfinal) s' = some ((), s', [])) :
    execEff (execute_CSRReg csr (.Regidx rs1) zreg .CSRRW) s = some (RETIRE_SUCCESS, s', []) := by
  unfold execute_CSRReg
  rw [execEffBindNil _ _ _ _ _ (execEffRXBitsGpr rs1 s)]
  exact execEffDoCSRCsrwP p csr _ s s' cfinal hcp hchk hext h344 h144 hw hcb

/-! ### 1g. The end-to-end mstatus execute, trace `[]` -/

/-- Rocq `exec_eff_execute_csrw_mstatus` (deviation 1). -/
theorem execEffExecuteCsrwMstatus (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .mstatus (WeakLeafCsrw.mstatusLegalized (s.regs .mstatus) (s.gpr rs1)), []) := by
  intro _ hpriv hS hU
  show execEff (execute_CSRReg 0x300#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x300#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwMstatus s) (by decide) (by decide) (by decide)
    (execEffWriteCSRMstatus _ s hS hU) (execEffCsrIdWriteCallbackMstatus _ _)

/-! ## 2. The successor register frame for a CSR-writing instruction -/

/-- Rocq `csrw_sexec_facts`. -/
theorem csrwSexecFacts (s0 : ExecSt) (b : Bool) (npc v : BitVec 64) :
    let sExec := ((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg .mstatus v
    sExec.regs .hart_state = s0.regs .hart_state ∧
    sExec.regs .minstret_increment = b ∧
    sExec.mem = s0.mem ∧
    sExec.dev = s0.dev ∧
    sExec.regs .nextPC = npc := by
  intro sExec
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · rw [setLookupNe .hart_state .mstatus _ _ (by decide)]
    leaf_peel .hart_state
  · rw [setLookupNe .minstret_increment .mstatus _ _ (by decide),
      setLookupNe .minstret_increment .nextPC _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  · rw [setLookupNe .nextPC .mstatus _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]

/-! ## 3. THE LEAF -/

/-- A non-GPR register write leaves every GPR read alone (Lean-only). -/
theorem WeakLeafCsrw.gprSetRegNe (s : ExecSt) (r : Register) (x : RegisterType r) (i : BitVec 5)
    (h : r ∉ uxaGprs) : (s.setReg r x).gpr i = s.gpr i := by
  unfold ExecSt.gpr
  exact uxaXget_congr _ _ (fun r' hr' => RegFile.set_other _ _ _ _ (fun e => h (by subst e; exact hr'))) i

/-- The csrw-mstatus `execute` at a pre-written state (Lean-only; the shared core of
the leaf's confined and flat runs). -/
theorem WeakLeafCsrw.execEffCsrwAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rs1 : BitVec 5)
    (ms0 rs1v : BitVec 64) (hrs1 : rs1.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hmisa : s0.regs .misa = misaC) (hms : s0.regs .mstatus = ms0) (hg : s0.gpr rs1 = rs1v) :
    execEff (execute (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setReg .mstatus
        (WeakLeafCsrw.mstatusLegalized ms0 rs1v), []) := by
  have hmisa' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .misa = misaC := by
    leaf_peel .misa; exact hmisa
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hms' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .mstatus = ms0 := by
    leaf_peel .mstatus; exact hms
  have hg' : ((s0.setReg .minstret_increment b).setReg .nextPC x).gpr rs1 = rs1v := by
    rw [WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide), WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide)]
    exact hg
  have h := execEffExecuteCsrwMstatus rs1 _ hrs1 hpriv' (by rw [hmisa']; decide) (by rw [hmisa']; decide)
  rw [hms', hg'] at h
  exact h

/-- The fetch-only trace's i-cache read is the text window (Lean-only). -/
theorem WeakLeafCsrw.fetchInWindow1 (pc : BitVec 64) (ak : AkInfo) :
    fetchInWindow pc [.WEread ak pc 4] := by
  intro ak' pa n hin _ j hj
  simp only [List.mem_singleton, Weff.WEread.injEq] at hin
  obtain ⟨rfl, rfl, rfl⟩ := hin
  exact ⟨j, hj, rfl⟩

/-- A one-element trace is fetch-fresh (Lean-only). -/
theorem WeakLeafCsrw.fetchFresh1 (e : Weff) : fetchFresh [e] := by
  simp [fetchFresh]

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrw_mstatus_leaf` (deviation 5). -/
theorem wwpCsrwMstatusLeaf (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32) (rs1 : BitVec 5)
    (ms0 rs1v npc0 : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) (D : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    rs1.toNat ≠ 0 →
    (_get_Mstatus_MIE ms0 == 1#1) = false →
    (_get_Mstatus_MPRV ms0 == 1#1) = false →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW), dst) →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms0 -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] WeakLeafCsrw.mstatusLegalized ms0 rs1v -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hpmp hal4 hrs1 hmie hmprv hdecf hagree hDmi hgood hdec
  iintro #Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  have hwd : winstrDec (.F_Base w) (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW)) :=
    fun t h1 h2 h3 h4 h5 => hdecf t h1 h2 h3 h4 h5
  ihave #Hi := winstrIntro pc false (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW)) (.F_Base w)
    rfl rfl hwd $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstrConfig gen cpu pc false (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW)) pmpcfg0 ms0
    (wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc 4])
    (wQFr wQPure (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc 4])
    hgen haccpc hpmp hmie hmprv
    (wstepCertFr cpu.val pc _ _ (wcertNowrite cpu.val pc _ (nowriteRead1 _ _ _)))
    $$ Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hi
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
  obtain ⟨hww, hnotRVC⟩ := hwok
  subst hww
  -- the operand register the funnel does not read
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1) $$ Hreg Hrs1c
    with ⟨%Lrs1, Hreg, Hrs1c⟩
  have Lrs1f : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafCsrw.gprSetRegNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := csrwSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4)
      (WeakLeafCsrw.mstatusLegalized ms0 rs1v)
    refine ⟨_, WeakLeafCsrw.execEffCsrwAt _ b' _ rs1 ms0 rs1v hrs1 Lpriv Lmisa Lms Lrs1f, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) [.WEread WeakFetchEff.wakIfetch pc 4] σ := by
    have h := wPEffOfLeafBase cpu.val σ (wwin pc pc 0) pc w
      (.CSRReg (0x300#12, .Regidx rs1, zreg, .CSRRW)) [] D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafCsrw.fetchInWindow1 pc _) (WeakLeafCsrw.fetchFresh1 _)
        (fun j hj => (htp j hj).2))
      Lpc Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS LmIE Lelp hal4 hram
      (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi hgood hdec
      rfl hc
    rw [List.append_nil] at h
    exact h
  -- the run at the FLAT state
  have Hef := WeakLeafCsrw.execEffCsrwAt (wflatSt σ) b (BitVec.addInt pc 4) rs1 ms0 rs1v hrs1 Lpriv Lmisa
    Lms Lrs1f
  obtain ⟨-, -, -, G4, G5⟩ := csrwSexecFacts (wflatSt σ) b (BitVec.addInt pc 4)
    (WeakLeafCsrw.mstatusLegalized ms0 rs1v)
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu ((wflatSt σ).setReg .minstret_increment b).regs .nextPC npc0
    (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu
    ((((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC (BitVec.addInt pc 4)) .mstatus ms0
    (WeakLeafCsrw.mstatusLegalized ms0 rs1v))) $$ Hreg Hms with ⟨Hreg, Hms⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
    .mstatus (WeakLeafCsrw.mstatusLegalized ms0 rs1v))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ Hef
  isplitl [Hreg]
  · rw [show ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
        .mstatus (WeakLeafCsrw.mstatusLegalized ms0 rs1v)).regs =
        ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)).set
        .mstatus (WeakLeafCsrw.mstatusLegalized ms0 rs1v)) from rfl]
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
      obtain ⟨j, hj, rfl⟩ := weffsTouchRead1 _ _ _ a ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdev, hQl]
    iframe Hdev Hlog Hwsa
  · iapply Hcont $$ %σ'.wmWs %(by rw [hws]; exact hQw) Hhs Hpriv Hms Hpmpc Hclk [HPC Hnpc] Hrs1c Hhws
    unfold pcIs
    iframe HPC Hnpc

end leaf

end Weak
