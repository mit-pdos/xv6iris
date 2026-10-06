/-
Weak: **the remaining weak csrr leaves** (M4, start/timerinit) -- csrr of
menvcfg, mcounteren, sie, mhartid and mstatus.

Rocq: `iris/WeakLeafCsrrM.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Seams 4-8 of the weak `start()`/`timerinit()`
port: the weak twins of `WpGprCsrrB.wp_csrr_menvcfg_gpr`,
`WpGprCsrrA.wp_csrr_mcounteren_gpr`, `WpGprCsrrB.wp_csrr_sie_gpr`,
`WpGprCsrrA.wp_csrr_mhartid_gpr` and `WpGprCsrrA.wp_csrr_mstatus_gpr`, at the
batch-2 register-only recipe.  `WeakLeafCsrrTime`'s CSR-GENERIC csrr spine
`execEffCsrrReadStepP` (and its `drive_csr_eff` macro and the two CSR-read
check combinators `execEffCheckCSRReadP` / `execEffCheckCSRResultReadP`) is
IMPORTED, never cloned, so each csrr leaf owes only its own `read_CSR` mirror,
accessibility discharge and callback.  Four leaves ride the PLAIN funnel
`wwpInstr`; `csrr rd, mstatus` rides the CONFIG funnel `wwpInstrConfig`, whose
callback pins `σ.wmRegs .mstatus = ms0` (the read value is mstatus's WHOLE
value).
* §1 the READ-side check-kit dispatchers, csr-generic (`_read_lit` /
  `_read_S` / `_read_U` / `_read_U_and`).
* §2 the five `read_CSR` mirrors, at trace `[]`.
* §3 the five callbacks, check results and end-to-end `execute` mirrors, each
  through the imported spine.
* §4 the pre-write peels (each read value past the funnel's
  `minstret_increment` and `nextPC` pre-writes).
* §5 the five leaves, all alignment-generic (`regonlyEs al4 pc` /
  `wcertRegonly` / `wPEffOfLeafRegonly`), all writing the one `rd` cell.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WeakLeafCsrrTime.lean` deviation 1 (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `mword n` ↦ `BitVec n`, `set_reg` ↦
   `ExecSt.setReg`, `subrange_vec_dec x 63 0` ↦ `Sail.BitVec.extractLsb x 63
   0`, `add_vec_int` ↦ `BitVec.addInt`, `uint x` ↦ `x.toNat`, `M X` ↦ `SailM
   X`, `CSR_Check_OK tt` ↦ `.CSR_Check_OK ()`, `eq_vec x 'b"1" = b` ↦ `(x ==
   1#1) = b`, `MISA_C` ↦ `misaC`); the CSR names are literals (`csr_menvcfg` ↦
   `0x30A#12`, `csr_mcounteren` ↦ `0x306#12`, `csr_sie` ↦ `0x104#12`,
   `csr_mstatus` ↦ `0x300#12`, `csr_csrr` ↦ `0xF14#12`); `zero_extend' 64` ↦
   `zero_extend (m := 64)`; the GPR write `set_reg s (R_bitvector_64 (gpr_of_Z
   (uint rd))) (regval_into_reg x)` is `s.setGpr rd x` (the `uint rd ≠ 0`
   premise is kept, though Lean's `execEffWXBitsGpr` does not need it).  The SC
   read values `menvcfg_rdval`, `mcounteren_rdval`, `sie_rdval` (Rocq
   `WpGprCsrrA/B`, no Lean twin) are the Lean-only
   `WeakLeafCsrrM.menvcfgRdval`/`mcounterenRdval`/`sieRdval`; `mstatus_rdval`
   is `ExecSC7.mstatusRdval` (reused).
2. §1: Lean's `check_CSR` has no `and_boolM`/`returnM` binds
   (`WeakLeafRegOnly` deviation 4): the `_read_lit` premise is `check_CSR csr
   .Machine .CSRRead = pure true`; `_read_U_and`'s accessibility premise is the
   Lean model's own menvcfg shape `(do let x ← currentlyEnabled .Ext_U; pure (x
   && b))`.
3. §2: Lean's `read_CSR` is a `match`; the mirrors rewrite with MachCSL's arm
   equations (`read_CSR_menvcfg`, … , `read_CSR_mhartid`) via
   `drive_csr_eff`; Rocq's by-hand mstatus peel is the same macro.
4. §4: `subrange64_id` is the Lean-only `WeakLeafCsrrM.extract64Id`;
   `mhartid_prewrite`'s `sregs (set_reg …)` is `(… .setReg …).regs`.
5. THE LEAVES on the plain funnel (owner decision Q3, `Weak/WeakFunnel.lean`
   deviation 7): Rocq `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q}
   pmpcfg0` ↦ `mConf cpu (DFrac.own q) c ∗ clockCells cpu` (`pmpcfg0 :=
   c.pmpcfg`, `pmp_allows_all pmpcfg0` ↦ `pmpAllowsAll c.pmpcfg`, plus
   `MConf.mok c`); the continuation gets the same back.  Lean's `mConf` OWNS
   the menvcfg / mcounteren / mie / mideleg cells (Rocq's `mmode_config` does
   not), so the Rocq leaves' separate `menvcfg ↦ᵣ menvcfg_in` (resp.
   `mcounteren ↦ᵣ mcen_in`, `mie ↦ᵣ mie_in ∗ mideleg ↦ᵣ mideleg_in`) is
   `mConf`'s own cell: the read value is `c.menvcfg` (resp. `zero_extend (m
   := 64) c.mcounteren`, `lower_mie c.mie c.mideleg`), and no separate cell is
   taken or returned.  To read that cell inside the funnel callback the leaf
   halves `mConf` (Lean-only `WeakLeafCsrrM.mConfHalves`, Rocq InstrBytes'
   `reg_pointsto_fractional`), lends one half to the funnel and keeps the
   other.  The mhartid leaf keeps Rocq's separate `mhartid ↦ᵣ mhartid_in`
   cell (mhartid is not in `mConf`).  The shared Iris proof of these four is
   the Lean-only `WeakLeafCsrrM.wwpCsrrCore`.  Rocq's `GenId`/`CpuId` are the
   explicit `gen`/`cpu`; `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`;
   `pc_is` ↦ `MachCSL.pcIs`; `hart_ws cpu_id` ↦ `hartWs cpu`; the rd cell
   `R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ x` ↦ `gpr cpu rd (DFrac.own 1) x`
   (`regval_into_reg` dropped); `winstr_bytes` ↦ `winstrBytes`; the decode
   premises over the funnel vocabulary (`privMSU`, `cfgOk`, `decodeFetch`; the
   agreement premise over `RegFile`, `mword_of_int 0` ↦ `0#64`).  O2: the
   fetch pin `fetchPin σ (regonlyEs al4 pc)` is discharged from
   `winstrTextPinned` (`fetchPinOfText` with
   `WeakLeafCsrrTime.fetchInWindowRegonly`/`fetchFreshRegonly`).
6. THE mstatus LEAF on the config funnel (`Weak/WeakFunnelCfg.lean` deviation
   2): Rocq `hw_config -∗ minstret_inv -∗ …` ↦ `hwConfig cpu ⊢ clockCells cpu
   -∗ …`; the continuation also receives `clockCells cpu` (after the
   `pmpcfg_n` cell).  The rest as deviation 5.
7. Rocq's five `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_check_CSR_result_read_lit`
`execEffCheckCSRResultReadLit`, `exec_eff_check_CSR_result_read_S`
`execEffCheckCSRResultReadS`, `exec_eff_check_CSR_result_read_U`
`execEffCheckCSRResultReadU`, `exec_eff_check_CSR_result_read_U_and`
`execEffCheckCSRResultReadUAnd`, `exec_eff_read_CSR_menvcfg`
`execEffReadCSRMenvcfg`, `exec_eff_read_CSR_mcounteren`
`execEffReadCSRMcounteren`, `exec_eff_read_CSR_sie` `execEffReadCSRSie`,
`exec_eff_read_CSR_mstatus` `execEffReadCSRMstatus`, `exec_eff_read_CSR_csrr`
`WeakLeafCsrrM.execEffReadCSRCsrr` (duplicated name),
`exec_eff_csr_id_read_callback_menvcfg` `execEffCsrIdReadCallbackMenvcfg`,
`exec_eff_csr_id_read_callback_mcounteren`
`execEffCsrIdReadCallbackMcounteren`, `exec_eff_csr_id_read_callback_sie`
`execEffCsrIdReadCallbackSie`, `exec_eff_csr_id_read_callback_mstatus`
`execEffCsrIdReadCallbackMstatus`, `exec_eff_csr_id_read_callback_csrr`
`WeakLeafCsrrM.execEffCsrIdReadCallbackCsrr` (duplicated name),
`exec_eff_check_CSR_result_menvcfg` `execEffCheckCSRResultMenvcfg`,
`exec_eff_execute_csrr_menvcfg_gpr` `execEffExecuteCsrrMenvcfgGpr`,
`exec_eff_check_CSR_result_mcounteren` `execEffCheckCSRResultMcounteren`,
`exec_eff_execute_csrr_mcounteren_gpr` `execEffExecuteCsrrMcounterenGpr`,
`exec_eff_check_CSR_result_sie` `execEffCheckCSRResultSie`,
`exec_eff_execute_csrr_sie_gpr` `execEffExecuteCsrrSieGpr`,
`exec_eff_check_CSR_result_mstatus` `execEffCheckCSRResultMstatus`,
`exec_eff_execute_csrr_mstatus_gpr` `execEffExecuteCsrrMstatusGpr`,
`exec_eff_check_CSR_result_csrr` `WeakLeafCsrrM.execEffCheckCSRResultCsrr`
(duplicated name), `exec_eff_execute_csrr_mhartid_gpr`
`execEffExecuteCsrrMhartidGpr`, `menvcfg_rdval_prewrite`
`menvcfgRdvalPrewrite`, `mcounteren_rdval_prewrite` `mcounterenRdvalPrewrite`,
`sie_rdval_prewrite` `sieRdvalPrewrite`, `mstatus_rdval_prewrite`
`mstatusRdvalPrewrite`, `mhartid_prewrite` `mhartidPrewrite`,
`wwp_csrr_menvcfg_leaf` `wwpCsrrMenvcfgLeaf`, `wwp_csrr_mcounteren_leaf`
`wwpCsrrMcounterenLeaf`, `wwp_csrr_sie_leaf` `wwpCsrrSieLeaf`,
`wwp_csrr_mhartid_leaf` `wwpCsrrMhartidLeaf`, `wwp_csrr_mstatus_leaf`
`wwpCsrrMstatusLeaf`.  Lean-only (file-qualified): the read values
`WeakLeafCsrrM.menvcfgRdval`/`mcounterenRdval`/`sieRdval` (deviation 1),
`WeakLeafCsrrM.extract64Id` (deviation 4), the fraction kit
`WeakLeafCsrrM.regSplit`/`sepSplit`/`mConfSplit`/`mConfHalves`/`mConfCsrFacts`
(deviation 5), the pre-written-state runs
`WeakLeafCsrrM.execEffCsrr{Menvcfg,Mcounteren,Sie,Mhartid,Mstatus}At`, and the
shared plain-funnel leaf `WeakLeafCsrrM.wwpCsrrCore`.

**Dropped:** nothing (Rocq 34 lemmas; Lean 34 + 15 Lean-only).
-/
import Weak.WeakLeafCsrrTime
import Weak.WeakFunnelCfg
import MachCSL.PlatformFacts

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE READ-SIDE CHECK KIT, csr-generic (deviation 2) -/

/-- Rocq `exec_eff_check_CSR_result_read_lit`: mstatus (0x300), mhartid (0xF14). -/
theorem execEffCheckCSRResultReadLit (csr : BitVec 12) (s : ExecSt) :
    check_CSR csr .Machine .CSRRead = (pure true : SailM Bool) →
    execEff (check_CSR_result csr .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  intro h
  unfold check_CSR_result
  rw [h]
  rfl

/-- Rocq `exec_eff_check_CSR_result_read_S`: sie (0x104). -/
theorem execEffCheckCSRResultReadS (csr : BitVec 12) (s : ExecSt) :
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_priv csr .Machine) s = some (true, s, []) →
    check_CSR_access csr .CSRRead = true →
    is_CSR_accessible csr .Machine .CSRRead = currentlyEnabled .Ext_S →
    execEff (stateen_allows_CSR_access csr .Machine .CSRRead) s = some (true, s, []) →
    execEff (check_CSR_result csr .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  intro hS hpriv hca hacceq hst
  apply execEffCheckCSRResultReadP
  apply execEffCheckCSRReadP _ _ _ hpriv hca _ hst
  rw [hacceq, WeakFetchEff.execEffCurrentlyEnabledS, hS]

/-- Rocq `exec_eff_check_CSR_result_read_U`: mcounteren (0x306). -/
theorem execEffCheckCSRResultReadU (csr : BitVec 12) (s : ExecSt) :
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_priv csr .Machine) s = some (true, s, []) →
    check_CSR_access csr .CSRRead = true →
    is_CSR_accessible csr .Machine .CSRRead = currentlyEnabled .Ext_U →
    execEff (stateen_allows_CSR_access csr .Machine .CSRRead) s = some (true, s, []) →
    execEff (check_CSR_result csr .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  intro hU hpriv hca hacceq hst
  apply execEffCheckCSRResultReadP
  apply execEffCheckCSRReadP _ _ _ hpriv hca _ hst
  rw [hacceq]
  exact execEffCurrentlyEnabledU s hU

/-- Rocq `exec_eff_check_CSR_result_read_U_and` (deviation 2): menvcfg (0x30A). -/
theorem execEffCheckCSRResultReadUAnd (csr : BitVec 12) (b : Bool) (s : ExecSt) :
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_priv csr .Machine) s = some (true, s, []) →
    check_CSR_access csr .CSRRead = true →
    is_CSR_accessible csr .Machine .CSRRead = (do let x ← currentlyEnabled .Ext_U; pure (x && b)) →
    b = true →
    execEff (stateen_allows_CSR_access csr .Machine .CSRRead) s = some (true, s, []) →
    execEff (check_CSR_result csr .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  intro hU hpriv hca hacceq hb hst
  apply execEffCheckCSRResultReadP
  apply execEffCheckCSRReadP _ _ _ hpriv hca _ hst
  rw [hacceq, execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledU s hU), hb]
  rfl

/-! ## 2. THE `read_CSR` MIRRORS (trace `[]`) -/

/-- Lean-only (deviation 1): Rocq `WpGprCsrrB.menvcfg_rdval`. -/
def WeakLeafCsrrM.menvcfgRdval (s : ExecSt) : BitVec 64 :=
  Sail.BitVec.extractLsb (s.regs .menvcfg) 63 0

/-- Lean-only (deviation 1): Rocq `WpGprCsrrA.mcounteren_rdval`. -/
def WeakLeafCsrrM.mcounterenRdval (s : ExecSt) : BitVec 64 :=
  zero_extend (m := 64) (s.regs .mcounteren)

/-- Lean-only (deviation 1): Rocq `WpGprCsrrB.sie_rdval`. -/
def WeakLeafCsrrM.sieRdval (s : ExecSt) : BitVec 64 :=
  lower_mie (s.regs .mie) (s.regs .mideleg)

/-- Rocq `exec_eff_read_CSR_menvcfg`. -/
theorem execEffReadCSRMenvcfg (s : ExecSt) :
    execEff (read_CSR 0x30A#12) s = some (WeakLeafCsrrM.menvcfgRdval s, s, []) := by
  unfold WeakLeafCsrrM.menvcfgRdval
  drive_csr_eff

/-- Rocq `exec_eff_read_CSR_mcounteren`. -/
theorem execEffReadCSRMcounteren (s : ExecSt) :
    execEff (read_CSR 0x306#12) s = some (WeakLeafCsrrM.mcounterenRdval s, s, []) := by
  unfold WeakLeafCsrrM.mcounterenRdval
  drive_csr_eff

/-- Rocq `exec_eff_read_CSR_sie`: sie is a VIEW of two registers. -/
theorem execEffReadCSRSie (s : ExecSt) :
    execEff (read_CSR 0x104#12) s = some (WeakLeafCsrrM.sieRdval s, s, []) := by
  unfold WeakLeafCsrrM.sieRdval
  drive_csr_eff

/-- Rocq `exec_eff_read_CSR_mstatus` (deviation 3). -/
theorem execEffReadCSRMstatus (s : ExecSt) :
    execEff (read_CSR 0x300#12) s = some (mstatusRdval s, s, []) := by
  unfold mstatusRdval
  drive_csr_eff

/-- Rocq `exec_eff_read_CSR_csrr` (duplicated name): mhartid (0xF14). -/
theorem WeakLeafCsrrM.execEffReadCSRCsrr (s : ExecSt) :
    execEff (read_CSR 0xF14#12) s = some (s.regs .mhartid, s, []) := by
  rw [read_CSR_mhartid]
  rfl

/-! ## 3. THE CALLBACKS AND THE END-TO-END `execute` MIRRORS -/

/-- Rocq `exec_eff_csr_id_read_callback_menvcfg`. -/
theorem execEffCsrIdReadCallbackMenvcfg (s : ExecSt) (d : BitVec 64) :
    execEff (csr_id_read_callback 0x30A#12 d) s = some ((), s, []) := by
  first
  | rfl
  | (rw [show csr_id_read_callback 0x30A#12 d = (pure () : SailM Unit) by csr_dispatch_eq]; rfl)

/-- Rocq `exec_eff_csr_id_read_callback_mcounteren`. -/
theorem execEffCsrIdReadCallbackMcounteren (s : ExecSt) (d : BitVec 64) :
    execEff (csr_id_read_callback 0x306#12 d) s = some ((), s, []) := by
  first
  | rfl
  | (rw [show csr_id_read_callback 0x306#12 d = (pure () : SailM Unit) by csr_dispatch_eq]; rfl)

/-- Rocq `exec_eff_csr_id_read_callback_sie`. -/
theorem execEffCsrIdReadCallbackSie (s : ExecSt) (d : BitVec 64) :
    execEff (csr_id_read_callback 0x104#12 d) s = some ((), s, []) := by
  first
  | rfl
  | (rw [show csr_id_read_callback 0x104#12 d = (pure () : SailM Unit) by csr_dispatch_eq]; rfl)

/-- Rocq `exec_eff_csr_id_read_callback_mstatus`. -/
theorem execEffCsrIdReadCallbackMstatus (s : ExecSt) (d : BitVec 64) :
    execEff (csr_id_read_callback 0x300#12 d) s = some ((), s, []) := by
  first
  | rfl
  | (rw [show csr_id_read_callback 0x300#12 d = (pure () : SailM Unit) by csr_dispatch_eq]; rfl)

/-- Rocq `exec_eff_csr_id_read_callback_csrr` (duplicated name). -/
theorem WeakLeafCsrrM.execEffCsrIdReadCallbackCsrr (s : ExecSt) (d : BitVec 64) :
    execEff (csr_id_read_callback 0xF14#12 d) s = some ((), s, []) := by
  first
  | rfl
  | (rw [show csr_id_read_callback 0xF14#12 d = (pure () : SailM Unit) by csr_dispatch_eq]; rfl)

/-! ### 3a. menvcfg (0x30A): Ext_U-gated AND the xenvcfg-exists predicate -/

/-- Rocq `exec_eff_check_CSR_result_menvcfg`. -/
theorem execEffCheckCSRResultMenvcfg (s : ExecSt) :
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_result 0x30A#12 .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  intro hU
  apply execEffCheckCSRResultReadUAnd 0x30A#12 xenvcfg_csrs_are_defined s hU
  · rw [show check_CSR_priv 0x30A#12 .Machine = (pure true : SailM Bool) by csr_dispatch_eq]
    rfl
  · first | rfl | decide
  · exact is_CSR_accessible_menvcfg _ _
  · first | rfl | decide
  · rw [stateen_menvcfg]
    rfl

/-- Rocq `exec_eff_execute_csrr_menvcfg_gpr` (deviation 1). -/
theorem execEffExecuteCsrrMenvcfgGpr (rd : BitVec 5) (s : ExecSt) :
    rd.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x30A#12, zreg, .Regidx rd, .CSRRS))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (WeakLeafCsrrM.menvcfgRdval s), []) := by
  intro _ hpriv hU
  show execEff (execute_CSRReg 0x30A#12 zreg (.Regidx rd) .CSRRS) s = _
  exact execEffCsrrReadStepP .Machine 0x30A#12 rd (WeakLeafCsrrM.menvcfgRdval s) s _ hpriv
    (execEffCheckCSRResultMenvcfg s hU) (by first | rfl | decide) (execEffReadCSRMenvcfg s)
    (by decide) (by decide) (execEffCsrIdReadCallbackMenvcfg s _) (execEffWXBitsGpr rd _ s)

/-! ### 3b. mcounteren (0x306): Ext_U-gated, 32-bit CSR -/

/-- Rocq `exec_eff_check_CSR_result_mcounteren`. -/
theorem execEffCheckCSRResultMcounteren (s : ExecSt) :
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_result 0x306#12 .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  intro hU
  apply execEffCheckCSRResultReadU 0x306#12 s hU
  · rw [show check_CSR_priv 0x306#12 .Machine = (pure true : SailM Bool) by csr_dispatch_eq]
    rfl
  · first | rfl | decide
  · exact is_CSR_accessible_mcounteren _ _
  · rw [stateen_mcounteren]
    rfl

/-- Rocq `exec_eff_execute_csrr_mcounteren_gpr` (deviation 1). -/
theorem execEffExecuteCsrrMcounterenGpr (rd : BitVec 5) (s : ExecSt) :
    rd.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x306#12, zreg, .Regidx rd, .CSRRS))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (WeakLeafCsrrM.mcounterenRdval s), []) := by
  intro _ hpriv hU
  show execEff (execute_CSRReg 0x306#12 zreg (.Regidx rd) .CSRRS) s = _
  exact execEffCsrrReadStepP .Machine 0x306#12 rd (WeakLeafCsrrM.mcounterenRdval s) s _ hpriv
    (execEffCheckCSRResultMcounteren s hU) (by first | rfl | decide) (execEffReadCSRMcounteren s)
    (by decide) (by decide) (execEffCsrIdReadCallbackMcounteren s _) (execEffWXBitsGpr rd _ s)

/-! ### 3c. sie (0x104): Ext_S-gated, a view of mie & mideleg -/

/-- Rocq `exec_eff_check_CSR_result_sie`. -/
theorem execEffCheckCSRResultSie (s : ExecSt) :
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (check_CSR_result 0x104#12 .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  intro hS
  apply execEffCheckCSRResultReadS 0x104#12 s hS
  · rw [show check_CSR_priv 0x104#12 .Machine = (pure true : SailM Bool) by csr_dispatch_eq]
    rfl
  · first | rfl | decide
  · exact is_CSR_accessible_sie _ _
  · rw [stateen_sie]
    rfl

/-- Rocq `exec_eff_execute_csrr_sie_gpr` (deviation 1). -/
theorem execEffExecuteCsrrSieGpr (rd : BitVec 5) (s : ExecSt) :
    rd.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x104#12, zreg, .Regidx rd, .CSRRS))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (WeakLeafCsrrM.sieRdval s), []) := by
  intro _ hpriv hS
  show execEff (execute_CSRReg 0x104#12 zreg (.Regidx rd) .CSRRS) s = _
  exact execEffCsrrReadStepP .Machine 0x104#12 rd (WeakLeafCsrrM.sieRdval s) s _ hpriv
    (execEffCheckCSRResultSie s hS) (by first | rfl | decide) (execEffReadCSRSie s)
    (by decide) (by decide) (execEffCsrIdReadCallbackSie s _) (execEffWXBitsGpr rd _ s)

/-! ### 3d. mstatus (0x300): no gate -/

/-- Rocq `exec_eff_check_CSR_result_mstatus`. -/
theorem execEffCheckCSRResultMstatus (s : ExecSt) :
    execEff (check_CSR_result 0x300#12 .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) :=
  execEffCheckCSRResultReadLit _ s (by csr_dispatch_eq)

/-- Rocq `exec_eff_execute_csrr_mstatus_gpr` (deviation 1). -/
theorem execEffExecuteCsrrMstatusGpr (rd : BitVec 5) (s : ExecSt) :
    rd.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    execEff (execute (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (mstatusRdval s), []) := by
  intro _ hpriv
  show execEff (execute_CSRReg 0x300#12 zreg (.Regidx rd) .CSRRS) s = _
  exact execEffCsrrReadStepP .Machine 0x300#12 rd (mstatusRdval s) s _ hpriv
    (execEffCheckCSRResultMstatus s) (by first | rfl | decide) (execEffReadCSRMstatus s)
    (by decide) (by decide) (execEffCsrIdReadCallbackMstatus s _) (execEffWXBitsGpr rd _ s)

/-! ### 3e. mhartid (0xF14): no gate -/

/-- Rocq `exec_eff_check_CSR_result_csrr` (duplicated name). -/
theorem WeakLeafCsrrM.execEffCheckCSRResultCsrr (s : ExecSt) :
    execEff (check_CSR_result 0xF14#12 .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) :=
  execEffCheckCSRResultReadLit _ s (by csr_dispatch_eq)

/-- Rocq `exec_eff_execute_csrr_mhartid_gpr` (deviation 1). -/
theorem execEffExecuteCsrrMhartidGpr (rd : BitVec 5) (s : ExecSt) :
    rd.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    execEff (execute (.CSRReg (0xF14#12, zreg, .Regidx rd, .CSRRS))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (s.regs .mhartid), []) := by
  intro _ hpriv
  show execEff (execute_CSRReg 0xF14#12 zreg (.Regidx rd) .CSRRS) s = _
  exact execEffCsrrReadStepP .Machine 0xF14#12 rd (s.regs .mhartid) s _ hpriv
    (WeakLeafCsrrM.execEffCheckCSRResultCsrr s) (by first | rfl | decide)
    (WeakLeafCsrrM.execEffReadCSRCsrr s) (by decide) (by decide)
    (WeakLeafCsrrM.execEffCsrIdReadCallbackCsrr s _) (execEffWXBitsGpr rd _ s)

/-! ## 4. THE PRE-WRITE PEELS -/

/-- Lean-only (deviation 4): Rocq `subrange64_id`. -/
theorem WeakLeafCsrrM.extract64Id (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb]

/-- Rocq `menvcfg_rdval_prewrite`. -/
theorem menvcfgRdvalPrewrite (s0 : ExecSt) (b : Bool) (npc v : BitVec 64) :
    s0.regs .menvcfg = v →
    WeakLeafCsrrM.menvcfgRdval ((s0.setReg .minstret_increment b).setReg .nextPC npc) = v := by
  intro h
  unfold WeakLeafCsrrM.menvcfgRdval
  rw [setLookupNe .menvcfg .nextPC _ _ (by decide), setLookupNe .menvcfg .minstret_increment _ _ (by decide),
    h]
  exact WeakLeafCsrrM.extract64Id v

/-- Rocq `mcounteren_rdval_prewrite`. -/
theorem mcounterenRdvalPrewrite (s0 : ExecSt) (b : Bool) (npc : BitVec 64) (v : BitVec 32) :
    s0.regs .mcounteren = v →
    WeakLeafCsrrM.mcounterenRdval ((s0.setReg .minstret_increment b).setReg .nextPC npc) =
      zero_extend (m := 64) v := by
  intro h
  unfold WeakLeafCsrrM.mcounterenRdval
  rw [setLookupNe .mcounteren .nextPC _ _ (by decide),
    setLookupNe .mcounteren .minstret_increment _ _ (by decide), h]

/-- Rocq `sie_rdval_prewrite`. -/
theorem sieRdvalPrewrite (s0 : ExecSt) (b : Bool) (npc v1 v2 : BitVec 64) :
    s0.regs .mie = v1 →
    s0.regs .mideleg = v2 →
    WeakLeafCsrrM.sieRdval ((s0.setReg .minstret_increment b).setReg .nextPC npc) = lower_mie v1 v2 := by
  intro h1 h2
  unfold WeakLeafCsrrM.sieRdval
  rw [setLookupNe .mie .nextPC _ _ (by decide), setLookupNe .mie .minstret_increment _ _ (by decide),
    setLookupNe .mideleg .nextPC _ _ (by decide),
    setLookupNe .mideleg .minstret_increment _ _ (by decide), h1, h2]

/-- Rocq `mstatus_rdval_prewrite`. -/
theorem mstatusRdvalPrewrite (s0 : ExecSt) (b : Bool) (npc v : BitVec 64) :
    s0.regs .mstatus = v →
    mstatusRdval ((s0.setReg .minstret_increment b).setReg .nextPC npc) = v := by
  intro h
  unfold mstatusRdval
  rw [setLookupNe .mstatus .nextPC _ _ (by decide), setLookupNe .mstatus .minstret_increment _ _ (by decide),
    h]
  exact WeakLeafCsrrM.extract64Id v

/-- Rocq `mhartid_prewrite` (deviation 4). -/
theorem mhartidPrewrite (s0 : ExecSt) (b : Bool) (npc v : BitVec 64) :
    s0.regs .mhartid = v →
    ((s0.setReg .minstret_increment b).setReg .nextPC npc).regs .mhartid = v := by
  intro h
  rw [setLookupNe .mhartid .nextPC _ _ (by decide), setLookupNe .mhartid .minstret_increment _ _ (by decide)]
  exact h

/-! ## 4b. The runs at a pre-written state (Lean-only) -/

/-- csrr menvcfg at a pre-written state (Lean-only). -/
theorem WeakLeafCsrrM.execEffCsrrMenvcfgAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rd : BitVec 5)
    (v : BitVec 64) (hrd : rd.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hmisa : s0.regs .misa = misaC) (hv : s0.regs .menvcfg = v) :
    execEff (execute (.CSRReg (0x30A#12, zreg, .Regidx rd, .CSRRS)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setGpr rd v, []) := by
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hmisa' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .misa = misaC := by
    leaf_peel .misa; exact hmisa
  have h := execEffExecuteCsrrMenvcfgGpr rd _ hrd hpriv' (by rw [hmisa']; decide)
  rw [menvcfgRdvalPrewrite s0 b x v hv] at h
  exact h

/-- csrr mcounteren at a pre-written state (Lean-only). -/
theorem WeakLeafCsrrM.execEffCsrrMcounterenAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rd : BitVec 5)
    (v : BitVec 32) (hrd : rd.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hmisa : s0.regs .misa = misaC) (hv : s0.regs .mcounteren = v) :
    execEff (execute (.CSRReg (0x306#12, zreg, .Regidx rd, .CSRRS)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setGpr rd
        (zero_extend (m := 64) v), []) := by
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hmisa' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .misa = misaC := by
    leaf_peel .misa; exact hmisa
  have h := execEffExecuteCsrrMcounterenGpr rd _ hrd hpriv' (by rw [hmisa']; decide)
  rw [mcounterenRdvalPrewrite s0 b x v hv] at h
  exact h

/-- csrr sie at a pre-written state (Lean-only). -/
theorem WeakLeafCsrrM.execEffCsrrSieAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rd : BitVec 5)
    (v1 v2 : BitVec 64) (hrd : rd.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hmisa : s0.regs .misa = misaC) (h1 : s0.regs .mie = v1) (h2 : s0.regs .mideleg = v2) :
    execEff (execute (.CSRReg (0x104#12, zreg, .Regidx rd, .CSRRS)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setGpr rd
        (lower_mie v1 v2), []) := by
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hmisa' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .misa = misaC := by
    leaf_peel .misa; exact hmisa
  have h := execEffExecuteCsrrSieGpr rd _ hrd hpriv' (by rw [hmisa']; decide)
  rw [sieRdvalPrewrite s0 b x v1 v2 h1 h2] at h
  exact h

/-- csrr mhartid at a pre-written state (Lean-only). -/
theorem WeakLeafCsrrM.execEffCsrrMhartidAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rd : BitVec 5)
    (v : BitVec 64) (hrd : rd.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hv : s0.regs .mhartid = v) :
    execEff (execute (.CSRReg (0xF14#12, zreg, .Regidx rd, .CSRRS)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setGpr rd v, []) := by
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have h := execEffExecuteCsrrMhartidGpr rd _ hrd hpriv'
  rw [mhartidPrewrite s0 b x v hv] at h
  exact h

/-- csrr mstatus at a pre-written state (Lean-only). -/
theorem WeakLeafCsrrM.execEffCsrrMstatusAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rd : BitVec 5)
    (v : BitVec 64) (hrd : rd.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hv : s0.regs .mstatus = v) :
    execEff (execute (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setGpr rd v, []) := by
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have h := execEffExecuteCsrrMstatusGpr rd _ hrd hpriv'
  rw [mstatusRdvalPrewrite s0 b x v hv] at h
  exact h

/-! ## 5. THE LEAVES -/

section leaves
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-! ### 5.0 The fraction kit (Lean-only, deviation 5) -/

/-- A register cell splits along its fraction (Rocq InstrBytes'
`reg_pointsto_fractional`). -/
theorem WeakLeafCsrrM.regSplit (cpu : CPU) (r : Register) (q1 q2 : Qp) (v : RegisterType r) :
    regPointsTo (hlc := hlc) (GF := GF) cpu r (DFrac.own (q1 + q2)) v ⊣⊢
      regPointsTo cpu r (DFrac.own q1) v ∗ regPointsTo cpu r (DFrac.own q2) v := by
  unfold regPointsTo regPointsToAt
  exact (ghost_map_elem_fractional _ _ _).fractional q1 q2

/-- Two splittable conjuncts split their conjunction (Lean-only). -/
theorem WeakLeafCsrrM.sepSplit {PROP : Type _} [BI PROP] {A A1 A2 B B1 B2 : PROP}
    (ha : A ⊣⊢ A1 ∗ A2) (hb : B ⊣⊢ B1 ∗ B2) : A ∗ B ⊣⊢ (A1 ∗ B1) ∗ (A2 ∗ B2) :=
  (sep_congr ha hb).trans sep_sep_sep_comm

/-- `mConf` splits along its fraction (Lean-only). -/
theorem WeakLeafCsrrM.mConfSplit (cpu : CPU) (q1 q2 : Qp) (c : MConf) :
    mConf (GF := GF) cpu (DFrac.own (q1 + q2)) c ⊣⊢
      mConf cpu (DFrac.own q1) c ∗ mConf cpu (DFrac.own q2) c := by
  unfold mConf confCells
  iterate 14 refine WeakLeafCsrrM.sepSplit (WeakLeafCsrrM.regSplit _ _ _ _ _) ?_
  exact persistent_sep_dup

/-- `mConf` at `q` is two `mConf`s at `q/2` (Lean-only). -/
theorem WeakLeafCsrrM.mConfHalves (cpu : CPU) (q : Qp) (c : MConf) :
    mConf (GF := GF) cpu (DFrac.own q) c ⊣⊢
      mConf cpu (DFrac.own q.half) c ∗ mConf cpu (DFrac.own q.half) c := by
  have h := WeakLeafCsrrM.mConfSplit (GF := GF) cpu q.half q.half c
  rwa [Qp.half_add_half] at h

/-- The csrr-relevant cells of `mConf` pin the register file (Lean-only). -/
theorem WeakLeafCsrrM.mConfCsrFacts (cpu : CPU) (dq : DFrac) (c : MConf) (f : RegFile) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢ mConf cpu dq c -∗
      ⌜f .mie = c.mie ∧ f .mideleg = c.mideleg ∧ f .menvcfg = c.menvcfg ∧
        f .mcounteren = c.mcounteren⌝ := by
  iintro Hr Hm
  icases mConf_cases cpu dq c $$ Hm with ⟨-, -, -, H4, H5, -, -, -, H9, H10, -, -, -, -, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H4 with ⟨%E1, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H5 with ⟨%E2, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H9 with ⟨%E3, Hr, -⟩
  ihave %E4 := wand_intro (reg_valid cpu f _ _ _) $$ Hr H10
  ipureintro
  exact ⟨E1, E2, E3, E4⟩

/-! ### 5.1 The shared plain-funnel csrr leaf (Lean-only, deviation 5) -/

/-- The plain-funnel csrr leaf, generic in the CSR, the read value `v`, a kept
resource `K` that pins the facts `R` the run needs, and the run itself
(Lean-only; the common proof of Rocq §5a-§5d). -/
theorem WeakLeafCsrrM.wwpCsrrCore (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (csr : BitVec 12) (rd : BitVec 5) (v rd0 npc0 : BitVec 64) (c : MConf) (dq : DFrac)
    (R : RegFile → Prop) (K : IProp GF) (D : Register → Bool) (dst : ExecSt) (ws : Wstate)
    (hK : ∀ f : RegFile, regInterp (hlc := hlc) (GF := GF) cpu f ⊢ K -∗ ⌜R f⌝)
    (hRmi : ∀ (f : RegFile) (b : Bool), R (f.set .minstret_increment b) → R f)
    (hexe : ∀ (s0 : ExecSt) (b : Bool) (x : BitVec 64),
      s0.regs .cur_privilege = .Machine → s0.regs .misa = misaC → R s0.regs →
      execEff (execute (.CSRReg (csr, zreg, .Regidx rd, .CSRRS)))
          ((s0.setReg .minstret_increment b).setReg .nextPC x) =
        some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setGpr rd v, [])) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (csr, zreg, .Regidx rd, .CSRRS), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (csr, zreg, .Regidx rd, .CSRRS), dst) →
    mConf (GF := GF) cpu dq c ⊢
      clockCells cpu -∗
      K -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu dq c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) v -∗
        K -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  iintro Hm Hclk HK Hpc Hnpc Hrdc #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.CSRReg (csr, zreg, .Regidx rd, .CSRRS)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.CSRReg (csr, zreg, .Regidx rd, .CSRRS)) (.F_Base w)
    (by first | rfl | decide) rfl hdecW $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstr gen cpu pc false (.CSRReg (csr, zreg, .Regidx rd, .CSRRS)) c dq
    (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgid haccpc hmok hpmp
    (wstepCertFr _ _ _ _ (wcertRegonly al4 cpu.val pc)) $$ Hm Hclk Hpc Hwi
  unfold wwpCb
  iintro %σ %b %mt %ip %Lpc0 %hcfg Hlat Hreg Hnorg Hti Hip
  unfold wmstateNorg
  icases Hnorg with ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc _ hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hram, w', hwok, htext0⟩ := hfok
  obtain ⟨hww, -⟩ := hwok
  subst hww
  -- the kept resource pins the facts the run needs
  icases keepPure (hK _) $$ Hreg HK with ⟨%hR0, Hreg, HK⟩
  have hR : R σ.wmRegs := hRmi σ.wmRegs b hR0
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (csr, zreg, .Regidx rd, .CSRRS)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := loadSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4) rd v
    refine ⟨_, hexe (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' _ Lpriv Lmisa hR,
      ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w (.CSRReg (csr, zreg, .Regidx rd, .CSRRS))
      D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafCsrrTime.fetchInWindowRegonly al4 pc haccpc)
        (WeakLeafCsrrTime.fetchFreshRegonly al4 pc) (fun j hj => (htp j hj).2))
      Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi
      hgood hdec (by first | rfl | decide) hc
  -- the run at the FLAT state
  have hexf := hexe (wflatSt σ) b (BitVec.addInt pc 4) Lpriv Lmisa hR
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rd v
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)) rd rd0 v hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd v)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %_hstep %hdevt0 %hpost %hQ Hm' Hclk' Hpc'
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨-, hdevs, -, -, -, hwsle, hwf', hbnd'⟩ := hpost
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
      obtain ⟨j, hj, rfl⟩ := weffsTouchRegonly al4 pc a haccpc ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  · iapply Hcont $$ %σ'.wmWs %hwsle Hm' Hclk' [Hpc' Hnpc] Hrdc HK Hhws
    unfold pcIs
    iframe Hpc' Hnpc

/-! ### 5a. `csrr rd, menvcfg` -- plain funnel, Ext_U-gated -/

/-- Rocq `wwp_csrr_menvcfg_leaf` (deviation 5). -/
theorem wwpCsrrMenvcfgLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (rd0 npc0 : BitVec 64) (c : MConf) (q : Qp) (D : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x30A#12, zreg, .Regidx rd, .CSRRS), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x30A#12, zreg, .Regidx rd, .CSRRS), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) c.menvcfg -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrdc #Hbs Hhws Hcont
  icases (WeakLeafCsrrM.mConfHalves cpu q c).1 $$ Hm with ⟨Hm1, Hm2⟩
  iapply WeakLeafCsrrM.wwpCsrrCore gen cpu al4 pc w 0x30A#12 rd c.menvcfg rd0 npc0 c (DFrac.own q.half)
    (fun f => f .menvcfg = c.menvcfg) (mConf cpu (DFrac.own q.half) c) D dst ws
    (fun f => (WeakLeafCsrrM.mConfCsrFacts cpu _ c f).trans (wand_mono_right (pure_mono fun h => h.2.2.1)))
    (fun f b h => by rw [← h]; exact (RegFile.set_other _ _ _ _ (by decide)).symm)
    (fun s0 b x hp hm hv => WeakLeafCsrrM.execEffCsrrMenvcfgAt s0 b x rd _ hrd hp hm hv)
    hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec $$ Hm1 Hclk Hm2 Hpc Hnpc Hrdc Hbs Hhws
  iintro %ws' %hle Hm1 Hclk Hpc Hrdc Hm2 Hhws
  iapply Hcont $$ %ws' %hle [Hm1 Hm2] Hclk Hpc Hrdc Hhws
  iapply (WeakLeafCsrrM.mConfHalves cpu q c).2
  iframe Hm1 Hm2

/-! ### 5b. `csrr rd, mcounteren` -- plain funnel, Ext_U-gated, 32-bit CSR -/

/-- Rocq `wwp_csrr_mcounteren_leaf` (deviation 5). -/
theorem wwpCsrrMcounterenLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (rd0 npc0 : BitVec 64) (c : MConf) (q : Qp) (D : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x306#12, zreg, .Regidx rd, .CSRRS), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x306#12, zreg, .Regidx rd, .CSRRS), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) (zero_extend (m := 64) c.mcounteren) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrdc #Hbs Hhws Hcont
  icases (WeakLeafCsrrM.mConfHalves cpu q c).1 $$ Hm with ⟨Hm1, Hm2⟩
  iapply WeakLeafCsrrM.wwpCsrrCore gen cpu al4 pc w 0x306#12 rd (zero_extend (m := 64) c.mcounteren)
    rd0 npc0 c (DFrac.own q.half)
    (fun f => f .mcounteren = c.mcounteren) (mConf cpu (DFrac.own q.half) c) D dst ws
    (fun f => (WeakLeafCsrrM.mConfCsrFacts cpu _ c f).trans (wand_mono_right (pure_mono fun h => h.2.2.2)))
    (fun f b h => by rw [← h]; exact (RegFile.set_other _ _ _ _ (by decide)).symm)
    (fun s0 b x hp hm hv => WeakLeafCsrrM.execEffCsrrMcounterenAt s0 b x rd _ hrd hp hm hv)
    hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec $$ Hm1 Hclk Hm2 Hpc Hnpc Hrdc Hbs Hhws
  iintro %ws' %hle Hm1 Hclk Hpc Hrdc Hm2 Hhws
  iapply Hcont $$ %ws' %hle [Hm1 Hm2] Hclk Hpc Hrdc Hhws
  iapply (WeakLeafCsrrM.mConfHalves cpu q c).2
  iframe Hm1 Hm2

/-! ### 5c. `csrr rd, sie` -- plain funnel, Ext_S-gated, a view of mie & mideleg -/

/-- Rocq `wwp_csrr_sie_leaf` (deviation 5). -/
theorem wwpCsrrSieLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (rd0 npc0 : BitVec 64) (c : MConf) (q : Qp) (D : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x104#12, zreg, .Regidx rd, .CSRRS), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x104#12, zreg, .Regidx rd, .CSRRS), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) (lower_mie c.mie c.mideleg) -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hrdc #Hbs Hhws Hcont
  icases (WeakLeafCsrrM.mConfHalves cpu q c).1 $$ Hm with ⟨Hm1, Hm2⟩
  iapply WeakLeafCsrrM.wwpCsrrCore gen cpu al4 pc w 0x104#12 rd (lower_mie c.mie c.mideleg)
    rd0 npc0 c (DFrac.own q.half)
    (fun f => f .mie = c.mie ∧ f .mideleg = c.mideleg) (mConf cpu (DFrac.own q.half) c) D dst ws
    (fun f => (WeakLeafCsrrM.mConfCsrFacts cpu _ c f).trans
      (wand_mono_right (pure_mono fun h => ⟨h.1, h.2.1⟩)))
    (fun f b h => ⟨by rw [← h.1]; exact (RegFile.set_other _ _ _ _ (by decide)).symm,
      by rw [← h.2]; exact (RegFile.set_other _ _ _ _ (by decide)).symm⟩)
    (fun s0 b x hp hm hv => WeakLeafCsrrM.execEffCsrrSieAt s0 b x rd _ _ hrd hp hm hv.1 hv.2)
    hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec $$ Hm1 Hclk Hm2 Hpc Hnpc Hrdc Hbs Hhws
  iintro %ws' %hle Hm1 Hclk Hpc Hrdc Hm2 Hhws
  iapply Hcont $$ %ws' %hle [Hm1 Hm2] Hclk Hpc Hrdc Hhws
  iapply (WeakLeafCsrrM.mConfHalves cpu q c).2
  iframe Hm1 Hm2

/-! ### 5d. `csrr rd, mhartid` -- plain funnel, no gate -/

/-- Rocq `wwp_csrr_mhartid_leaf` (deviation 5). -/
theorem wwpCsrrMhartidLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (mhartid_in rd0 npc0 : BitVec 64) (c : MConf) (q : Qp) (D : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0xF14#12, zreg, .Regidx rd, .CSRRS), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0xF14#12, zreg, .Regidx rd, .CSRRS), dst) →
    mConf (GF := GF) cpu (DFrac.own q) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      Register.mhartid ↦ᵣ[cpu] mhartid_in -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own q) c -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) mhartid_in -∗
        Register.mhartid ↦ᵣ[cpu] mhartid_in -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec
  iintro Hm Hclk Hpc Hnpc Hmh Hrdc #Hbs Hhws Hcont
  iapply WeakLeafCsrrM.wwpCsrrCore gen cpu al4 pc w 0xF14#12 rd mhartid_in rd0 npc0 c (DFrac.own q)
    (fun f => f .mhartid = mhartid_in) (Register.mhartid ↦ᵣ[cpu] mhartid_in) D dst ws
    (fun f => wand_intro (reg_valid cpu f .mhartid _ mhartid_in))
    (fun f b h => by rw [← h]; exact (RegFile.set_other _ _ _ _ (by decide)).symm)
    (fun s0 b x hp _ hv => WeakLeafCsrrM.execEffCsrrMhartidAt s0 b x rd _ hrd hp hv)
    hgid hmok hpmp hal2 hal4 hrd hdecf hagree hDmi hgood hdec $$ Hm Hclk Hmh Hpc Hnpc Hrdc Hbs Hhws
  iintro %ws' %hle Hm Hclk Hpc Hrdc Hmh Hhws
  iapply Hcont $$ %ws' %hle Hm Hclk Hpc Hrdc Hmh Hhws

/-! ### 5e. `csrr rd, mstatus` -- the CONFIG funnel (deviation 6) -/

/-- Rocq `wwp_csrr_mstatus_leaf` (deviation 6). -/
theorem wwpCsrrMstatusLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rd : BitVec 5) (ms0 rd0 npc0 : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) (D : Register → Bool)
    (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rd.toNat ≠ 0 →
    (_get_Mstatus_MIE ms0 == 1#1) = false →
    (_get_Mstatus_MPRV ms0 == 1#1) = false →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS), t)) →
    (∀ rs : RegFile,
      rs .cur_privilege = .Machine →
      rs .misa = misaC →
      rs .mseccfg = 0#64 →
      ∀ r, D r = true → rs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS), dst) →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms0 -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rd (DFrac.own 1) rd0 -∗
      winstrBytes (GF := GF) pc (.F_Base w) -∗
      hartWs (GF := GF) cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] ms0 -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rd (DFrac.own 1) ms0 -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgid hpmp hal2 hal4 hrd hmie hmprv hdecf hagree hDmi hgood hdec
  iintro #Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hrdc #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  ihave %hnotRVC := WeakLeafLw4.winstrBytesNotRVC pc w $$ Hbs
  have hdecW : winstrDec (.F_Base w) (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS)) := by
    intro t h1 h2 h3 h4 h5
    simp only [fetchIsRvc, Bool.false_eq_true, ↓reduceIte]
    exact hdecf t h1 h2 h3 h4 h5
  ihave #Hwi := winstrIntro (GF := GF) pc false (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS))
    (.F_Base w) (by first | rfl | decide) rfl hdecW $$ Hbs
  -- the config funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstrConfig gen cpu pc false (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS)) pmpcfg0 ms0
    (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgid haccpc hpmp hmie hmprv
    (wstepCertFr _ _ _ _ (wcertRegonly al4 cpu.val pc)) $$ Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hwi
  unfold wwpCbConfig wmstateNorg
  iintro %σ %b %mt %ip %Lpc0 %hcfg %Lms Hpriv Hms Hpmpc Hlat Hreg
    ⟨%hbnd, %hnv, %hwf, Hdev, Hlogauth, Hwsauth⟩ Hti Hip
  ihave ⟨%hws, Hwsauth, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsauth Hhws]
  · iframe Hwsauth Hhws
  subst hws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc _ hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hram, w', hwok, htext0⟩ := hfok
  obtain ⟨hww, -⟩ := hwok
  subst hww
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := loadSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4) rd ms0
    refine ⟨_, WeakLeafCsrrM.execEffCsrrMstatusAt
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' _ rd ms0 hrd Lpriv Lms, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w (.CSRReg (0x300#12, zreg, .Regidx rd, .CSRRS))
      D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafCsrrTime.fetchInWindowRegonly al4 pc haccpc)
        (WeakLeafCsrrTime.fetchFreshRegonly al4 pc) (fun j hj => (htp j hj).2))
      Lpc0 Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi
      hgood hdec (by first | rfl | decide) hc
  -- the run at the FLAT state
  have hexf := WeakLeafCsrrM.execEffCsrrMstatusAt (wflatSt σ) b (BitVec.addInt pc 4) rd ms0 hrd Lpriv Lms
  have hfacts := loadSexecFacts (wflatSt σ) b (BitVec.addInt pc 4) rd ms0
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  rw [show (((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)) =
      (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs from rfl]
  imod WeakLeafLw4.gprUpdate cpu (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
      (BitVec.addInt pc 4)) rd rd0 ms0 hrd $$ Hreg Hrdc with ⟨Hreg, Hrdc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd ms0)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ hexf
  isplitl [Hreg]
  · iexact Hreg
  isplitl [Hti Hip]
  · iexists mt, ip
    iframe Hti Hip
  inext
  iintro %tick %σ' %t %_hstep %hdevt0 %hpost %hQ Hhs' Hclk' Hpc'
  have hdevt : t.dev = σ.wmDev := by rw [hdevt0, hfacts.2.2.2.1]; rfl
  obtain ⟨-, hdevs, -, -, -, hwsle, hwf', hbnd'⟩ := hpost
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
      obtain ⟨j, hj, rfl⟩ := weffsTouchRegonly al4 pc a haccpc ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdevs, hdevt, hQl]
    iframe Hdev Hlogauth Hwsauth
  · iapply Hcont $$ %σ'.wmWs %hwsle Hhs' Hpriv Hms Hpmpc Hclk' [Hpc' Hnpc] Hrdc Hhws
    unfold pcIs
    iframe Hpc' Hnpc

end leaves

end Weak
