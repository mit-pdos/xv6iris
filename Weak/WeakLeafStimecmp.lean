/-
Weak: **the weak leaf for `csrw stimecmp` (0x14D)** (M4).

Rocq: `iris/WeakLeafStimecmp.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The one register-only csrw whose `write_CSR`
is NOT confined to its own CSR: the 0x14D clause runs `clint_dispatch false`
between the register write and the read-back, which refreshes `mip` (MTIP
from `mtimecmp ≤u mtime`, STIP under Sstc/STCE from `stimecmp ≤u mtime`).  So
the successor state carries an EXTRA `mip` write whose value is existential.
* §1 the `execEff` mirrors (trace `[]`) of the stimecmp cone, every one
  below `execute` EXISTENTIAL in the mip value; the `clint_dispatch false`
  mirror is `WeakTickEff.execEffClintDispatchFalse` (reused).  The successor
  register tower is FOUR deep (`minstret_increment` / `nextPC` / `stimecmp` /
  `mip`), hence the file's own `stimecmpSexecFacts`.
* §2 the leaf `wwpCsrwStimecmpLeaf`.  Rocq opens `clock_inv` inside the
  funnel callback to move `mip`; here (owner decision Q3) the funnel hands the
  callback the OWNED `mip` cell (`clockCells`), so the leaf just
  `reg_update`s it.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WeakLeafCsrw.lean` deviation 1 (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `set_reg` ↦ `ExecSt.setReg`, `subrange_vec_dec v (xlen-1) 0` ↦
   `Sail.BitVec.extractLsb v 63 0`, `csr_stimecmp` ↦ `0x14D#12`, the GPR read
   `register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) …` ↦ `s.gpr rs1`
   under the kept premise `rs1.toNat ≠ 0`); `stimecmp_legalized` (Rocq
   `WpGprCsrwB`) is `ExecSC7.stimecmpLegalized` (reused).
2. §1a: `hartSupports` is pure in Lean (`WeakTickEff` deviation 3):
   `exec_eff_hartSupports_Sstc` is `hartSupports .Ext_Sstc = true`; both
   Sstc probes are the `WeakTickEff` ones re-exported (duplicated names,
   file-qualified).
3. §1c: Lean's `write_CSR 0x14D` is MachCSL's `write_CSR_stimecmp` equation,
   so Rocq's `remember`/`skip_csr_false_clauses_eff`/fold dance is a plain
   bind peel.  §1d goes through `WeakLeafCsrw.execEffExecuteCsrwGprP` and
   `WeakLeafRegOnly`'s check kit, as Rocq.
4. THE LEAF, THE CONFIG INTERFACE (owner decision Q3, `WeakFunnel` deviation
   7): Rocq `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ …
   stimecmp ↦ᵣ stimecmp0` ↦ `mConf cpu (DFrac.own 1) c ⊢ clockCells cpu -∗ …`
   (`pmpcfg0 := c.pmpcfg`, `stimecmp0 := c.stimecmp`, plus `MConf.mok c`);
   the continuation receives `mConf cpu (DFrac.own 1) {c with stimecmp :=
   stimecmpLegalized c.stimecmp rs1v}` and `clockCells cpu`.  The fraction
   is FULL (Rocq: any `q`) because the Lean `mConf` bundles the stimecmp cell
   the instruction writes; for the same reason the leaf runs on
   `WeakFunnelCfg.wwpInstrConfig` (the unbundled config funnel), unbundling
   `mConf` with `mConf_cases` and rebuilding it with `mConf_introW` (Rocq:
   `wwp_instr` + `mmode_config_rebuild`).  No `clock_inv` is opened: `mip`
   arrives owned in the callback.  `GenId`/`CpuId` are the explicit
   `gen`/`cpu`; `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`; `pc_is` ↦
   `pcIs`; the operand cell is `gpr cpu rs1 (DFrac.own 1) rs1v`; decode
   premises as `WeakLeafCsrw` deviation 5.  The fetch pin (O2) of
   `regonlyEs al4 pc` is discharged from `winstrTextPinned` through the
   Lean-only `WeakLeafStimecmp.fetchInWindowRegonly`/`fetchFreshRegonly`.
5. Rocq §3's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_hartSupports_Sstc`
`WeakLeafStimecmp.execEffHartSupportsSstc`, `exec_eff_currentlyEnabled_Sstc`
`WeakLeafStimecmp.execEffCurrentlyEnabledSstc` (both duplicated names,
file-qualified), `exec_eff_is_stimecmp_accessible_M`
`execEffIsStimecmpAccessibleM`, `exec_eff_is_CSR_accessible_stimecmp`
`execEffIsCSRAccessibleStimecmp`, `exec_eff_write_CSR_stimecmp`
`execEffWriteCSRStimecmp`, `exec_eff_csr_id_write_callback_stimecmp`
`execEffCsrIdWriteCallbackStimecmp`, `exec_eff_execute_csrw_stimecmp`
`execEffExecuteCsrwStimecmp`, `stimecmp_sexec_facts` `stimecmpSexecFacts`,
`wwp_csrw_stimecmp_leaf` `wwpCsrwStimecmpLeaf`.  Lean-only (file-qualified):
`WeakLeafStimecmp.execEffStimecmpAt`, `WeakLeafStimecmp.fetchInWindowRegonly`,
`WeakLeafStimecmp.fetchFreshRegonly`.

**Dropped:** nothing (9 Rocq `Lemma`s; Lean 9 theorems + 3 Lean-only).
-/
import Weak.WeakLeafCsrw
import Weak.WeakLeafRegOnly
import Weak.WeakTickEff

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The `execEff` mirrors, trace `[]` -/

/-! ### 1a. The Sstc gate (deviation 2) -/

/-- Rocq `exec_eff_hartSupports_Sstc`. -/
theorem WeakLeafStimecmp.execEffHartSupportsSstc : hartSupports .Ext_Sstc = true :=
  wteExecEffHartSupportsSstc

/-- Rocq `exec_eff_currentlyEnabled_Sstc`. -/
theorem WeakLeafStimecmp.execEffCurrentlyEnabledSstc (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Sstc) s = some (true, s, []) :=
  wteExecEffCurrentlyEnabledSstc s

/-! ### 1b. Accessibility -/

/-- Rocq `exec_eff_is_stimecmp_accessible_M`. -/
theorem execEffIsStimecmpAccessibleM (s : ExecSt) :
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (is_stimecmp_accessible .Machine) s = some (true, s, []) := by
  intro hS
  unfold is_stimecmp_accessible
  rw [execEffBindNil _ _ _ _ _ (WeakLeafEffCommon.execEffCurrentlyEnabledS s), hS]
  simp only [↓reduceIte]
  rw [execEffBindNil _ _ _ _ _ (WeakLeafStimecmp.execEffCurrentlyEnabledSstc s)]
  rfl

/-- Rocq `exec_eff_is_CSR_accessible_stimecmp`. -/
theorem execEffIsCSRAccessibleStimecmp (s : ExecSt) :
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (is_CSR_accessible 0x14D#12 .Machine .CSRWrite) s = some (true, s, []) := by
  intro hS
  rw [is_CSR_accessible_stimecmp]
  exact execEffIsStimecmpAccessibleM s hS

/-! ### 1c. `write_CSR`, existential in the mip value (deviation 3) -/

/-- Rocq `exec_eff_write_CSR_stimecmp`. -/
theorem execEffWriteCSRStimecmp (v : BitVec 64) (s : ExecSt) :
    ∃ mp : BitVec 64,
      execEff (write_CSR 0x14D#12 v) s =
        some (.Ok (Sail.BitVec.extractLsb (stimecmpLegalized (s.regs .stimecmp) v) 63 0),
          (s.setReg .stimecmp (stimecmpLegalized (s.regs .stimecmp) v)).setReg .mip mp, []) := by
  obtain ⟨mp, hcd⟩ :=
    execEffClintDispatchFalse (s.setReg .stimecmp (stimecmpLegalized (s.regs .stimecmp) v))
  refine ⟨mp, ?_⟩
  rw [write_CSR_stimecmp]
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .stimecmp s)]
  unfold stimecmpLegalized at hcd ⊢
  rw [execEffBind0Nil _ _ _ _ _ (execEffWriteReg .stimecmp _ s),
    execEffBind0Nil _ _ _ _ _ hcd,
    execEffBindNil _ _ _ _ _ (execEffReadReg .stimecmp _)]
  rw [setLookupNe .stimecmp .mip _ _ (by decide)]
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_stimecmp`. -/
theorem execEffCsrIdWriteCallbackStimecmp (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x14D#12 d) s = some ((), s, []) := rfl

/-! ### 1d. The end-to-end `execute` mirror, existential in mip -/

/-- Rocq `exec_eff_execute_csrw_stimecmp` (deviation 1). -/
theorem execEffExecuteCsrwStimecmp (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    ∃ mp : BitVec 64,
      execEff (execute (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW))) s =
        some (RETIRE_SUCCESS,
          (s.setReg .stimecmp (stimecmpLegalized (s.regs .stimecmp) (s.gpr rs1))).setReg .mip mp,
          []) := by
  intro _ hpriv hS
  obtain ⟨mp, hw⟩ := execEffWriteCSRStimecmp (s.gpr rs1) s
  refine ⟨mp, ?_⟩
  show execEff (execute_CSRReg 0x14D#12 (.Regidx rs1) zreg .CSRRW) s = _
  have hchk : execEff (check_CSR_result 0x14D#12 .Machine .CSRWrite) s =
      some (.CSR_Check_OK (), s, []) :=
    execEffCheckCSRResultCsrwP _ _ _ (execEffCheckCSRCsrwP _ _ _ (by rfl) (by decide)
      (execEffIsCSRAccessibleStimecmp s hS) (by rw [stateen_stimecmp]; rfl))
  exact execEffExecuteCsrwGprP .Machine 0x14D#12 rs1 s _ _ hpriv hchk (by decide) (by decide)
    (by decide) hw (execEffCsrIdWriteCallbackStimecmp _ _)

/-! ## 1e. The FOUR-deep successor register frame -/

/-- Rocq `stimecmp_sexec_facts`. -/
theorem stimecmpSexecFacts (s0 : ExecSt) (b : Bool) (npc v p : BitVec 64) :
    let sExec := (((s0.setReg .minstret_increment b).setReg .nextPC npc).setReg .stimecmp v).setReg
      .mip p
    sExec.regs .hart_state = s0.regs .hart_state ∧
    sExec.regs .minstret_increment = b ∧
    sExec.mem = s0.mem ∧
    sExec.dev = s0.dev ∧
    sExec.regs .nextPC = npc := by
  intro sExec
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · rw [setLookupNe .hart_state .mip _ _ (by decide), setLookupNe .hart_state .stimecmp _ _ (by decide)]
    leaf_peel .hart_state
  · rw [setLookupNe .minstret_increment .mip _ _ (by decide),
      setLookupNe .minstret_increment .stimecmp _ _ (by decide),
      setLookupNe .minstret_increment .nextPC _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  · rw [setLookupNe .nextPC .mip _ _ (by decide), setLookupNe .nextPC .stimecmp _ _ (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]

/-! ## 2. THE LEAF -/

/-- The csrw-stimecmp `execute` at a pre-written state (Lean-only; the shared
core of the leaf's confined and flat runs). -/
theorem WeakLeafStimecmp.execEffStimecmpAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rs1 : BitVec 5)
    (st0 rs1v : BitVec 64) (hrs1 : rs1.toNat ≠ 0) (hpriv : s0.regs .cur_privilege = .Machine)
    (hmisa : s0.regs .misa = misaC) (hst : s0.regs .stimecmp = st0) (hg : s0.gpr rs1 = rs1v) :
    ∃ mp : BitVec 64,
      execEff (execute (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)))
          ((s0.setReg .minstret_increment b).setReg .nextPC x) =
        some (RETIRE_SUCCESS,
          (((s0.setReg .minstret_increment b).setReg .nextPC x).setReg .stimecmp
            (stimecmpLegalized st0 rs1v)).setReg .mip mp, []) := by
  have hmisa' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .misa = misaC := by
    leaf_peel .misa; exact hmisa
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege =
      .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hst' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .stimecmp = st0 := by
    leaf_peel .stimecmp; exact hst
  have hg' : ((s0.setReg .minstret_increment b).setReg .nextPC x).gpr rs1 = rs1v := by
    rw [WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide), WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide)]
    exact hg
  obtain ⟨mp, h⟩ := execEffExecuteCsrwStimecmp rs1 _ hrs1 hpriv' (by rw [hmisa']; decide)
  rw [hst', hg'] at h
  exact ⟨mp, h⟩

/-- Every i-cache read of the register-only fetch trace lies in the text
window (Lean-only). -/
theorem WeakLeafStimecmp.fetchInWindowRegonly (al4 : Bool) (pc : BitVec 64) (hacc : accWf pc 4) :
    fetchInWindow pc (regonlyEs al4 pc) := by
  intro ak pa n hin _ j hj
  obtain ⟨j', hj', he⟩ := weffsTouchRegonly al4 pc _ hacc ⟨_, hin, j, hj, rfl⟩
  exact ⟨j', hj', he⟩

/-- The register-only fetch trace writes nothing (Lean-only). -/
theorem WeakLeafStimecmp.fetchFreshRegonly (al4 : Bool) (pc : BitVec 64) :
    fetchFresh (regonlyEs al4 pc) := by
  cases al4 <;> simp [regonlyEs, fetchFresh, weffWrites]

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrw_stimecmp_leaf` (deviation 4). -/
theorem wwpCsrwStimecmpLeaf (gen : Nat) (cpu : CPU) (al4 : Bool) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (rs1v npc0 : BitVec 64) (c : MConf) (D : Register → Bool) (dst : ExecSt)
    (ws : Wstate) :
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with stimecmp := stimecmpLegalized c.stimecmp rs1v } -∗
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
  have hmie : (_get_Mstatus_MIE c.mstatus == 1#1) = false := by
    rw [get_Mstatus_MIE_eq, hmok.1]; rfl
  have hmprv : (_get_Mstatus_MPRV c.mstatus == 1#1) = false := by
    rw [get_Mstatus_MPRV_eq, hmok.2]; rfl
  have hwd : winstrDec (.F_Base w) (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)) :=
    fun t h1 h2 h3 h4 h5 => hdecf t h1 h2 h3 h4 h5
  ihave #Hi := winstrIntro pc false (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)) (.F_Base w)
    rfl rfl hwd $$ Hbs
  -- the config funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstrConfig gen cpu pc false (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)) c.pmpcfg
    c.mstatus (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgen haccpc hpmp hmie hmprv
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
  obtain ⟨hww, hnotRVC⟩ := hwok
  subst hww
  -- the two registers the funnel does not read: the source and the CSR
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1) $$ Hreg Hrs1c
    with ⟨%Lrs1, Hreg, Hrs1c⟩
  have Lrs1f : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafCsrw.gprSetRegNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1
  icases keepPure (wand_intro (reg_valid cpu _ .stimecmp _ c.stimecmp)) $$ Hreg Hstimecmp
    with ⟨%Lcsra, Hreg, Hstimecmp⟩
  have Lcsr : σ.wmRegs .stimecmp = c.stimecmp := by
    rw [regAtFlat .stimecmp σ b (by decide)] at Lcsra
    exact Lcsra
  -- premise (c): the execute mirror, at the CONFINED state (its own mip value)
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨mp', he⟩ := WeakLeafStimecmp.execEffStimecmpAt
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4) rs1
      c.stimecmp rs1v hrs1 Lpriv Lmisa Lcsr Lrs1f
    obtain ⟨F1, F2, F3, -, -⟩ := stimecmpSexecFacts
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4)
      (stimecmpLegalized c.stimecmp rs1v) mp'
    refine ⟨_, he, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w
      (.CSRReg (0x14D#12, .Regidx rs1, zreg, .CSRRW)) D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafStimecmp.fetchInWindowRegonly al4 pc haccpc)
        (WeakLeafStimecmp.fetchFreshRegonly al4 pc) (fun j hj => (htp j hj).2))
      Lpc Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi
      hgood hdec rfl hc
  -- the run at the FLAT state; its mip value is the one the cell is moved to
  obtain ⟨mp, Hef⟩ := WeakLeafStimecmp.execEffStimecmpAt (wflatSt σ) b (BitVec.addInt pc 4) rs1
    c.stimecmp rs1v hrs1 Lpriv Lmisa Lcsr Lrs1f
  obtain ⟨-, -, -, G4, G5⟩ := stimecmpSexecFacts (wflatSt σ) b (BitVec.addInt pc 4)
    (stimecmpLegalized c.stimecmp rs1v) mp
  -- the three register writes the `execute` performs (mip: the owned clock cell)
  imod (wand_intro (reg_update cpu ((wflatSt σ).setReg .minstret_increment b).regs .nextPC npc0
    (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu
    ((((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC (BitVec.addInt pc 4)) .stimecmp
    c.stimecmp (stimecmpLegalized c.stimecmp rs1v))) $$ Hreg Hstimecmp with ⟨Hreg, Hstimecmp⟩
  imod (wand_intro (reg_update cpu
    (((((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC (BitVec.addInt pc 4)).set
      .stimecmp (stimecmpLegalized c.stimecmp rs1v)) .mip ip mp)) $$ Hreg Hip with ⟨Hreg, Hip⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists (((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
    .stimecmp (stimecmpLegalized c.stimecmp rs1v)).setReg .mip mp)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ Hef
  isplitl [Hreg]
  · rw [show (((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
        .stimecmp (stimecmpLegalized c.stimecmp rs1v)).setReg .mip mp).regs =
        (((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)).set
        .stimecmp (stimecmpLegalized c.stimecmp rs1v)).set .mip mp) from rfl]
    iexact Hreg
  isplitl [Hmt Hip]
  · iexists mt, mp
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
  · -- rebuild the config bundle at the written stimecmp
    ihave Hm' := mConf_introW cpu (DFrac.own 1) { c with stimecmp := stimecmpLegalized c.stimecmp rs1v }
      $$ Hpriv Hhs Hms Hmie Hmideleg Hmedeleg Hmepc Hsatp Hmenvcfg Hmcounteren Hmtimecmp Hstimecmp
        Hpmpc Hpmpaddr_n Hhw
    iapply Hcont $$ %σ'.wmWs %(by rw [hws]; exact hQw) Hm' Hclk [HPC Hnpc] Hrs1c Hhws
    unfold pcIs
    iframe HPC Hnpc

end leaf

end Weak
