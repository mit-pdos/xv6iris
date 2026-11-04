/-
Weak: **the SIMPLE-LEGALIZER csrw leaves** (M4, `start()`/`timerinit()`):
medeleg / mideleg / mepc / mcounteren / menvcfg.

Rocq: `iris/WeakLeafCsrw2.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The weak twins of `WpGprCsrwA`/`WpGprCsrwB`'s
register-only csrw leaves whose `write_CSR` reads nothing but the target CSR
itself.  Each is `WeakLeafCsrw.wwpCsrwMstatusLeaf`'s recipe driven through the
alignment-generic register-only kit (`WeakLeafRegOnly`): every leaf takes the
fetch alignment `al4` as a parameter and covers both the 4-aligned and the
2-not-4-aligned call sites of `start()`/`timerinit()` with one statement.
Per CSR this file owes: the `write_CSR` trace-`[]` mirror (the `doCSR` /
`execute_CSRReg` spine is `WeakLeafCsrw` §1f's, the check dispatchers are
`WeakLeafRegOnly` §3's); the end-to-end `execute` mirror; the leaf.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WeakLeafCsrw.lean` deviation 1 (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `set_reg` ↦ `ExecSt.setReg`, `uint x` ↦ `x.toNat`, `add_vec_int` ↦
   `BitVec.addInt`, `zero_extend' 64` ↦ `zero_extend (m := 64)`); the CSR
   numbers are literals (`csr_medeleg` `0x302#12`, `csr_mideleg` `0x303#12`,
   `csr_mepc` `0x341#12`, `csr_mcounteren` `0x306#12`, `csr_menvcfg`
   `0x30A#12`); the GPR read `if uint rs1 =? 0 then zero_reg else …` and
   `register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))` are `s.gpr rs1`
   (the `uint rs1 ≠ 0` premises are kept).  `write_CSR`'s arm is MachCSL's
   `write_CSR_<csr>` equation (Lean's `write_CSR` is a `match`, so
   `skip_csr_false_clauses_eff` is not needed).
2. `hartSupports` is a pure `Bool` function in Lean (no fuel, no monad;
   `WeakLeafEffCommon` deviation 9): every Rocq `exec_eff_hartSupports_X s :
   exec_eff (hartSupports X) s = Some (true, s, [])` is `hartSupports .Ext_X =
   true` (by `decide +kernel`).  `currentlyEnabled` has no fuel either, so the
   `exec_eff_currentlyEnabled_X` proofs are a plain unfolding and the Ltac
   `crush_inner_cE_S_eff` is a macro rewriting with
   `WeakLeafEffCommon.execEffCurrentlyEnabledS` (argument dropped).
3. Lean's `legalize_xepc` is PURE: `exec_eff_legalize_xepc` is the equation
   `legalize_xepc v = WeakLeafCsrw2.mepcVal v`.
4. The SC values Rocq reuses (`WpGprCsrwB.mideleg_legalized`,
   `WpGprCsrwA.mepc_val`, `WpGprCsrwA.menvcfg_legalized`,
   `WpGprCsrwA.menvcfg_cbie`; not in the Lean tree) are the Lean-only
   file-qualified definitions `WeakLeafCsrw2.midelegLegalized`, `mepcVal`,
   `menvcfgLegalized`, `menvcfgCbie`, literally.
5. §3 / `exec_eff_check_CSR_result_*` side conditions: the `vm_compute`
   facts are `rfl`/`decide`/`csr_dispatch_eq`; `is_CSR_accessible` and
   `stateen_allows_CSR_access` are MachCSL's `is_CSR_accessible_<csr>` /
   `stateen_<csr>` equations (menvcfg's `and_boolM` in the Lean shape,
   `WeakLeafRegOnly` deviation 4).
6. THE LEAVES, the config interface (owner decision Q3, `WeakFunnel`
   deviation 7): Rocq `mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q}
   pmpcfg0 -∗ … -∗ <csr> ↦ᵣ csr0` ↦ `mConf cpu (DFrac.own 1) c ⊢ clockCells
   cpu -∗ …`, and the continuation receives `mConf cpu (DFrac.own 1) {c with
   <csr> := new}` and `clockCells cpu`.  In Lean the five CSRs are cells OF
   `mConf` (MachCSL.MConf), so Rocq's separate full CSR cell is merged into
   the config at full ownership (`csr0 := c.<csr>`, `pmpcfg0 := c.pmpcfg`;
   premises `MConf.mok c`, `pmpAllowsAll c.pmpcfg`); the leaf unbundles the
   config (`mConf_cases`), runs the CONFIG funnel `WeakFunnelCfg.wwpInstrConfig`
   (the plain `wwpInstr` holds `mConf` across the step and could not write the
   CSR) and rebuilds it (`confCells_intro`).  `GenId`/`CpuId` ↦ explicit
   `gen`/`cpu`; `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`; `pc_is` ↦
   `pcIs`; the operand cell ↦ `gpr cpu rs1 (DFrac.own 1) rs1v`; the decode /
   agreement premises as `WeakLeafCsrw` deviation 5.  The certificate's fetch
   pin is discharged from `winstrTextPinned` (`fetchPinOfText`).
7. The five leaves share ONE Lean-only proof: `WeakLeafCsrw2.wwpCsrwLeaf`
   (the cell-form leaf, generic in the CSR register `r`, its number and its
   `execute` fact), with `WeakLeafCsrw2.execEffCsrwAt` (the execute at the
   funnel's pre-written state), `WeakLeafCsrw2.fetchInWindowRegonly` /
   `fetchFreshRegonly` (the O2 fetch-pin facts of `regonlyEs`),
   `WeakLeafCsrw2.execEffOfEqPure` and `WeakLeafCsrw2.mokBits`.
8. Rocq's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  §1 `exec_eff_write_CSR_medeleg`
`execEffWriteCSRMedeleg`, `exec_eff_csr_id_write_callback_medeleg`
`execEffCsrIdWriteCallbackMedeleg`, `exec_eff_execute_csrw_medeleg`
`execEffExecuteCsrwMedeleg`, `wwp_csrw_medeleg_leaf` `wwpCsrwMedelegLeaf`.
§2 `exec_eff_hartSupports_Sscofpmf` `execEffHartSupportsSscofpmf`,
`exec_eff_hartSupports_Zihpm` `execEffHartSupportsZihpm`,
`exec_eff_currentlyEnabled_Sscofpmf` `execEffCurrentlyEnabledSscofpmf`,
`exec_eff_legalize_mideleg` `execEffLegalizeMideleg`,
`exec_eff_write_CSR_mideleg` `execEffWriteCSRMideleg`,
`exec_eff_csr_id_write_callback_mideleg` `execEffCsrIdWriteCallbackMideleg`,
`exec_eff_execute_csrw_mideleg` `execEffExecuteCsrwMideleg`,
`wwp_csrw_mideleg_leaf` `wwpCsrwMidelegLeaf`.  §3 `exec_eff_hartSupports_Zca`
`WeakLeafCsrw2.execEffHartSupportsZca` (duplicated name),
`exec_eff_legalize_xepc` `execEffLegalizeXepc`, `exec_eff_write_CSR_mepc`
`execEffWriteCSRMepc`, `exec_eff_csr_id_write_callback_mepc`
`execEffCsrIdWriteCallbackMepc`, `exec_eff_execute_csrw_mepc`
`execEffExecuteCsrwMepc`, `wwp_csrw_mepc_leaf` `wwpCsrwMepcLeaf`.  §4
`exec_eff_write_CSR_mcounteren` `execEffWriteCSRMcounteren`,
`exec_eff_csr_id_write_callback_mcounteren`
`execEffCsrIdWriteCallbackMcounteren`, `exec_eff_execute_csrw_mcounteren`
`execEffExecuteCsrwMcounteren`, `exec_eff_execute_csrw_mcounteren_full`
`execEffExecuteCsrwMcounterenFull`, `wwp_csrw_mcounteren_leaf`
`wwpCsrwMcounterenLeaf`.  §5 `exec_eff_hartSupports_Zicfiss`
`execEffHartSupportsZicfiss`, `exec_eff_hartSupports_Zicboz`
`execEffHartSupportsZicboz`, `exec_eff_hartSupports_Zicbom`
`execEffHartSupportsZicbom`, `exec_eff_hartSupports_Sstc`
`WeakLeafCsrw2.execEffHartSupportsSstc` (duplicated),
`exec_eff_hartSupports_Smnpm` `execEffHartSupportsSmnpm`,
`exec_eff_hartSupports_Svadu` `execEffHartSupportsSvadu`,
`exec_eff_hartSupports_Svpbmt` `execEffHartSupportsSvpbmt`,
`exec_eff_currentlyEnabled_Zicboz` `execEffCurrentlyEnabledZicboz`,
`exec_eff_currentlyEnabled_Zicbom` `execEffCurrentlyEnabledZicbom`,
`exec_eff_currentlyEnabled_Sstc` `WeakLeafCsrw2.execEffCurrentlyEnabledSstc`
(duplicated), `exec_eff_currentlyEnabled_Smnpm`
`execEffCurrentlyEnabledSmnpm`, `exec_eff_currentlyEnabled_Svadu`
`WeakLeafCsrw2.execEffCurrentlyEnabledSvadu` (duplicated),
`crush_inner_cE_S_eff` (Ltac) `crush_inner_cE_S_eff` (macro),
`exec_eff_currentlyEnabled_Svpbmt` `execEffCurrentlyEnabledSvpbmt`,
`exec_eff_legalize_xenvcfg_cbie` `execEffLegalizeXenvcfgCbie`,
`exec_eff_legalize_menvcfg` `execEffLegalizeMenvcfg`,
`exec_eff_write_CSR_menvcfg` `execEffWriteCSRMenvcfg`,
`exec_eff_csr_id_write_callback_menvcfg` `execEffCsrIdWriteCallbackMenvcfg`,
`exec_eff_execute_csrw_menvcfg` `execEffExecuteCsrwMenvcfg`,
`wwp_csrw_menvcfg_leaf` `wwpCsrwMenvcfgLeaf`.
Lean-only (file-qualified): the definitions of deviation 4 and the helpers of
deviation 7.

**Dropped:** nothing (42 Rocq `Lemma`s + 1 `Ltac`; Lean 42 theorems + 1 macro,
plus 4 Lean-only definitions and 6 Lean-only theorems).
-/
import Weak.WeakLeafCsrw
import Weak.WeakLeafRegOnly

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. Lean-only helpers (deviation 7) -/

/-- An `execEff` of a computation that is `pure` (Lean-only). -/
theorem WeakLeafCsrw2.execEffOfEqPure {X : Type} (m : SailM X) (x : X) (s : ExecSt)
    (h : m = pure x) : execEff m s = some (x, s, []) := by
  rw [h]; rfl

/-- The two `mstatus` bits the config funnel wants, off `MConf.mok` (Lean-only). -/
theorem WeakLeafCsrw2.mokBits (c : MConf) (hmok : MConf.mok c) :
    (_get_Mstatus_MIE c.mstatus == 1#1) = false ∧ (_get_Mstatus_MPRV c.mstatus == 1#1) = false := by
  refine ⟨?_, ?_⟩
  · rw [get_Mstatus_MIE_eq, hmok.1]; rfl
  · rw [get_Mstatus_MPRV_eq, hmok.2]; rfl

/-- The fetch-only trace reads inside the text window, at either alignment (Lean-only). -/
theorem WeakLeafCsrw2.fetchInWindowRegonly (al4 : Bool) (pc : BitVec 64) (hacc : accWf pc 4) :
    fetchInWindow pc (regonlyEs al4 pc) := by
  intro ak pa n hin _ j hj
  obtain ⟨j', hj', he⟩ := weffsTouchRegonly al4 pc (WeakInterp.accAddr pa j) hacc ⟨_, hin, ⟨j, hj, rfl⟩⟩
  exact ⟨j', hj', he⟩

/-- The fetch-only trace is fetch-fresh (Lean-only). -/
theorem WeakLeafCsrw2.fetchFreshRegonly (al4 : Bool) (pc : BitVec 64) :
    fetchFresh (regonlyEs al4 pc) := by
  cases al4 <;> simp [regonlyEs, fetchFresh, weffWrites]

/-- The csrw `execute` of a register-only CSR, at the funnel's pre-written state
(Lean-only; the shared core of a leaf's confined and flat runs). -/
theorem WeakLeafCsrw2.execEffCsrwAt (csr : BitVec 12) (r : Register) (c0 c1 : RegisterType r)
    (rs1 : BitVec 5) (rs1v : BitVec 64)
    (hrmi : Register.minstret_increment ≠ r) (hrnpc : Register.nextPC ≠ r)
    (hexe : ∀ s : ExecSt, s.regs .cur_privilege = .Machine → s.regs .misa = misaC →
      s.regs r = c0 → s.gpr rs1 = rs1v →
      execEff (execute (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW))) s =
        some (RETIRE_SUCCESS, s.setReg r c1, []))
    (s0 : ExecSt) (b : Bool) (x : BitVec 64)
    (hpriv : s0.regs .cur_privilege = .Machine) (hmisa : s0.regs .misa = misaC)
    (hcsr : s0.regs r = c0) (hg : s0.gpr rs1 = rs1v) :
    execEff (execute (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setReg r c1, []) := by
  apply hexe
  · leaf_peel .cur_privilege; exact hpriv
  · leaf_peel .misa; exact hmisa
  · rw [setLookupNe _ _ _ _ (Ne.symm hrnpc), setLookupNe _ _ _ _ (Ne.symm hrmi)]; exact hcsr
  · rw [WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide), WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide)]
    exact hg

section leafGen
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- THE SHARED LEAF (Lean-only, deviation 7): a register-only csrw of the CSR
cell `r`, on the config funnel, with the cells unbundled.  The five Rocq leaves
are its instances. -/
theorem WeakLeafCsrw2.wwpCsrwLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64)
    (w : BitVec 32) (rs1 : BitVec 5) (csr : BitVec 12) (r : Register) (c0 c1 : RegisterType r)
    (ms0 rs1v npc0 : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n) (D : Register → Bool)
    (dst : ExecSt) (ws : Wstate)
    (hrhs : Register.hart_state ≠ r) (hrmi : Register.minstret_increment ≠ r)
    (hrnpc : Register.nextPC ≠ r)
    (hexe : ∀ s : ExecSt, s.regs .cur_privilege = .Machine → s.regs .misa = misaC →
      s.regs r = c0 → s.gpr rs1 = rs1v →
      execEff (execute (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW))) s =
        some (RETIRE_SUCCESS, s.setReg r c1, [])) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    (_get_Mstatus_MIE ms0 == 1#1) = false →
    (_get_Mstatus_MPRV ms0 == 1#1) = false →
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW), dst) →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms0 -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      r ↦ᵣ[cpu] c0 -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] ms0 -∗
        Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        r ↦ᵣ[cpu] c1 -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hpmp hal2 hal4 hrs1 hmie hmprv hdecf hagree hDmi hgood hdec
  iintro #Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  have hwd : winstrDec (.F_Base w) (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW)) :=
    fun t h1 h2 h3 h4 h5 => hdecf t h1 h2 h3 h4 h5
  ihave #Hi := winstrIntro pc false (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW)) (.F_Base w)
    rfl rfl hwd $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstrConfig gen cpu pc false (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW)) pmpcfg0 ms0
    (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgen haccpc hpmp hmie hmprv
    (wstepCertFr cpu.val pc _ _ (wcertRegonly al4 cpu.val pc))
    $$ Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hi
  unfold wwpCbConfig wmstateNorg
  iintro %σ %b %mt %ip %Lpc %hcfg %_Lms Hpriv Hms Hpmpc Hlat Hreg
    ⟨%hbnd, %hnv, %hwf, Hdev, Hlog, Hwsa⟩ Hmt Hip
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
  icases keepPure (wand_intro (reg_valid cpu _ r _ c0)) $$ Hreg Hcsr with ⟨%Lcsr0, Hreg, Hcsr⟩
  have Lcsr : σ.wmRegs r = c0 := by
    rw [← Lcsr0]
    exact (RegFile.set_other _ _ _ _ (Ne.symm hrmi)).symm
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := csrwSexecFactsR r
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4) c1
      hrhs hrmi hrnpc
    refine ⟨_, WeakLeafCsrw2.execEffCsrwAt csr r c0 c1 rs1 rs1v hrmi hrnpc hexe _ b' _ Lpriv Lmisa
      Lcsr Lrs1f, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w
      (.CSRReg (csr, .Regidx rs1, zreg, .CSRRW)) D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafCsrw2.fetchInWindowRegonly al4 pc haccpc)
        (WeakLeafCsrw2.fetchFreshRegonly al4 pc) (fun j hj => (htp j hj).2))
      Lpc Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS (by rw [Lmisa]; decide) LmIE Lelp
      hal2 hal4 hram (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec)
      hDmi hgood hdec rfl hc
  -- the run at the FLAT state
  have Hef := WeakLeafCsrw2.execEffCsrwAt csr r c0 c1 rs1 rs1v hrmi hrnpc hexe (wflatSt σ) b
    (BitVec.addInt pc 4) Lpriv Lmisa Lcsr Lrs1f
  obtain ⟨-, -, -, G4, G5⟩ := csrwSexecFactsR r (wflatSt σ) b (BitVec.addInt pc 4) c1 hrhs hrmi hrnpc
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu ((wflatSt σ).setReg .minstret_increment b).regs .nextPC npc0
    (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu
    ((((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC (BitVec.addInt pc 4)) r c0 c1))
    $$ Hreg Hcsr with ⟨Hreg, Hcsr⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg r c1)
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ Hef
  isplitl [Hreg]
  · rw [show ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
        r c1).regs =
        ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)).set r c1)
        from rfl]
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
  · iapply Hcont $$ %σ'.wmWs %(by rw [hws]; exact hQw) Hhs Hpriv Hms Hpmpc Hclk [HPC Hnpc] Hrs1c Hcsr
      Hhws
    unfold pcIs
    iframe HPC Hnpc

end leafGen

/-! ## 1. medeleg (0x302; Ext_S-gated, pure legalize) — THE TEMPLATE -/

/-- Rocq `exec_eff_write_CSR_medeleg`. -/
theorem execEffWriteCSRMedeleg (v : BitVec 64) (s : ExecSt) :
    execEff (write_CSR 0x302#12 v) s =
      some (.Ok (legalize_medeleg (s.regs .medeleg) v),
        s.setReg .medeleg (legalize_medeleg (s.regs .medeleg) v), []) := by
  rw [write_CSR_medeleg]
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .medeleg s),
    execEffBind0Nil _ _ _ _ _ (execEffWriteReg .medeleg _ s),
    execEffBindNil _ _ _ _ _ (execEffReadReg .medeleg _)]
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_medeleg`. -/
theorem execEffCsrIdWriteCallbackMedeleg (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x302#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_execute_csrw_medeleg` (deviation 1). -/
theorem execEffExecuteCsrwMedeleg (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x302#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .medeleg (legalize_medeleg (s.regs .medeleg) (s.gpr rs1)), []) := by
  intro _ hpriv hS
  show execEff (execute_CSRReg 0x302#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x302#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwS _ s hS
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (by csr_dispatch_eq)) (by decide)
      (is_CSR_accessible_medeleg _ _) (WeakLeafCsrw2.execEffOfEqPure _ _ s (stateen_medeleg _ _)))
    (by decide) (by decide) (by decide)
    (execEffWriteCSRMedeleg _ s) (execEffCsrIdWriteCallbackMedeleg _ _)

section leafMedeleg
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrw_medeleg_leaf` (deviation 6). -/
theorem wwpCsrwMedelegLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (c : MConf) (rs1v npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt)
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
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x302#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x302#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with medeleg := legalize_medeleg c.medeleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hal2 hal4 hrs1 hdecf hagree hDmi hgood hdec
  obtain ⟨hmie, hmprv⟩ := WeakLeafCsrw2.mokBits c hmok
  iintro Hm Hclk Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  icases mConf_cases cpu (DFrac.own 1) c $$ Hm with
    ⟨Hpriv, Hhs, Hms, Hmie, Hmid, Hmed, Hmepc, Hsatp, Hmenv, Hmcnt, Hmtc, Hstc, Hpmpc, Hpmpa, #Hhw⟩
  iapply WeakLeafCsrw2.wwpCsrwLeaf al4 gen cpu pc w rs1 0x302#12 .medeleg c.medeleg
    (legalize_medeleg c.medeleg rs1v) c.mstatus rs1v npc0 c.pmpcfg D dst ws (by decide) (by decide)
    (by decide)
    (fun s h1 h2 h3 h4 => by
      have h := execEffExecuteCsrwMedeleg rs1 s hrs1 h1 (by rw [h2]; decide)
      rw [h3, h4] at h
      exact h)
    hgen hpmp hal2 hal4 hrs1 hmie hmprv hdecf hagree hDmi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpmpc Hpc Hnpc Hrs1c Hmed Hbs Hhws
  iintro %ws' %hle Hhs Hpriv Hms Hpmpc Hclk Hpcs Hrs1c Hmed Hhws
  iapply Hcont $$ %ws' %hle
    [Hpriv Hhs Hms Hmie Hmid Hmed Hmepc Hsatp Hmenv Hmcnt Hmtc Hstc Hpmpc Hpmpa] Hclk Hpcs Hrs1c Hhws
  iapply confCells_intro
  simp only []
  iframe
  iexact Hhw

end leafMedeleg

/-! ## 2. mideleg (0x303; Ext_S-gated, MONADIC legalize) -/

/-- Rocq `exec_eff_hartSupports_Sscofpmf` (deviation 2). -/
theorem execEffHartSupportsSscofpmf : hartSupports .Ext_Sscofpmf = true := by decide +kernel

/-- Rocq `exec_eff_hartSupports_Zihpm` (deviation 2). -/
theorem execEffHartSupportsZihpm : hartSupports .Ext_Zihpm = true := by decide +kernel

/-- Rocq `exec_eff_currentlyEnabled_Sscofpmf`. -/
theorem execEffCurrentlyEnabledSscofpmf (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Sscofpmf) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSscofpmf, ↓reduceIte]
  rw [currentlyEnabled]
  simp only [execEffHartSupportsZihpm, ↓reduceIte, execEffRecCEZicsrAny]

/-- Rocq `WpGprCsrwB.mideleg_legalized` (deviation 4; the old value is unused). -/
def WeakLeafCsrw2.midelegLegalized (_o v : BitVec 64) : BitVec 64 :=
  let v := Mk_Minterrupts (v &&& plat_mideleg_delegatable_bits)
  _update_Minterrupts_SSI
    (_update_Minterrupts_STI
      (_update_Minterrupts_SEI
        (_update_Minterrupts_LCOFI v (_get_Minterrupts_LCOFI v))
        (_get_Minterrupts_SEI v))
      (_get_Minterrupts_STI v))
    (_get_Minterrupts_SSI v)

/-- Rocq `exec_eff_legalize_mideleg`. -/
theorem execEffLegalizeMideleg (o v : BitVec 64) (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (legalize_mideleg o v) s = some (WeakLeafCsrw2.midelegLegalized o v, s, []) := by
  unfold legalize_mideleg WeakLeafCsrw2.midelegLegalized
  exec_eff_steps [execEffCurrentlyEnabledSscofpmf, WeakLeafEffCommon.execEffCurrentlyEnabledS, hS]

/-- Rocq `exec_eff_write_CSR_mideleg`. -/
theorem execEffWriteCSRMideleg (v : BitVec 64) (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (write_CSR 0x303#12 v) s =
      some (.Ok (WeakLeafCsrw2.midelegLegalized (s.regs .mideleg) v),
        s.setReg .mideleg (WeakLeafCsrw2.midelegLegalized (s.regs .mideleg) v), []) := by
  rw [write_CSR_mideleg]
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .mideleg s),
    execEffBindNil _ _ _ _ _ (execEffLegalizeMideleg (s.regs .mideleg) v s hS),
    execEffBind0Nil _ _ _ _ _ (execEffWriteReg .mideleg _ s),
    execEffBindNil _ _ _ _ _ (execEffReadReg .mideleg _)]
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_mideleg`. -/
theorem execEffCsrIdWriteCallbackMideleg (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x303#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_execute_csrw_mideleg` (deviation 1). -/
theorem execEffExecuteCsrwMideleg (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x303#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .mideleg (WeakLeafCsrw2.midelegLegalized (s.regs .mideleg) (s.gpr rs1)), []) := by
  intro _ hpriv hS
  show execEff (execute_CSRReg 0x303#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x303#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwS _ s hS
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (by csr_dispatch_eq)) (by decide)
      (is_CSR_accessible_mideleg _ _) (WeakLeafCsrw2.execEffOfEqPure _ _ s (stateen_mideleg _ _)))
    (by decide) (by decide) (by decide)
    (execEffWriteCSRMideleg _ s hS) (execEffCsrIdWriteCallbackMideleg _ _)

section leafMideleg
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrw_mideleg_leaf` (deviation 6). -/
theorem wwpCsrwMidelegLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (c : MConf) (rs1v npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt)
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
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x303#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x303#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with mideleg := WeakLeafCsrw2.midelegLegalized c.mideleg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hal2 hal4 hrs1 hdecf hagree hDmi hgood hdec
  obtain ⟨hmie, hmprv⟩ := WeakLeafCsrw2.mokBits c hmok
  iintro Hm Hclk Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  icases mConf_cases cpu (DFrac.own 1) c $$ Hm with
    ⟨Hpriv, Hhs, Hms, Hmie, Hmid, Hmed, Hmepc, Hsatp, Hmenv, Hmcnt, Hmtc, Hstc, Hpmpc, Hpmpa, #Hhw⟩
  iapply WeakLeafCsrw2.wwpCsrwLeaf al4 gen cpu pc w rs1 0x303#12 .mideleg c.mideleg
    (WeakLeafCsrw2.midelegLegalized c.mideleg rs1v) c.mstatus rs1v npc0 c.pmpcfg D dst ws
    (by decide) (by decide) (by decide)
    (fun s h1 h2 h3 h4 => by
      have h := execEffExecuteCsrwMideleg rs1 s hrs1 h1 (by rw [h2]; decide)
      rw [h3, h4] at h
      exact h)
    hgen hpmp hal2 hal4 hrs1 hmie hmprv hdecf hagree hDmi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpmpc Hpc Hnpc Hrs1c Hmid Hbs Hhws
  iintro %ws' %hle Hhs Hpriv Hms Hpmpc Hclk Hpcs Hrs1c Hmid Hhws
  iapply Hcont $$ %ws' %hle
    [Hpriv Hhs Hms Hmie Hmid Hmed Hmepc Hsatp Hmenv Hmcnt Hmtc Hstc Hpmpc Hpmpa] Hclk Hpcs Hrs1c Hhws
  iapply confCells_intro
  simp only []
  iframe
  iexact Hhw

end leafMideleg

/-! ## 3. mepc (0x341; pure check, `set_xepc` → `mepcVal`) -/

/-- Rocq `exec_eff_hartSupports_Zca` (deviation 2; duplicated name). -/
theorem WeakLeafCsrw2.execEffHartSupportsZca : hartSupports .Ext_Zca = true := by decide +kernel

/-- Rocq `WpGprCsrwA.mepc_val` (deviation 4). -/
def WeakLeafCsrw2.mepcVal (v : BitVec 64) : BitVec 64 := BitVec.update v 0 0#1

/-- Rocq `exec_eff_legalize_xepc` (deviation 3: Lean's `legalize_xepc` is pure). -/
theorem execEffLegalizeXepc (v : BitVec 64) : legalize_xepc v = WeakLeafCsrw2.mepcVal v := by
  unfold legalize_xepc WeakLeafCsrw2.mepcVal
  rw [WeakLeafCsrw2.execEffHartSupportsZca]
  rfl

/-- Rocq `exec_eff_write_CSR_mepc`. -/
theorem execEffWriteCSRMepc (v : BitVec 64) (s : ExecSt) :
    execEff (write_CSR 0x341#12 v) s =
      some (.Ok (WeakLeafCsrw2.mepcVal v), s.setReg .mepc (WeakLeafCsrw2.mepcVal v), []) := by
  rw [write_CSR_mepc, ← execEffLegalizeXepc]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_mepc`. -/
theorem execEffCsrIdWriteCallbackMepc (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x341#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_execute_csrw_mepc` (deviation 1). -/
theorem execEffExecuteCsrwMepc (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    execEff (execute (.CSRReg (0x341#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS, s.setReg .mepc (WeakLeafCsrw2.mepcVal (s.gpr rs1)), []) := by
  intro _ hpriv
  show execEff (execute_CSRReg 0x341#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x341#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwPure _ s
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (by csr_dispatch_eq)) (by decide)
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (is_CSR_accessible_mepc _ _))
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (stateen_mepc _ _)))
    (by decide) (by decide) (by decide)
    (execEffWriteCSRMepc _ s) (execEffCsrIdWriteCallbackMepc _ _)

section leafMepc
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrw_mepc_leaf` (deviation 6). -/
theorem wwpCsrwMepcLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (c : MConf) (rs1v npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt)
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
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x341#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x341#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with mepc := WeakLeafCsrw2.mepcVal rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hal2 hal4 hrs1 hdecf hagree hDmi hgood hdec
  obtain ⟨hmie, hmprv⟩ := WeakLeafCsrw2.mokBits c hmok
  iintro Hm Hclk Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  icases mConf_cases cpu (DFrac.own 1) c $$ Hm with
    ⟨Hpriv, Hhs, Hms, Hmie, Hmid, Hmed, Hmepc, Hsatp, Hmenv, Hmcnt, Hmtc, Hstc, Hpmpc, Hpmpa, #Hhw⟩
  iapply WeakLeafCsrw2.wwpCsrwLeaf al4 gen cpu pc w rs1 0x341#12 .mepc c.mepc
    (WeakLeafCsrw2.mepcVal rs1v) c.mstatus rs1v npc0 c.pmpcfg D dst ws (by decide) (by decide)
    (by decide)
    (fun s h1 _ _ h4 => by
      have h := execEffExecuteCsrwMepc rs1 s hrs1 h1
      rw [h4] at h
      exact h)
    hgen hpmp hal2 hal4 hrs1 hmie hmprv hdecf hagree hDmi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpmpc Hpc Hnpc Hrs1c Hmepc Hbs Hhws
  iintro %ws' %hle Hhs Hpriv Hms Hpmpc Hclk Hpcs Hrs1c Hmepc Hhws
  iapply Hcont $$ %ws' %hle
    [Hpriv Hhs Hms Hmie Hmid Hmed Hmepc Hsatp Hmenv Hmcnt Hmtc Hstc Hpmpc Hpmpa] Hclk Hpcs Hrs1c Hhws
  iapply confCells_intro
  simp only []
  iframe
  iexact Hhw

end leafMepc

/-! ## 4. mcounteren (0x306; Ext_U-gated, pure legalize)

The CELL is 32 bits while the `write_CSR` result the callback sees is its
64-bit zero extension. -/

/-- Rocq `exec_eff_write_CSR_mcounteren`. -/
theorem execEffWriteCSRMcounteren (v : BitVec 64) (s : ExecSt) :
    execEff (write_CSR 0x306#12 v) s =
      some (.Ok (zero_extend (m := 64) (legalize_mcounteren (s.regs .mcounteren) v)),
        s.setReg .mcounteren (legalize_mcounteren (s.regs .mcounteren) v), []) := by
  rw [write_CSR_mcounteren]
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .mcounteren s),
    execEffBind0Nil _ _ _ _ _ (execEffWriteReg .mcounteren _ s),
    execEffBindNil _ _ _ _ _ (execEffReadReg .mcounteren _)]
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_mcounteren`. -/
theorem execEffCsrIdWriteCallbackMcounteren (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x306#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_execute_csrw_mcounteren` (deviation 1). -/
theorem execEffExecuteCsrwMcounteren (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    execEff (check_CSR_result 0x306#12 .Machine .CSRWrite) s = some (.CSR_Check_OK (), s, []) →
    execEff (execute (.CSRReg (0x306#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .mcounteren (legalize_mcounteren (s.regs .mcounteren) (s.gpr rs1)), []) := by
  intro _ hpriv hchk
  show execEff (execute_CSRReg 0x306#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x306#12 rs1 s _ _ hpriv hchk
    (by decide) (by decide) (by decide)
    (execEffWriteCSRMcounteren _ s) (execEffCsrIdWriteCallbackMcounteren _ _)

/-- Rocq `exec_eff_execute_csrw_mcounteren_full`. -/
theorem execEffExecuteCsrwMcounterenFull (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x306#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .mcounteren (legalize_mcounteren (s.regs .mcounteren) (s.gpr rs1)), []) := by
  intro hrs1 hpriv hU
  exact execEffExecuteCsrwMcounteren rs1 s hrs1 hpriv
    (execEffCheckCSRResultCsrwU _ s hU
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (by csr_dispatch_eq)) (by decide)
      (is_CSR_accessible_mcounteren _ _)
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (stateen_mcounteren _ _)))

section leafMcounteren
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrw_mcounteren_leaf` (deviation 6). -/
theorem wwpCsrwMcounterenLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (c : MConf) (rs1v npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt)
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
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x306#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x306#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with mcounteren := legalize_mcounteren c.mcounteren rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hal2 hal4 hrs1 hdecf hagree hDmi hgood hdec
  obtain ⟨hmie, hmprv⟩ := WeakLeafCsrw2.mokBits c hmok
  iintro Hm Hclk Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  icases mConf_cases cpu (DFrac.own 1) c $$ Hm with
    ⟨Hpriv, Hhs, Hms, Hmie, Hmid, Hmed, Hmepc, Hsatp, Hmenv, Hmcnt, Hmtc, Hstc, Hpmpc, Hpmpa, #Hhw⟩
  iapply WeakLeafCsrw2.wwpCsrwLeaf al4 gen cpu pc w rs1 0x306#12 .mcounteren c.mcounteren
    (legalize_mcounteren c.mcounteren rs1v) c.mstatus rs1v npc0 c.pmpcfg D dst ws (by decide)
    (by decide) (by decide)
    (fun s h1 h2 h3 h4 => by
      have h := execEffExecuteCsrwMcounterenFull rs1 s hrs1 h1 (by rw [h2]; decide)
      rw [h3, h4] at h
      exact h)
    hgen hpmp hal2 hal4 hrs1 hmie hmprv hdecf hagree hDmi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpmpc Hpc Hnpc Hrs1c Hmcnt Hbs Hhws
  iintro %ws' %hle Hhs Hpriv Hms Hpmpc Hclk Hpcs Hrs1c Hmcnt Hhws
  iapply Hcont $$ %ws' %hle
    [Hpriv Hhs Hms Hmie Hmid Hmed Hmepc Hsatp Hmenv Hmcnt Hmtc Hstc Hpmpc Hpmpa] Hclk Hpcs Hrs1c Hhws
  iapply confCells_intro
  simp only []
  iframe
  iexact Hhw

end leafMcounteren

/-! ## 5. menvcfg (0x30A; Ext_U-and-gated check, MONADIC legalize) -/

/-- Rocq `exec_eff_hartSupports_Zicfiss` (deviation 2). -/
theorem execEffHartSupportsZicfiss : hartSupports .Ext_Zicfiss = false := by decide +kernel  -- no Zicfiss since 2026-11-04
/-- Rocq `exec_eff_hartSupports_Zicboz` (deviation 2). -/
theorem execEffHartSupportsZicboz : hartSupports .Ext_Zicboz = true := by decide +kernel
/-- Rocq `exec_eff_hartSupports_Zicbom` (deviation 2). -/
theorem execEffHartSupportsZicbom : hartSupports .Ext_Zicbom = true := by decide +kernel
/-- Rocq `exec_eff_hartSupports_Sstc` (deviation 2; duplicated name). -/
theorem WeakLeafCsrw2.execEffHartSupportsSstc : hartSupports .Ext_Sstc = true := by decide +kernel
/-- Rocq `exec_eff_hartSupports_Smnpm` (deviation 2). -/
theorem execEffHartSupportsSmnpm : hartSupports .Ext_Smnpm = true := by decide +kernel
/-- Rocq `exec_eff_hartSupports_Svadu` (deviation 2). -/
theorem execEffHartSupportsSvadu : hartSupports .Ext_Svadu = true := by decide +kernel
/-- Rocq `exec_eff_hartSupports_Svpbmt` (deviation 2). -/
theorem execEffHartSupportsSvpbmt : hartSupports .Ext_Svpbmt = true := by decide +kernel

/-- Rocq `exec_eff_currentlyEnabled_Zicboz`. -/
theorem execEffCurrentlyEnabledZicboz (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Zicboz) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsZicboz, execEffReturnm]

/-- Rocq `exec_eff_currentlyEnabled_Zicbom`. -/
theorem execEffCurrentlyEnabledZicbom (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Zicbom) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsZicbom, execEffReturnm]

/-- Rocq `exec_eff_currentlyEnabled_Sstc` (duplicated name). -/
theorem WeakLeafCsrw2.execEffCurrentlyEnabledSstc (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Sstc) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [WeakLeafCsrw2.execEffHartSupportsSstc, execEffReturnm]

/-- Rocq `exec_eff_currentlyEnabled_Smnpm`. -/
theorem execEffCurrentlyEnabledSmnpm (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Smnpm) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSmnpm, execEffReturnm]

/-- Rocq `exec_eff_currentlyEnabled_Svadu` (duplicated name). -/
theorem WeakLeafCsrw2.execEffCurrentlyEnabledSvadu (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Svadu) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSvadu, execEffReturnm]

/-- Rocq's Ltac `crush_inner_cE_S_eff` (deviation 2): an inner
`currentlyEnabled Ext_S` reduced to the misa.S bit. -/
macro "crush_inner_cE_S_eff" : tactic =>
  `(tactic| simp only [WeakLeafEffCommon.execEffCurrentlyEnabledS])

/-- Rocq `exec_eff_currentlyEnabled_Svpbmt`. -/
theorem execEffCurrentlyEnabledSvpbmt (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_Svpbmt) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSvpbmt, ↓reduceIte]
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSv39, ↓reduceIte]
  crush_inner_cE_S_eff
  rw [hS]

/-- Rocq `WpGprCsrwA.menvcfg_cbie` (deviation 4). -/
def WeakLeafCsrw2.menvcfgCbie (v : BitVec 64) : BitVec 2 :=
  if _get_MEnvcfg_CBIE (Mk_MEnvcfg v) != 0b10#2 then _get_MEnvcfg_CBIE (Mk_MEnvcfg v) else 0b00#2

/-- Rocq `WpGprCsrwA.menvcfg_legalized` (deviation 4). -/
def WeakLeafCsrw2.menvcfgLegalized (o v : BitVec 64) : BitVec 64 :=
  let v' := Mk_MEnvcfg v
  _update_MEnvcfg_PBMTE
    (_update_MEnvcfg_ADUE
      (_update_MEnvcfg_PMM
        (_update_MEnvcfg_STCE
          (_update_MEnvcfg_CBIE
            (_update_MEnvcfg_CBCFE
              (_update_MEnvcfg_CBZE
                (_update_MEnvcfg_SSE
                  (_update_MEnvcfg_LPE
                    (_update_MEnvcfg_FIOM o
                      (if sys_enable_writable_fiom then _get_MEnvcfg_FIOM v' else 0#1))
                    0#1)  -- LPE/SSE: 0 (no Zicfilp/Zicfiss, 2026-11-04)
                  0#1)
                (_get_MEnvcfg_CBZE v'))
              (_get_MEnvcfg_CBCFE v'))
            (WeakLeafCsrw2.menvcfgCbie v))
          (_get_MEnvcfg_STCE v'))
        (if (true && is_supported_pmm .PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM v')))
         then _get_MEnvcfg_PMM v' else _get_MEnvcfg_PMM o))
      (_get_MEnvcfg_ADUE v'))
    (_get_MEnvcfg_PBMTE v')

/-- Rocq `exec_eff_legalize_xenvcfg_cbie`. -/
theorem execEffLegalizeXenvcfgCbie (cbie : BitVec 2) (s : ExecSt) :
    execEff (legalize_xenvcfg_cbie cbie) s =
      some (if cbie != 0b10#2 then cbie else 0b00#2, s, []) := by
  unfold legalize_xenvcfg_cbie
  cases (cbie != 0b10#2) <;> simp only [↓reduceIte, Bool.false_eq_true] <;> rfl

/-- Rocq `exec_eff_legalize_menvcfg`. -/
theorem execEffLegalizeMenvcfg (o v : BitVec 64) (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (legalize_menvcfg o v) s = some (WeakLeafCsrw2.menvcfgLegalized o v, s, []) := by
  unfold legalize_menvcfg WeakLeafCsrw2.menvcfgLegalized WeakLeafCsrw2.menvcfgCbie
  cases hp : is_supported_pmm .PM_SMNPM (pmm_mode_backwards (_get_MEnvcfg_PMM (Mk_MEnvcfg v))) <;>
  exec_eff_steps [execEffHartSupportsZicfilp, execEffHartSupportsZicfiss,
    execEffCurrentlyEnabledZicboz, execEffCurrentlyEnabledZicbom, execEffLegalizeXenvcfgCbie,
    WeakLeafCsrw2.execEffCurrentlyEnabledSstc, execEffCurrentlyEnabledSmnpm,
    WeakLeafCsrw2.execEffCurrentlyEnabledSvadu, execEffCurrentlyEnabledSvpbmt s hS, hp, Bool.true_and]
  all_goals rfl

/-- Rocq `exec_eff_write_CSR_menvcfg`. -/
theorem execEffWriteCSRMenvcfg (v : BitVec 64) (s : ExecSt)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (write_CSR 0x30A#12 v) s =
      some (.Ok (WeakLeafCsrw2.menvcfgLegalized (s.regs .menvcfg) v),
        s.setReg .menvcfg (WeakLeafCsrw2.menvcfgLegalized (s.regs .menvcfg) v), []) := by
  rw [write_CSR_menvcfg]
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .menvcfg s),
    execEffBindNil _ _ _ _ _ (execEffLegalizeMenvcfg (s.regs .menvcfg) v s hS),
    execEffBind0Nil _ _ _ _ _ (execEffWriteReg .menvcfg _ s),
    execEffBindNil _ _ _ _ _ (execEffReadReg .menvcfg _)]
  simp only [ExecSt.setReg_regs, RegFile.set_same]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_menvcfg`. -/
theorem execEffCsrIdWriteCallbackMenvcfg (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x30A#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_execute_csrw_menvcfg` (deviation 1). -/
theorem execEffExecuteCsrwMenvcfg (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    (_get_Misa_U (s.regs .misa) == 1#1) = true →
    execEff (execute (.CSRReg (0x30A#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS,
        s.setReg .menvcfg (WeakLeafCsrw2.menvcfgLegalized (s.regs .menvcfg) (s.gpr rs1)), []) := by
  intro _ hpriv hS hU
  show execEff (execute_CSRReg 0x30A#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x30A#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwUAnd _ xenvcfg_csrs_are_defined s hU
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (by csr_dispatch_eq)) (by decide)
      (is_CSR_accessible_menvcfg _ _) (by first | rfl | decide)
      (WeakLeafCsrw2.execEffOfEqPure _ _ s (stateen_menvcfg _ _)))
    (by decide) (by decide) (by decide)
    (execEffWriteCSRMenvcfg _ s hS) (execEffCsrIdWriteCallbackMenvcfg _ _)

section leafMenvcfg
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrw_menvcfg_leaf` (deviation 6). -/
theorem wwpCsrwMenvcfgLeaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (c : MConf) (rs1v npc0 : BitVec 64) (D : Register → Bool) (dst : ExecSt)
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
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x30A#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x30A#12, .Regidx rs1, zreg, .CSRRW), dst) →
    mConf (GF := GF) cpu (DFrac.own 1) c ⊢
      clockCells cpu -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        mConf cpu (DFrac.own 1) { c with menvcfg := WeakLeafCsrw2.menvcfgLegalized c.menvcfg rs1v } -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hmok hpmp hal2 hal4 hrs1 hdecf hagree hDmi hgood hdec
  obtain ⟨hmie, hmprv⟩ := WeakLeafCsrw2.mokBits c hmok
  iintro Hm Hclk Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  icases mConf_cases cpu (DFrac.own 1) c $$ Hm with
    ⟨Hpriv, Hhs, Hms, Hmie, Hmid, Hmed, Hmepc, Hsatp, Hmenv, Hmcnt, Hmtc, Hstc, Hpmpc, Hpmpa, #Hhw⟩
  iapply WeakLeafCsrw2.wwpCsrwLeaf al4 gen cpu pc w rs1 0x30A#12 .menvcfg c.menvcfg
    (WeakLeafCsrw2.menvcfgLegalized c.menvcfg rs1v) c.mstatus rs1v npc0 c.pmpcfg D dst ws
    (by decide) (by decide) (by decide)
    (fun s h1 h2 h3 h4 => by
      have h := execEffExecuteCsrwMenvcfg rs1 s hrs1 h1 (by rw [h2]; decide) (by rw [h2]; decide)
      rw [h3, h4] at h
      exact h)
    hgen hpmp hal2 hal4 hrs1 hmie hmprv hdecf hagree hDmi hgood hdec
    $$ Hhw Hclk Hhs Hpriv Hms Hpmpc Hpc Hnpc Hrs1c Hmenv Hbs Hhws
  iintro %ws' %hle Hhs Hpriv Hms Hpmpc Hclk Hpcs Hrs1c Hmenv Hhws
  iapply Hcont $$ %ws' %hle
    [Hpriv Hhs Hms Hmie Hmid Hmed Hmepc Hsatp Hmenv Hmcnt Hmtc Hstc Hpmpc Hpmpa] Hclk Hpcs Hrs1c Hhws
  iapply confCells_intro
  simp only []
  iframe
  iexact Hhw

end leafMenvcfg

end Weak
