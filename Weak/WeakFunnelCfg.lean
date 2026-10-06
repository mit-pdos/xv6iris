/-
Weak: **the weak funnel for CONFIG-WRITING instructions** -- the config-side
companion of `Weak/WeakFunnel.lean`.

Rocq: `iris/WeakFunnelCfg.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakFunnel.wwpInstr` holds the M-mode config
cells inside the config bundle across the step and hands the SAME bundle back
-- right for every instruction that only READS the config, wrong for the three
that WRITE it (csrw mstatus / csrw pmpcfg0 / MRET): their `execute` must
`reg_update` the very cells the funnel holds.  This file is the weak twin of
SC `InstrBytes.wp_instr_config`; the interface delta from `wwpInstr` mirrors
the SC delta: the funnel takes the UNBUNDLED config cells (`cur_privilege`,
`mstatus ↦ᵣ ms0`, `pmpcfg_n ↦ᵣ pmpcfg0`, `hart_state`) at FULL ownership with
`ms0` explicit; only the MIE and MPRV facts on `ms0` are premises (MIE runs
`dispatchInterrupt`, MPRV is carried by `wcfgRegs`); the engine reads the
three cells and passes them INTO the callback, so the leaf can `reg_update`
them when exhibiting `sExec`; the callback also receives the whole-value pin
`⌜σ.wmRegs .mstatus = ms0⌝`; the continuation gets back only the raw
`hart_state` cell (plus the stepped PC).  Everything else -- the certificate
(`wstepCert`), the fetch obligations, the device seam `⌜t.dev = sExec.dev⌝`,
`wstepPost`, the `wmstateNorg` hand-off -- is `wwpInstr`'s, and the proof is
that proof with the cell plumbing swapped.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WeakFunnel.lean` deviation 1 (`mstate` ↦ `ExecSt`,
   `register_lookup r s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦
   `(x == 1#1) = b`, `cpu_id` ↦ the explicit `cpu`, ...).
2. THE CONFIG INTERFACE (owner decision Q3, option A; `WeakFunnel` header
   deviation 7, followed exactly).  `MinstretInv` is NOT ported: Rocq's
   `minstret_inv` (persistent invariants over the five clock cells) is the
   OWNED `clockCells cpu`, so every mask `⊤ ∖ ↑minstretN` is `⊤`
   (`wwpCbConfig` is `={⊤,∅}=∗`, its continuation `|={∅,⊤}=>`).  Because
   the cells are owned, not invariant-held: (a) like `wwpCb`, the callback is
   also `∀ mt ip`, takes `mtime ↦ᵣ mt ∗ mip ↦ᵣ ip` and returns `∃ mt' ip'` of
   them next to `regInterp cpu sExec.regs`; (b) its continuation receives
   `clockCells cpu` (between Rocq's `hart_state ↦ᵣ` and `PC ↦ᵣ`); (c) the
   post-write registers are `((wflatSt σ).setReg .minstret_increment b).regs`.
   Rocq `hw_config` ↦ `MachCSL.hwConfig cpu` (persistent; misa = `misaC`,
   mseccfg = 0, `pma_regions = bootPMA` -- `WeakFunnel` deviation 2 --,
   htif none, elp = 0); its pure facts (misa.S/C/A, PMM disabled, elp not
   LP_EXPECTED) are derived from those values instead of being stored.
   Rocq's `cur_privilege ↦ᵣ Machine` / `mstatus ↦ᵣ ms0` / `pmpcfg_n ↦ᵣ
   pmpcfg0` / `hart_state ↦ᵣ` are full-ownership `↦ᵣ[cpu]` cells.  A leaf
   rebuilds `mConf cpu (DfracOwn 1) c'` (Rocq `mmode_config_rebuild`) with
   `MachCSL.mConf_introW` from its written cells, the raw `hart_state` and the
   other `mConf` cells it kept (Rocq `mmode_config_unbundle` ↦
   `MachCSL.mConf_cases`).
3. STATEMENT SHAPES (WeakInstr deviation 3): `hwConfig cpu ⊢ clockCells cpu
   -∗ …` for Rocq `hw_config -∗ minstret_inv -∗ …`; pure premises are Lean
   premises.
4. Lean-only (2, file-qualified): `WeakFunnelCfg.hwRegFacts` (the
   `reg_valid_dq` block on `hwConfig`), `WeakFunnelCfg.wcfgRegsOfCells` (the
   `wcfg_regs` assembly).  The exec chain is `WeakFunnel.wwpStepExec`, the
   register writes `WeakFunnel.wwpRetireRegs`/`wwpTickRegs` (reused).
   (2 Rocq + 2 Lean-only = 4.)

**Rocq → Lean name map.**  `wwp_cb_config` `wwpCbConfig`, `wwp_instr_config`
`wwpInstrConfig` (neither in the duplicated-name table).

**Dropped:** nothing.
-/
import Weak.WeakFunnel

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- The `wcfg_regs` record from the raw cell reads and `ms0`'s two bits
(Lean-only). -/
theorem WeakFunnelCfg.wcfgRegsOfCells (σ : Wmstate) (pmpcfg0 : RegisterType .pmpcfg_n)
    (ms0 : BitVec 64)
    (hmie : (_get_Mstatus_MIE ms0 == 1#1) = false)
    (hmprv : (_get_Mstatus_MPRV ms0 == 1#1) = false)
    (Epriv : σ.wmRegs .cur_privilege = .Machine) (Ehs : σ.wmRegs .hart_state = .HART_ACTIVE ())
    (Ems : σ.wmRegs .mstatus = ms0) (Epmp : σ.wmRegs .pmpcfg_n = pmpcfg0)
    (Emisa : σ.wmRegs .misa = misaC) (Esec : σ.wmRegs .mseccfg = 0#64)
    (Epma : σ.wmRegs .pma_regions = bootPMA) (Ehtif : σ.wmRegs .htif_tohost_base = none)
    (Eelp : σ.wmRegs .elp = 0#1) :
    wcfgRegs σ pmpcfg0 := by
  refine ⟨Epriv, Ehs, Emisa, Esec, Epmp, Epma, Ehtif, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Emisa]; decide
  · rw [Ems]; exact hmie
  · rw [Ems]; exact hmprv
  · rw [Esec]; rfl
  · rw [Eelp]; decide

section funnelcfg
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The register reads of `hwConfig` (Lean-only; Rocq's `reg_valid_dq` block). -/
theorem WeakFunnelCfg.hwRegFacts (cpu : CPU) (f : RegFile) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢ hwConfig cpu -∗
      ⌜f .misa = misaC ∧ f .mseccfg = 0#64 ∧ f .pma_regions = bootPMA ∧
        f .htif_tohost_base = none ∧ f .elp = 0#1⌝ := by
  iintro Hr #Hhw
  ihave #Hmisa := hwConfig_reg cpu .misa misaC rfl $$ Hhw
  ihave #Hsec := hwConfig_reg cpu .mseccfg (0#64) rfl $$ Hhw
  ihave #Hpma := hwConfig_reg cpu .pma_regions bootPMA rfl $$ Hhw
  ihave #Hhtif := hwConfig_reg cpu .htif_tohost_base none rfl $$ Hhw
  ihave #Help := hwConfig_reg cpu .elp (0#1) rfl $$ Hhw
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr Hmisa with ⟨%E5, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr Hsec with ⟨%E6, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr Hpma with ⟨%E7, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr Hhtif with ⟨%E8, Hr, -⟩
  ihave %E9 := wand_intro (reg_valid cpu f _ _ _) $$ Hr Help
  ipureintro
  exact ⟨E5, E6, E7, E8, E9⟩

/-- THE LEAF'S OBLIGATION (Rocq `wwp_cb_config`): `wwpCb` with the config
variant delta -- the three written cells arrive at full ownership INSIDE the
callback with the mstatus whole-value pin, and the continuation gets back the
raw `hart_state` cell, `clockCells` and the stepped PC. -/
def wwpCbConfig (gen : Nat) (cpu : CPU) (pc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (pmpcfg0 : RegisterType .pmpcfg_n) (ms0 : BitVec 64)
    (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) : IProp GF :=
  iprop(∀ (σ : Wmstate) (b : Bool) (mt ip : BitVec 64),
    ⌜σ.wmRegs .PC = pc⌝ -∗
    ⌜wcfgRegs σ pmpcfg0⌝ -∗
    ⌜σ.wmRegs .mstatus = ms0⌝ -∗
    Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
    Register.mstatus ↦ᵣ[cpu] ms0 -∗
    Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
    wlatInterp σ.wmImg σ.wmLog -∗
    regInterp cpu ((wflatSt σ).setReg .minstret_increment b).regs -∗
    wmstateNorg (hlc := hlc) (GF := GF) cpu σ -∗
    Register.mtime ↦ᵣ[cpu] mt -∗
    Register.mip ↦ᵣ[cpu] ip ={⊤, ∅}=∗
      ⌜P σ⌝ ∗
      ∃ sExec : ExecSt,
        ⌜exec (execute i)
            (((wflatSt σ).setReg .minstret_increment b).setReg .nextPC
              (Sail.BitVec.addInt pc (if is_rvc then 2 else 4))) =
          some (RETIRE_SUCCESS, sExec)⌝ ∗
        regInterp cpu sExec.regs ∗
        (∃ mt' ip' : BitVec 64, Register.mtime ↦ᵣ[cpu] mt' ∗ Register.mip ↦ᵣ[cpu] ip') ∗
        ▷ (∀ (tick : Bool) (σ' : Wmstate) (t : ExecSt),
            ⌜exec (riscvStep tick) (wflatSt σ) = some ((), t)⌝ -∗
            ⌜t.dev = sExec.dev⌝ -∗
            ⌜wstepPost σ σ' t⌝ -∗
            ⌜Q σ σ'⌝ -∗
            Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
            clockCells cpu -∗
            Register.PC ↦ᵣ[cpu] (sExec.regs .nextPC) -∗
            |={∅, ⊤}=> (wlatInterp σ'.wmImg σ'.wmLog ∗
              wmstateNorg (hlc := hlc) (GF := GF) cpu σ' ∗
              wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))))

theorem wwpInstrConfig (gen : Nat) (cpu : CPU) (pc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (pmpcfg0 : RegisterType .pmpcfg_n) (ms0 : BitVec 64)
    (P : Wmstate → Prop) (Q : Wmstate → Wmstate → Prop) :
    gen = 0 →
    accWf pc 4 →
    pmpAllowsAll pmpcfg0 →
    (_get_Mstatus_MIE ms0 == 1#1) = false →
    (_get_Mstatus_MPRV ms0 == 1#1) = false →
    wstepCert cpu.val pc P Q →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms0 -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      winstr pc is_rvc i -∗
      wwpCbConfig (hlc := hlc) gen cpu pc is_rvc i pmpcfg0 ms0 P Q -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hacc hpmp hmie hmprv hcert
  iintro #Hhw Hclk Hhs Hpriv Hms Hpmpc Hpc #Hinstr H
  unfold winstr wwpCbConfig
  icases Hinstr with ⟨%hnlpad, %r, %hrvc, #Hb, %hdec⟩
  icases clockCells_cases cpu $$ Hclk with ⟨%mi0, %mst0, %cy0, %ti0, %ip0, Hmi, Hmst, Hcy, Hti, Hip⟩
  iapply wpWinstr gen cpu pc P Q hgen hacc hcert
  iintro %σ Hσ
  icases (wmstateInterpSplitRegs cpu σ).mp $$ Hσ with ⟨Hreg, Hlat, Hnorg⟩
  icases keepPure1 (wmstateNorgFacts cpu σ) $$ Hnorg with ⟨%hfacts, Hnorg⟩
  obtain ⟨_, hwf⟩ := hfacts
  -- every register the wrapper / fetch / decode reads, at `σ.wmRegs`
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .PC _ pc)) $$ Hreg Hpc with ⟨%Lpc, Hreg, Hpc⟩
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .cur_privilege _ _)) $$ Hreg Hpriv
    with ⟨%Lpriv, Hreg, Hpriv⟩
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .hart_state _ _)) $$ Hreg Hhs
    with ⟨%Lhs, Hreg, Hhs⟩
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .mstatus _ _)) $$ Hreg Hms
    with ⟨%Lms, Hreg, Hms⟩
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .pmpcfg_n _ _)) $$ Hreg Hpmpc
    with ⟨%Lpmpc, Hreg, Hpmpc⟩
  icases keepPure (WeakFunnelCfg.hwRegFacts cpu σ.wmRegs) $$ Hreg Hhw with ⟨%hhw, Hreg, -⟩
  obtain ⟨Lmisa, Lsec, Lpma, Lhtif, Lelp⟩ := hhw
  -- the same reads, packaged for the leaf: the MIE/MPRV bits off `ms0`'s premises
  have hcfg : wcfgRegs σ pmpcfg0 := WeakFunnelCfg.wcfgRegsOfCells σ pmpcfg0 ms0 hmie hmprv
    Lpriv Lhs Lms Lpmpc Lmisa Lsec Lpma Lhtif Lelp
  -- the two facts the weak fetch needs, off the text elements
  icases keepPure (winstrFlat σ pc r hwf) $$ Hlat Hb with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc r hwf) $$ Hlat Hb with ⟨%htext, Hlat, -⟩
  -- the funnel's own choice of the increment flag
  obtain ⟨b, hsi⟩ := execShouldIncMinstretSome (σ.wmRegs .cur_privilege) (wflatSt σ)
  imod (wand_intro (reg_update cpu σ.wmRegs .minstret_increment mi0 b)) $$ Hreg Hmi with ⟨Hreg, Hmi⟩
  rw [show σ.wmRegs.set .minstret_increment b = ((wflatSt σ).setReg .minstret_increment b).regs from rfl]
  -- the leaf's obligation: the written cells go IN
  imod H $$ %σ %b %ti0 %ip0 %Lpc %hcfg %Lms Hpriv Hms Hpmpc Hlat Hreg Hnorg Hti Hip
    with ⟨%hP, %sExec, %hexec, Hreg, ⟨%mt1, %ip1, Hti, Hip⟩, Hk⟩
  icases keepPure (wand_intro (reg_valid cpu sExec.regs .hart_state _ _)) $$ Hreg Hhs
    with ⟨%LhsE, Hreg, Hhs⟩
  icases keepPure (wand_intro (reg_valid cpu sExec.regs .minstret_increment _ b)) $$ Hreg Hmi
    with ⟨%Lmi, Hreg, Hmi⟩
  obtain ⟨hst0, cc, tt, pp, hst1⟩ := wwpStepExec σ pc is_rvc i pmpcfg0 r b sExec hcfg hpmp Lpc hfok
    hrvc hnlpad hdec hsi hexec LhsE Lmi
  have hdev0 : (hartActiveSFinal sExec b).dev = sExec.dev := hartActiveSFinalDev sExec b
  have hdev1 : ((((hartActiveSFinal sExec b).setReg .mcycle cc).setReg .mtime tt).setReg .mip pp).dev =
      sExec.dev := hdev0
  -- the wrapper's own register writes: tick PC, maybe bump minstret
  imod wwpRetireRegs cpu sExec b pc mst0 $$ Hreg Hpc Hmst with ⟨Hreg, Hpc, %mst1, Hmst⟩
  -- hand the two successors to `wpWinstr`
  imodintro
  isplitr
  · ipureintro; exact Lpc
  isplitr
  · ipureintro; exact htext
  isplitr
  · ipureintro; exact hP
  iexists (hartActiveSFinal sExec b),
    ((((hartActiveSFinal sExec b).setReg .mcycle cc).setReg .mtime tt).setReg .mip pp)
  isplitr
  · ipureintro; exact hst0
  isplitr
  · ipureintro; exact hst1
  inext
  iintro %tick %σ' %hpost %hQ
  cases tick
  · -- NO TICK: the registers are already those of `t0`
    simp only [Bool.false_eq_true, ↓reduceIte] at hpost
    have hregs' : σ'.wmRegs = (hartActiveSFinal sExec b).regs := hpost.1
    ihave Hclk := clockCells_introW cpu b mst1 cy0 mt1 ip1 $$ Hmi Hmst Hcy Hti Hip
    imod Hk $$ %false %σ' %(hartActiveSFinal sExec b) %hst0 %hdev0 %hpost %hQ Hhs Hclk Hpc
      with ⟨Hlat', Hnorg', Hwp⟩
    imodintro
    isplitl [Hreg Hlat' Hnorg']
    · iapply (wmstateInterpSplitRegs cpu σ').mpr
      rw [hregs']
      iframe Hreg Hlat' Hnorg'
    · iexact Hwp
  · -- TICK: `tick_clock` wrote mcycle / mtime / mip
    simp only [↓reduceIte] at hpost
    have hregs' : σ'.wmRegs =
        ((((hartActiveSFinal sExec b).setReg .mcycle cc).setReg .mtime tt).setReg .mip pp).regs := hpost.1
    imod wwpTickRegs cpu (hartActiveSFinal sExec b) cc tt pp cy0 mt1 ip1 $$ Hreg Hcy Hti Hip
      with ⟨Hreg, Hcy, Hti, Hip⟩
    ihave Hclk := clockCells_introW cpu b mst1 cc tt pp $$ Hmi Hmst Hcy Hti Hip
    imod Hk $$ %true %σ' %((((hartActiveSFinal sExec b).setReg .mcycle cc).setReg .mtime tt).setReg .mip pp)
      %hst1 %hdev1 %hpost %hQ Hhs Hclk Hpc with ⟨Hlat', Hnorg', Hwp⟩
    imodintro
    isplitl [Hreg Hlat' Hnorg']
    · iapply (wmstateInterpSplitRegs cpu σ').mpr
      rw [hregs']
      iframe Hreg Hlat' Hnorg'
    · iexact Hwp

end funnelcfg

end Weak
