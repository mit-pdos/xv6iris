/-
Weak: **constraint B, §5 of `AxIntr`: the SIE-agnostic SPINE `SpineOkI`, the spine mirrors with
the interrupt arm, and the whole-instruction certificates whose post is "Good ∨ TrapPost".**
PURE (no Iris).

Rocq: `iris/AxIntr3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`SpineOkI img ctrlOk textAt`: `AxSpineOk5.SpineOkT`'s fields with (a) the dispatch field SPLIT
(`spiDisp`: `dispPost` — `none`, or `some (ip, Supervisor)` with SIE = 1); (b) the TRAP fields
`spiTrap` (the handler tree, at SIE = 1, is certified with post `trapSt`) and `spiTrapOk` (the
trap state is in the regime); (c) the tick field in the `tickFrame` form.  `spineOkIS`: ALL
fields at the SIE-agnostic S-mode regime `ctrlOkSI` (premises: only the three static satp facts,
as `spineOkTS`).  `EvAHartActiveRvcI` / `EvATryStepI`: the SC spine mirrors with the
`Step_Pending_Interrupt` arm (`run_hart_active` early-returns BEFORE the fetch — no text read, no
memory event; `try_step` runs `handle_interrupt`, `tick_pc`, no retire, no minstret bump).
`TrapPost ctrlOk rs rs'`: the trap-entry state relative to the boundary registers `rs`: SIE was 1
at rs; rs' in the regime; PC = stvecBase(stvec); sepc = pc; mstatus = trapMs elp ms; scause =
interrupt cause; stval = 0; priv = S; every GPR unchanged.  `spineCertI` (GPR write, the
`spineCertT` twin) and `spineCertCI` (compressed control transfer, the `AxSymCtl2.spineCertC`
twin): post `Good ∨ TrapPost` / `GoodC ∨ TrapPost`, both ticks, every pin answer.
`trapPostOff`: at SIE = 0 the trap disjunct is empty.

## Deviations from Rocq

1. All of `AxIntr`/`AxIntr2`/`AxSpineOk5`/`AxSymCtl2`'s spelling deviations (`mstate` ↦
   `ExecSt`, `register_lookup r rs` ↦ `rs r`, `set_reg` ↦ `ExecSt.setReg`, `seip_reg` ↦
   `AxRunClose.pinReg`, `zeros' 64` ↦ `zeros (n := 64)`, `WpIntrCore.stvec_base` ↦
   `stvecBase`, `trap_ms` ↦ `AxIntr2.trapMs`, `add_vec_int` ↦ `BitVec.addInt`,
   `R_bitvector_64 (gpr_of_Z (uint rd))` writes ↦ `ExecSt.setGpr rd`).
2. `TrapPost`'s GPR clause `∀ z, register_lookup (R_bitvector_64 (gpr_of_Z z)) rs' = … rs` ↦
   `∀ z : BitVec 5, uxaXget rs' z = uxaXget rs z` (the tree's GPR reading, as `keepRegs`).
3. `spineCertCI` takes `textOkCtl img ctrlOk textAt no4 …` (Lean `textOkCtl` carries the 4-byte
   predicate explicitly, as Rocq) — same statement.
4. TACTICS: the Ltacs `nseip`, `rne`, `ev_step`, `ev_go`, `ev_use`, `lk`, `tp` are not
   redeclared (`ax_sym2_ev_go`, `AxSymEngine2.evFactUse`/`evFactQ`/`EvAFactLift`, `simp` over
   `RegFile.set_*`, `AxIntr2.trapSt*`).  Section `img` and the `EvM` notation are unfolded
   (`img` is an explicit argument).
5. `spineOkIS`'s satp premises take `AxIntr.sptFetchSI`'s shapes (`8#4`, `zero_extend (m := 16)
   (satp_to_asid satp0) = 0#16`, `BitVec.setWidth 44 (satp_to_ppn satp0) = T.base`).

**Rocq → Lean name map.**  `TrapPost` `TrapPost`, `TrapPost_off` `trapPostOff`,
`TrapPost_tick` `trapPostTick`, `SpineOkI` `SpineOkI` (fields `spi_seip` `spiSeip`, `spi_hart`
`spiHart`, `spi_frame` `spiFrame`, `spi_inc` `spiInc`, `spi_disp` `spiDisp`, `spi_trap`
`spiTrap`, `spi_trap_ok` `spiTrapOk`, `spi_fetch` `spiFetch`, `spi_lpad` `spiLpad`, `spi_zca`
`spiZca`, `spi_tick` `spiTick`), `EvA_hart_active_rvc_I` `EvAHartActiveRvcI`, `EvA_try_step_I`
`EvATryStepI`, `SpineOkI_S` `spineOkIS`, `trap_post_of` `trapPostOf`, `intr_on_minc`
`intrOnMinc`, `spine_cert_I` `spineCertI`, `wr_npc_ctrl_I` `wrNpcCtrlI`, `spine_certC_I`
`spineCertCI`.  None is in the duplicated-name table.  Lean-only (file-qualified):
`AxIntr3.trapStXget` (GPR values survive `trapSt`).

**Dropped:** the Ltacs (deviation 4).  Rocq 12 definitions/lemmas + 7 Ltacs; Lean 12 + 1
Lean-only.  **Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxIntr2
import Weak.AxSymCtl2

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The trap-entry post -/

/-- Rocq `TrapPost` (deviation 2). -/
def TrapPost (ctrlOk : RegFile → Prop) (rs rs' : RegFile) : Prop :=
  intrOn rs ∧ ctrlOk rs' ∧ ∃ ip : InterruptType,
    rs' .PC = stvecBase (rs .stvec) ∧
    rs' .sepc = rs .PC ∧
    rs' .mstatus = AxIntr2.trapMs (rs .elp) (rs .mstatus) ∧
    rs' .scause = scauseIntr ip (rs .scause) ∧
    rs' .stval = zeros (n := 64) ∧
    rs' .cur_privilege = .Supervisor ∧
    ∀ z : BitVec 5, uxaXget rs' z = uxaXget rs z

/-- Rocq `TrapPost_off`. -/
theorem trapPostOff (ctrlOk : RegFile → Prop) (rs rs' : RegFile) :
    ¬ intrOn rs → ¬ TrapPost ctrlOk rs rs' :=
  fun Hoff H => Hoff H.1

/-- Rocq `TrapPost_tick`. -/
theorem trapPostTick (ctrlOk : RegFile → Prop) (rs : RegFile) (t' t'' : ExecSt) :
    TrapPost ctrlOk rs t'.regs → ctrlOk t''.regs → tickFrame t' t'' →
    TrapPost ctrlOk rs t''.regs := by
  rintro ⟨Hon, -, ip, H1, H2, H3, H4, H5, H6, H7⟩ Hc Hf
  refine ⟨Hon, Hc, ip, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Hf _ (by decide) (by decide) (by decide)]; exact H1
  · rw [Hf _ (by decide) (by decide) (by decide)]; exact H2
  · rw [Hf _ (by decide) (by decide) (by decide)]; exact H3
  · rw [Hf _ (by decide) (by decide) (by decide)]; exact H4
  · rw [Hf _ (by decide) (by decide) (by decide)]; exact H5
  · rw [Hf _ (by decide) (by decide) (by decide)]; exact H6
  · intro z; rw [(tickFrameKeep _ _ Hf).2 z]; exact H7 z

/-- (Lean-only) GPR values survive the trap. -/
theorem AxIntr3.trapStXget (s : ExecSt) (ip : InterruptType) (z : BitVec 5) :
    uxaXget (trapSt s ip).regs z = uxaXget s.regs z := by
  have hg : ∀ r ∈ uxaGprs, r ≠ .mstatus ∧ r ≠ .elp ∧ r ≠ .scause ∧ r ≠ .stval ∧ r ≠ .sepc ∧
      r ≠ .cur_privilege ∧ r ≠ .nextPC := by decide
  refine uxaXget_congr s.regs (trapSt s ip).regs (fun r hr => ?_) z
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg r hr
  exact trapStOther s ip r h1 h2 h3 h4 h5 h6 h7

/-! # 2. The record -/

section regimeI
variable (img : Image)

/-- Rocq `SpineOkI`. -/
structure SpineOkI (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop) : Prop where
  spiSeip : ∀ rs rs', ctrlOk rs → regsAgree AxRunClose.pinReg rs' rs → ctrlOk rs'
  spiHart : ∀ rs, ctrlOk rs → rs .hart_state = .HART_ACTIVE ()
  spiFrame : ∀ rs (r : Register) (v : RegisterType r), ctrlFree r → ctrlOk rs → ctrlOk (rs.set r v)
  spiInc : ∀ t : ExecSt, ctrlOk t.regs → ∃ b, EvA img (fun _ _ => False)
    (fun x t' => x = b ∧ t' = t) (should_inc_minstret (t.regs .cur_privilege)) t
  spiDisp : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (dispPost t) (dispatchInterrupt (t.regs .cur_privilege)) t
  spiTrap : ∀ (t : ExecSt) (ip : InterruptType), ctrlOk t.regs → intrOn t.regs →
    EvA img (fun _ _ => False) (fun x t' => x = () ∧ t' = trapSt t ip)
      (handle_interrupt ip .Supervisor) t
  spiTrapOk : ∀ (t : ExecSt) (ip : InterruptType), ctrlOk t.regs → ctrlOk (trapSt t ip).regs
  spiFetch : ∀ (t : ExecSt) pc h, ctrlOk t.regs → t.regs .PC = pc → textAt pc h →
    ∃ t1, tlbFrame t t1 ∧ ctrlOk t1.regs ∧
      EvA img (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t1) (fetch ()) t
  spiLpad : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t) (is_landing_pad_expected ()) t
  spiZca : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t) (currentlyEnabled .Ext_Zca) t
  spiTick : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun _ t' => ctrlOk t'.regs ∧ tickFrame t t') (tick_clock ()) t

/-- Rocq `EvA_hart_active_rvc_I`: `run_hart_active` with the interrupt arm — the dispatch answers
`some (ip, S)` ⇒ early return `Step_Pending_Interrupt` at the UNCHANGED state, before any fetch. -/
theorem EvAHartActiveRvcI (t t1 : ExecSt) (h : BitVec 16) (i0 ins : instruction) (pc : BitVec 64)
    (Qx : ExecSt → Prop) :
    EvA img (fun _ _ => False) (dispPost t) (dispatchInterrupt (t.regs .cur_privilege)) t →
    EvA img (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t1) (fetch ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t1) (ext_decode_compressed h) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t1) (is_landing_pad_expected ()) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t1) (currentlyEnabled .Ext_Zca) t1 →
    t1.regs .PC = pc →
    EvA img (fun _ _ => False)
      (fun x t' => x = .ExecuteAs ins ∧ t' = t1.setReg .nextPC (BitVec.addInt pc 2))
      (execute i0) (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    EvA img (fun _ _ => False) (fun x t' => x = RETIRE_SUCCESS ∧ Qx t') (execute ins)
      (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    EvA img (fun _ _ => False)
      (fun x t' => (x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) h) ∧ Qx t') ∨
        (∃ ip, x = .Step_Pending_Interrupt (ip, .Supervisor) ∧ t' = t ∧ intrOn t.regs))
      (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hlpad Hzca HPC Hexp Hexec
  subst HPC
  unfold run_hart_active
  apply EvACatchEarlyReturn
  ax_sym2_ev_go
  refine EvAFactLift img _ _ _ _ _ _ Hdisp ?_
  rintro r t' ⟨rfl, rfl | ⟨ip, rfl, hon⟩⟩
  · ax_sym2_ev_go
    refine AxSymEngine2.evRUse Hfetch ?_
    ax_sym2_ev_go
    refine AxSymEngine2.evRUse Hdec ?_
    ax_sym2_ev_go
    refine AxSymEngine2.evRUse Hlpad ?_
    ax_sym2_ev_go
    refine AxSymEngine2.evRUse Hzca ?_
    ax_sym2_ev_go
    refine AxSymEngine2.evRUse Hexp ?_
    ax_sym2_ev_go
    refine EvAFactLift img _ _ _ _ _ _ Hexec ?_
    rintro _ t' ⟨rfl, hq⟩
    exact .evRet _ _ (Or.inl ⟨rfl, hq⟩)
  · exact .evRet _ _ (Or.inr ⟨ip, rfl, rfl, hon⟩)

/-- Rocq `EvA_try_step_I`: `try_step` with the interrupt arm. -/
theorem EvATryStepI (t : ExecSt) (b : Bool) (bits : BitVec 32) (P : Prop)
    (Qx Qf : ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun x t' => x = b ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t →
    (t.setReg .minstret_increment b).regs .hart_state = .HART_ACTIVE () →
    EvA img (fun _ _ => False)
      (fun x t' => (x = .Step_Execute (RETIRE_SUCCESS, bits) ∧ Qx t') ∨
        (∃ ip, x = .Step_Pending_Interrupt (ip, .Supervisor) ∧
          t' = t.setReg .minstret_increment b ∧ P))
      (run_hart_active 0) (t.setReg .minstret_increment b) →
    (∀ tx, Qx tx → tx.regs .hart_state = .HART_ACTIVE () ∧
      tx.regs .minstret_increment = b ∧ Qf (tfinal b tx)) →
    (P → ∀ ip, EvA img (fun _ _ => False)
      (fun _ t' => t'.regs .hart_state = .HART_ACTIVE () ∧ Qf (t'.setReg .PC (t'.regs .nextPC)))
      (handle_interrupt ip .Supervisor) (t.setReg .minstret_increment b)) →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ Qf t') (try_step 0 false) t := by
  intro Hsi Hha Hrun Hfin Htrap
  unfold try_step
  dsimp only
  ax_sym2_ev_go
  refine AxSymEngine2.evFactUse Hsi ?_
  ax_sym2_ev_go
  apply EvABind
  ax_sym2_ev_go
  simp only [Hha]
  refine EvAMono img _ _ _ _ _ _ (fun _ _ h => h) ?_ Hrun
  rintro _ tx (⟨rfl, HQ⟩ | ⟨ip, rfl, rfl, HP⟩)
  · obtain ⟨Hhx, Hmix, HQf⟩ := Hfin tx HQ
    ax_sym2_ev_go
    simp only [Hhx]
    ax_sym2_ev_go
    simp only [Hhx]
    ax_sym2_ev_go
    have hmi : (tx.setReg .PC (tx.regs .nextPC)).regs .minstret_increment = b := by
      rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
      exact Hmix
    simp only [hmi]
    cases b <;> ax_sym2_ev_go <;> exact .evRet _ _ ⟨rfl, HQf⟩
  · ax_sym2_ev_go
    refine AxSymEngine2.evFactQ (Htrap HP ip) ?_
    rintro _ t' ⟨Hhs, HQf⟩
    ax_sym2_ev_go
    simp only [Hhs]
    ax_sym2_ev_go
    exact .evRet _ _ ⟨rfl, HQf⟩

end regimeI

/-! # 3. The record at the S-mode SIE-agnostic regime -/

/-- Rocq `SpineOkI_S` (deviation 5). -/
theorem spineOkIS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) :
    SpineOkI (imgS σi) (ctrlOkSI T satp0) (textAtS σi T) := by
  refine ⟨fun rs rs' hc hag => sptSeipSI T satp0 rs rs' hc hag,
    fun rs hc => sptHartSI T satp0 rs hc,
    fun rs r v hf hc => sptFrameSI T satp0 rs r v hf hc,
    fun t hc => sptIncSI σi T satp0 t hc,
    fun t hc => spiDispSI (imgS σi) T satp0 t hc, ?_,
    fun t ip hc => (trapOkSI T satp0 t ip hc).1,
    fun t pc h hc hpc ht => sptFetchSI σi T satp0 hmode hasid hppn t pc h hc hpc ht,
    fun t hc => sptLpadSI σi T satp0 t hc,
    fun t hc => sptZcaSI σi T satp0 t hc, ?_⟩
  · intro t ip hc hon
    obtain ⟨hpriv, -, hmisa, -, -, -, -, -, hsie, -⟩ := hc
    refine EvAHandleInterrupt (imgS σi) t ip hpriv (by rw [hmisa]; decide) ?_
    rcases hsie with hoff | hd
    · unfold intrOn at hon
      rw [hon] at hoff
      exact absurd hoff (by decide)
    · exact hd
  · intro t hc
    refine EvAMono (imgS σi) _ _ _ _ _ t (fun _ _ h => h) ?_ (sptTickFrame (imgS σi) t)
    intro _ t' hf
    exact ⟨tickFrameCtrl T satp0 t t' hf hc, hf⟩

/-! # 4. The trap post, and the whole-instruction certificates -/

section certI
variable (img : Image)

/-- Rocq `trap_post_of`. -/
theorem trapPostOf (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOkI img ctrlOk textAt) (rs : RegFile) (t : ExecSt) (b : Bool)
    (ip : InterruptType) :
    regsAgree AxRunClose.pinReg t.regs rs → intrOn rs → ctrlOk t.regs →
    TrapPost ctrlOk rs
      ((trapSt (t.setReg .minstret_increment b) ip).setReg .PC
        ((trapSt (t.setReg .minstret_increment b) ip).regs .nextPC)).regs := by
  intro Hag Hon Hc
  have Hca : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.spiFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hc
  have hm : ∀ r : Register, r ≠ .minstret_increment → r ≠ .sig_seip → r ≠ .sig_meip →
      (t.setReg .minstret_increment b).regs r = rs r := by
    intro r h1 h2 h3
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ h1]
    exact Hag r (AxSymEngine2.notPin r h2 h3)
  refine ⟨Hon, Hsp.spiFrame _ _ _ (Or.inl rfl) (Hsp.spiTrapOk _ ip Hca), ip, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [ExecSt.setReg_regs, RegFile.set_same]
    rw [trapStNextPC, hm _ (by decide) (by decide) (by decide)]
  · rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide), trapStSepc,
      hm _ (by decide) (by decide) (by decide)]
  · rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide), trapStMstatus,
      hm _ (by decide) (by decide) (by decide), hm _ (by decide) (by decide) (by decide)]
  · rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide), trapStScause,
      hm _ (by decide) (by decide) (by decide)]
  · rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide), trapStStval]
  · rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide), trapStPriv]
  · intro z
    rw [ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxIntr3.trapStXget,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag z

/-- Rocq `intr_on_minc`. -/
theorem intrOnMinc (t : ExecSt) (b : Bool) (rs : RegFile) :
    regsAgree AxRunClose.pinReg t.regs rs →
    intrOn (t.setReg .minstret_increment b).regs → intrOn rs := by
  intro Hag
  unfold intrOn
  rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide),
    Hag .mstatus (AxSymEngine2.notPin _ (by decide) (by decide))]
  exact id

/-- Rocq `spine_cert_I`: THE GPR-WRITE CERTIFICATE, SIE-agnostic (`spineCertT` with post
`Good ∨ TrapPost`). -/
theorem spineCertI (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOkI img ctrlOk textAt) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (rd : BitVec 5) (wval : BitVec 64) :
    ctrlOk rs → rs .PC = pc → textOkD img ctrlOk textAt pc true ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = BitVec.addInt pc 2 →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvA img (fun _ _ => False)
        (fun _ t' => Good ctrlOk rs pc rd wval t'.regs ∨ TrapPost ctrlOk rs t'.regs)
        (riscvStep tick) t := by
  intro Hct HPC ⟨_, h, i0, Hat, Hdec, Hexp, Hrf⟩ Hrd Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.spiSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.spiInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.spiFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct_1, Hfetch⟩ := Hsp.spiFetch _ pc h Hct_a HPC_a Hat
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc 2)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hexec : EvA img (fun _ _ => False)
      (fun x t' => x = RETIRE_SUCCESS ∧
        t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
      (execute ins) (t1.setReg .nextPC (BitVec.addInt pc 2)) :=
    rf0EvA img _ _ Hrf _ _ _ (Hcert _ (by simp only [ExecSt.setReg_regs, RegFile.set_same]) Hgag)
  have Hrun := EvAHartActiveRvcI img (t.setReg .minstret_increment b) t1 h i0 ins pc
    (fun t' => t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
    (Hsp.spiDisp _ Hct_a) Hfetch (Hdec _ Hct_1) (Hsp.spiLpad _ Hct_1)
    (Hsp.spiZca _ Hct_1) HPC_1 (Hexp _) Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  refine EvARiscvStep img tick t
    (fun t' => Good ctrlOk rs pc rd wval t'.regs ∨ TrapPost ctrlOk rs t'.regs) _ ?_ ?_
  · have HT := EvATryStepI img t b (zero_extend (m := 32) h)
      (intrOn (t.setReg .minstret_increment b).regs)
      (fun t' => t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
      (fun t' => Good ctrlOk rs pc rd wval t'.regs ∨ TrapPost ctrlOk rs t'.regs) Hb
      (Hsp.spiHart _ Hct_a) Hrun ?_ ?_
    · exact EvAMono img _ _ _ _ _ t (fun _ _ h => h) (fun _ _ h => h.2) HT
    · rintro _ rfl
      have Hx := AxSymEngine2.setGprRegsNe (t1.setReg .nextPC (BitVec.addInt pc 2)) rd wval
      refine ⟨?_, ?_, Or.inl ?_⟩
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.spiHart _ Hct_1
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · have Hct_x := AxSymEngine2.ctrlOkSetGpr ctrlOk Hsp.spiFrame
          (t1.setReg .nextPC (BitVec.addInt pc 2)) rd wval
          (Hsp.spiFrame _ _ _ (Or.inr (Or.inl rfl)) Hct_1)
        refine ⟨?_, ?_, ?_⟩
        · unfold tfinal
          cases b
          · exact Hsp.spiFrame _ _ _ (Or.inl rfl) Hct_x
          · exact Hsp.spiFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              (Hsp.spiFrame _ _ _ (Or.inl rfl) Hct_x)
        · unfold tfinal
          cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
            (try rw [RegFile.set_other _ _ _ _ (by decide)]) <;>
            rw [RegFile.set_same, Hx _ (by decide)] <;>
            simp only [ExecSt.setReg_regs, RegFile.set_same]
        · intro r Hr
          have e : uxaXget (tfinal b ((t1.setReg .nextPC
              (BitVec.addInt pc 2)).setGpr rd wval)).regs r =
              ((t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval).gpr r := by
            unfold tfinal ExecSt.gpr
            cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
              (try rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]) <;>
              rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
          rw [e]
          by_cases E : r = rd
          · subst E
            simp only [if_true]
            exact AxFetch3c.gprSetGprSame _ r wval Hrd
          · simp only [E, if_false]
            rw [AxFetch3c.gprSetGprNe _ rd r wval E]
            exact Hgag r Hr
    · intro Hon ip
      refine EvAMono img _ _ _ _ _ _ (fun _ _ h => h) ?_ (Hsp.spiTrap _ ip Hct_a Hon)
      rintro _ t' ⟨-, rfl⟩
      exact ⟨Hsp.spiHart _ (Hsp.spiTrapOk _ ip Hct_a),
        Or.inr (trapPostOf img ctrlOk textAt Hsp rs t b ip Hag (intrOnMinc t b rs Hag Hon) Hct_t)⟩
  · intro t' HG
    cases tick with
    | false => exact HG
    | true =>
      have Hc' : ctrlOk t'.regs := by
        rcases HG with HG | HG
        · exact HG.1
        · exact HG.2.1
      refine EvAMono img _ _ _ _ _ t' (fun _ _ h => h) ?_ (Hsp.spiTick t' Hc')
      rintro _ t'' ⟨Hc, Hf⟩
      rcases HG with HG | HG
      · obtain ⟨Hk1, Hk2⟩ := tickFrameKeep _ _ Hf
        obtain ⟨-, HG2, HG3⟩ := HG
        exact Or.inl ⟨Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩
      · exact Or.inr (trapPostTick ctrlOk rs t' t'' HG Hc Hf)

end certI

section certCI
variable (img : Image)

/-- Rocq `wr_npc_ctrl_I`. -/
theorem wrNpcCtrlI (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOkI img ctrlOk textAt) (ow : Option (BitVec 5 × BitVec 64))
    (ot : Option (BitVec 64)) (s : ExecSt) :
    ctrlOk s.regs → ctrlOk (wrOpt ow (npcOpt ot s)).regs := by
  intro Hc
  have Hn : ctrlOk (npcOpt ot s).regs := by
    cases ot with
    | none => exact Hc
    | some tg => exact Hsp.spiFrame _ _ _ (Or.inr (Or.inl rfl)) Hc
  cases ow with
  | none => exact Hn
  | some p =>
    obtain ⟨rd, v⟩ := p
    exact AxSymEngine2.ctrlOkSetGpr ctrlOk Hsp.spiFrame _ rd v Hn

/-- Rocq `spine_certC_I`: THE COMPRESSED CONTROL-TRANSFER CERTIFICATE, SIE-agnostic
(`AxSymCtl2.spineCertC` at `no4`, post `GoodC ∨ TrapPost`). -/
theorem spineCertCI (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOkI img ctrlOk textAt) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64)) :
    ctrlOk rs → rs .PC = pc → textOkCtl img ctrlOk textAt no4 pc is_rvc ins →
    owOk ow → CertC ctrlOk rs pc is_rvc ins ot ow →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvA img (fun _ _ => False)
        (fun _ t' => GoodC ctrlOk is_rvc rs pc ot ow t'.regs ∨ TrapPost ctrlOk rs t'.regs)
        (riscvStep tick) t := by
  intro Hct HPC ⟨Hrf, Htx⟩ How Hcert tick t Hag
  cases is_rvc with
  | false =>
    rw [if_neg Bool.false_ne_true] at Htx
    obtain ⟨_, Hw, _⟩ := Htx
    exact Hw.elim
  | true =>
  rw [if_pos rfl] at Htx
  obtain ⟨h, i0, Hat, Hdec, Hexp⟩ := Htx
  have Hct_t : ctrlOk t.regs := Hsp.spiSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.spiInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.spiFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct1, Hfetch⟩ := Hsp.spiFetch _ pc h Hct_a HPC_a Hat
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc (incr true))).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOk (t1.setReg .nextPC (BitVec.addInt pc (incr true))).regs :=
    Hsp.spiFrame _ _ _ (Or.inr (Or.inl rfl)) Hct1
  have HPC_pc : (t1.setReg .nextPC (BitVec.addInt pc (incr true))).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_1
  have Hnpc_pc : (t1.setReg .nextPC (BitVec.addInt pc (incr true))).regs .nextPC =
      BitVec.addInt pc (incr true) := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hexec := EvAOfRfF img _ Hrf _ _ _ (Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag)
  have Hrun := EvAHartActiveRvcI img (t.setReg .minstret_increment b) t1 h i0 ins pc
    (fun t' => t' = wrOpt ow (npcOpt ot (t1.setReg .nextPC (BitVec.addInt pc (incr true)))))
    (Hsp.spiDisp _ Hct_a) Hfetch (Hdec _ Hct1) (Hsp.spiLpad _ Hct1) (Hsp.spiZca _ Hct1) HPC_1
    (Hexp _) Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hct_x := wrNpcCtrlI img ctrlOk textAt Hsp ow ot _ Hct_pc
  refine EvARiscvStep img tick t
    (fun t' => GoodC ctrlOk true rs pc ot ow t'.regs ∨ TrapPost ctrlOk rs t'.regs) _ ?_ ?_
  · have HT := EvATryStepI img t b (zero_extend (m := 32) h)
      (intrOn (t.setReg .minstret_increment b).regs)
      (fun t' => t' = wrOpt ow (npcOpt ot (t1.setReg .nextPC (BitVec.addInt pc (incr true)))))
      (fun t' => GoodC ctrlOk true rs pc ot ow t'.regs ∨ TrapPost ctrlOk rs t'.regs) Hb
      (Hsp.spiHart _ Hct_a) Hrun ?_ ?_
    · exact EvAMono img _ _ _ _ _ t (fun _ _ h => h) (fun _ _ h => h.2) HT
    · rintro _ rfl
      refine ⟨?_, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.spiHart _ Hct1
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · unfold tfinal
        cases b
        · exact Hsp.spiFrame _ _ _ (Or.inl rfl) Hct_x
        · exact Hsp.spiFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (Hsp.spiFrame _ _ _ (Or.inl rfl) Hct_x)
      · rw [tfinalPC, wrNpcNextPC]
        cases ot with
        | none => exact Hnpc_pc
        | some tg => rfl
      · intro r Hr
        rw [tfinalGpr, wrNpcGpr _ _ _ _ Hr How]
        exact gprPostAgree _ _ _ _ Hgag Hr
    · intro Hon ip
      refine EvAMono img _ _ _ _ _ _ (fun _ _ h => h) ?_ (Hsp.spiTrap _ ip Hct_a Hon)
      rintro _ t' ⟨-, rfl⟩
      exact ⟨Hsp.spiHart _ (Hsp.spiTrapOk _ ip Hct_a),
        Or.inr (trapPostOf img ctrlOk textAt Hsp rs t b ip Hag (intrOnMinc t b rs Hag Hon) Hct_t)⟩
  · intro t' HG
    cases tick with
    | false => exact HG
    | true =>
      have Hc' : ctrlOk t'.regs := by
        rcases HG with HG | HG
        · exact HG.1
        · exact HG.2.1
      refine EvAMono img _ _ _ _ _ t' (fun _ _ h => h) ?_ (Hsp.spiTick t' Hc')
      rintro _ t'' ⟨Hc, Hf⟩
      rcases HG with HG | HG
      · obtain ⟨Hk1, Hk2⟩ := tickFrameKeep _ _ Hf
        obtain ⟨-, HG2, HG3⟩ := HG
        exact Or.inl ⟨Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩
      · exact Or.inr (trapPostTick ctrlOk rs t' t'' HG Hc Hf)

end certCI

end Weak
