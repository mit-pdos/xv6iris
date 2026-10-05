/-
MachCSL: `csrw scounteren, rs1` in supervisor mode -- the S-mode
counter-enable write (NI M3 quotas Q-0: the `verified-quota` kernel's
`w_scounteren(0)` at the end of `plicinithart`, which every hart runs before
user mode, so a user `rdcycle`/`rdtime`/`rdinstret` traps).

Derived from the model, as `WpSmodeTime`'s `stimecmp` write: `write_CSR
0x106` reads the cell, writes `legalize_scounteren` of the value and reads it
back.  The cell is one of the hart's clock cells (`MachCSL.clockCells`, at
some value; it left the frozen `hwConfig` at Q-0), lent to the execute stage
(`execSpecClkPP`), so the kernel context comes back UNCHANGED and the new
value disappears into `clockCells`' existential (the per-hart pin
`scounteren = 0` is optional lane Q-5's).  No new axiom or opaque.
-/
import MachCSL.WpSmodeTime

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {lent : Bool}

@[sail_facts] theorem csr_name_map_forwards_scounteren : csr_name_map_forwards 0x106#12 = pure "scounteren" :=
  rfl

-- the `write_CSR` arm, so the leaf never unfolds the model's whole match.
theorem write_CSR_scounteren (v : BitVec 64) : write_CSR 0x106#12 v =
    (do writeReg Register.scounteren (legalize_scounteren (← readReg Register.scounteren) v)
        pure (.Ok (zero_extend (m := 64) (← readReg Register.scounteren)))) := rfl

set_option maxHeartbeats 4000000 in
/-- `write_CSR scounteren v`: the cell takes `legalize_scounteren sc v`. -/
theorem swp_write_CSR_scounteren (cpu : CPU) (sc : BitVec 32) (v : BitVec 64)
    (Φ : Result (BitVec 64) Unit → IProp GF) :
    Register.scounteren ↦ᵣ[cpu] sc ∗
    ▷ (Register.scounteren ↦ᵣ[cpu] legalize_scounteren sc v -∗
        Φ (.Ok (zero_extend (m := 64) (legalize_scounteren sc v))))
    ⊢ swp cpu (write_CSR 0x106#12 v) Φ := by
  iintro ⟨Hscounteren, HΦ⟩
  rw [write_CSR_scounteren]
  swp_run 40
  iapply HΦ $$ Hscounteren

set_option maxHeartbeats 4000000 in
/-- The execute stage of `csrw scounteren, rs1` in supervisor mode: the
cell takes the (legalized) register value; the file and the configuration
are untouched. -/
theorem execSpecF_csrw_scounteren (cpu : CPU) (c : MConf) (sie : Bool) (hok : SConfPhys (GF := GF) c sie)
    (pc npc₀ : BitVec 64) (rs1 : BitVec 5) (R : RegMap) (sc : BitVec 32) :
    execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c
      (instruction.CSRReg (0x106#12, regidx.Regidx rs1, regidx.Regidx 0#5, csrop.CSRRW)) pc npc₀ npc₀
      iprop(gprFile cpu R ∗ Register.scounteren ↦ᵣ[cpu] sc)
      iprop(gprFile cpu R ∗ ∃ sc' : BitVec 32, Register.scounteren ↦ᵣ[cpu] sc') := by
  intro Φ
  iintro ⟨HmConf, HPC, HnextPC, ⟨HF, Hscounteren⟩, HΦ⟩
  conf_cases HmConf
  obtain ⟨hpmp, hms, hpmm, hlpe⟩ := hok
  obtain ⟨hSIE, hMPRV, hSXL, hMXR, hTSR, hTVM, hFS, hXS, hVS, hSD, hMPP⟩ := hms
  unfold execute
  swp_run 30
  iapply swp_bind
  iapply swp_rX_file
  iframe
  iintro HF
  try unfold doCSR
  generalize hW : write_CSR 0x106#12 = W
  swp_run 300
  subst hW
  iapply swp_bind
  iapply swp_write_CSR_scounteren
  iframe
  inext
  iintro Hscounteren
  swp_run 30
  try (unfold wX_bits wX; simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast])
  swp_run 80
  conf_intro HmConf
  iapply HΦ $$ HmConf HPC HnextPC [HF Hscounteren]
  iframe HF
  iexists _
  iexact Hscounteren

/-- `csrw scounteren, rs1` as a clock-lending stage. -/
theorem execSpecClk_csrw_scounteren (cpu : CPU) (c : MConf) (sie : Bool) (hok : SConfPhys (GF := GF) c sie)
    (pc npc₀ : BitVec 64) (rs1 : BitVec 5) (R : RegMap) :
    execSpecClkPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c
      (instruction.CSRReg (0x106#12, regidx.Regidx rs1, regidx.Regidx 0#5, csrop.CSRRW)) pc npc₀ npc₀
      (gprFile cpu R) (gprFile cpu R) := by
  intro ip mt sc Φ
  iintro ⟨HmConf, HPC, HnextPC, ⟨HF, Hmip, Hmtime, Hscounteren⟩, HΦ⟩
  iapply (execSpecF_csrw_scounteren cpu c sie hok pc npc₀ rs1 R sc Φ)
  iframe HmConf HPC HnextPC HF Hscounteren
  inext
  iintro HmConf HPC HnextPC ⟨HF, %sc', Hscounteren⟩
  iapply HΦ $$ HmConf HPC HnextPC [HF Hmip Hmtime Hscounteren]
  isplitl [HF]
  · iexact HF
  · iexists ip, mt, sc'
    iframe Hmip Hmtime Hscounteren

set_option maxHeartbeats 4000000 in
/-- **`csrw scounteren, rs1`** with interrupts off (NI M3 quotas Q-0): the
S-mode counter-enable takes the register's (legalized) value.  The cell is
one of `clockCells`, at some value, so the kernel context comes back
UNCHANGED. -/
theorem wp_s_csrw_scounteren [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (pc : BitVec 64) (is_rvc : Bool) (rs1 : BitVec 5) :
    instr (GF := GF) pc is_rvc (instruction.CSRReg (0x106#12, regidx.Regidx rs1, regidx.Regidx 0#5, csrop.CSRRW)) ∗
    kctxL lent cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctxL lent cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, HConf, HF, Hstack, Htrans, Harm, Hcpu, Htok, Hclock, #Hro⟩
  icases kConf_cases cpu _ _ _ _ _ $$ HConf with ⟨%ms, %mdl, %mepc, %stc, %lf, %⟨hsm, hsr, hmdl, hlf⟩, HmConf⟩
  unfold transSlot
  icases Htrans with ⟨%hkt, Htrans⟩
  rw [hsie] at hsm hsr
  simp only [hsie, hkt, trapRes_off]
  have hok := SConfAt_sConfOf (GF := GF) curTier k.root ms mdl mepc stc lf false hsm hlf
  have hexec := (execSpecClk_csrw_scounteren (GF := GF) cpu (sConfOf curTier k.root ms mdl mepc stc lf) false
    hok.phys pc (pc + instrLen is_rvc) rs1 (tpPin cpu k.regs)).frameL (transTok cpu curTier k.root)
  iapply (wpLoop_s_instr_clk cpu _ _ curTier k.root false hok hmdl rfl rfl pc _ is_rvc _ _ _ hexec)
  iframe HI HmConf Hclock Hpc HF
  isplitl [Htrans Htok]
  · unfold transTok; iframe Htrans Htok
  isplit
  rotate_left 1
  · unfold trapBranch
    iintro %hs
    exact absurd hs Bool.false_ne_true
  inext
  iintro HmConf Hclock Hpc HT HF
  unfold transTok
  icases HT with ⟨Htrans, Htok⟩
  ihave HΦ' := wpNext_off _ _ _ $$ HΦ
  ihave HConf := kConf_intro cpu curTier k.root false k.spie k.spp ms mdl mepc stc lf
    ⟨hsm, hsr, hmdl, hlf⟩ $$ HmConf
  iapply HΦ' $$ [HConf HF Hstack Htrans Harm Hcpu Htok Hclock] Hpc
  iapply (kctx_intro' cpu k hwf)
  simp only [hkt, hsie, trapRes_off]
  unfold transSlot
  iframe HConf HF Hstack Htrans Harm Hcpu Htok Hclock
  isplit
  · ipureintro; rfl
  · iexact Hro

end MachCSL
