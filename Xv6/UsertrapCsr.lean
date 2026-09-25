/-
`usertrap()`'s two trap-CSR reads the landed MachCSL rules do not cover
(Rocq's `wp_csrr_s_sconf` at `stval`, and `sepc` at an arbitrary value):

* `csrr rd, stval` (the unexpected-scause printk and the vmfault argument);
* `csrr rd, sepc` at ANY cell value: the model aligns what it returns
  (`get_xepc` clears bit 0), so `rd` gets `e &&& ~1` (`retPc e`) -- the
  landed `MachCSL.wp_s_csrr_sepc` asks for an even cell, which a trap from
  U-mode's `sepc` is not known to be here.

Recommended move: both into `MachCSL/WpSmodeTrapCsr.lean` (a landed edit).
-/
import MachCSL.WpSmodeTrapCsr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {lent : Bool}

@[local sail_facts] theorem ut_csr_name_map_forwards_stval :
    csr_name_map_forwards 0x143#12 = pure "stval" := rfl
@[local sail_facts] theorem ut_read_CSR_stval : read_CSR 0x143#12 = readReg Register.stval := rfl

set_option maxHeartbeats 4000000 in
/-- `csrr rd, stval`: the trap value into `rd`, the cell untouched. -/
theorem ut_execSpecF_csrr_stval (cpu : CPU) (c : MConf) (sie : Bool) (hok : SConfPhys (GF := GF) c sie)
    (pc npc₀ : BitVec 64) (rd : BitVec 5) (hrd : rd ≠ 0#5) (R : RegMap) (e : BitVec 64) :
    execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c
      (instruction.CSRReg (0x143#12, regidx.Regidx 0#5, regidx.Regidx rd, csrop.CSRRS)) pc npc₀ npc₀
      iprop(gprFile cpu R ∗ Register.stval ↦ᵣ[cpu] e)
      iprop(gprFile cpu (R.set rd e) ∗ Register.stval ↦ᵣ[cpu] e) := by
  intro Φ
  iintro ⟨HmConf, HPC, HnextPC, ⟨HF, Hstval⟩, HΦ⟩
  conf_cases HmConf
  obtain ⟨hpmp, hms, hpmm, hlpe⟩ := hok
  obtain ⟨hSIE, hMPRV, hSXL, hMXR, hTSR, hTVM, hFS, hXS, hVS, hSD, hMPP⟩ := hms
  unfold execute
  swp_run 300
  iapply swp_bind
  iapply swp_wX_file (hrd := hrd)
  iframe
  inext
  iintro HF
  swp_run 20
  conf_intro HmConf
  iapply HΦ $$ HmConf HPC HnextPC [HF Hstval]
  iframe HF Hstval

/-- `csrr rd, stval` with interrupts off: the client's `stval` cell. -/
theorem ut_wp_s_csrr_stval [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (pc : BitVec 64) (is_rvc : Bool) (rd : BitVec 5) (hrd : rdOk rd) (e : BitVec 64) :
    instr (GF := GF) pc is_rvc (instruction.CSRReg (0x143#12, regidx.Regidx 0#5, regidx.Regidx rd, csrop.CSRRS)) ∗
    kctxL lent cpu k ∗ pcIs cpu pc ∗ Register.stval ↦ᵣ[cpu] e ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctxL lent cpu' (k.setReg rd e) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          Register.stval ↦ᵣ[cpu'] e -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_setReg' cpu k pc _ is_rvc _ rd hrd (fun _ => e) _ _
    (fun cpu' c hpin hok _ => by
      obtain rfl := hpin (Or.inl hsie)
      exact ut_execSpecF_csrr_stval (GF := GF) cpu' c k.sie hok.phys pc (pc + instrLen is_rvc) rd hrd.1
        (tpPin cpu' k.regs) e)

/-- `csrr rd, sepc` at any cell value, interrupts off: the aligned value. -/
theorem ut_wp_s_csrr_sepc_any [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx)
    (hsie : k.sie = false) (pc : BitVec 64) (is_rvc : Bool) (rd : BitVec 5) (hrd : rdOk rd) (e : BitVec 64) :
    instr (GF := GF) pc is_rvc (instruction.CSRReg (0x141#12, regidx.Regidx 0#5, regidx.Regidx rd, csrop.CSRRS)) ∗
    kctxL lent cpu k ∗ pcIs cpu pc ∗ Register.sepc ↦ᵣ[cpu] e ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctxL lent cpu' (k.setReg rd (e &&& 0xFFFFFFFFFFFFFFFE#64)) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          Register.sepc ↦ᵣ[cpu'] e -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_setReg' cpu k pc _ is_rvc _ rd hrd (fun _ => e &&& 0xFFFFFFFFFFFFFFFE#64) _ _
    (fun cpu' c hpin hok _ => by
      obtain rfl := hpin (Or.inl hsie)
      exact execSpecF_csrr_sepc (GF := GF) cpu' c k.sie hok.phys pc (pc + instrLen is_rvc) rd hrd.1
        (tpPin cpu' k.regs) e)

end Xv6
