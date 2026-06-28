/-
The xv6 boot extended INTO supervisor-mode `main`: `start()` runs through `mret`
to `main` (0x80000E82, Supervisor), then `main`'s first instruction
(`c.addi sp,sp,-16`) executes — IN SUPERVISOR MODE — and this is chained onto the
post-`start()` WP. All on the real Sail model.

Engine: the whole-machine-state `wp_run` (KernelMain). `wp_start_to_main` (55 steps
to `main`) hands off `machineState σmain`; `wp_main_step` runs main's first
instruction (one S-mode `try_step`); `wp_boot_to_main1` is the chain (56 steps =
55 ▸ 1, via `runSteps_add`). The single 56-step operational reduction `main_first`
supplies everything — no per-instruction lemmas, and the S-mode fetch works because
`start()` set `satp=Bare`/PMP-open. Build with `make kernel-start` (big `--tstack`).
-/
import Xv6Iris.KernelMain
import Xv6Iris.KernelImage
import LeanRV64D

open Iris Iris.BI Iris.ProgramLogic Std
open Xv6Iris.Model Xv6Iris.Model.KernelMain
open LeanRV64D.Defs LeanRV64D.Functions PreSail

set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000000

namespace Xv6Iris.Model.KernelStart

noncomputable def ramPMA : PMA := { (default : PMA) with
  executable := true, readable := true, writable := true }
noncomputable def ramRegion : PMA_Region :=
  { base := 0x80000000#64, size := 0x10000000#64, attributes := ramPMA, include_in_device_tree := false }

/-- Kernel text: `start`/`timerinit` (0x1c..0xbf) + `main`'s first bytes (0x80000e82..). -/
/-- Kernel memory: the shared ELF image (KernelImage), 0 outside it. -/
noncomputable def mem0 (a : Nat) : Option (BitVec 8) := some (kernelByte a)

/-- Booting-Machine state at the `start` entry (hart 0; reset CSRs + RAM stack). -/
noncomputable def σ0 : MState where
  regs r := match r with
    | .cur_privilege => some Privilege.Machine
    | .PC => some (0x80000058#64)
    | .misa => some 0x8000000003ffffff
    | .mstatus => some 0xA00000000
    | .pma_regions => some [ramRegion]
    | .x1 => some 0x8000001a
    | .x2 => some 0x80100000
    | r => some (decReg r 0)
  mem := mem0

def mainAddr1 : BitVec 64 := 0x80000E84

/-- **Operational: through `mret` AND main's first instruction.** 56 real
`try_step`s — `start()` (incl. `timerinit` + `mret`) then `main`'s `c.addi sp,-16`
in **Supervisor** mode — leave PC at `main+2`, sp decremented, still Supervisor. -/
theorem main_first :
    (runSteps 56 σ0).map (fun s => (s.regs Register.PC, s.regs Register.x2, s.regs Register.cur_privilege))
      = some (some mainAddr1, some 0x800fffe0, some Privilege.Supervisor) := by
  with_unfolding_all rfl


theorem isSome56 : (runSteps 56 σ0).isSome := by
  obtain ⟨σm, h1, _⟩ := Option.map_eq_some_iff.mp main_first; rw [h1]; rfl

/-- Machine state after `start()` + main's first instruction. -/
noncomputable def σ_main1 : MState := (runSteps 56 σ0).get isSome56
theorem run56 : runSteps 56 σ0 = some σ_main1 := (Option.some_get isSome56).symm

theorem isSome55 : (runSteps 55 σ0).isSome := by
  have hadd : runSteps 56 σ0 = (runSteps 55 σ0).bind (fun s => runSteps 1 s) := runSteps_add 55 1 σ0
  rw [run56] at hadd
  rcases hs : runSteps 55 σ0 with _ | σm
  · rw [hs] at hadd; simp at hadd
  · rfl

/-- Machine state after `start()` (the `wp_start_to_main` hand-off point). -/
noncomputable def σmain : MState := (runSteps 55 σ0).get isSome55
theorem run55 : runSteps 55 σ0 = some σmain := (Option.some_get isSome55).symm

/-- The first `main` instruction, as a single `exec` step from `σmain`. -/
theorem exec_main1 : exec riscv_step σmain = some ((), σ_main1) := by
  have hadd : runSteps 56 σ0 = (runSteps 55 σ0).bind (fun s => runSteps 1 s) := runSteps_add 55 1 σ0
  rw [run55, run56] at hadd
  have hadd2 : (exec riscv_step σmain).bind (fun p => some p.2) = some σ_main1 := by
    rw [hadd]; rfl
  obtain ⟨⟨u, σ''⟩, he, hb⟩ := Option.bind_eq_some_iff.mp hadd2
  cases u
  have hσ : σ'' = σ_main1 := by simpa using hb
  subst hσ; exact he

theorem σ_main1_props :
    σ_main1.regs Register.PC = some mainAddr1 ∧
    σ_main1.regs Register.x2 = some 0x800fffe0 ∧
    σ_main1.regs Register.cur_privilege = some Privilege.Supervisor := by
  obtain ⟨a, h1, h2⟩ := Option.map_eq_some_iff.mp main_first
  have ha : a = σ_main1 := Option.some.inj (h1.symm.trans run56)
  subst ha
  exact ⟨congrArg (·.1) h2, congrArg (·.2.1) h2, congrArg (·.2.2) h2⟩

section
variable {GF : BundledGFunctors} {hlc : HasLC} [D : MainGS hlc GF]

/-- After `start()` (`wp_start_to_main`'s hand-off). -/
theorem wp_start_to_main {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    (machineState σ0 : IProp GF) ⊢
      (▷^[55] (machineState σmain -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} :=
  wp_run 55 σ0 σmain run55

/-- **The first instruction of `main` (Supervisor mode), as a WP step** from the
post-`start()` state. -/
theorem wp_main_step {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    machineState σmain -∗ ▷ (machineState σ_main1 -∗ WP RiscvExpr.Loop @ s; E {{ Φ }}) -∗
      WP RiscvExpr.Loop @ s; E {{ Φ }} :=
  wp_machine_step exec_main1

/-- **Boot through the first `main` instruction, chained.** This is
`wp_start_to_main` (55 steps to `main`) composed with `wp_main_step` (one S-mode
step) — `runSteps 56 = runSteps 55 ▸ runSteps 1`. -/
theorem wp_boot_to_main1 {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    (machineState σ0 : IProp GF) ⊢
      (▷^[56] (machineState σ_main1 -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} :=
  wp_run 56 σ0 σ_main1 run56

end
end Xv6Iris.Model.KernelStart
