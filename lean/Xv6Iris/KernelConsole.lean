/-
The whole xv6 boot ALL THE WAY THROUGH `consoleinit()`, on the real Sail model:
boot, `start()`/`mret` into supervisor-mode `main`, then `main` calls `cpuid()`
and `consoleinit()` — which runs `initlock`, `uartinit` (UART MMIO at 0x10000000),
`initlock` again, and wires up `devsw` — and returns. 145 real `try_step`s, all in
the right privilege modes (M for boot, S for main/consoleinit).

Built on the whole-machine-state engine `KernelMain.wp_run`: `wp_through_consoleinit`
runs all 145 steps from one operational reduction, and it CHAINS `wp_boot_to_main1`
(its first 56 steps) with `wp_console_from_main1` (89 more), via `runSteps_add`. No
per-instruction lemmas; UART MMIO is just plain memory writes (not `within_mmio`),
and S-mode/privilege transitions need no special handling (all in the one state
cell). Big R/W/X PMA region covers RAM + the UART device. `make kernel-console`.
-/
import Xv6Iris.KernelMain
import Xv6Iris.KernelImage
import LeanRV64D

open Iris Iris.BI Iris.ProgramLogic Std
open Xv6Iris.Model Xv6Iris.Model.KernelMain
open LeanRV64D.Defs LeanRV64D.Functions PreSail

set_option maxRecDepth 16000000
set_option maxHeartbeats 16000000000

namespace Xv6Iris.Model.KernelConsole

noncomputable def bigPMA : PMA := { (default : PMA) with
  executable := true, readable := true, writable := true }
/-- One big region covering RAM (0x80000000+) AND the UART device (0x10000000). -/
noncomputable def bigRegion : PMA_Region :=
  { base := 0x0#64, size := 0x90000000#64, attributes := bigPMA, include_in_device_tree := false }

/-- Kernel text for every function on the path: start/timerinit, main, cpuid,
consoleinit, initlock, uartinit. -/
/-- Kernel memory: the shared ELF image (KernelImage), 0 outside it. -/
noncomputable def mem0 (a : Nat) : Option (BitVec 8) := some (kernelByte a)

/-- Booting-Machine state at the `start` entry (hart 0); big PMA region. -/
noncomputable def σ0 : MState where
  regs r := match r with
    | .cur_privilege => some Privilege.Machine
    | .PC => some (0x80000058#64)
    | .misa => some 0x8000000003ffffff
    | .mstatus => some 0xA00000000
    | .pma_regions => some [bigRegion]
    | .x1 => some 0x8000001a
    | .x2 => some 0x80100000
    | r => some (decReg r 0)
  mem := mem0

def consRet : BitVec 64 := 0x80000EC8

/-- **Operational: boot all the way through `consoleinit`.** 145 real `try_step`s
reach `consoleinit`'s return point in `main` (0x80000EC8), still in Supervisor mode. -/
theorem console_to_main_ret :
    (runSteps 145 σ0).map (fun s => (s.regs Register.PC, s.regs Register.cur_privilege))
      = some (some consRet, some Privilege.Supervisor) := by
  with_unfolding_all rfl


theorem isSome145 : (runSteps 145 σ0).isSome := by
  obtain ⟨σm, h1, _⟩ := Option.map_eq_some_iff.mp console_to_main_ret; rw [h1]; rfl

/-- Machine state at `consoleinit`'s return (back in `main`). -/
noncomputable def σ_console : MState := (runSteps 145 σ0).get isSome145
theorem run145 : runSteps 145 σ0 = some σ_console := (Option.some_get isSome145).symm

theorem isSome56 : (runSteps 56 σ0).isSome := by
  have hadd : runSteps 145 σ0 = (runSteps 56 σ0).bind (fun s => runSteps 89 s) := runSteps_add 56 89 σ0
  rw [run145] at hadd
  rcases hs : runSteps 56 σ0 with _ | σm
  · rw [hs] at hadd; simp at hadd
  · rfl

/-- Machine state after `main`'s first instruction (the `wp_boot_to_main1` point). -/
noncomputable def σ_main1 : MState := (runSteps 56 σ0).get isSome56
theorem run56 : runSteps 56 σ0 = some σ_main1 := (Option.some_get isSome56).symm

/-- The `consoleinit` run, as 89 steps from the post-main-first state. -/
theorem run_main1_to_console : runSteps 89 σ_main1 = some σ_console := by
  have hadd : runSteps 145 σ0 = (runSteps 56 σ0).bind (fun s => runSteps 89 s) := runSteps_add 56 89 σ0
  rw [run56, run145] at hadd
  exact hadd.symm

theorem σ_console_props :
    σ_console.regs Register.PC = some consRet ∧
    σ_console.regs Register.cur_privilege = some Privilege.Supervisor := by
  obtain ⟨a, h1, h2⟩ := Option.map_eq_some_iff.mp console_to_main_ret
  have ha : a = σ_console := Option.some.inj (h1.symm.trans run145)
  subst ha
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

section
variable {GF : BundledGFunctors} {hlc : HasLC} [D : MainGS hlc GF]

/-- Boot through `main`'s first instruction (= `KernelStart.wp_boot_to_main1`). -/
theorem wp_boot_to_main1 {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    (machineState σ0 : IProp GF) ⊢
      (▷^[56] (machineState σ_main1 -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} :=
  wp_run 56 σ0 σ_main1 run56

/-- **Through all of `consoleinit`, from the post-main-first state** (supervisor
mode: prologue, `cpuid`, `consoleinit` → `initlock`/`uartinit`(UART MMIO)/`initlock`,
`devsw`). -/
theorem wp_console_from_main1 {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    machineState σ_main1 -∗
      (▷^[89] (machineState σ_console -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro Hm; iapply (wp_run 89 σ_main1 σ_console run_main1_to_console) $$ Hm

/-- **The whole boot all the way through `consoleinit`, chained.** 145 real
`try_step`s — boot, `start()`/`mret`, into supervisor-mode `main`, through
`consoleinit`'s return — = `wp_boot_to_main1` (56) ▸ `wp_console_from_main1` (89). -/
theorem wp_through_consoleinit {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    (machineState σ0 : IProp GF) ⊢
      (▷^[145] (machineState σ_console -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} :=
  wp_run 145 σ0 σ_console run145

end
end Xv6Iris.Model.KernelConsole
