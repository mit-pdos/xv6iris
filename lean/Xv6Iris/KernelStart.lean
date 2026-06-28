/-
The xv6 kernel's `start()` verified through `mret`, BOTH operationally
(`start_to_main`) and as a weakest-precondition over the program logic
(`wp_start_to_main`) — the WP for execution up to `main`.

`start()` (54 instructions: the M-mode config body + the called `timerinit()` + the
`mret`) leaves the hart at `main` (0x80000E82) in Supervisor mode. The WP is built
on the whole-machine-state engine `KernelMain.wp_run`: owning the boot token
`machineState σ0`, after 55 real `try_step`s the continuation gets `machineState
σmain`, which (`σmain_at_main`) is at `main` in Supervisor mode. The 55 per-step
`exec` facts come from decomposing the single operational reduction — no
per-instruction lemmas, and memory writes + the privilege change are handled
automatically (the whole state is one heap cell).

Boot-frontier reset CSRs: mstatus.SXL/UXL = RV64, misa.MXL = RV64. Build with
`make kernel-start` (the operational reduction needs a large `--tstack`).
-/
import Xv6Iris.KernelMain
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

/-- Kernel text for `start` (0x58..0xbc) + `timerinit` (0x1c..0x56); stack RAM is
the default `some 0`. -/
noncomputable def mem0 (a : Nat) : Option (BitVec 8) :=
  if a = 0 then some 0
  else if a = 0x8000001c then some 0x41
  else if a = 0x8000001d then some 0x11
  else if a = 0x8000001e then some 0x6
  else if a = 0x8000001f then some 0xe4
  else if a = 0x80000020 then some 0x22
  else if a = 0x80000021 then some 0xe0
  else if a = 0x80000022 then some 0x0
  else if a = 0x80000023 then some 0x8
  else if a = 0x80000024 then some 0xf3
  else if a = 0x80000025 then some 0x27
  else if a = 0x80000026 then some 0xa0
  else if a = 0x80000027 then some 0x30
  else if a = 0x80000028 then some 0x7d
  else if a = 0x80000029 then some 0x57
  else if a = 0x8000002a then some 0x7e
  else if a = 0x8000002b then some 0x17
  else if a = 0x8000002c then some 0xd9
  else if a = 0x8000002d then some 0x8f
  else if a = 0x8000002e then some 0x73
  else if a = 0x8000002f then some 0x90
  else if a = 0x80000030 then some 0xa7
  else if a = 0x80000031 then some 0x30
  else if a = 0x80000032 then some 0xf3
  else if a = 0x80000033 then some 0x27
  else if a = 0x80000034 then some 0x60
  else if a = 0x80000035 then some 0x30
  else if a = 0x80000036 then some 0x93
  else if a = 0x80000037 then some 0xe7
  else if a = 0x80000038 then some 0x27
  else if a = 0x80000039 then some 0x0
  else if a = 0x8000003a then some 0x73
  else if a = 0x8000003b then some 0x90
  else if a = 0x8000003c then some 0x67
  else if a = 0x8000003d then some 0x30
  else if a = 0x8000003e then some 0xf3
  else if a = 0x8000003f then some 0x27
  else if a = 0x80000040 then some 0x10
  else if a = 0x80000041 then some 0xc0
  else if a = 0x80000042 then some 0x37
  else if a = 0x80000043 then some 0x47
  else if a = 0x80000044 then some 0xf
  else if a = 0x80000045 then some 0x0
  else if a = 0x80000046 then some 0x13
  else if a = 0x80000047 then some 0x7
  else if a = 0x80000048 then some 0x7
  else if a = 0x80000049 then some 0x24
  else if a = 0x8000004a then some 0xba
  else if a = 0x8000004b then some 0x97
  else if a = 0x8000004c then some 0x73
  else if a = 0x8000004d then some 0x90
  else if a = 0x8000004e then some 0xd7
  else if a = 0x8000004f then some 0x14
  else if a = 0x80000050 then some 0xa2
  else if a = 0x80000051 then some 0x60
  else if a = 0x80000052 then some 0x2
  else if a = 0x80000053 then some 0x64
  else if a = 0x80000054 then some 0x41
  else if a = 0x80000055 then some 0x1
  else if a = 0x80000056 then some 0x82
  else if a = 0x80000057 then some 0x80
  else if a = 0x80000058 then some 0x41
  else if a = 0x80000059 then some 0x11
  else if a = 0x8000005a then some 0x6
  else if a = 0x8000005b then some 0xe4
  else if a = 0x8000005c then some 0x22
  else if a = 0x8000005d then some 0xe0
  else if a = 0x8000005e then some 0x0
  else if a = 0x8000005f then some 0x8
  else if a = 0x80000060 then some 0xf3
  else if a = 0x80000061 then some 0x27
  else if a = 0x80000062 then some 0x0
  else if a = 0x80000063 then some 0x30
  else if a = 0x80000064 then some 0x79
  else if a = 0x80000065 then some 0x77
  else if a = 0x80000066 then some 0x13
  else if a = 0x80000067 then some 0x7
  else if a = 0x80000068 then some 0xf7
  else if a = 0x80000069 then some 0x7f
  else if a = 0x8000006a then some 0xf9
  else if a = 0x8000006b then some 0x8f
  else if a = 0x8000006c then some 0x5
  else if a = 0x8000006d then some 0x67
  else if a = 0x8000006e then some 0x13
  else if a = 0x8000006f then some 0x7
  else if a = 0x80000070 then some 0x7
  else if a = 0x80000071 then some 0x80
  else if a = 0x80000072 then some 0xd9
  else if a = 0x80000073 then some 0x8f
  else if a = 0x80000074 then some 0x73
  else if a = 0x80000075 then some 0x90
  else if a = 0x80000076 then some 0x7
  else if a = 0x80000077 then some 0x30
  else if a = 0x80000078 then some 0x97
  else if a = 0x80000079 then some 0x17
  else if a = 0x8000007a then some 0x0
  else if a = 0x8000007b then some 0x0
  else if a = 0x8000007c then some 0x93
  else if a = 0x8000007d then some 0x87
  else if a = 0x8000007e then some 0xa7
  else if a = 0x8000007f then some 0xe0
  else if a = 0x80000080 then some 0x73
  else if a = 0x80000081 then some 0x90
  else if a = 0x80000082 then some 0x17
  else if a = 0x80000083 then some 0x34
  else if a = 0x80000084 then some 0x81
  else if a = 0x80000085 then some 0x47
  else if a = 0x80000086 then some 0x73
  else if a = 0x80000087 then some 0x90
  else if a = 0x80000088 then some 0x7
  else if a = 0x80000089 then some 0x18
  else if a = 0x8000008a then some 0xc1
  else if a = 0x8000008b then some 0x67
  else if a = 0x8000008c then some 0xfd
  else if a = 0x8000008d then some 0x17
  else if a = 0x8000008e then some 0x73
  else if a = 0x8000008f then some 0x90
  else if a = 0x80000090 then some 0x27
  else if a = 0x80000091 then some 0x30
  else if a = 0x80000092 then some 0x73
  else if a = 0x80000093 then some 0x90
  else if a = 0x80000094 then some 0x37
  else if a = 0x80000095 then some 0x30
  else if a = 0x80000096 then some 0xf3
  else if a = 0x80000097 then some 0x27
  else if a = 0x80000098 then some 0x40
  else if a = 0x80000099 then some 0x10
  else if a = 0x8000009a then some 0x93
  else if a = 0x8000009b then some 0xe7
  else if a = 0x8000009c then some 0x7
  else if a = 0x8000009d then some 0x22
  else if a = 0x8000009e then some 0x73
  else if a = 0x8000009f then some 0x90
  else if a = 0x800000a0 then some 0x47
  else if a = 0x800000a1 then some 0x10
  else if a = 0x800000a2 then some 0xfd
  else if a = 0x800000a3 then some 0x57
  else if a = 0x800000a4 then some 0xa9
  else if a = 0x800000a5 then some 0x83
  else if a = 0x800000a6 then some 0x73
  else if a = 0x800000a7 then some 0x90
  else if a = 0x800000a8 then some 0x7
  else if a = 0x800000a9 then some 0x3b
  else if a = 0x800000aa then some 0xbd
  else if a = 0x800000ab then some 0x47
  else if a = 0x800000ac then some 0x73
  else if a = 0x800000ad then some 0x90
  else if a = 0x800000ae then some 0x7
  else if a = 0x800000af then some 0x3a
  else if a = 0x800000b0 then some 0xef
  else if a = 0x800000b1 then some 0xf0
  else if a = 0x800000b2 then some 0xdf
  else if a = 0x800000b3 then some 0xf6
  else if a = 0x800000b4 then some 0xf3
  else if a = 0x800000b5 then some 0x27
  else if a = 0x800000b6 then some 0x40
  else if a = 0x800000b7 then some 0xf1
  else if a = 0x800000b8 then some 0x81
  else if a = 0x800000b9 then some 0x27
  else if a = 0x800000ba then some 0x3e
  else if a = 0x800000bb then some 0x82
  else if a = 0x800000bc then some 0x73
  else if a = 0x800000bd then some 0x0
  else if a = 0x800000be then some 0x20
  else if a = 0x800000bf then some 0x30
  else some 0#8

/-- Booting-Machine state at the `start` entry (hart 0), with reset CSR values
(`mstatus.SXL/UXL = RV64`, `misa.MXL = RV64`) and a RAM stack. -/
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

def mainAddr : BitVec 64 := 0x80000E82

/-- **`start()` through `mret`, operationally.** 55 real `try_step`s reach `main`
in Supervisor mode. Kernel reduction (large `--tstack`). -/
theorem start_to_main :
    (runSteps 55 σ0).map (fun s => (s.regs Register.PC, s.regs Register.cur_privilege))
      = some (some mainAddr, some Privilege.Supervisor) := by
  with_unfolding_all rfl

/-! ## The WP for execution up to `main` -/

theorem start_isSome : (runSteps 55 σ0).isSome := by
  obtain ⟨σm, h1, _⟩ := Option.map_eq_some_iff.mp start_to_main
  rw [h1]; rfl

/-- The machine state after `start()`. -/
noncomputable def σmain : MState := (runSteps 55 σ0).get start_isSome

theorem run_to_σmain : runSteps 55 σ0 = some σmain := (Option.some_get start_isSome).symm

/-- `σmain` is at `main` in Supervisor mode. -/
theorem σmain_at_main :
    σmain.regs Register.PC = some mainAddr ∧
    σmain.regs Register.cur_privilege = some Privilege.Supervisor := by
  obtain ⟨a, h1, h2⟩ := Option.map_eq_some_iff.mp start_to_main
  have ha : a = σmain := Option.some.inj (h1.symm.trans run_to_σmain)
  subst ha
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

section
variable {GF : BundledGFunctors} {hlc : HasLC} [D : MainGS hlc GF]

/-- **The WP for execution up to `main`.** Owning the whole-machine token at the
`start()` entry, after 55 real `try_step`s the continuation receives the token for
`σmain` — at `main` in Supervisor mode (`σmain_at_main`). -/
theorem wp_start_to_main {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} :
    (machineState σ0 : IProp GF) ⊢
      (▷^[55] (machineState σmain -∗ WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
        WP RiscvExpr.Loop @ s; E {{ Φ }} :=
  wp_run 55 σ0 σmain run_to_σmain

end
end Xv6Iris.Model.KernelStart
