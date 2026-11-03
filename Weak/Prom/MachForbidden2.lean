/-
Weak/Prom: **machine-v2 FORBIDDEN verdicts** (S0-P part (2), milestone 2b) (part 2 of 3).

`mach_<test>_forbidden : ¬ allowedMach <test>`: machine v2 (Machine.lean `validRun`, program half `litStep`) has NO
valid run of the test in which every hart finishes and the condition holds.  Each proof is the kernel evaluating the
checker `forbidMachB` (`Weak/Prom/MachForbid.lean`, sound by `forbidMachB_sound`).  Together with
`mach_<test>_exec` (MachCerts.lean: the test HAS complete valid runs) these are the machine's verdicts on the
FORBIDDEN rows of `Weak/Prom/RefLitmus*.lean`, equal to the reference's `ref_<test>`.
Rows `rng` and `parInc` (value domains with no finite closure) are in MachForbidden4.lean (domain-chain checker).
-/
import Weak.Prom.MachForbid
import Weak.Prom.RefLitmus2

namespace Weak.Prom.Mach.Forbidden

open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref Weak.Prom.Ref.Lit

set_option maxRecDepth 100000

theorem mach_w22F_forbidden : ¬ allowedMach Lit.w22F := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_coWW_forbidden : ¬ allowedMach Lit.coWW := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_coWR0_forbidden : ¬ allowedMach Lit.coWR0 := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_coWR_forbidden : ¬ allowedMach Lit.coWR := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_coRW1_forbidden : ¬ allowedMach Lit.coRW1 := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_coRW2_forbidden : ¬ allowedMach Lit.coRW2 := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_coRR_forbidden : ¬ allowedMach Lit.coRR := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_coRR2_forbidden : ¬ allowedMach Lit.coRR2 := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_isa2F_forbidden : ¬ allowedMach Lit.isa2F := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_wrcF_forbidden : ¬ allowedMach Lit.wrcF := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_iriwF_forbidden : ¬ allowedMach Lit.iriwF := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mix26a_forbidden : ¬ allowedMach Lit.mix26a := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mix26b_forbidden : ¬ allowedMach Lit.mix26b := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mix26c_forbidden : ¬ allowedMach Lit.mix26c := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mix26dNot_forbidden : ¬ allowedMach Lit.mix26dNot := forbidMachB_sound _ 6 (by decide +kernel)

end Weak.Prom.Mach.Forbidden
