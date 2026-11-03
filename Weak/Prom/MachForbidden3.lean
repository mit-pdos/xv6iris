/-
Weak/Prom: **machine-v2 FORBIDDEN verdicts** (S0-P part (2), milestone 2b) (part 3 of 3).

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

theorem mach_mix26h_forbidden : ¬ allowedMach Lit.mix26h := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mix26i_forbidden : ¬ allowedMach Lit.mix26i := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mpAmoData_forbidden : ¬ allowedMach Lit.mpAmoData := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mpAmoCtrl_forbidden : ¬ allowedMach Lit.mpAmoCtrl := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mixSca_forbidden : ¬ allowedMach Lit.mixSca := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_lrScSc_forbidden : ¬ allowedMach Lit.lrScSc := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_wsub_forbidden : ¬ allowedMach Lit.wsub := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_armWeak_forbidden : ¬ allowedMach Lit.armWeak := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_lbAcq_forbidden : ¬ allowedMach Lit.lbAcq := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_lbRel_forbidden : ¬ allowedMach Lit.lbRel := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_coh_forbidden : ¬ allowedMach Lit.coh := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_seqT_forbidden : ¬ allowedMach Lit.seqT := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_lbfd_forbidden : ¬ allowedMach Lit.lbfd := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_disjLists_forbidden : ¬ allowedMach Lit.disjLists := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_ramAq_forbidden : ¬ allowedMach Lit.ramAq := forbidMachB_sound _ 6 (by decide +kernel)

end Weak.Prom.Mach.Forbidden
