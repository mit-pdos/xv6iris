/-
Weak/Prom: **machine-v2 FORBIDDEN verdicts** (S0-P part (2), milestone 2b) (part 1 of 3).

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

theorem mach_lbdd_forbidden : ¬ allowedMach Lit.lbdd := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_lbDatas_forbidden : ¬ allowedMach Lit.lbDatas := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_lbCtrls_forbidden : ¬ allowedMach Lit.lbCtrls := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_lbCtrlsBeq_forbidden : ¬ allowedMach Lit.lbCtrlsBeq := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_lbLrsc_forbidden : ¬ allowedMach Lit.lbLrsc := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_oota42_forbidden : ¬ allowedMach Lit.oota42 := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mpFF_forbidden : ¬ allowedMach Lit.mpFF := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mpFFrr_forbidden : ¬ allowedMach Lit.mpFFrr := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mpFAddr_forbidden : ¬ allowedMach Lit.mpFAddr := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mpAmoRlAq_forbidden : ¬ allowedMach Lit.mpAmoRlAq := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_mpFAmo_forbidden : ¬ allowedMach Lit.mpFAmo := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_amoStorePart_forbidden : ¬ allowedMach Lit.amoStorePart := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_sbFF_forbidden : ¬ allowedMach Lit.sbFF := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_datarfi_forbidden : ¬ allowedMach Lit.datarfi := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_addrpo_forbidden : ¬ allowedMach Lit.addrpo := forbidMachB_sound _ 6 (by decide +kernel)

theorem mach_addrpoR_forbidden : ¬ allowedMach Lit.addrpoR := forbidMachB_sound _ 6 (by decide +kernel)

end Weak.Prom.Mach.Forbidden
