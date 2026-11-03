/-
Weak/Prom: **machine-v2 FORBIDDEN verdicts** (S0-P part (2), milestone 2b) (part 4 of 4: the domain-chain checker).

`rng` (row 60, `x := y + 1` loop) and `parInc` (row 23, two `amoadd`) have value domains with no finite closure, so the
closed-domain checker `forbidMachB` does not apply; `forbidChainB` (MachForbid.lean, sound by `forbidChainB_sound`:
NOTA in depth form, `D_t` after `t` closure rounds, with `|M| ≤ Σ |prog|`) does.
-/
import Weak.Prom.MachForbid
import Weak.Prom.RefLitmus2

namespace Weak.Prom.Mach.Forbidden

open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref Weak.Prom.Ref.Lit

set_option maxRecDepth 100000

theorem mach_rng_forbidden : ¬ allowedMach Lit.rng := forbidChainB_sound _ (by decide +kernel)

theorem mach_parInc_forbidden : ¬ allowedMach Lit.parInc := forbidChainB_sound _ (by decide +kernel)

end Weak.Prom.Mach.Forbidden
