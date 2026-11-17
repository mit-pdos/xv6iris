/-
Weak/Mini: the reference's well-formedness implies the machine's (P1 gate fix 4).

`MProg.wf` (Ref.lean §5, the scope of E1: a RISC-V size, aligned image, targets inside the texts, registers `< 32`)
implies `Mach.progWf` (Mach.lean §0, the scope of E2: a positive size, aligned image), so every program E1 covers is
also covered by E2.
Imports: only `Weak.Mini.Ref` and `Weak.Mini.Mach` (plan §2 import discipline).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Ref
import Weak.Mini.Mach

namespace Weak.Mini

theorem MProg.wf_progWf {P : MProg} (hwf : P.wf) : Mach.progWf P := ⟨hwf.sz_pos, hwf.2.1⟩

end Weak.Mini
