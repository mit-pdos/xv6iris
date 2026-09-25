/-
Specification of `devintr` (kernel/trap.c) at a cause that is NOT a
supervisor device interrupt: the dispatcher's third arm.

```
  } else return 0;          // neither the external nor the timer cause
```

`SpecDevintr.DEVINTR` states devintr only at the two causes it handles
(`sCauseOk sc`: kerneltrap's caller, whose trap is always an interrupt, never
reaches the third arm -- its proof calls that arm DEAD).  `usertrap` calls
devintr for EVERY cause but the ecall (`else if ((which_dev = devintr()) !=
0)`), so a page fault or an unexpected exception reaches it too, and there
it returns 0 without touching anything: the scause cell, read and handed
back, and the context's registers.  Rocq's `DEVINTR` states both arms in one
contract; Lean keeps `DEVINTR` as landed and states the third arm here
(deviation: two contracts for one function, recommended merge into
SpecDevintr as a landed edit).

Interrupts off (D28, as `DEVINTR`), any depth and locks (nothing is taken),
devintr's own four-slot frame.

Imports only definitional files and Spec files.
-/
import Xv6.SpecDevintr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- **WP of `devintr` at a non-device cause**: returns 0, the cell and the
callee-saved registers untouched. -/
def wp_devintr_none_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (sc : BitVec 64)
    (hsie : k.sie = false) (hK : 4 ≤ k.avail) (hsc : ¬ sCauseOk sc) : Prop :=
  kctx cpu k ∗ pcIs cpu devintrAddr ∗ Register.scause ↦ᵣ[cpu] sc ∗
  (∀ R' : RegMap, kctx cpu (k.withRegs R') -∗ pcIs cpu (jumpPc (k.regs 1#5)) -∗
    Register.scause ↦ᵣ[cpu] sc -∗ ⌜calleeSaved k.regs R' ∧ R' 10#5 = 0#64⌝ -∗ wpLoop cpu)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `devintr`'s third arm. -/
structure DEVINTR_NONE : Prop where
  wp_devintr_none : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (sc : BitVec 64) hsie hK hsc,
    wp_devintr_none_body (hlc := hlc) (GF := GF) cpu k sc hsie hK hsc

end Xv6
