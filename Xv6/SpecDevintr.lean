/-
Specification of `devintr` (kernel/trap.c), ASSUMED as an interface for
now: the device interrupt dispatcher kerneltrap calls (its cone -- the
PLIC, uartintr, virtio_disk_intr, clockintr -- is not modeled yet).

For a supervisor interrupt (`sCauseOk`): an external interrupt is
claimed, dispatched and completed and `1` returned; a timer interrupt
runs clockintr and returns `2`.  Interrupts are off throughout (the hart
does not move), depth and locks are as at trap entry.
Imports only definitional files.
-/
import Xv6.Image
import Xv6.UartTrace
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `devintr`. -/
def devintrAddr : BitVec 64 := KA.«devintr»

/-- devintr's result for a supervisor interrupt: `1` for an external one,
`2` for the timer. -/
def devintrRet (sc : BitVec 64) : BitVec 64 :=
  if sc = sCause InterruptType.I_S_External then 1#64 else 2#64

theorem devintrRet_ne_zero (sc : BitVec 64) : devintrRet sc ≠ 0#64 := by
  unfold devintrRet; split <;> decide

/-- The stack devintr's cone needs (the Rocq `devintr_stack`). -/
def devintrSlots : Nat := 52

/-- **WP of `devintr`.** -/
def wp_devintr_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (sc : BitVec 64) (dq : DFrac)
    (hsie : k.sie = false) (hnoff : k.noff + 2 < 2 ^ 31) (hlocks : k.locks = [])
    (hK : devintrSlots ≤ k.avail) (hsc : sCauseOk sc) : Prop :=
  kctx cpu k ∗ pcIs cpu devintrAddr ∗ Register.scause ↦ᵣ[cpu]{dq} sc ∗
  (∀ R' : RegMap, kctx cpu (k.withRegs R') -∗ pcIs cpu (jumpPc (k.regs 1#5)) -∗
    Register.scause ↦ᵣ[cpu]{dq} sc -∗ ⌜calleeSaved k.regs R' ∧ R' 10#5 = devintrRet sc⌝ -∗ wpLoop cpu)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `devintr`. -/
structure DEVINTR : Prop where
  wp_devintr : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (sc : BitVec 64) (dq : DFrac) hsie hnoff hlocks hK hsc,
    wp_devintr_body (hlc := hlc) (GF := GF) cpu k sc dq hsie hnoff hlocks hK hsc

end Xv6
