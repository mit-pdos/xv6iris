/-
Specification of `consoleintr` (kernel/console.c): the console input
handler `uartintr` calls per received byte.  Under `cons.lock` it edits
the ring (kill-line, backspace, or append), echoes through `consputc`, and
wakes readers (`wakeup(&cons.r)`) when a line is complete.

Interrupts are off (the hart stays); the depth headroom covers the nested
acquire of port 0's transmit lock inside `consputc`; `cons`, `proc` and
`uart0` are not held.  The caller holds the console lock credential, port
0's transmit bundle and a sublist witness of its trace (the echo extends it
by some bytes).  Stack: the 6-slot frame over `consputc`'s 20.

Imports only definitional files.
-/
import MachCSL.CallConv
import Xv6.Image
import Xv6.ConsoleDefs
import Xv6.SchedCtx

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `consoleintr`. -/
def consoleintrAddr : BitVec 64 := KA.«consoleintr»

/-- The stack `consoleintr`'s cone needs: its 6-slot frame over `consputc`'s 20. -/
def consoleintrSlots : Nat := 26

/-- **WP of `consoleintr`.**  The byte in `a0`. -/
def wp_consoleintr_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γc γl : GName) (γ : UartNames) (bs : List (BitVec 8))
    (hsie : k.sie = false) (hnoff : k.noff + 2 < 2 ^ 31) (hK : consoleintrSlots ≤ k.avail)
    (hlk : "cons" ∉ k.locks ∧ "proc" ∉ k.locks ∧ "uart0" ∉ k.locks)
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu consoleintrAddr ∗ procsInv Γ ∗
  isConsLock γc ∗ uartPort .uart0 γl γ ∗ uartSentSub γ bs ∗ consLicence ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ (R' : RegMap) (cs : List (BitVec 8)),
    kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ uartSentSub γ (bs ++ cs) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `consoleintr`. -/
structure CONSOLEINTR : Prop where
  wp_consoleintr : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γc γl : GName) (γ : UartNames) (bs : List (BitVec 8))
    hsie hnoff hK hlk htier,
    wp_consoleintr_body (hlc := hlc) (GF := GF) Γ cpu k γc γl γ bs hsie hnoff hK hlk htier

end Xv6
