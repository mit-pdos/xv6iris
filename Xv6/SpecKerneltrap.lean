/-
Specification of `kerneltrap` (kernel/trap.c): the C handler `kernelvec`
calls, ASSUMED as an interface for now (its proof needs devintr's cone:
the UART and disk interrupt handlers, clockintr, and `yield`).

kerneltrap runs in the handler's context a supervisor interrupt left
(interrupts off, `SPIE = 1`, `SPP = S`, depth 0, no locks; `KCtx.trapped`
below kernelvec's frame) with the trap CSRs, the running proc's claim and
the installed handler (`intrRes`).  It returns to `ra` on WHICHEVER hart
the thread lands on (a timer interrupt yields the thread when there is a
proc), the callee-saved registers preserved, the context the same up to
the registers, `sepc` written back to the trapped pc and `sstatus`
restored, and the arm's cells of the resumed hart in hand.
Imports only definitional files.
-/
import Xv6.Image
import Xv6.UartTrace
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kerneltrap`. -/
def kerneltrapAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«kerneltrap»

/-- The stack kerneltrap and its cone need below kernelvec's 32-slot frame:
the rest of the trap reserve. -/
def ktSlots : Nat := kvFrameSlots - 32

/-- **WP of `kerneltrap`.** -/
def wp_kerneltrap_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (epc sc : BitVec 64)
    (hsie : k.sie = false) (hspie : k.spie = true) (hspp : k.spp = true)
    (hnoff : k.noff = 0) (hlocks : k.locks = []) (hK : ktSlots ≤ k.avail)
    (hsc : sCauseOk sc) (hepc : epc.toNat % 2 = 0) : Prop :=
  kctx cpu k ∗ pcIs cpu kerneltrapAddr ∗ trapCsrsAt cpu epc sc 0#64 ∗ cpuClaim k.proc ∗ intrRes cpu ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (R' : RegMap) (sc' tv' : BitVec 64),
    kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗ trapCsrsAt cpu' epc sc' tv' -∗
    cpuClaim k.proc -∗ intrRes cpu' -∗ ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kerneltrap`. -/
structure KERNELTRAP : Prop where
  wp_kerneltrap : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (epc sc : BitVec 64) hsie hspie hspp hnoff hlocks hK hsc hepc,
    wp_kerneltrap_body (hlc := hlc) (GF := GF) cpu k epc sc hsie hspie hspp hnoff hlocks hK hsc hepc

end Xv6
