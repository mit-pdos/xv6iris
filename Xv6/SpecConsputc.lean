/-
Specification of `consputc` (kernel/console.c): send one byte to the
console (`uartputc_sync`), under the transmit lock.  Rocq
`SpecConsputc.wp_consputc_sconf_body`: the caller holds the persistent
transmit-lock credential and a sublist witness of the trace; SOME bytes
`cs` are appended to it (another hart may interleave).  `consputc`
acquires `tx_lock` (push_off/pop_off inside), so the depth headroom and
the lock's absence from the held set are caller obligations.  Stack:
consputc's frame over uartputc_sync's (16 slots).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.CallConv
import Xv6.Image
import Xv6.Geom
import Xv6.UartTrace

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `consputc`. -/
def consputcAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«consputc»

/-- **WP of `consputc`.**  The byte in `a0`. -/
def wp_consputc_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γd : UartNames) (bs : List (BitVec 8))
    (hsie : k.sie = false) (hK : 16 ≤ k.avail)
    (hnoff : k.noff + 1 < 2 ^ 31) (huart : "uart" ∉ k.locks) : Prop :=
  kctx cpu k ∗ pcIs cpu consputcAddr ∗ isTxLock γl γd ∗ uartSentSub γd bs ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ (R' : RegMap) (cs : List (BitVec 8)),
    kctx cpu' (k.withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ uartSentSub γd (bs ++ cs) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `consputc`. -/
structure CONSPUTC : Prop where
  wp_consputc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γd : UartNames) (bs : List (BitVec 8)) hsie hK hnoff huart,
    wp_consputc_body (hlc := hlc) (GF := GF) cpu k γl γd bs hsie hK hnoff huart

end Xv6
