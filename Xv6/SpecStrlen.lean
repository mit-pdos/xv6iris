/-
Specification of `strlen` (kernel/string.c): the public contract, stated
once, in the kernel execution context.

`strlen(s)` returns the number of bytes before the first zero byte of the
string at `s`.  The caller owns the buffer `bs` at `s` (any fraction),
which holds a C string of length `n`: bytes `0..n-1` nonzero, byte `n`
zero.  The function needs two of the caller's stack slots (its frame) and
returns them; `a0 = n` on return, the callee-saved registers and the
buffer are preserved, and control returns to `ra` (bit 0 cleared).
`n < 2^31`: the length is a C `int`.

Present limits of the context layer: interrupts off and the Bare tier
(hypotheses, to be dropped when the interrupt engine and page-table fetch
exist).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.KernelText
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `strlen`. -/
def strlenAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«strlen»

/-- `bs` holds a C string of length `n`: bytes `0..n-1` nonzero, byte `n` zero. -/
def cstrAt (bs : List (BitVec 8)) (n : Nat) : Prop :=
  (∀ j, j < n → ∃ b, bs[j]? = some b ∧ b ≠ 0#8) ∧ bs[n]? = some 0#8

/-- **WP of `strlen`.** -/
def wp_strlen_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (bs : List (BitVec 8)) (n : Nat) (dq : DFrac)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 2 ≤ k.avail)
    (hcstr : cstrAt bs n) (hn31 : n < 2 ^ 31) (hbuf : inRam (k.regs 10#5) bs.length) : Prop :=
  kctx cpu k ∗ kernelText ∗ pcIs cpu strlenAddr ∗ byteBuf (k.regs 10#5) dq bs ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
    kctx cpu' (k.withRegs R') -∗ pcIs cpu' (retPc (k.regs 1#5)) -∗
    byteBuf (k.regs 10#5) dq bs -∗
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.ofNat 64 n⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `strlen`. -/
structure STRLEN : Prop where
  wp_strlen : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (bs : List (BitVec 8)) (n : Nat) (dq : DFrac) hsie htier hK hcstr hn31 hbuf,
    wp_strlen_body (hlc := hlc) (GF := GF) cpu k bs n dq hsie htier hK hcstr hn31 hbuf

end Xv6
