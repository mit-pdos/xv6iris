/-
Specification of `push_off` (kernel/spinlock.c):

  flags = rc_sstatus(SSTATUS_SIE); old = !!(flags & SIE);
  if (mycpu()->noff == 0) mycpu()->intena = old;
  mycpu()->noff += 1;

Rocq `SpecPushOff.wp_push_off_sconf_body`.  push_off is one of the two
functions that move the per-cpu bundle across the interrupt-arm seam: at
`sie = true` the `csrrci` flips the arm to `false` and the trap reserve
of the stack becomes usable.  At `sie = false` (the only index the
context layer supports today) nothing moves: the `csrrci` leaves
`sstatus` as it is, `old = 0`, and the exit context is the entry one
with the depth incremented -- `KCtx.pushOff`.  `intena` is left as is:
the write of `old = 0` into `c->intena` at depth 0 agrees with
`KCtx.wf`'s coupling `noff = 0 → sie = intena` (so `intena = false`
there already), and at depth ≥ 1 the cell is not written.  The depth
increment must stay in `int` range (a caller obligation, as in Rocq);
push_off's own frame is 4 slots over mycpu's 2.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.CallConv
import Xv6.KernelText
import Xv6.Geom


namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `push_off`. -/
def pushOffAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«push_off»

/-- **WP of `push_off`.** -/
def wp_push_off_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 6 ≤ k.avail) : Prop :=
  kctx cpu k ∗ kernelText ∗ pcIs cpu pushOffAddr ∗
  (∀ R' : RegMap, kctx cpu (k.pushOff.withRegs R') -∗ pcIs cpu (retPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `push_off`. -/
structure PUSHOFF : Prop where
  wp_push_off : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx] (cpu : CPU) (k : KCtx) hsie htier hnoff hK,
    wp_push_off_body (hlc := hlc) (GF := GF) cpu k hsie htier hnoff hK

end Xv6
