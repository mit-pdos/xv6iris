/-
Specification of `kalloc` (kernel/kalloc.c): the public contract, stated
once, in the kernel execution context.

`kalloc()` takes a page off the free list, fills it with `5`s and returns
it, or returns `0` when the list is empty.  A caller tracking the count of
free pages (`kallocAvail γk (some n)`) gets a page whenever `n ≠ 0`
(`kallocPost`); a caller who is not gets a page or `0`.  The lock is taken
and released inside, so the function is stated at either interrupt index
(the exit as `kfree`'s).  The function needs 14 of the caller's stack slots
(its frame of 4, then `acquire`'s 10) and returns them; the callee-saved
registers are preserved.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.KallocDefs
import Xv6.Image

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kalloc`. -/
def kallocAddr : BitVec 64 := KA.«kalloc»

/-- What `kalloc` returns in `a0`: `0` only if the count, if tracked, was
zero; otherwise a valid page filled with `5`s, the count down by one. -/
def kallocPost {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (γk : KmemNames) (on : Option Nat) (r : BitVec 64) : IProp GF := iprop%
  (⌜r = 0#64 ∧ availZero on⌝ ∗ kallocAvail γk on) ∨
  (⌜pageValid r⌝ ∗ byteBuf r (DFrac.own 1) (List.replicate 4096 5#8) ∗ kallocAvail γk (availDec on))

/-- The specification of `kalloc`, as a proposition over the ambient
kernel context. -/
def wp_kalloc_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (on : Option Nat)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 14 ≤ k.avail) (hlk : "kmem" ∉ k.locks) : Prop :=
  kctx cpu k ∗ pcIs cpu kallocAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗
  kallocAvail γk on ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    kallocPost γk on (R' 10#5) -∗ ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kalloc`. -/
structure KALLOC : Prop where
  wp_kalloc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (on : Option Nat) hnoff hK hlk,
    wp_kalloc_body (hlc := hlc) (GF := GF) cpu k γl γk on hnoff hK hlk

end Xv6
