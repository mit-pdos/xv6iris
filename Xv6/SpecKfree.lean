/-
Specification of `kfree` (kernel/kalloc.c): the public contract, stated
once, in the kernel execution context.

`kfree(pa)` puts the page at `pa` on the free list.  The caller owns the
page whole (`pageOwn`) and knows it is one of the allocator's
(`pageValid`: the checks `kfree` panics on); the caller's count of the
free pages, if tracked, goes up by one.  The lock is taken and released
inside, so the function is stated at either interrupt index: with
interrupts on at entry, they are on at exit with `spie`/`spp` pinned by
the trap that may have run (as `acquire`'s contract has it).  The
function needs 14 of the caller's stack slots (its frame of 4, then
`acquire`'s 10) and returns them; the callee-saved registers are
preserved.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.KallocDefs
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kfree`. -/
def kfreeAddr : BitVec 64 := KA.«kfree»

/-- The specification of `kfree`, as a proposition over the ambient
kernel context. -/
def wp_kfree_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (on : Option Nat)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 14 ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hp : pageValid (k.regs 10#5)) : Prop :=
  kctx cpu k ∗ pcIs cpu kfreeAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗
  pageOwn (k.regs 10#5) ∗ kallocAvail γk on ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    kallocAvail γk (availInc on) -∗ ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kfree`. -/
structure KFREE : Prop where
  wp_kfree : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (on : Option Nat) hnoff hK hlk hp,
    wp_kfree_body (hlc := hlc) (GF := GF) cpu k γl γk on hnoff hK hlk hp

/-- **`kfree` over a VISIBILITY-FREE page.**  Identical to `wp_kfree_body`
but the caller supplies `pageFree` (reclaimed memory whose per-byte
era-visibility keys are gone) rather than the valued `pageOwn`.  `kfree`
memsets the page (re-minting each byte's key from its own store) before
threading it onto the free list. -/
def wp_kfree_free_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (on : Option Nat)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 14 ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hp : pageValid (k.regs 10#5)) : Prop :=
  kctx cpu k ∗ pcIs cpu kfreeAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗
  pageFree (k.regs 10#5) ∗ kallocAvail γk on ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    kallocAvail γk (availInc on) -∗ ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kfree` over visibility-free pages. -/
structure KFREE_FREE : Prop where
  wp_kfree_free : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (on : Option Nat) hnoff hK hlk hp,
    wp_kfree_free_body (hlc := hlc) (GF := GF) cpu k γl γk on hnoff hK hlk hp


end Xv6
