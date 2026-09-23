/-
Specification of `kinit` (kernel/kalloc.c): the public contract, stated
once, in the kernel execution context.

`kinit()` initialises `kmem.lock` and frees every page between the end
of the kernel image and `PHYSTOP`.  The caller brings the three words of
`kmem.lock` (whatever they hold), the freelist word (zero, from `.bss`),
and the `kinitPages` whole pages from `PGROUNDUP(end)`; it gets back the
lock (`isLock` on the allocator's payload, born from the words `initlock`
wrote) and the count of free pages.  Stated at either interrupt index
(the exit as `freerange`'s).  The function needs 22 of the caller's stack
slots (its frame of 2, then `freerange`'s 20) and returns them; the
callee-saved registers are preserved.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.KallocDefs
import Xv6.SpecFreerange
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kinit`. -/
def kinitAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«kinit»

/-- `PGROUNDUP(end)`. -/
def kinitBase : BitVec 64 := 0x80024000#64
/-- The pages between `PGROUNDUP(end)` and `PHYSTOP`. -/
def kinitPages : Nat := 32732
/-- The `"kmem"` literal `kinit` names the lock with. -/
def kmemNameAddr : BitVec 64 := 0x80007048#64

/-- The specification of `kinit`. -/
def wp_kinit_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (vlock : BitVec 32) (vname vcpu : BitVec 64)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 22 ≤ k.avail) (hlk : "kmem" ∉ k.locks) : Prop :=
  kctx cpu k ∗ pcIs cpu kinitAddr ∗
  kmapId kmemLockAddr ∗ kmapId (kmemLockAddr + 16#64) ∗
  wordPointsTo kmemLockAddr 4 (DFrac.own 1) vlock ∗
  wordPointsTo (kmemLockAddr + 8#64) 8 (DFrac.own 1) vname ∗
  wordPointsTo (kmemLockAddr + 16#64) 8 (DFrac.own 1) vcpu ∗
  wordPointsTo kmemFreelistAddr 8 (DFrac.own 1) 0#64 ∗
  pageRange kinitBase kinitPages ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ (R' : RegMap) (γl : GName) (γk : KmemNames),
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    isLock γl kmemLockAddr "kmem" (kmemRes γk) -∗ kallocAvail γk (some kinitPages) -∗
    wordPointsTo (kmemLockAddr + 8#64) 8 (DFrac.own 1) kmemNameAddr -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kinit`. -/
structure KINIT : Prop where
  wp_kinit : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (vlock : BitVec 32) (vname vcpu : BitVec 64) hnoff hK hlk,
    wp_kinit_body (hlc := hlc) (GF := GF) cpu k vlock vname vcpu hnoff hK hlk

end Xv6
