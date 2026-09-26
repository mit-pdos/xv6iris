/-
Specification of `uvmcreate` (kernel/vm.c): an empty user page table
from `kalloc` + `memset`, or `0` when the allocator is dry.  Stated in
either count mode (`on`), generic in SIE.  Needs 18 of the caller's
stack slots.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.Image
import Xv6.KallocDefs
import Xv6.PtOwn

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def uvmcreateAddr : BitVec 64 := KA.«uvmcreate»
def uvmcreateSlots : Nat := 18

/-- `0` with the count dry, or an empty root node one page down. -/
def uvmcreatePost {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (γk : KmemNames) (on : Option Nat) (r : BitVec 64) : IProp GF := iprop%
  (⌜r = 0#64 ∧ availZero on⌝ ∗ kallocAvail γk on) ∨
  (∃ b : BitVec 44, ⌜r = pageAddr b ∧ pageValid (pageAddr b)⌝ ∗
    ptreeOwn 2 (DFrac.own 1) (PTree.zeroNode b) ∗ kallocAvail γk (availDec on))

def wp_uvmcreate_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (on : Option Nat)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : uvmcreateSlots ≤ k.avail) (hlk : "kmem" ∉ k.locks) : Prop :=
  kctx cpu k ∗ pcIs cpu uvmcreateAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk on ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    uvmcreatePost γk on (R' 10#5) -∗ ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure UVMCREATE : Prop where
  wp_uvmcreate : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (on : Option Nat) hnoff hK hlk,
    wp_uvmcreate_body (hlc := hlc) (GF := GF) cpu k γl γk on hnoff hK hlk

end Xv6
