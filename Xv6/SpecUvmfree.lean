/-
Specification of `uvmfree` (kernel/vm.c): the user pages of a table
whose only leaves are user leaves (the fixed mappings already unmapped)
freed, then the table itself (uncounted mode).  Needs 36 slots.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.UPtDefs
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def uvmfreeAddr : BitVec 64 := KA.«uvmfree»
def uvmfreeSlots : Nat := 36

def wp_uvmfree_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8))
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : uvmfreeSlots ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr P.root) (hsz : (k.regs 11#5).toNat ≤ uvmMaxsz)
    (hwf : uptWf P) (hbelow : umBelow (k.regs 11#5) P) : Prop :=
  kctx cpu k ∗ pcIs cpu uvmfreeAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  ptOwnRep P.root P.um ∗ umPages P M ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure UVMFREE : Prop where
  wp_uvmfree : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8)) hnoff hK hlk hroot hsz hwf hbelow,
    wp_uvmfree_body (hlc := hlc) (GF := GF) cpu k γl γk P M hnoff hK hlk hroot hsz hwf hbelow

end Xv6
