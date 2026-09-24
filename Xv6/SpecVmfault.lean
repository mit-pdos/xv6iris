/-
Specification of `vmfault` (kernel/vm.c), over an address space.
`vmfault(pt, psz, va, read)` lazily maps a zeroed page at
`PGROUNDDOWN(va)` when `va < psz` and it is unmapped, returning the page,
else `0` (uncounted mode; needs 38 slots).

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

def vmfaultAddr : BitVec 64 := KA.«vmfault»
def vmfaultSlots : Nat := 38

def wp_vmfault_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8))
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : vmfaultSlots ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr P.root) (hsz : (k.regs 11#5).toNat ≤ 2 ^ 38) : Prop :=
  kctx cpu k ∗ pcIs cpu vmfaultAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPtAt P M ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ((⌜R' 10#5 = 0#64⌝ ∗ procPtAt P M) ∨
     (∃ r : BitVec 64,
        ⌜R' 10#5 = r ∧ pageValid r ∧ (k.regs 12#5).toNat < (k.regs 11#5).toNat ∧
          Iris.Std.PartialMap.get? P.um (vpnOf (k.regs 12#5)).toNat = none⌝ ∗
        procPtAt (P.insertLeaf (vpnOf (k.regs 12#5)).toNat r (PTE_W ||| PTE_U ||| PTE_R))
          (viewZero M (vpnOf (k.regs 12#5)).toNat))) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure VMFAULT : Prop where
  wp_vmfault : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8)) hnoff hK hlk hroot hsz,
    wp_vmfault_body (hlc := hlc) (GF := GF) cpu k γl γk P M hnoff hK hlk hroot hsz

end Xv6
