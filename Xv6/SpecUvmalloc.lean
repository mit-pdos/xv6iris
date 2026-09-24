/-
Specification of `uvmalloc` (kernel/vm.c), over an address space
(uncounted mode).  `uvmalloc(pt, oldsz, newsz, xperm)` maps zeroed pages
from `PGROUNDUP(oldsz)` to `newsz` at `PTE_R|PTE_U|xperm`, or fails with
`0` leaving the space as it was; needs 42 slots.

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

def uvmallocAddr : BitVec 64 := KA.«uvmalloc»
def uvmallocSlots : Nat := 42

/-- The first vpn of the run `uvmalloc` maps. -/
def uvmaVpn0 (oldsz : BitVec 64) : Nat := pgRoundUpN oldsz.toNat / 4096

/-- `uvmalloc`'s success: the run mapped to fresh zeroed pages. -/
def uvmallocOk (P P' : UPtd) (M M' : Nat → List (BitVec 8)) (oldsz newsz xperm : BitVec 64) : Prop :=
  P.ext P' ∧
  (∀ k, ¬ (uvmaVpn0 oldsz ≤ k ∧ k < uvmaVpn0 oldsz + uvmaNp oldsz newsz) →
    Iris.Std.PartialMap.get? P'.um k = Iris.Std.PartialMap.get? P.um k ∧ M' k = M k) ∧
  (∀ i, i < uvmaNp oldsz newsz →
    (∃ r : BitVec 64, pageValid r ∧
      Iris.Std.PartialMap.get? P'.um (uvmaVpn0 oldsz + i) = some (uLeaf (BitVec.extractLsb' 12 44 r) (xperm ||| PTE_R ||| PTE_U))) ∧
    M' (uvmaVpn0 oldsz + i) = List.replicate 4096 0#8)

def wp_uvmalloc_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8))
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : uvmallocSlots ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr P.root)
    (hold : (k.regs 11#5).toNat ≤ uvmMaxsz) (hnew : (k.regs 12#5).toNat ≤ uvmMaxsz)
    (hperm : k.regs 13#5 &&& ~~~0x3EE#64 = 0#64)
    (hfree : ∀ i, i < uvmaNp (k.regs 11#5) (k.regs 12#5) →
      Iris.Std.PartialMap.get? P.um (uvmaVpn0 (k.regs 11#5) + i) = none) : Prop :=
  kctx cpu k ∗ pcIs cpu uvmallocAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPtAt P M ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ((⌜R' 10#5 = 0#64⌝ ∗ procPtAt P M) ∨
     (∃ (P' : UPtd) (M' : Nat → List (BitVec 8)),
        ⌜uvmallocOk P P' M M' (k.regs 11#5) (k.regs 12#5) (k.regs 13#5) ∧
          R' 10#5 = (if (k.regs 12#5).toNat < (k.regs 11#5).toNat then k.regs 11#5 else k.regs 12#5)⌝ ∗
        procPtAt P' M')) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure UVMALLOC : Prop where
  wp_uvmalloc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8)) hnoff hK hlk hroot hold hnew hperm hfree,
    wp_uvmalloc_body (hlc := hlc) (GF := GF) cpu k γl γk P M hnoff hK hlk hroot hold hnew hperm hfree

end Xv6
