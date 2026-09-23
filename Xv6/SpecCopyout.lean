/-
Specifications of `copyout`, `copyin` and `copyinstr` (kernel/vm.c): the
kernel reading or writing a process's memory through its page table,
faulting in lazily allocated pages on the way (`vmfault`, the uncounted
mode).  Each returns `0`, or `-1` after a prefix (a failed fault, a
page without `PTE_W` for copyout, no NUL within `max` for copyinstr).
copyout needs 52 slots, copyin 50, copyinstr 50.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.UMem
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def copyoutAddr : BitVec 64 := KA.«copyout»
def copyinstrAddr : BitVec 64 := KA.«copyinstr»

/-- `copyout(pt a0, psz a1, dstva a2, src a3, len a4)`. -/
def wp_copyout_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8))
    (dqs : DFrac) (bs : List (BitVec 8))
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 52 ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr P.root) (hsz : (k.regs 11#5).toNat ≤ 2 ^ 38)
    (hlen : k.regs 14#5 = BitVec.ofNat 64 bs.length) (hlen' : bs.length < 2 ^ 63) : Prop :=
  kctx cpu k ∗ pcIs cpu copyoutAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPtAt P M ∗ byteBuf (k.regs 13#5) dqs bs ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    byteBuf (k.regs 13#5) dqs bs -∗
    (∃ (P' : UPtd) (M' : Nat → List (BitVec 8)),
      ⌜P.ext P' ∧
        ((R' 10#5 = 0#64 ∧ M' = umemWrite (viewFaulted P P' M) (k.regs 12#5).toNat bs) ∨
         (R' 10#5 = -1#64 ∧ ∃ d, d < bs.length ∧
            M' = umemWrite (viewFaulted P P' M) (k.regs 12#5).toNat (bs.take d)))⌝ ∗
      procPtAt P' M') -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure COPYOUT : Prop where
  wp_copyout : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8)) (dqs : DFrac) (bs : List (BitVec 8))
    hnoff hK hlk hroot hsz hlen hlen',
    wp_copyout_body (hlc := hlc) (GF := GF) cpu k γl γk P M dqs bs hnoff hK hlk hroot hsz hlen hlen'

/-- `copyinstr(pt a0, psz a1, dst a2, srcva a3, max a4)`: the NUL-terminated
string from `srcva` (at most `max` bytes, NUL included) into `dst`. -/
def wp_copyinstr_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8))
    (old : List (BitVec 8))
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 50 ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr P.root) (hsz : (k.regs 11#5).toNat ≤ 2 ^ 38)
    (hmax : k.regs 14#5 = BitVec.ofNat 64 old.length) (hmax' : old.length < 2 ^ 63) : Prop :=
  kctx cpu k ∗ pcIs cpu copyinstrAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPtAt P M ∗ byteBuf (k.regs 12#5) (DFrac.own 1) old ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    (∃ (P' : UPtd) (bs' : List (BitVec 8)),
      ⌜P.ext P' ∧
        ((R' 10#5 = 0#64 ∧ ∃ s, umemStr (viewFaulted P P' M) (k.regs 13#5).toNat old.length = some s ∧
            bs' = s ++ old.drop s.length) ∨
         (R' 10#5 = -1#64 ∧ ∃ d, d ≤ old.length ∧
            bs' = umemRead (viewFaulted P P' M) (k.regs 13#5).toNat d ++ old.drop d))⌝ ∗
      procPtAt P' (viewFaulted P P' M) ∗ byteBuf (k.regs 12#5) (DFrac.own 1) bs') -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure COPYINSTR : Prop where
  wp_copyinstr : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8)) (old : List (BitVec 8))
    hnoff hK hlk hroot hsz hmax hmax',
    wp_copyinstr_body (hlc := hlc) (GF := GF) cpu k γl γk P M old hnoff hK hlk hroot hsz hmax hmax'

end Xv6
