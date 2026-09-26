/-
Specification of `freewalk` (kernel/vm.c): a leaf-free table's node pages
returned to the allocator, recursively (stated at the level `lvl` of the
node passed, as the recursion needs; the uncounted mode).  Needs
`6 * (lvl + 1) + 14` of the caller's stack slots.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.UPtDefs
import Xv6.Image

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def freewalkAddr : BitVec 64 := KA.«freewalk»
def freewalkSlots (lvl : Nat) : Nat := 6 * (lvl + 1) + 14

def wp_freewalk_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (lvl : Nat) (t : PTree)
    (hlvl : lvl ≤ 2) (hnoff : k.noff + 1 < 2 ^ 31) (hK : freewalkSlots lvl ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr t.base) (hwf : t.wfU lvl) (hnd : t.pagesNodup lvl)
    (hpg : ∀ b ∈ t.pages lvl, pageValid (pageAddr b)) (hnl : t.noLeaves lvl) : Prop :=
  kctx cpu k ∗ pcIs cpu freewalkAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  ptreeOwn lvl (DFrac.own 1) t ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure FREEWALK : Prop where
  wp_freewalk : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (lvl : Nat) (t : PTree) hlvl hnoff hK hlk hroot hwf hnd hpg hnl,
    wp_freewalk_body (hlc := hlc) (GF := GF) cpu k γl γk lvl t hlvl hnoff hK hlk hroot hwf hnd hpg hnl

end Xv6
