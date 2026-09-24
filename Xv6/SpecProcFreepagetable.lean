/-
Specification of `proc_freepagetable` (kernel/proc.c).
`proc_freepagetable(pt, sz)` unmaps the two fixed pages (the trampoline
and the trapframe) and frees the space (uncounted); needs 40 slots
(`procPagetableSlots`, named in `Xv6/SpecProcPagetable.lean`).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.SchedCtx
import Xv6.PidLock
import Xv6.Image
import Xv6.Geom
import Xv6.SpecProcPagetable

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def procFreepagetableAddr : BitVec 64 := KA.«proc_freepagetable»

def wp_proc_freepagetable_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8))
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : procPagetableSlots ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr P.root) (hsz : (k.regs 11#5).toNat ≤ uvmMaxsz)
    (hbelow : umBelow (k.regs 11#5) P) : Prop :=
  kctx cpu k ∗ pcIs cpu procFreepagetableAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPtAt P M ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure PROC_FREEPAGETABLE : Prop where
  wp_proc_freepagetable : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (P : UPtd) (M : Nat → List (BitVec 8)) hnoff hK hlk hroot hsz hbelow,
    wp_proc_freepagetable_body (hlc := hlc) (GF := GF) cpu k γl γk P M hnoff hK hlk hroot hsz hbelow

end Xv6
