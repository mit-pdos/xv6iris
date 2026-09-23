/-
Specifications of `proc_pagetable` and `proc_freepagetable` (kernel/proc.c).
`proc_pagetable(p)` builds an empty user table with the trampoline and the
process's trapframe page mapped (3 nodes), or returns `0` (the failure
tails free what was built and the count is then unknown).  Needs 40
slots.  `proc_freepagetable(pt, sz)` unmaps the two fixed pages and frees
the space (uncounted); needs 40 slots.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.SchedCtx
import Xv6.PidLock
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def procPagetableAddr : BitVec 64 := KA.«proc_pagetable»
def procFreepagetableAddr : BitVec 64 := KA.«proc_freepagetable»
def procPagetableSlots : Nat := 40
/-- The nodes of a fresh table (root and the two nodes of the top page's path). -/
def procPagetableNodes : Nat := 3

/-- `proc_pagetable`'s result: the space `⟨root, tfp, ∅⟩` at `root`, or `0`. -/
def pptPost {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (γk : KmemNames) (on : Option Nat) (tfp : BitVec 44) (r : BitVec 64) : IProp GF := iprop%
  (∃ (root : BitVec 44) (M : Nat → List (BitVec 8)),
    ⌜r = pageAddr root⌝ ∗ procPtAt ⟨root, tfp, ∅⟩ M ∗ kallocAvail γk (availSub on procPagetableNodes)) ∨
  (⌜r = 0#64 ∧ ∃ n, n ≤ procPagetableNodes ∧ availZero (availSub on n)⌝ ∗ kallocAvail γk none)

def wp_proc_pagetable_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (on : Option Nat) (tf : BitVec 64) (dq : DFrac)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : procPagetableSlots ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (htf : tf &&& 0xfff#64 = 0#64) (htfv : pageValid tf) : Prop :=
  kctx cpu k ∗ pcIs cpu procPagetableAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk on ∗
  wordPointsTo (pTrapframe (k.regs 10#5)) 8 dq tf ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    wordPointsTo (pTrapframe (k.regs 10#5)) 8 dq tf -∗
    pptPost γk on (BitVec.extractLsb' 12 44 tf) (R' 10#5) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure PROC_PAGETABLE : Prop where
  wp_proc_pagetable : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (on : Option Nat) (tf : BitVec 64) (dq : DFrac) hnoff hK hlk htf htfv,
    wp_proc_pagetable_body (hlc := hlc) (GF := GF) cpu k γl γk on tf dq hnoff hK hlk htf htfv

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
