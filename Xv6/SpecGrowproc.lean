/-
Specification of `growproc` (kernel/proc.c): the running process's size
grown (`uvmalloc`, refused above `TRAPFRAME` or when the allocator is
dry, `-1`) or shrunk (`uvmdealloc`), `p->sz` updated.  Uncounted; needs
46 slots (4 + `uvmalloc`'s 42).

The block is `procPrivNoctxAt curCtx` (Rocq `ProcInv.proc_priv`: the
running process's private block WITHOUT the 14 context words, which the
lock's RUNNING arm owns) -- the same block the current-process syscalls
(`sys_sbrk`, its one caller) hold.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.SchedCtx
import Xv6.SpecUvmalloc
import Xv6.PidLock
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def growprocAddr : BitVec 64 := KA.«growproc»
def growprocSlots : Nat := 46

/-- The size and space after `growproc(n)` with result `r`. -/
def growprocOk (V V' : ProcPriv) (M M' : Nat → List (BitVec 8)) (n r : BitVec 64) : Prop :=
  let sz := V.sz
  let nz : Int := n.toInt
  (nz = 0 → r = 0#64 ∧ V' = V ∧ M' = M) ∧
  (0 < nz → ((r = -1#64 ∧ V' = V ∧ M' = M) ∨
    (r = 0#64 ∧ (sz.toNat + nz.toNat) ≤ uvmMaxsz ∧
      V' = { V with sz := sz + n, upt := V'.upt } ∧ uvmallocOk V.upt V'.upt M M' sz (sz + n) PTE_W))) ∧
  (nz < 0 → r = 0#64 ∧
    V' = { V with sz := uvmdRsz sz (sz + n),
                  upt := V.upt.delRun (pgRoundUpN (sz + n).toNat / 4096) (uvmdNp sz (sz + n)) } ∧ M' = M)

def wp_growproc_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hproc : k.proc = procAddr j)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : growprocSlots ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu growprocAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    (∃ (V' : ProcPriv) (M' : Nat → List (BitVec 8)),
      ⌜growprocOk V V' M M' (k.regs 10#5) (R' 10#5)⌝ ∗ procPrivNoctxAt curCtx (procAddr j) pid V' M') -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure GROWPROC : Prop where
  wp_growproc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8))
    hj hproc hnoff hK hlk htier,
    wp_growproc_body (hlc := hlc) (GF := GF) cpu k γl γk j pid V M hj hproc hnoff hK hlk htier

end Xv6
