/-
Specification of `freeproc` (kernel/proc.c; static, called with `p->lock`
held from `allocproc`'s failure tails and from `wait`): the trapframe page
and the address space (each if present) returned to the allocator, the
pid cleared under `pid_lock`, the public fields zeroed, the slot UNUSED.
Uncounted.  Needs 44 slots (4 + `proc_freepagetable`'s 40).

PINNED AT INTERRUPTS OFF (`hsie`), and it has to be: the post hands
`procHeld` back, and `procHeld` names the hart the lock is HELD ON, while
`wpNext`'s hart equality holds only under `k.sie = false ∨ k.proc = 0`.
Both callers hold `p->lock`, so interrupts are off on this hart anyway
(the Rocq contract pins the same way).

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

def freeprocAddr : BitVec 64 := KA.«freeproc»
def freeprocSlots : Nat := 44

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]

/-- What `freeproc` takes of the block: the private fields, the slot's
allowances (`dormantAllow`, Rocq `fp_rest`'s `[∗ list] _ ∈ pv_ofile V,
fd_slot ∗ fd_slots FDSPARE ∗ iref_slots (1 + IREFSPARE) ∗ bslots 3`:
freeproc moves none of them, which is what makes its ZOMBIE → UNUSED step a
pass-through for the supplies), the trapframe
page if `trapframe ≠ 0`, the address space if `pagetable ≠ 0`.  The files
are already closed and the cwd dropped (the Rocq `fp_rest`'s two pure
rows): `freeproc` only zeroes cells, so what the UNUSED block it rebuilds
records of `ofile`/`cwd` has to arrive here.  The trapframe page carries
its `pageValid` (Rocq `fp_tf`), which is what `kfree` demands of the
pointer it is handed and which the pagetable arm, when absent, cannot
supply. -/
def freeprocIn (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) : IProp GF := iprop%
  ⌜V.ofile = List.replicate NOFILE 0#64 ∧ V.cwd = 0#64⌝ ∗
  wordPointsTo (pPid pa) 4 pidPriv pid ∗ procFields pa (DFrac.own 1) V ∗
  dormantAllow ∗ stackOwn (V.kstack + 4096#64) 512 ∗
  (if V.trapframe = 0#64 then emp else
    ⌜V.trapframe = pageAddr V.upt.tfp ∧ pageValid V.trapframe⌝ ∗ tfPageAt V.upt.tfp V.tf) ∗
  (if V.pagetable = 0#64 then emp else
    ⌜V.pagetable = pageAddr V.upt.root ∧ V.sz.toNat ≤ uvmMaxsz ∧ umBelow V.sz V.upt⌝ ∗ procPtAt V.upt M)

end

def wp_freeproc_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γl γp : GName) (γk : KmemNames) (j : Nat) (st : BitVec 32) (ch : BitVec 64)
    (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hp : k.regs 10#5 = procAddr j) (hst : st = USED ∨ st = ZOMBIE)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : freeprocSlots ≤ k.avail) (hsie : k.sie = false)
    (hlk : "kmem" ∉ k.locks) (hlp : "nextpid" ∉ k.locks) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu freeprocAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  procHeld Γ cpu j st ch ∗ freeprocIn (procAddr j) pid V M ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    procHeld Γ cpu' j UNUSED 0#64 -∗ procDormant (procAddr j) UNUSED -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure FREEPROC : Prop where
  wp_freeproc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx] (Γ : SchedNames) (cpu : CPU) (k : KCtx)
    (γl γp : GName) (γk : KmemNames) (j : Nat) (st : BitVec 32) (ch : BitVec 64) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) hj hp hst hnoff hK hsie hlk hlp htier,
    wp_freeproc_body (hlc := hlc) (GF := GF) Γ cpu k γl γp γk j st ch pid V M hj hp hst hnoff hK hsie hlk hlp htier

end Xv6
