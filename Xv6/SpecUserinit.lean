/-
Specification of `userinit` (kernel/proc.c), the first process:

    void userinit(void) {
      struct proc *p = allocproc();
      initproc = p;
      p->cwd = namei("/");
      p->state = RUNNABLE;
      release(&p->lock);
    }

BOOT CODE: it runs on the boot hart before any scheduler does, so there
is no process on this hart (`k.proc = 0`), no claim and no parking.  Both
of its callees are fine with that -- `allocproc` never calls `myproc` and
is generic in the interrupt index, and `namei` is taken at the boot arm of
the file-system boundary (`Xv6.FsEnv.wp_boot_blocking_body`: at boot there
is nothing to sleep on).

INTERRUPTS ARE OFF (`hsie : k.sie = false`): `main` runs the whole of boot
at `SIE = 0` (it is `scheduler` that first enables them).  The hypothesis is
REQUIRED, not cosmetic: `userinit`'s closing `release` is the pop of the
push_off `allocproc`'s last `acquire` did, and at `SIE = 1` that pop has to
hand the trap resources back (`popArm`/`sieArm`) -- but `allocproc`'s
success arm returns its context at `pushOffAt` (interrupts off) without
returning the arm, so a caller at `SIE = 1` cannot re-enable them.  Drop
this hypothesis only together with an `allocproc` post that hands
`sieArm cpu' k.sie k.proc` back on the success arm.

IT PUBLISHES `initproc`.  The word at `&initproc` is written exactly once,
here, and read forever after (`kexit`'s "init exiting" check, `reparent`'s
target), so `userinit` takes it owned and gives it back DISCARDED, as the
persistent `initprocIs` every later reader takes as a premise.

COUNTED: `allocproc` needs a trapframe page and up to
`procPagetableNodes` table nodes, so the caller lends `kallocAvail γk
(some nb)` with `nb` over that bound and gets back what is left; and it
needs a FREE SLOT, which it does not check for, so the caller lends the
proc table's counted regime `procsAvail Γ (some (np + 1))`
(`Xv6/ProcAvail.lean`) -- the only thing that can refute `allocproc`'s
empty-table arm -- and gets back `procsAvail Γ (some np)`.  The
whole of the first process -- its block, its kernel stack, its parked
`forkret` record (`Xv6/ForkretRecord.lean`, whence `[ForkretIs]`) -- goes
into `procsInv` at the closing `release`, and the slot is left RUNNABLE
for the first scheduler that looks.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SchedCtx
import Xv6.WaitLock
import Xv6.PidLock
import Xv6.FsEnv
import Xv6.SpecForkret
import Xv6.SpecAllocproc
import Xv6.ProcAvail
import MachCSL.Lock
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `userinit`. -/
def userinitAddr : BitVec 64 := KA.«userinit»

/-- The stack `userinit`'s cone needs: its own 4-slot frame over `namei`'s
(`allocproc` needs 48). -/
def userinitSlots : Nat := 4 + fsSlots

/-- **WP of `userinit`.** -/
def wp_userinit_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γp γl : GName) (γk : KmemNames) (nb np : Nat)
    (hnoff : k.noff + 2 < 2 ^ 31) (hnoff0 : k.noff = 0) (hK : userinitSlots ≤ k.avail)
    (hlk : "kmem" ∉ k.locks) (hlp : "nextpid" ∉ k.locks) (hlq : "proc" ∉ k.locks)
    (hlocks : k.locks = []) (htier : k.tier = KTier.kpt) (hproc : k.proc = 0#64)
    (hsie : k.sie = false) (hnb : procPagetableNodes + 1 < nb) : Prop :=
  kctx cpu k ∗ pcIs cpu userinitAddr ∗ procsInv Γ ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ isLock γp pidLockAddr "nextpid" pidLockPay ∗
  kallocAvail γk (some nb) ∗ procsAvail Γ (some (np + 1)) ∗
  (∃ w : BitVec 64, wordPointsTo initprocAddr 8 (DFrac.own 1) w) ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (ip : BitVec 64)
    (g : Nat),
    ⌜(k.sie = false → spie = k.spie ∧ spp = k.spp) ∧ calleeSaved k.regs R' ∧
      g ≤ procPagetableNodes + 1 ∧ ∃ i : Nat, i < NPROC ∧ ip = procAddr i⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    initprocIs ip -∗ kallocAvail γk (availSub (some nb) g) -∗ procsAvail Γ (some np) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `userinit`. -/
structure USERINIT : Prop where
  wp_userinit : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γp γl : GName) (γk : KmemNames) (nb np : Nat)
    hnoff hnoff0 hK hlk hlp hlq hlocks htier hproc hsie hnb,
    wp_userinit_body (hlc := hlc) (GF := GF) Γ cpu k γp γl γk nb np
      hnoff hnoff0 hK hlk hlp hlq hlocks htier hproc hsie hnb

end Xv6
