/-
Specification of `kexit` (kernel/proc.c), the thread's last call:

    void kexit(int status) {
      struct proc *p = myproc();
      if (p == initproc) panic("init exiting");
      for (fd = 0; fd < NOFILE; fd++)
        if (p->ofile[fd]) { fileclose(p->ofile[fd]); p->ofile[fd] = 0; }
      begin_op(); iput(p->cwd); end_op(); p->cwd = 0;
      acquire(&wait_lock);
      reparent(p);
      wakeup(p->parent);
      acquire(&p->lock);
      p->xstate = status;
      p->state = ZOMBIE;
      release(&wait_lock);
      sched();
      unreachable("zombie exit");
    }

IT DOES NOT RETURN: the contract has NO continuation.  `sched()` parks the
thread at ZOMBIE, and `needsCtx ZOMBIE` is false, so `wp_sched_body`'s
post-resume half is `emp` -- nobody can ever resume this record, which is
what makes the `unreachable` after the call dead code rather than an arm
to discharge.  What the thread owes the slot at that park is
`procDormantNoctx` (`parkPay` at a dormant state): its private block minus
the save area -- which is why the ofile loop and `p->cwd = 0` are not
bookkeeping but the payment (`procDormant` demands `ofile = 0 x 16` and
`cwd = 0`) -- TOGETHER WITH THE WHOLE KERNEL STACK.

Hence the STACK CLOSER premise.  A dormant slot owns all 512 slots below
`p->kstack + PGSIZE` (nobody runs on them any more), but the exiting
thread is standing on them: it owns only the region below its own `sp`.
The frames above `sp` belong to its callers, so the closer is what the
caller hands over when it calls the function that never returns -- and
`kexit` uses it exactly once, at the park.

`initproc` may not exit (the C panics); the premise `procAddr j ≠ ip`
against the published `initprocIs` is what rules that branch out.

`fileclose`, `begin_op`, `iput` and `end_op` are the assumed file-system
boundary (`Xv6/FsEnv.lean`), every one of them sleep-shaped.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SchedCtx
import Xv6.WaitLock
import Xv6.FsEnv
import Xv6.SpecSched
import Xv6.SpecReparent
import MachCSL.Lock
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kexit`. -/
def kexitAddr : BitVec 64 := KA.«kexit»

/-- The stack `kexit`'s cone needs: its own 6-slot frame over the deepest
callee, an fs entry point (`reparent` needs 24, `sched` 16). -/
def kexitSlots : Nat := 6 + fsSlots

/-- **WP of `kexit`**: no continuation -- the thread parks as a ZOMBIE and
is never resumed. -/
def wp_kexit_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv]
    (cpu : CPU) (k : KCtx) (γw : GName) (j : Nat) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (ip : BitVec 64)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : kexitSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) (hinit : procAddr j ≠ ip) : Prop :=
  kctx cpu k ∗ pcIs cpu kexitAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗ initprocIs ip ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  (stackOwn k.sp k.avail -∗ stackOwn (V.kstack + 4096#64) 512)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kexit`. -/
structure KEXIT : Prop where
  wp_kexit : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv]
    (cpu : CPU) (k : KCtx) (γw : GName) (j : Nat) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (ip : BitVec 64) hj hproc hK hsie hnoff hlocks htier hinit,
    wp_kexit_body (hlc := hlc) (GF := GF) Γ cpu k γw j pid V M ip
      hj hproc hK hsie hnoff hlocks htier hinit

end Xv6
