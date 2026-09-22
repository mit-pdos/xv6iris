/-
Specification of `kfork` (kernel/proc.c):

    int kfork(void) {
      struct proc *p = myproc();
      if ((np = allocproc()) == 0) return -1;
      if (uvmcopy(p->pagetable, np->pagetable, p->sz) < 0) {
        freeproc(np); release(&np->lock); return -1;
      }
      np->sz = p->sz;
      *(np->trapframe) = *(p->trapframe);
      np->trapframe->a0 = 0;
      for (i = 0; i < NOFILE; i++)
        if (p->ofile[i]) np->ofile[i] = filedup(p->ofile[i]);
      np->cwd = idup(p->cwd);
      safestrcpy(np->name, p->name, sizeof(p->name));
      pid = np->pid;
      release(&np->lock);
      acquire(&wait_lock); np->parent = p; release(&wait_lock);
      acquire(&np->lock); np->state = RUNNABLE; release(&np->lock);
      return pid;
    }

THE PARENT'S BLOCK COMES BACK UNCHANGED: `uvmcopy` reads the parent's
address space and hands it back (`Xv6/SpecUvmcopy.lean` returns
`procPtAt Pold Mold`), the trapframe and `p->name` are only read, and the
parent's `sz`, files and cwd are not touched.  Everything the child gets
-- its block, its kernel stack, its parked record -- goes INTO `procsInv`
before the first `release(&np->lock)`, and nothing of it reaches the
caller: what the caller gets back is a pid.

THE CHILD'S RECORD is `Xv6/ForkretRecord.lean`'s: `allocproc` leaves the
save area at `[forkret, kstack + PGSIZE, 0 x 12]`, and the creator owes
the slot a parked record before it may release the lock, which is why
`[ForkretIs]` is a premise of `fork` and not of `allocproc`.

`filedup` and `idup` are the assumed file-system boundary
(`Xv6/FsEnv.lean`) and both may SLEEP, so the whole call is sleep-shaped:
the thread may park inside them and come back on another hart, and the
trap CSRs, the claim and the installed handler it gets back are that
hart's.

The returned pid is the child's, which `allocproc` minted in `[1, PIDMAX]`.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SchedCtx
import Xv6.WaitLock
import Xv6.PidLock
import Xv6.FsEnv
import Xv6.SpecForkret
import Xv6.SpecAllocproc
import Xv6.ProcAvail
import Xv6.SpecFreeproc
import Xv6.SpecUvmcopy
import Xv6.SpecSleep
import MachCSL.Lock
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kfork`. -/
def kforkAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«kfork»

/-- The stack `kfork`'s cone needs: its own 8-slot frame over the deepest
callee, an fs entry point (`allocproc` needs 48, `uvmcopy` 42,
`freeproc` 44). -/
def kforkSlots : Nat := 8 + fsSlots

/-- What `kfork` answered: `-1` (no free slot, no memory), or the child's
pid, which `allocproc` minted in `[1, PIDMAX]`. -/
def kforkAns (rv : BitVec 32) : Prop :=
  rv = -1#32 ∨ (1 ≤ rv.toNat ∧ rv.toNat ≤ PIDMAX)

/-- **WP of `kfork`.** -/
def wp_kfork_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : kforkSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu kforkAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗ procsAvail Γ none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (rv : BitVec 32),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ kforkAns rv⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    procPrivNoctxAt curCtx (procAddr j) pid V M -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kfork`. -/
structure KFORK : Prop where
  wp_kfork : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) hj hproc hK hsie hnoff hlocks htier,
    wp_kfork_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M
      hj hproc hK hsie hnoff hlocks htier

end Xv6
