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

THE CHILD INHERITS THE PARENT'S LAZY BIT (Rocq `ProofKforkB6`'s close):
`uvmcopy` maps a child page wherever the parent has one below the break,
so the parent's `lazyFree` claim transfers (`LazyFree.lazyFree_uvmcopy`,
Rocq `lazy_free_dom`); the dormant block allocproc handed out was at
`true`.

THE CHILD'S RECORD is `Xv6/ForkretRecord.lean`'s: `allocproc` leaves the
save area at `[forkret, kstack + PGSIZE, 0 x 12]`, and the creator owes
the slot a parked record before it may release the lock, which is why
`[ForkretIs]` is a premise of `fork` and not of `allocproc`.

`filedup` and `idup` are the assumed NON-BLOCKING file-system entries
(`Xv6/FsEnv.lean`, `FsEntryNB`), so kfork never sleeps: as in Rocq, the
contract is BALANCED and generic in the entry interrupt index
(`wp_kfork_eb_body`: no trap bundle, crossing `k.sie`).  Each of its three
lock windows -- allocproc's `np->lock` (whose arm allocproc hands back),
`wait_lock`, the second `np->lock` -- releases at `reen = k.sie`, paying
back the arm its acquire minted.  The old interrupts-off, trap-bundle-
threading contract `KFORK.wp_kfork` is derived.

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
import Iris.ProofMode

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

/-- Address of `kfork`. -/
def kforkAddr : BitVec 64 := KA.«kfork»

/-- The stack `kfork`'s cone needs: its own 8-slot frame over the deepest
callee, an fs entry point (`allocproc` needs 48, `uvmcopy` 42,
`freeproc` 44). -/
def kforkSlots : Nat := 8 + fsSlots

/-- What `kfork` answered: `-1` (no free slot, no memory), or the child's
pid, which `allocproc` minted in `[1, PIDMAX]`. -/
def kforkAns (rv : BitVec 32) : Prop :=
  rv = -1#32 ∨ (1 ≤ rv.toNat ∧ rv.toNat ≤ PIDMAX)

/-- **WP of `kfork`.** -/
def wp_kfork_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
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

/-- What `kfork` hands back (Rocq `kfork_post`), at whichever hart the
thread returns on: the entry context with some `SPIE`/`SPP` (left
unconstrained, as the interrupts-off contract always stated it), callee-saved
registers, the answer in `a0`, and the caller's block unchanged. -/
def kforkPost {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (k : KCtx) (j : Nat) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) :
    CPU → IProp GF := fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (rv : BitVec 32),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ kforkAns rv⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    procPrivNoctxAt curCtx (procAddr j) pid V M -∗ wpLoop cpu')

/-- **WP of `kfork`, at either entry `SIE`** (Rocq `wp_kfork_sconf_body`:
`cpu_own lvl eb pme b lks` in and out, crossing `wp_next b`).  `kfork` does
not sleep (`filedup`/`idup` are the non-blocking fs entries), so it is
BALANCED: every `acquire` it makes (allocproc's `np->lock`, `wait_lock`,
the second `np->lock`) is paired with a `release` that re-enables
interrupts exactly when the entry had them on, paying back the arm the
acquire minted.  No trap bundle crosses the interface; the crossing is
`k.sie`.  Entered at depth 0 (so, by `KCtx.wf`, no spinlock held). -/
def wp_kfork_eb_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : kforkSlots ≤ k.avail)
    (hnoff : k.noff = 0) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu kforkAddr ∗ procsInv Γ ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗ procsAvail Γ none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext k.sie k.proc cpu (kforkPost k j pid V M)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kfork`. -/
structure KFORK : Prop where
  wp_kfork_eb : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) hj hproc hK hnoff htier,
    wp_kfork_eb_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M
      hj hproc hK hnoff htier

/-- The interrupts-off instance of `wp_kfork_eb`: the hart is pinned, so the
trap bundle frames across the call. -/
theorem KFORK.wp_kfork (A : KFORK) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF]
    [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) hj hproc hK hsie hnoff hlocks htier :
    wp_kfork_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M
      hj hproc hK hsie hnoff hlocks htier := by
  have h := A.wp_kfork_eb (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M hj hproc hK hnoff htier
  unfold wp_kfork_eb_body at h
  unfold wp_kfork_body
  iintro ⟨H0, H1, H2, Htc, Hcl, Hir, H6, H7, H8, H9, H10, H11, Hnext⟩
  iapply h
  iframe H0 H1 H2 H6 H7 H8 H9 H10 H11
  rw [hsie]
  iapply wpNext_off_intro
  unfold kforkPost
  iintro %spie %spp %R' %rv %hpost Hk Hpc Hpriv
  ihave Hn := wpNext_at true k.proc cpu cpu _ (fun _ => rfl) $$ Hnext
  iapply Hn $$ %spie %spp %R' %rv %hpost Hk Hpc Htc Hcl Hir Hpriv

end Xv6
