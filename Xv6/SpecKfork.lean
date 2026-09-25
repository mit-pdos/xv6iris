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

`filedup` and `idup` are the REAL non-blocking file-system callees (wave 7
W7-C retired the assumed `FsEnv` boundary; Rocq `LinkKfork.v`'s functor
line `KforkProof Myproc AllocprocGen Uvmcopy Freeproc Release Acquire
Filedup Idup Safestrcpy`), so kfork never sleeps: as in Rocq, the contract
is BALANCED and generic in the entry interrupt index (`wp_kfork_eb_body`: no
trap bundle, crossing `k.sie`).  Each of its three lock windows --
allocproc's `np->lock` (whose arm allocproc hands back), `wait_lock`, the
second `np->lock` -- releases at `reen = k.sie`, paying back the arm its
acquire minted.  The old interrupts-off, trap-bundle-threading contract
`KFORK.wp_kfork` is derived.

THE PARENT'S BLOCK IS ROCQ'S WHOLE `proc_priv` (`procPrivFd`, the core with
`p->cwd`'s reference, and the descriptor array with its payloads) BESIDE ITS
FRAGMENT BUNDLE `fdFrags V.fdg stsP` (Rocq `fd_frags (pv_fdg) stsP`), and
BOTH COME BACK VERBATIM: kfork reads every slot of `p->ofile` and writes
none.  The copy loop halves each open descriptor's reference (`filedup`) and
the cwd's (`idup`); the parent keeps one half of each, the child the other.
The file-system rows are Rocq's: `isFtable` (filedup's lock), and idup's
`isItable2` / `itableInv` / `iregInv` at the ambient names.  Rocq's
`printk_env` (for filedup's `panic`) has no Lean counterpart: the Lean
filedup contract refutes its panic without it.

The returned pid is the child's, which `allocproc` minted in `[1, PIDMAX]`.

THE CHILD'S SUPPLY ALLOWANCES (`dormantAllow`, wave 7 P3) come out of
`allocproc`.  On the failure tails they go straight back to `freeproc`
(`freeprocIn`).  On success the child SPENDS them as Rocq's does: each open
descriptor's `fd_slot` on its `filedup` (the others stay in the child's
null slots), the cwd's `iref_slot` on `idup`; the rest (`liveAllow`:
`fdSlots FDSPARE ∗ irefSlots IREFSPARE ∗ bslots 3`) is PARKED with the child
(`ForkretRecord.newbornPay`).  The child's file table is built at a fresh
descriptor ghost (`fdSt_alloc`), each descriptor retyped to the parent's
state.

PROCESS-LAYER DEVIATIONS (flagged):
1. The child's descriptor ghost is minted by kfork at the copy loop, not by
   allocproc (Rocq `proc_dormant_unused` / allocproc's post: Lean's
   allocproc returns the fd-free block `procPriv`).
2. The child's file table, fragment bundle and cwd reference are DROPPED at
   the park (see `SpecForkret`'s deviation: no `CtxMorph` for the file-layer
   predicates yet); Rocq parks the whole `proc_priv`.
3. The D8 generation machinery (the child's generation `Q` / `child_tok`,
   `ch_frag`, `first_tok`, the kill wand, `uslot` / `park_world` /
   `park_token`) is not yet in the contract.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SchedCtx
import Xv6.WaitLock
import Xv6.PidLock
import Xv6.SpecForkret
import Xv6.SpecFiledup
import Xv6.SpecIdup
import Xv6.FdTable
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

/-- The stack `kfork`'s cone needs (Rocq `K_kfork = 56`): its own 8-slot
frame over the deepest callee, `allocproc` (48; `uvmcopy` 42, `freeproc` 44,
`filedup` / `idup` 14 apiece, acquire/release 10, safestrcpy 2). -/
def kforkSlots : Nat := 8 + allocprocSlots

theorem kforkSlots_eq : kforkSlots = 56 := by decide

/-- What `kfork` answered: `-1` (no free slot, no memory), or the child's
pid, which `allocproc` minted in `[1, PIDMAX]`. -/
def kforkAns (rv : BitVec 32) : Prop :=
  rv = -1#32 ∨ (1 ≤ rv.toNat ∧ rv.toNat ≤ PIDMAX)

/-- **WP of `kfork`.** -/
def wp_kfork_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (γft : GName) (γ : FileNames)
    (j : Nat) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (stsP : List FdState)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : kforkSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu kforkAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗ procsAvail Γ none ∗
  isFtable γft γ ∗
  isItable2 fscItlock fscIc fscFs fscIreg fscCov fscLogst icfgNib icfgDev ∗
  itableInv (hlc := hlc) ∗ iregInv (hlc := hlc) fscIreg fscFs icfgIst icfgNib ∗
  procPrivFd γ (procAddr j) pid V M ∗ fdFrags V.fdg stsP ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (rv : BitVec 32),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ kforkAns rv⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    procPrivFd γ (procAddr j) pid V M -∗ fdFrags V.fdg stsP -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- What `kfork` hands back, over an abstract returned bundle `B`: at
whichever hart the thread returns on, the entry context with some
`SPIE`/`SPP` (left unconstrained, as the interrupts-off contract always
stated it), callee-saved registers, the answer in `a0`, and `B`. -/
def kforkPostB {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (k : KCtx) (B : IProp GF) : CPU → IProp GF := fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (rv : BitVec 32),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ kforkAns rv⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    B -∗ wpLoop cpu')

/-- What `kfork` hands back (Rocq `kfork_post`): the caller's block and its
descriptor states, VERBATIM (kfork only reads them). -/
def kforkPost {hlc : HasLC} {GF : BundledGFunctors}
    [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]
    (k : KCtx) (γ : FileNames) (j : Nat) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8))
    (stsP : List FdState) : CPU → IProp GF :=
  kforkPostB k iprop(procPrivFd γ (procAddr j) pid V M ∗ fdFrags V.fdg stsP)

/-- **WP of `kfork`, at either entry `SIE`** (Rocq `wp_kfork_sconf_body`:
`cpu_own lvl eb pme b lks` in and out, crossing `wp_next b`).  `kfork` does
not sleep (`filedup`/`idup` are the non-blocking fs entries), so it is
BALANCED: every `acquire` it makes (allocproc's `np->lock`, `wait_lock`,
the second `np->lock`) is paired with a `release` that re-enables
interrupts exactly when the entry had them on, paying back the arm the
acquire minted.  No trap bundle crosses the interface; the crossing is
`k.sie`.  Entered at depth 0 (so, by `KCtx.wf`, no spinlock held). -/
def wp_kfork_eb_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (γft : GName) (γ : FileNames)
    (j : Nat) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (stsP : List FdState)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : kforkSlots ≤ k.avail)
    (hnoff : k.noff = 0) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu kforkAddr ∗ procsInv Γ ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗ procsAvail Γ none ∗
  isFtable γft γ ∗
  isItable2 fscItlock fscIc fscFs fscIreg fscCov fscLogst icfgNib icfgDev ∗
  itableInv (hlc := hlc) ∗ iregInv (hlc := hlc) fscIreg fscFs icfgIst icfgNib ∗
  procPrivFd γ (procAddr j) pid V M ∗ fdFrags V.fdg stsP ∗
  wpNext k.sie k.proc cpu (kforkPost k γ j pid V M stsP)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kfork`. -/
structure KFORK : Prop where
  wp_kfork_eb : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (γft : GName) (γ : FileNames)
    (j : Nat) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (stsP : List FdState) hj hproc hK hnoff htier,
    wp_kfork_eb_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk γft γ j pid V M stsP
      hj hproc hK hnoff htier

/-- The interrupts-off instance of `wp_kfork_eb`: the hart is pinned, so the
trap bundle frames across the call. -/
theorem KFORK.wp_kfork (A : KFORK) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (γft : GName) (γ : FileNames)
    (j : Nat) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (stsP : List FdState) hj hproc hK hsie hnoff hlocks htier :
    wp_kfork_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk γft γ j pid V M stsP
      hj hproc hK hsie hnoff hlocks htier := by
  have h := A.wp_kfork_eb (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk γft γ j pid V M stsP hj hproc hK hnoff htier
  unfold wp_kfork_eb_body at h
  unfold wp_kfork_body
  iintro ⟨H0, H1, H2, Htc, Hcl, Hir, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, Hnext⟩
  iapply h
  iframe H0 H1 H2 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16
  rw [hsie]
  iapply wpNext_off_intro
  unfold kforkPost kforkPostB
  iintro %spie %spp %R' %rv %hpost Hk Hpc ⟨Hpriv, Hfr⟩
  ihave Hn := wpNext_at true k.proc cpu cpu _ (fun _ => rfl) $$ Hnext
  iapply Hn $$ %spie %spp %R' %rv %hpost Hk Hpc Htc Hcl Hir Hpriv Hfr

end Xv6
