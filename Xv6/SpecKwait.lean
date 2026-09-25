/-
Specification of `kwait` (kernel/proc.c), the reaper:

    int kwait(uint64 addr) {
      struct proc *p = myproc();
      acquire(&wait_lock);
      for (;;) {
        havekids = 0;
        for (pp = proc; pp < &proc[NPROC]; pp++)
          if (pp->parent == p) {
            acquire(&pp->lock);
            havekids = 1;
            if (pp->state == ZOMBIE) {
              pid = pp->pid;
              if (addr != 0 && copyout(p->pagetable, p->sz, addr,
                                       (char *)&pp->xstate, sizeof(pp->xstate)) < 0) {
                release(&pp->lock); release(&wait_lock); return -1;
              }
              pp->parent = 0; freeproc(pp);
              release(&pp->lock); release(&wait_lock); return pid;
            }
            release(&pp->lock);
          }
        if (!havekids || killed(p)) { release(&wait_lock); return -1; }
        sleep_prepare(p); release(&wait_lock); sleep(); acquire(&wait_lock);
      }
    }

The scan runs over `wait_lock`'s payload (the 64 `parent` words), each
child's own lock is taken and released inside it, and the reap -- the
ZOMBIE child's `freeproc` -- happens entirely inside `procsInv`: what
comes out is the child's dormant block, which `freeproc` hands back to
the allocator.  NOTHING OF THE CHILD REACHES THE CALLER.

THE ONLY THING `kwait` WRITES IS THE FOUR-BYTE EXIT STATUS, at `addr`,
and only when `addr != 0` (the port of the Rocq prototype's
`wp_kwait_sconf_body` post): `d` is the count `copyout` actually placed
(`0` on the null-destination arm, on the no-child arm and on `killed`;
`4` on the reaping arm; a short prefix when `copyout` itself failed), and
the bytes are those of ONE status word `xw`, the zombie's.

WHICH child was reaped is NOT stated: the prototype answers that with a
children-row ghost (`ch_frag`, a set of generations) and a pid escrow,
which this port does not carry -- `kwaitAns` keeps only what is provable
without them, and it is enough to tell a `-1` apart from a reap whose
status did reach the caller.

THE BLOCK COMES BACK WHOLE at the descriptor `copyout`'s lazy faults grew
(Rocq: `uptd_ext_sz (pv_sz V)` and `proc_priv (us_upt U P')`): `copyout`
promises `V.upt.extSz V.sz P'`, every gained leaf below the break, so
`umBelow` survives.

It SLEEPS (the shape of `Xv6/SpecSleep.lean`): the thread may park and
come back on another hart, so the trap CSRs, the claim and the installed
handler it gets back are that hart's, and `SPIE`/`SPP` are quantified.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SchedCtx
import Xv6.WaitLock
import Xv6.PidLock
import Xv6.SpecEitherCopyout
import Xv6.SpecCopyout
import Xv6.SpecFreeproc
import Xv6.SpecSleep
import MachCSL.Lock
import MachCSL.WpSmodeIntr
import Iris.ProofMode

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

/-- Address of `kwait`. -/
def kwaitAddr : BitVec 64 := KA.«kwait»

/-- The stack `kwait`'s cone needs: its own 10-slot frame over `copyout`'s
52 (`freeproc` needs 44, `sleep` 20, `killed` 14). -/
def kwaitSlots : Nat := 62

/-- `sizeof(pp->xstate)` bytes of the status word, little-endian. -/
def xstateBytes (xw : BitVec 32) : List (BitVec 8) :=
  [nthByte (n := 4) xw 0, nthByte (n := 4) xw 1, nthByte (n := 4) xw 2, nthByte (n := 4) xw 3]

@[simp] theorem xstateBytes_length (xw : BitVec 32) : (xstateBytes xw).length = 4 := rfl

/-- What `kwait` answered: `-1` -- no child, or `killed`, or a `copyout`
that failed after a prefix -- or the reaped child's pid, and then the
WHOLE status word reached `addr` (nothing at all if `addr` was null). -/
def kwaitAns (rv : BitVec 32) (addr : BitVec 64) (d : Nat) : Prop :=
  rv = -1#32 ∨ (addr = 0#64 ∧ d = 0) ∨ (addr ≠ 0#64 ∧ d = 4)

/-- **WP of `kwait(addr = a0)`.** -/
def wp_kwait_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : kwaitSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu kwaitAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (P' : UPtd)
    (rv xw : BitVec 32) (d : Nat),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ V.upt.extSz V.sz P' ∧ d ≤ 4 ∧
      kwaitAns rv (k.regs 10#5) d⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    procPrivNoctxAt curCtx (procAddr j) pid { V with upt := P' }
      (umemWrite (viewFaulted V.upt P' M) (k.regs 10#5).toNat ((xstateBytes xw).take d)) -∗
    wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- **WP of `kwait(addr = a0)`, at either entry `SIE`** (Rocq
`wp_kwait_sconf_body`, stated there at `eb = true`; this is its eb-generic
form, the Rocq kexit/sys_sync shape): `cpu_own 0 eb`, the trap-CSR complement
`trapCsrsExt` / `cpuClaimExt` in and out.  kwait is balanced -- its own
`acquire(&wait_lock)` mints the pay its interior sleep needs at `sie = true`
(the complement is `emp`), at `sie = false` the caller brings the pair.
Depth 0, so no spinlock held (`KCtx.wf`).  It parks: the crossing is the
literal `true`. -/
def wp_kwait_eb_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8))
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : kwaitSlots ≤ k.avail)
    (hnoff : k.noff = 0)
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu kwaitAddr ∗ procsInv Γ ∗
  trapCsrsExt cpu k.sie ∗ cpuClaimExt cpu k.sie k.proc ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (P' : UPtd)
    (rv xw : BitVec 32) (d : Nat),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ V.upt.extSz V.sz P' ∧ d ≤ 4 ∧
      kwaitAns rv (k.regs 10#5) d⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrsExt cpu' k.sie -∗ cpuClaimExt cpu' k.sie k.proc -∗
    procPrivNoctxAt curCtx (procAddr j) pid { V with upt := P' }
      (umemWrite (viewFaulted V.upt P' M) (k.regs 10#5).toNat ((xstateBytes xw).take d)) -∗
    wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `kwait`. -/
structure KWAIT : Prop where
  wp_kwait_eb : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) hj hproc hK hnoff htier,
    wp_kwait_eb_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M
      hj hproc hK hnoff htier

/-- The interrupts-off instance of `wp_kwait_eb` (the complement is the whole
bundle): the contract every not-yet-generalized caller states. -/
theorem KWAIT.wp_kwait (A : KWAIT) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF]
    [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) hj hproc hK hsie hnoff hlocks htier :
    wp_kwait_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M
      hj hproc hK hsie hnoff hlocks htier := by
  have h := A.wp_kwait_eb (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M hj hproc hK hnoff htier
  unfold wp_kwait_eb_body at h
  unfold wp_kwait_body
  rw [hsie] at h
  simp only [trapCsrsExt_false, cpuClaimExt_false] at h
  iintro ⟨H0, H1, H2, Htc, Hcl, Hir, H6, H7, H8, H9, H10, Hnext⟩
  iapply h
  iframe H0 H1 H2 Htc Hcl Hir H6 H7 H8 H9 H10
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK %spie %spp %R' %P' %rv %xw %d %p0 H1 H2 ⟨Htc, Hir⟩ Hcl H6
  iapply HK $$ %spie %spp %R' %P' %rv %xw %d %p0 H1 H2 Htc Hcl Hir H6

end Xv6
