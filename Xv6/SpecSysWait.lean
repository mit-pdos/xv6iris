/-
Specification of `sys_wait` (kernel/sysproc.c; Rocq SpecSysWait.v):

    uint64 sys_wait(void) {
      uint64 p;
      argaddr(0, &p);
      return kwait(p);
    }

THE CONTRACT IS THE UNION OF ITS TWO CALLEES', and kwait's dominates it:
everything `kwait` asks for (wait_lock, pid_lock, the kalloc environment,
`procsInv`, the parking premises) is here verbatim.  The destination cell
is carved out of sys_wait's own frame, so it does not appear.

THE ARGUMENT COMES OUT OF THE PRIVATE BLOCK, not a separate trapframe
fraction: argaddr's contract takes the trapframe as a bare fraction, but
kwait needs the whole block, so the proof splits the fraction out for the
duration of the call and puts it back.  The argument is named as a fact
about the block's own trapframe record, `V.tf[tfArgIdx 0]? = some v`.

WHAT IT SAYS ABOUT THE RESULT is kwait's verbatim, with `v` -- the
syscall's argument 0 -- in place of kwait's `a0`: `-1` with nothing
moved, or the reaped child's pid with the four-byte status word at `v`
(nothing when `v = 0`).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SpecKwait
import Xv6.SpecArgaddr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `sys_wait`. -/
def sysWaitAddr : BitVec 64 := KA.«sys_wait»

/-- 4 slots for sys_wait's own frame, and below it the deeper of its two
callees: kwait's 62 (argaddr's is 18). -/
def sysWaitSlots : Nat := 4 + kwaitSlots

/-- **WP of `sys_wait()`.** -/
def wp_sys_wait_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (v : BitVec 64)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hv : V.tf[tfArgIdx 0]? = some v)
    (hK : sysWaitSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu sysWaitAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  isLock γp pidLockAddr "nextpid" pidLockPay ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (P' : UPtd)
    (rv xw : BitVec 32) (d : Nat),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = BitVec.signExtend 64 rv ∧ V.upt.extSz V.sz P' ∧ d ≤ 4 ∧
      kwaitAns rv v d⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    procPrivNoctxAt curCtx (procAddr j) pid { V with upt := P' }
      (umemWrite (viewFaulted V.upt P' M) v.toNat ((xstateBytes xw).take d)) -∗
    wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `sys_wait`. -/
structure SYSWAIT : Prop where
  wp_sys_wait : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γw γp γl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (v : BitVec 64) hj hproc hv hK hsie hnoff hlocks htier,
    wp_sys_wait_body (hlc := hlc) (GF := GF) Γ cpu k γw γp γl γk j pid V M v
      hj hproc hv hK hsie hnoff hlocks htier

end Xv6
