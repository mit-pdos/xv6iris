/-
Specification of `sys_exit` (kernel/sysproc.c; Rocq SpecSysExit.v):

    uint64 sys_exit(void) {
      int n;
      argint(0, &n);
      kexit(n);
      return 0;  // not reached
    }

IT DIVERGES.  Like `kexit`'s, the contract has NO continuation: nothing
after the `jal kexit` is reachable, and gcc's dead `li a0,0` / epilogue
tail is decoded by nobody -- kexit's own contract discharges the rest of
the function by never handing control back.

THE CONTRACT IS THE UNION OF ITS TWO CALLEES', and kexit's dominates it:
everything `kexit` asks for (`procsInv`, wait_lock, `initprocIs`, the
not-init premise, the whole private block, the stack closer) is here
verbatim.  The `int n` cell is carved out of sys_exit's own frame, so it
does not appear.  The status itself is not named: kexit's contract takes
none (nothing downstream of `p->xstate` is observable from its diverging
body), so all sys_exit needs from `argint` is that argument 0 exists -- a
fact about the block's own trapframe record, `V.tf[tfArgIdx 0]? = some v`,
exactly as in `SpecSysWait`.  The trapframe pointer and page are split out
of the block for the duration of `argint` and put back before `kexit`.

THE STACK CLOSER is in transit: sys_exit takes the closer anchored at ITS
entry `sp`, wraps its own (dead) 4-slot frame around it, and hands the
result to kexit, whose ZOMBIE park is where the page reaches the slot.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SpecKexit
import Xv6.SpecArgint

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `sys_exit`. -/
def sysExitAddr : BitVec 64 := KA.«sys_exit»

/-- 4 slots for sys_exit's own frame, and below it kexit's (argint's 18 is
smaller and subsumed). -/
def sysExitSlots : Nat := 4 + kexitSlots

/-- **WP of `sys_exit()`**: no continuation -- the thread parks as a ZOMBIE
inside `kexit` and is never resumed. -/
def wp_sys_exit_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv]
    (cpu : CPU) (k : KCtx) (γw : GName) (j : Nat) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (ip v : BitVec 64)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hv : V.tf[tfArgIdx 0]? = some v)
    (hK : sysExitSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) (hinit : procAddr j ≠ ip) : Prop :=
  kctx cpu k ∗ pcIs cpu sysExitAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗ initprocIs ip ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  (stackOwn k.sp k.avail -∗ stackOwn (V.kstack + 4096#64) 512)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `sys_exit`. -/
structure SYSEXIT : Prop where
  wp_sys_exit : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv]
    (cpu : CPU) (k : KCtx) (γw : GName) (j : Nat) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (ip v : BitVec 64) hj hproc hv hK hsie hnoff hlocks htier hinit,
    wp_sys_exit_body (hlc := hlc) (GF := GF) Γ cpu k γw j pid V M ip v
      hj hproc hv hK hsie hnoff hlocks htier hinit

end Xv6
