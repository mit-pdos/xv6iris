/-
`pid_lock` (kernel/proc.c): protects `nextpid` and the pid scan of
`allocpid` (inlined into `allocproc`), which reads every process's `pid`
without its lock.  The payload carries the `nextpid` word and a quarter
of every `pid` word (the private block keeps a half, `p->lock` a quarter),
with the invariant that live pids are distinct and in `[1, PIDMAX]`.
-/
import Xv6.UPtDefs
import Xv6.ProcDefs
import Xv6.SpecProcinit
import MachCSL.Lock

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-- `&nextpid`, `&initproc` (`&pid_lock` is `Xv6/SpecProcinit.lean`'s
`pidLockAddr`). -/
def nextpidAddr : BitVec 64 := 0x8000a2b4#64
def initprocAddr : BitVec 64 := 0x8000a340#64
/-- `PIDMAX`. -/
def PIDMAX : Nat := 1000

/-- The pids are distinct where nonzero, and in range. -/
def pidsOk (pids : Nat → BitVec 32) : Prop :=
  ∀ j1 j2, j1 < NPROC → j2 < NPROC → pids j1 ≠ 0#32 → pids j1 = pids j2 → j1 = j2

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- The payload of `pid_lock` at context `ξ`. -/
def pidLockResAt [CurCtx] (ξ : CtxId) : IProp GF := iprop%
  ∃ (np : BitVec 32) (pids : Nat → BitVec 32),
    ⌜1 ≤ np.toNat ∧ np.toNat ≤ PIDMAX ∧ pidsOk pids⌝ ∗
    wordAtN ξ nextpidAddr 4 (DFrac.own 1) np ∗
    [∗list] j ∈ List.range NPROC, wordAtN ξ (pPid (procAddr j)) 4 pidLockQ (pids j)

/-- The payload as a function of the holder's context. -/
def pidLockPay [CurCtx] : CtxId → IProp GF := fun ξ => pidLockResAt ξ

end

end Xv6
