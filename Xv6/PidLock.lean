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
def nextpidAddr : BitVec 64 := KA.«nextpid»
def initprocAddr : BitVec 64 := KA.«initproc»
-- `PIDMAX` is `Xv6/ProcGeom.lean`'s (Rocq `ProcGeom.PIDMAX`).

/-- The pids are distinct where nonzero, and in range. -/
def pidsOk (pids : Nat → BitVec 32) : Prop :=
  ∀ j1 j2, j1 < NPROC → j2 < NPROC → pids j1 ≠ 0#32 → pids j1 = pids j2 → j1 = j2

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WchG GF]

/-- The payload of `pid_lock` at context `ξ` (Rocq `PidLock.nextpid_res_at`):
the counter in `[1, PIDMAX]`, a quarter of every slot's `pid` cell, THE PID
REGISTER's authority (`SlotGen.pidRegAuth`, D8) with its domain fact
(`pidRegDom`: every registered pid is nonzero and held by some slot), and
THE BOOT ERA'S TWO MARKS -- the counter is 1, and no slot holds pid 1 --
each discharged for good by the one-shot `nextpidShot` (fired by the first
allocation's store to `nextpid`).  The distinctness conjunct `pidsOk` is
Lean's (kept from the pre-D8 payload; Rocq derives what it needs from the
scan and the register). -/
def pidLockResAt [CurCtx] (ξ : CtxId) : IProp GF := iprop%
  ∃ (np : BitVec 32) (pids : Nat → BitVec 32),
    ⌜1 ≤ np.toNat ∧ np.toNat ≤ PIDMAX ∧ pidsOk pids⌝ ∗
    wordAtN ξ nextpidAddr 4 (DFrac.own 1) np ∗
    ([∗list] j ∈ List.range NPROC, wordAtN ξ (pPid (procAddr j)) 4 pidLockQ (pids j)) ∗
    (⌜np.toNat = 1⌝ ∨ nextpidShot) ∗
    ∃ R : IntMapF GName, ⌜pidRegDom R pids⌝ ∗ pidRegAuth R ∗
      (⌜∀ j, j < NPROC → (pids j).toNat ≠ 1⌝ ∨ nextpidShot)

/-- The payload as a function of the holder's context. -/
def pidLockPay [CurCtx] : CtxId → IProp GF := fun ξ => pidLockResAt ξ

/-- `pid_lock`'s payload transports between contexts, so `acquire` and
`release` apply to it (the register rows are ghost: constants). -/
instance instCtxMorphPidLockPay [CurCtx] : CtxMorph (GF := GF) pidLockPay := by
  unfold pidLockPay pidLockResAt
  exact @instCtxMorphExists hlc GF _ _ _ (fun _ => @instCtxMorphExists hlc GF _ _ _ (fun pids =>
    @instCtxMorphSep hlc GF _ _ _ (instCtxMorphConst _)
      (@instCtxMorphSep hlc GF _ _ _ (instCtxMorphWordAtN _ _ _ _)
        (@instCtxMorphSep hlc GF _ _ _
          (ctxMorph_bigSepL (List.range NPROC)
            (fun _ y ξ => wordAtN ξ (pPid (procAddr y)) 4 pidLockQ (pids y))
            (fun _ _ => instCtxMorphWordAtN _ _ _ _))
          (instCtxMorphConst _)))))

end

end Xv6
