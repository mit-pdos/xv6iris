/-
The tick counter `ticks` and the spinlock that owns it, `tickslock`
(Rocq TicksInv.v).  The payload is deliberately the WEAKEST useful
invariant: ownership of the 4-byte counter cell at an arbitrary value --
all `sys_pause` needs (it compares readings and sleeps), and all
`clockintr` can maintain without a ghost tick history.

The lock's name is the literal `"time"` that `trapinit` passes to
`initlock` (`Xv6/SpecTrapinit.lean`), so `isTickslock` is what a caller
seals from trapinit's `lkFresh`.
-/
import Xv6.KallocDefs
import Xv6.SpecTrapinit
import MachCSL.Lock

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-- `&ticks` (kernel/trap.c). -/
def ticksAddr : BitVec 64 := 0x8000a348#64

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-- The payload of `tickslock` at context `ξ`: the counter cell, contents
existential. -/
def ticksResAt [CurCtx] (ξ : CtxId) : IProp GF := iprop%
  ∃ t : BitVec 32, wordAtN ξ ticksAddr 4 (DFrac.own 1) t

instance instCtxMorphTicksResAt [CurCtx] : CtxMorph (GF := GF) (ticksResAt (GF := GF)) :=
  @instCtxMorphExists hlc GF _ _ (fun (t : BitVec 32) ξ => wordAtN ξ ticksAddr 4 (DFrac.own 1) t)
    (fun t => instCtxMorphWordAtN _ _ _ _)

/-- The payload, opened at the ambient context. -/
theorem ticksRes_elim [CurCtx] :
    ticksResAt (GF := GF) curCtx ⊢ ∃ t : BitVec 32, wordPointsTo ticksAddr 4 (DFrac.own 1) t := by
  unfold ticksResAt; simp only [wordAtN_cur]; iintro H; iexact H

/-- ...and built. -/
theorem ticksRes_intro [CurCtx] (t : BitVec 32) :
    wordPointsTo (GF := GF) ticksAddr 4 (DFrac.own 1) t ⊢ ticksResAt curCtx := by
  unfold ticksResAt; simp only [wordAtN_cur]; iintro H; iexists t; iexact H

/-- The tick lock. -/
def isTickslock [CurCtx] (γt : GName) : IProp GF :=
  isLock γt tickslockAddr "time" ticksResAt

instance isTickslock_persistent [CurCtx] (γt : GName) : Persistent (isTickslock (GF := GF) γt) := by
  unfold isTickslock; infer_instance

end

end Xv6
