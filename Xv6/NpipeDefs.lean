/-
**The pipe-buffer counter and its lock** (NI M3 quotas, Q-0; kernel
`verified-quota`, `kernel/pipe.c`):

```
static struct spinlock npipelock;   // zero-initialized: no initlock
static int npipe;                   // pipe buffers allocated, at most NPIPE
```

`pipealloc` takes `npipelock`, refuses at `npipe >= NPIPE` (`NPIPE = NFILE / 2
= 50`, the `li a4,49 ; blt a4,a5` at `pipealloc+0x3e`), and otherwise counts
the buffer before its `kalloc`; `pipeclose` uncounts it after its `kfree`.

THE PAYLOAD (Q-0): the counter cell at SOME value -- the weakest useful
invariant, as `TicksDefs.ticksResAt` began.  Nothing yet relates `npipe` to the
number of live pipes; Q-1 strengthens the payload with the reservation
(`kCredit (NPIPE - npipe)`, design "M3 quotas", R7) and the bound.

THE HANDLE rides `FileDefs.isFtable` (the table's persistent handle, which every
caller of `pipealloc` and of `fileclose` -- hence of `pipeclose` -- already
holds), so no caller's contract gains a premise.  The lock is never
`initlock`ed: it is minted at boot from its zero `.bss` words
(`FileBoot.fileBoot_npipe`); `acquire`/`release` read no name, so the ghost
name `"npipe"` is free.
-/
import Xv6.KallocDefs
import MachCSL.Lock

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-- `&npipe` (kernel/pipe.c, a static `.bss` word). -/
def npipeAddr : BitVec 64 := KA.«npipe»

/-- `&npipelock` (kernel/pipe.c, a static, zero-initialized spinlock). -/
def npipelockAddr : BitVec 64 := KA.«npipelock»

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- **The payload of `npipelock`** at context `ξ`: the counter cell, at some
value (Q-0; the reservation is Q-1's). -/
def npipeResAt [CurCtx] (ξ : CtxId) : IProp GF := iprop%
  ∃ n : BitVec 32, wordAtN ξ npipeAddr 4 (DFrac.own 1) n

instance instCtxMorphNpipeResAt [CurCtx] : CtxMorph (GF := GF) (npipeResAt (GF := GF)) :=
  @instCtxMorphExists hlc GF _ _ (fun (n : BitVec 32) ξ => wordAtN ξ npipeAddr 4 (DFrac.own 1) n)
    (fun _ => instCtxMorphWordAtN _ _ _ _)

/-- The payload, opened at the ambient context. -/
theorem npipeRes_elim [CurCtx] :
    npipeResAt (GF := GF) curCtx ⊢ ∃ n : BitVec 32, wordPointsTo npipeAddr 4 (DFrac.own 1) n := by
  unfold npipeResAt; simp only [wordAtN_cur]; iintro H; iexact H

/-- ...and built. -/
theorem npipeRes_intro [CurCtx] (n : BitVec 32) :
    wordPointsTo (GF := GF) npipeAddr 4 (DFrac.own 1) n ⊢ npipeResAt curCtx := by
  unfold npipeResAt; simp only [wordAtN_cur]; iintro H; iexists n; iexact H

/-- **The counter's lock** (persistent). -/
def isNpipe [CurCtx] (γn : GName) : IProp GF :=
  isLock γn npipelockAddr "npipe" npipeResAt

instance isNpipe_persistent [CurCtx] (γn : GName) : Persistent (isNpipe (GF := GF) γn) := by
  unfold isNpipe; infer_instance

/-- The handle transports at any tier (as `HandlerEnv.instCtxMorphIsTickslock`). -/
instance instCtxMorphIsNpipe (t : KTier) (γn : GName) :
    CtxMorph (GF := GF) (fun ξ => @isNpipe hlc GF _ ⟨ξ, t⟩ γn) :=
  show CtxMorph (GF := GF) (fun ξ => @isLock hlc GF _ _ ⟨ξ, t⟩ γn npipelockAddr "npipe"
      (fun ζ => @npipeResAt hlc GF _ ⟨ζ, t⟩ ζ)) from
    instCtxMorphIsLock _ _ _ _ _

end

end Xv6
