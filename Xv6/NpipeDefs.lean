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
invariant, as `TicksDefs.ticksResAt` began.  (NI M3 quotas Q-1, design R7)
The payload is now the PIPE SHARE at the count the cell reads
(`npipeShare`): the bound `npipe ≤ NPIPE`, the `NPIPE - npipe` credits of the
buffers not yet allocated, and the ticket authority at `npipe` -- every
counted buffer holds one ticket (`PipeInvDefs.pipeSlack`), so `pipeclose`'s
`npipe--` never goes below zero (the design's credits alone do not bound the
count from below).

THE HANDLE rides `FileDefs.isFtable` (the table's persistent handle, which every
caller of `pipealloc` and of `fileclose` -- hence of `pipeclose` -- already
holds), so no caller's contract gains a premise.  The lock is never
`initlock`ed: it is minted at boot from its zero `.bss` words
(`FileBoot.fileBoot_npipe`); `acquire`/`release` read no name, so the ghost
name `"npipe"` is free.
-/
import Xv6.KallocDefs
import Xv6.KcredDefs
import MachCSL.Lock

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-- `&npipe` (kernel/pipe.c, a static `.bss` word). -/
def npipeAddr : BitVec 64 := KA.«npipe»

/-- `&npipelock` (kernel/pipe.c, a static, zero-initialized spinlock). -/
def npipelockAddr : BitVec 64 := KA.«npipelock»

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [WchG GF]

/-- **The pipe share's payload** (NI M3 quotas Q-1): at count `n` (at most
`NPIPE`), the `NPIPE - n` credits of the buffers not yet allocated
(`KcredDefs.pageCredit`) and the ticket authority at `n` (one ticket per
counted buffer, `KcredDefs.npTicketAuth`). -/
def npipeShare (n : Nat) : IProp GF := iprop%
  ⌜n ≤ NPIPE⌝ ∗ pageCredit (NPIPE - n) ∗ npTicketAuth n

instance npipeShare_timeless (n : Nat) : Timeless (npipeShare (GF := GF) n) := by
  unfold npipeShare; infer_instance

/-- **The payload of `npipelock`** at context `ξ`: the counter cell, and
(NI M3 quotas Q-1, in place of Q-0's "at some value") the pipe share at
the count the cell reads. -/
def npipeResAt [CurCtx] (ξ : CtxId) : IProp GF := iprop%
  ∃ n : BitVec 32, wordAtN ξ npipeAddr 4 (DFrac.own 1) n ∗ npipeShare n.toNat

instance instCtxMorphNpipeResAt [CurCtx] : CtxMorph (GF := GF) (npipeResAt (GF := GF)) :=
  @instCtxMorphExists hlc GF _ _ (fun (n : BitVec 32) ξ => iprop(wordAtN ξ npipeAddr 4 (DFrac.own 1) n ∗
      npipeShare n.toNat))
    (fun _ => @instCtxMorphSep hlc GF _ _ _ (instCtxMorphWordAtN _ _ _ _) (instCtxMorphConst _))

/-- The payload, opened at the ambient context. -/
theorem npipeRes_elim [CurCtx] :
    npipeResAt (GF := GF) curCtx ⊢
      ∃ n : BitVec 32, wordPointsTo npipeAddr 4 (DFrac.own 1) n ∗ npipeShare n.toNat := by
  unfold npipeResAt; simp only [wordAtN_cur]; iintro H; iexact H

/-- ...and built. -/
theorem npipeRes_intro [CurCtx] (n : BitVec 32) :
    wordPointsTo (GF := GF) npipeAddr 4 (DFrac.own 1) n ∗ npipeShare n.toNat ⊢ npipeResAt curCtx := by
  unfold npipeResAt; simp only [wordAtN_cur]; iintro H; iexists n; iexact H

/-- **Counting a buffer** (`pipealloc`, below the cap): one credit out for
its `kalloc`, its ticket minted. -/
theorem npipeShare_take (n : Nat) (h : n < NPIPE) :
    npipeShare (GF := GF) n ⊢ |==> (npipeShare (n + 1) ∗ pageCredit 1 ∗ npTicket 1) := by
  unfold npipeShare
  iintro ⟨-, Hc, Ha⟩
  imod npTicket_mint n $$ Ha with ⟨Ha, Ht⟩
  icases pageCredit_take (NPIPE - n) 1 (by omega) $$ Hc with ⟨H1, Hc⟩
  imodintro
  iframe Ht H1 Ha
  isplitl []
  · ipureintro; omega
  iapply pageCredit_congr (NPIPE - n - 1) (NPIPE - (n + 1)) (by omega) $$ Hc

/-- **Uncounting a buffer** (`pipeclose`, after the freeing `kfree`): its
ticket says the count is positive, its page's credit goes back. -/
theorem npipeShare_give (n : Nat) :
    npipeShare (GF := GF) n ∗ pageCredit 1 ∗ npTicket 1 ⊢ |==> (⌜1 ≤ n⌝ ∗ npipeShare (n - 1)) := by
  unfold npipeShare
  iintro ⟨⟨%hn, Hc, Ha⟩, H1, Ht⟩
  imod npTicket_return n $$ [Ha Ht] with ⟨%h1, Ha⟩
  · iframe
  imodintro
  isplitl []
  · ipureintro; exact h1
  iframe Ha
  isplitl []
  · ipureintro; omega
  iapply pageCredit_congr (NPIPE - n + 1) (NPIPE - (n - 1)) (by omega)
  iapply pageCredit_join $$ [Hc H1]
  iframe

/-- **The boot's pipe share**: no buffer counted, all `NPIPE` credits. -/
theorem npipeShare_boot :
    pageCredit (GF := GF) NPIPE ∗ npTicketAuth 0 ⊢ npipeShare 0 := by
  unfold npipeShare
  iintro ⟨Hc, Ha⟩
  iframe Hc Ha
  ipureintro; decide

/-- **The counter's lock** (persistent). -/
def isNpipe [CurCtx] (γn : GName) : IProp GF :=
  isLock γn npipelockAddr "npipe" npipeResAt

instance isNpipe_persistent [CurCtx] (γn : GName) : Persistent (isNpipe (GF := GF) γn) := by
  unfold isNpipe; infer_instance

/-- The handle transports at any tier (as `HandlerEnv.instCtxMorphIsTickslock`). -/
instance instCtxMorphIsNpipe (t : KTier) (γn : GName) :
    CtxMorph (GF := GF) (fun ξ => @isNpipe hlc GF _ _ _ ⟨ξ, t⟩ γn) :=
  show CtxMorph (GF := GF) (fun ξ => @isLock hlc GF _ _ ⟨ξ, t⟩ γn npipelockAddr "npipe"
      (fun ζ => @npipeResAt hlc GF _ _ _ ⟨ζ, t⟩ ζ)) from
    instCtxMorphIsLock _ _ _ _ _

end

end Xv6
