/-
Specification of `holding` (kernel/spinlock.c):

  int r; r = (lk->locked && lk->cpu == mycpu()); return r;

Rocq `SpecHolding.v`, two contracts:

* `wp_holding_notheld_body`: the caller does not hold `lk` (its name is
  not in the context's held set), so the answer is 0.  The word may read
  anything (a racy load); if nonzero, the owner word is read, and a hart
  that is not the recorded holder never reads its own `&cpus[i]` out of it
  (`MachCSL.lkCpu_read_not_mine`).  This is what acquire's
  `if(holding(lk)) panic(...)` needs.
* `wp_holding_locked_body`: the caller holds `lk` (`locked γ cpu`), so the
  answer is 1: the holder's view has passed the winning AMO, so the word
  reads 1, and the owner word's head is its own entry.  This is what
  release's `if(!holding(lk)) panic(...)` needs.

Both are stated at `sie = false` (the only index the context layer
supports today; `holding` calls `mycpu`, which requires it anyway).
Stack: holding's own 4 slots over mycpu's 2.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.Lock
import MachCSL.CallConv
import Xv6.KernelText
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `holding`. -/
def holdingAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«holding»

/-- **WP of `holding`, not held by the caller.**  `lk` in `a0`; returns 0. -/
def wp_holding_notheld_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : CtxId → IProp GF)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 6 ≤ k.avail) (hs : s ∉ k.locks) : Prop :=
  kctx cpu k ∗ kernelText ∗ pcIs cpu holdingAddr ∗ isLock γ (k.regs 10#5) s R ∗
  (∀ R' : RegMap, kctx cpu (k.withRegs R') -∗ pcIs cpu (retPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = 0#64⌝ -∗ wpLoop cpu)
  ⊢ wpLoop (GF := GF) cpu

/-- **WP of `holding`, held by the caller.**  `lk` in `a0`; returns 1; the
holder token comes back. -/
def wp_holding_locked_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : CtxId → IProp GF)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 6 ≤ k.avail) : Prop :=
  kctx cpu k ∗ kernelText ∗ pcIs cpu holdingAddr ∗ isLock γ (k.regs 10#5) s R ∗
  locked γ cpu ∗
  (∀ R' : RegMap, kctx cpu (k.withRegs R') -∗ pcIs cpu (retPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = 1#64⌝ -∗ locked γ cpu -∗ wpLoop cpu)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `holding`. -/
structure HOLDING : Prop where
  wp_holding_notheld : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γ : GName) (s : String) (R : CtxId → IProp GF) hsie htier hK hs,
    wp_holding_notheld_body (hlc := hlc) (GF := GF) cpu k γ s R hsie htier hK hs
  wp_holding_locked : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γ : GName) (s : String) (R : CtxId → IProp GF) hsie htier hK,
    wp_holding_locked_body (hlc := hlc) (GF := GF) cpu k γ s R hsie htier hK

end Xv6
