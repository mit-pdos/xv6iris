/-
Specification of `release` (kernel/spinlock.c):

  if(!holding(lk)) panic("release");
  lk->cpu = 0;
  __sync_synchronize();
  __sync_lock_release(&lk->locked);
  pop_off();

Rocq `SpecRelease.wp_release_sconf_body`: the caller holds the lock
(`locked γ cpu`) and DEPOSITS the payload at its own context (`R curCtx`);
the lock's word store publishes it: the payload moves into the lock's own
context, resumed from under the holder's token, and is stamped there
(`MachCSL.lock_pay_intro`) -- so it needs `CtxMorph R`.  `s` leaves the
held set; `pop_off` unwinds one level (so the entry depth is at least 1,
and at depth 1 the saved enable state must be off: this is the
interrupts-off index the context layer supports today).  Stack: release's
4 slots over holding's 6 (and pop_off's 4).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.Image
import Xv6.SpecHolding

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `release`. -/
def releaseAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«release»

/-- **WP of `release`.** -/
def wp_release_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : CtxId → IProp GF) [CtxMorph R]
    (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (hnoff : 1 ≤ k.noff) (hK : 10 ≤ k.avail) (hexit : k.noff = 1 → k.intena = false) : Prop :=
  kctx cpu k ∗ pcIs cpu releaseAddr ∗ isLock γ (k.regs 10#5) s R ∗
  locked γ cpu ∗ R curCtx ∗
  (∀ R' : RegMap, kctx cpu ((k.popOff.withRegs R').withLocks (k.locks.filter (fun x => x ≠ s))) -∗
    pcIs cpu (retPc (k.regs 1#5)) -∗ ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu)
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `release`. -/
structure RELEASE : Prop where
  wp_release : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γ : GName) (s : String) (R : CtxId → IProp GF) [CtxMorph R] hsie htier hnoff hK hexit,
    wp_release_body (hlc := hlc) (GF := GF) cpu k γ s R hsie htier hnoff hK hexit

end Xv6
