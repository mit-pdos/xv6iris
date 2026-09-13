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
held set; `pop_off` unwinds one level (so the entry depth is at least 1),
re-enabling interrupts when the outermost push_off found them on.  Stack:
release's 4 slots over holding's 6 (and pop_off's 4).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.Image
import Xv6.SpecHolding
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `release`. -/
def releaseAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«release»

/-- **WP of `release`.**  `pop_off` unwinds one level; when this was the
outermost push_off and it found interrupts on (`reen`), they are on again
(`KCtx.popExit`): the caller brings the arm push_off paid out (`popArm`),
the context must be one interrupts may be enabled in, and the continuation
is at whichever hart the thread lands on. -/
def wp_release_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : CtxId → IProp GF) [CtxMorph R]
    (hsie : k.sie = false)
    (hnoff : 1 ≤ k.noff) (hK : 10 ≤ k.avail)
    (reen : Bool) (hreen : reen = (decide (k.noff = 1) && k.intena))
    (hon : reen = true → k.tier = .kpt ∧ trapRes true + 6 ≤ k.avail) : Prop :=
  kctx cpu k ∗ pcIs cpu releaseAddr ∗ isLock γ (k.regs 10#5) s R ∗
  locked γ cpu ∗ R curCtx ∗ popArm cpu k reen ∗
  wpNext (k.popExit reen).sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
    kctx cpu' (((k.popExit reen).withRegs R').withLocks (k.locks.filter (fun x => x ≠ s))) -∗
    pcIs cpu' (jumpPc (k.regs 1#5)) -∗ ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `release`. -/
structure RELEASE : Prop where
  wp_release : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γ : GName) (s : String) (R : CtxId → IProp GF) [CtxMorph R] hsie hnoff hK reen hreen hon,
    wp_release_body (hlc := hlc) (GF := GF) cpu k γ s R hsie hnoff hK reen hreen hon

end Xv6
