/-
Specification of `acquire` (kernel/spinlock.c):

  push_off();
  if(holding(lk)) panic("acquire");
  while(__sync_lock_test_and_set(&lk->locked, 1) != 0) ;
  lk->cpu = mycpu();

Rocq `SpecAcquire.wp_acquire_sconf_body`, with the context-handling
subtleties that matter to later users (tso-port M2/M3):

* THE PAYLOAD COMES BACK AT THE CALLER'S OWN CONTEXT: `R curCtx`, with
  `curCtx` bound OUTSIDE the `wpNext` binder.  The hart may rebind at
  `wpNext` (a migration during the enabled prologue); the thread of
  control does not, and the facts a thread wins are its own.  The lock's
  payload is moved out of the lock's parked context into the winner's at
  the AMO (`MachCSL.lock_pay_take`), so it needs `CtxMorph R`.
* THE VIEW RECEIPT: `∃ K, viewLb cpu' K`, minted at the acquire AMO --
  the stable "my view passed the acquire" fact the scheduler chain
  threads to `swtch`.
* THE HOLDER TOKEN `locked γ cpu'` names the hart that won, and carries
  the lock's context parked under the winner's (`lockCtxHeld`).
* The exit context is UNBALANCED: `push_off`'s depth, and `s` enters the
  held set (`s ∉ k.locks` on entry: taking a lock twice is the panic arm,
  discharged as dead code by `holding`'s not-held contract).

`sie = false` is the only index the context layer supports today, so the
`wpNext` continuation collapses to this hart; it is kept for the reason
above.  Stack: acquire's 4 slots over holding's 6 (and push_off's 6).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.Image
import Xv6.SpecHolding

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `acquire`. -/
def acquireAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«acquire»

/-- **WP of `acquire`.** -/
def wp_acquire_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : CtxId → IProp GF) [CtxMorph R]
    (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 10 ≤ k.avail) (hs : s ∉ k.locks) : Prop :=
  kctx cpu k ∗ pcIs cpu acquireAddr ∗ isLock γ (k.regs 10#5) s R ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
    kctx cpu' ((k.pushOff.withRegs R').withLocks (s :: k.locks)) -∗
    pcIs cpu' (jumpPc (k.regs 1#5)) -∗ ⌜calleeSaved k.regs R'⌝ -∗
    locked γ cpu' -∗ R curCtx -∗ (∃ K : Nat, viewLb cpu' K) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `acquire`. -/
structure ACQUIRE : Prop where
  wp_acquire : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γ : GName) (s : String) (R : CtxId → IProp GF) [CtxMorph R] hsie htier hnoff hK hs,
    wp_acquire_body (hlc := hlc) (GF := GF) cpu k γ s R hsie htier hnoff hK hs

end Xv6
