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

* Interrupts may be on at entry: push_off turns them off (`KCtx.pushOffAt`,
  the arm paid out to the caller), and the thread may move harts until
  then, hence the `wpNext`.  Stack: acquire's 4 slots over holding's 6
  (and push_off's 6).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.Image
import Xv6.SpecHolding
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `acquire`. -/
def acquireAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«acquire»

/-- **WP of `acquire`**, at either `SIE`: interrupts are off on exit
(push_off's `KCtx.pushOffAt`, with the arm the entry context held the
caller's afterwards -- nothing when they were already off), the lock's
name enters the held set, and the continuation is at whichever hart the
thread landed on while interrupts were on. -/
def wp_acquire_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : CtxId → IProp GF) [CtxMorph R]
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 10 ≤ k.avail) (hs : s ∉ k.locks) : Prop :=
  kctx cpu k ∗ pcIs cpu acquireAddr ∗ isLock γ (k.regs 10#5) s R ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' (((k.pushOffAt spie spp).withRegs R').withLocks (s :: k.locks)) -∗
    pcIs cpu' (jumpPc (k.regs 1#5)) -∗ ⌜calleeSaved k.regs R'⌝ -∗
    locked γ cpu' -∗ R curCtx -∗ (∃ K : Nat, viewLb cpu' K) -∗ sieArm cpu' k.sie k.proc -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `acquire`. -/
structure ACQUIRE : Prop where
  wp_acquire : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γ : GName) (s : String) (R : CtxId → IProp GF) [CtxMorph R] hnoff hK hs,
    wp_acquire_body (hlc := hlc) (GF := GF) cpu k γ s R hnoff hK hs

end Xv6
