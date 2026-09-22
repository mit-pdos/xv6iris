/-
Specification of `acquiresleep` (kernel/sleeplock.c; Rocq SpecAcquiresleep.v):

    void acquiresleep(struct sleeplock *lk) {
      acquire(&lk->lk);
      while (lk->locked) { sleep_prepare(lk); release(&lk->lk); sleep(); acquire(&lk->lk); }
      lk->locked = 1;
      lk->pid = myproc()->pid;
      release(&lk->lk);
    }

The separation-logic lock spec, sleeplock flavour, over the holder DEPOSIT
`H` (`Xv6/SleepLockDefs.lean`):

    { isSleeplockGen γl γ slk R H ∗ H q ∗ <thread resources> }
      acquiresleep(slk)
    { sleeplockedQ γ q slk pid ∗ R ∗ <thread resources> }

The <thread resources> are what the callees demand: the caller's own pid
cell at any fraction (`lk->pid = myproc()->pid`), and -- because the wait
loop parks through `sleep` -- the running-thread bundle (`procsInv`, the
trap CSRs, the claim, the installed handler).  Entered with no lock held at
`noff = 0`: `sleep` requires exactly that.  It PARKS, so the post is
`wpNext true` (the shape of `Xv6/SpecSleep.lean`).

`wp_acquiresleep_body` is the untracked instance (`H := slUntracked`,
`q := 1`), derived below; it is what every ordinary caller takes.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SleepLockDefs
import Xv6.SpecSleep
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

/-- Address of `acquiresleep`. -/
def acquiresleepAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«acquiresleep»

/-- acquiresleep's 4-slot frame over the deepest callee, `sleep`'s 20
(`sleep_prepare` 14, `acquire`/`release`/`myproc` 10). -/
def acquiresleepSlots : Nat := 4 + sleepSlots

/-- **WP of `acquiresleep(slk = a0)`**, over the deposit `H` at `q`. -/
def wp_acquiresleep_gen_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [SleepLockG GF]
    [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl γ : GName) (R : CtxId → IProp GF) [CtxMorph R] (H : Qp → IProp GF) (q : Qp)
    (j : Nat) (pid : BitVec 32) (dqp : DFrac)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : acquiresleepSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu acquiresleepAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isSleeplockGen γl γ (k.regs 10#5) R H ∗ H q ∗
  wordPointsTo (pPid k.proc) 4 dqp pid ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
    ⌜calleeSaved k.regs R'⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    sleeplockedQ γ q (k.regs 10#5) pid -∗ R curCtx -∗
    wordPointsTo (pPid k.proc) 4 dqp pid -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The untracked instance: nothing deposited, the token at `1`. -/
def wp_acquiresleep_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [SleepLockG GF]
    [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl γ : GName) (R : CtxId → IProp GF) [CtxMorph R]
    (j : Nat) (pid : BitVec 32) (dqp : DFrac)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : acquiresleepSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu acquiresleepAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isSleeplock γl γ (k.regs 10#5) R ∗
  wordPointsTo (pPid k.proc) 4 dqp pid ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
    ⌜calleeSaved k.regs R'⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    sleeplockedQ γ 1 (k.regs 10#5) pid -∗ R curCtx -∗
    wordPointsTo (pPid k.proc) 4 dqp pid -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `acquiresleep`. -/
structure ACQUIRESLEEP : Prop where
  wp_acquiresleep_gen : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [SleepLockG GF]
    [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl γ : GName) (R : CtxId → IProp GF) [CtxMorph R] (H : Qp → IProp GF) (q : Qp)
    (j : Nat) (pid : BitVec 32) (dqp : DFrac) hj hproc hK hsie hnoff hlocks htier,
    wp_acquiresleep_gen_body (hlc := hlc) (GF := GF) Γ cpu k γl γ R H q j pid dqp
      hj hproc hK hsie hnoff hlocks htier

/-- The untracked contract, from the general one. -/
theorem ACQUIRESLEEP.wp_acquiresleep (A : ACQUIRESLEEP) {hlc : HasLC} {GF : BundledGFunctors}
    [MachGS hlc GF] [Xv6G GF] [SleepLockG GF] [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl γ : GName) (R : CtxId → IProp GF) [CtxMorph R]
    (j : Nat) (pid : BitVec 32) (dqp : DFrac) hj hproc hK hsie hnoff hlocks htier :
    wp_acquiresleep_body (hlc := hlc) (GF := GF) Γ cpu k γl γ R j pid dqp hj hproc hK hsie hnoff hlocks htier := by
  have h := A.wp_acquiresleep_gen (hlc := hlc) (GF := GF) Γ cpu k γl γ R slUntracked 1 j pid dqp
    hj hproc hK hsie hnoff hlocks htier
  unfold wp_acquiresleep_gen_body at h
  unfold wp_acquiresleep_body isSleeplock
  iintro ⟨Hk, Hpc, Hpi, Htc, Hcl, Hir, Hsl, Hpid, Hnext⟩
  iapply h
  iframe Hk Hpc Hpi Htc Hcl Hir Hsl Hpid Hnext
  unfold slUntracked
  iempintro

end Xv6
