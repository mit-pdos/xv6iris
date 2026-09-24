/-
Specification of `consolewrite` (kernel/console.c): a user `write()` to
the console -- batches of up to 32 bytes copied in from the process and
pushed through `uartwrite(0, ...)`.

```
int consolewrite(int user_src, uint64 src, int n) {
  char buf[32]; int i = 0;
  while (i < n) {
    int nn = sizeof(buf); if (nn > n - i) nn = n - i;
    if (either_copyin(buf, user_src, src + i, nn) == -1) break;
    uartwrite(0, buf, nn);
    i += nn;
  }
  return i;
}
```

The running thread is proc `j` with a user source (`user_src != 0`, the
only caller being `filewrite`); its private view `M` may fault pages in
(`either_copyin`'s post), and `uartwrite` sleeps (the trap CSRs, the hart's
claim and the interrupt resource travel).  Returns the count written,
between `0` and `max 0 n` (`pipeRwRet`, without the `-1`).  Stack: the
16-slot frame over `either_copyin`'s 56.

Imports only definitional files.
-/
import MachCSL.CallConv
import Xv6.Image
import Xv6.UartInv
import Xv6.KallocDefs
import Xv6.SchedCtx
import Xv6.UMem
import Xv6.SpecEitherCopyin
import Xv6.SpecUartwrite

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `consolewrite`. -/
def consolewriteAddr : BitVec 64 := KA.«consolewrite»

/-- The stack `consolewrite`'s cone needs: its 16-slot frame over `either_copyin`'s. -/
def consolewriteSlots : Nat := 16 + eitherCopyinSlots

/-- `consolewrite`'s result: a count in `[0, max 0 n]`. -/
def consWriteRet (n : Int) (r : BitVec 64) : Prop :=
  ∃ i : Int, r = BitVec.ofInt 64 i ∧ 0 ≤ i ∧ i ≤ max 0 n

/-- **WP of `consolewrite`.**  `a0 = user_src` (nonzero), `a1 = src`, `a2 = n`. -/
def wp_consolewrite_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : UartNames) (bs : List (BitVec 8))
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : consolewriteSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) (huser : k.regs 10#5 ≠ 0#64)
    (hn : k.regs 12#5 = BitVec.ofInt 64 n) (hn' : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) : Prop :=
  kctx cpu k ∗ pcIs cpu consolewriteAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  uartPort .uart0 γl γ ∗ uartSentSub γ bs ∗
  isLock γkl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (P' : UPtd),
    ⌜calleeSaved k.regs R' ∧ V.upt.ext P' ∧ consWriteRet n (R' 10#5)⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    (∃ cs : List (BitVec 8), uartSentSub γ (bs ++ cs)) -∗
    procPrivExtNoctxAt curCtx (procAddr j) pid V P' (viewFaulted V.upt P' M) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `consolewrite`. -/
structure CONSOLEWRITE : Prop where
  wp_consolewrite : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : UartNames) (bs : List (BitVec 8))
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int) hj hproc hK hsie hnoff hlocks htier huser hn hn',
    wp_consolewrite_body (hlc := hlc) (GF := GF) Γ cpu k γl γ bs γkl γk j pid V M n hj hproc hK hsie hnoff hlocks htier huser hn hn'

end Xv6
