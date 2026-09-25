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
(`either_copyin`'s post), and `uartwrite` sleeps.  The contract is
`wp_consolewrite_eb_body`, at either entry `SIE` (Rocq pins it at `eb = true`):
consolewrite takes no lock, so the caller's trap-CSR complement
(`trapCsrsExt`/`cpuClaimExt`, `emp` with interrupts on) is threaded to
`uartwrite`'s eb contract and back.  The interrupts-off
`wp_consolewrite_body` is its derived instance.  Returns the count written,
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
import Iris.ProofMode

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

/-- Address of `consolewrite`. -/
def consolewriteAddr : BitVec 64 := KA.«consolewrite»

/-- The stack `consolewrite`'s cone needs: its 16-slot frame over `either_copyin`'s. -/
def consolewriteSlots : Nat := 16 + eitherCopyinSlots

/-- `consolewrite`'s result: a count in `[0, max 0 n]`. -/
def consWriteRet (n : Int) (r : BitVec 64) : Prop :=
  ∃ i : Int, r = BitVec.ofInt 64 i ∧ 0 ≤ i ∧ i ≤ max 0 n

/-- **WP of `consolewrite`.**  `a0 = user_src` (nonzero), `a1 = src`, `a2 = n`. -/
def wp_consolewrite_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
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
    ⌜calleeSaved k.regs R' ∧ V.upt.extSz V.sz P' ∧ consWriteRet n (R' 10#5)⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    (∃ cs : List (BitVec 8), uartSentSub γ (bs ++ cs)) -∗
    procPrivNoctxAt curCtx (procAddr j) pid { V with upt := P' } (viewFaulted V.upt P' M) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- **WP of `consolewrite`, at either entry `SIE`** (Rocq
`wp_consolewrite_sconf_body`, there pinned at `eb = true`; this form is that
instance at `k.sie = true`): the trap-CSR complement (`trapCsrsExt` /
`cpuClaimExt`, `emp` at `sie = true`) in and out, handed to `uartwrite`'s eb
contract across each park.  Depth 0 (no spinlock held, `KCtx.wf`); it parks,
so the crossing is the literal `true`. -/
def wp_consolewrite_eb_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : UartNames) (bs : List (BitVec 8))
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : consolewriteSlots ≤ k.avail)
    (hnoff : k.noff = 0)
    (htier : k.tier = KTier.kpt) (huser : k.regs 10#5 ≠ 0#64)
    (hn : k.regs 12#5 = BitVec.ofInt 64 n) (hn' : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) : Prop :=
  kctx cpu k ∗ pcIs cpu consolewriteAddr ∗ procsInv Γ ∗
  trapCsrsExt cpu k.sie ∗ cpuClaimExt cpu k.sie k.proc ∗
  uartPort .uart0 γl γ ∗ uartSentSub γ bs ∗
  isLock γkl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (P' : UPtd),
    ⌜calleeSaved k.regs R' ∧ V.upt.extSz V.sz P' ∧ consWriteRet n (R' 10#5)⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrsExt cpu' k.sie -∗ cpuClaimExt cpu' k.sie k.proc -∗
    (∃ cs : List (BitVec 8), uartSentSub γ (bs ++ cs)) -∗
    procPrivNoctxAt curCtx (procAddr j) pid { V with upt := P' } (viewFaulted V.upt P' M) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `consolewrite`. -/
structure CONSOLEWRITE : Prop where
  wp_consolewrite_eb : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : UartNames) (bs : List (BitVec 8))
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int) hj hproc hK hnoff htier huser hn hn',
    wp_consolewrite_eb_body (hlc := hlc) (GF := GF) Γ cpu k γl γ bs γkl γk j pid V M n hj hproc hK hnoff htier huser hn hn'

/-- The interrupts-off instance of `wp_consolewrite_eb` (the complement is the
whole bundle). -/
theorem CONSOLEWRITE.wp_consolewrite (A : CONSOLEWRITE) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    [Xv6G GF] [FdslotG GF] [BioslotG GF] [IrefslotG GF] [CurCtx] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : UartNames) (bs : List (BitVec 8))
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int) hj hproc hK hsie hnoff hlocks htier huser hn hn' :
    wp_consolewrite_body (hlc := hlc) (GF := GF) Γ cpu k γl γ bs γkl γk j pid V M n hj hproc hK hsie hnoff
      hlocks htier huser hn hn' := by
  have h := A.wp_consolewrite_eb (hlc := hlc) (GF := GF) Γ cpu k γl γ bs γkl γk j pid V M n hj hproc hK
    hnoff htier huser hn hn'
  unfold wp_consolewrite_eb_body at h
  unfold wp_consolewrite_body
  rw [hsie] at h
  simp only [trapCsrsExt_false, cpuClaimExt_false] at h
  iintro ⟨H0, H1, H2, Htc, Hcl, Hir, H6, H7, H8, H9, H10, Hnext⟩
  iapply h
  iframe H0 H1 H2 Htc Hcl Hir H6 H7 H8 H9 H10
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK %spie %spp %R' %P' %p0 H1 H2 ⟨Htc, Hir⟩ Hcl H6 H7
  iapply HK $$ %spie %spp %R' %P' %p0 H1 H2 Htc Hcl Hir H6 H7

end Xv6
