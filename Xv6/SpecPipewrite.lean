/-
Specification of `pipewrite` (kernel/pipe.c): the public contract, stated
once, in the kernel execution context.

  int pipewrite(struct pipe *pi, uint64 addr, int n)

pipewrite copies up to `n` bytes from user address `addr` into the pipe,
sleeping on `&pi->nwrite` while the pipe is full, and returns the number it
copied -- or -1 if the read end closed or the process was killed while it
waited (or the very first copyin failed).  Rocq `SpecPipewrite.v`.

THE ALTITUDE: the pipe at the reference tier (`isPipe` persistent, and
`pipeRef γp w q` -- ANY end, ANY positive fraction -- is the whole
credential: it refutes the pipe's dead branch for every acquire, including
the re-acquire after sleep); the process at the sleeping-syscall tier
(`SpecKwait`'s shape): interrupts off at entry, depth 0, no lock held, the
running process is proc `j`, and the `trapCsrs`/`cpuClaim`/`intrRes` bundle
crosses `sleep`'s hart-generic return.

THE IMAGE DOES NOT MOVE: pipewrite only READS user memory (one byte per
round through `copyin`), so the process block comes back at the caller's own
`M` with only the faulted pages zeroed (`viewFaulted`) and the DESCRIPTOR
grown (`V.upt.ext P'`).  The pipe's CONTENTS stay existential (`pipeResAt`
hides the byte window), so nothing about them is promised.

Stack: pipewrite's own 14 slots over copyin's 50 (`pipewriteSlots = 64`).

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.SpecSleep
import Xv6.PipeInvDefs
import Xv6.KallocDefs
import Xv6.SchedCtx
import Xv6.UMem
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `pipewrite`. -/
def pipewriteAddr : BitVec 64 := KA.«pipewrite»

/-- pipewrite's 14-slot frame over copyin's 50. -/
def pipewriteSlots : Nat := 64

/-- **WP of `pipewrite`.**  `a0 = pi`, `a1 = addr`, `a2 = n` (an `int`). -/
def wp_pipewrite_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (γp : PipeNames) (w : Bool) (q : Qp)
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : pipewriteSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt)
    (hn : k.regs 12#5 = BitVec.ofInt 64 n) (hn' : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) : Prop :=
  kctx cpu k ∗ pcIs cpu pipewriteAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isPipe γl γp (k.regs 10#5) ∗ pipeRef γp w q ∗
  isLock γkl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (P' : UPtd),
    ⌜calleeSaved k.regs R' ∧ V.upt.ext P' ∧ pipeRwRet n (R' 10#5)⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    pipeRef γp w q -∗
    procPrivExtNoctxAt curCtx (procAddr j) pid V P' (viewFaulted V.upt P' M) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `pipewrite`. -/
structure PIPEWRITE : Prop where
  wp_pipewrite : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γl : GName) (γp : PipeNames) (w : Bool) (q : Qp)
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int)
    hj hproc hK hsie hnoff hlocks htier hn hn',
    wp_pipewrite_body (hlc := hlc) (GF := GF) Γ cpu k γl γp w q γkl γk j pid V M n
      hj hproc hK hsie hnoff hlocks htier hn hn'

end Xv6
