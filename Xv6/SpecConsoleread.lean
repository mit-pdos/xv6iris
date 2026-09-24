/-
Specification of `consoleread` (kernel/console.c): a user `read()` from
the console -- up to `n` bytes of one input line, copied out one at a time,
sleeping on `&cons.r` under `cons.lock` while the ring is empty; `-1` if
the process is killed while waiting.

The running thread is proc `j` with a user destination (`user_dst != 0`,
the only caller being `fileread`); its private view may fault pages in
and is written at `dst` (`umemUntouched` bounds the damage to the `d`
bytes delivered, as `piperead`'s contract does).  Stack: the 12-slot
frame over `either_copyout`'s 58.

Imports only definitional files.
-/
import MachCSL.CallConv
import Xv6.Image
import Xv6.ConsoleDefs
import Xv6.KallocDefs
import Xv6.SchedCtx
import Xv6.UMem
import Xv6.UMemWindow
import Xv6.SpecEitherCopyout
import Xv6.SpecSleep

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `consoleread`. -/
def consolereadAddr : BitVec 64 := KA.«consoleread»

/-- The stack `consoleread`'s cone needs: its 12-slot frame over `either_copyout`'s. -/
def consolereadSlots : Nat := 12 + eitherCopyoutSlots

/-- `consoleread`'s result for `d` bytes delivered: `-1` (the process was
killed while waiting -- possibly after some bytes were delivered) or `d`. -/
def consReadRet (d : Nat) (r : BitVec 64) : Prop :=
  r = -1#64 ∨ r = BitVec.ofInt 64 d

/-- **WP of `consoleread`.**  `a0 = user_dst` (nonzero), `a1 = dst`, `a2 = n`. -/
def wp_consoleread_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γc : GName)
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : consolereadSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) (huser : k.regs 10#5 ≠ 0#64)
    (hn : k.regs 12#5 = BitVec.ofInt 64 n) (hn' : -2 ^ 31 ≤ n ∧ n < 2 ^ 31) : Prop :=
  kctx cpu k ∗ pcIs cpu consolereadAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  isConsLock γc ∗
  isLock γkl kmemLockAddr "kmem" (kmemRes γk) ∗ kallocAvail γk none ∗
  procPrivNoctxAt curCtx (procAddr j) pid V M ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (P' : UPtd)
    (M' : Nat → List (BitVec 8)) (d : Nat),
    ⌜calleeSaved k.regs R' ∧ V.upt.ext P' ∧ (d : Int) ≤ max 0 n ∧ consReadRet d (R' 10#5) ∧
      UMemL.umemUntouched (viewFaulted V.upt P' M) M' (k.regs 11#5) d⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    procPrivExtNoctxAt curCtx (procAddr j) pid V P' M' -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `consoleread`. -/
structure CONSOLEREAD : Prop where
  wp_consoleread : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γc : GName)
    (γkl : GName) (γk : KmemNames) (j : Nat) (pid : BitVec 32)
    (V : ProcPriv) (M : Nat → List (BitVec 8)) (n : Int) hj hproc hK hsie hnoff hlocks htier huser hn hn',
    wp_consoleread_body (hlc := hlc) (GF := GF) Γ cpu k γc γkl γk j pid V M n hj hproc hK hsie hnoff hlocks htier huser hn hn'

end Xv6
