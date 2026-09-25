/-
`usertrap()`'s syscall-arm stage file 0: **THE SYSCALL CONTRACT WITH THE
KSTACK ROW** (`SYSCALLKS`).

`SpecSyscall.SyscRows` has no `kstack` row, but the trap residue after the
dispatch needs `V'.kstack = V.kstack` (UtRows0.ks, the ksp pin
`V.kstack + 4096 = ksp`, kexit's closer), and nothing persistent ties the
block's `p->kstack` cell (UsertrapRes deviation 4 dropped Rocq's
`is_kstack`).  `syscallPostKs` is `SpecSyscall.syscallPost` with ONE extra
pure premise `⌜V'.kstack = V.kstack⌝` right after the rows; `SYSCALLKS` is
`SYSCALL` at it.

REPORTED edit (SpecSyscall): add the field `ks : V'.kstack = V.kstack` to
`SyscRows` (every arm builds `V'` by record update, so W8-E2 discharges it
by `rfl`); after it `SYSCALLKS` is `SYSCALL` (the premise is `rows.ks`).

Definitional only.
-/
import Xv6.SpecSyscall

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section Contract
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
  [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
  [Appcfg GF] [FileG GF] [SG : UexecSG GF] [Fscfg] [Icfg] [CurCtx]

/-- `SpecSyscall.syscallPost` with the kstack row. -/
def syscallPostKs (PT : SchedNames → IProp GF) (Γ : SchedNames) (k : KCtx) (γ : FileNames)
    (j : Nat) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (sts : List FdState)
    (gn : GName) (cs : ExtTreeSet GName compare) (ip : BitVec 64) (f : UexecSG.sfam GF) :
    CPU → IProp GF := fun cpu' =>
  iprop(∀ (spie spp : Bool) (R' : RegMap) (V' : ProcPriv) (M' : Nat → List (BitVec 8))
      (sts' : List FdState) (cs' : ExtTreeSet GName compare),
    ⌜calleeSaved k.regs R'⌝ -∗ ⌜SyscRows V M V' M' sts sts' cs cs' pid⌝ -∗ ⌜V'.kstack = V.kstack⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrsExt cpu' k.sie -∗ cpuClaimExt cpu' k.sie k.proc -∗
    bslots 3 -∗ syscInitId ip -∗ fdSlots FDSPARE -∗ irefSlots IREFSPARE -∗
    syscallEnv (hlc := hlc) PT Γ γ -∗
    procPrivFd γ (procAddr j) pid V' M' -∗ fdFrags V.fdg sts' -∗ chFrag V.chg (procAddr j) cs' -∗
    syscExecOut (hlc := hlc) V M V' M' sts sts' gn cs pid -∗
    syscSysOut (hlc := hlc) f V M sts gn cs pid (syscA0 V') (syscImg V' M') sts' V'.cwi cs' -∗
    syscForkOut f V (syscA0 V') cs cs' -∗
    syscWaitOut V M (syscImg V' M') (syscA0 V') cs cs' pid -∗
    wpLoop cpu')

/-- `SpecSyscall.wp_syscall_body` at `syscallPostKs`. -/
def wp_syscall_bodyKs (PT : SchedNames → IProp GF) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γw : GName) (γ : FileNames) (j : Nat) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (sts : List FdState) (gn : GName) (cs : ExtTreeSet GName compare)
    (ip : BitVec 64) (f : UexecSG.sfam GF)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : syscallSlots ≤ k.avail)
    (hnoff : k.noff = 0) (htier : k.tier = KTier.kpt) (hgn : gn = V.gen) : Prop :=
  kctx cpu k ∗ pcIs cpu syscallAddr ∗ procsInv Γ ∗
  trapCsrsExt cpu k.sie ∗ cpuClaimExt cpu k.sie k.proc ∗
  isLock γw waitLockAddr "wait_lock" waitLockPay ∗
  bslots 3 ∗ syscInitId ip ∗ fdSlots FDSPARE ∗ irefSlots IREFSPARE ∗
  syscallEnv (hlc := hlc) PT Γ γ ∗
  procPrivFd γ (procAddr j) pid V M ∗ fdFrags V.fdg sts ∗ chFrag V.chg (procAddr j) cs ∗
  syscSysIn (hlc := hlc) f V M sts gn cs pid ∗ syscForkIn (hlc := hlc) f V M sts ∗
  syscPayIn f V ∗
  (wpNext true k.proc cpu (syscallPostKs (hlc := hlc) PT Γ k γ j pid V M sts gn cs ip f) ∧
    syscallCloser k V)
  ⊢ wpLoop (GF := GF) cpu

end Contract

/-- `SpecSyscall.SYSCALL` at `wp_syscall_bodyKs` (identical binders). -/
structure SYSCALLKS : Prop where
  wp_syscall : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF]
    [BioslotG GF] [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF]
    [IregG GF] [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF]
    [CtokG GF] [WchG GF] [Appcfg GF] [FileG GF] [UexecSG GF] [Fscfg] [Icfg] [CurCtx]
    (PT : SchedNames → IProp GF) [∀ Γ, Persistent (PT Γ)] (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γw : GName) (γ : FileNames) (j : Nat) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (sts : List FdState) (gn : GName) (cs : ExtTreeSet GName compare)
    (ip : BitVec 64) (f : UexecSG.sfam GF) hj hproc hK hnoff htier hgn,
    wp_syscall_bodyKs (hlc := hlc) (GF := GF) PT Γ cpu k γw γ j pid V M sts gn cs ip f
      hj hproc hK hnoff htier hgn

end Xv6
