/-
Specification of `sys_sync` (kernel/sysfile.c): the public contract.
Mirrors Rocq `SpecSysSync.v`.

    uint64 sys_sync(void) {
      int n;
      acquire(&log.lock);
      n = log.ncommit;
      while (log.outstanding > 0 || log.committing || n == log.ncommit)
        sleep(&log, &log.lock);       // (the C waits for a commit to pass)
      release(&log.lock);
      return 0;
    }

**THE RECEIPT IS GONE IN THIS PORT.**  Rocq's contract is the DURABILITY
form: the caller hands in its invocation-time batch witness
`log_epoch_lb γ e` and gets `flushed_sync γ e` back -- "the batch counter
had reached some `e'` at or past yours, and here is the durable state
standing there".  That receipt is `FsFlushed.flushed`, a lower bound on
the CRASH RECORD's monotone history, and it is produced by
`LogInv.log_res`'s banked copy `log_flushed_bank`.  This port has no crash
record, no durable epoch registry and therefore no bank (see
`Xv6/LogInv.lean`'s header), so the contract below keeps the witness --
which is free, persistent and constrains no caller -- and returns only the
machine half: `a0 = 0`.  What `sys_sync` proves here is that it runs, not
that anything is durable.  Restoring the receipt needs the crash layer,
not the log layer.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.LogInv
import Xv6.SpecSleep
import Xv6.SpecAcquire
import Xv6.SpecRelease

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

/-- Address of `sys_sync`. -/
def sysSyncAddr : BitVec 64 := KA.«sys_sync»

/-- `sys_sync`'s frame over its deepest callee, `sleep`. -/
def sysSyncSlots : Nat := 4 + sleepSlots

/-- **WP of `sys_sync()`**. -/
def wp_sys_sync_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γb : BcacheNames) (V : BioView GF)
    (γfs : FsNames) (j : Nat) (logstart : Nat) (dev : BitVec 32) (e : Nat)
    (pidv : BitVec 32) (dqp : DFrac)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : sysSyncSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu sysSyncAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  logCtx γ γb γfs V.cov logstart dev ∗
  -- the caller's batch witness: persistent, and free at zero
  logEpochLb γ e ∗
  wordPointsTo (pPid k.proc) 4 dqp pidv ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = 0#64⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    wordPointsTo (pPid k.proc) 4 dqp pidv -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- **The eb-generic form** (Rocq `SpecSysSync.v`: `cpu_own 0 eb`, the
complement `trap_csrs_ext` / `cpu_claim_ext` in and out, the crossing the
literal `true`; depth 0, so no spinlock held by `KCtx.wf`).  At `sie = true`
sys_sync's own `acquire(&log.lock)` mints the bundle the interior sleep
needs and the caller brings nothing; at `sie = false` the caller brings it. -/
def wp_sys_sync_eb_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γb : BcacheNames) (V : BioView GF)
    (γfs : FsNames) (j : Nat) (logstart : Nat) (dev : BitVec 32) (e : Nat)
    (pidv : BitVec 32) (dqp : DFrac)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : sysSyncSlots ≤ k.avail)
    (hnoff : k.noff = 0)
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu sysSyncAddr ∗ procsInv Γ ∗
  trapCsrsExt cpu k.sie ∗ cpuClaimExt cpu k.sie k.proc ∗
  logCtx γ γb γfs V.cov logstart dev ∗
  logEpochLb γ e ∗
  wordPointsTo (pPid k.proc) 4 dqp pidv ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = 0#64⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrsExt cpu' k.sie -∗ cpuClaimExt cpu' k.sie k.proc -∗
    wordPointsTo (pPid k.proc) 4 dqp pidv -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `sys_sync`. -/
structure SYS_SYNC : Prop where
  wp_sys_sync_eb : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γb : BcacheNames) (V : BioView GF)
    (γfs : FsNames) (j : Nat) (logstart : Nat) (dev : BitVec 32) (e : Nat)
    (pidv : BitVec 32) (dqp : DFrac) hj hproc hK hnoff htier,
    wp_sys_sync_eb_body (hlc := hlc) (GF := GF) Γ cpu k γ γb V γfs j logstart dev e pidv dqp
      hj hproc hK hnoff htier

/-- The interrupts-off instance of `wp_sys_sync_eb` (the complement is the
whole bundle). -/
theorem SYS_SYNC.wp_sys_sync (A : SYS_SYNC) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    [Xv6G GF] [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γb : BcacheNames) (V : BioView GF)
    (γfs : FsNames) (j : Nat) (logstart : Nat) (dev : BitVec 32) (e : Nat)
    (pidv : BitVec 32) (dqp : DFrac) hj hproc hK hsie hnoff hlocks htier :
    wp_sys_sync_body (hlc := hlc) (GF := GF) Γ cpu k γ γb V γfs j logstart dev e pidv dqp
      hj hproc hK hsie hnoff hlocks htier := by
  have h := A.wp_sys_sync_eb (hlc := hlc) (GF := GF) Γ cpu k γ γb V γfs j logstart dev e pidv dqp
    hj hproc hK hnoff htier
  unfold wp_sys_sync_eb_body at h
  unfold wp_sys_sync_body
  rw [hsie] at h
  simp only [trapCsrsExt_false, cpuClaimExt_false] at h
  iintro ⟨H0, H1, H2, Htc, Hcl, Hir, H6, H7, H8, Hnext⟩
  iapply h
  iframe H0 H1 H2 Htc Hcl Hir H6 H7 H8
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK %spie %spp %R' %p0 H1 H2 ⟨Htc, Hir⟩ Hcl H6
  iapply HK $$ %spie %spp %R' %p0 H1 H2 Htc Hcl Hir H6

end Xv6
