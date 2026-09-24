/-
Specification of `end_op` (kernel/log.c): the public contract.  Mirrors
Rocq `SpecEndOp.v`.

    void end_op(void) {
      int do_commit = 0;
      acquire(&log.lock);
      log.outstanding -= 1;
      if (log.committing) panic("log.committing");
      if (log.outstanding == 0) { do_commit = 1; log.committing = 1; }
      else wakeup(&log);
      release(&log.lock);
      if (do_commit) {
        commit();                      // INLINED: write_log, write_head,
                                       // install_trans(0), write_head
        acquire(&log.lock);
        log.committing = 0;
        log.ncommit++;
        wakeup(&log);
        release(&log.lock);
      }
    }

THE OPERATION IS RETIRED AND NOTHING LOG-SPECIFIC COMES BACK.  The token
in hand is what kills the `"log.committing"` panic (an op token forces
`out >= 1`, and `logResAt`'s `⌜cmt = true → out = 0⌝` then forces
`cmt = false`).

NO FS-FACING PREMISE, exactly as in Rocq after ruling 3: `end_op` is the
one place the durable state moves for a client, and the log proves for
itself what it moves to.  What Rocq additionally threads and this port
cannot -- the crash seam `fs_crash_seam`, the era certificate `gen_cert`
and the commit's durability fupds -- is dropped with the crash layer
(`Xv6/DiskInvDefs.lean` has no crash permits); the receipt `end_op` would
deposit in `log_flushed_bank` goes with it.

**BLOCKED, like `end_op`'s callee.**  `end_op`'s commit runs
`install_trans(0)`, whose commit arm is not provable against this port's
`Xv6.SpecBunpin` -- see the header of `Xv6/SpecInstallTrans.lean` for the
exact reason (the Lean pin token is slot-indexed, Rocq's is part of the
block's travelling payload).  This contract is stated, not proved.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.LogInv
import Xv6.SpecWriteHead
import Xv6.SpecInstallTrans
import Xv6.SpecWakeup
import Xv6.SpecAcquire
import Xv6.SpecRelease

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `end_op`. -/
def endOpAddr : BitVec 64 := KA.«end_op»

/-- `end_op`'s frame over its deepest callee (the inlined commit's
`bread`, through `write_head`/`install_trans`). -/
def endOpSlots : Nat := 6 + installTransSlots

/-- **WP of `end_op()`**. -/
def wp_end_op_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γl : GName) (γb : BcacheNames) (V : BioView)
    (γdl : GName) (γfs : FsNames) (pd pav pu : BitVec 64)
    (j : Nat) (logstart : Nat) (dev : BitVec 32) (u : Nat)
    (pidv : BitVec 32) (dqp : DFrac)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : endOpSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt)
    (hgeom : logGeomOk V.cov logstart) (hdev : dev = V.dev) (hpd : descPageRw pd) : Prop :=
  kctx cpu k ∗ pcIs cpu endOpAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  bioCtx γl γb V ∗ diskCaps V.gd γdl pd pav pu ∗ panicEnv ∗
  logCtx γ γb γfs V.cov logstart dev ∗
  wordPointsTo (pPid k.proc) 4 dqp pidv ∗
  logOp γ u ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
    ⌜calleeSaved k.regs R'⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    wordPointsTo (pPid k.proc) 4 dqp pidv -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `end_op`. -/
structure END_OP : Prop where
  wp_end_op : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γl : GName) (γb : BcacheNames) (V : BioView)
    (γdl : GName) (γfs : FsNames) (pd pav pu : BitVec 64)
    (j : Nat) (logstart : Nat) (dev : BitVec 32) (u : Nat) (pidv : BitVec 32) (dqp : DFrac)
    hj hproc hK hsie hnoff hlocks htier hgeom hdev hpd,
    wp_end_op_body (hlc := hlc) (GF := GF) Γ cpu k γ γl γb V γdl γfs pd pav pu j
      logstart dev u pidv dqp hj hproc hK hsie hnoff hlocks htier hgeom hdev hpd

end Xv6
