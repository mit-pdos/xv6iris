/-
Specification of `log_write` (kernel/log.c): the public contract.
Mirrors Rocq `SpecLogWrite.v`.

    void log_write(struct buf *b) {
      int i;
      acquire(&log.lock);
      if (log.lh.n >= LOGSIZE || log.lh.n >= log.size - 1)
        panic("too big a transaction");
      if (log.outstanding < 1) panic("log_write outside of trans");
      for (i = 0; i < log.lh.n; i++)
        if (log.lh.block[i] == b->blockno) break;   // log absorption
      log.lh.block[i] = b->blockno;
      if (i == log.lh.n) { bpin(b); log.lh.n++; }
      release(&log.lock);
    }

ONE UNIT OF THE CALLER'S RESERVATION IS SPENT UNCONDITIONALLY, and the
block's logged content becomes the bytes the caller wrote.  The two panic
arms are both dead: the sum tie `n + opSum om ≤ LOGBLOCKS` in
`Xv6.logResAt` kills "too big a transaction", and an op token in hand
forces `out ≥ 1`, killing "log_write outside of trans".

THE APPEND RECEIPT (`Xv6.logOpSw`): the op's own ledger entry with a NAME
for its birth epoch, and the witness `Xv6.loggedAt` for the block it just
logged, minted at exactly that epoch -- the currency the ABSORPTION CREDIT
(`Xv6.logCredit`) is later spent against.  The caller's anchor `v` comes
in as a lower bound and rides out ordered against the entry's epoch;
a caller with no receipt to build passes `v := 0`.

**Two deviations, both the log port's standing ones.**  (1) Rocq's
contract moves the byte view (`fsblock (fs_bytes γfs)`); this port has no
byte view, so the block's content moves at the CACHE level
(`Xv6.fsChalf`), which is the pre-byte-view Rocq shape.  (2) The `bpin`
the append arm performs yields this port's `Xv6.bref` -- a token indexed
by the BUFFER SLOT -- and the batch has nowhere to put it: Rocq's pin is
the `bv_dirty` half of the block's travelling payload, a hook this port's
`Xv6.BioView` does not have (see `Xv6/SpecInstallTrans.lean`'s header).
The contract below states the pin as Rocq does -- the log-side pin flips
to `true` -- and `log_write` is therefore stated, not proved: the append
arm cannot be closed until the hook exists.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.LogInv
import Xv6.SpecBpin
import Xv6.SpecPanic
import Xv6.SpecAcquire
import Xv6.SpecRelease

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `log_write`. -/
def logWriteAddr : BitVec 64 := KA.«log_write»

/-- `log_write`'s frame over its deepest callee, `panic`. -/
def logWriteSlots : Nat := 4 + panicSlots

/-- **WP of `log_write(b = a0)`**. -/
def wp_log_write_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γl : GName) (γb : BcacheNames) (V : BioView GF)
    (γfs : FsNames) (logstart : Nat) (dev : BitVec 32)
    (kk : Nat) (pidv bno : BitVec 32) (bs bsl bsd : List (BitVec 8)) (u v : Nat)
    (dqp : DFrac)
    (hK : logWriteSlots ≤ k.avail) (hnoff : k.noff + 2 < 2 ^ 31)
    (hlk : "log" ∉ k.locks) (hbc : "bcache" ∉ k.locks) (htier : k.tier = KTier.kpt)
    (hkk : kk < NBUF) (ha0 : k.regs 10#5 = bnode kk)
    (hdev : dev = V.dev) (hhome : fsHome V.cov logstart bno.toNat) : Prop :=
  kctx cpu k ∗ pcIs cpu logWriteAddr ∗
  bioCtx γl γb V ∗ logCtx γ γb γfs V.cov logstart dev ∗ panicEnv ∗
  logEpochLb γ v ∗
  wordPointsTo (pPid k.proc) 4 dqp pidv ∗
  -- the slot unit backing the (possible) bpin
  bslot γb ∗
  -- one unit of this operation's reservation, spent unconditionally
  logOp γ (u + 1) ∗
  -- the caller's own view of the block, at its OLD content
  fsChalf γfs bno.toNat bsl ∗
  -- the checked-out buffer, whose bytes the caller has typically edited
  bufHold0 γb V kk pidv dev bno bs bsd ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (Sb : List Nat),
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗
    wordPointsTo (pPid k.proc) 4 dqp pidv -∗
    -- the unit is gone, and the append receipt comes back
    logOpSw γ u Sb bno.toNat v -∗ logTx γ -∗
    -- the logged view of the block is now the bytes the caller wrote
    fsChalf γfs bno.toNat bs -∗
    -- ...and the log holds a pin on it
    fsDirtyHalf γfs bno.toNat true -∗
    bufHold0 γb V kk pidv dev bno bs bsd -∗
    -- the slot unit comes back UNCONDITIONALLY (the append path's n++
    -- releases a pool unit to replace the one bpin absorbed; the absorb
    -- path never takes one)
    bslot γb -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `log_write`. -/
structure LOG_WRITE : Prop where
  wp_log_write : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γl : GName) (γb : BcacheNames) (V : BioView GF)
    (γfs : FsNames) (logstart : Nat) (dev : BitVec 32)
    (kk : Nat) (pidv bno : BitVec 32) (bs bsl bsd : List (BitVec 8)) (u v : Nat) (dqp : DFrac)
    hK hnoff hlk hbc htier hkk ha0 hdev hhome,
    wp_log_write_body (hlc := hlc) (GF := GF) cpu k γ γl γb V γfs logstart dev kk pidv bno
      bs bsl bsd u v dqp hK hnoff hlk hbc htier hkk ha0 hdev hhome

end Xv6
