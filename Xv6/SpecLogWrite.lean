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
`Xv6.logResAt` kills "too big a transaction" (a unit in hand forces
`opSum om ≥ 1`, hence `lh.n ≤ LOGBLOCKS - 1`), and an op token against the
ledger authority forces `log.outstanding ≥ 1`, killing "log_write outside
of trans".

**`d` DECIDES WHICH PATH RUNS** (Rocq's `d`, the incoming payload's
polarity).  `d = false` -- the first `log_write` of this block in the
current batch: the block is appended to `lh.block[]`, `lh.n++`, and `bpin`
mints the pin that keeps the buffer un-evictable until `install_trans`
installs it.  `d = true` -- log ABSORPTION: the block is already in
`lh.block[]` (its dirty payload carries the earlier `bpin`'s reference),
so no `bpin` runs at all.  The caller does NOT choose: `d` is pinned by
the log's own pin half for the block, which is exactly the fact the scan
reads off `lh.block[]`.

NEITHER PATH COSTS THE CALLER A SLOT UNIT: `Xv6.bslot` goes in and comes
back out, unconditionally.  On the absorb path it is never spent; on the
append path `bpin` absorbs it and the `n++` releases one unit of the pool
parked in `Xv6.logStateAt` to replace it.

THE APPEND RECEIPT (`Xv6.logOpSw`): the op's own ledger entry with a NAME
for its birth epoch, and the witness `Xv6.loggedAt` for the block it just
logged, minted at exactly that epoch -- the currency the ABSORPTION CREDIT
(`Xv6.logCredit`) is later spent against.  The caller's anchor `v` comes
in as a lower bound and rides out ordered against the entry's epoch;
a caller with no receipt to build passes `v := 0`.

**Deviations from Rocq, reported.**

1. NO BYTE VIEW.  Rocq's contract moves `fsblock (fs_bytes γfs)`; this
   port has no byte view, so the block's content moves at the CACHE level
   (`Xv6.fsChalf`), which is the pre-byte-view Rocq shape.  There is
   likewise no atomic-update form (`wp_log_write_au_body`): with no byte
   view there is no invariant for the caller's half to live in.
2. NO ABSORPTION CREDIT ARGUMENT (`cr`).  Rocq hands the budget unit BACK
   on the credited absorb path (`log_opS γ (if cr then S u else u)`).
   This port always spends it -- which is sound for the same reason
   Rocq's `cr = false` instance is (the sum tie only ever improves) and is
   what `Xv6.logSpendStep` does on both arms; a credited caller simply
   pays a unit it need not have.  `Xv6.logCredit` and `Xv6.logCreditUse`
   stay where they are, unused by this contract, for the caller-side
   refund a later wave may want.
3. THE VIEW IS A PARAMETER.  Rocq runs the bio layer at
   `fs_view γfs γd dev cov` literally; this port keeps `V` a parameter and
   says the same thing with `hcl`/`hdt` (the `Xv6/SpecInstallTrans.lean`
   convention).
4. NO PANIC CREDENTIALS, AND THE FRAME IS ROCQ'S.  Both panic arms are
   refuted, and this port's `acquire` has no panic obligation of its own,
   so `Xv6.panicEnv` is not asked for and the budget is Rocq's
   `K_log_write = 18` (four slots over `bpin`'s fourteen), not `panic`'s.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import Xv6.LogInv
import Xv6.SpecBpin
import Xv6.SpecAcquire
import Xv6.SpecRelease

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `log_write`. -/
def logWriteAddr : BitVec 64 := KA.«log_write»

/-- `log_write`'s frame over its deepest callee, `bpin` (Rocq's
`K_log_write`): its own four slots over `bpin`'s fourteen. -/
def logWriteSlots : Nat := 4 + 14

/-- **WP of `log_write(b = a0)`**. -/
def wp_log_write_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [FsBlocksG GF] [LogG GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γ : LogNames) (γl : GName) (γb : BcacheNames) (V : BioView GF)
    (γfs : FsNames) (logstart : Nat) (dev : BitVec 32)
    (kk : Nat) (pidv bno : BitVec 32) (bs bsl bsd : List (BitVec 8)) (d : Bool) (u v : Nat)
    (hK : logWriteSlots ≤ k.avail) (hnoff : k.noff + 2 < 2 ^ 31)
    (hlk : "log" ∉ k.locks) (hbc : "bcache" ∉ k.locks) (htier : k.tier = KTier.kpt)
    (hkk : kk < NBUF) (ha0 : k.regs 10#5 = bnode kk)
    (hdev : dev = V.dev) (hcl : V.clean = fsMclean γfs) (hdt : V.dirty = fsMdirty γfs)
    (hhome : fsHome V.cov logstart bno.toNat) : Prop :=
  kctx cpu k ∗ pcIs cpu logWriteAddr ∗
  bioCtx γl γb V ∗ logCtx γ γb γfs V.cov logstart dev ∗
  logEpochLb γ v ∗
  -- the slot unit backing the (possible) bpin
  bslot γb ∗
  -- one unit of this operation's reservation, spent unconditionally
  logOp γ (u + 1) ∗
  -- the caller's own view of the block, at its OLD content
  fsChalf γfs bno.toNat bsl ∗
  -- the checked-out buffer, whose bytes the caller has typically edited,
  -- beside its travelling payload -- still indexed at `bsl` (Rocq's
  -- `bio_held`, which is `bio_locked` off its index)
  bufHold0 γb V kk pidv dev bno bs bsd ∗ bioPay γb V kk dev bno bsl bsd d ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (Sb : List Nat),
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗
    -- the unit is gone, and the append receipt comes back
    logOpSw γ u Sb bno.toNat v -∗ logTx γ -∗
    -- the logged view of the block is now the bytes the caller wrote
    fsChalf γfs bno.toNat bs -∗
    -- ...and the handle is re-indexed at those bytes and DIRTY: brelse-able
    bioLocked γb V kk pidv dev bno bs bsd true -∗
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
    (kk : Nat) (pidv bno : BitVec 32) (bs bsl bsd : List (BitVec 8)) (d : Bool) (u v : Nat)
    hK hnoff hlk hbc htier hkk ha0 hdev hcl hdt hhome,
    wp_log_write_body (hlc := hlc) (GF := GF) cpu k γ γl γb V γfs logstart dev kk pidv bno
      bs bsl bsd d u v hK hnoff hlk hbc htier hkk ha0 hdev hcl hdt hhome

end Xv6
