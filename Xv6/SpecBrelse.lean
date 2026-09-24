/-
Specification of `brelse` (kernel/bio.c): the public contract.  Mirrors Rocq
`SpecBrelse.v`.

    void brelse(struct buf *b) {
      if (!holdingsleep(&b->lock)) unreachable("brelse");
      releasesleep(&b->lock);
      acquire(&bcache.lock);
      b->refcnt--;
      if (b->refcnt == 0) { <unlink b; splice after head> }
      release(&bcache.lock);
    }

The end of a `bread`..`brelse` chain: the locked buffer goes back, the
checkout token returns to the sleeplock as `releasesleep`'s `R`, the
reference is burned at the decrement, and the caller's `bslot` comes back
out.  The LRU rotate on the zero arm happens wholly inside the `bcache`
resource (`bcacheLru_unlink` then `bcacheLru_splice`).

The `unreachable` arm is dead (token + `pid` agreement, as in `bwrite`).
The body calls `releasesleep`, which wakes every process sleeping on the
lock, so `wakeup`'s resource (`procsInv`) is threaded through.

**Deviation from Rocq (reported).**  Rocq's proof parks the buffer's
travelling content (`valid`, `dev`, the rw bundle and the block's image
fragment) back into the per-buffer ESCROW at the first instruction, so that
a waiter's `acquiresleep` finds it.  This port does not build the escrow
(see the header of `Xv6/BcacheInv.lean`), so the proof DISCARDS that part of
the handle instead.  The contract below is Rocq's verbatim -- nothing is
weakened or assumed here -- but the buffer-cache invariant it rests on is
weaker than Rocq's: a released buffer's content is not recoverable, which is
exactly what `bread` would need.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.BcacheInv
import Xv6.SpecReleasesleep

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `brelse`. -/
def brelseAddr : BitVec 64 := KA.«brelse»

/-- brelse's 4-slot frame over `releasesleep`'s cone. -/
def brelseSlots : Nat := 4 + releasesleepSlots

/-- **WP of `brelse(b = a0)`**. -/
def wp_brelse_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [CurCtx] (Γ : SchedNames)
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : BcacheNames) (γd : DiskNames) (kk : Nat)
    (pidv dev bno : BitVec 32) (dqp : DFrac) (bs bsd : List (BitVec 8))
    (hnoff : k.noff + 2 < 2 ^ 31) (hK : brelseSlots ≤ k.avail)
    (hlk : "bcache" ∉ k.locks) (hsl : "sleep lock" ∉ k.locks) (hp : "proc" ∉ k.locks)
    (htier : k.tier = KTier.kpt)
    (hkk : kk < NBUF) (ha0 : k.regs 10#5 = bnode kk) : Prop :=
  kctx cpu k ∗ pcIs cpu brelseAddr ∗ procsInv Γ ∗
  bioCtx γl γ ∗ wordPointsTo (pPid k.proc) 4 dqp pidv ∗
  bufHold0 γ γd kk pidv dev bno bs bsd ∗ bref γ kk ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wordPointsTo (pPid k.proc) 4 dqp pidv -∗
    bslot γ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `brelse`. -/
structure BRELSE : Prop where
  wp_brelse : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [CurCtx] (Γ : SchedNames)
    (cpu : CPU) (k : KCtx) (γl : GName) (γ : BcacheNames) (γd : DiskNames) (kk : Nat)
    (pidv dev bno : BitVec 32) (dqp : DFrac) (bs bsd : List (BitVec 8))
    hnoff hK hlk hsl hp htier hkk ha0,
    wp_brelse_body (hlc := hlc) (GF := GF) Γ cpu k γl γ γd kk pidv dev bno dqp bs bsd
      hnoff hK hlk hsl hp htier hkk ha0

end Xv6
