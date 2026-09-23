/-
The virtio disk's INVARIANT and its ghost state (the Rocq `DiskInv.v` /
`VirtioProto.v`, as far as this port carries them).  The lease proof
itself is `Xv6/DiskInv.lean`; this file is the vocabulary.

---------------------------------------------------------------------
THE TIERS.  `MachCSL/WpDma.lean` settles where a device's DMA footprint
must live: at the RAW HISTORY tier (`histBytes`), because a byte the disk
appends to is authored by `diskAgent` and `keyAt` can justify such an
entry at a context only through its clean arm.  So

* everything the device may READ or WRITE is owned by the INVARIANT at
  the raw tier -- `dmaOwn` (own 1, content unconstrained), `dmaOwnAt`
  (own 1 at a value), `dmaHalf`/`dmaHalfAt` (a half, which is all a DMA
  READ needs: a cell at ANY fraction pins the byte's top);
* everything the DRIVER reads or writes is owned by the lock payload at
  the CONTEXT tier (`wordAtN`), and a cell split in halves between the two
  (Rocq's `half_map` of control bytes) is a `ctxByte ξ a ½ v` on the
  payload side against a raw `↦ₕ{½}` on the invariant side -- the same
  ghost element, since `ctxByte` is `a ↦ₕ{dq} (e :: H)` plus a key.

---------------------------------------------------------------------
THE SHAPE.  `diskProto γ v` is indexed by the device's own state and is
what sits beside the device's mirror inside `devInvR`:

    diskProto γ v  =  ⌜cacheOk v⌝ ∗ imgCoupled γ v ∗ (DEAD ∨ ALIVE)

* `imgCoupled` is the block image: the ghost map's AUTHORITY, plus the
  pure clause that every block the driver holds a fragment of reads as
  the model says (`blockView` = the write-back cache overlaid on the
  durable image).  The authority alone cannot move a block: an update
  needs the fragment too, and the fragment of an in-flight request's
  block is DEPOSITED in that request's row.  So a block at rest is
  frozen, and the device can only move the block it is serving.
* the DEAD arm is the pre-`virtio_disk_init` world: the invariant holds
  its half of the configuration ghost, the device is not live, and
  nothing is in flight.  Every DMA-write obligation is vacuous there,
  because each one is guarded on a request being in flight.  It carries
  three further clauses that the LIVE FLIP consumes
  (`Xv6.diskProto_flip`): no serve permit records an armed receipt
  (`permOk pm (fun _ => .inactive)`), and `v.usedIdx = 0`, `v.seen = 0`.
  All three are stable: a permit is only ever taken in the live world, and
  the two counters move only in `Virtio.complete` and in `Virtio.body`'s
  live branch, both of which carry a frozen configuration that refutes
  this arm (`Xv6.diskProto_complete`, `Xv6.diskProto_pop_live`).
* the ALIVE arm freezes the configuration: `diskCfgFrozen γ c0` is
  persistent, so once the driver has persisted its half the device's
  `v.cfg` is `c0` in every later state -- which is what makes the
  addresses `c0.desc`/`c0.avail`/`c0.used` of a DMA write a function of
  the state at the write, and what makes a post-init RESET unprovable on
  the driver's side (Rocq's `cfg` dfrac_agree, ½ pre-live / frozen after).

`diskLive` holds, per descriptor index `i < NUM`:

* the invariant's half of the RECEIPT `γ.head i` (`HState`: `.inactive`
  for a free descriptor, `.active c` for the head of the formatted chain
  `c`); the driver holds the other half as `headTok`;
* when armed, `chainLease`: HALVES of the chain's three descriptor words
  and of the three fields of its request header (the device only reads
  those, and a half pins them -- the header is kept as the 4/4/8 pieces
  the device's `fetch` actually reads, so no byte-range splitting is
  needed at a read), OWN 1 of the status byte, OWN 1 of each of the two
  sectors of `b->data`, and the block's image fragment;
* when FREE, NOTHING (`headRes .inactive = emp`).  The queue accounting
  below says a pop only ever lands on a PUBLISHED position, whose head is
  armed, so a `serve` task never meets a free descriptor and the invariant
  need hold nothing there.  The driver keeps the whole zeroed descriptor
  at the context tier, which is what makes `free_desc` four ordinary
  stores.

and, once:

* the USED-INDEX WRITE LOG (`usedIdxCell`, `usedOk`, `doneAuth`,
  `dlTops`): the device's writes of `used->idx` in order, each with the
  counter it published, the position of the write in the store order, and
  the descriptor head whose completion it reported.  It is what makes the
  handler's racy read of that cell say anything (`Xv6.usedIdx_read`);
* the SERVE PERMITS (`permAuth`/`permTok`): the POP mints one for the task
  it forks, and the task holds it to its last step, so the receipt of the
  head it is serving cannot move under it.  A permit records a CHAIN, so
  `permOk` says its head is ARMED with that chain -- which is what lets
  the driver arm a head it holds free (`disk_publish`) without having to
  chase outstanding permits;
* the whole used ring (`usedLease`), a half of `avail->idx` and of the
  eight ring cells (`availLease`), the completion counter `nc` as a
  mono-nat authority with `v.usedIdx = wrap16 nc`, and the coupling
  `inflightOk v st`;
* THE QUEUE ACCOUNTING (`Xv6/VirtioQueue.lean`): the pop counter `lo`
  with `v.seen = wrap16 lo`, the published count `np` with `lo ≤ np`,
  `queueOk st ring lo np` (every position in `[lo, np)` names an ARMED
  descriptor at ring cell `p % NUM`, and distinct positions name distinct
  descriptors -- so `np ≤ lo + NUM` by pigeonhole), `posOk pmap ring lo np`
  (the published heads, in a MONOTONE LIST from which a persistent
  per-position record `posRec` may be taken at any time), and
  `stageOk stg ring lo np` (what the ring-cell store established for the
  `avail->idx` bump that follows it).

---------------------------------------------------------------------
HOW THE ACCOUNTING IS MAINTAINED AGAINST THE DEVICE.  The pop reads
`avail->idx` at one state and changes `seen` at another, so the fact it
needs -- `lo < np` -- has to cross device steps.  Two mechanisms carry it:

* the DEVICE'S ROOT TASK holds the other half of `lo` for the whole of its
  loop (`diskRoot`, `MachCSL.DevSig.LeaseV`'s `Cr`), so `v.seen` cannot
  move under it and the `lo` it read at its first `get` is still the
  invariant's at the pop;
* the `avail->idx` read leaves PERSISTENT facts behind -- `diskPubLb`
  (`np` is monotone) and `posRec` (a published position is never
  republished) -- through `MachCSL.DevM.LeaseV.dmaReadV`, the read arm
  whose postcondition may depend on the value pinned
  (`MachCSL/WpDevDmaStepV.lean`).

---------------------------------------------------------------------
WHAT IS NOT HERE, AND WHY.

* No PER-COMPLETION ROWS on the completion side: the used-ring ELEMENT the
  device wrote at each position, the completed request's status byte at a
  known value, and the `topLb` bound on that request's DATA writes.  The
  used-index cell's WRITE LOG is here (see below), and with it the
  per-completion record `doneRec`/`headDone` and the handler's credential
  `diskWm`; the rows are what the last three accessors of
  `Xv6/DiskAcc.lean` still wait on.  The invariant now KNOWS the handler
  watermark (`diskReadAt` is a ghost PAIR: the payload's half and
  `diskReadAtAuth` inside the dead and live arms) and the exact PHASE of
  every in-flight request (`permOk`, below), which is what the rows are
  built on; the rows themselves, the window bound `dl.length - nr ≤ NUM`
  and the one clause they all hang off -- "an in-flight head is at no
  published, unpopped position" -- are still to come.  The section head
  of `Xv6/DiskAcc.lean` sets the design out in full.
* The CONTENT of a disk read's data transfer is existential (`dmaOwn`,
  not `dmaOwnAt`).  The device computes the payload from a SNAPSHOT of its
  image taken at the task's `get` and writes it several steps later.  The
  bytes themselves are not the problem -- a DMA write may re-choose the
  invariant's existential witness, so `bufLease` can be kept at values --
  the COUPLING to `Xv6.diskBlock` is: it needs the clause "an in-flight
  READ chain's image fragment is `blockView v c.blk`".
* No crash permits, no `Q`, no `disk_seq_permit` (the port drops Rocq's
  crash story), and no TSO floor rows (`fl0`/`fl1`/`flr`/`pos`).
-/
import Xv6.VirtioQueue
import Xv6.KallocDefs
import MachCSL.WpDevDma
import MachCSL.WordHist

namespace Xv6

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL

/-! ## The ghost libraries -/

/-- The ghost libraries the disk needs beyond `Xv6G` (Rocq's `diskG`). -/
class DiskG (GF : BundledGFunctors) where
  /-- the frozen configuration (`VirtioProto.v`'s `cfg`) -/
  [gvCfgG : GhostVarG GF VirtioCfg]
  /-- the per-descriptor receipt -/
  [gvHeadG : GhostVarG GF HState]
  /-- the staged head, between the ring store and the `avail->idx` bump -/
  [gvStageG : GhostVarG GF (Option Nat)]
  /-- the block image -/
  [gmImgG : GhostMapG GF Nat (List (BitVec 8)) RegMapF]
  /-- the completion counter -/
  [mnG : MonoNatG GF]
  /-- the SERVE PERMITS (see `permTok`) -/
  [gmPermG : GhostMapG GF Nat (BitVec 16 × Chain × Option VPhase × Option (BitVec 16)) RegMapF]
  /-- the PUBLISHED POSITIONS (see `posRec`): a monotone list of heads,
  one entry per position, from which a persistent per-position record may
  be taken at any time -/
  [mlPosG : MonoListG GF Nat]
  /-- the COMPLETION RECORDS (see `doneRec`): the lagging monotone list of
  the device's used-index writes -/
  [mlDoneG : MonoListG GF (Nat × Nat × Nat)]

attribute [reducible, instance] DiskG.gvCfgG DiskG.gvHeadG DiskG.gvStageG DiskG.gmImgG DiskG.mnG
attribute [reducible, instance] DiskG.gmPermG
attribute [reducible, instance] DiskG.mlPosG DiskG.mlDoneG

/-- The disk's ghost names (Rocq's `disk_names`, the subset this port
carries). -/
structure DiskNames where
  /-- the configuration: halves before the device is live, frozen after -/
  cfg : GName
  /-- the block image: a ghost map `blockno ↦ BSIZE bytes` -/
  img : GName
  /-- one receipt per descriptor index -/
  head : Nat → GName
  /-- the published count (`avail->idx`) -/
  np : GName
  /-- the largest counter a reader has cashed out of the used-index cell's
  write log, a mono-nat (it LAGS the device's own count) -/
  nc : GName
  /-- the POPPED count (the device's `seen`): halves, the DEVICE ROOT
  LOOP's own resource on one side and the invariant on the other, so
  `seen` cannot move without the root's half -/
  lo : GName
  /-- the handler watermark (`disk.used_idx`) -/
  nr : GName
  /-- the head staged between the ring store and the index bump -/
  stage : GName
  /-- the serve permits -/
  perm : GName
  /-- the published count AGAIN, as a MONOTONE counter: `np` only grows,
  and a persistent lower bound on it is the only thing that can carry
  "the available index was past `lo` when I read it" from the read to the
  pop several device steps later -/
  npm : GName
  /-- the published POSITIONS, as a monotone list: entry `p` is the
  descriptor head published at position `p`, immutable once appended -/
  pos : GName
  /-- the device's used-index WRITES, as a lagging monotone list -/
  done : GName
  /-- the bound on the stores that zeroed the used page before the flip -/
  base : GName

/-- The disk invariant's namespace. -/
def diskN : Namespace := ndot nroot "xv6disk"


section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]

/-! ## The raw tier: what a lease is made of -/

/-- The footprint at FULL ownership, content unconstrained: what the
device may WRITE. -/
def dmaOwn (pa : PAddr) (n : Nat) : IProp GF := iprop%
  ∃ Hs : Nat → Hist, histBytes pa n (fun _ => DFrac.own 1) Hs

/-- The footprint at full ownership, at a value. -/
def dmaOwnAt (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) : IProp GF := iprop%
  ∃ Hs : Nat → Hist, histBytes pa n (fun _ => DFrac.own 1) Hs ∗ ⌜headsAre Hs n w⌝

/-- A HALF of the footprint: all a DMA READ needs (a cell at any fraction
pins the byte's top), and what leaves the other half to the driver. -/
def dmaHalf (pa : PAddr) (n : Nat) : IProp GF := iprop%
  ∃ Hs : Nat → Hist, histBytes pa n (fun _ => DFrac.own (1 : Qp).half) Hs

/-- A half of the footprint, at a value: the invariant's side of a cell
the driver formats and the device reads. -/
def dmaHalfAt (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) : IProp GF := iprop%
  ∃ Hs : Nat → Hist, histBytes pa n (fun _ => DFrac.own (1 : Qp).half) Hs ∗ ⌜headsAre Hs n w⌝

instance dmaOwn_timeless (pa : PAddr) (n : Nat) : Timeless (dmaOwn (GF := GF) pa n) := by
  unfold dmaOwn; infer_instance
instance dmaOwnAt_timeless (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    Timeless (dmaOwnAt (GF := GF) pa n w) := by unfold dmaOwnAt; infer_instance
instance dmaHalf_timeless (pa : PAddr) (n : Nat) : Timeless (dmaHalf (GF := GF) pa n) := by
  unfold dmaHalf; infer_instance
instance dmaHalfAt_timeless (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    Timeless (dmaHalfAt (GF := GF) pa n w) := by unfold dmaHalfAt; infer_instance

theorem dmaOwnAt_dmaOwn (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    dmaOwnAt (GF := GF) pa n w ⊢ dmaOwn pa n := by
  unfold dmaOwnAt dmaOwn
  iintro ⟨%Hs, H, %_⟩
  iexists Hs
  iexact H

/-- **A leased footprint answers a DMA write**: full ownership of the
bytes is exactly `dmaWriteLease`, and what comes back is the same
footprint at the written value. -/
theorem dmaOwn_lease (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    dmaOwn (GF := GF) pa n ⊢ dmaWriteLease pa n w (dmaOwnAt pa n w) := by
  unfold dmaOwn dmaWriteLease dmaOwnAt
  iintro ⟨%Hs, Hb⟩
  iexists Hs
  iframe Hb
  iintro %t Hb2 _ _
  iexists (pushed Hs t diskAgent w)
  iframe Hb2
  ipureintro
  exact headsAre_pushed Hs t diskAgent n w

/-- The same, forgetting the value written. -/
theorem dmaOwn_lease' (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    dmaOwn (GF := GF) pa n ⊢ dmaWriteLease pa n w (dmaOwn pa n) := by
  unfold dmaOwn dmaWriteLease
  iintro ⟨%Hs, Hb⟩
  iexists Hs
  iframe Hb
  iintro %t Hb2 _ _
  iexists (pushed Hs t diskAgent w)
  iexact Hb2

/-- A cell over the whole footprint, at any fraction, pins a DMA READ. -/
theorem dmaHalfAt_pin (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (P : IProp GF)
    (Q : BitVec (8 * n) → Prop) (hQ : Q w) :
    dmaHalfAt pa n w ∗ (dmaHalfAt pa n w -∗ P) ⊢ dmaReadPin pa n Q P := by
  unfold dmaReadPin dmaHalfAt
  iintro ⟨⟨%Hs, Hb, %hh⟩, Hback⟩
  iright
  iexists (fun _ => DFrac.own (1 : Qp).half), Hs, w
  iframe Hb
  isplit
  · ipureintro; exact hh
  isplit
  · ipureintro; exact hQ
  iintro Hb2
  iapply Hback
  iexists Hs
  iframe Hb2
  ipureintro; exact hh

/-- **The lease, framed**: full ownership of the footprint plus the way
back into the client's state is exactly what a DMA write asks for. -/
theorem dmaOwn_lease_frame (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (Q : IProp GF) :
    dmaOwn pa n ∗ (dmaOwn pa n -∗ Q) ⊢ dmaWriteLease pa n w Q := by
  unfold dmaOwn dmaWriteLease
  iintro ⟨⟨%Hs, Hb⟩, Hback⟩
  iexists Hs
  iframe Hb
  iintro %t Hb2 _ _
  iapply Hback
  iexists (pushed Hs t diskAgent w)
  iexact Hb2

/-- The empty footprint is free. -/
theorem dmaOwn_zero (pa : PAddr) : emp ⊢@{IProp GF} dmaOwn pa 0 := by
  unfold dmaOwn histBytes
  iintro _
  iexists (fun _ => ([] : Hist))
  simp only [List.range_zero]
  exact BigSepL.bigSepL_nil_intro

/-- A zero-width DMA write asks for nothing. -/
theorem dmaWriteLease_zero (pa : PAddr) (n : Nat) (hn : n = 0) (w : BitVec (8 * n))
    (Q : IProp GF) : Q ⊢ dmaWriteLease pa n w Q := by
  subst hn
  iintro H
  iapply dmaOwn_lease_frame pa 0 w Q
  isplitl []
  · iapply dmaOwn_zero pa
    itrivial
  · iintro _
    iexact H


/-- Any answer will do: the trivial read obligation. -/
theorem dmaReadPin_any (pa : PAddr) (n : Nat) (P : IProp GF) :
    P ⊢ dmaReadPin pa n (fun _ => True) P := by
  unfold dmaReadPin
  iintro H
  ileft
  iframe H
  ipureintro
  intro _; trivial

/-! ## The ghost state -/

/-- The invariant's half of the configuration, before the device is live. -/
def diskCfgAuth (γ : DiskNames) (c : VirtioCfg) : IProp GF := γ.cfg ↪VAR{.own (1 : Qp).half} c
/-- The driver's half, which `virtio_disk_init` moves along with each
MMIO write and persists at the end. -/
def diskCfgOwn (γ : DiskNames) (c : VirtioCfg) : IProp GF := γ.cfg ↪VAR{.own (1 : Qp).half} c
/-- The configuration, frozen: persistent, and unique. -/
def diskCfgFrozen (γ : DiskNames) (c : VirtioCfg) : IProp GF := γ.cfg ↪VAR{.discard} c

instance diskCfgFrozen_persistent (γ : DiskNames) (c : VirtioCfg) :
    Persistent (diskCfgFrozen (GF := GF) γ c) := by unfold diskCfgFrozen; infer_instance

theorem diskCfgFrozen_agree (γ : DiskNames) (c c' : VirtioCfg) :
    diskCfgFrozen (GF := GF) γ c ∗ diskCfgFrozen γ c' ⊢ ⌜c = c'⌝ := by
  unfold diskCfgFrozen
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ.cfg _ _ _ _ $$ H1 H2
  ipureintro; exact h

/-- The invariant's half of the receipt of descriptor `i`. -/
def headAuth (γ : DiskNames) (i : Nat) (s : HState) : IProp GF :=
  γ.head i ↪VAR{.own (1 : Qp).half} s
/-- The DRIVER's half: `HInactive` travels with a free descriptor,
`HActive c` with a chain in flight (Rocq's `head` receipt). -/
def headTok (γ : DiskNames) (i : Nat) (s : HState) : IProp GF :=
  γ.head i ↪VAR{.own (1 : Qp).half} s

theorem headTok_agree (γ : DiskNames) (i : Nat) (s s' : HState) :
    headAuth (GF := GF) γ i s ∗ headTok γ i s' ⊢ ⌜s = s'⌝ := by
  unfold headAuth headTok
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree (γ.head i) _ _ _ _ $$ H1 H2
  ipureintro; exact h

/-- The block image's authority. -/
def imgAuth (γ : DiskNames) (m : RegMapF (List (BitVec 8))) : IProp GF := γ.img ↪●MAP m
/-- **The disk image fragment**: block `bno` holds `bs`.  Exclusive, so a
block only moves with its holder's consent; a request in flight deposits
it in the invariant's row for the duration of the transfer. -/
def diskBlock (γ : DiskNames) (bno : Nat) (bs : List (BitVec 8)) : IProp GF :=
  γ.img ↪◯MAP[bno] bs

theorem diskBlock_agree (γ : DiskNames) (m : RegMapF (List (BitVec 8))) (bno : Nat)
    (bs : List (BitVec 8)) :
    imgAuth (GF := GF) γ m ∗ diskBlock γ bno bs ⊢ ⌜PartialMap.get? m bno = some bs⌝ := by
  unfold imgAuth diskBlock
  iintro ⟨H1, H2⟩
  ihave %h := ghost_map_lookup $$ H1 H2
  ipureintro; exact h

/-- The largest counter the used-index cell has been seen at, as the
invariant holds it.  It LAGS the device's own count, because the device
cannot allocate ghost state: a reader cashes the counter it saw inside its
own view shift (`Xv6.diskDoneAuth_cash`). -/
def diskDoneAuth (γ : DiskNames) (n : Nat) : IProp GF :=
  MonoNat.auth_own γ.nc (DFrac.own 1) (.ofNat n)
/-- **The used index has been written to `wrap16 n`** (persistent): the
device has published at least `n` completions, so the used-ring elements
of positions `0 .. n-1` have been written. -/
def diskDoneLb (γ : DiskNames) (n : Nat) : IProp GF := MonoNat.lb_own γ.nc (.ofNat n)

instance diskDoneLb_persistent (γ : DiskNames) (n : Nat) :
    Persistent (diskDoneLb (GF := GF) γ n) := by unfold diskDoneLb; infer_instance

/-- The completion counter yields its persistent lower bound. -/
theorem diskDoneAuth_lb (γ : DiskNames) (n : Nat) :
    diskDoneAuth (GF := GF) γ n ⊢ |==> (diskDoneAuth γ n ∗ diskDoneLb γ n) := by
  unfold diskDoneAuth diskDoneLb
  iintro H
  imod MonoNat.own_update γ.nc (.ofNat n) (.ofNat n)
    (by simp only [MaxNat.le_toNat]; omega) $$ H with ⟨H1, H2⟩
  imodintro
  iframe H1 H2

/-- The published count: the lock payload's half. -/
def diskPubAuth (γ : DiskNames) (n : Nat) : IProp GF := γ.np ↪VAR{.own (1 : Qp).half} n
/-- The published count: the publisher's half (Rocq's `disk_pub`). -/
def diskPub (γ : DiskNames) (n : Nat) : IProp GF := γ.np ↪VAR{.own (1 : Qp).half} n
/-- The handler watermark (`disk.used_idx`), Rocq's `disk_read_at`: the
LOCK PAYLOAD's half.  It is split, not whole, because the PER-POSITION
ROWS of the completion side are indexed by `[nr, nc)`: the invariant has
to know how far the handler has read before it can say which used-ring
elements are still the handler's to collect.  So a bump needs both halves,
and goes through the invariant (`Xv6.disk_deposit`). -/
def diskReadAt (γ : DiskNames) (n : Nat) : IProp GF := γ.nr ↪VAR{.own (1 : Qp).half} n

/-- The handler watermark: the INVARIANT's half. -/
def diskReadAtAuth (γ : DiskNames) (n : Nat) : IProp GF := γ.nr ↪VAR{.own (1 : Qp).half} n

theorem diskReadAt_agree (γ : DiskNames) (n n' : Nat) :
    ⊢@{IProp GF} diskReadAtAuth γ n -∗ diskReadAt γ n' -∗ ⌜n = n'⌝ := by
  unfold diskReadAtAuth diskReadAt
  iintro H1 H2
  ihave %h := ghost_var_agree γ.nr _ _ _ _ $$ H1 H2
  ipureintro; exact h
/-- The head staged between the ring store and the `avail->idx` bump
(Rocq's `disk_stage`), the DRIVER's half.  It is split, not whole,
because the invariant has to remember what the ring store established:
that there was room for one more position, and that the staging cell
holds that head (`Xv6.stageOk`).  Neither fact can be recovered at the
`avail->idx` bump, where the head is no longer free. -/
def diskStage (γ : DiskNames) (s : Option Nat) : IProp GF := γ.stage ↪VAR{.own (1 : Qp).half} s

/-- The invariant's half of the staged head. -/
def diskStageAuth (γ : DiskNames) (s : Option Nat) : IProp GF :=
  γ.stage ↪VAR{.own (1 : Qp).half} s

theorem diskStage_agree (γ : DiskNames) (s s' : Option Nat) :
    ⊢@{IProp GF} diskStageAuth γ s -∗ diskStage γ s' -∗ ⌜s = s'⌝ := by
  unfold diskStageAuth diskStage
  iintro H1 H2
  ihave %h := ghost_var_agree γ.stage _ _ _ _ $$ H1 H2
  ipureintro; exact h

theorem diskStage_split (γ : DiskNames) (s : Option Nat) :
    ⊢@{IProp GF} (γ.stage ↪VAR{.own 1} s) -∗ (diskStageAuth γ s ∗ diskStage γ s) := by
  unfold diskStageAuth diskStage
  have h := ghost_var_split (GF := GF) γ.stage s (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem diskReadAt_update (γ : DiskNames) (n n' t : Nat) :
    diskReadAtAuth (GF := GF) γ n ∗ diskReadAt γ n' ⊢
      |==> (diskReadAtAuth γ t ∗ diskReadAt γ t) := by
  unfold diskReadAtAuth diskReadAt
  iintro ⟨H1, H2⟩
  iapply ghost_var_update_halves t γ.nr _ _ $$ H1 H2

theorem diskStage_update (γ : DiskNames) (s s' t : Option Nat) :
    diskStageAuth (GF := GF) γ s ∗ diskStage γ s' ⊢
      |==> (diskStageAuth γ t ∗ diskStage γ t) := by
  unfold diskStageAuth diskStage
  iintro ⟨H1, H2⟩
  iapply ghost_var_update_halves t γ.stage _ _ $$ H1 H2

/-! ## The pop counter

The device's `seen`, as a natural number, in ghost halves: the INVARIANT
holds one beside `⌜v.seen = wrap16 lo⌝`, and the DEVICE'S ROOT TASK holds
the other for the whole of its loop (`MachCSL.DevSig.LeaseL`'s `Cr`).  So
`lo` moves only at a step the root itself takes -- which is what turns
"the pop index has not moved since I read it" into agreement against a
half, and so lets the pop at `lo` use a fact the loop established several
steps earlier. -/

/-- The invariant's half of the pop counter. -/
def diskLoAuth (γ : DiskNames) (n : Nat) : IProp GF := γ.lo ↪VAR{.own (1 : Qp).half} n

/-- The root's half at a definite value. -/
def diskLoTok (γ : DiskNames) (n : Nat) : IProp GF := γ.lo ↪VAR{.own (1 : Qp).half} n

/-- **The device root task's own resource** (`Cr`): the other half of the
pop counter, held across every iteration of `Virtio.body`. -/
def diskRoot (γ : DiskNames) : IProp GF := iprop% ∃ n : Nat, diskLoTok γ n

theorem diskLoTok_root (γ : DiskNames) (n : Nat) : diskLoTok (GF := GF) γ n ⊢ diskRoot γ := by
  unfold diskRoot
  iintro H
  iexists n
  iexact H

theorem diskLo_agree (γ : DiskNames) (n n' : Nat) :
    ⊢@{IProp GF} diskLoAuth γ n -∗ diskLoTok γ n' -∗ ⌜n = n'⌝ := by
  unfold diskLoAuth diskLoTok
  iintro H1 H2
  ihave %h := ghost_var_agree γ.lo _ _ _ _ $$ H1 H2
  ipureintro; exact h

theorem diskLo_update (γ : DiskNames) (n n' m : Nat) :
    diskLoAuth (GF := GF) γ n ∗ diskLoTok γ n' ⊢ |==> (diskLoAuth γ m ∗ diskLoTok γ m) := by
  unfold diskLoAuth diskLoTok
  iintro ⟨H1, H2⟩
  iapply ghost_var_update_halves m γ.lo _ _ $$ H1 H2

/-! ## The published positions

`posRec γ p i` -- "position `p` was published with descriptor head `i`" --
is PERSISTENT and immutable: the published heads are a MONOTONE LIST, so a
per-position record may be taken out of the invariant's authority at any
time and kept for ever.  It is what carries the device's ring-cell read
forward: the root loop takes `posRec γ lo i` when it finds `avail->idx`
past `lo`, so the head the cell yields is a LEAN-LEVEL parameter of the
rest of the iteration, and the pop several steps later can match it
against the invariant's own row for position `lo`. -/

/-- The published heads, in order: the invariant's authority, WITH the
persistent snapshot beside it, so that a per-position record may be taken
out with no update at all (a DMA read pin has no room for one). -/
def posAuth (γ : DiskNames) (l : List Nat) : IProp GF := iprop%
  MonoList.auth_own γ.pos (DFrac.own 1) l ∗ MonoList.lb_own γ.pos l

/-- **Position `p` was published with head `i`** (persistent). -/
def posRec (γ : DiskNames) (p i : Nat) : IProp GF := MonoList.idx_own γ.pos p i

instance posRec_persistent (γ : DiskNames) (p i : Nat) :
    Persistent (posRec (GF := GF) γ p i) := by unfold posRec MonoList.idx_own; infer_instance

instance posAuth_timeless (γ : DiskNames) (l : List Nat) :
    Timeless (posAuth (GF := GF) γ l) := by unfold posAuth; infer_instance

theorem posRec_lookup (γ : DiskNames) (l : List Nat) (p i : Nat) :
    ⊢@{IProp GF} posAuth γ l -∗ posRec γ p i -∗ ⌜l[p]? = some i⌝ := by
  unfold posAuth posRec
  iintro H1 H2
  icases H1 with ⟨Ha, _⟩
  iapply MonoList.auth_idx_lookup γ.pos _ l p i $$ Ha H2

/-- **A record comes out for free**: the snapshot beside the authority is
persistent, so no update is needed. -/
theorem posRec_get (γ : DiskNames) (l : List Nat) (p i : Nat) (h : l[p]? = some i) :
    posAuth (GF := GF) γ l ⊢ posAuth γ l ∗ posRec γ p i := by
  unfold posAuth posRec
  iintro ⟨Ha, #Hlb⟩
  iframe Ha Hlb
  iapply MonoList.idx_own_get γ.pos p i h
  iexact Hlb

/-- PUBLISHING appends one head. -/
theorem posAuth_append (γ : DiskNames) (l : List Nat) (i : Nat) :
    posAuth (GF := GF) γ l ⊢ |==> posAuth γ (l ++ [i]) := by
  unfold posAuth
  iintro ⟨Ha, _⟩
  imod MonoList.auth_own_update_app γ.pos [i] $$ Ha with ⟨H1, #H2⟩
  imodintro
  iframe H1 H2

/-- Every published, unpopped position has its head recorded. -/
def posOk (l : List Nat) (ring : Nat → Nat) (lo np : Nat) : Prop :=
  l.length = np ∧ ∀ p, lo ≤ p → p < np → l[p]? = some (ring (p % NUM))

theorem posOk_pop (l : List Nat) (ring : Nat → Nat) (lo np : Nat) (h : posOk l ring lo np) :
    posOk l ring (lo + 1) np := ⟨h.1, fun p h1 h2 => h.2 p (by omega) h2⟩

theorem posOk_setcell (l : List Nat) (ring : Nat → Nat) (lo np x : Nat)
    (h : posOk l ring lo np) (hlt : np < lo + NUM) :
    posOk l (updN ring (np % NUM) x) lo np := by
  refine ⟨h.1, fun p h1 h2 => ?_⟩
  rw [updN_ne _ _ _ _ (ring_mod_ne lo np p h1 h2 hlt)]
  exact h.2 p h1 h2

theorem posOk_extend (l : List Nat) (ring : Nat → Nat) (lo np : Nat) (h : posOk l ring lo np) :
    posOk (l ++ [ring (np % NUM)]) ring lo (np + 1) := by
  refine ⟨by rw [List.length_append, h.1]; rfl, fun p h1 h2 => ?_⟩
  have hlen := h.1
  by_cases hpn : p = np
  · subst hpn
    rw [List.getElem?_append_right (by omega), hlen]
    simp
  · rw [List.getElem?_append_left (by omega)]
    exact h.2 p h1 (by omega)

/-! ## The completion side: the used-index cell's WRITE LOG

`used->idx` is written by the DEVICE alone, once per completion, and the
interrupt handler reads it racily.  A `dmaOwn` cell -- full ownership at an
UNCONSTRAINED value -- tells a read nothing, so the invariant keeps the
cell's HISTORY instead: a list of the writes so far, newest last, each
recorded as the counter it published and the POSITION of the write in the
store order (`UsedRec`).  What a racy read returns is then the first entry
of that list VISIBLE to the reader (`Xv6.usedIdx_read`), and two clauses
turn that into a number the handler can use:

* the counters never decrease along the log, so the entry a reader sees is
  at least as new as any entry its floor has passed -- that is how
  `disk.used_idx = nr` plus "the write that published `nr` is below my
  floor" (`Xv6.diskWm`) yields `nr ≤ m`;
* every counter is at most `nc + 1`, which bounds the answer.

The DEVICE cannot allocate ghost state: `MachCSL.dmaWriteLease`'s
continuation is a plain wand, with no update modality, so the used-index
write cannot append to a ghost list.  The per-write RECORDS are therefore
kept in a LAGGING monotone list (`doneAuth γ dl0` with `dl0 <+: dl`): the
device grows the real log `dl` alone, and any client with a view shift in
hand -- the handler's accessors -- catches the ghost list up and takes out
the persistent record it needs (`Xv6.doneAuth_sync`). -/

/-- One write of `used->idx`: the counter it published, the position of the
write in the store order, and the descriptor HEAD whose completion it
reported (the used-ring element of that position went with it). -/
abbrev UsedRec : Type := Nat × Nat × Nat

/-- The counter a log entry published. -/
abbrev UsedRec.cnt (r : UsedRec) : Nat := r.1
/-- The position of the write in the store order. -/
abbrev UsedRec.pos (r : UsedRec) : Nat := r.2.1
/-- The descriptor head whose completion the write reported. -/
abbrev UsedRec.hd (r : UsedRec) : Nat := r.2.2

/-- The word entry a used-index write leaves in the cell's history. -/
def usedEnt (r : UsedRec) : WEnt 2 := ⟨r.2.1, diskAgent, wrap16 r.1⟩

/-- The used-index cell's word history: the log, NEWEST FIRST. -/
def usedW (dl : List UsedRec) : WordHist 2 := (dl.map usedEnt).reverse

theorem usedW_nil : usedW [] = [] := rfl

theorem usedW_rev (dl : List UsedRec) : usedW dl = dl.reverse.map usedEnt := by
  unfold usedW; rw [List.map_reverse]

theorem usedW_snoc (dl : List UsedRec) (r : UsedRec) :
    usedW (dl ++ [r]) = usedEnt r :: usedW dl := by
  unfold usedW
  rw [List.map_append, List.reverse_append]
  rfl

/-- The tails under the log: nonempty, spelling `0`, at positions at most
`b` -- the stores that zeroed the used page before the flip. -/
def usedTailOk (b : Nat) (Hold : Nat → Hist) : Prop :=
  ∀ j, j < 2 → ∃ e H, Hold j = e :: H ∧ e.v = nthByte (0 : BitVec (8 * 2)) j ∧ e.t ≤ b

theorem usedTailOk_vals (b : Nat) (Hold : Nat → Hist) (h : usedTailOk b Hold) :
    tailVals 2 (0 : BitVec (8 * 2)) Hold :=
  fun j hj => let ⟨e, H, h1, h2, _⟩ := h j hj; ⟨e, H, h1, h2⟩

/-- **The log's bookkeeping.**  `dl` is the real write log, `dl0` the ghost
list that lags it, `M` the monotone counter a reader may cash, `nc` the
device's completion count. -/
def usedOk (dl dl0 : List UsedRec) (nc M : Nat) : Prop :=
  dl0 <+: dl ∧ (∀ r ∈ dl, r.1 ≤ nc + 1) ∧ M ≤ nc + 1 ∧
  dl.Pairwise (fun a c => a.1 ≤ c.1) ∧ (M = 0 ∨ ∃ r ∈ dl, M ≤ r.1)

theorem usedOk_nil (nc : Nat) : usedOk [] [] nc 0 :=
  ⟨List.prefix_rfl, fun r hr => absurd hr (by simp), by omega, List.Pairwise.nil, Or.inl rfl⟩

/-- The device's completion moves `nc` up; the log is untouched. -/
theorem usedOk_complete (dl dl0 : List UsedRec) (nc M : Nat) (h : usedOk dl dl0 nc M) :
    usedOk dl dl0 (nc + 1) M :=
  ⟨h.1, fun r hr => by have := h.2.1 r hr; omega, by have := h.2.2.1; omega, h.2.2.2.1,
    h.2.2.2.2⟩

/-- Catching the ghost list up: any longer prefix will do. -/
theorem usedOk_sync (dl dl0 : List UsedRec) (nc M : Nat) (h : usedOk dl dl0 nc M) :
    usedOk dl dl nc M := ⟨List.prefix_rfl, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Cashing a counter the log holds: `M` may rise to it. -/
theorem usedOk_bump (dl dl0 : List UsedRec) (nc M m : Nat) (h : usedOk dl dl0 nc M)
    (hm : m ≤ nc + 1) (hw : m = 0 ∨ ∃ r ∈ dl, m ≤ r.1) : usedOk dl dl0 nc (max M m) := by
  obtain ⟨hp, hb, hM, hmono, hach⟩ := h
  refine ⟨hp, hb, Nat.max_le.2 ⟨hM, hm⟩, hmono, ?_⟩
  rcases Nat.le_total m M with hle | hle
  · rw [Nat.max_eq_left hle]; exact hach
  · rw [Nat.max_eq_right hle]
    rcases hw with hz | ⟨r, hr, hmr⟩
    · exact Or.inl hz
    · exact Or.inr ⟨r, hr, hmr⟩

/-- **The used-index write**: the counter `nc + 1` joins the log. -/
theorem usedOk_write (dl dl0 : List UsedRec) (nc M t hd : Nat) (h : usedOk dl dl0 nc M) :
    usedOk (dl ++ [(nc + 1, t, hd)]) dl0 nc M := by
  obtain ⟨hp, hb, hM, hpw, hach⟩ := h
  refine ⟨hp.trans (List.prefix_append dl _), ?_, hM, ?_, ?_⟩
  case refine_3 =>
    rcases hach with hz | ⟨r, hr, hmr⟩
    · exact Or.inl hz
    · exact Or.inr ⟨r, List.mem_append_left _ hr, hmr⟩
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hb r hr
    · have : r = (nc + 1, t, hd) := by simpa using hr
      simp [this]
  · refine List.pairwise_append.2 ⟨hpw, List.pairwise_singleton _ _, ?_⟩
    intro a ha c hc
    have : c = (nc + 1, t, hd) := by simpa using hc
    rw [this]
    exact hb a ha

/-- **The largest counter a reader can see.**  The log never decreases, so
the newest entry a reader's view reaches dominates every entry it
reaches. -/
theorem used_find_max (dl : List UsedRec) (tvn : Nat) (r : UsedRec)
    (hpw : dl.Pairwise (fun a c => a.1 ≤ c.1))
    (hf : dl.reverse.find? (fun x => decide (x.2.1 ≤ tvn)) = some r)
    (x : UsedRec) (hx : x ∈ dl) (ht : x.2.1 ≤ tvn) : x.1 ≤ r.1 := by
  obtain ⟨hvis, L1, L2, hW, hL1⟩ := List.find?_eq_some_iff_append.1 hf
  have hprev : dl.reverse.Pairwise (fun a c => c.1 ≤ a.1) := by
    rw [List.pairwise_reverse]
    exact hpw
  rw [hW] at hprev
  have hx' : x ∈ L1 ++ r :: L2 := by rw [← hW]; exact List.mem_reverse.2 hx
  rcases List.mem_append.1 hx' with h | h
  · have := hL1 x h
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact absurd ht this
  · rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_refl _
    · exact (List.pairwise_cons.1 (List.pairwise_append.1 hprev).2.1).1 x h

theorem used_find_mem (dl : List UsedRec) (tvn : Nat) (r : UsedRec)
    (hf : dl.reverse.find? (fun x => decide (x.2.1 ≤ tvn)) = some r) : r ∈ dl :=
  List.mem_reverse.1 (List.mem_of_find?_eq_some hf)

/-! ### The log, as resources -/

/-- **The used-index cell**, with its write log explicit. -/
def usedIdxCell (pa : PAddr) (b : Nat) (dl : List UsedRec) : IProp GF := iprop%
  ∃ Hold : Nat → Hist,
    histBytes pa 2 (fun _ => DFrac.own 1) ((usedW dl).hist Hold) ∗ ⌜usedTailOk b Hold⌝

instance usedIdxCell_timeless (pa : PAddr) (b : Nat) (dl : List UsedRec) :
    Timeless (usedIdxCell (GF := GF) pa b dl) := by unfold usedIdxCell; infer_instance

/-- **The used-index write, leased.**  The device's store appends its entry
to the log; the position the machine gives it is the entry's timestamp. -/
theorem usedIdxCell_lease (pa : PAddr) (b : Nat) (dl : List UsedRec) (m hd : Nat)
    (R P : IProp GF)
    (hback : ∀ t : Nat, iprop(usedIdxCell (GF := GF) pa b (dl ++ [(m, t, hd)]) ∗ topLb t ∗ R) ⊢ P) :
    usedIdxCell (GF := GF) pa b dl ∗ R ⊢ dmaWriteLease pa 2 (wrap16 m) P := by
  unfold usedIdxCell dmaWriteLease
  iintro ⟨⟨%Hold, Hb, %ht⟩, HR⟩
  iexists ((usedW dl).hist Hold)
  iframe Hb
  iintro %t Hb2 _ #Htop
  iapply hback t
  iframe Htop
  isplitl [Hb2]
  · unfold usedIdxCell
    iexists Hold
    rw [WordHist.hist_push, show (⟨t, diskAgent, wrap16 m⟩ : WEnt 2) :: usedW dl
        = usedW (dl ++ [(m, t, hd)]) from (usedW_snoc dl (m, t, hd)).symm]
    iframe Hb2
    ipureintro; exact ht
  · iexact HR

/-- **The tails of a context window**, with a bound on their positions:
what a window the driver hands over whole leaves the invariant to start
its log from. -/
theorem ctxBytes_tails (ξ : CtxId) (pa : PAddr) (dq : DFrac) (bs : Nat → BitVec 8) :
    ∀ n : Nat, ([∗list] j ∈ List.range n, ctxByte ξ (pa + BitVec.ofNat 64 j) dq (bs j))
      ⊢@{IProp GF} ∃ (Hold : Nat → Hist) (b : Nat), histBytes pa n (fun _ => dq) Hold ∗
        ⌜∀ j, j < n → ∃ e H, Hold j = e :: H ∧ e.v = bs j ∧ e.t ≤ b⌝
  | 0 => by
    iintro H
    iexists (fun _ => ([] : Hist)), 0
    unfold histBytes
    simp only [List.range_zero]
    isplitl []
    · exact BigSepL.bigSepL_nil_intro
    · ipureintro
      intro j hj; omega
  | n + 1 => by
    rw [List.range_succ]
    iintro H
    icases BigSepL.bigSepL_snoc.1 $$ H with ⟨H1, H2⟩
    icases ctxBytes_tails ξ pa dq bs n $$ H1 with ⟨%Hold, %b, Hb, %hh⟩
    icases ctxByte_cases ξ (pa + BitVec.ofNat 64 n) dq (bs n) $$ H2
      with ⟨%e, %He, Hpt, %hev, _⟩
    iexists (fun j => if j = n then e :: He else Hold j), (max b e.t)
    isplitl [Hb Hpt]
    · unfold histBytes
      rw [List.range_succ]
      iapply BigSepL.bigSepL_snoc.2
      isplitl [Hb]
      · rw [BigSepL.bigSepL_eq (l := List.range n)
          (Φ := fun _ (j : Nat) => iprop((pa + BitVec.ofNat 64 j) ↦ₕ{dq}
            (if j = n then e :: He else Hold j)))
          (Ψ := fun _ (j : Nat) => iprop((pa + BitVec.ofNat 64 j) ↦ₕ{dq} Hold j))
          (fun {_ x} hx => by rw [if_neg (Nat.ne_of_lt (range_getElem?_lt hx))])]
        iexact Hb
      · simp only [↓reduceIte]
        iexact Hpt
    · ipureintro
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · obtain ⟨e', H', h1, h2, h3⟩ := hh j h
        exact ⟨e', H', by simp only [if_neg (Nat.ne_of_lt h)]; exact h1, h2, by omega⟩
      · subst h
        exact ⟨e, He, by simp, hev, by omega⟩

/-- **The used-index cell, as the flip hands it over**: the driver's whole
window becomes an empty log over tails whose positions are bounded. -/
theorem ctxBytes_usedIdxCell (ξ : CtxId) (pa : PAddr) :
    ctxBytes (GF := GF) ξ pa 2 (DFrac.own 1) (0 : BitVec (8 * 2)) ⊢
      ∃ b : Nat, usedIdxCell pa b [] := by
  unfold ctxBytes usedIdxCell
  iintro H
  icases ctxBytes_tails ξ pa (DFrac.own 1) (nthByte (0 : BitVec (8 * 2))) 2 $$ H
    with ⟨%Hold, %b, Hb, %ht⟩
  iexists b, Hold
  rw [usedW_nil, WordHist.hist_nil]
  iframe Hb
  ipureintro
  exact ht

/-! ### What a racy read of `used->idx` returns -/

/-- A used-index entry is visible to a hart exactly when its position is
below the hart's view: the disk is not a hart, so there is no
store-to-load forwarding to help. -/
theorem usedEnt_visible (cpu : CPU) (tvn : Nat) (r : UsedRec) :
    WEnt.visible (hartAgent cpu) tvn (usedEnt r) = decide (r.2.1 ≤ tvn) := by
  unfold WEnt.visible usedEnt
  simp only [Bool.or_eq_left_iff_imp, decide_eq_true_eq]
  intro h
  exact absurd h (diskAgent_ne_hartAgent cpu)

theorem usedW_find (dl : List UsedRec) (cpu : CPU) (tvn : Nat) :
    (usedW dl).find? (WEnt.visible (hartAgent cpu) tvn) =
      (dl.reverse.find? (fun x => decide (x.2.1 ≤ tvn))).map usedEnt := by
  rw [usedW_rev, List.find?_map]
  have h : (WEnt.visible (hartAgent cpu) tvn ∘ usedEnt) = (fun x => decide (x.2.1 ≤ tvn)) := by
    funext r
    exact usedEnt_visible cpu tvn r
  rw [h]

theorem usedIdx_read_some (dl : List UsedRec) (Hold : Nat → Hist) (cpu : CPU) (tvn : Nat)
    (w : BitVec (8 * 2)) (e : WEnt 2)
    (hf : (usedW dl).find? (WEnt.visible (hartAgent cpu) tvn) = some e)
    (hrd : readsAre (hartAgent cpu) tvn ((usedW dl).hist Hold) 2 w) : w = e.v := by
  apply bv_eq_of_bytes
  intro j hj
  have h := hrd j hj
  unfold Hist.read at h
  rw [WordHist.find?_hist, hf] at h
  simp only [Option.map_some, Option.some_or, WEnt.proj, Option.some.injEq] at h
  exact h.symm

theorem usedIdx_read_none (dl : List UsedRec) (Hold : Nat → Hist) (b : Nat) (cpu : CPU)
    (tvn : Nat) (w : BitVec (8 * 2)) (htail : usedTailOk b Hold) (hb : b ≤ tvn)
    (hf : (usedW dl).find? (WEnt.visible (hartAgent cpu) tvn) = none)
    (hrd : readsAre (hartAgent cpu) tvn ((usedW dl).hist Hold) 2 w) :
    w = (0 : BitVec (8 * 2)) := by
  apply bv_eq_of_bytes
  intro j hj
  have h := hrd j hj
  obtain ⟨e, H, hH, hev, het⟩ := htail j hj
  unfold Hist.read at h
  rw [WordHist.find?_hist, hf, Option.map_none, Option.none_or, hH] at h
  have hvis : HEnt.visible (hartAgent cpu) tvn e = true :=
    HEnt.visible_of_le _ _ _ (by omega)
  simp only [List.find?_cons, hvis, Option.map_some, Option.some.injEq] at h
  rw [← h, hev]

theorem wrap16_zero : wrap16 0 = (0 : BitVec (8 * 2)) := by decide

/-- **What a racy read of `used->idx` returns**: a counter the device has
published (or the `0` the cell starts at), and one that dominates every
write the reader's view has passed -- so a reader whose floor covers the
write that published its own watermark reads a counter at least as
large. -/
theorem usedIdx_read (dl : List UsedRec) (Hold : Nat → Hist) (b : Nat) (cpu : CPU)
    (tvn : Nat) (w : BitVec (8 * 2)) (htail : usedTailOk b Hold) (hb : b ≤ tvn)
    (hpw : dl.Pairwise (fun a c => a.1 ≤ c.1))
    (hrd : readsAre (hartAgent cpu) tvn ((usedW dl).hist Hold) 2 w) :
    ∃ m : Nat, w = wrap16 m ∧ (m = 0 ∨ ∃ (t hd : Nat), (m, t, hd) ∈ dl ∧ t ≤ tvn) ∧
      ∀ x ∈ dl, x.2.1 ≤ tvn → x.1 ≤ m := by
  cases hfr : dl.reverse.find? (fun x => decide (x.2.1 ≤ tvn)) with
  | none =>
    refine ⟨0, ?_, Or.inl rfl, ?_⟩
    · rw [wrap16_zero]
      exact usedIdx_read_none dl Hold b cpu tvn w htail hb
        (by rw [usedW_find, hfr]; rfl) hrd
    · intro x hx ht
      have := List.find?_eq_none.1 hfr x (List.mem_reverse.2 hx)
      simp only [decide_eq_true_eq] at this
      exact absurd ht this
  | some r =>
    have hrt : r.2.1 ≤ tvn := by
      have := List.find?_eq_some_iff_append.1 hfr
      simpa only [decide_eq_true_eq] using this.1
    refine ⟨r.1, ?_, Or.inr ⟨r.2.1, r.2.2, ?_, hrt⟩, ?_⟩
    · have := usedIdx_read_some dl Hold cpu tvn w (usedEnt r)
        (by rw [usedW_find, hfr]; rfl) hrd
      rw [this]
      rfl
    · have := used_find_mem dl tvn r hfr
      rwa [show (r.1, r.2.1, r.2.2) = r from rfl]
    · exact fun x hx ht => used_find_max dl tvn r hpw hfr x hx ht

/-- The completion records the invariant has published: the LAGGING ghost
list of the write log, with its persistent snapshot beside it. -/
def doneAuth (γ : DiskNames) (l : List UsedRec) : IProp GF := iprop%
  MonoList.auth_own γ.done (DFrac.own 1) l ∗ MonoList.lb_own γ.done l

/-- **The `k`-th used-index write published counter `m` at position `t`**
(persistent). -/
def doneRec (γ : DiskNames) (k : Nat) (r : UsedRec) : IProp GF := MonoList.idx_own γ.done k r

instance doneRec_persistent (γ : DiskNames) (k : Nat) (r : UsedRec) :
    Persistent (doneRec (GF := GF) γ k r) := by unfold doneRec MonoList.idx_own; infer_instance

instance doneAuth_timeless (γ : DiskNames) (l : List UsedRec) :
    Timeless (doneAuth (GF := GF) γ l) := by unfold doneAuth; infer_instance

theorem doneRec_lookup (γ : DiskNames) (l : List UsedRec) (k : Nat) (r : UsedRec) :
    ⊢@{IProp GF} doneAuth γ l -∗ doneRec γ k r -∗ ⌜l[k]? = some r⌝ := by
  unfold doneAuth doneRec
  iintro H1 H2
  icases H1 with ⟨Ha, _⟩
  iapply MonoList.auth_idx_lookup γ.done _ l k r $$ Ha H2

theorem doneRec_get (γ : DiskNames) (l : List UsedRec) (k : Nat) (r : UsedRec)
    (h : l[k]? = some r) : doneAuth (GF := GF) γ l ⊢ doneAuth γ l ∗ doneRec γ k r := by
  unfold doneAuth doneRec
  iintro ⟨Ha, #Hlb⟩
  iframe Ha Hlb
  iapply MonoList.idx_own_get γ.done k r h
  iexact Hlb

/-- **Catching the ghost list up with the device's log.** -/
theorem doneAuth_sync (γ : DiskNames) (l l' : List UsedRec) (h : l <+: l') :
    doneAuth (GF := GF) γ l ⊢ |==> doneAuth γ l' := by
  unfold doneAuth
  iintro ⟨Ha, _⟩
  imod MonoList.auth_own_update γ.done l' h $$ Ha with ⟨H1, #H2⟩
  imodintro
  iframe H1 H2

/-- The positions of the used-index writes, as persistent top bounds: what
a hart's floor must pass before an entry of the log means anything to
it. -/
def dlTops (dl : List UsedRec) : IProp GF := iprop% [∗list] r ∈ dl, topLb r.2.1

instance dlTops_persistent (dl : List UsedRec) : Persistent (dlTops (GF := GF) dl) := by
  unfold dlTops; infer_instance

instance dlTops_timeless (dl : List UsedRec) : Timeless (dlTops (GF := GF) dl) := by
  unfold dlTops; infer_instance

theorem dlTops_nil : ⊢@{IProp GF} dlTops [] := by
  unfold dlTops
  exact BigSepL.bigSepL_nil_intro

theorem dlTops_snoc (dl : List UsedRec) (r : UsedRec) :
    dlTops (GF := GF) dl ∗ topLb r.2.1 ⊢ dlTops (dl ++ [r]) := by
  unfold dlTops
  iintro H
  iapply BigSepL.bigSepL_snoc.2
  iexact H

theorem dlTops_mem (dl : List UsedRec) (r : UsedRec) (h : r ∈ dl) :
    dlTops (GF := GF) dl ⊢ topLb r.2.1 := by
  unfold dlTops
  iintro H
  icases BigSepL.bigSepL_mem_acc (Φ := fun (r : UsedRec) => topLb (GF := GF) r.2.1) h $$ H
    with ⟨Hr, _⟩
  iexact Hr

theorem usedIdxCell_cases (pa : PAddr) (b : Nat) (dl : List UsedRec) :
    usedIdxCell (GF := GF) pa b dl ⊢ ∃ Hold : Nat → Hist,
      histBytes pa 2 (fun _ => DFrac.own 1) ((usedW dl).hist Hold) ∗ ⌜usedTailOk b Hold⌝ := by
  unfold usedIdxCell
  iintro H
  iexact H

/-- Rebuilding the cell from its histories. -/
theorem usedIdxCell_intro (pa : PAddr) (b : Nat) (dl : List UsedRec) (Hold : Nat → Hist)
    (h : usedTailOk b Hold) :
    histBytes (GF := GF) pa 2 (fun _ => DFrac.own 1) ((usedW dl).hist Hold) ⊢
      usedIdxCell pa b dl := by
  unfold usedIdxCell
  iintro H
  iexists Hold
  iframe H
  ipureintro; exact h

/-- Every byte of the cell has a history: the tails are nonempty. -/
theorem usedIdxCell_ne_nil (b : Nat) (dl : List UsedRec) (Hold : Nat → Hist)
    (h : usedTailOk b Hold) (j : Nat) (hj : j < 2) : (usedW dl).hist Hold j ≠ [] :=
  WordHist.hist_ne_nil_vals (usedW dl) Hold (usedTailOk_vals b Hold h) j hj

theorem diskDoneLb_le (γ : DiskNames) (M n : Nat) :
    ⊢@{IProp GF} diskDoneAuth γ M -∗ diskDoneLb γ n -∗ ⌜n ≤ M⌝ := by
  unfold diskDoneAuth diskDoneLb
  iintro H1 H2
  ihave %h := MonoNat.auth_lb_own_valid γ.nc _ _ _ $$ H1 H2
  ipureintro
  simpa only [MaxNat.le_toNat] using h.2

/-- **Cashing a counter the log holds**: the monotone completion counter
rises to it, and its persistent lower bound comes out. -/
theorem diskDoneAuth_cash (γ : DiskNames) (M m : Nat) :
    diskDoneAuth (GF := GF) γ M ⊢ |==> (diskDoneAuth γ (max M m) ∗ diskDoneLb γ m) := by
  unfold diskDoneAuth diskDoneLb
  iintro H
  imod MonoNat.own_update γ.nc (.ofNat M) (.ofNat (max M m))
    (by simp only [MaxNat.le_toNat]; omega) $$ H with ⟨H1, #H2⟩
  imodintro
  iframe H1
  iapply MonoNat.lb_own_le γ.nc (.ofNat (max M m)) (.ofNat m)
    (by simp only [MaxNat.le_toNat]; omega)
  iexact H2

/-! ### The base of the log

The used page was zeroed before the flip, by stores this invariant did not
make; their positions are what a reader's floor must have passed before the
`0` the cell starts at means anything to it.  The flip freezes that bound
in a ghost variable, and `Xv6.diskWm` is how a client carries it. -/

/-- The bound on the zeroing stores, before the flip. -/
def diskBaseAuth (γ : DiskNames) (b : Nat) : IProp GF := γ.base ↪VAR{.own 1} b
/-- The same, frozen at the flip (persistent). -/
def diskBaseFrozen (γ : DiskNames) (b : Nat) : IProp GF := γ.base ↪VAR{.discard} b

instance diskBaseFrozen_persistent (γ : DiskNames) (b : Nat) :
    Persistent (diskBaseFrozen (GF := GF) γ b) := by unfold diskBaseFrozen; infer_instance

theorem diskBase_freeze (γ : DiskNames) (b b' : Nat) :
    diskBaseAuth (GF := GF) γ b ⊢ |==> diskBaseFrozen γ b' := by
  unfold diskBaseAuth diskBaseFrozen
  iintro H
  imod ghost_var_update b' γ.base $$ H with H
  imod ghost_var_persist γ.base _ b' $$ H with #H
  imodintro
  iexact H

theorem diskBaseFrozen_agree (γ : DiskNames) (b b' : Nat) :
    ⊢@{IProp GF} diskBaseFrozen γ b -∗ diskBaseFrozen γ b' -∗ ⌜b = b'⌝ := by
  unfold diskBaseFrozen
  iintro H1 H2
  ihave %h := ghost_var_agree γ.base _ _ _ _ $$ H1 H2
  ipureintro; exact h

/-- **The handler's TSO credential**: its floor `F` has passed the stores
that zeroed the used page, and -- when its watermark `n` is not zero -- a
used-index write that published a counter at least `n`.  Persistent,
monotone UP in `F` and DOWN in `n`.

It is Rocq's `disk_flr`, the credential the handler carries from one
iteration of its loop to the next.  It is MINTED by the read of
`used->idx` itself (`Xv6.disk_used_idx_read`, over `MachCSL.readAUr`,
whose continuation names the view the load read at) and CASHED by the
reads that follow the loop body's `__sync_synchronize()`, which is what
turns that read watermark into a floor
(`MachCSL.wp_s_fence_rw_rw_floor`). -/
def diskWm (γ : DiskNames) (n F : Nat) : IProp GF := iprop%
  (∃ b : Nat, diskBaseFrozen γ b ∗ ⌜b ≤ F⌝) ∗
  (⌜n = 0⌝ ∨ ∃ (k m t hd : Nat), doneRec γ k (m, t, hd) ∗ ⌜n ≤ m ∧ t ≤ F⌝)

instance diskWm_persistent (γ : DiskNames) (n F : Nat) :
    Persistent (diskWm (GF := GF) γ n F) := by unfold diskWm; infer_instance

theorem diskWm_base (γ : DiskNames) (n F : Nat) :
    diskWm (GF := GF) γ n F ⊢ ∃ b : Nat, diskBaseFrozen γ b ∗ ⌜b ≤ F⌝ := by
  unfold diskWm
  iintro ⟨H, _⟩
  iexact H

/-- **The completion record of a head**: the used-index write that
published counter `n` reported the completion of descriptor head `h` (its
used-ring element went with it).  Persistent -- and it is what the status
and collect accessors must take as their premise, since neither is sound
for a head whose request has NOT completed. -/
def headDone (γ : DiskNames) (n h : Nat) : IProp GF := iprop%
  ∃ (k t : Nat), doneRec γ k (n, t, h)

instance headDone_persistent (γ : DiskNames) (n h : Nat) :
    Persistent (headDone (GF := GF) γ n h) := by unfold headDone; infer_instance

/-- **The credential at the base**: a watermark of zero needs only the
bound on the zeroing stores. -/
theorem diskWm_zero (γ : DiskNames) (F b : Nat) (hb : b ≤ F) :
    diskBaseFrozen (GF := GF) γ b ⊢ diskWm γ 0 F := by
  unfold diskWm
  iintro #Hb
  isplitl []
  · iexists b
    iframe Hb
    ipureintro; exact hb
  · ileft
    ipureintro; rfl

theorem diskWm_mono (γ : DiskNames) (n n' F F' : Nat) (hn : n' ≤ n) (hF : F ≤ F') :
    diskWm (GF := GF) γ n F ⊢ diskWm γ n' F' := by
  unfold diskWm
  iintro ⟨⟨%b, #Hb, %hb⟩, Hor⟩
  isplitl []
  · iexists b
    iframe Hb
    ipureintro; omega
  icases Hor with ⟨%hz | ⟨%k, %m, %t, %hd, #Hr, %hmt⟩⟩
  · ileft; ipureintro; omega
  · iright
    iexists k, m, t, hd
    iframe Hr
    ipureintro
    exact ⟨by omega, by omega⟩

/-- **What the credential says about the log**: the write that published
the watermark is in it, at a position the floor has passed. -/
theorem diskWm_mem (γ : DiskNames) (nr F : Nat) (dl dl0 : List UsedRec) (hpre : dl0 <+: dl) :
    ⊢@{IProp GF} doneAuth γ dl0 -∗ diskWm γ nr F -∗
      ⌜nr = 0 ∨ ∃ (m t hd : Nat), (m, t, hd) ∈ dl ∧ nr ≤ m ∧ t ≤ F⌝ := by
  unfold diskWm
  iintro Hdn ⟨_, Hor⟩
  icases Hor with ⟨%hz | ⟨%k, %m, %t, %hd, #Hr, %hmt⟩⟩
  · ipureintro; exact Or.inl hz
  · ihave %hl := doneRec_lookup γ dl0 k (m, t, hd) $$ Hdn Hr
    ipureintro
    exact Or.inr ⟨m, t, hd,
      List.mem_of_getElem? (MonoList.prefix_getElem? hpre hl), hmt.1, hmt.2⟩

/-! ## The published count, monotonically

`np` is a ghost var split between the invariant and the publisher, so that
a bump needs both halves; it is ALSO a mono-nat, so that a persistent
lower bound can be minted at one state and cashed at a later one.  That is
what the root loop's `avail->idx` read leaves behind: `np` was past `lo`
when the read ran, so it still is at the pop. -/

/-- At least `n` requests have been published (persistent). -/
def diskPubLb (γ : DiskNames) (n : Nat) : IProp GF := MonoNat.lb_own γ.npm (.ofNat n)

instance diskPubLb_persistent (γ : DiskNames) (n : Nat) :
    Persistent (diskPubLb (GF := GF) γ n) := by unfold diskPubLb; infer_instance

/-- The monotone published count, as the invariant holds it: the authority
WITH its persistent lower bound beside it, so that a bound may be taken
out with no update (a DMA read pin has no room for one). -/
def diskPubAuthM (γ : DiskNames) (n : Nat) : IProp GF := iprop%
  MonoNat.auth_own γ.npm (DFrac.own 1) (.ofNat n) ∗ diskPubLb γ n

instance diskPubAuthM_timeless (γ : DiskNames) (n : Nat) :
    Timeless (diskPubAuthM (GF := GF) γ n) := by unfold diskPubAuthM diskPubLb; infer_instance

theorem diskPubLb_le (γ : DiskNames) (n m : Nat) :
    ⊢@{IProp GF} diskPubAuthM γ n -∗ diskPubLb γ m -∗ ⌜m ≤ n⌝ := by
  unfold diskPubAuthM diskPubLb
  iintro H1 H2
  icases H1 with ⟨Ha, _⟩
  ihave %h := MonoNat.auth_lb_own_valid γ.npm _ _ _ $$ Ha H2
  ipureintro
  simpa only [MaxNat.le_toNat] using h.2

/-- **A bound comes out for free.** -/
theorem diskPubAuthM_lb (γ : DiskNames) (n m : Nat) (hm : m ≤ n) :
    diskPubAuthM (GF := GF) γ n ⊢ diskPubAuthM γ n ∗ diskPubLb γ m := by
  unfold diskPubAuthM diskPubLb
  iintro ⟨Ha, #Hlb⟩
  iframe Ha Hlb
  iapply MonoNat.lb_own_le γ.npm (.ofNat n) (.ofNat m) (by simp only [MaxNat.le_toNat]; omega)
  iexact Hlb

theorem diskPubAuthM_bump (γ : DiskNames) (n m : Nat) (hm : n ≤ m) :
    diskPubAuthM (GF := GF) γ n ⊢ |==> diskPubAuthM γ m := by
  unfold diskPubAuthM diskPubLb
  iintro ⟨Ha, _⟩
  imod MonoNat.own_update γ.npm (.ofNat n) (.ofNat m)
    (by simp only [MaxNat.le_toNat]; omega) $$ Ha with ⟨H1, #H2⟩
  imodintro
  iframe H1 H2

/-! ## The serve permits

A `serve h` task must know, at the step where it installs the request it
parsed, that head `h` still carries the chain whose descriptors it read.
That is not a monotone fact, so no persistent token can carry it: the
permit is an EXCLUSIVE ghost-map element that the POP MINTS and hands to
the task it forks, and the task holds it to its last step.  While a
permit for `h` is out, the receipt of `h` cannot move: any move would
have to change the permit's value, which needs the permit back.

Minting at the POP rather than at the task's first `get` is what the queue
accounting buys, and it is what the DRIVER's side needs: a permit now
RECORDS AN ARMED CHAIN (`PermVal` is a head and a `Chain`, not a head and
an `HState`), so a head the driver holds free (`headTok γ h .inactive`)
provably has no permit out -- which is exactly `disk_publish`'s
obligation.  It also means a `serve` task never meets a free head, so the
invariant need hold nothing at all for a free descriptor
(`headRes .inactive = emp`) and the driver keeps the whole free descriptor
at the context tier.

The permits are a ghost map keyed by a serial number, so minting one is
always possible -- `permFresh` keeps a bound above which the map is
empty. -/

/-- What a permit records: the head, the CHAIN armed there, whether the
task has INSTALLED the request it parsed (so the device's in-flight map
carries `c.req` at that head), and -- once the task has passed the
completion gate -- the used index it LATCHED at the `get` that follows the
gate, which is the index it will report at.

The last two fields are the IN-FLIGHT BOOKKEEPING the completion side
needs.  `MachCSL.DevM.LeaseL`'s DMA-write arm is quantified over every
state the guard fires at, and the guard of each of a request's four
writes is a fact about the device's in-flight map (`reqOf s h = some r`,
`s.usedIdx = ui`).  Without a per-head record of those facts the
derivation would have to cope with a state in which the write is SKIPPED,
and then nothing at all is known about the bytes at its address.  A
permit is exclusive and one per head (`Xv6.permInj`), so it is the
natural place to keep them. -/
abbrev PermVal : Type := BitVec 16 × Chain × Option VPhase × Option (BitVec 16)

/-- The permits the invariant has handed out. -/
def permAuth (γ : DiskNames) (pm : RegMapF PermVal) : IProp GF := γ.perm ↪●MAP pm

/-- **A serve permit**: exclusive, and pins head `h`'s receipt to `.active c`. -/
def permTok (γ : DiskNames) (k : Nat) (h : BitVec 16) (c : Chain) (p : Option VPhase)
    (u : Option (BitVec 16)) : IProp GF :=
  γ.perm ↪◯MAP[k] ((h, c, p, u) : PermVal)

/-- Every permit names a descriptor of the queue, armed with the chain it
records, and a head that is IN FLIGHT; once the task has installed the
request it parsed, the device's map carries that request; and once it has
latched the used index, the device's index is still there and the request
has passed the completion gate. -/
def permOk (v : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState) : Prop :=
  ∀ k h c p u, PartialMap.get? pm k = some ((h, c, p, u) : PermVal) →
    h.toNat < NUM ∧ st h.toNat = .active c ∧ (Virtio.phase v h).isSome = true ∧
    (∀ ph, p = some ph → Virtio.phase v h = some ph ∧ ph.req = some c.req) ∧
    (∀ y, u = some y → v.usedIdx = y ∧ p = some (.pushed c.req))

/-- **One permit per head.**  A permit's head is in flight, and the pop
refuses a head that is, so the map never holds two permits for one
head. -/
def permInj (pm : RegMapF PermVal) : Prop :=
  ∀ k k' h c p u c' p' u', PartialMap.get? pm k = some ((h, c, p, u) : PermVal) →
    PartialMap.get? pm k' = some ((h, c', p', u') : PermVal) → k = k'

/-- **At most one request sits between its used element and its used
index.**  The model's `MachCSL.Virtio.pushOk` guards the completion gate;
this is what that guard maintains, and it is what says the device's used
index cannot move under a task that has latched it. -/
def pushedUniq (v : VirtioState) : Prop :=
  ∀ (h h' : BitVec 16) (r r' : VioReq), Virtio.phase v h = some (.pushed r) →
    Virtio.phase v h' = some (.pushed r') → h = h'

/-! ### The phases, as the model moves them -/

theorem phase_setPhase_self (v : VirtioState) (h : BitVec 16) (ph : VPhase) :
    Virtio.phase (Virtio.setPhase v h ph) h = some ph := by
  unfold Virtio.phase Virtio.setPhase
  rw [Alist.get_set_eq]

theorem phase_setPhase_other (v : VirtioState) (h k : BitVec 16) (ph : VPhase) (hk : k ≠ h) :
    Virtio.phase (Virtio.setPhase v h ph) k = Virtio.phase v k := by
  unfold Virtio.phase Virtio.setPhase
  rw [Alist.get_set_ne _ _ _ _ hk]

theorem phase_complete_self (v : VirtioState) (h : BitVec 16) :
    Virtio.phase (Virtio.complete v h) h = none := by
  unfold Virtio.phase Virtio.complete
  rw [Alist.get_del_eq]

theorem phase_complete_other (v : VirtioState) (h k : BitVec 16) (hk : k ≠ h) :
    Virtio.phase (Virtio.complete v h) k = Virtio.phase v k := by
  unfold Virtio.phase Virtio.complete
  rw [Alist.get_del_ne _ _ _ hk]

/-- What `MachCSL.Virtio.pushOk` says head by head. -/
theorem pushOk_not_pushed (v : VirtioState) (hok : Virtio.pushOk v = true) (h : BitVec 16)
    (r : VioReq) : Virtio.phase v h ≠ some (.pushed r) := by
  intro hp
  have hm : (h, (VPhase.pushed r)) ∈ v.inflight := Alist.get_mem _ _ _ hp
  have := List.all_eq_true.1 hok _ hm
  simp [VPhase.isPushed] at this

/-! ### The permits, as the moves keep them honest -/

/-- No permit at all: the dead arm, and the state the live flip starts from. -/
theorem permOk_none (v : VirtioState) (pm : RegMapF PermVal)
    (h : permOk v pm (fun _ => .inactive)) (k : Nat) (hh : BitVec 16) (c : Chain)
    (p : Option VPhase) (u : Option (BitVec 16)) :
    PartialMap.get? pm k ≠ some ((hh, c, p, u) : PermVal) := by
  intro hget
  have := (h k hh c p u hget).2.1
  exact absurd this (by simp)

/-- In the dead world no permit is out at all, so any state will do. -/
theorem permOk_dead (v v' : VirtioState) (pm : RegMapF PermVal)
    (hok : permOk v pm (fun _ => .inactive)) : permOk v' pm (fun _ => .inactive) := by
  intro k h c p u hget
  exact absurd hget (permOk_none v pm hok k h c p u)

theorem permOk_delete (v : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat)
    (hok : permOk v pm st) : permOk v (PartialMap.delete pm k) st := by
  intro k' h' c' p' u' hget
  by_cases hk : k = k'
  · rw [get?_delete_eq hk] at hget; exact absurd hget (by simp)
  · exact hok k' h' c' p' u' (by rwa [get?_delete_ne hk] at hget)

/-- Arming a head no permit names keeps every permit honest. -/
theorem permOk_arm (v : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState) (i : Nat)
    (c : Chain) (hok : permOk v pm st) (hfree : st i = .inactive) :
    permOk v pm (fun j => if j = i then .active c else st j) := by
  intro k' h' c' p' u' hget
  obtain ⟨hlt, hst, h3, h4, h5⟩ := hok k' h' c' p' u' hget
  refine ⟨hlt, ?_, h3, h4, h5⟩
  have hne : h'.toNat ≠ i := by
    intro he; rw [he, hfree] at hst; exact absurd hst (by simp)
  simp only [if_neg hne]
  exact hst

/-- A head that is NOT in flight has no permit out. -/
theorem perm_none_of_notFlight (v : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState)
    (h : BitVec 16) (hnf : (Virtio.phase v h).isSome = false) (hok : permOk v pm st) :
    ∀ k' c' p' u', PartialMap.get? pm k' ≠ some ((h, c', p', u') : PermVal) := by
  intro k' c' p' u' hget
  have := (hok k' h c' p' u' hget).2.2.1
  rw [hnf] at this
  exact absurd this (by simp)

/-- **The pop**, as the permits see it: the head was not in flight, so no
permit named it, and the new permit starts un-installed and un-latched. -/
theorem permOk_pop (v : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat)
    (h : BitVec 16) (c : Chain) (sn : BitVec 16) (hlt : h.toNat < NUM)
    (hst : st h.toNat = .active c) (hnf : (Virtio.phase v h).isSome = false)
    (hok : permOk v pm st) :
    permOk { Virtio.setPhase v h .popped with seen := sn }
      (PartialMap.insert pm k ((h, c, none, none) : PermVal)) st := by
  have hph : ∀ x : BitVec 16, Virtio.phase { Virtio.setPhase v h .popped with seen := sn } x
      = Virtio.phase (Virtio.setPhase v h .popped) x := fun _ => rfl
  intro k' h' c' p' u' hget
  by_cases hk : k = k'
  · rw [get?_insert_eq hk] at hget
    cases hget
    exact ⟨hlt, hst, by rw [hph, phase_setPhase_self]; rfl, by simp, by simp⟩
  · rw [get?_insert_ne hk] at hget
    obtain ⟨p1, p2, p3, p4, p5⟩ := hok k' h' c' p' u' hget
    have hne : h' ≠ h := by
      intro he; subst he; rw [hnf] at p3; exact absurd p3 (by simp)
    have hx : Virtio.phase { Virtio.setPhase v h .popped with seen := sn } h'
        = Virtio.phase v h' := by rw [hph, phase_setPhase_other v h h' _ hne]
    exact ⟨p1, p2, by rw [hx]; exact p3, fun ph hp => ⟨by rw [hx]; exact (p4 ph hp).1,
      (p4 ph hp).2⟩, fun y hy => ⟨(p5 y hy).1, (p5 y hy).2⟩⟩

/-- `pushedUniq` sees only the in-flight map. -/
theorem pushedUniq_seen (v : VirtioState) (sn : BitVec 16) (hu : pushedUniq v) :
    pushedUniq { v with seen := sn } := hu

/-- **The install**: the task records the request it parsed at its own
head, and the permit records the phase the device is now in.  Every other
permit names another head (`Xv6.permInj`), which the move leaves alone. -/
theorem permOk_install (v : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat)
    (h : BitVec 16) (c : Chain) (p0 : Option VPhase) (u0 : Option (BitVec 16)) (ph : VPhase)
    (hget : PartialMap.get? pm k = some ((h, c, p0, u0) : PermVal))
    (hreq : ph.req = some c.req) (hok : permOk v pm st) (hinj : permInj pm) :
    permOk (Virtio.setPhase v h ph)
      (PartialMap.insert pm k ((h, c, some ph, none) : PermVal)) st := by
  intro k' h' c' p' u' hget'
  by_cases hk : k = k'
  · rw [get?_insert_eq hk] at hget'
    cases hget'
    obtain ⟨hlt, hst, _, _, _⟩ := hok k h c p0 u0 hget
    refine ⟨hlt, hst, by rw [phase_setPhase_self]; rfl, ?_, by simp⟩
    intro ph' hph'
    cases hph'
    exact ⟨phase_setPhase_self v h ph, hreq⟩
  · rw [get?_insert_ne hk] at hget'
    obtain ⟨hlt, hst, h3, h4, h5⟩ := hok k' h' c' p' u' hget'
    have hne : h' ≠ h := by
      intro he; subst he; exact hk (hinj k k' h' c p0 u0 c' p' u' hget hget')
    have hx : Virtio.phase (Virtio.setPhase v h ph) h' = Virtio.phase v h' :=
      phase_setPhase_other v h h' ph hne
    exact ⟨hlt, hst, by rw [hx]; exact h3, fun q hq => ⟨by rw [hx]; exact (h4 q hq).1,
      (h4 q hq).2⟩, fun y hy => ⟨(h5 y hy).1, (h5 y hy).2⟩⟩

/-- **The latch**: the task that has passed the completion gate reads the
used index and records it.  The move changes nothing. -/
theorem permOk_latch (v : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat)
    (h : BitVec 16) (c : Chain) (u0 : Option (BitVec 16))
    (hget : PartialMap.get? pm k = some ((h, c, some (.pushed c.req), u0) : PermVal))
    (hok : permOk v pm st) :
    permOk v (PartialMap.insert pm k ((h, c, some (.pushed c.req), some v.usedIdx) : PermVal))
      st := by
  intro k' h' c' p' u' hget'
  by_cases hk : k = k'
  · rw [get?_insert_eq hk] at hget'
    cases hget'
    obtain ⟨hlt, hst, h3, h4, _⟩ := hok k h c (some (.pushed c.req)) u0 hget
    exact ⟨hlt, hst, h3, h4, by rintro y ⟨rfl⟩; exact ⟨rfl, rfl⟩⟩
  · rw [get?_insert_ne hk] at hget'
    exact hok k' h' c' p' u' hget'

/-- **The completion**: the permit the completing task holds goes, and no
other permit is disturbed -- the head leaves the in-flight map, and the
used index moves, but a permit at that head would be this one
(`Xv6.permInj`) and a LATCHED permit at another head would be pushed too
(`Xv6.pushedUniq`). -/
theorem permOk_complete (v : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat)
    (h : BitVec 16) (c : Chain) (ui : BitVec 16)
    (hget : PartialMap.get? pm k = some ((h, c, some (.pushed c.req), some ui) : PermVal))
    (hok : permOk v pm st) (hinj : permInj pm) (hpu : pushedUniq v) :
    permOk (Virtio.complete v h) (PartialMap.delete pm k) st := by
  intro k' h' c' p' u' hget'
  have hk : k ≠ k' := by
    intro he; rw [get?_delete_eq he] at hget'; exact absurd hget' (by simp)
  rw [get?_delete_ne hk] at hget'
  obtain ⟨hlt, hst, h3, h4, h5⟩ := hok k' h' c' p' u' hget'
  have hne : h' ≠ h := by
    intro he; subst he
    exact hk (hinj k k' h' c (some (.pushed c.req)) (some ui) c' p' u' hget hget')
  have hx : Virtio.phase (Virtio.complete v h) h' = Virtio.phase v h' :=
    phase_complete_other v h h' hne
  refine ⟨hlt, hst, by rw [hx]; exact h3, fun q hq => ⟨by rw [hx]; exact (h4 q hq).1,
    (h4 q hq).2⟩, ?_⟩
  intro y hy
  obtain ⟨_, hp⟩ := h5 y hy
  have hph' := (h4 _ hp).1
  have hph := (hok k h c (some (.pushed c.req)) (some ui) hget).2.2.2.1 _ rfl
  exact absurd (hpu h' h c'.req c.req hph' hph.1) hne

/-! ### `permInj` and `pushedUniq`, as the moves keep them -/

theorem permInj_insert (pm : RegMapF PermVal) (k : Nat) (h : BitVec 16) (c c0 : Chain)
    (p p0 : Option VPhase) (u u0 : Option (BitVec 16)) (hinj : permInj pm)
    (hget : PartialMap.get? pm k = some ((h, c0, p0, u0) : PermVal)) :
    permInj (PartialMap.insert pm k ((h, c, p, u) : PermVal)) := by
  intro k1 k2 hh c1 p1 u1 c2 p2 u2 hg1 hg2
  have key : ∀ k' c' p' u', PartialMap.get? (PartialMap.insert pm k ((h, c, p, u) : PermVal)) k'
      = some ((hh, c', p', u') : PermVal) →
      ∃ c'' p'' u'', PartialMap.get? pm k' = some ((hh, c'', p'', u'') : PermVal) := by
    intro k' c' p' u' hg
    by_cases hkk : k = k'
    · rw [get?_insert_eq hkk] at hg
      cases hg
      exact ⟨c0, p0, u0, hkk ▸ hget⟩
    · rw [get?_insert_ne hkk] at hg
      exact ⟨c', p', u', hg⟩
  obtain ⟨c1', p1', u1', hp1⟩ := key k1 c1 p1 u1 hg1
  obtain ⟨c2', p2', u2', hp2⟩ := key k2 c2 p2 u2 hg2
  exact hinj k1 k2 hh c1' p1' u1' c2' p2' u2' hp1 hp2

theorem permInj_fresh (pm : RegMapF PermVal) (k : Nat) (h : BitVec 16) (c : Chain)
    (hinj : permInj pm)
    (hfree : ∀ k' c' p' u', PartialMap.get? pm k' ≠ some ((h, c', p', u') : PermVal)) :
    permInj (PartialMap.insert pm k ((h, c, none, none) : PermVal)) := by
  intro k1 k2 hh c1 p1 u1 c2 p2 u2 hg1 hg2
  by_cases hk1 : k = k1
  · by_cases hk2 : k = k2
    · omega
    · rw [get?_insert_eq hk1] at hg1
      cases hg1
      rw [get?_insert_ne hk2] at hg2
      exact absurd hg2 (hfree k2 c2 p2 u2)
  · rw [get?_insert_ne hk1] at hg1
    by_cases hk2 : k = k2
    · rw [get?_insert_eq hk2] at hg2
      cases hg2
      exact absurd hg1 (hfree k1 c1 p1 u1)
    · rw [get?_insert_ne hk2] at hg2
      exact hinj k1 k2 hh c1 p1 u1 c2 p2 u2 hg1 hg2

theorem permInj_delete (pm : RegMapF PermVal) (k : Nat) (hinj : permInj pm) :
    permInj (PartialMap.delete pm k) := by
  intro k1 k2 hh c1 p1 u1 c2 p2 u2 hg1 hg2
  have hn1 : k ≠ k1 := by
    intro he; rw [get?_delete_eq he] at hg1; exact absurd hg1 (by simp)
  have hn2 : k ≠ k2 := by
    intro he; rw [get?_delete_eq he] at hg2; exact absurd hg2 (by simp)
  rw [get?_delete_ne hn1] at hg1
  rw [get?_delete_ne hn2] at hg2
  exact hinj k1 k2 hh c1 p1 u1 c2 p2 u2 hg1 hg2

theorem pushedUniq_none (v : VirtioState) (h : noInflight v) : pushedUniq v := by
  intro hh hh' r r' hp _
  have := h hh
  unfold Virtio.reqOf at this
  rw [hp] at this
  exact absurd this (by simp [VPhase.req])

theorem pushedUniq_setPhase (v : VirtioState) (h : BitVec 16) (ph : VPhase)
    (hnp : ∀ r, ph ≠ .pushed r) (hu : pushedUniq v) : pushedUniq (Virtio.setPhase v h ph) := by
  intro h1 h2 r1 r2 hp1 hp2
  have key : ∀ (hx : BitVec 16) (rx : VioReq),
      Virtio.phase (Virtio.setPhase v h ph) hx = some (.pushed rx) →
      hx ≠ h ∧ Virtio.phase v hx = some (.pushed rx) := by
    intro hx rx hpx
    by_cases hxh : hx = h
    · subst hxh
      rw [phase_setPhase_self] at hpx
      exact absurd (Option.some.inj hpx) (hnp rx)
    · exact ⟨hxh, by rwa [phase_setPhase_other v h hx ph hxh] at hpx⟩
  obtain ⟨_, k1⟩ := key h1 r1 hp1
  obtain ⟨_, k2⟩ := key h2 r2 hp2
  exact hu h1 h2 r1 r2 k1 k2

theorem pushedUniq_pushed (v : VirtioState) (h : BitVec 16) (r : VioReq)
    (hok : Virtio.pushOk v = true) : pushedUniq (Virtio.setPhase v h (.pushed r)) := by
  intro h1 h2 r1 r2 hp1 hp2
  have key : ∀ (hx : BitVec 16) (rx : VioReq),
      Virtio.phase (Virtio.setPhase v h (.pushed r)) hx = some (.pushed rx) → hx = h := by
    intro hx rx hpx
    by_cases hxh : hx = h
    · exact hxh
    · rw [phase_setPhase_other v h hx _ hxh] at hpx
      exact absurd hpx (pushOk_not_pushed v hok hx rx)
  rw [key h1 r1 hp1, key h2 r2 hp2]

theorem pushedUniq_complete (v : VirtioState) (h : BitVec 16) (hu : pushedUniq v) :
    pushedUniq (Virtio.complete v h) := by
  intro h1 h2 r1 r2 hp1 hp2
  have key : ∀ (hx : BitVec 16) (rx : VioReq),
      Virtio.phase (Virtio.complete v h) hx = some (.pushed rx) →
      Virtio.phase v hx = some (.pushed rx) := by
    intro hx rx hpx
    by_cases hxh : hx = h
    · subst hxh; rw [phase_complete_self] at hpx; exact absurd hpx (by simp)
    · rwa [phase_complete_other v h hx hxh] at hpx
  exact hu h1 h2 r1 r2 (key h1 r1 hp1) (key h2 r2 hp2)

theorem pushedUniq_congr (v v' : VirtioState)
    (hph : ∀ h, Virtio.phase v' h = Virtio.phase v h) (hu : pushedUniq v) : pushedUniq v' := by
  intro h1 h2 r1 r2 hp1 hp2
  exact hu h1 h2 r1 r2 (by rw [← hph h1]; exact hp1) (by rw [← hph h2]; exact hp2)

theorem permOk_congr (v v' : VirtioState) (pm : RegMapF PermVal) (st : Nat → HState)
    (hph : ∀ h, Virtio.phase v' h = Virtio.phase v h) (hidx : v'.usedIdx = v.usedIdx)
    (hok : permOk v pm st) : permOk v' pm st := by
  intro k h c p u hget
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok k h c p u hget
  exact ⟨h1, h2, by rw [hph h]; exact h3,
    fun q hq => ⟨by rw [hph h]; exact (h4 q hq).1, (h4 q hq).2⟩,
    fun y hy => ⟨by rw [hidx]; exact (h5 y hy).1, (h5 y hy).2⟩⟩

/-- Keys at or above `n` are free, so `n` is a key a permit may take. -/
def permFresh (n : Nat) (pm : RegMapF PermVal) : Prop :=
  ∀ k, n ≤ k → PartialMap.get? pm k = none

theorem permFresh_insert (pm : RegMapF PermVal) (n : Nat) (h : BitVec 16) (c : Chain)
    (p : Option VPhase) (u : Option (BitVec 16)) (hf : permFresh n pm) :
    permFresh (n + 1) (PartialMap.insert pm n ((h, c, p, u) : PermVal)) := by
  intro k hk
  rw [get?_insert_ne (by omega)]
  exact hf k (by omega)

theorem permFresh_keep (pm : RegMapF PermVal) (n k : Nat) (h : BitVec 16) (c : Chain)
    (p : Option VPhase) (u : Option (BitVec 16)) (hf : permFresh n pm) (hk : k < n) :
    permFresh n (PartialMap.insert pm k ((h, c, p, u) : PermVal)) := by
  intro k' hk'
  rw [get?_insert_ne (by omega)]
  exact hf k' hk'

theorem permFresh_delete (pm : RegMapF PermVal) (n k : Nat) (hf : permFresh n pm) :
    permFresh n (PartialMap.delete pm k) := by
  intro k' hk'
  by_cases hkk : k = k'
  · exact get?_delete_eq hkk
  · rw [get?_delete_ne hkk]; exact hf k' hk'

/-- A permit's key is below the freshness bound. -/
theorem permFresh_lt (pm : RegMapF PermVal) (n k : Nat) (h : BitVec 16) (c : Chain)
    (p : Option VPhase) (u : Option (BitVec 16)) (hf : permFresh n pm)
    (hget : PartialMap.get? pm k = some ((h, c, p, u) : PermVal)) : k < n := by
  rcases Nat.lt_or_ge k n with hk | hk
  · exact hk
  · rw [hf k hk] at hget; exact absurd hget (by simp)

/-! ## The leases -/

/-- The address of sector `i` of a buffer. -/
def sectorAddr (base : PAddr) (i : Nat) : PAddr :=
  base + BitVec.ofNat 64 (Virtio.sectorSize * i)

/-- The data buffer of a chain, WHILE IT IS IN FLIGHT: both of its sectors
at full ownership, content unconstrained.  Full ownership in both
directions, not a half for a disk write: `DevSig.Lease` asks for a
derivation for EVERY task name, so `VTask.xferIn h i` -- the fill of a
read -- must be covered even at a head that carries a write chain, and
its DMA write needs the bytes at own 1.  The driver gets the buffer back
when it collects the chain. -/
def bufLease (c : Chain) : IProp GF := iprop%
  [∗list] i ∈ List.range SPB, dmaOwn (sectorAddr c.data i) Virtio.sectorSize

instance bufLease_timeless (c : Chain) : Timeless (bufLease (GF := GF) c) := by
  unfold bufLease
  infer_instance

/-- Everything the device may touch on behalf of one armed chain. -/
def chainLease (pd : PAddr) (c : Chain) : IProp GF := iprop%
  dmaHalfAt (descAt pd c.hd) 16 c.d0 ∗
  dmaHalfAt (descAt pd c.md) 16 c.d1 ∗
  dmaHalfAt (descAt pd c.tl) 16 c.d2 ∗
  dmaHalfAt c.hdrAddr 4 c.req.type ∗
  dmaHalfAt (c.hdrAddr + 4#64) 4 0#32 ∗
  dmaHalfAt (c.hdrAddr + 8#64) 8 c.sector ∗
  dmaOwn c.status 1 ∗
  bufLease c

instance chainLease_timeless (pd : PAddr) (c : Chain) : Timeless (chainLease (GF := GF) pd c) := by
  unfold chainLease
  infer_instance

/-- One descriptor slot of the invariant.  A FREE slot is EMPTY: the queue
accounting says a pop only ever lands on a published position, whose head
is armed, so a `serve` task never meets a free descriptor and the
invariant need hold nothing there.  The driver keeps the whole free
descriptor at the context tier, which is what makes `free_desc` four
ordinary stores. -/
def headRes (γ : DiskNames) (pd : PAddr) (i : Nat) : HState → IProp GF
  | .inactive => iprop(emp)
  | .active c => iprop(⌜c.hd = i ∧ c.wf⌝ ∗ chainLease pd c ∗ ∃ bs, diskBlock γ c.blk bs)
  | .member _ => iprop(emp)

theorem headRes_inactive (γ : DiskNames) (pd : PAddr) (i : Nat) :
    headRes (GF := GF) γ pd i .inactive = iprop(emp) := rfl

theorem headRes_active (γ : DiskNames) (pd : PAddr) (i : Nat) (c : Chain) :
    headRes (GF := GF) γ pd i (.active c) =
      iprop(⌜c.hd = i ∧ c.wf⌝ ∗ chainLease pd c ∗ ∃ bs, diskBlock γ c.blk bs) := rfl

/-- A MEMBER slot costs the invariant nothing: the chain's descriptor
words are leased under its HEAD. -/
theorem headRes_member (γ : DiskNames) (pd : PAddr) (i h : Nat) :
    headRes (GF := GF) γ pd i (.member h) = iprop(emp) := rfl

/-- The used RING is entirely the device's.  The used INDEX is kept apart
(`Xv6.usedIdxCell`), because the handler reads it and a `dmaOwn` cell tells
a read nothing. -/
def usedLease (pu : PAddr) : IProp GF := iprop%
  [∗list] j ∈ List.range NUM, dmaOwn (usedElemAt pu j) 8

/-- The invariant's half of `avail->idx` and of the eight ring cells. -/
def availLease (pav : PAddr) (np : Nat) (ring : Nat → Nat) : IProp GF := iprop%
  dmaHalfAt (availIdxAt pav) 2 (wrap16 np) ∗
  ([∗list] j ∈ List.range NUM, dmaHalfAt (availRingAt pav j) 2 (BitVec.ofNat 16 (ring j)))

/-! ### Accessors -/

theorem range_mem (i n : Nat) (h : i < n) : i ∈ List.range n := List.mem_range.2 h

theorem usedElem_acc (pu : PAddr) (j : Nat) (hj : j < NUM) :
    usedLease (GF := GF) pu ⊢ dmaOwn (usedElemAt pu j) 8 ∗ (dmaOwn (usedElemAt pu j) 8 -∗ usedLease pu) := by
  unfold usedLease
  exact BigSepL.bigSepL_mem_acc (Φ := fun j => dmaOwn (GF := GF) (usedElemAt pu j) 8)
    (range_mem j NUM hj)

theorem availLease_idx (pav : PAddr) (np : Nat) (ring : Nat → Nat) :
    availLease (GF := GF) pav np ring ⊢ dmaHalfAt (availIdxAt pav) 2 (wrap16 np) ∗
      (dmaHalfAt (availIdxAt pav) 2 (wrap16 np) -∗ availLease pav np ring) := by
  unfold availLease
  iintro ⟨Hi, Hr⟩
  iframe Hi
  iintro Hi2
  iframe Hi2 Hr

theorem availLease_cell (pav : PAddr) (np : Nat) (ring : Nat → Nat) (j : Nat) (hj : j < NUM) :
    availLease (GF := GF) pav np ring ⊢
      dmaHalfAt (availRingAt pav j) 2 (BitVec.ofNat 16 (ring j)) ∗
      (dmaHalfAt (availRingAt pav j) 2 (BitVec.ofNat 16 (ring j)) -∗ availLease pav np ring) := by
  unfold availLease
  iintro ⟨Hi, Hr⟩
  icases BigSepL.bigSepL_mem_acc
      (Φ := fun j => dmaHalfAt (GF := GF) (availRingAt pav j) 2 (BitVec.ofNat 16 (ring j)))
      (range_mem j NUM hj) $$ Hr with ⟨He, Hback⟩
  iframe He
  iintro He2
  iframe Hi
  iapply Hback $$ He2

theorem headRes_acc (γ : DiskNames) (pd : PAddr) (st : Nat → HState) (i : Nat) (hi : i < NUM) :
    ([∗list] j ∈ List.range NUM, headRes (GF := GF) γ pd j (st j)) ⊢
      headRes γ pd i (st i) ∗ (headRes γ pd i (st i) -∗
        [∗list] j ∈ List.range NUM, headRes γ pd j (st j)) :=
  BigSepL.bigSepL_mem_acc (Φ := fun j => headRes (GF := GF) γ pd j (st j)) (range_mem i NUM hi)

theorem bufSector_acc (c : Chain) (i : Nat) (hi : i < SPB) :
    bufLease (GF := GF) c ⊢ dmaOwn (sectorAddr c.data i) Virtio.sectorSize ∗
      (dmaOwn (sectorAddr c.data i) Virtio.sectorSize -∗ bufLease c) := by
  unfold bufLease
  exact BigSepL.bigSepL_mem_acc
    (Φ := fun i => dmaOwn (GF := GF) (sectorAddr c.data i) Virtio.sectorSize) (range_mem i SPB hi)

/-! ## The invariant -/

/-- The coupling of the image ghost to the model: a block the driver holds
a fragment of reads as the fragment says -- UNLESS the block is in flight,
in which case the invariant itself holds the fragment (inside that
chain's row) and the device is free to move it. -/
def imgOk (v : VirtioState) (m : RegMapF (List (BitVec 8))) (P : Nat → Prop) : Prop :=
  ∀ bno bs, PartialMap.get? m bno = some bs → P bno ∨ bs = blockView v bno

/-- The live arm: the queue, the receipts, the leases. -/
def diskLive (γ : DiskNames) (c0 : VirtioCfg) (v : VirtioState)
    (pm : RegMapF PermVal) : IProp GF := iprop%
  ∃ (st : Nat → HState) (nc np lo : Nat) (ring : Nat → Nat) (m : RegMapF (List (BitVec 8)))
      (pmap : List Nat) (stg : Option Nat) (b M : Nat) (dl dl0 : List UsedRec) (nr : Nat),
    imgAuth γ m ∗
    ([∗list] i ∈ List.range NUM, headAuth γ i (st i)) ∗
    ([∗list] i ∈ List.range NUM, headRes γ c0.desc i (st i)) ∗
    usedLease c0.used ∗ availLease c0.avail np ring ∗
    diskDoneAuth γ M ∗ diskPubAuth γ np ∗ diskLoAuth γ lo ∗
    diskPubAuthM γ np ∗ posAuth γ pmap ∗ diskStageAuth γ stg ∗
    usedIdxCell (usedIdxAt c0.used) b dl ∗ doneAuth γ dl0 ∗ diskBaseFrozen γ b ∗
    dlTops dl ∗ diskReadAtAuth γ nr ∗
    ⌜v.usedIdx = wrap16 nc ∧ v.seen = wrap16 lo ∧ lo ≤ np ∧ queueOk st ring lo np ∧
      posOk pmap ring lo np ∧ stageOk stg ring lo np ∧ inflightOk v st ∧
      imgOk v m (inFlightBlk st) ∧ cachedOk v st ∧ permOk v pm st ∧ usedOk dl dl0 nc M⌝

/-- The dead arm: before `virtio_disk_init`, and never again after.

Beyond the obvious clauses: `permOk pm (fun _ => .inactive)` says NO serve
permit is out at all (a permit records an armed chain), which is what lets
the live flip install eight `.inactive` receipts; and `v.usedIdx = 0`,
`v.seen = 0` are the queue counters of a device that has never been live,
which is what the flip hands to `diskLive`'s `v.usedIdx = wrap16 nc` and
`v.seen = wrap16 lo` at `nc = lo = 0`.  Both are restored by a RESET and
moved by no step of the dead world: the used-index bump lives in
`Virtio.complete`, and the pop in `Virtio.body`'s live branch, and both of
those carry a frozen configuration that refutes this arm.

The dead arm also holds the ACCOUNTING GHOSTS at their initial values --
the invariant's halves of the pop counter and of the staged head, the
monotone published count, and the empty list of published positions.  They
are allocated at power-on, with the invariant itself: the pop counter's
other half is `diskRoot γ`, which the boot client hands the device's root
task, and the staged head's other half rides in `diskInitGhosts`. -/
def diskDead (γ : DiskNames) (v : VirtioState) (pm : RegMapF PermVal) : IProp GF := iprop%
  ∃ m : RegMapF (List (BitVec 8)),
    imgAuth γ m ∗ diskCfgAuth γ v.cfg ∗ diskLoAuth γ 0 ∗ diskPubAuthM γ 0 ∗ posAuth γ [] ∗
    diskStageAuth γ none ∗ diskBaseAuth γ 0 ∗ doneAuth γ [] ∗ diskReadAtAuth γ 0 ∗
    ⌜Virtio.live v.cfg = false ∧ noInflight v ∧ v.cache = [] ∧ imgOk v m (fun _ => False) ∧
      permOk v pm (fun _ => .inactive) ∧ v.usedIdx = 0#16 ∧ v.seen = 0#16⌝

/-- **The disk protocol**, indexed by the device's own state: what sits
beside the device's mirror inside `diskInv`. -/
def diskProto (γ : DiskNames) (v : VirtioState) : IProp GF := iprop%
  ⌜cacheOk v⌝ ∗
  ∃ (pn : Nat) (pm : RegMapF PermVal), permAuth γ pm ∗
    ⌜permFresh pn pm ∧ permInj pm ∧ pushedUniq v⌝ ∗
    (diskDead γ v pm ∨
     ∃ c0 : VirtioCfg, diskCfgFrozen γ c0 ∗
       ⌜v.cfg = c0 ∧ Virtio.live c0 = true ∧ c0.qnum.toNat = NUM⌝ ∗ diskLive γ c0 v pm)

instance headRes_timeless (γ : DiskNames) (pd : PAddr) (i : Nat) (s : HState) :
    Timeless (headRes (GF := GF) γ pd i s) := by
  cases s with
  | inactive =>
    show Timeless (iprop(emp) : IProp GF)
    infer_instance
  | active c =>
    show Timeless iprop(⌜c.hd = i ∧ c.wf⌝ ∗ chainLease pd c ∗ ∃ bs, diskBlock γ c.blk bs)
    unfold chainLease diskBlock
    infer_instance
  | member _ =>
    show Timeless (iprop(emp) : IProp GF)
    infer_instance

instance usedLease_timeless (pu : PAddr) : Timeless (usedLease (GF := GF) pu) := by
  unfold usedLease; infer_instance
instance availLease_timeless (pav : PAddr) (np : Nat) (ring : Nat → Nat) :
    Timeless (availLease (GF := GF) pav np ring) := by unfold availLease; infer_instance
instance diskLive_timeless (γ : DiskNames) (c0 : VirtioCfg) (v : VirtioState)
    (pm : RegMapF PermVal) : Timeless (diskLive (GF := GF) γ c0 v pm) := by
  unfold diskLive headAuth diskDoneAuth diskPubAuth diskLoAuth diskStageAuth imgAuth
    diskBaseFrozen diskReadAtAuth
  infer_instance
instance diskDead_timeless (γ : DiskNames) (v : VirtioState) (pm : RegMapF PermVal) :
    Timeless (diskDead (GF := GF) γ v pm) := by
  unfold diskDead diskCfgAuth diskLoAuth diskStageAuth imgAuth diskBaseAuth diskReadAtAuth
  infer_instance

instance permAuth_timeless (γ : DiskNames) (pm : RegMapF PermVal) :
    Timeless (permAuth (GF := GF) γ pm) := by unfold permAuth; infer_instance

instance diskProto_timeless (γ : DiskNames) (v : VirtioState) :
    Timeless (diskProto (GF := GF) γ v) := by
  unfold diskProto diskCfgFrozen permAuth
  infer_instance

/-- **The disk invariant**: the device's mirror beside the protocol. -/
def diskInv (γ : DiskNames) : IProp GF := devInvR diskN .virtio (diskProto γ)

instance diskInv_persistent (γ : DiskNames) : Persistent (diskInv (GF := GF) γ) := by
  unfold diskInv devInvR; infer_instance

/-! ## The geometry, and the lock's payload -/

section payload
variable [CurCtx]

/-- **The geometry**, persistent: the three page pointers of `struct disk`
(read-only after `virtio_disk_init`) and the frozen configuration they
were written into.  `wce c0 = false`: xv6 clears both `VIRTIO_BLK_F_FLUSH`
and `VIRTIO_BLK_F_CONFIG_WCE` during feature negotiation, so the device is
in write-THROUGH mode and a write request cannot complete before its
payload has reached the durable image (`Virtio.completeOk`). -/
def diskGeom (γ : DiskNames) (pd pav pu : PAddr) : IProp GF := iprop%
  ∃ c0 : VirtioCfg, diskCfgFrozen γ c0 ∗
    ⌜c0.desc = pd ∧ c0.avail = pav ∧ c0.used = pu ∧ Virtio.live c0 = true ∧
      c0.qnum.toNat = NUM ∧ Virtio.wce c0 = false⌝ ∗
    wordPointsTo aDescPtr 8 DFrac.discard pd ∗
    wordPointsTo aAvailPtr 8 DFrac.discard pav ∗
    wordPointsTo aUsedPtr 8 DFrac.discard pu

instance diskGeom_persistent (γ : DiskNames) (pd pav pu : PAddr) :
    Persistent (diskGeom (GF := GF) γ pd pav pu) := by
  unfold diskGeom diskCfgFrozen wordPointsTo; infer_instance

/-- A FREE descriptor, on the driver's side: `free_desc` zeroed its
sixteen bytes, and the driver holds ALL of them -- the invariant holds
nothing for a free slot, because the accounting rules out a fetch there. -/
def freeSlotRes (ξ : CtxId) (pd : PAddr) (i : Nat) : IProp GF := iprop%
  ctxBytes ξ (descAt pd i) 16 (DFrac.own 1) 0

/-- An ARMED descriptor, on the driver's side: the other halves of the
chain's three descriptor words and of its request header, and
`disk.info[hd].b`, the `struct buf` the interrupt handler wakes. -/
def claimRes (ξ : CtxId) (pd : PAddr) (c : Chain) : IProp GF := iprop%
  ctxBytes ξ (descAt pd c.hd) 16 (DFrac.own (1 : Qp).half) c.d0 ∗
  ctxBytes ξ (descAt pd c.md) 16 (DFrac.own (1 : Qp).half) c.d1 ∗
  ctxBytes ξ (descAt pd c.tl) 16 (DFrac.own (1 : Qp).half) c.d2 ∗
  ctxBytes ξ c.hdrAddr 16 (DFrac.own (1 : Qp).half) c.hdr ∗
  wordAtN ξ (aInfoB c.hd) 8 (DFrac.own 1) c.bp

/-- One slot of the payload: `disk.free[i]` and whatever the receipt says. -/
def slotBody (ξ : CtxId) (pd : PAddr) (i : Nat) : HState → IProp GF
  | .inactive => iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 1#8 ∗ freeSlotRes ξ pd i)
  | .active c => iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 0#8 ∗ claimRes ξ pd c)
  | .member _ => iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 0#8)

def slotRes (γ : DiskNames) (ξ : CtxId) (pd : PAddr) (i : Nat) : IProp GF := iprop%
  ∃ s : HState, headTok γ i s ∗ slotBody ξ pd i s

theorem slotBody_inactive (ξ : CtxId) (pd : PAddr) (i : Nat) :
    slotBody (GF := GF) ξ pd i .inactive =
      iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 1#8 ∗ freeSlotRes ξ pd i) := rfl

theorem slotBody_active (ξ : CtxId) (pd : PAddr) (i : Nat) (c : Chain) :
    slotBody (GF := GF) ξ pd i (.active c) =
      iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 0#8 ∗ claimRes ξ pd c) := rfl

/-- A MEMBER slot on the driver's side: TAKEN (`disk.free[i] = 0`) and
nothing else -- the descriptor's own words are the HEAD's `claimRes`. -/
theorem slotBody_member (ξ : CtxId) (pd : PAddr) (i h : Nat) :
    slotBody (GF := GF) ξ pd i (.member h) =
      iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 0#8) := rfl

/-- **The payload of `disk.vdisk_lock`** (Rocq's `disk_res`): the
publisher's and the handler's halves of the counters (the watermark
included -- the invariant holds the other half, `Xv6.diskReadAtAuth`, and
the bump goes through `Xv6.disk_deposit`), the staged head,
`disk.used_idx` at the handler watermark, the driver's halves of
`avail->idx` and of the eight ring cells, and the eight descriptor slots
with their receipts. -/
def diskRes (γ : DiskNames) (pd pav pu : PAddr) (ξ : CtxId) : IProp GF := iprop%
  ∃ (np nr : Nat) (stg : Option Nat) (ring : Nat → Nat),
    diskPub γ np ∗ diskReadAt γ nr ∗ diskStage γ stg ∗ diskDoneLb γ nr ∗
    wordAtN ξ aUsedIdx 2 (DFrac.own 1) (wrap16 nr) ∗
    ctxBytes ξ (availIdxAt pav) 2 (DFrac.own (1 : Qp).half) (wrap16 np) ∗
    ([∗list] j ∈ List.range NUM,
      ctxBytes ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) (BitVec.ofNat 16 (ring j))) ∗
    ([∗list] i ∈ List.range NUM, slotRes γ ξ pd i)

instance instCtxMorphSlotBody (pd : PAddr) (i : Nat) (s : HState) :
    CtxMorph (GF := GF) (fun ξ => slotBody ξ pd i s) := by
  cases s with
  | inactive =>
    show CtxMorph (fun ξ => iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 1#8 ∗ freeSlotRes ξ pd i))
    unfold freeSlotRes
    infer_instance
  | active c =>
    show CtxMorph (fun ξ => iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 0#8 ∗ claimRes ξ pd c))
    unfold claimRes
    infer_instance
  | member _ =>
    show CtxMorph (fun ξ => iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 0#8))
    infer_instance

instance instCtxMorphSlotRes (γ : DiskNames) (pd : PAddr) (i : Nat) :
    CtxMorph (GF := GF) (fun ξ => slotRes γ ξ pd i) := by
  unfold slotRes
  exact instCtxMorphExists (fun (s : HState) ξ => iprop(headTok γ i s ∗ slotBody ξ pd i s))

instance instCtxMorphRingCells (pav : PAddr) (ring : Nat → Nat) :
    CtxMorph (GF := GF) (fun ξ => iprop([∗list] j ∈ List.range NUM,
      ctxBytes ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) (BitVec.ofNat 16 (ring j)))) :=
  ctxMorph_bigSepL _ (fun _ j ξ =>
    ctxBytes ξ (availRingAt pav j) 2 (DFrac.own (1 : Qp).half) (BitVec.ofNat 16 (ring j)))
    (fun _ _ => inferInstance)

instance instCtxMorphSlots (γ : DiskNames) (pd : PAddr) :
    CtxMorph (GF := GF) (fun ξ => iprop([∗list] i ∈ List.range NUM, slotRes γ ξ pd i)) :=
  ctxMorph_bigSepL _ (fun _ i ξ => slotRes γ ξ pd i) (fun _ _ => inferInstance)

instance instCtxMorphDiskRes (γ : DiskNames) (pd pav pu : PAddr) :
    CtxMorph (GF := GF) (diskRes γ pd pav pu) := by
  unfold diskRes
  infer_instance

end payload

end

end Xv6

