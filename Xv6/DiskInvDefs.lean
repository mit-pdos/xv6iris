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

* No COMPLETION-side accounting: the used-index cell's history, a
  per-completion record of the head reported at each used-ring position,
  the completed request's status byte and the `topLb` bound on its DMA
  writes.  That is what the five remaining accessors of
  `Xv6/DiskAcc.lean` need; the handler watermark `diskReadAt` is still a
  WHOLE ghost variable in the lock payload, because the invariant never
  mentions it.
* The CONTENT of a disk read's data transfer is existential (`dmaOwn`,
  not `dmaOwnAt`).  The device computes the payload from a SNAPSHOT of its
  image taken at the task's `get` and writes it several steps later; a
  per-step lease has no way to say the image did not move in between.
  Making it precise needs a persistent, generation-keyed snapshot of the
  block.
* No crash permits, no `Q`, no `disk_seq_permit` (the port drops Rocq's
  crash story), and no TSO floor rows (`fl0`/`fl1`/`flr`/`pos`).
-/
import Xv6.VirtioQueue
import Xv6.KallocDefs
import MachCSL.WpDevDma

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
  [gmPermG : GhostMapG GF Nat (BitVec 16 × Chain) RegMapF]
  /-- the PUBLISHED POSITIONS (see `posRec`): a monotone list of heads,
  one entry per position, from which a persistent per-position record may
  be taken at any time -/
  [mlPosG : MonoListG GF Nat]

attribute [reducible, instance] DiskG.gvCfgG DiskG.gvHeadG DiskG.gvStageG DiskG.gmImgG DiskG.mnG
attribute [reducible, instance] DiskG.gmPermG
attribute [reducible, instance] DiskG.mlPosG

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
  /-- the completed count (`used->idx`), a mono-nat -/
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

/-- The completed count, as the invariant holds it. -/
def diskDoneAuth (γ : DiskNames) (n : Nat) : IProp GF :=
  MonoNat.auth_own γ.nc (DFrac.own 1) (.ofNat n)
/-- At least `n` requests have completed (persistent). -/
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
/-- The handler watermark (`disk.used_idx`), Rocq's `disk_read_at`.  The
INVARIANT never mentions it -- it is the driver's own count of the used
elements it has consumed -- so the lock payload holds the whole ghost
variable rather than a half, and the interrupt handler may bump it with
nothing else in hand. -/
def diskReadAt (γ : DiskNames) (n : Nat) : IProp GF := γ.nr ↪VAR{.own 1} n
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

theorem diskReadAt_update (γ : DiskNames) (n n' : Nat) :
    diskReadAt (GF := GF) γ n ⊢ |==> diskReadAt γ n' := by
  unfold diskReadAt
  iintro H
  iapply ghost_var_update n' γ.nr $$ H

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

/-- What a permit records: the head, and the CHAIN armed there. -/
abbrev PermVal : Type := BitVec 16 × Chain

/-- The permits the invariant has handed out. -/
def permAuth (γ : DiskNames) (pm : RegMapF PermVal) : IProp GF := γ.perm ↪●MAP pm

/-- **A serve permit**: exclusive, and pins head `h`'s receipt to `.active c`. -/
def permTok (γ : DiskNames) (k : Nat) (h : BitVec 16) (c : Chain) : IProp GF :=
  γ.perm ↪◯MAP[k] ((h, c) : PermVal)

/-- Every permit names a descriptor of the queue, armed with the chain it
records. -/
def permOk (pm : RegMapF PermVal) (st : Nat → HState) : Prop :=
  ∀ k h c, PartialMap.get? pm k = some ((h, c) : PermVal) →
    h.toNat < NUM ∧ st h.toNat = .active c

/-- Keys at or above `n` are free, so `n` is a key a permit may take. -/
def permFresh (n : Nat) (pm : RegMapF PermVal) : Prop :=
  ∀ k, n ≤ k → PartialMap.get? pm k = none

/-- No permit at all: the dead arm, and the state the live flip starts from. -/
theorem permOk_none (pm : RegMapF PermVal) (st : Nat → HState)
    (h : permOk pm (fun _ => .inactive)) (k : Nat) (hh : BitVec 16) (c : Chain) :
    PartialMap.get? pm k ≠ some ((hh, c) : PermVal) := by
  intro hget
  have := (h k hh c hget).2
  exact absurd this (by simp)

theorem permOk_insert (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat) (h : BitVec 16)
    (c : Chain) (hlt : h.toNat < NUM) (hst : st h.toNat = .active c) (hok : permOk pm st) :
    permOk (PartialMap.insert pm k ((h, c) : PermVal)) st := by
  intro k' h' c' hget
  by_cases hk : k = k'
  · rw [get?_insert_eq hk] at hget
    cases hget
    exact ⟨hlt, hst⟩
  · exact hok k' h' c' (by rwa [get?_insert_ne hk] at hget)

theorem permOk_delete (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat) (hok : permOk pm st) :
    permOk (PartialMap.delete pm k) st := by
  intro k' h' c' hget
  by_cases hk : k = k'
  · rw [get?_delete_eq hk] at hget; exact absurd hget (by simp)
  · exact hok k' h' c' (by rwa [get?_delete_ne hk] at hget)

/-- Arming a head no permit names keeps every permit honest. -/
theorem permOk_arm (pm : RegMapF PermVal) (st : Nat → HState) (i : Nat) (c : Chain)
    (hok : permOk pm st) (hfree : st i = .inactive) :
    permOk pm (fun j => if j = i then .active c else st j) := by
  intro k' h' c' hget
  obtain ⟨hlt, hst⟩ := hok k' h' c' hget
  refine ⟨hlt, ?_⟩
  have hne : h'.toNat ≠ i := by
    intro he; rw [he, hfree] at hst; exact absurd hst (by simp)
  simp only [if_neg hne]
  exact hst

theorem permFresh_insert (pm : RegMapF PermVal) (n : Nat) (h : BitVec 16) (c : Chain)
    (hf : permFresh n pm) : permFresh (n + 1) (PartialMap.insert pm n ((h, c) : PermVal)) := by
  intro k hk
  rw [get?_insert_ne (by omega)]
  exact hf k (by omega)

theorem permFresh_delete (pm : RegMapF PermVal) (n k : Nat) (hf : permFresh n pm) :
    permFresh n (PartialMap.delete pm k) := by
  intro k' hk'
  by_cases hkk : k = k'
  · exact get?_delete_eq hkk
  · rw [get?_delete_ne hkk]; exact hf k' hk'

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

theorem headRes_inactive (γ : DiskNames) (pd : PAddr) (i : Nat) :
    headRes (GF := GF) γ pd i .inactive = iprop(emp) := rfl

theorem headRes_active (γ : DiskNames) (pd : PAddr) (i : Nat) (c : Chain) :
    headRes (GF := GF) γ pd i (.active c) =
      iprop(⌜c.hd = i ∧ c.wf⌝ ∗ chainLease pd c ∗ ∃ bs, diskBlock γ c.blk bs) := rfl

/-- The used ring is ENTIRELY the device's. -/
def usedLease (pu : PAddr) : IProp GF := iprop%
  dmaOwn (usedIdxAt pu) 2 ∗ ([∗list] j ∈ List.range NUM, dmaOwn (usedElemAt pu j) 8)

/-- The invariant's half of `avail->idx` and of the eight ring cells. -/
def availLease (pav : PAddr) (np : Nat) (ring : Nat → Nat) : IProp GF := iprop%
  dmaHalfAt (availIdxAt pav) 2 (wrap16 np) ∗
  ([∗list] j ∈ List.range NUM, dmaHalfAt (availRingAt pav j) 2 (BitVec.ofNat 16 (ring j)))

/-! ### Accessors -/

theorem range_mem (i n : Nat) (h : i < n) : i ∈ List.range n := List.mem_range.2 h

theorem usedElem_acc (pu : PAddr) (j : Nat) (hj : j < NUM) :
    usedLease (GF := GF) pu ⊢ dmaOwn (usedElemAt pu j) 8 ∗ (dmaOwn (usedElemAt pu j) 8 -∗ usedLease pu) := by
  unfold usedLease
  iintro ⟨Hi, Hr⟩
  icases BigSepL.bigSepL_mem_acc (Φ := fun j => dmaOwn (GF := GF) (usedElemAt pu j) 8)
      (range_mem j NUM hj) $$ Hr with ⟨He, Hback⟩
  iframe He
  iintro He2
  iframe Hi
  iapply Hback $$ He2

theorem usedIdx_acc (pu : PAddr) :
    usedLease (GF := GF) pu ⊢ dmaOwn (usedIdxAt pu) 2 ∗ (dmaOwn (usedIdxAt pu) 2 -∗ usedLease pu) := by
  unfold usedLease
  iintro ⟨Hi, Hr⟩
  iframe Hi
  iintro Hi2
  iframe Hi2 Hr

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
      (pmap : List Nat) (stg : Option Nat),
    imgAuth γ m ∗
    ([∗list] i ∈ List.range NUM, headAuth γ i (st i)) ∗
    ([∗list] i ∈ List.range NUM, headRes γ c0.desc i (st i)) ∗
    usedLease c0.used ∗ availLease c0.avail np ring ∗
    diskDoneAuth γ nc ∗ diskPubAuth γ np ∗ diskLoAuth γ lo ∗
    diskPubAuthM γ np ∗ posAuth γ pmap ∗ diskStageAuth γ stg ∗
    ⌜v.usedIdx = wrap16 nc ∧ v.seen = wrap16 lo ∧ lo ≤ np ∧ queueOk st ring lo np ∧
      posOk pmap ring lo np ∧ stageOk stg ring lo np ∧ inflightOk v st ∧
      imgOk v m (inFlightBlk st) ∧ cachedOk v st ∧ permOk pm st⌝

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
    diskStageAuth γ none ∗
    ⌜Virtio.live v.cfg = false ∧ noInflight v ∧ v.cache = [] ∧ imgOk v m (fun _ => False) ∧
      permOk pm (fun _ => .inactive) ∧ v.usedIdx = 0#16 ∧ v.seen = 0#16⌝

/-- **The disk protocol**, indexed by the device's own state: what sits
beside the device's mirror inside `diskInv`. -/
def diskProto (γ : DiskNames) (v : VirtioState) : IProp GF := iprop%
  ⌜cacheOk v⌝ ∗
  ∃ (pn : Nat) (pm : RegMapF PermVal), permAuth γ pm ∗ ⌜permFresh pn pm⌝ ∗
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

instance usedLease_timeless (pu : PAddr) : Timeless (usedLease (GF := GF) pu) := by
  unfold usedLease; infer_instance
instance availLease_timeless (pav : PAddr) (np : Nat) (ring : Nat → Nat) :
    Timeless (availLease (GF := GF) pav np ring) := by unfold availLease; infer_instance
instance diskLive_timeless (γ : DiskNames) (c0 : VirtioCfg) (v : VirtioState)
    (pm : RegMapF PermVal) : Timeless (diskLive (GF := GF) γ c0 v pm) := by
  unfold diskLive headAuth diskDoneAuth diskPubAuth diskLoAuth diskStageAuth imgAuth
  infer_instance
instance diskDead_timeless (γ : DiskNames) (v : VirtioState) (pm : RegMapF PermVal) :
    Timeless (diskDead (GF := GF) γ v pm) := by
  unfold diskDead diskCfgAuth diskLoAuth diskStageAuth imgAuth; infer_instance

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

def slotRes (γ : DiskNames) (ξ : CtxId) (pd : PAddr) (i : Nat) : IProp GF := iprop%
  ∃ s : HState, headTok γ i s ∗ slotBody ξ pd i s

theorem slotBody_inactive (ξ : CtxId) (pd : PAddr) (i : Nat) :
    slotBody (GF := GF) ξ pd i .inactive =
      iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 1#8 ∗ freeSlotRes ξ pd i) := rfl

theorem slotBody_active (ξ : CtxId) (pd : PAddr) (i : Nat) (c : Chain) :
    slotBody (GF := GF) ξ pd i (.active c) =
      iprop(wordAtN ξ (aFree i) 1 (DFrac.own 1) 0#8 ∗ claimRes ξ pd c) := rfl

/-- **The payload of `disk.vdisk_lock`** (Rocq's `disk_res`): the
publisher's and the handler's halves of the counters, the staged head,
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

