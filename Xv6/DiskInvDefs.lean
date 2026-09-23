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
  because each one is guarded on a request being in flight.
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
  sectors of `b->data` for a disk READ (the device writes them) or a HALF
  for a disk WRITE (it only reads them), and the block's image fragment;
* when FREE, a half of the descriptor's sixteen ZERO bytes: `free_desc`
  zeroes a descriptor it gives back, and the invariant keeping its half
  is what makes a `fetch` at an unarmed head read a descriptor with no
  NEXT flag and STALL, instead of parsing a request out of whatever is
  in the queue page;

and, once, the SERVE PERMITS (`permAuth`/`permTok`, see below: what a
`serve` task takes at its first `get` so that the receipt of the head it
is serving cannot move under it), the whole used ring (`usedLease`: `used->idx` and the eight
elements at own 1 -- the used page is entirely the device's), a half of
`avail->idx` and of the eight ring cells (`availLease`), the completion
counter `nc` as a mono-nat authority with `v.usedIdx = wrap16 nc`, and
the coupling `inflightOk v st`: every request the device holds IS the
chain armed at that head.

---------------------------------------------------------------------
WHAT IS NOT HERE, AND WHY.

* No `VQ.Ok` inside the invariant.  The device's `complete` and its pop
  have to be admitted at every state, so `nc ≤ lo ≤ np` cannot be
  maintained against them here.  The record and its preservation lemmas
  live in `Xv6/VirtioQueue.lean` for the driver's side, which is also
  where they are NEEDED: the driver's future `publish`/`reclaim` must
  show that no serve permit for the head is out, and it is the queue
  accounting that bounds the permits on a head to the one `serve` task
  that is running (`Xv6/DiskInv.lean`'s header).
* No `seen` clause.  Same reason: the pop bumps `seen` unconditionally.
* The install of a fetched request is NOT assumed any more; the serve
  permit below is what pays for it (see `Xv6/DiskInv.lean`).
* The CONTENT of a disk read's data transfer is existential
  (`dmaOwn`, not `dmaOwnAt`).  The device computes the payload from a
  SNAPSHOT of its image taken at the task's `get` and writes it several
  steps later; a per-step lease has no way to say the image did not move
  in between (Rocq's model reads and writes in one step).  Making it
  precise needs a persistent, generation-keyed snapshot of the block --
  see the report.
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
  [gmPermG : GhostMapG GF Nat (BitVec 16 × HState) RegMapF]

attribute [reducible, instance] DiskG.gvCfgG DiskG.gvHeadG DiskG.gvStageG DiskG.gmImgG DiskG.mnG
attribute [reducible, instance] DiskG.gmPermG

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
  /-- the handler watermark (`disk.used_idx`) -/
  nr : GName
  /-- the head staged between the ring store and the index bump -/
  stage : GName
  /-- the serve permits -/
  perm : GName

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

/-- The published count: the lock payload's half. -/
def diskPubAuth (γ : DiskNames) (n : Nat) : IProp GF := γ.np ↪VAR{.own (1 : Qp).half} n
/-- The published count: the publisher's half (Rocq's `disk_pub`). -/
def diskPub (γ : DiskNames) (n : Nat) : IProp GF := γ.np ↪VAR{.own (1 : Qp).half} n
/-- The handler watermark (`disk.used_idx`), the payload's half. -/
def diskReadAtAuth (γ : DiskNames) (n : Nat) : IProp GF := γ.nr ↪VAR{.own (1 : Qp).half} n
/-- The handler watermark, the handler's half (Rocq's `disk_read_at`). -/
def diskReadAt (γ : DiskNames) (n : Nat) : IProp GF := γ.nr ↪VAR{.own (1 : Qp).half} n
/-- The head staged between the ring store and the `avail->idx` bump. -/
def diskStageAuth (γ : DiskNames) (s : Option Nat) : IProp GF :=
  γ.stage ↪VAR{.own (1 : Qp).half} s
/-- The stage, the publisher's half (Rocq's `disk_stage`). -/
def diskStage (γ : DiskNames) (s : Option Nat) : IProp GF :=
  γ.stage ↪VAR{.own (1 : Qp).half} s

/-! ## The serve permits

A `serve h` task must know, at the step where it installs the request it
parsed, that head `h` still carries the chain whose descriptors it read.
That is not a monotone fact, so no persistent token can carry it: the
task takes an EXCLUSIVE permit out of the invariant at its first `get`
(`MachCSL.DevM.LeaseL`'s `.get` arm may update the invariant, and the
invariant is re-established with the permit's key recorded in it), and
holds it to its last step.  While a permit for `h` is out, the receipt of
`h` cannot move: any move would have to change the permit's value, which
needs the permit back.

The permits are a ghost map keyed by a serial number, so taking one is
always possible -- `permFresh` keeps a bound above which the map is
empty.  The driver's future `publish`/`reclaim` accessors, which DO move
a receipt, will have to show that no permit for that head is out; that is
where the queue record's `nc ≤ lo ≤ np` accounting (`Xv6.VQ.Ok`) belongs,
since it is what rules out a pop of a head that is already in flight or
not armed at all. -/

/-- What a permit records: the head, and the receipt that head carried
when the permit was taken. -/
abbrev PermVal : Type := BitVec 16 × HState

/-- The permits the invariant has handed out. -/
def permAuth (γ : DiskNames) (pm : RegMapF PermVal) : IProp GF := γ.perm ↪●MAP pm

/-- **A serve permit**: exclusive, and pins head `h`'s receipt to `s`. -/
def permTok (γ : DiskNames) (k : Nat) (h : BitVec 16) (s : HState) : IProp GF :=
  γ.perm ↪◯MAP[k] ((h, s) : PermVal)

/-- The receipt of a head, as a permit sees it: a head outside the queue
is free by definition. -/
def hstateAt (st : Nat → HState) (h : BitVec 16) : HState :=
  if h.toNat < NUM then st h.toNat else .inactive

/-- Every permit agrees with the receipt it names. -/
def permOk (pm : RegMapF PermVal) (st : Nat → HState) : Prop :=
  ∀ k h s, PartialMap.get? pm k = some ((h, s) : PermVal) → s = hstateAt st h

/-- Keys at or above `n` are free, so `n` is a key a permit may take. -/
def permFresh (n : Nat) (pm : RegMapF PermVal) : Prop :=
  ∀ k, n ≤ k → PartialMap.get? pm k = none

theorem permOk_insert (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat) (h : BitVec 16)
    (hok : permOk pm st) : permOk (PartialMap.insert pm k ((h, hstateAt st h) : PermVal)) st := by
  intro k' h' s' hget
  by_cases hk : k = k'
  · rw [get?_insert_eq hk] at hget
    cases hget
    rfl
  · exact hok k' h' s' (by rwa [get?_insert_ne hk] at hget)

theorem permOk_delete (pm : RegMapF PermVal) (st : Nat → HState) (k : Nat) (hok : permOk pm st) :
    permOk (PartialMap.delete pm k) st := by
  intro k' h' s' hget
  by_cases hk : k = k'
  · rw [get?_delete_eq hk] at hget; exact absurd hget (by simp)
  · exact hok k' h' s' (by rwa [get?_delete_ne hk] at hget)

theorem permFresh_insert (pm : RegMapF PermVal) (n : Nat) (h : BitVec 16) (s : HState)
    (hf : permFresh n pm) : permFresh (n + 1) (PartialMap.insert pm n ((h, s) : PermVal)) := by
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

/-- One descriptor slot of the invariant.  A FREE slot is not empty: the
driver's `free_desc` zeroes the descriptor, and the invariant keeps a half
of the sixteen zero bytes -- which is what makes a `fetch` at a head the
driver has not armed read a descriptor with no NEXT flag, and so STALL
rather than parse a request out of nothing. -/
def headRes (γ : DiskNames) (pd : PAddr) (i : Nat) : HState → IProp GF
  | .inactive => dmaHalfAt (descAt pd i) 16 (0 : BitVec (8 * 16))
  | .active c => iprop(⌜c.hd = i ∧ c.wf⌝ ∗ chainLease pd c ∗ ∃ bs, diskBlock γ c.blk bs)

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
  ∃ (st : Nat → HState) (nc np : Nat) (ring : Nat → Nat) (m : RegMapF (List (BitVec 8))),
    imgAuth γ m ∗
    ([∗list] i ∈ List.range NUM, headAuth γ i (st i)) ∗
    ([∗list] i ∈ List.range NUM, headRes γ c0.desc i (st i)) ∗
    usedLease c0.used ∗ availLease c0.avail np ring ∗
    diskDoneAuth γ nc ∗ diskPubAuth γ np ∗
    ⌜v.usedIdx = wrap16 nc ∧ inflightOk v st ∧ imgOk v m (inFlightBlk st) ∧ cachedOk v st ∧
      permOk pm st⌝

/-- The dead arm: before `virtio_disk_init`, and never again after. -/
def diskDead (γ : DiskNames) (v : VirtioState) : IProp GF := iprop%
  ∃ m : RegMapF (List (BitVec 8)), imgAuth γ m ∗ diskCfgAuth γ v.cfg ∗
    ⌜Virtio.live v.cfg = false ∧ noInflight v ∧ v.cache = [] ∧ imgOk v m (fun _ => False)⌝

/-- **The disk protocol**, indexed by the device's own state: what sits
beside the device's mirror inside `diskInv`. -/
def diskProto (γ : DiskNames) (v : VirtioState) : IProp GF := iprop%
  ⌜cacheOk v⌝ ∗
  ∃ (pn : Nat) (pm : RegMapF PermVal), permAuth γ pm ∗ ⌜permFresh pn pm⌝ ∗
    (diskDead γ v ∨
     ∃ c0 : VirtioCfg, diskCfgFrozen γ c0 ∗
       ⌜v.cfg = c0 ∧ Virtio.live c0 = true ∧ c0.qnum.toNat = NUM⌝ ∗ diskLive γ c0 v pm)

instance headRes_timeless (γ : DiskNames) (pd : PAddr) (i : Nat) (s : HState) :
    Timeless (headRes (GF := GF) γ pd i s) := by
  cases s with
  | inactive =>
    show Timeless (dmaHalfAt (GF := GF) (descAt pd i) 16 (0 : BitVec (8 * 16)))
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
  unfold diskLive headAuth diskDoneAuth diskPubAuth imgAuth; infer_instance
instance diskDead_timeless (γ : DiskNames) (v : VirtioState) :
    Timeless (diskDead (GF := GF) γ v) := by unfold diskDead diskCfgAuth imgAuth; infer_instance

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
sixteen bytes, and the driver holds the other half of them. -/
def freeSlotRes (ξ : CtxId) (pd : PAddr) (i : Nat) : IProp GF := iprop%
  ctxBytes ξ (descAt pd i) 16 (DFrac.own (1 : Qp).half) 0

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
