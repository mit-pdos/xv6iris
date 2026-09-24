/-
**THE PER-BUFFER ESCROW** (`kernel/bio.c`): the transit box that carries a
buffer's travelling content -- `valid`, `dev`, the `bufOwn` bundle
(`blockno`, the pinned `disk` flag, the 1024 data bytes) and the block's
disk-image fragment -- from the holder that releases it to the holder that
next acquires it.

A port of the escrow part of Rocq `BioInv.v` (its `BioBox` section), over
this port's `MachCSL.CtxBox`.  The box's payload family (`Xv6.bufHdr`,
`Xv6.bufRest`, `Xv6.bufBoxPay`, `Xv6.bufBox`) and its two payload rows
(`Xv6.bufSlotRegs`, `Xv6.bufSlpBox`) are in `Xv6/BcacheInv.lean`, where the
cache's invariant seats them; this file is the SIX OPERATIONS over them.

**Why neither lock can be the handover point** (Rocq `BioInv.v`'s header):

1. a releasing holder's content must be reachable from the SLEEPLOCK side by
   the end of `releasesleep`, because a blocked waiter's `acquiresleep` can
   return -- and its caller touch `b->valid` / `b->data` -- before the
   releaser's `refcnt--` runs.  So the content cannot ride `bcache.lock`.
2. `bget`'s miss path rewrites `dev`/`blockno`/`valid` under `bcache.lock`
   ALONE (at `refcnt == 0`), and its scan reads every buffer's
   `dev`/`blockno` there.  So the content cannot be wholly inside the
   sleeplock chain either.

Hence a namespace invariant, openable atomically at any instruction, with
the content parked in its own STAMPED context; the two sides reach it
through the box's registers:

* the `bcache.lock` side (L1) opens a WINDOW (`bufEscrow_withdraw`) over the
  header at `refcnt == 0`, rewrites `dev`/`blockno`/`valid`, and DEPOSITS
  the header at the new identity (`bufEscrow_recycle`), which mints the
  chain's first reference;
* the sleeplock side (L2) CHECKS OUT the whole bundle against a reference
  (`bufEscrow_take`, what `bread` runs after `acquiresleep`) and PARKS it
  back (`bufEscrow_deposit`, what `brelse` runs at its first instruction).

**Parametric in the key-cell fractions.**  `Xv6.bufOwn` holds `b->blockno`
at a half and `Xv6.bufHold0` holds `b->dev` at a half, the other halves
living in `bcache.lock`'s `Xv6.bkeyAt` forever.  Everything below takes the
two fractions `qd` (dev) and `qb` (blockno) as parameters, and
`bufHold0_travel` is the bridge at the fractions `Xv6/BcacheInv.lean`
currently uses; if those change, only that one lemma moves.

**Deviations from Rocq**, beyond `MachCSL/CtxBox.lean`'s own (the unit
references, and withdraw/deposit at count zero):

* Rocq's payload is the client view `bio_view`'s `bv_clean`/`bv_dirty`, with
  an UNCACHED POOL that holds the bundle of every block not in the cache.
  This port has no log layer and no pool: the travelling payload is exactly
  the block's `Xv6.diskBlock` image fragment, which is what `Xv6.bufHold0`
  carries, and the recycler must therefore present the NEW block's fragment
  and takes the old one away.
* the two floor-consuming operations, `bufEscrow_take` and
  `bufEscrow_withdraw`, each want a `MachCSL.ctxFloor` of the CALLER's
  context covering the box's stamp.  Those floors ride the payload rows
  (`Xv6.bcacheResAt`'s floor slot, `Xv6.bufSlpBox`'s park floor) and the
  acquire edge (`Xv6.ACQUIRESLEEP_LLB`); see the header of
  `Xv6/BcacheInv.lean`.  `bread` is what consumes them.
-/
import Xv6.BcacheInv
import MachCSL.CtxBox

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedSectionVars false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
variable [BcacheG GF] [SleepLockG GF] [DiskG GF] [CurCtx]

instance diskBlock_timeless (γd : DiskNames) (b : Nat) (bs : List (BitVec 8)) :
    Timeless (diskBlock (GF := GF) γd b bs) := by unfold diskBlock; infer_instance

/-! ## The travelling content, as the bio proofs hold it -/

/-- **WHAT TRAVELS** (Rocq's `bio_hold0` minus the sleeplock row and the
chain's tokens): the `valid` cell in full at whatever it says, the two key
cells at the caller's fractions, the pinned `disk` flag, the 1024 data
bytes, and -- WHEN `valid` IS SET -- the block's disk-image fragment.  This
is exactly what `brelse` deposits and what `bread` takes. -/
def bufTravelV (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno v : BitVec 32)
    (bs : List (BitVec 8)) : IProp GF := iprop%
  ⌜bs.length = BSIZE⌝ ∗
  wordPointsTo (aBufValid (bnode k)) 4 (DFrac.own 1) v ∗
  wordPointsTo (aBufDev (bnode k)) 4 (DFrac.own qd) dev ∗
  wordPointsTo (aBufBlockno (bnode k)) 4 (DFrac.own qb) bno ∗
  wordPointsTo (aBufDisk (bnode k)) 4 (DFrac.own 1) 0#32 ∗
  byteBuf (aBufData (bnode k)) (DFrac.own 1) bs ∗
  bufPayV γd ((dev, bno) : BufId) v

/-- The same with the fragment NAMED: what a holder of a valid buffer has. -/
def bufTravel (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno v : BitVec 32)
    (bs bsd : List (BitVec 8)) : IProp GF := iprop%
  ⌜bs.length = BSIZE⌝ ∗
  wordPointsTo (aBufValid (bnode k)) 4 (DFrac.own 1) v ∗
  wordPointsTo (aBufDev (bnode k)) 4 (DFrac.own qd) dev ∗
  wordPointsTo (aBufBlockno (bnode k)) 4 (DFrac.own qb) bno ∗
  wordPointsTo (aBufDisk (bnode k)) 4 (DFrac.own 1) 0#32 ∗
  byteBuf (aBufData (bnode k)) (DFrac.own 1) bs ∗
  diskBlock γd bno.toNat bsd

theorem bufTravel_travelV (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno v : BitVec 32)
    (bs bsd : List (BitVec 8)) :
    bufTravel (GF := GF) γd k qd qb dev bno v bs bsd ⊢ bufTravelV γd k qd qb dev bno v bs := by
  unfold bufTravel bufTravelV bufPayV
  iintro ⟨%hlen, Hv, Hd, Hb, Hdk, Hdata, Hpay⟩
  isplit
  · ipureintro; exact hlen
  iframe Hv Hd Hb Hdk Hdata
  iright
  iexists bsd
  iexact Hpay

/-- The content, folded into the box's `IN` arm at the holder's context. -/
theorem bufTravelV_inArm (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno v : BitVec 32)
    (bs : List (BitVec 8)) :
    bufTravelV (GF := GF) γd k qd qb dev bno v bs ⊢
      inArm (bufBoxPay γd k qd qb) (dev, bno) curCtx := by
  unfold bufTravelV inArm bufBoxPay bufHdr bufRest byteBuf
  simp only [wordAtN_cur]
  iintro ⟨%hlen, Hv, Hd, Hb, Hdk, Hdata, Hpay⟩
  iexists bs
  isplitl [Hv Hd Hb Hpay]
  · iexists v
    iframe Hv Hd Hb
    iexact Hpay
  · isplit
    · ipureintro; exact hlen
    iframe Hdk
    iexact Hdata

/-- ...and unfolded back out of it. -/
theorem inArm_bufTravelV (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno : BitVec 32) :
    inArm (bufBoxPay (GF := GF) γd k qd qb) (dev, bno) curCtx ⊢
      ∃ (v : BitVec 32) (bs : List (BitVec 8)), bufTravelV γd k qd qb dev bno v bs := by
  unfold bufTravelV inArm bufBoxPay bufHdr bufRest byteBuf
  simp only [wordAtN_cur]
  iintro ⟨%x, ⟨%v, Hv, Hd, Hb, Hpay⟩, ⟨%hlen, Hdk, Hdata⟩⟩
  iexists v, x
  isplit
  · ipureintro; exact hlen
  iframe Hv Hd Hb Hdk Hdata
  iexact Hpay

/-! ## The bridge to `Xv6.bufHold0`

`Xv6.bufHold0` is the handle `bwrite`/`brelse` speak of.  At the fractions
`Xv6/BcacheInv.lean` currently uses -- `dev` at a half (the other half in
`Xv6.bkeyAt`), `blockno` at a half inside `Xv6.bufOwn` -- it is the
sleeplock row, the chain's two tokens, and `bufTravel` beside them. -/

theorem bufHold0_travel (γ : BcacheNames) (γd : DiskNames) (k : Nat)
    (pidv dev bno : BitVec 32) (bs bsd : List (BitVec 8)) :
    bufHold0 (GF := GF) γ γd k pidv dev bno bs bsd ⊢
      ⌜k < NBUF⌝ ∗ sleeplockedQ (γ.slk k).2 1 (aBufLock (bnode k)) pidv ∗ bufTok γ k ∗
        brefTok γ k ∗ (∃ id : Nat, l2Hold (γ.box k) ((dev, bno) : BufId) id) ∗
        bufTravel γd k (1 : Qp).half (1 : Qp).half dev bno 1#32 bs bsd := by
  unfold bufHold0 bufTravel bufOwn
  iintro ⟨%hk, Hsl, Htok, Hrt, Hhold, Hv, Hd, ⟨%hlen, Hb, Hdk, Hdata⟩, Hpay⟩
  isplit
  · ipureintro; exact hk
  iframe Hsl Htok Hrt Hhold
  isplit
  · ipureintro; exact hlen
  iframe Hv Hd Hb Hdk Hdata
  iexact Hpay

theorem bufHold0_of_travel (γ : BcacheNames) (γd : DiskNames) (k : Nat)
    (pidv dev bno : BitVec 32) (bs bsd : List (BitVec 8)) (hk : k < NBUF) :
    sleeplockedQ (GF := GF) (γ.slk k).2 1 (aBufLock (bnode k)) pidv ∗ bufTok γ k ∗
      brefTok γ k ∗ (∃ id : Nat, l2Hold (γ.box k) ((dev, bno) : BufId) id) ∗
      bufTravel γd k (1 : Qp).half (1 : Qp).half dev bno 1#32 bs bsd ⊢
      bufHold0 γ γd k pidv dev bno bs bsd := by
  unfold bufHold0 bufTravel bufOwn
  iintro ⟨Hsl, Htok, Hrt, Hhold, %hlen, Hv, Hd, Hb, Hdk, Hdata, Hpay⟩
  isplit
  · ipureintro; exact hk
  iframe Hsl Htok Hrt Hhold Hv Hd
  isplitl [Hb Hdk Hdata]
  · isplit
    · ipureintro; exact hlen
    iframe Hb Hdk
    iexact Hdata
  · iexact Hpay

/-! ## The two payload rows, folded and unfolded -/

/-- The L1 row, built from the register half and its receipt. -/
theorem bufSlotRegs_intro (γbk : BoxNames) (r : SlotReg BufId BufX) (tl : Nat) (dev bno : BitVec 32)
    (hw : r.win = false) (hx : r.x = none) (hi : r.ident = ((dev, bno) : BufId)) (htl : r.td ≤ tl) :
    slotdHalf (GF := GF) γbk r ∗ topLb r.td ⊢ bufSlotRegs γbk tl dev bno := by
  unfold bufSlotRegs
  iintro ⟨Hrd, #Htd⟩
  iexists r
  iframe Hrd
  isplit
  · ipureintro; exact ⟨hw, hx, hi⟩
  isplit
  · iexact Htd
  · ipureintro; exact htl

theorem bufSlotRegs_elim (γbk : BoxNames) (tl : Nat) (dev bno : BitVec 32) :
    bufSlotRegs (GF := GF) γbk tl dev bno ⊢
      ∃ r : SlotReg BufId BufX,
        ⌜(r.win = false ∧ r.x = none ∧ r.ident = ((dev, bno) : BufId)) ∧ r.td ≤ tl⌝ ∗
        slotdHalf γbk r ∗ topLb r.td := by
  unfold bufSlotRegs
  iintro ⟨%r, Hrd, %hr, #Htd, %htl⟩
  iexists r
  isplit
  · ipureintro; exact ⟨hr, htl⟩
  iframe Hrd
  iexact Htd

/-- The sleeplock payload, built from the park register's half AND the
floor over its stamp; a releaser that has only the `MachCSL.topLb` builds
`Xv6.bufSlpDep` instead and lets the lock hook finish it. -/
theorem bufSlpBox_intro (γ : BcacheNames) (k T' : Nat) :
    bufTok (GF := GF) γ k ∗ slotpHalf (γ.box k) (⟨T', none⟩ : L2Reg BufId) ∗ ctxFloor curCtx T' ⊢
      bufSlpBox γ k curCtx := by
  unfold bufSlpBox
  iintro ⟨Htok, Hrp, #Htp⟩
  iframe Htok
  iexists (⟨T', none⟩ : L2Reg BufId)
  iframe Hrp
  isplit
  · ipureintro; rfl
  · iexact Htp

theorem bufSlpDep_intro (γ : BcacheNames) (k T' : Nat) (ξ : CtxId) :
    bufTok (GF := GF) γ k ∗ slotpHalf (γ.box k) (⟨T', none⟩ : L2Reg BufId) ⊢
      bufSlpDep γ k T' ξ := by
  unfold bufSlpDep; iintro H; iexact H

theorem bufSlpBox_elim (γ : BcacheNames) (k : Nat) (ξ : CtxId) :
    bufSlpBox (GF := GF) γ k ξ ⊢
      bufTok γ k ∗ ∃ s : L2Reg BufId, slotpHalf (γ.box k) s ∗ ⌜s.hold = none⌝ ∗ ctxFloor ξ s.tp := by
  unfold bufSlpBox; iintro H; iexact H

/-! ## The header, as the `bcache.lock` side holds it -/

/-- The header at the holder's own context, spelled in `wordPointsTo` (what
`bget`'s miss path receives from `bufEscrow_withdraw` and hands back to
`bufEscrow_recycle`). -/
def bufHeaderAt (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno : BitVec 32) : IProp GF := iprop%
  ∃ v : BitVec 32,
    wordPointsTo (aBufValid (bnode k)) 4 (DFrac.own 1) v ∗
    wordPointsTo (aBufDev (bnode k)) 4 (DFrac.own qd) dev ∗
    wordPointsTo (aBufBlockno (bnode k)) 4 (DFrac.own qb) bno ∗
    bufPayV γd ((dev, bno) : BufId) v

theorem bufHeaderAt_hdr (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno : BitVec 32)
    (x : BufX) :
    bufHeaderAt (GF := GF) γd k qd qb dev bno ⊣⊢ bufHdr γd k qd qb (dev, bno) x curCtx := by
  unfold bufHeaderAt bufHdr
  simp only [wordAtN_cur]
  constructor
  · iintro H; iexact H
  · iintro H; iexact H

/-! ## The six operations, at the buffer cache -/

/-- **THE DEPOSIT** (Rocq's `bbox_park`): `brelse`'s first instruction hands
the travelling content back to the escrow, at the identity its reference
names, and takes the reference back MINTED AT THE NEW STAMP. -/
theorem bufEscrow_deposit (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp)
    (cpu : CPU) (dev bno v : BitVec 32) (bs : List (BitVec 8)) (id : Nat)
    (E : CoPset) (hE : ↑bioxN ⊆ E) :
    bufBox γd γbk k qd qb ∗ ownCtx cpu curCtx ∗ bufTravelV γd k qd qb dev bno v bs ∗
      l2Hold (GF := GF) γbk (dev, bno) id ⊢
      |={E}=> (ownCtx cpu curCtx ∗ ∃ T' : Nat,
        slotpHalf (GF := GF) γbk (⟨T', none⟩ : L2Reg BufId) ∗ boxRef (GF := GF) γbk (dev, bno) T' ∗ topLb T') := by
  iintro ⟨#Hbox, Hrun, Htrav, Hhold⟩
  unfold bufBox
  imod boxPark (bufBoxPay γd k qd qb) (ndot bioxN k) γbk cpu curCtx (dev, bno) id E
      (nclose_subseteq' k hE) $$ [Hbox Hrun Htrav Hhold] with ⟨Hrun, -, H⟩
  · iframe Hbox Hrun Hhold
    iapply bufTravelV_inArm γd k qd qb dev bno v bs
    iexact Htrav
  imodintro
  iframe Hrun
  iexact H

/-- **THE TAKE** (Rocq's `bbox_checkout`): what `bread` runs after
`acquiresleep` -- the whole bundle comes out of the escrow into the caller's
context, against the reference `bget` minted, and the reference's element
goes into the box for the park to take back. -/
theorem bufEscrow_take (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp)
    (cpu : CPU) (dev bno : BitVec 32) (T0 : Nat) (s0 : L2Reg BufId) (Kt Kp : Nat)
    (E : CoPset) (hE : ↑bioxN ⊆ E) (hs : s0.hold = none) (hKt : T0 ≤ Kt) (hKp : s0.tp ≤ Kp) :
    bufBox γd γbk k qd qb ∗ ownCtx cpu curCtx ∗ ctxFloor curCtx Kt ∗ ctxFloor curCtx Kp ∗
      boxRef (GF := GF) γbk (dev, bno) T0 ∗ slotpHalf (GF := GF) γbk s0 ⊢
      |={E}=> (ownCtx cpu curCtx ∗
        (∃ (v : BitVec 32) (bs : List (BitVec 8)), bufTravelV (GF := GF) γd k qd qb dev bno v bs) ∗
        ∃ id : Nat, l2Hold (GF := GF) γbk (dev, bno) id) := by
  iintro ⟨#Hbox, Hrun, #Hflt, #Hflp, Href, Hrp⟩
  unfold bufBox
  imod boxCheckout (bufBoxPay γd k qd qb) (ndot bioxN k) γbk cpu curCtx (dev, bno) T0 s0
      Kt Kp E (nclose_subseteq' k hE) hs hKt hKp $$ [Hbox Hrun Hflt Hflp Href Hrp]
    with ⟨Hrun, Hin, Hhold⟩
  · iframe Hbox Hrun Href Hrp
    isplit
    · iexact Hflt
    isplit
    · iexact Hflp
    · simp only [bufBoxPay]
      itrivial
  imodintro
  iframe Hrun Hhold
  iapply inArm_bufTravelV γd k qd qb dev bno
  iexact Hin

/-- **THE WINDOW OPENS** (Rocq's `bbox_withdraw_L1`): at `refcnt == 0`, under
`bcache.lock`, the recycler takes the header out of the escrow -- the rest of
the bundle stays parked -- so that it may rewrite `dev`/`blockno`/`valid`. -/
theorem bufEscrow_withdraw (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp)
    (cpu : CPU) (r : SlotReg BufId BufX) (Kd : Nat) (E : CoPset) (hE : ↑bioxN ⊆ E)
    (hw : r.win = false) (hKd : r.td ≤ Kd) :
    bufBox γd γbk k qd qb ∗ ownCtx cpu curCtx ∗ ctxFloor curCtx Kd ∗
      slotdHalf (GF := GF) γbk r ∗ cntHalf (GF := GF) γbk 0 ⊢
      |={E}=> (ownCtx cpu curCtx ∗ cntHalf (GF := GF) γbk 0 ∗
        ∃ (x0 : BufX) (T0 : Nat), ⌜T0 ≤ Kd⌝ ∗
          slotdHalf (GF := GF) γbk (⟨r.td, true, r.ident, some (x0, T0)⟩ : SlotReg BufId BufX) ∗
          bufHeaderAt γd k qd qb r.ident.1 r.ident.2) := by
  iintro ⟨#Hbox, Hrun, #Hfld, Hrd, Hc⟩
  unfold bufBox
  imod boxWithdrawL1 (bufBoxPay γd k qd qb) (ndot bioxN k) γbk cpu curCtx r Kd E
      (nclose_subseteq' k hE) hw hKd $$ [Hbox Hrun Hfld Hrd Hc]
    with ⟨Hrun, Hc, ⟨%x0, %T0, %hT0, Hrd, Hhdr⟩⟩
  · iframe Hbox Hrun Hrd Hc
    isplit
    · iexact Hfld
    · simp only [bufBoxPay]
      itrivial
  simp only [bufBoxPay]
  imodintro
  iframe Hrun Hc
  iexists x0, T0
  isplit
  · ipureintro; exact hT0
  iframe Hrd
  iapply (bufHeaderAt_hdr γd k qd qb r.ident.1 r.ident.2 x0).2
  iexact Hhdr

/-- **THE WINDOW CLOSES** (Rocq's `bbox_deposit_L1`): the header goes back at
the NEW identity, and the chain's first reference is minted at the new
stamp -- which is the reference `bget`'s caller will check out with. -/
theorem bufEscrow_recycle (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp)
    (cpu : CPU) (r : SlotReg BufId BufX) (dev' bno' : BitVec 32) (x0 : BufX) (T0 : Nat)
    (E : CoPset) (hE : ↑bioxN ⊆ E) (hw : r.win = true) (hx : r.x = some (x0, T0)) :
    bufBox γd γbk k qd qb ∗ ownCtx cpu curCtx ∗ slotdHalf (GF := GF) γbk r ∗ cntHalf (GF := GF) γbk 0 ∗
      bufHeaderAt γd k qd qb dev' bno' ⊢
      |={E}=> (ownCtx cpu curCtx ∗ ∃ T' : Nat,
        slotdHalf (GF := GF) γbk (⟨T', false, (dev', bno'), none⟩ : SlotReg BufId BufX) ∗
        cntHalf (GF := GF) γbk 1 ∗ boxRef (GF := GF) γbk (dev', bno') T' ∗ topLb T') := by
  iintro ⟨#Hbox, Hrun, Hrd, Hc, Hhdr⟩
  unfold bufBox
  imod boxDepositL1 (bufBoxPay γd k qd qb) (ndot bioxN k) γbk cpu curCtx r (dev', bno') x0 T0 E
      (nclose_subseteq' k hE) hw hx $$ [Hbox Hrun Hrd Hc Hhdr] with ⟨Hrun, -, H⟩
  · iframe Hbox Hrun Hrd Hc
    simp only [bufBoxPay]
    iapply (bufHeaderAt_hdr γd k qd qb dev' bno' x0).1
    iexact Hhdr
  imodintro
  iframe Hrun
  iexact H

/-- **`refcnt++`** (Rocq's `bbox_ref_incr`): a reference at the identity the
L1 register records, minted at the escrow's current stamp. -/
theorem bufEscrow_refIncr (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp)
    (r : SlotReg BufId BufX) (c : Nat) (E : CoPset) (hE : ↑bioxN ⊆ E) (hw : r.win = false) :
    bufBox γd γbk k qd qb ∗ slotdHalf (GF := GF) γbk r ∗ cntHalf (GF := GF) γbk c ⊢
      |={E}=> (slotdHalf (GF := GF) γbk r ∗ cntHalf (GF := GF) γbk (c + 1) ∗ ∃ T : Nat, boxRef (GF := GF) γbk r.ident T) := by
  iintro ⟨#Hbox, Hrd, Hc⟩
  unfold bufBox
  iapply boxRefIncr (bufBoxPay γd k qd qb) (ndot bioxN k) γbk r c E
    (nclose_subseteq' k hE) hw $$ [$Hbox $Hrd $Hc]

/-- **`refcnt--`** (Rocq's `bbox_ref_decr`): the reference is burned and the
L1 floor register joins its stamp, so that the next withdrawal's cover
(row D) still holds. -/
theorem bufEscrow_refDecr (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp)
    (r : SlotReg BufId BufX) (c : Nat) (i : BufId) (T0 : Nat) (E : CoPset)
    (hE : ↑bioxN ⊆ E) (hw : r.win = false) :
    bufBox γd γbk k qd qb ∗ slotdHalf (GF := GF) γbk r ∗ topLb r.td ∗ cntHalf (GF := GF) γbk (c + 1) ∗
      boxRef (GF := GF) γbk i T0 ⊢
      |={E}=> (slotdHalf (GF := GF) γbk (⟨max r.td T0, false, r.ident, r.x⟩ : SlotReg BufId BufX) ∗
        cntHalf (GF := GF) γbk c ∗ topLb (max r.td T0)) := by
  iintro ⟨#Hbox, Hrd, #Htd, Hc, Href⟩
  unfold bufBox
  iapply boxRefDecr (bufBoxPay γd k qd qb) (ndot bioxN k) γbk r c i T0 E
    (nclose_subseteq' k hE) hw $$ [$Hbox $Hrd $Htd $Hc $Href]

/-! ## Allocation, from the `.bss` cells -/

/-- **THE ESCROW OF ONE BUFFER, BORN** out of the raw cells `binit` owns:
the content moves into a fresh twin context, which is stamped, and the
invariant is allocated over it.  The caller keeps both payload rows -- the
L1 register half (with its receipt) and the L2 register half -- to seat in
`bcache.lock`'s resource and in the buffer's sleeplock.

At `binit` the caller passes `v = 0` and the LEFT arm of `Xv6.bufPayV`: an
invalid buffer owes no disk fragment, which is what lets thirty buffers all
naming block `0` coexist. -/
theorem bufEscrow_alloc (γd : DiskNames) (k : Nat) (qd qb : Qp) (cpu : CPU)
    (dev bno v : BitVec 32) (bs : List (BitVec 8)) (E : CoPset) :
    ownCtx cpu curCtx ∗ bufTravelV γd k qd qb dev bno v bs ⊢
      |={E}=> (ownCtx cpu curCtx ∗ ∃ (γbk : BoxNames) (Tb : Nat),
        bufBox γd γbk k qd qb ∗
        slotdHalf (GF := GF) γbk (⟨Tb, false, (dev, bno), none⟩ : SlotReg BufId BufX) ∗ topLb Tb ∗
        cntHalf (GF := GF) γbk 0 ∗ slotpHalf (GF := GF) γbk (⟨0, none⟩ : L2Reg BufId)) := by
  iintro ⟨Hrun, Htrav⟩
  imod boxAlloc (bufBoxPay γd k qd qb) (ndot bioxN k) cpu curCtx (dev, bno) E
      $$ [Hrun Htrav] with ⟨Hrun, H⟩
  · iframe Hrun
    iapply bufTravelV_inArm γd k qd qb dev bno v bs
    iexact Htrav
  imodintro
  iframe Hrun
  unfold bufBox
  iexact H

/-- One buffer's escrow as `binit` must hand it on: the box itself, the L1
row for `bcache.lock`'s `Xv6.bkeyAt`, the count half for its `Xv6.bslotAt`
(at zero -- `b->refcnt` is zero at boot), and the L2 register half for the
buffer's sleeplock payload `Xv6.bufSlpBox`. -/
def bufBoxRow (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp)
    (dev bno : BitVec 32) : IProp GF := iprop%
  bufBox γd γbk k qd qb ∗
  (∃ r : SlotReg BufId BufX,
    slotdHalf γbk r ∗ ⌜r.win = false ∧ r.x = none ∧ r.ident = ((dev, bno) : BufId)⌝ ∗ topLb r.td) ∗
  cntHalf γbk 0 ∗ slotpHalf γbk (⟨0, none⟩ : L2Reg BufId)

theorem bufEscrow_allocRow (γd : DiskNames) (k : Nat) (qd qb : Qp) (cpu : CPU)
    (dev bno v : BitVec 32) (bs : List (BitVec 8)) (E : CoPset) :
    ownCtx cpu curCtx ∗ bufTravelV (GF := GF) γd k qd qb dev bno v bs ⊢
      |={E}=> (ownCtx cpu curCtx ∗ ∃ γbk : BoxNames, bufBoxRow γd γbk k qd qb dev bno) := by
  iintro ⟨Hrun, Htrav⟩
  imod bufEscrow_alloc γd k qd qb cpu dev bno v bs E $$ [Hrun Htrav]
    with ⟨Hrun, ⟨%γbk, %Tb, #Hbox, Hrd, #Htb, Hc, Hrp⟩⟩
  · iframe Hrun Htrav
  imodintro
  iframe Hrun
  iexists γbk
  unfold bufBoxRow
  isplit
  · iexact Hbox
  iframe Hc Hrp
  iexists (⟨Tb, false, (dev, bno), none⟩ : SlotReg BufId BufX)
  iframe Hrd
  isplit
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  · iexact Htb

/-- A big-sep over `List.range n` only sees indices below `n`. -/
theorem bigSepL_range_congr (Φ Ψ : Nat → IProp GF) :
    ∀ n : Nat, (∀ k, k < n → Φ k = Ψ k) →
      (([∗list] k ∈ List.range n, Φ k) ⊢ [∗list] k ∈ List.range n, Ψ k) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp only [List.range_zero]
      iintro -
      iapply BigSepL.bigSepL_nil.2
      itrivial
  | succ n ih =>
      intro h
      rw [List.range_succ]
      iintro H
      icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
      iapply BigSepL.bigSepL_append.2
      isplitl [H1]
      · iapply ih (fun k hk => h k (by omega)) $$ H1
      · have he : Φ n = Ψ n := h n (by omega)
        iapply BigSepL.bigSepL_singleton.2
        rw [← he]
        iapply BigSepL.bigSepL_singleton.1 $$ H2

/-- **THE THIRTY ESCROWS, BORN TOGETHER** (the fold Rocq's `bio_init` runs
over `seq 0 NBUF`): every buffer's raw travelling content goes into its own
box, and the caller comes away with a `box : Nat → BoxNames` for
`Xv6.BcacheNames` and every buffer's three rows.

At `binit` the natural instance is `v k = 0` with `Xv6.bufPayV`'s LEFT arm:
nothing owes a disk fragment, which is what lets thirty buffers all naming
block `0` coexist.

**WHAT `binit`'s POST LACKS** (reported).  `Xv6.wp_binit_body`'s `bufOut i`
hands back only the three things `binit` writes: the initialised sleeplock
(`sleepLockInited`), `b->prev` and `b->next`.  The rest of `struct buf` is
`.bss` that `binit` never touches and its spec never mentions, so a full
`bioInit` must take, per buffer, as EXTRA inputs beside `binit`'s post:
`b->valid` (`+0`), `b->disk` (`+4`), `b->dev` (`+8`), `b->blockno` (`+12`),
`b->refcnt` (`+64`) and the 1024 data bytes (`+88`) -- all zero out of
`.bss`.  `Xv6.bufTravelV` at `v = 0` is exactly the first six of those minus
`refcnt`, which stays behind in `Xv6.bslotAt`.  Beyond this fold, a full
`bioInit` still owes: the thirty sleeplocks re-sealed over `Xv6.bufSlpBox`
(Rocq's "gnames before the record" dance -- the checkout tokens first, then
the sleeplocks, then the `Xv6.BcacheNames` record), the reference/slot
authorities with `Xv6.bslots γ BSLOTS`, the LRU cycle out of `binit`'s
`prev`/`next` values (`Xv6.bcacheLru_splice`), and `Xv6.isBcache` over the
assembled `Xv6.bcacheResAt`. -/
theorem bufEscrow_allocAll (γd : DiskNames) (qd qb : Qp) (cpu : CPU)
    (dev bno v : Nat → BitVec 32) (bs : Nat → List (BitVec 8)) (E : CoPset) :
    ∀ n : Nat,
      ownCtx cpu curCtx ∗
        ([∗list] k ∈ List.range n, bufTravelV (GF := GF) γd k qd qb (dev k) (bno k) (v k) (bs k)) ⊢
      |={E}=> (ownCtx cpu curCtx ∗ ∃ bx : Nat → BoxNames,
        [∗list] k ∈ List.range n, bufBoxRow γd (bx k) k qd qb (dev k) (bno k)) := by
  intro n
  induction n with
  | zero =>
      iintro ⟨Hrun, -⟩
      imodintro
      iframe Hrun
      iexists (fun _ => (⟨0, 0, 0, 0⟩ : BoxNames))
      simp only [List.range_zero]
      iapply BigSepL.bigSepL_nil.2
      itrivial
  | succ n ih =>
      rw [List.range_succ]
      iintro ⟨Hrun, H⟩
      icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
      imod ih $$ [Hrun H1] with ⟨Hrun, ⟨%bx0, Hrows⟩⟩
      · iframe Hrun H1
      ihave H2 := BigSepL.bigSepL_singleton.1 $$ H2
      imod bufEscrow_allocRow γd n qd qb cpu (dev n) (bno n) (v n) (bs n) E $$ [Hrun H2]
        with ⟨Hrun, ⟨%γbn, Hrow⟩⟩
      · iframe Hrun H2
      imodintro
      iframe Hrun
      iexists (fun j => if j = n then γbn else bx0 j)
      iapply BigSepL.bigSepL_append.2
      isplitl [Hrows]
      · iapply bigSepL_range_congr
          (fun k => bufBoxRow γd (bx0 k) k qd qb (dev k) (bno k))
          (fun k => bufBoxRow γd (if k = n then γbn else bx0 k) k qd qb (dev k) (bno k))
          n (fun k hk => by rw [if_neg (by omega)]) $$ Hrows
      · iapply BigSepL.bigSepL_singleton.2
        simp only [reduceIte]
        iexact Hrow

end

end Xv6
