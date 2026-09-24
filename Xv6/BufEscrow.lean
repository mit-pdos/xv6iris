/-
**THE PER-BUFFER ESCROW** (`kernel/bio.c`): the transit box that carries a
buffer's travelling content -- `valid`, `dev`, the `bufOwn` bundle
(`blockno`, the pinned `disk` flag, the 1024 data bytes) and the block's
disk-image fragment -- from the holder that releases it to the holder that
next acquires it.

A port of the escrow part of Rocq `BioInv.v` (its `BioBox` section), over
this port's `MachCSL.CtxBox`.

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
* Rocq's `buf_hdr` is indexed by the boolean `valid` and the payload depends
  on it; here `valid` is existential inside the header (the taker reads the
  cell, as the C code does) and the payload does not depend on it.
-/
import Xv6.BcacheInv
import MachCSL.CtxBox

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedSectionVars false

/-- The escrow's identity: the pair `(dev, blockno)` the buffer currently
names (Rocq's `bio_id`). -/
abbrev BufId : Type := BitVec 32 × BitVec 32

/-- The escrow's shared witness: the buffer's data bytes (Rocq's `bio_x`). -/
abbrev BufX : Type := List (BitVec 8)

/-- The escrow invariants' namespace (Rocq's `bioxN`). -/
def bioxN : Namespace := ndot nroot "xv6biox"

/-- The ghost libraries the escrow needs, beside `Xv6.BcacheG`. -/
class BufBoxG (GF : BundledGFunctors) where
  [gmStm : GhostMapG GF Nat (BufId × Nat) RegMapF]
  [gvCnt : GhostVarG GF Nat]
  [gvSlotd : GhostVarG GF (SlotReg BufId BufX)]
  [gvSlotp : GhostVarG GF (L2Reg BufId)]

attribute [reducible, instance] BufBoxG.gmStm BufBoxG.gvCnt BufBoxG.gvSlotd BufBoxG.gvSlotp

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]

instance wordAtN_timeless (ξ : CtxId) (a : BitVec 64) (n : Nat) (dq : DFrac)
    (w : BitVec (8 * n)) : Timeless (wordAtN (GF := GF) ξ a n dq w) := by
  unfold wordAtN; infer_instance

end

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
variable [BcacheG GF] [SleepLockG GF] [DiskG GF] [BufBoxG GF] [CurCtx]

instance diskBlock_timeless (γd : DiskNames) (b : Nat) (bs : List (BitVec 8)) :
    Timeless (diskBlock (GF := GF) γd b bs) := by unfold diskBlock; infer_instance

/-! ## The bundle, split header / rest -/

/-- The travelling payload at an identity (Rocq's `buf_pay`, with the pool
and the log layer's clean/dirty distinction dropped): the block's disk-image
fragment.  Ghost, so context-free. -/
def bufPay (γd : DiskNames) (i : BufId) : CtxId → IProp GF := fun _ => iprop%
  ∃ bsd : List (BitVec 8), diskBlock γd i.2.toNat bsd

/-- **THE HEADER** (Rocq's `buf_hdr`): the cells the `bcache.lock` side reads
and rewrites -- `valid` in full, and the two key cells at the caller's
fractions -- beside the payload at the identity they name. -/
def bufHdr (γd : DiskNames) (k : Nat) (qd qb : Qp) (i : BufId) (_x : BufX)
    (ξ : CtxId) : IProp GF := iprop%
  (∃ v : BitVec 32, wordAtN ξ (aBufValid (bnode k)) 4 (DFrac.own 1) v) ∗
  wordAtN ξ (aBufDev (bnode k)) 4 (DFrac.own qd) i.1 ∗
  wordAtN ξ (aBufBlockno (bnode k)) 4 (DFrac.own qb) i.2 ∗
  bufPay γd i ξ

/-- **THE REST** (Rocq's `buf_rest`): the pinned `disk` flag and the data. -/
def bufRest (k : Nat) (x : BufX) (ξ : CtxId) : IProp GF := iprop%
  ⌜x.length = BSIZE⌝ ∗
  wordAtN ξ (aBufDisk (bnode k)) 4 (DFrac.own 1) 0#32 ∗
  ([∗list] j ↦ b ∈ x, wordAtN ξ (aBufData (bnode k) + BitVec.ofNat 64 j) 1 (DFrac.own 1) b)

/-- The box's payload family at buffer `k` (Rocq instantiates `CtxBox` with
`Q1 := λ _, emp` and `Q2 := emp`: the bcache keeps no ghost residue while
the bundle is out). -/
def bufBoxPay (γd : DiskNames) (k : Nat) (qd qb : Qp) : BoxPay GF BufId BufX where
  hdr := bufHdr γd k qd qb
  rest := bufRest k
  q1 := fun _ => iprop(emp)
  q2 := iprop(emp)

instance bufHdr_morph (γd : DiskNames) (k : Nat) (qd qb : Qp) (i : BufId) (x : BufX) :
    CtxMorph (GF := GF) (bufHdr γd k qd qb i x) := by
  unfold bufHdr bufPay; infer_instance

instance bufRest_morph (k : Nat) (x : BufX) : CtxMorph (GF := GF) (bufRest k x) := by
  unfold bufRest
  have h := ctxMorph_bigSepL (GF := GF) x
    (fun j b ξ => wordAtN ξ (aBufData (bnode k) + BitVec.ofNat 64 j) 1 (DFrac.own 1) b)
    (fun j b => instCtxMorphWordAtN _ _ _ _)
  infer_instance

instance bufHdr_timeless (γd : DiskNames) (k : Nat) (qd qb : Qp) (i : BufId) (x : BufX)
    (ξ : CtxId) : Timeless (bufHdr (GF := GF) γd k qd qb i x ξ) := by
  unfold bufHdr bufPay; infer_instance

instance bufRest_timeless (k : Nat) (x : BufX) (ξ : CtxId) :
    Timeless (bufRest (GF := GF) k x ξ) := by unfold bufRest; infer_instance

instance bufBoxPay_ok (γd : DiskNames) (k : Nat) (qd qb : Qp) :
    BoxPayOk (bufBoxPay (GF := GF) γd k qd qb) where
  hdrMorph i x := bufHdr_morph γd k qd qb i x
  restMorph x := bufRest_morph k x
  hdrTimeless i x ξ := bufHdr_timeless γd k qd qb i x ξ
  restTimeless x ξ := bufRest_timeless k x ξ
  q1Timeless _ := by unfold bufBoxPay; infer_instance
  q2Timeless := by unfold bufBoxPay; infer_instance

/-! ## The escrow itself -/

/-- **BUFFER `k`'s ESCROW** (Rocq's `buf_box`), persistent. -/
def bufBox (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp) : IProp GF :=
  isBox (bufBoxPay γd k qd qb) (ndot bioxN k) γbk

instance bufBox_persistent (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp) :
    Persistent (bufBox (GF := GF) γd γbk k qd qb) := by unfold bufBox; infer_instance

/-! ## The travelling content, as the bio proofs hold it -/

/-- **WHAT TRAVELS** (Rocq's `bio_hold0` minus the sleeplock row): the
`valid` cell (in full, at whatever it says), the two key cells at the
caller's fractions, the pinned `disk` flag, the 1024 data bytes, and the
block's disk-image fragment.  This is exactly what `brelse` deposits and
what `bread` takes. -/
def bufTravel (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno v : BitVec 32)
    (bs bsd : List (BitVec 8)) : IProp GF := iprop%
  ⌜bs.length = BSIZE⌝ ∗
  wordPointsTo (aBufValid (bnode k)) 4 (DFrac.own 1) v ∗
  wordPointsTo (aBufDev (bnode k)) 4 (DFrac.own qd) dev ∗
  wordPointsTo (aBufBlockno (bnode k)) 4 (DFrac.own qb) bno ∗
  wordPointsTo (aBufDisk (bnode k)) 4 (DFrac.own 1) 0#32 ∗
  byteBuf (aBufData (bnode k)) (DFrac.own 1) bs ∗
  diskBlock γd bno.toNat bsd

/-- The content, folded into the box's `IN` arm at the holder's context. -/
theorem bufTravel_inArm (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno v : BitVec 32)
    (bs bsd : List (BitVec 8)) :
    bufTravel (GF := GF) γd k qd qb dev bno v bs bsd ⊢
      inArm (bufBoxPay γd k qd qb) (dev, bno) curCtx := by
  unfold bufTravel inArm bufBoxPay bufHdr bufRest bufPay byteBuf
  simp only [wordAtN_cur]
  iintro ⟨%hlen, Hv, Hd, Hb, Hdk, Hdata, Hpay⟩
  iexists bs
  isplitl [Hv Hd Hb Hpay]
  · isplitl [Hv]
    · iexists v; iexact Hv
    iframe Hd Hb
    iexists bsd
    iexact Hpay
  · isplit
    · ipureintro; exact hlen
    iframe Hdk
    iexact Hdata

/-- ...and unfolded back out of it. -/
theorem inArm_bufTravel (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno : BitVec 32) :
    inArm (bufBoxPay (GF := GF) γd k qd qb) (dev, bno) curCtx ⊢
      ∃ (v : BitVec 32) (bs bsd : List (BitVec 8)), bufTravel γd k qd qb dev bno v bs bsd := by
  unfold bufTravel inArm bufBoxPay bufHdr bufRest bufPay byteBuf
  simp only [wordAtN_cur]
  iintro ⟨%x, ⟨⟨%v, Hv⟩, Hd, Hb, ⟨%bsd, Hpay⟩⟩, ⟨%hlen, Hdk, Hdata⟩⟩
  iexists v, x, bsd
  isplit
  · ipureintro; exact hlen
  iframe Hv Hd Hb Hdk Hdata
  iexact Hpay

/-! ## The bridge to `Xv6.bufHold0`

`Xv6.bufHold0` is the handle `bwrite`/`brelse` speak of.  At the fractions
`Xv6/BcacheInv.lean` currently uses -- `dev` at a half (the other half in
`Xv6.bkeyAt`), `blockno` at a half inside `Xv6.bufOwn` -- it is exactly the
sleeplock row beside `bufTravel`.  If those fractions move, only these two
lemmas move with them. -/

theorem bufHold0_travel (γ : BcacheNames) (γd : DiskNames) (k : Nat)
    (pidv dev bno : BitVec 32) (bs bsd : List (BitVec 8)) :
    bufHold0 (GF := GF) γ γd k pidv dev bno bs bsd ⊢
      ⌜k < NBUF⌝ ∗ sleeplockedQ (γ.slk k).2 1 (aBufLock (bnode k)) pidv ∗ bufTok γ k ∗
        bufTravel γd k (1 : Qp).half (1 : Qp).half dev bno 1#32 bs bsd := by
  unfold bufHold0 bufTravel bufOwn
  iintro ⟨%hk, Hsl, Htok, Hv, Hd, ⟨%hlen, Hb, Hdk, Hdata⟩, Hpay⟩
  isplit
  · ipureintro; exact hk
  iframe Hsl Htok
  isplit
  · ipureintro; exact hlen
  iframe Hv Hd Hb Hdk Hdata
  iexact Hpay

theorem bufHold0_of_travel (γ : BcacheNames) (γd : DiskNames) (k : Nat)
    (pidv dev bno : BitVec 32) (bs bsd : List (BitVec 8)) (hk : k < NBUF) :
    sleeplockedQ (GF := GF) (γ.slk k).2 1 (aBufLock (bnode k)) pidv ∗ bufTok γ k ∗
      bufTravel γd k (1 : Qp).half (1 : Qp).half dev bno 1#32 bs bsd ⊢
      bufHold0 γ γd k pidv dev bno bs bsd := by
  unfold bufHold0 bufTravel bufOwn
  iintro ⟨Hsl, Htok, %hlen, Hv, Hd, Hb, Hdk, Hdata, Hpay⟩
  isplit
  · ipureintro; exact hk
  iframe Hsl Htok Hv Hd
  isplitl [Hb Hdk Hdata]
  · isplit
    · ipureintro; exact hlen
    iframe Hb Hdk
    iexact Hdata
  · iexact Hpay

/-! ## The header, as the `bcache.lock` side holds it -/

/-- The header at the holder's own context, spelled in `wordPointsTo` (what
`bget`'s miss path receives from `bufEscrow_withdraw` and hands back to
`bufEscrow_recycle`). -/
def bufHeaderAt (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno : BitVec 32) : IProp GF := iprop%
  (∃ v : BitVec 32, wordPointsTo (aBufValid (bnode k)) 4 (DFrac.own 1) v) ∗
  wordPointsTo (aBufDev (bnode k)) 4 (DFrac.own qd) dev ∗
  wordPointsTo (aBufBlockno (bnode k)) 4 (DFrac.own qb) bno ∗
  (∃ bsd : List (BitVec 8), diskBlock γd bno.toNat bsd)

theorem bufHeaderAt_hdr (γd : DiskNames) (k : Nat) (qd qb : Qp) (dev bno : BitVec 32)
    (x : BufX) :
    bufHeaderAt (GF := GF) γd k qd qb dev bno ⊣⊢ bufHdr γd k qd qb (dev, bno) x curCtx := by
  unfold bufHeaderAt bufHdr bufPay
  simp only [wordAtN_cur]
  constructor
  · iintro H; iexact H
  · iintro H; iexact H

/-! ## The six operations, at the buffer cache -/

/-- **THE DEPOSIT** (Rocq's `bbox_park`): `brelse`'s first instruction hands
the travelling content back to the escrow, at the identity its reference
names, and takes the reference back MINTED AT THE NEW STAMP.  This is where
`Xv6/SpecBrelse.lean`'s proof currently DROPS the content. -/
theorem bufEscrow_deposit (γd : DiskNames) (γbk : BoxNames) (k : Nat) (qd qb : Qp)
    (cpu : CPU) (dev bno v : BitVec 32) (bs bsd : List (BitVec 8)) (id : Nat)
    (E : CoPset) (hE : ↑bioxN ⊆ E) :
    bufBox γd γbk k qd qb ∗ ownCtx cpu curCtx ∗ bufTravel γd k qd qb dev bno v bs bsd ∗
      l2Hold (GF := GF) γbk (dev, bno) id ⊢
      |={E}=> (ownCtx cpu curCtx ∗ ∃ T' : Nat,
        slotpHalf (GF := GF) γbk (⟨T', none⟩ : L2Reg BufId) ∗ boxRef (GF := GF) γbk (dev, bno) T' ∗ topLb T') := by
  iintro ⟨#Hbox, Hrun, Htrav, Hhold⟩
  unfold bufBox
  imod boxPark (bufBoxPay γd k qd qb) (ndot bioxN k) γbk cpu curCtx (dev, bno) id E
      (nclose_subseteq' k hE) $$ [Hbox Hrun Htrav Hhold] with ⟨Hrun, -, H⟩
  · iframe Hbox Hrun Hhold
    iapply bufTravel_inArm γd k qd qb dev bno v bs bsd
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
        (∃ (v : BitVec 32) (bs bsd : List (BitVec 8)), bufTravel (GF := GF) γd k qd qb dev bno v bs bsd) ∗
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
  iapply inArm_bufTravel γd k qd qb dev bno
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

/-! ## The two payload rows the escrow's registers live in

The registers' other halves do not float: one rides `bcache.lock`'s slot row
(Rocq's `bslot_regs`) and the other rides the buffer's SLEEPLOCK payload
(Rocq's `bslp`), so that the party that holds the lock is the party that may
move the register.  These are the shapes the wiring wave will seat in
`Xv6.bcacheResAt` and `Xv6.bufSlp`. -/

/-- **THE L1 ROW** (Rocq's `bslot_regs`): the drop register's other half,
closed, at the identity the slot's cells name, with its floor receipt under
the resource's floor slot `tl`. -/
def bufSlotRegs (γbk : BoxNames) (tl : Nat) (dev bno : BitVec 32) (ξ : CtxId) : IProp GF := iprop%
  ∃ r : SlotReg BufId BufX,
    l1Row γbk r ξ ∗ ⌜r.ident = (dev, bno) ∧ r.td ≤ tl⌝

/-- **THE L2 ROW** (Rocq's `bslp`): what buffer `k`'s sleeplock protects once
the escrow exists -- the checkout token AND the park register's other half,
at rest. -/
def bufSlpBox (γ : BcacheNames) (γbk : BoxNames) (k : Nat) (ξ : CtxId) : IProp GF := iprop%
  bufTok γ k ∗ ∃ s : L2Reg BufId, l2Row γbk s ξ

instance bufSlotRegs_morph (γbk : BoxNames) (tl : Nat) (dev bno : BitVec 32) :
    CtxMorph (GF := GF) (bufSlotRegs γbk tl dev bno) := by
  unfold bufSlotRegs; infer_instance

instance bufSlpBox_morph (γ : BcacheNames) (γbk : BoxNames) (k : Nat) :
    CtxMorph (GF := GF) (bufSlpBox γ γbk k) := by
  unfold bufSlpBox; infer_instance

/-! ## Allocation, from the `.bss` cells -/

/-- **THE ESCROW OF ONE BUFFER, BORN** out of the raw cells `binit` owns:
the content moves into a fresh twin context, which is stamped, and the
invariant is allocated over it.  The caller keeps both payload rows -- the
L1 register half (with its floor receipt) and the L2 register half -- to
seat in `bcache.lock`'s resource and in the buffer's sleeplock. -/
theorem bufEscrow_alloc (γd : DiskNames) (k : Nat) (qd qb : Qp) (cpu : CPU)
    (dev bno v : BitVec 32) (bs bsd : List (BitVec 8)) (E : CoPset) :
    ownCtx cpu curCtx ∗ bufTravel γd k qd qb dev bno v bs bsd ⊢
      |={E}=> (ownCtx cpu curCtx ∗ ∃ (γbk : BoxNames) (Tb : Nat),
        bufBox γd γbk k qd qb ∗
        slotdHalf (GF := GF) γbk (⟨Tb, false, (dev, bno), none⟩ : SlotReg BufId BufX) ∗ topLb Tb ∗
        cntHalf (GF := GF) γbk 0 ∗ slotpHalf (GF := GF) γbk (⟨0, none⟩ : L2Reg BufId)) := by
  iintro ⟨Hrun, Htrav⟩
  imod boxAlloc (bufBoxPay γd k qd qb) (ndot bioxN k) cpu curCtx (dev, bno) E
      $$ [Hrun Htrav] with ⟨Hrun, H⟩
  · iframe Hrun
    iapply bufTravel_inArm γd k qd qb dev bno v bs bsd
    iexact Htrav
  imodintro
  iframe Hrun
  unfold bufBox
  iexact H

end

end Xv6
