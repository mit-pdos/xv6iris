/-
MachCSL: **THE TRANSIT BOX** -- a port of the Rocq `CtxBox.v` (1775 lines,
"the generic box with stamps/floors/park registers").

A box is a namespace invariant that holds a client bundle `P_hdr i x ξb ∗
P_rest x ξb` parked in its own STAMPED context `ξb`, so that the bundle can
be handed from the party that releases it to the party that next acquires it
ATOMICALLY AT ANY INSTRUCTION -- no lock is the handover point.  Two levels
of client code reach into it:

* **L1** (the buffer cache's `bcache.lock` side): opens a WINDOW over the
  header while it rewrites the identity-bearing cells, then deposits a
  header at a NEW identity.  Its register `slotd` records the window flag,
  the identity, the floor it has reached (`td`) and, while the window is
  open, the witness `x` the parked `P_rest` sits at, with the stamp it sits
  at.
* **L2** (the per-buffer sleeplock side): CHECKS OUT the whole bundle
  against a reference, and PARKS it back.  Its register `slotp` records
  which reference is currently checked out.

The handover is sound at TSO because every party's floor covers the stamp
the bundle was last deposited at: the box's rows (C)/(D) say that the
current stamp `T` is covered either by the L1 floor register `td`, or by a
live reference's own stamp, or by the L2 floor register `tp` -- and each
party holds a `ctxFloor` receipt of whichever of those it owns.
`ctxAbsorbLb` then moves the bundle out of `ξb` into the taker's context,
and `ctxDeposit` moves it back in, RAISING the stamp, so a deposit owes
nothing at the deposit site.

**Deviations from Rocq** (all reported in this file's report):

* the stamped-share camera `auth (gmap (id * nat) ufrac)` -- whose `qsum`
  masses let a Rocq reference be SPLIT into fractional shares -- is replaced
  by a ghost map `refId ↦ (identity, stamp)` in which every reference is ONE
  unit, counted in the row's `Nodup` id list exactly as `Xv6.bslotAt` counts
  `b->refcnt`.  The bcache instantiates Rocq's box with unit singletons
  everywhere (`{[((dev,bno),t) := 1%Qp]}`), so nothing bio needs is lost;
  the log layer's fractional `bpin` reference would need the masses back.
* `box_withdraw_L1` is ported at count ZERO only (`bbox_withdraw_L1`'s
  instance): the general version's premise `qsum mD = nat_Qc c` is "the
  caller holds ALL the mass", which at units means it must present the whole
  id list.  Recycling is the only client.
* correspondingly `box_deposit_L1` sets the count to 1 (Rocq: `max 1 c`).
* the hooked forms (`*_hook`, `box_withdraw_L1_free`, `box_checkout_split`,
  `box_park_join`, `box_deposit_L1_shape`, `box_l1_to_l2`) are not ported:
  they exist for the icache instance, which this port does not have.
-/
import MachCSL.Lock
import Iris.Instances.Lib.Invariants
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.GhostMap

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Std
open LeanRV64D

set_option linter.unusedSectionVars false

section transport
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

local notation "era" => MachGS.era (hlc := hlc) (GF := GF)

/-! ## The two transport laws a box lives on

Rocq `TsoCtxAbsorbLb.ctx_absorb_lb` and `TsoCtx.ctx_deposit`.  Neither was
needed by the lock kit (`lock_pay_take` resumes the lock's context outright,
because the lock's payload leaves its context EMPTY); the box instead takes
a PART of the bundle out and leaves the rest parked, so the parked context
must survive both moves. -/

/-- **THE ABSORB**: a payload moves OUT of a stamped context into a running
one, at a view receipt past the stamp; the stamped token is returned
unchanged. -/
theorem ctxAbsorbLb (R : CtxId → IProp GF) [CtxMorph R] (cpu : CPU) (ξ ξ' : CtxId)
    (T K : Nat) (hTK : T ≤ K) :
    ownCtx (GF := GF) cpu ξ' ∗ viewLb cpu K ∗ ctxStamped ξ T ∗ R ξ ⊢
      |==> (ownCtx cpu ξ' ∗ ctxStamped ξ T ∗ R ξ') := by
  iintro ⟨Hrun, #HK, Hst, HR⟩
  icases ctxStamped_cases ξ T $$ Hst with ⟨%D, Hat, #HT, %hD, #Hels⟩
  imod ctx_absorb cpu ξ' K $$ [$Hrun $HK] with ⟨Hrun, #Hfl'⟩
  icases (ctxAt_halves ξ T D).1 $$ Hat with ⟨Hat1, Hat2⟩
  ihave Hdom : ctxDom ξ ξ' $$ [Hat1]
  · iapply ctxDomAt_intro ξ ξ' _ T D
    iframe Hat1
    isplit
    · iapply ctxFloor_le ξ' K T hTK; iexact Hfl'
    isplit
    · iexact Hels
    · imodintro
      iintro %k %h %hk
      unfold keyAt
      ileft
      iapply ctxFloor_le ξ' K k (by have := hD k h hk; omega)
      iexact Hfl'
  imod CtxMorph.morph (R := R) ξ ξ' $$ [$Hdom $HR] with ⟨Hdom, HR⟩
  icases ctxDomAt_cases ξ ξ' _ $$ Hdom with ⟨%B2, %D2, Hat1, -, -, -⟩
  ihave %heq : ⌜B2 = T ∧ D2 = D⌝ $$ [Hat1 Hat2]
  · iapply ctxAt_agree ξ _ _ B2 T D2 D $$ [Hat1 Hat2]
    iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hat := (ctxAt_halves ξ B2 D2).2 $$ [Hat1 Hat2]
  · iframe
  imodintro
  iframe Hrun HR
  unfold ctxStamped
  iexists D2
  iframe Hat
  isplit
  · iexact HT
  isplit
  · ipureintro; exact hD
  · iexact Hels

/-- Raise a context's bound, at full authority (the step `ctx_absorb` makes
against a view receipt, here made outright). -/
theorem ctxAt_raise (ξ : CtxId) (B B' : Nat) (D : RegMapF CPU) (h : B ≤ B') :
    ctxAt (GF := GF) ξ 1 B D ⊢ |==> (ctxAt ξ 1 B' D ∗ ctxFloor ξ B') := by
  unfold ctxAt
  iintro ⟨Hb, Hd⟩
  imod MonoNat.own_update _ (.ofNat B) (.ofNat B') (by simp only [MaxNat.le_toNat]; omega)
    $$ Hb with ⟨Hb, #Hlb⟩
  imodintro
  iframe Hb Hd
  unfold ctxFloor
  iright
  iexact Hlb

/-- **THE DEPOSIT**: a payload moves INTO a stamped context from a running
one, and the stamp is RAISED to cover it -- so there is nothing to prove at
the deposit site; whoever takes it next pays the raised stamp.  (Rocq's
`ctx_deposit`.) -/
theorem ctxDeposit (R : CtxId → IProp GF) [CtxMorph R] (cpu : CPU) (ξ ξc : CtxId) (T : Nat) :
    ownCtx (GF := GF) cpu ξ ∗ ctxStamped ξc T ∗ R ξ ⊢
      |==> (ownCtx cpu ξ ∗ ∃ T' : Nat, ⌜T ≤ T'⌝ ∗ ctxStamped ξc T' ∗ R ξc) := by
  iintro ⟨Hrun, Hst, HR⟩
  icases ownCtx_cases cpu ξ $$ Hrun with ⟨%B, %K, %W, %D, Hat, #HK, %hBK, #HW, %hok, #Hels⟩
  icases ctxStamped_cases ξc T $$ Hst with ⟨%Dc, Hatc, #HTc, %hDc, #Helsc⟩
  imod ctxAt_raise ξc T (max T (max K W)) Dc (by omega) $$ Hatc with ⟨Hatc, #HflcT⟩
  icases (ctxAt_halves ξ B D).1 $$ Hat with ⟨Hat1, Hat2⟩
  ihave Hdom : ctxDom ξ ξc $$ [Hat1]
  · iapply ctxDomAt_intro ξ ξc _ B D
    iframe Hat1
    isplit
    · iapply ctxFloor_le ξc (max T (max K W)) B (by omega); iexact HflcT
    isplit
    · iexact Hels
    · imodintro
      iintro %k %h %hk
      unfold keyAt
      ileft
      iapply ctxFloor_le ξc (max T (max K W)) k (by have := (hok k h hk).1; omega)
      iexact HflcT
  imod CtxMorph.morph (R := R) ξ ξc $$ [$Hdom $HR] with ⟨Hdom, HR⟩
  icases ctxDomAt_cases ξ ξc _ $$ Hdom with ⟨%B2, %D2, Hat1, -, -, -⟩
  ihave %heq : ⌜B2 = B ∧ D2 = D⌝ $$ [Hat1 Hat2]
  · iapply ctxAt_agree ξ _ _ B2 B D2 D $$ [Hat1 Hat2]
    iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hat := (ctxAt_halves ξ B2 D2).2 $$ [Hat1 Hat2]
  · iframe
  imodintro
  isplitl [Hat]
  · iapply ownCtx_intro cpu ξ B2 K W D2
    iframe Hat
    isplit
    · iexact HK
    isplit
    · ipureintro; exact hBK
    isplit
    · iexact HW
    isplit
    · ipureintro; exact hok
    · iexact Hels
  iexists (max T (max K W))
  isplit
  · ipureintro; omega
  isplitl [Hatc]
  · unfold ctxStamped
    iexists Dc
    iframe Hatc
    isplit
    · iapply topLb_max T (max K W)
      isplit
      · iexact HTc
      iapply topLb_max K W
      isplit
      · iapply viewLb_topLb cpu K; iexact HK
      · iexact HW
    isplit
    · ipureintro; intro k h hk; have := hDc k h hk; omega
    · iexact Helsc
  · iexact HR

/-- `dirtyElems` is timeless (so a stamped context can be pulled out from
under an invariant's later). -/
instance dirtyElems_timeless (E : EraGS GF) (ξ : CtxId) (D : RegMapF CPU) :
    Timeless (PROP := IProp GF) (dirtyElems E ξ D) := by unfold dirtyElems; infer_instance

instance ctxStamped_timeless (ξ : CtxId) (T : Nat) :
    Timeless (ctxStamped (GF := GF) ξ T) := by unfold ctxStamped; infer_instance

end transport

/-! ## The registers -/

/-- **The L1 slot register** (Rocq's `slot_reg`): the floor L1 has reached,
the window flag, the identity the box holds, and -- while the window is open
-- the witness the parked `rest` sits at, with the stamp it sits at. -/
structure SlotReg (Id X : Type) where
  td : Nat
  win : Bool
  ident : Id
  x : Option (X × Nat)
  deriving Inhabited

/-- **The L2 slot register** (Rocq's `l2_reg`): the floor L2 has reached and
-- while a checkout is out -- the identity and the reference that is
parked. -/
structure L2Reg (Id : Type) where
  tp : Nat
  hold : Option (Id × Nat)
  deriving Inhabited

/-- **The box's ghost names**: the stamp map (reference id ↦ identity and
the stamp the reference witnessed), the count, and the two registers. -/
structure BoxNames where
  stm : GName
  cnt : GName
  slotd : GName
  slotp : GName

/-- **The client's payload family** (Rocq's four section parameters): the
header the L1 side reads and writes, the rest of the bundle, and the two
arm-indexed ghost residues. -/
structure BoxPay (GF : BundledGFunctors) (Id X : Type) where
  hdr : Id → X → CtxId → IProp GF
  rest : X → CtxId → IProp GF
  q1 : Nat → IProp GF
  q2 : IProp GF

/-- An id not in the list. -/
def freshId (L : List Nat) : Nat := L.foldr max 0 + 1

theorem foldr_max_ge : ∀ (L : List Nat), ∀ j ∈ L, j ≤ L.foldr max 0
  | [], _, hj => absurd hj (by simp)
  | a :: L, j, hj => by
      rcases List.mem_cons.1 hj with rfl | hj
      · simp only [List.foldr]; omega
      · have := foldr_max_ge L j hj; simp only [List.foldr]; omega

theorem freshId_not_mem (L : List Nat) : freshId L ∉ L := by
  intro hmem
  have := foldr_max_ge L _ hmem
  unfold freshId at this
  omega

section box

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {Id X : Type}

/-- The client's obligations: both halves of the bundle transport along a
domination, and everything in the body is timeless (so the box can be opened
and its arm consumed at one instruction). -/
class BoxPayOk (P : BoxPay GF Id X) : Prop where
  hdrMorph : ∀ i x, CtxMorph (GF := GF) (P.hdr i x)
  restMorph : ∀ x, CtxMorph (GF := GF) (P.rest x)
  hdrTimeless : ∀ i x ξ, Timeless (P.hdr i x ξ)
  restTimeless : ∀ x ξ, Timeless (P.rest x ξ)
  q1Timeless : ∀ c, Timeless (P.q1 c)
  q2Timeless : Timeless P.q2

attribute [instance] BoxPayOk.hdrMorph BoxPayOk.restMorph BoxPayOk.hdrTimeless
  BoxPayOk.restTimeless BoxPayOk.q1Timeless BoxPayOk.q2Timeless

variable [GhostMapG GF Nat (Id × Nat) RegMapF] [GhostVarG GF Nat]
variable [GhostVarG GF (L2Reg Id)]

/-! ## The ghosts, named -/

/-- The stamp authority: every live reference's identity and stamp. -/
def stampsAuth (γ : BoxNames) (M : RegMapF (Id × Nat)) : IProp GF := γ.stm ↪●MAP M

/-- One reference's element of the stamp map. -/
def stampElem (γ : BoxNames) (id : Nat) (v : Id × Nat) : IProp GF := γ.stm ↪◯MAP[id] v

/-- Half of the count (the other half sits beside L1's `refcnt` cell). -/
def cntHalf (γ : BoxNames) (c : Nat) : IProp GF := γ.cnt ↪VAR{.own (1 : Qp).half} c

section withX
variable [GhostVarG GF (SlotReg Id X)]

/-- Half of the L1 register. -/
def slotdHalf (γ : BoxNames) (r : SlotReg Id X) : IProp GF :=
  γ.slotd ↪VAR{.own (1 : Qp).half} r

/-- Half of the L2 register. -/
def slotpHalf (γ : BoxNames) (s : L2Reg Id) : IProp GF :=
  γ.slotp ↪VAR{.own (1 : Qp).half} s

/-- **A REFERENCE** at identity `i`, minted at stamp `T` (Rocq's `reference`
at a unit singleton): the stamp-map element, and the store-order receipt of
the stamp -- which, cashed against the holder's own floor, is what lets the
holder take the bundle out. -/
def boxRef (γ : BoxNames) (i : Id) (T : Nat) : IProp GF := iprop%
  ∃ id : Nat, stampElem (Id := Id) γ id (i, T) ∗ topLb T

/-- **THE L2 HOLDER'S HANDLE** (Rocq's `l2_hold`): the L2 register half,
naming exactly the reference the checkout parked -- so the park can take it
back. -/
def l2Hold (γ : BoxNames) (i : Id) (id : Nat) : IProp GF := iprop%
  ∃ tp : Nat, slotpHalf γ ⟨tp, some (i, id)⟩

/-- **L1's payload row**: the register half at rest, with the floor receipts
of the floor it records. -/
def l1Row (γ : BoxNames) (r : SlotReg Id X) (ξ : CtxId) : IProp GF := iprop%
  slotdHalf γ r ∗ ⌜r.win = false ∧ r.x = none⌝ ∗ ctxFloor ξ r.td ∗ topLb r.td

end withX

/-- **L2's payload row**, at rest: the register half with nothing held, and
its floor. -/
def l2Row (γ : BoxNames) (s : L2Reg Id) (ξ : CtxId) : IProp GF := iprop%
  slotpHalf γ s ∗ ⌜s.hold = none⌝ ∗ ctxFloor ξ s.tp

instance l2Row_morph (γ : BoxNames) (s : L2Reg Id) :
    CtxMorph (GF := GF) (l2Row γ s) := by unfold l2Row; infer_instance

instance slotpHalf_timeless (γ : BoxNames) (s : L2Reg Id) :
    Timeless (slotpHalf (GF := GF) γ s) := by unfold slotpHalf; infer_instance

/-- L2's row, folded (Rocq's `l2_row_fold`). -/
theorem l2Row_fold (γ : BoxNames) (T' : Nat) (ξ : CtxId) :
    slotpHalf (GF := GF) γ (⟨T', none⟩ : L2Reg Id) ∗ ctxFloor ξ T' ⊢
      l2Row γ (⟨T', none⟩ : L2Reg Id) ξ := by
  unfold l2Row
  iintro ⟨Hs, #Hfl⟩
  iframe Hs
  isplit
  · ipureintro; rfl
  · iexact Hfl

section withX2
variable [GhostVarG GF (SlotReg Id X)] [Inhabited Id] [Inhabited X]

/-! ## The arms -/

/-- The bundle, at rest in the box's own context. -/
def inArm (P : BoxPay GF Id X) (i : Id) (ξb : CtxId) : IProp GF := iprop%
  ∃ x : X, P.hdr i x ξb ∗ P.rest x ξb

/-- **THE THREE ARMS**, selected by the two registers: `IN` (both closed),
`OUT_L1` (L1's window open: the header is out, the rest is still parked at
the stamp the register names, and L1 has surrendered every live reference's
element), `OUT_L2` (a checkout is out: the parked reference's element is in
the box). -/
def boxArm (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId) (L : List Nat)
    (c : Nat) (r : SlotReg Id X) (s : L2Reg Id) : IProp GF :=
  match s.hold with
  | some ih =>
      iprop(⌜r.win = false⌝ ∗ ⌜ih.2 ∈ L⌝ ∗ (∃ T' : Nat, stampElem γ ih.2 (ih.1, T')) ∗ P.q2)
  | none =>
      match r.win with
      | true =>
        iprop(([∗list] id ∈ L, ∃ v : Id × Nat, stampElem γ id v) ∗
          (∃ x : X, ⌜r.x = some (x, T)⌝ ∗ P.rest x ξb) ∗ P.q1 c)
      | false => inArm P r.ident ξb

/-- **THE FOUR PURE ROWS** (Rocq's `box_rows`), over the id list `L` that
enumerates the stamp map's domain:

* `L` is exactly the live references, without repeats, and there are `c` of
  them (Σ: mass = refcount);
* every live reference names the identity the L1 register records (I);
* the L2-side cover (C): every live stamp is at or past `T`, or L2's floor
  register is;
* the L1-side cover (D): L1's floor register is at or past `T`, or some live
  reference witnesses `T` itself. -/
def boxRows (T : Nat) (M : RegMapF (Id × Nat)) (L : List Nat) (c : Nat)
    (r : SlotReg Id X) (s : L2Reg Id) : Prop :=
  L.Nodup ∧ L.length = c ∧
  (∀ id : Nat, id ∈ L ↔ (get? M id).isSome) ∧
  (∀ id v, get? M id = some v → v.1 = r.ident) ∧
  ((∀ id v, get? M id = some v → T ≤ v.2) ∨ T ≤ s.tp) ∧
  (T ≤ r.td ∨ ∃ id v, get? M id = some v ∧ v.2 = T)

/-- **THE BODY.** -/
def boxBody (P : BoxPay GF Id X) (γ : BoxNames) : IProp GF := iprop%
  ∃ (T : Nat) (ξb : CtxId) (M : RegMapF (Id × Nat)) (L : List Nat) (c : Nat)
    (r : SlotReg Id X) (s : L2Reg Id),
    ctxStamped ξb T ∗ stampsAuth γ M ∗ cntHalf γ c ∗ slotdHalf γ r ∗ slotpHalf γ s ∗
    ⌜boxRows T M L c r s⌝ ∗ boxArm P γ T ξb L c r s

/-- **THE BOX** (persistent). -/
def isBox (P : BoxPay GF Id X) (N : Namespace) (γ : BoxNames) : IProp GF :=
  inv N (boxBody P γ)

instance isBox_persistent (P : BoxPay GF Id X) (N : Namespace) (γ : BoxNames) :
    Persistent (isBox P N γ) := by unfold isBox; infer_instance

/-! ## Timelessness of the body -/

instance stampsAuth_timeless (γ : BoxNames) (M : RegMapF (Id × Nat)) :
    Timeless (stampsAuth (GF := GF) γ M) := by unfold stampsAuth; infer_instance
instance stampElem_timeless (γ : BoxNames) (id : Nat) (v : Id × Nat) :
    Timeless (stampElem (GF := GF) γ id v) := by unfold stampElem; infer_instance
instance cntHalf_timeless (γ : BoxNames) (c : Nat) :
    Timeless (cntHalf (GF := GF) γ c) := by unfold cntHalf; infer_instance
instance slotdHalf_timeless (γ : BoxNames) (r : SlotReg Id X) :
    Timeless (slotdHalf (GF := GF) γ r) := by unfold slotdHalf; infer_instance
instance inArm_timeless (P : BoxPay GF Id X) [BoxPayOk P] (i : Id) (ξb : CtxId) :
    Timeless (inArm P i ξb) := by unfold inArm; infer_instance

instance boxArm_timeless (P : BoxPay GF Id X) [BoxPayOk P] (γ : BoxNames) (T : Nat)
    (ξb : CtxId) (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id) :
    Timeless (boxArm P γ T ξb L c r s) := by
  cases hs : s.hold with
  | none => cases hw : r.win <;> simp only [boxArm, hs, hw] <;> infer_instance
  | some ih => simp only [boxArm, hs]; infer_instance

instance boxBody_timeless (P : BoxPay GF Id X) [BoxPayOk P] (γ : BoxNames) :
    Timeless (boxBody P γ) := by unfold boxBody; infer_instance

/-! ## The payload rows transport -/

instance inArm_morph (P : BoxPay GF Id X) [BoxPayOk P] (i : Id) : CtxMorph (inArm P i) := by
  unfold inArm; infer_instance

instance l1Row_morph (γ : BoxNames) (r : SlotReg Id X) :
    CtxMorph (GF := GF) (l1Row γ r) := by unfold l1Row; infer_instance

/-- L1's row, folded (Rocq's `l1_row_fold`). -/
theorem l1Row_fold (γ : BoxNames) (r : SlotReg Id X) (ξ : CtxId)
    (hw : r.win = false) (hx : r.x = none) :
    slotdHalf (GF := GF) γ r ∗ ctxFloor ξ r.td ∗ topLb r.td ⊢ l1Row γ r ξ := by
  unfold l1Row
  iintro ⟨Hr, #Hfl, #Ht⟩
  iframe Hr
  isplit
  · ipureintro; exact ⟨hw, hx⟩
  isplit
  · iexact Hfl
  · iexact Ht

/-- Split a full ghost variable into the two halves the box and its client
hold. -/
theorem ghostVar_halves {A : Type} [GhostVarG GF A] (g : GName) (a : A) :
    (g ↪VAR a) ⊢@{IProp GF} (g ↪VAR{.own (1 : Qp).half} a) ∗ (g ↪VAR{.own (1 : Qp).half} a) := by
  have h := ghost_var_split (GF := GF) (A := A) g a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iintro H
  ihave H2 := h $$ H
  iexact H2

/-! ## Agreement and update of the register halves -/

theorem cntHalf_agree (γ : BoxNames) (c c' : Nat) :
    cntHalf (GF := GF) γ c ∗ cntHalf γ c' ⊢ ⌜c = c'⌝ := by
  unfold cntHalf
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree _ _ _ _ _ $$ H1 H2
  ipureintro; exact h

theorem cntHalf_update (γ : BoxNames) (c c' c'' : Nat) :
    cntHalf (GF := GF) γ c ∗ cntHalf γ c' ⊢ |==> (cntHalf γ c'' ∗ cntHalf γ c'') := by
  unfold cntHalf
  iintro ⟨H1, H2⟩
  ihave H := ghost_var_update_halves c'' _ c c' $$ H1 H2
  iexact H

theorem slotdHalf_agree (γ : BoxNames) (r r' : SlotReg Id X) :
    slotdHalf (GF := GF) γ r ∗ slotdHalf γ r' ⊢ ⌜r = r'⌝ := by
  unfold slotdHalf
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree _ _ _ _ _ $$ H1 H2
  ipureintro; exact h

theorem slotdHalf_update (γ : BoxNames) (r r' r'' : SlotReg Id X) :
    slotdHalf (GF := GF) γ r ∗ slotdHalf γ r' ⊢ |==> (slotdHalf γ r'' ∗ slotdHalf γ r'') := by
  unfold slotdHalf
  iintro ⟨H1, H2⟩
  ihave H := ghost_var_update_halves r'' _ r r' $$ H1 H2
  iexact H

theorem slotpHalf_agree (γ : BoxNames) (s s' : L2Reg Id) :
    slotpHalf (GF := GF) γ s ∗ slotpHalf γ s' ⊢ ⌜s = s'⌝ := by
  unfold slotpHalf
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree _ _ _ _ _ $$ H1 H2
  ipureintro; exact h

theorem slotpHalf_update (γ : BoxNames) (s s' s'' : L2Reg Id) :
    slotpHalf (GF := GF) γ s ∗ slotpHalf γ s' ⊢ |==> (slotpHalf γ s'' ∗ slotpHalf γ s'') := by
  unfold slotpHalf
  iintro ⟨H1, H2⟩
  ihave H := ghost_var_update_halves s'' _ s s' $$ H1 H2
  iexact H

/-- Two full stamp-map elements at the same id cannot coexist. -/
theorem stampElem_excl (γ : BoxNames) (id : Nat) (v v' : Id × Nat) :
    stampElem (GF := GF) γ id v ∗ stampElem γ id v' ⊢ False := by
  unfold stampElem
  iintro ⟨H1, H2⟩
  ihave %hne := ghost_map_elem_frac_ne _ id id _ _ v v'
    (fun h => absurd (DFrac.valid_own_op h) (by simp)) $$ H1 H2
  exact absurd rfl hne

theorem stampsAuth_insert (γ : BoxNames) (M : RegMapF (Id × Nat)) (id : Nat) (v : Id × Nat)
    (h : get? M id = none) :
    stampsAuth (GF := GF) γ M ⊢
      |==> (stampsAuth γ (Iris.Std.PartialMap.insert M id v) ∗ stampElem γ id v) := by
  unfold stampsAuth stampElem
  iintro H
  imod ghost_map_insert id v h $$ H with ⟨H1, H2⟩
  imodintro; iframe

theorem stampsAuth_delete (γ : BoxNames) (M : RegMapF (Id × Nat)) (id : Nat) (v : Id × Nat) :
    stampsAuth (GF := GF) γ M ∗ stampElem γ id v ⊢
      |==> stampsAuth γ (Iris.Std.PartialMap.delete M id) := by
  unfold stampsAuth stampElem
  iintro ⟨H1, H2⟩
  imod ghost_map_delete id v $$ H1 H2 with H
  imodintro; iexact H

theorem stampsAuth_update (γ : BoxNames) (M : RegMapF (Id × Nat)) (id : Nat) (v w : Id × Nat) :
    stampsAuth (GF := GF) γ M ∗ stampElem γ id v ⊢
      |==> (stampsAuth γ (Iris.Std.PartialMap.insert M id w) ∗ stampElem γ id w) := by
  unfold stampsAuth stampElem
  iintro ⟨H1, H2⟩
  imod ghost_map_update w $$ H1 H2 with ⟨H1, H2⟩
  imodintro; iframe

theorem stampElem_lookup (γ : BoxNames) (M : RegMapF (Id × Nat)) (id : Nat) (v : Id × Nat) :
    stampsAuth (GF := GF) γ M ∗ stampElem γ id v ⊢ ⌜get? M id = some v⌝ := by
  unfold stampsAuth stampElem
  iintro ⟨H1, H2⟩
  ihave %h := ghost_map_lookup $$ H1 H2
  ipureintro; exact h

/-! ## Reading and rebuilding an arm -/

theorem boxArm_out2_cases (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id) (i : Id) (id : Nat)
    (hs : s.hold = some (i, id)) :
    boxArm P γ T ξb L c r s ⊢
      ⌜r.win = false⌝ ∗ ⌜id ∈ L⌝ ∗ (∃ T' : Nat, stampElem γ id (i, T')) ∗ P.q2 := by
  simp only [boxArm, hs]
  iintro H; iexact H

theorem boxArm_out2_intro (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id) (i : Id) (id : Nat)
    (hs : s.hold = some (i, id)) (hw : r.win = false) (hmem : id ∈ L) :
    (∃ T' : Nat, stampElem (GF := GF) γ id (i, T')) ∗ P.q2 ⊢ boxArm P γ T ξb L c r s := by
  simp only [boxArm, hs]
  iintro H
  isplit
  · ipureintro; exact hw
  isplit
  · ipureintro; exact hmem
  · iexact H

theorem boxArm_in_cases (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id)
    (hs : s.hold = none) (hw : r.win = false) :
    boxArm P γ T ξb L c r s ⊢ inArm P r.ident ξb := by
  simp only [boxArm, hs, hw]
  iintro H; iexact H

theorem boxArm_in_intro (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id)
    (hs : s.hold = none) (hw : r.win = false) :
    inArm P r.ident ξb ⊢ boxArm P γ T ξb L c r s := by
  simp only [boxArm, hs, hw]
  iintro H; iexact H

theorem boxArm_out1_cases (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id)
    (hs : s.hold = none) (hw : r.win = true) :
    boxArm P γ T ξb L c r s ⊢
      ([∗list] id ∈ L, ∃ v : Id × Nat, stampElem γ id v) ∗
        (∃ x : X, ⌜r.x = some (x, T)⌝ ∗ P.rest x ξb) ∗ P.q1 c := by
  simp only [boxArm, hs, hw]
  iintro H; iexact H

/-- The arm survives an enlargement of the id list and a change of count,
as long as L1's window is closed (only the open window mentions either). -/
theorem boxArm_widen (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L L' : List Nat) (c c' : Nat) (r : SlotReg Id X) (s : L2Reg Id)
    (hw : r.win = false) (hsub : ∀ j, j ∈ L → j ∈ L') :
    boxArm P γ T ξb L c r s ⊢ boxArm P γ T ξb L' c' r s := by
  cases hs : s.hold with
  | none => simp only [boxArm, hs, hw]; iintro H; iexact H
  | some ih =>
    simp only [boxArm, hs]
    iintro ⟨%h1, %h2, H⟩
    isplit
    · ipureintro; exact h1
    isplit
    · ipureintro; exact hsub _ h2
    · iexact H

/-- While L1's window is open the box holds EVERY live reference's element,
so no one else can hold one. -/
theorem boxArm_out1_excl (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id)
    (hs : s.hold = none) (hw : r.win = true) (id : Nat) (v : Id × Nat) (hmem : id ∈ L) :
    boxArm P γ T ξb L c r s ∗ stampElem γ id v ⊢ False := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hmem
  iintro ⟨Harm, Hel⟩
  icases boxArm_out1_cases P γ T ξb L c r s hs hw $$ Harm with ⟨Hbig, -, -⟩
  icases BigSepL.bigSepL_lookup_acc
      (Φ := fun (_ : Nat) (j : Nat) => iprop(∃ v : Id × Nat, stampElem (GF := GF) γ j v)) hn
      $$ Hbig with ⟨Hel2, -⟩
  icases Hel2 with ⟨%v2, Hel2⟩
  iapply stampElem_excl γ id v2 v $$ [Hel2 Hel]
  iframe

/-- The arm survives the removal of one reference from the id list, given
that reference's own element -- which refutes the possibility that the box
holds it (the checkout arm's element is full, and so is ours). -/
theorem boxArm_erase (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L : List Nat) (c c' : Nat) (r r' : SlotReg Id X) (s : L2Reg Id)
    (id : Nat) (v : Id × Nat) (hw : r.win = false) (hw' : r'.win = false)
    (hid : r'.ident = r.ident) (hnd : L.Nodup) :
    boxArm P γ T ξb L c r s ∗ stampElem γ id v ⊢
      boxArm P γ T ξb (L.erase id) c' r' s ∗ stampElem γ id v := by
  cases hs : s.hold with
  | none =>
    iintro ⟨Harm, Hel⟩
    iframe Hel
    ihave Hin := boxArm_in_cases P γ T ξb L c r s hs hw $$ Harm
    iapply boxArm_in_intro P γ T ξb (L.erase id) c' r' s hs hw'
    rw [hid]
    iexact Hin
  | some ih =>
    obtain ⟨i2, id2⟩ := ih
    iintro ⟨Harm, Hel⟩
    icases boxArm_out2_cases P γ T ξb L c r s i2 id2 hs $$ Harm with ⟨%_, %hm2, Hel2, HQ⟩
    by_cases hne : id2 = id
    · subst hne
      icases Hel2 with ⟨%T2, Hel2⟩
      iexfalso
      iapply stampElem_excl γ id2 (i2, T2) v $$ [Hel2 Hel]
      iframe
    · iframe Hel
      iapply boxArm_out2_intro P γ T ξb (L.erase id) c' r' s i2 id2 hs hw'
        ((List.mem_erase_of_ne hne).2 hm2)
      iframe Hel2 HQ

theorem boxArm_out1_intro (P : BoxPay GF Id X) (γ : BoxNames) (T : Nat) (ξb : CtxId)
    (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id)
    (hs : s.hold = none) (hw : r.win = true) :
    ([∗list] id ∈ L, ∃ v : Id × Nat, stampElem (GF := GF) γ id v) ∗
      (∃ x : X, ⌜r.x = some (x, T)⌝ ∗ P.rest x ξb) ∗ P.q1 c ⊢ boxArm P γ T ξb L c r s := by
  simp only [boxArm, hs, hw]
  iintro H; iexact H

/-! ## (c) `refs++`: a reference is minted at the box's current stamp -/

/-- Rocq's `box_ref_incr`. -/
theorem boxRefIncr (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace) (γ : BoxNames)
    (r : SlotReg Id X) (c : Nat) (E : CoPset) (hE : ↑N ⊆ E) (hw : r.win = false) :
    isBox P N γ ∗ slotdHalf γ r ∗ cntHalf γ c ⊢
      |={E}=> (slotdHalf γ r ∗ cntHalf γ (c + 1) ∗ ∃ T : Nat, boxRef γ r.ident T) := by
  iintro ⟨#Hbox, Hrd0, Hc0⟩
  unfold isBox
  iinv Hbox with Hbody Hclose
  unfold boxBody
  icases Hbody with ⟨%T, %ξb, %M, %L, %c1, %r1, %s1, >Hpk, >Hst, >Hc, >Hrd, >Hrp, >%hrows, >Harm⟩
  ihave %hr := slotdHalf_agree γ r1 r $$ [Hrd Hrd0]
  · iframe
  ihave %hc := cntHalf_agree γ c1 c $$ [Hc Hc0]
  · iframe
  subst hr; subst hc
  obtain ⟨hnd, hlen, hdom, hI, hC, hD⟩ := hrows
  -- the fresh reference id
  have hfresh : get? M (freshId L) = none := by
    cases hh : get? M (freshId L) with
    | none => rfl
    | some v => exact absurd ((hdom (freshId L)).2 (by rw [hh]; rfl)) (freshId_not_mem L)
  imod stampsAuth_insert γ M (freshId L) (r1.ident, T) hfresh $$ Hst with ⟨Hst, Hfr⟩
  imod cntHalf_update γ c1 c1 (c1 + 1) $$ [$Hc $Hc0] with ⟨Hc, Hc0⟩
  ihave ⟨#HtopT, Hpk⟩ := ctxStamped_topLb ξb T $$ Hpk
  ihave Harm := boxArm_widen P γ T ξb L (freshId L :: L) c1 (c1 + 1) r1 s1 hw
    (fun j hj => List.mem_cons_of_mem _ hj) $$ Harm
  ihave Hcl := Hclose $$ [Hpk Hst Hc Hrd Hrp Harm]
  case' _ =>
    inext
    iexists T, ξb, (Iris.Std.PartialMap.insert M (freshId L) (r1.ident, T)), (freshId L :: L), (c1 + 1), r1, s1
    iframe Hpk Hst Hc Hrd Hrp Harm
    ipureintro
    refine ⟨List.nodup_cons.2 ⟨freshId_not_mem L, hnd⟩, by simp [hlen], ?_, ?_, ?_, ?_⟩
    · intro id
      by_cases hid : freshId L = id
      · subst hid; simp [get?_insert_eq (rfl : freshId L = freshId L)]
      · rw [get?_insert_ne hid]
        constructor
        · intro hm; rcases List.mem_cons.1 hm with rfl | hm
          · exact absurd rfl hid
          · exact (hdom id).1 hm
        · intro hm; exact List.mem_cons_of_mem _ ((hdom id).2 hm)
    · intro id v hv
      by_cases hid : freshId L = id
      · subst hid; rw [get?_insert_eq (rfl : freshId L = freshId L)] at hv
        cases hv; rfl
      · rw [get?_insert_ne hid] at hv; exact hI id v hv
    · rcases hC with hC | hC
      · left; intro id v hv
        by_cases hid : freshId L = id
        · subst hid; rw [get?_insert_eq (rfl : freshId L = freshId L)] at hv
          cases hv; exact Nat.le_refl _
        · rw [get?_insert_ne hid] at hv; exact hC id v hv
      · right; exact hC
    · rcases hD with hD | ⟨id, v, hv, hv2⟩
      · left; exact hD
      · right
        refine ⟨id, v, ?_, hv2⟩
        by_cases hid : freshId L = id
        · subst hid; exact absurd hv (by rw [hfresh]; simp)
        · rw [get?_insert_ne hid]; exact hv
  imod Hcl
  imodintro
  iframe Hrd0 Hc0
  iexists T
  unfold boxRef
  iexists (freshId L)
  iframe Hfr
  iexact HtopT

/-! ## (d) `refs--`: a reference is burned; the L1 floor register joins its stamp -/

/-- Rocq's `box_ref_decr`. -/
theorem boxRefDecr (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace) (γ : BoxNames)
    (r : SlotReg Id X) (c : Nat) (i : Id) (T0 : Nat) (E : CoPset)
    (hE : ↑N ⊆ E) (hw : r.win = false) :
    isBox P N γ ∗ slotdHalf γ r ∗ topLb r.td ∗ cntHalf γ (c + 1) ∗ boxRef γ i T0 ⊢
      |={E}=> (slotdHalf γ ⟨max r.td T0, false, r.ident, r.x⟩ ∗ cntHalf γ c ∗
        topLb (max r.td T0)) := by
  iintro ⟨#Hbox, Hrd0, #Htd, Hc0, Href⟩
  unfold isBox boxRef
  icases Href with ⟨%id, Hel, #HT0⟩
  iinv Hbox with Hbody Hclose
  unfold boxBody
  icases Hbody with ⟨%T, %ξb, %M, %L, %c1, %r1, %s1, >Hpk, >Hst, >Hc, >Hrd, >Hrp, >%hrows, >Harm⟩
  ihave %hr := slotdHalf_agree γ r1 r $$ [Hrd Hrd0]
  · iframe
  ihave %hc := cntHalf_agree γ c1 (c + 1) $$ [Hc Hc0]
  · iframe
  subst hr; subst hc
  obtain ⟨hnd, hlen, hdom, hI, hC, hD⟩ := hrows
  ihave %hlk := stampElem_lookup γ M id (i, T0) $$ [Hst Hel]
  · iframe
  have hmem : id ∈ L := (hdom id).2 (by rw [hlk]; rfl)
  icases boxArm_erase P γ T ξb L (c + 1) c r1
      ⟨max r1.td T0, false, r1.ident, r1.x⟩ s1 id (i, T0) hw rfl rfl hnd $$ [Harm Hel]
    with ⟨Harm, Hel⟩
  · iframe
  imod stampsAuth_delete γ M id (i, T0) $$ [$Hst $Hel] with Hst
  imod cntHalf_update γ (c + 1) (c + 1) c $$ [$Hc $Hc0] with ⟨Hc, Hc0⟩
  imod slotdHalf_update γ r1 r1 ⟨max r1.td T0, false, r1.ident, r1.x⟩ $$ [$Hrd $Hrd0]
    with ⟨Hrd, Hrd0⟩
  ihave #Hmax : topLb (max r1.td T0) $$ []
  · iapply topLb_max r1.td T0
    isplit
    · iexact Htd
    · iexact HT0
  ihave Hcl := Hclose $$ [Hpk Hst Hc Hrd Hrp Harm]
  case' _ =>
    inext
    iexists T, ξb, (Iris.Std.PartialMap.delete M id), (L.erase id), c,
      (⟨max r1.td T0, false, r1.ident, r1.x⟩ : SlotReg Id X), s1
    iframe Hpk Hst Hc Hrd Hrp Harm
    ipureintro
    refine ⟨List.Nodup.erase id hnd, by rw [List.length_erase_of_mem hmem, hlen]; omega, ?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : id = j
      · subst hj
        rw [get?_delete_eq (rfl : id = id)]
        simp only [Option.isSome_none, Bool.false_eq_true, iff_false]
        exact List.Nodup.not_mem_erase hnd
      · rw [get?_delete_ne hj, List.mem_erase_of_ne (fun hh => hj hh.symm)]
        exact hdom j
    · intro j v hv
      by_cases hj : id = j
      · rw [get?_delete_eq hj] at hv; cases hv
      · rw [get?_delete_ne hj] at hv; exact hI j v hv
    · rcases hC with hC | hC
      · left; intro j v hv
        by_cases hj : id = j
        · rw [get?_delete_eq hj] at hv; cases hv
        · rw [get?_delete_ne hj] at hv; exact hC j v hv
      · right; exact hC
    · rcases hD with hD | ⟨j, v, hv, hv2⟩
      · left; exact le_trans hD (Nat.le_max_left _ _)
      · by_cases hj : id = j
        · left
          subst hj
          rw [hlk] at hv
          cases hv
          have h2 : T0 = T := hv2
          show T ≤ max r1.td T0
          omega
        · right
          exact ⟨j, v, by rw [get?_delete_ne hj]; exact hv, hv2⟩
  imod Hcl
  imodintro
  iframe Hrd0 Hc0
  iexact Hmax

/-! ## (a) `withdraw_L1`: the L1 window opens over the header -/

/-- Rocq's `box_withdraw_L1`, at count ZERO (`bbox_withdraw_L1`'s instance;
see the file header for why the general count is not ported).  The caller's
floor `Kd` covers L1's floor register, which by row (D) -- there being no
live reference to witness the stamp -- covers the box's stamp; so the header
may be absorbed into the caller's context, while the rest stays parked. -/
theorem boxWithdrawL1 (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace) (γ : BoxNames)
    (cpu : CPU) (ξ : CtxId) (r : SlotReg Id X) (Kd : Nat) (E : CoPset)
    (hE : ↑N ⊆ E) (hw : r.win = false) (hKd : r.td ≤ Kd) :
    isBox P N γ ∗ ownCtx cpu ξ ∗ ctxFloor ξ Kd ∗ slotdHalf γ r ∗ cntHalf γ 0 ∗ P.q1 0 ⊢
      |={E}=> (ownCtx cpu ξ ∗ cntHalf γ 0 ∗
        ∃ (x0 : X) (T0 : Nat), ⌜T0 ≤ Kd⌝ ∗
          slotdHalf γ ⟨r.td, true, r.ident, some (x0, T0)⟩ ∗ P.hdr r.ident x0 ξ) := by
  iintro ⟨#Hbox, Hrun, #Hfld, Hrd0, Hc0, HQ1⟩
  unfold isBox
  iinv Hbox with Hbody Hclose
  unfold boxBody
  icases Hbody with ⟨%T, %ξb, %M, %L, %c1, %r1, %s1, >Hpk, >Hst, >Hc, >Hrd, >Hrp, >%hrows, >Harm⟩
  ihave %hr := slotdHalf_agree γ r1 r $$ [Hrd Hrd0]
  · iframe
  ihave %hc := cntHalf_agree γ c1 0 $$ [Hc Hc0]
  · iframe
  subst hr; subst hc
  obtain ⟨hnd, hlen, hdom, hI, hC, hD⟩ := hrows
  have hL : L = [] := List.length_eq_zero_iff.1 hlen
  subst hL
  have hMnone : ∀ j, get? M j = none := by
    intro j
    cases hh : get? M j with
    | none => rfl
    | some v => exact absurd ((hdom j).2 (by rw [hh]; rfl)) (by simp)
  have hTd : T ≤ r1.td := by
    rcases hD with h | ⟨j, v, hv, _⟩
    · exact h
    · exact absurd hv (by rw [hMnone j]; simp)
  rcases hh : s1.hold with _ | ⟨i2, id2⟩
  · -- IN: the bundle is at rest in the box's context
    ihave Hin := boxArm_in_cases P γ T ξb [] 0 r1 s1 hh hw $$ Harm
    icases ownCtx_floor_view cpu ξ Kd $$ [Hrun Hfld] with ⟨Hrun, ⟨%K, #HK, %hKdK⟩⟩
    · iframe Hrun; iexact Hfld
    unfold inArm
    icases Hin with ⟨%x0, Hhdr, Hrest⟩
    imod ctxAbsorbLb (P.hdr r1.ident x0) cpu ξb ξ T K (by omega) $$ [$Hrun $HK $Hpk $Hhdr]
      with ⟨Hrun, Hpk, Hhdr⟩
    imod slotdHalf_update γ r1 r1 ⟨r1.td, true, r1.ident, some (x0, T)⟩ $$ [$Hrd $Hrd0]
      with ⟨Hrd, Hrd0⟩
    ihave Hcl := Hclose $$ [Hpk Hst Hc Hrd Hrp Hrest HQ1]
    case' _ =>
      inext
      iexists T, ξb, M, [], 0, (⟨r1.td, true, r1.ident, some (x0, T)⟩ : SlotReg Id X), s1
      iframe Hpk Hst Hc Hrd Hrp
      isplit
      · ipureintro
        exact ⟨hnd, hlen, hdom, hI, hC, Or.inl hTd⟩
      iapply boxArm_out1_intro P γ T ξb [] 0
        (⟨r1.td, true, r1.ident, some (x0, T)⟩ : SlotReg Id X) s1 hh rfl
      isplitl []
      · exact BigSepL.bigSepL_nil_intro
      isplitl [Hrest]
      · iexists x0
        isplit
        · ipureintro; rfl
        · iexact Hrest
      · iexact HQ1
    imod Hcl
    imodintro
    iframe Hrun Hc0
    iexists x0, T
    isplit
    · ipureintro; omega
    iframe Hrd0
    iexact Hhdr
  · -- OUT_L2 is refuted: the parked reference would be a live one
    icases boxArm_out2_cases P γ T ξb [] 0 r1 s1 i2 id2 hh $$ Harm with ⟨%hw2, %hm2, -, -⟩
    exact absurd hm2 (by simp)

/-! ## (b) `deposit_L1`: the header comes back, at a NEW identity -/

/-- Rocq's `box_deposit_L1`, at count ZERO (so the count after the deposit is
`1`, Rocq's `max 1 c`): the header the window handed out is deposited back
into the box's context -- `ctxDeposit` RAISES the stamp, so the depositor
owes no floor -- and the chain's first reference is minted at the new
stamp. -/
theorem boxDepositL1 (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace) (γ : BoxNames)
    (cpu : CPU) (ξ : CtxId) (r : SlotReg Id X) (i' : Id) (x0 : X) (T0 : Nat) (E : CoPset)
    (hE : ↑N ⊆ E) (hw : r.win = true) (hx : r.x = some (x0, T0)) :
    isBox P N γ ∗ ownCtx cpu ξ ∗ slotdHalf γ r ∗ cntHalf γ 0 ∗ P.hdr i' x0 ξ ⊢
      |={E}=> (ownCtx cpu ξ ∗ P.q1 0 ∗
        ∃ T' : Nat, slotdHalf γ (⟨T', false, i', none⟩ : SlotReg Id X) ∗ cntHalf γ 1 ∗
          boxRef γ i' T' ∗ topLb T') := by
  iintro ⟨#Hbox, Hrun, Hrd0, Hc0, Hhdr⟩
  unfold isBox
  iinv Hbox with Hbody Hclose
  unfold boxBody
  icases Hbody with ⟨%T, %ξb, %M, %L, %c1, %r1, %s1, >Hpk, >Hst, >Hc, >Hrd, >Hrp, >%hrows, >Harm⟩
  ihave %hr := slotdHalf_agree γ r1 r $$ [Hrd Hrd0]
  · iframe
  ihave %hc := cntHalf_agree γ c1 0 $$ [Hc Hc0]
  · iframe
  subst hr; subst hc
  obtain ⟨hnd, hlen, hdom, hI, hC, hD⟩ := hrows
  have hL : L = [] := List.length_eq_zero_iff.1 hlen
  subst hL
  have hMnone : ∀ j, get? M j = none := by
    intro j
    cases hh : get? M j with
    | none => rfl
    | some v => exact absurd ((hdom j).2 (by rw [hh]; rfl)) (by simp)
  rcases hh : s1.hold with _ | ⟨i2, id2⟩
  · -- OUT_L1: the window is open, and the count says nothing was surrendered
    icases boxArm_out1_cases P γ T ξb [] 0 r1 s1 hh hw $$ Harm with ⟨-, ⟨%x, %hxx, Hrest⟩, HQ1⟩
    have hpe : (x0, T0) = (x, T) := Option.some.inj (hx.symm.trans hxx)
    have hx1 : x0 = x := congrArg Prod.fst hpe
    have hT1 : T = T0 := (congrArg Prod.snd hpe).symm
    subst hx1; subst hT1
    imod ctxDeposit (P.hdr i' x0) cpu ξ ξb T $$ [$Hrun $Hpk $Hhdr]
      with ⟨Hrun, ⟨%T', %hTT', Hpk, Hhdr⟩⟩
    ihave ⟨#HtopT', Hpk⟩ := ctxStamped_topLb ξb T' $$ Hpk
    imod stampsAuth_insert γ M (freshId ([] : List Nat)) (i', T') (hMnone _) $$ Hst
      with ⟨Hst, Hfr⟩
    imod cntHalf_update γ 0 0 1 $$ [$Hc $Hc0] with ⟨Hc, Hc0⟩
    imod slotdHalf_update γ r1 r1 ⟨T', false, i', none⟩ $$ [$Hrd $Hrd0] with ⟨Hrd, Hrd0⟩
    ihave Hcl := Hclose $$ [Hpk Hst Hc Hrd Hrp Hhdr Hrest]
    case' _ =>
      inext
      iexists T', ξb, (Iris.Std.PartialMap.insert M (freshId ([] : List Nat)) (i', T')),
        [freshId ([] : List Nat)], 1, (⟨T', false, i', none⟩ : SlotReg Id X), s1
      iframe Hpk Hst Hc Hrd Hrp
      isplit
      · ipureintro
        refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
        · intro j
          by_cases hj : freshId ([] : List Nat) = j
          · subst hj; simp [get?_insert_eq (rfl : freshId ([] : List Nat) = freshId [])]
          · rw [get?_insert_ne hj, hMnone j]
            simp only [List.mem_singleton, Option.isSome_none, Bool.false_eq_true, iff_false]
            exact fun hh2 => hj hh2.symm
        · intro j v hv
          by_cases hj : freshId ([] : List Nat) = j
          · subst hj; rw [get?_insert_eq (rfl : freshId ([] : List Nat) = freshId [])] at hv
            cases hv; rfl
          · rw [get?_insert_ne hj, hMnone j] at hv; cases hv
        · left
          intro j v hv
          by_cases hj : freshId ([] : List Nat) = j
          · subst hj; rw [get?_insert_eq (rfl : freshId ([] : List Nat) = freshId [])] at hv
            cases hv; exact Nat.le_refl _
          · rw [get?_insert_ne hj, hMnone j] at hv; cases hv
        · left; exact Nat.le_refl _
      iapply boxArm_in_intro P γ T' ξb [freshId ([] : List Nat)] 1
        (⟨T', false, i', none⟩ : SlotReg Id X) s1 hh rfl
      unfold inArm
      iexists x0
      iframe Hhdr Hrest
    imod Hcl
    imodintro
    iframe Hrun HQ1
    iexists T'
    iframe Hrd0 Hc0
    isplitl [Hfr]
    · unfold boxRef
      iexists (freshId ([] : List Nat))
      iframe Hfr
      iexact HtopT'
    · iexact HtopT'
  · -- OUT_L2 records a CLOSED window; the caller's half says it is open
    icases boxArm_out2_cases P γ T ξb [] 0 r1 s1 i2 id2 hh $$ Harm with ⟨%hw2, -, -, -⟩
    rw [hw2] at hw
    exact absurd hw (by simp)

/-! ## (e) the CHECKOUT: the whole bundle leaves, against a reference -/

/-- Rocq's `box_checkout`.  The taker's floor covers the box's stamp by row
(C) -- either through its own reference's stamp (`Kt`) or through L2's floor
register (`Kp`) -- so the bundle may be absorbed into its context; the
reference's element is handed to the box, and the register names it. -/
theorem boxCheckout (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace) (γ : BoxNames)
    (cpu : CPU) (ξ : CtxId) (i : Id) (T0 : Nat) (s0 : L2Reg Id) (Kt Kp : Nat) (E : CoPset)
    (hE : ↑N ⊆ E) (hs : s0.hold = none) (hKt : T0 ≤ Kt) (hKp : s0.tp ≤ Kp) :
    isBox P N γ ∗ ownCtx cpu ξ ∗ ctxFloor ξ Kt ∗ ctxFloor ξ Kp ∗ boxRef γ i T0 ∗ P.q2 ∗
      slotpHalf γ s0 ⊢
      |={E}=> (ownCtx cpu ξ ∗ inArm P i ξ ∗ ∃ id : Nat, l2Hold γ i id) := by
  iintro ⟨#Hbox, Hrun, #Hflt, #Hflp, Href, HQ2, Hrp0⟩
  unfold isBox boxRef
  icases Href with ⟨%id, Hel, #HT0⟩
  iinv Hbox with Hbody Hclose
  unfold boxBody
  icases Hbody with ⟨%T, %ξb, %M, %L, %c1, %r1, %s1, >Hpk, >Hst, >Hc, >Hrd, >Hrp, >%hrows, >Harm⟩
  ihave %hsq := slotpHalf_agree γ s1 s0 $$ [Hrp Hrp0]
  · iframe
  subst hsq
  obtain ⟨hnd, hlen, hdom, hI, hC, hD⟩ := hrows
  ihave %hlk := stampElem_lookup γ M id (i, T0) $$ [Hst Hel]
  · iframe
  have hmem : id ∈ L := (hdom id).2 (by rw [hlk]; rfl)
  have hIi : i = r1.ident := hI id (i, T0) hlk
  subst hIi
  cases hwv : r1.win with
  | true =>
    iexfalso
    iapply boxArm_out1_excl P γ T ξb L c1 r1 s1 hs hwv id (r1.ident, T0) hmem $$ [Harm Hel]
    iframe
  | false =>
    ihave Hin := boxArm_in_cases P γ T ξb L c1 r1 s1 hs hwv $$ Harm
    ihave Hcov : (ownCtx cpu ξ ∗ ∃ K : Nat, viewLb cpu K ∗ ⌜T ≤ K⌝) $$ [Hrun]
    · rcases hC with hC | hC
      · icases ownCtx_floor_view cpu ξ Kt $$ [Hrun Hflt] with ⟨Hrun, ⟨%K, #HK, %hk⟩⟩
        · iframe Hrun; iexact Hflt
        iframe Hrun
        iexists K
        iframe HK
        ipureintro
        have := hC id (r1.ident, T0) hlk
        simp only [] at this
        omega
      · icases ownCtx_floor_view cpu ξ Kp $$ [Hrun Hflp] with ⟨Hrun, ⟨%K, #HK, %hk⟩⟩
        · iframe Hrun; iexact Hflp
        iframe Hrun
        iexists K
        iframe HK
        ipureintro
        omega
    icases Hcov with ⟨Hrun, %K, #HK, %hTK⟩
    imod ctxAbsorbLb (inArm P r1.ident) cpu ξb ξ T K hTK $$ [$Hrun $HK $Hpk $Hin]
      with ⟨Hrun, Hpk, Hin⟩
    imod slotpHalf_update γ s1 s1 ⟨s1.tp, some (r1.ident, id)⟩ $$ [$Hrp $Hrp0]
      with ⟨Hrp, Hrp0⟩
    ihave Hcl := Hclose $$ [Hpk Hst Hc Hrd Hrp Hel HQ2]
    case' _ =>
      inext
      iexists T, ξb, M, L, c1, r1, (⟨s1.tp, some (r1.ident, id)⟩ : L2Reg Id)
      iframe Hpk Hst Hc Hrd Hrp
      isplit
      · ipureintro
        exact ⟨hnd, hlen, hdom, hI, hC, hD⟩
      iapply boxArm_out2_intro P γ T ξb L c1 r1
        (⟨s1.tp, some (r1.ident, id)⟩ : L2Reg Id) r1.ident id rfl hwv hmem
      isplitl [Hel]
      · iexists T0; iexact Hel
      · iexact HQ2
    imod Hcl
    imodintro
    iframe Hrun Hin
    iexists id
    unfold l2Hold
    iexists s1.tp
    iexact Hrp0

/-! ## (f) the PARK: the bundle goes back, and the reference is re-stamped -/

/-- Rocq's `box_park`.  `ctxDeposit` raises the box's stamp to cover the
bundle; the parked reference comes back MINTED AT THE NEW STAMP, which is
what row (D) needs and what the next taker's floor will have to pass. -/
theorem boxPark (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace) (γ : BoxNames)
    (cpu : CPU) (ξ : CtxId) (i : Id) (id : Nat) (E : CoPset) (hE : ↑N ⊆ E) :
    isBox P N γ ∗ ownCtx cpu ξ ∗ inArm P i ξ ∗ l2Hold γ i id ⊢
      |={E}=> (ownCtx cpu ξ ∗ P.q2 ∗ ∃ T' : Nat,
        slotpHalf γ (⟨T', none⟩ : L2Reg Id) ∗ boxRef γ i T' ∗ topLb T') := by
  iintro ⟨#Hbox, Hrun, Hin, Hhold⟩
  unfold isBox l2Hold
  icases Hhold with ⟨%tp, Hrp0⟩
  iinv Hbox with Hbody Hclose
  unfold boxBody
  icases Hbody with ⟨%T, %ξb, %M, %L, %c1, %r1, %s1, >Hpk, >Hst, >Hc, >Hrd, >Hrp, >%hrows, >Harm⟩
  ihave %hsq := slotpHalf_agree γ s1 ⟨tp, some (i, id)⟩ $$ [Hrp Hrp0]
  · iframe
  subst hsq
  obtain ⟨hnd, hlen, hdom, hI, hC, hD⟩ := hrows
  icases boxArm_out2_cases P γ T ξb L c1 r1 ⟨tp, some (i, id)⟩ i id rfl $$ Harm
    with ⟨%hwv, %hmem, Hel, HQ2⟩
  icases Hel with ⟨%T2, Hel⟩
  ihave %hlk := stampElem_lookup γ M id (i, T2) $$ [Hst Hel]
  · iframe
  have hIi : i = r1.ident := hI id (i, T2) hlk
  subst hIi
  imod ctxDeposit (inArm P r1.ident) cpu ξ ξb T $$ [$Hrun $Hpk $Hin]
    with ⟨Hrun, ⟨%T', %hTT', Hpk, Hin⟩⟩
  ihave ⟨#HtopT', Hpk⟩ := ctxStamped_topLb ξb T' $$ Hpk
  imod stampsAuth_update γ M id (r1.ident, T2) (r1.ident, T') $$ [$Hst $Hel] with ⟨Hst, Hel⟩
  imod slotpHalf_update γ ⟨tp, some (r1.ident, id)⟩ ⟨tp, some (r1.ident, id)⟩
    (⟨T', none⟩ : L2Reg Id) $$ [$Hrp $Hrp0] with ⟨Hrp, Hrp0⟩
  ihave Hcl := Hclose $$ [Hpk Hst Hc Hrd Hrp Hin]
  case' _ =>
    inext
    iexists T', ξb, (Iris.Std.PartialMap.insert M id (r1.ident, T')), L, c1, r1,
      (⟨T', none⟩ : L2Reg Id)
    iframe Hpk Hst Hc Hrd Hrp
    isplit
    · ipureintro
      refine ⟨hnd, hlen, ?_, ?_, Or.inr (Nat.le_refl _), Or.inr ⟨id, (r1.ident, T'), ?_, rfl⟩⟩
      · intro j
        by_cases hj : id = j
        · subst hj
          rw [get?_insert_eq (rfl : id = id)]
          simp only [Option.isSome_some, iff_true]
          exact hmem
        · rw [get?_insert_ne hj]; exact hdom j
      · intro j v hv
        by_cases hj : id = j
        · subst hj; rw [get?_insert_eq (rfl : id = id)] at hv; cases hv; rfl
        · rw [get?_insert_ne hj] at hv; exact hI j v hv
      · rw [get?_insert_eq (rfl : id = id)]
    iapply boxArm_in_intro P γ T' ξb L c1 r1 (⟨T', none⟩ : L2Reg Id) rfl hwv
    iexact Hin
  imod Hcl
  imodintro
  iframe Hrun HQ2
  iexists T'
  iframe Hrp0
  isplitl [Hel]
  · unfold boxRef
    iexists id
    iframe Hel
    iexact HtopT'
  · iexact HtopT'

/-! ## The invariant-side view -/

/-- Rocq's `box_view`: a client may read the arm (to refute an alternative)
and put it straight back, without touching a register. -/
theorem boxView (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace) (γ : BoxNames)
    (E : CoPset) (hE : ↑N ⊆ E) :
    isBox P N γ ⊢ |={E, E \ ↑N}=> ∃ (T : Nat) (ξb : CtxId) (M : RegMapF (Id × Nat))
      (L : List Nat) (c : Nat) (r : SlotReg Id X) (s : L2Reg Id),
      ⌜boxRows T M L c r s⌝ ∗ boxArm P γ T ξb L c r s ∗
      (boxArm P γ T ξb L c r s ={E \ ↑N, E}=∗ True) := by
  iintro #Hbox
  unfold isBox inv
  ihave Hacc := Hbox $$ %E %hE
  icases Hacc with #Hacc
  imod Hacc with ⟨Hbody, Hclose⟩
  unfold boxBody
  icases Hbody with ⟨%T, %ξb, %M, %L, %c1, %r1, %s1, >Hpk, >Hst, >Hc, >Hrd, >Hrp, >%hrows, >Harm⟩
  imodintro
  iexists T, ξb, M, L, c1, r1, s1
  isplit
  · ipureintro; exact hrows
  isplitl [Harm]
  · iexact Harm
  iintro Harm
  ihave Hcl := Hclose $$ [Hpk Hst Hc Hrd Hrp Harm]
  case' _ =>
    inext
    iexists T, ξb, M, L, c1, r1, s1
    iframe Hpk Hst Hc Hrd Hrp Harm
    ipureintro; exact hrows
  imod Hcl
  imodintro
  itrivial

/-! ## Allocation -/

/-- Rocq's `box_alloc_at`: the box is built at names already allocated, out
of a bundle the creator holds in its own running context.  The bundle moves
to a fresh twin context, which is stamped: that stamp is the box's first
`T`, and the L1 register's floor. -/
theorem boxAllocAt (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace) (γ : BoxNames)
    (cpu : CPU) (ξ : CtxId) (i0 : Id) (E : CoPset) :
    stampsAuth γ (∅ : RegMapF (Id × Nat)) ∗ (γ.cnt ↪VAR (0 : Nat)) ∗
      (∃ r0 : SlotReg Id X, γ.slotd ↪VAR r0) ∗ (γ.slotp ↪VAR (⟨0, none⟩ : L2Reg Id)) ∗
      ownCtx cpu ξ ∗ inArm P i0 ξ ⊢
      |={E}=> (ownCtx cpu ξ ∗ ∃ Tb : Nat, isBox P N γ ∗
        slotdHalf γ (⟨Tb, false, i0, none⟩ : SlotReg Id X) ∗ topLb Tb ∗ cntHalf γ 0 ∗
        slotpHalf γ (⟨0, none⟩ : L2Reg Id)) := by
  iintro ⟨Hst, Hcnt, Hrd, Hrp, Hrun, Hin⟩
  icases Hrd with ⟨%r0, Hrd⟩
  imod ownCtx_new cpu ξ $$ Hrun with ⟨Hrun, ⟨%ξb, Hξb⟩⟩
  imod ctx_move (inArm P i0) cpu ξ ξb $$ [$Hrun $Hξb $Hin] with ⟨Hrun, Hξb, Hin⟩
  imod ctx_stamp cpu ξb $$ Hξb with ⟨%Tb, Hpk, -⟩
  ihave ⟨#HtopTb, Hpk⟩ := ctxStamped_topLb ξb Tb $$ Hpk
  imod ghost_var_update (⟨Tb, false, i0, none⟩ : SlotReg Id X) γ.slotd r0 $$ Hrd with Hrd
  icases ghostVar_halves γ.cnt (0 : Nat) $$ Hcnt with ⟨Hc, Hc0⟩
  icases ghostVar_halves γ.slotd (⟨Tb, false, i0, none⟩ : SlotReg Id X) $$ Hrd with ⟨Hrd, Hrd0⟩
  icases ghostVar_halves γ.slotp (⟨0, none⟩ : L2Reg Id) $$ Hrp with ⟨Hrp, Hrp0⟩
  imod inv_alloc N E (boxBody P γ) $$ [Hpk Hst Hc Hrd Hrp Hin] with #Hinv
  · inext
    unfold boxBody
    iexists Tb, ξb, (∅ : RegMapF (Id × Nat)), ([] : List Nat), 0,
      (⟨Tb, false, i0, none⟩ : SlotReg Id X), (⟨0, none⟩ : L2Reg Id)
    iframe Hpk
    unfold stampsAuth cntHalf slotdHalf slotpHalf
    iframe Hst Hc Hrd Hrp
    isplit
    · ipureintro
      refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
      · intro j; rw [get?_empty]; simp
      · intro j v hv; rw [get?_empty] at hv; cases hv
      · left; intro j v hv; rw [get?_empty] at hv; cases hv
      · left; exact Nat.le_refl _
    iapply boxArm_in_intro P γ Tb ξb ([] : List Nat) 0
      (⟨Tb, false, i0, none⟩ : SlotReg Id X) (⟨0, none⟩ : L2Reg Id) rfl rfl
    iexact Hin
  imodintro
  iframe Hrun
  iexists Tb
  unfold isBox cntHalf slotdHalf slotpHalf
  iframe Hrd0 Hc0 Hrp0
  isplit
  · iexact Hinv
  · iexact HtopTb

/-- Rocq's `box_alloc`: the names are allocated too. -/
theorem boxAlloc (P : BoxPay GF Id X) [BoxPayOk P] (N : Namespace)
    (cpu : CPU) (ξ : CtxId) (i0 : Id) (E : CoPset) :
    ownCtx cpu ξ ∗ inArm P i0 ξ ⊢
      |={E}=> (ownCtx cpu ξ ∗ ∃ (γ : BoxNames) (Tb : Nat), isBox P N γ ∗
        slotdHalf γ (⟨Tb, false, i0, none⟩ : SlotReg Id X) ∗ topLb Tb ∗ cntHalf γ 0 ∗
        slotpHalf γ (⟨0, none⟩ : L2Reg Id)) := by
  iintro ⟨Hrun, Hin⟩
  imod ghost_map_alloc_empty (K := Nat) (V := Id × Nat) (H := RegMapF) with ⟨%g1, Hst⟩
  imod ghost_var_alloc (GF := GF) (0 : Nat) with ⟨%g2, Hcnt⟩
  imod ghost_var_alloc (GF := GF) (default : SlotReg Id X) with ⟨%g3, Hrd⟩
  imod ghost_var_alloc (GF := GF) (⟨0, none⟩ : L2Reg Id) with ⟨%g4, Hrp⟩
  imod boxAllocAt P N ⟨g1, g2, g3, g4⟩ cpu ξ i0 E
    $$ [Hst Hcnt Hrd Hrp Hrun Hin] with ⟨Hrun, ⟨%Tb, H⟩⟩
  · unfold stampsAuth
    iframe Hst Hcnt Hrp Hrun Hin
    iexists (default : SlotReg Id X)
    iexact Hrd
  imodintro
  iframe Hrun
  iexists ⟨g1, g2, g3, g4⟩, Tb
  iexact H

end withX2

end box

end MachCSL
