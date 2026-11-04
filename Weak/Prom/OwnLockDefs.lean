/-
Weak/Prom: **G4 target (1a) on track (b): the spinlock test and the LOCK PROTOCOL with the (b1) PULL** (stage S4b
part 2; plan rev 7 §4 "Pull rule" (b1), "Gate G4" (1a): the manual's Example 1, `amoswap.w.aq` / release
`amoswap.w.rl x0,x0,(a0)`, with a critical-section counter `ld; addi; sd`).

Test `lkT` (real litmus front end; the counter `c` = 0x1000 (8 bytes), the lock word `lk` = 0x2000 (4 bytes), image 0),
both harts run
`amoswap.w.aq x5,x6,(x10); bne x5,x0,END; ld x7,(x11); addi x7,x7,1; sd x7,(x11); amoswap.w.rl x0,x0,(x10)`
(x6 = 1, x10 = lk, x11 = c).  The litmus front end has forward branches only, so a failed acquire gives up (finite
runs; spin loops need the prefix lemma S3d, separate).  Verdict: if both harts acquired (x5 = 0), their counter
values differ (mutual exclusion of the critical sections).

THE (b1) PULL (plan §4): the promise agent, appending an acquire-shaped message `u` of hart `i` while the lock is
FREE (its resource R — the counter's points-to — in the live cell `lc`, the latest in-place release or the image),
pulls R into `pulled(i, u)` (R stays in the state interpretation, on `i`'s behalf, and `i` becomes the counter's
holder: its counter promises appended from now on are BACKED, plan §4 (b2-own) "owned or pulled").  `i`'s AMO, at
its execution, consumes the pull iff it read the lock's byte 0 as 0 from a live message (the TAKER invariant
`LockOk.taker`: an AMO whose byte-0 answer `t0` is the image or a live release, with no other-hart write to the lock
byte in `(t0, ts)`, finds `pulled(h, u)` with `u ≤ ts`).  An in-place (release-class) acquire on a free lock does
the pull itself.  Releases are always in place: the release DEPOSITS R into a new live cell.  The case split of the
agent is total (R-b2): acquire-shaped (pull or attempt), other lock writes (dead), counter writes (backed by the
holder or dead), the rest (untracked).

Robustness to the prophecy (any final memory): a DEAD message is pending and never fulfilled; reading one sets
`bad`; a hart that read a dead lock message as "free" proceeds as a ROGUE and SPOILS the protocol (`spoil`: the lock
and counter clauses switch off; a permanent dead lock message witnesses that the run is not valid).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnMPLDefs

namespace Weak.Prom.Own.Lk

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y XRec xVal wrX toBytes_get relPrG)
open Weak.Prom.Ref (Instr Test two64)
open PLabel

/-! ## 1. The test -/

/-- The counter (8 bytes) and the lock word (4 bytes). -/
abbrev C : Int := X
abbrev Lw : Int := Y

/-- One hart's program (both harts run it). -/
def lkProg : List Instr :=
  [Weak.Prom.Ref.Lit.amoswapW true false 5 6 10, .br .ne 5 0 6, Weak.Prom.Ref.Lit.ld 7 11, .alui .add 7 7 1,
   Weak.Prom.Ref.Lit.sd 7 11, Weak.Prom.Ref.Lit.amoswapW false true 0 0 10]

def lkRegs0 : List (Nat × Nat) := [(6, 1), (10, Weak.Prom.Ref.Lit.Y), (11, Weak.Prom.Ref.Lit.X)]

/-- G4 (1a): two harts, the manual's Example 1 lock around a counter. -/
def lkT : Test :=
  { harts := [lkProg, lkProg]
    regs0 := [lkRegs0, lkRegs0]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev lkImg : Image := testImg lkT

theorem lkImg_zero (a : Int) : lkImg a = some 0 := by
  simp [lkImg, testImg, Test.imgF, lkT, bv8]

/-- THE (1a) VERDICT: if both harts acquired, their counter values differ. -/
def lkSpec (g0 g1 : List Nat) : Prop :=
  (g0[5]?).getD 0 = 0 → (g1[5]?).getD 0 = 0 → (g0[7]?).getD 0 ≠ (g1[7]?).getD 0

/-! ## 2. Messages -/

def acqMsg (h : Nat) : PMsg := ⟨Lw, toBytes 1 4, some h, .excl⟩
def relMsg (h : Nat) : PMsg := ⟨Lw, toBytes 0 4, some h, .excl⟩
def cMsg (h v : Nat) : PMsg := ⟨C, toBytes v 8, some h, .plain⟩

def isAcq (M : List PMsg) (t : Nat) : Prop := ∃ a, M[t - 1]? = some (acqMsg a)
def isRel (M : List PMsg) (t : Nat) : Prop := ∃ a, M[t - 1]? = some (relMsg a)
/-- Message `t` writes the lock's byte 0. -/
def wrL (M : List PMsg) (t : Nat) : Prop := wrA M t Lw

theorem acq_ne_rel (a b : Nat) : acqMsg a ≠ relMsg b := by
  intro h
  have := congrArg (fun m => m.byteAt Lw) h
  rw [show (acqMsg a).byteAt Lw = some 1 by simp [acqMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8],
    show (relMsg b).byteAt Lw = some 0 by simp [relMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8]] at this
  cases this

theorem acq_wrL {M : List PMsg} {t a : Nat} (h : M[t - 1]? = some (acqMsg a)) : wrL M t :=
  ⟨_, h, by simp [acqMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList]⟩

theorem rel_wrL {M : List PMsg} {t a : Nat} (h : M[t - 1]? = some (relMsg a)) : wrL M t :=
  ⟨_, h, by simp [relMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList]⟩

theorem acq_not_wrX {M : List PMsg} {t a : Nat} (h : M[t - 1]? = some (acqMsg a)) : ¬ wrX M t := by
  rintro ⟨j, hj, m, hm, hb⟩
  rw [h] at hm; cases hm
  have hlt : ¬ (Y ≤ X + (j : Int)) := by simp only [X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]; omega
  simp [acqMsg, PMsg.byteAt, hlt] at hb

theorem rel_not_wrX {M : List PMsg} {t a : Nat} (h : M[t - 1]? = some (relMsg a)) : ¬ wrX M t := by
  rintro ⟨j, hj, m, hm, hb⟩
  rw [h] at hm; cases hm
  have hlt : ¬ (Y ≤ X + (j : Int)) := by simp only [X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]; omega
  simp [relMsg, PMsg.byteAt, hlt] at hb

theorem c_not_wrL {M : List PMsg} {t a v : Nat} (h : M[t - 1]? = some (cMsg a v)) : ¬ wrL M t := by
  rintro ⟨m, hm, hb⟩
  rw [h] at hm; cases hm
  simp only [cMsg, PMsg.byteAt, X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at hb
  rw [if_pos (by omega)] at hb
  rw [List.getElem?_eq_none (by simp [toBytes, Weak.Prom.Ref.byteList] <;> omega)] at hb
  simp at hb

theorem c_not_acq {M : List PMsg} {t a v : Nat} (h : M[t - 1]? = some (cMsg a v)) : ¬ isAcq M t := by
  rintro ⟨b, hb⟩; rw [h] at hb; cases hb

theorem c_wrX {M : List PMsg} {t a v : Nat} (h : M[t - 1]? = some (cMsg a v)) : wrX M t :=
  ⟨0, by omega, _, h, by simp [cMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList]⟩

theorem cMsg_byte (a v j : Nat) (hj : j < 8) : (cMsg a v).byteAt (C + j) = (toBytes v 8)[j]? := by
  simp only [PMsg.byteAt, cMsg]
  rw [if_pos (by omega)]
  congr 1; omega

theorem acq_b0 (a : Nat) : (acqMsg a).byteAt Lw = some 1 := by
  simp [acqMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8]

theorem rel_b0 (a : Nat) : (relMsg a).byteAt Lw = some 0 := by
  simp [relMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8]

/-! ## 3. The protocol state -/

/-- The lock's state: R in the live cell; R pulled for `h` at its acquire-shaped message `u`; R owned by `h`. -/
inductive LSt where
  | free
  | pulled (h u : Nat)
  | owned (h u : Nat)

/-- The pure protocol state. -/
structure LkS where
  /-- dead lock messages (never fulfilled) -/
  Dl : Nat → Prop
  /-- dead counter messages -/
  Dc : Nat → Prop
  bad : Bool
  spoil : Bool
  /-- the counter's ownership record (holder, tenure start, latest message, value) -/
  cr : XRec
  /-- the live cell (latest in-place release, or 0 = the image) -/
  lc : Nat
  ls : LSt
  /-- per hart: 0 before the acquire, 1 holding the lock, 2 done, 3 rogue -/
  ph : Nat → Nat
  /-- per hart: the counter value it read (recorded at its store) -/
  rds : Nat → Option Nat
  /-- per hart: a counter message it read above its view and marked dead -/
  mark : Nat → Option Nat
  cnt : Nat

def pend (M : List PMsg) (σ : OSt (List Nat)) (t : Nat) : Prop := ∃ a, au M t = some a ∧ t ∈ σ.pr a

/-- A LIVE value-0 answer of the lock's byte 0: the image, or a live (non-dead) release. -/
def nd0 (M : List PMsg) (g : LkS) (t0 : Nat) : Prop := t0 = 0 ∨ (isRel M t0 ∧ ¬ g.Dl t0)

/-- `u` is the TAKER of the live cell for `h`. -/
def takerOk (M : List PMsg) (σ : OSt (List Nat)) (g : LkS) (h u : Nat) : Prop :=
  g.lc < u ∧ u ≤ σ.n ∧ M[u - 1]? = some (acqMsg h) ∧ (∀ t, g.lc < t → t < u → wrL M t → g.Dl t) ∧
    g.cr.hold = some h ∧ g.cr.tstart = u

def lsOk (M : List PMsg) (σ : OSt (List Nat)) (g : LkS) : LSt → Prop
  | .free => (∀ t, g.lc < t → t ≤ σ.n → wrL M t → g.Dl t) ∧ g.cr.hold = none ∧ g.cr.tstar ≤ g.lc ∧
      ∀ a, g.ph a ≠ 1
  | .pulled h u => takerOk M σ g h u ∧ g.cr.tstar < u ∧ ∀ a, g.ph a ≠ 1
  | .owned h u => takerOk M σ g h u ∧ g.ph h = 1 ∧ ∀ a, a ≠ h → g.ph a ≠ 1

/-- THE LOCK CLAUSES. -/
structure LockOk (M : List PMsg) (σ : OSt (List Nat)) (g : LkS) : Prop where
  lc_le : g.lc ≤ σ.n
  lc_ok : g.lc = 0 ∨ (isRel M g.lc ∧ ¬ g.Dl g.lc)
  wrL_cls : ∀ t, 1 ≤ t → t ≤ σ.n → wrL M t → g.Dl t ∨ isAcq M t ∨ (isRel M t ∧ t ≤ g.lc)
  rel_ph : ∀ t a, 1 ≤ t → t ≤ σ.n → M[t - 1]? = some (relMsg a) → ¬ g.Dl t → g.ph a = 2
  ls_ok : lsOk M σ g g.ls
  taker : ∀ h ts, ts ∈ σ.pr h → g.ph h = 0 → M[ts - 1]? = some (acqMsg h) → ∀ t0, t0 < ts → nd0 M g t0 →
    (∀ t, t0 < t → t < ts → wrL M t → au M t = some h) → ∃ u, u ≤ ts ∧ g.ls = .pulled h u

/-- THE COUNTER CLAUSES (MPL's record, holders changing with the lock). -/
structure COk (img : Image) (M : List PMsg) (σ : OSt (List Nat)) (g : LkS) : Prop where
  tstar_le : g.cr.tstar ≤ σ.n
  val : xVal img M g.cr.tstar g.cr.v
  tstart_le : g.cr.tstart ≤ σ.n
  later : ∀ t, g.cr.tstar < t → t ≤ σ.n → wrX M t →
    g.Dc t ∨ (g.cr.hold = au M t ∧ g.cr.tstart < t ∧ pend M σ t) ∨ (∃ a, au M t = some a ∧ t ∈ σ.pr a ∧ g.ph a = 2)
  dc : ∀ t, g.Dc t → 1 ≤ t ∧ t ≤ σ.n ∧ pend M σ t ∧ wrX M t
  dc_hold : ∀ t a, g.Dc t → g.cr.hold = some a → au M t = some a → t ≤ g.cr.tstart ∨ g.mark a = some t ∨ wrL M t

/-- THE COUNTER'S CLIENT CLAUSES. -/
structure CntOk (g : LkS) : Prop where
  v_cnt : g.cr.v = g.cnt
  rds_lt : ∀ a v, g.rds a = some v → v < g.cnt
  rds_inj : ∀ a b v, a ≠ b → g.rds a = some v → g.rds b = some v → False
  cnt_def : g.cnt = (if (g.rds 0).isSome then 1 else 0) + (if (g.rds 1).isSome then 1 else 0)
  rds_hi : ∀ a, 2 ≤ a → g.rds a = none

/-- A finished hart's registers: it did not acquire, or `bad`, or its counter value is its recorded read + 1. -/
def specH (gg : List Nat) (g : LkS) (h : Nat) : Prop :=
  (gg[5]?).getD 0 ≠ 0 ∨ g.bad = true ∨ ∃ v, g.rds h = some v ∧ (gg[7]?).getD 0 = (v + 1) % two64

/-- THE PROTOCOL. -/
structure LkOk (img : Image) (M : List PMsg) (σ : OSt (List Nat)) (g : LkS) : Prop where
  pr : ∀ a t, t ∈ σ.pr a → 1 ≤ t ∧ t ≤ σ.n ∧ au M t = some a
  dl : ∀ t, g.Dl t → 1 ≤ t ∧ t ≤ σ.n ∧ pend M σ t ∧ wrL M t ∧ ¬ isAcq M t
  bad : g.bad = true → (∃ t, g.Dl t) ∨ (g.spoil = false ∧ ∃ t, g.Dc t)
  spoil : g.spoil = true → g.bad = true ∧ ∃ t, g.Dl t
  lock : g.spoil = false → LockOk M σ g
  c : g.spoil = false → COk img M σ g
  cnt : g.bad = false → CntOk g
  done : ∀ h gg, σ.done h = some gg → specH gg g h
  /-- a rogue (phase 3) exists only in spoiled mode -/
  ph3 : ∀ a, g.ph a = 3 → g.spoil = true
  /-- a hart's mark witnesses `bad` -/
  mk_bad : ∀ a t, g.mark a = some t → g.bad = true

/-! ## 4. Pure facts -/

section facts

variable {img : Image} {M : List PMsg}

theorem pend_le {σ : OSt (List Nat)} {t : Nat} (hP : ∀ a t, t ∈ σ.pr a → 1 ≤ t ∧ t ≤ σ.n ∧ au M t = some a)
    (h : pend M σ t) : 1 ≤ t ∧ t ≤ σ.n := by
  obtain ⟨a, _, ha⟩ := h; exact ⟨(hP a t ha).1, (hP a t ha).2.1⟩

/-- THE FULFIL FACTS for the protocol (OwnKit.lean `fulO`). -/
theorem ful_facts {σ σ' : OSt (List Nat)} {h ts : Nat} {rc : Prop}
    (hP : ∀ a t, t ∈ σ.pr a → 1 ≤ t ∧ t ≤ σ.n ∧ au M t = some a) (hful : fulO M h σ rc ts σ') :
    σ'.done = σ.done ∧ σ.n ≤ σ'.n ∧ σ'.n ≤ σ.n + 1 ∧ ts ≤ σ'.n ∧ 1 ≤ ts ∧
      (∀ a t, t ∈ σ'.pr a ↔ (t ∈ σ.pr a ∧ t ≠ ts)) ∧
      ((ts ∈ σ.pr h ∧ σ'.n = σ.n ∧ ¬ rc) ∨ (ts = σ.n + 1 ∧ σ'.n = σ.n + 1 ∧ rc ∧ au M ts = some h)) := by
  rcases hful with ⟨hnr, hts, rfl⟩ | ⟨hrc, hn, hau, rfl, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := hP h ts hts
    refine ⟨rfl, Nat.le_refl _, by simp only; omega, h2, h1, fun a t => ?_, .inl ⟨hts, rfl, hnr⟩⟩
    by_cases e : a = h
    · subst e; simp only [upd_eq, elemOfDifference, elemOfSingleton]
    · simp only [upd_ne _ _ e]
      constructor
      · intro ht; refine ⟨ht, fun e2 => ?_⟩; subst e2
        have := (hP a _ ht).2.2; rw [h3] at this; cases this; exact e rfl
      · exact fun h => h.1
  · refine ⟨rfl, by simp only; omega, by simp only; omega, by simp only; omega, by omega, fun a t => ?_,
      .inr ⟨rfl, rfl, hrc, by simpa [au, authorAt] using hau⟩⟩
    simp only [relPrG (fun t ht => (hP h t ht).2.1)]
    constructor
    · intro ht; exact ⟨ht, fun e => by have := (hP a t ht).2.1; omega⟩
    · exact fun h => h.1

theorem pend_iff {σ σ' : OSt (List Nat)} {ts : Nat} (hpr : ∀ a t, t ∈ σ'.pr a ↔ (t ∈ σ.pr a ∧ t ≠ ts)) (t : Nat) :
    pend M σ' t ↔ pend M σ t ∧ t ≠ ts := by
  constructor
  · rintro ⟨a, h1, h2⟩; exact ⟨⟨a, h1, ((hpr a t).1 h2).1⟩, ((hpr a t).1 h2).2⟩
  · rintro ⟨⟨a, h1, h2⟩, h3⟩; exact ⟨a, h1, (hpr a t).2 ⟨h2, h3⟩⟩

/-- The x5 value of an `amoswap.w` that read byte 0 as `b0`: nonzero when `b0 ≠ 0`. -/
theorem amo_x5 {t0 : Nat} {b0 : BitVec 8} {rest : List (Nat × BitVec 8)} (hl : rest.length = 3)
    (h : (Weak.Prom.Ref.sext 4 (ofBytes (((t0, b0) :: rest).map Prod.snd))) % two64 = 0) : b0 = 0 := by
  match rest, hl with
  | [(_, b1), (_, b2), (_, b3)], _ =>
    have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
    simp only [Weak.Prom.Ref.sext, ofBytes, Weak.Prom.Ref.bytesVal, List.map, List.foldr, two64] at h
    apply BitVec.eq_of_toNat_eq
    show b0.toNat = 0
    split at h <;> omega

end facts

end Weak.Prom.Own.Lk
