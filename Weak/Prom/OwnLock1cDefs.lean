/-
Weak/Prom: **G4 (1c) + (3) on track (b): the LOCK PROTOCOL for xv6's exact text** (stage S4b part 3, tag S4b3;
plan rev 7 §4 "Gate G4" (1c): acquire `amoswap.w.aq a5,a5,(s1); sext.w; bnez; …; sd a0,16(s1)`, release
`sd zero,16(s1); fence rw,w; sw zero,0(s1)` (Xv6/KernelImage.lean:2265–2274, :2359–2364); (3) "A `holding()`-shaped
racy read that drives a branch").

A copy of (1a)'s protocol (OwnLockDefs … OwnLockSteps2.lean; the state `LkS`/`LSt` REUSED, so (1a)'s Iris layer —
`hv`, `Pg`, `Rbox`, the ghost bundle — applies) with three changes:
* THE RELEASE MESSAGE is xv6's PLAIN store `sw zero,0(s1)` (`relMsg h = ⟨lk, 0, h, .plain⟩`, was `.excl`); it is
  release-class by `fence rw,w` directly before it (plan §3's class, OwnMPL.lean `relClass_fW`), so in place;
* A FAILED ACQUIRE RETRIES (the spin loop `bnez a5,again`): the AMO leaf's nonzero branch keeps the hart in phase 0
  (`lk_acq`), was "give up" (phase 2);
* `specH`: a finished hart (it always acquired) recorded its counter read and its `holding()` read (x13) was
  nonzero — or `bad`.
New lemmas: `lk_untr` (a fulfil of a message that writes neither the lock byte nor the counter — xv6's `cpu` field
stores `sd a0,16(s1)` / `sd zero,16(s1)` — keeps the protocol), `lk_ldL` (THE `holding()` READ: the holder's racy
read of the lock word returns 1 — its own acquire or another hart's attempt — or a dead message), `lk_setBad`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLockSteps2

namespace Weak.Prom.Own.Lk1c

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y XRec xVal wrX toBytes_get relPrG map_snd_of)
open Weak.Prom.Own.Lk (C Lw LSt LkS)
open Weak.Prom.Ref (Instr Test two64)
open PLabel

/-- THE (1c) + (3) VERDICT: the two harts' counter values differ and both `holding()` reads were nonzero. -/
def lkSpec (g0 g1 : List Nat) : Prop :=
  (g0[7]?).getD 0 ≠ (g1[7]?).getD 0 ∧ (g0[13]?).getD 0 ≠ 0 ∧ (g1[13]?).getD 0 ≠ 0

/-! ## 2. Messages -/

def acqMsg (h : Nat) : PMsg := ⟨Lw, toBytes 1 4, some h, .excl⟩
def relMsg (h : Nat) : PMsg := ⟨Lw, toBytes 0 4, some h, .plain⟩
def cMsg (h v : Nat) : PMsg := ⟨C, toBytes v 8, some h, .plain⟩

def isAcq (M : List PMsg) (t : Nat) : Prop := ∃ a, M[t - 1]? = some (acqMsg a)
def isRel (M : List PMsg) (t : Nat) : Prop := ∃ a, M[t - 1]? = some (relMsg a)
/-- Message `t` writes the lock's byte 0. -/
def wrL (M : List PMsg) (t : Nat) : Prop := ∃ j : Nat, j < 4 ∧ wrA M t (Lw + j)
/-- Message `t` writes the lock's byte 0 (the AMO leaf's atomicity window, `exclOk` at byte 0). -/
def wrL0 (M : List PMsg) (t : Nat) : Prop := wrA M t Lw

theorem acq_ne_rel (a b : Nat) : acqMsg a ≠ relMsg b := by
  intro h
  have := congrArg (fun m => m.byteAt Lw) h
  rw [show (acqMsg a).byteAt Lw = some 1 by simp [acqMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8],
    show (relMsg b).byteAt Lw = some 0 by simp [relMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8]] at this
  cases this

theorem acq_wrL0 {M : List PMsg} {t a : Nat} (h : M[t - 1]? = some (acqMsg a)) : wrL0 M t :=
  ⟨_, h, by simp [acqMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList]⟩

theorem acq_wrL {M : List PMsg} {t a : Nat} (h : M[t - 1]? = some (acqMsg a)) : wrL M t :=
  ⟨0, by omega, _, h, by simp [acqMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList]⟩

theorem rel_wrL {M : List PMsg} {t a : Nat} (h : M[t - 1]? = some (relMsg a)) : wrL M t :=
  ⟨0, by omega, _, h, by simp [relMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList]⟩

theorem wrL_of_memByte {img : Image} {M : List PMsg} {t : Nat} {b : BitVec 8} (h1 : 1 ≤ t)
    (h : memByte img M t Lw = some b) : wrL M t :=
  ⟨0, by omega, by simpa using wrA_of_memByte h1 h⟩

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
  rintro ⟨j, hj, m, hm, hb⟩
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
    (∀ t, t0 < t → t < ts → wrL0 M t → au M t = some h) → ∃ u, u ≤ ts ∧ g.ls = .pulled h u

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

/-- A finished hart's registers (G4 (1c) + (3)): `bad`, or its counter value is its recorded read + 1 and its
`holding()` read (x13) was nonzero. -/
def specH (gg : List Nat) (g : LkS) (h : Nat) : Prop :=
  g.bad = true ∨ ∃ v, g.rds h = some v ∧ (gg[7]?).getD 0 = (v + 1) % two64 ∧ (gg[13]?).getD 0 ≠ 0

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



section agent

variable {img : Image} {M : List PMsg}

/-- THE INITIAL PROTOCOL STATE: the lock free in the image's cell, nobody holds the counter (value 0). -/
def g0 : LkS := ⟨fun _ => False, fun _ => False, false, false, ⟨none, 0, 0, 0⟩, 0, .free, fun _ => 0,
  fun _ => none, fun _ => none, 0⟩

theorem lk_init (hz : ∀ a, img a = some 0) : LkOk img M σ0 g0 := by
  have hval := (MPL.mpOk_init (img := img) (M := M) hz).2.2.2.1.2.1
  refine ⟨fun a t ht => absurd ht notElemOfEmpty, fun t ht => False.elim ht, fun h => (by cases h),
    fun h => (by cases h), fun _ => ?_, fun _ => ?_, fun _ => ?_, fun h gg hg => (by simp [σ0] at hg),
    fun a h => (by simp [g0] at h), fun a t h => (by cases h)⟩
  · refine ⟨Nat.le_refl _, .inl rfl, fun t h1 h2 _ => (by simp [σ0] at h2; omega),
      fun t a h1 h2 _ _ => (by simp [σ0] at h2; omega), ?_, fun h ts hts => absurd hts notElemOfEmpty⟩
    show lsOk M σ0 g0 LSt.free
    exact ⟨fun t h1 h2 _ => (by simp [σ0, g0] at h1 h2; omega), rfl, Nat.le_refl _, fun a => by simp [g0]⟩
  · exact ⟨Nat.le_refl _, hval, Nat.le_refl _, fun t h1 h2 _ => (by simp [σ0, g0] at h1 h2; omega),
      fun t ht => False.elim ht, fun t a ht => False.elim ht⟩
  · exact ⟨rfl, fun a v h => (by cases h), fun a b v _ h => (by cases h), by simp [g0], fun a _ => rfl⟩

theorem au_acq {t a : Nat} (h : M[t - 1]? = some (acqMsg a)) : au M t = some a := by
  simp [au, h, acqMsg]

theorem au_rel {t a : Nat} (h : M[t - 1]? = some (relMsg a)) : au M t = some a := by
  simp [au, h, relMsg]

/-- A live value-0 answer lies at or below the live cell. -/
theorem nd0_le {σ : OSt (List Nat)} {g : LkS} (hL : LockOk M σ g) {t0 : Nat} (hn : t0 ≤ σ.n) (h : nd0 M g t0) :
    t0 ≤ g.lc := by
  by_cases h0 : t0 = 0
  · omega
  rcases h with h | ⟨⟨a, ha⟩, hd⟩
  · omega
  · rcases hL.wrL_cls t0 (by omega) hn (rel_wrL ha) with u | ⟨b, hb⟩ | ⟨_, u⟩
    · exact absurd u hd
    · rw [ha] at hb; exact absurd (Option.some.inj hb).symm (acq_ne_rel b a)
    · exact u

theorem cnt_congr {g g' : LkS} (h1 : g'.cr.v = g.cr.v) (h2 : g'.rds = g.rds) (h3 : g'.cnt = g.cnt)
    (h4 : g'.bad = g.bad) (h : g.bad = false → CntOk g) : g'.bad = false → CntOk g' := by
  intro hb
  rw [h4] at hb
  obtain ⟨c1, c2, c3, c4, c5⟩ := h hb
  exact ⟨by rw [h1, h3]; exact c1, by rw [h2, h3]; exact c2, by rw [h2]; exact c3, by rw [h2, h3]; exact c4,
    by rw [h2]; exact c5⟩

theorem done_congr {σ σ' : OSt (List Nat)} {g g' : LkS} (h1 : σ'.done = σ.done) (h2 : g'.rds = g.rds)
    (h4 : g'.bad = g.bad) (h : ∀ h gg, σ.done h = some gg → specH gg g h) :
    ∀ h gg, σ'.done h = some gg → specH gg g' h := by
  intro hh gg hg
  rw [h1] at hg
  unfold specH; rw [h2, h4]; exact h hh gg hg

/-- THE PROMISE AGENT'S OBLIGATION (plan §4 "the promise agent's wp is the invariant"), with THE (b1) PULL. -/
theorem lk_agent {σ σ' : OSt (List Nat)} {g : LkS} (hok : LkOk img M σ g) (ha : agentStep (litOW img M) σ σ') :
    ∃ g', LkOk img M σ' g' ∧ g'.ph = g.ph ∧ g'.rds = g.rds ∧ g'.mark = g.mark ∧ g'.spoil = g.spoil ∧
      g'.cnt = g.cnt ∧ g'.bad = g.bad ∧
      ((g'.ls = g.ls ∧ g'.cr = g.cr) ∨ (g.spoil = false ∧ g.ls = .free ∧ ∃ i u, g'.ls = .pulled i u)) := by
  obtain ⟨i, hn, hau, rfl⟩ := ha
  have hau' : au M (σ.n + 1) = some i := by simpa [au, authorAt] using hau
  have hpr' : ∀ a t, t ∈ upd σ.pr i ({σ.n + 1} ∪ σ.pr i) a ↔ (t ∈ σ.pr a ∨ (a = i ∧ t = σ.n + 1)) := by
    intro a t
    by_cases e : a = i
    · subst e; simp only [upd_eq, elemOfUnion, elemOfSingleton]; constructor
      · rintro (h | h); exact .inr ⟨by simp, h⟩; exact .inl h
      · rintro (h | ⟨_, h⟩); exact .inr h; exact .inl h
    · simp only [upd_ne _ _ e]; constructor
      · exact .inl
      · rintro (h | ⟨h, _⟩); exact h; exact absurd h e
  have hpend : ∀ t, pend M { σ with n := σ.n + 1, pr := upd σ.pr i ({σ.n + 1} ∪ σ.pr i) } t ↔
      (pend M σ t ∨ t = σ.n + 1) := by
    intro t; constructor
    · rintro ⟨a, h1, h2⟩
      rcases (hpr' a t).1 h2 with h | ⟨_, h⟩
      · exact .inl ⟨a, h1, h⟩
      · exact .inr h
    · rintro (⟨a, h1, h2⟩ | rfl)
      · exact ⟨a, h1, (hpr' a t).2 (.inl h2)⟩
      · exact ⟨i, hau', (hpr' i _).2 (.inr ⟨rfl, rfl⟩)⟩
  have hP' : ∀ a t, t ∈ upd σ.pr i ({σ.n + 1} ∪ σ.pr i) a → 1 ≤ t ∧ t ≤ σ.n + 1 ∧ au M t = some a := by
    intro a t ht
    rcases (hpr' a t).1 ht with h | ⟨rfl, rfl⟩
    · obtain ⟨u1, u2, u3⟩ := hok.pr a t h; exact ⟨u1, by omega, u3⟩
    · exact ⟨by omega, Nat.le_refl _, hau'⟩
  -- the old pending timestamps are the new ones below `n + 1`
  have hold_pr : ∀ a t, t ≤ σ.n → (t ∈ upd σ.pr i ({σ.n + 1} ∪ σ.pr i) a ↔ t ∈ σ.pr a) := by
    intro a t ht; rw [hpr']; constructor
    · rintro (h | ⟨_, rfl⟩); exact h; omega
    · exact .inl
  by_cases hA : M[σ.n]? = some (acqMsg i)
  · have hA' : M[σ.n + 1 - 1]? = some (acqMsg i) := by simpa using hA
    have hnX : ¬ wrX M (σ.n + 1) := acq_not_wrX hA'
    -- an acquire-shaped promise: THE PULL (lock free) or an attempt
    by_cases hpull : g.spoil = false ∧ g.ls = .free
    · obtain ⟨hsp, hfree⟩ := hpull
      have hL := hok.lock hsp
      have hC := hok.c hsp
      have hls := hL.ls_ok; rw [hfree] at hls
      obtain ⟨hf1, hf2, hf3, hf4⟩ := hls
      refine ⟨{ g with ls := .pulled i (σ.n + 1), cr := { g.cr with hold := some i, tstart := σ.n + 1 } },
        ⟨hP', fun t ht => ?_, hok.bad, hok.spoil, fun _ => ?_, fun _ => ?_,
          cnt_congr (g := g) rfl rfl rfl rfl hok.cnt, done_congr (g := g) rfl rfl rfl hok.done,
          hok.ph3, hok.mk_bad⟩,
        rfl, rfl, rfl, rfl, rfl, rfl, .inr ⟨hsp, hfree, i, _, rfl⟩⟩
      · obtain ⟨u1, u2, u3, u4, u5⟩ := hok.dl t ht
        exact ⟨u1, by simp only; omega, (hpend t).2 (.inl u3), u4, u5⟩
      · refine ⟨by simp only; have := hL.lc_le; omega, hL.lc_ok, fun t h1 h2 h3 => ?_, fun t a h1 h2 h3 h4 => ?_,
          ?_, fun h ts hts hph hts' t0 ht0 hnd hwin => ?_⟩
        · by_cases e : t = σ.n + 1
          · subst e; exact .inr (.inl ⟨i, hA'⟩)
          · exact hL.wrL_cls t h1 (by simp only at h2; omega) h3
        · by_cases e : t = σ.n + 1
          · subst e; rw [hA'] at h3; exact absurd (Option.some.inj h3) (acq_ne_rel i a)
          · exact hL.rel_ph t a h1 (by simp only at h2; omega) h3 h4
        · refine ⟨⟨by simp only; have := hL.lc_le; omega, Nat.le_refl _, hA', fun t h1 h2 h3 => hf1 t h1 (by omega) h3,
            rfl, rfl⟩, by simp only; have := hL.lc_le; omega, hf4⟩
        · by_cases e : ts = σ.n + 1
          · subst e
            have : h = i := by
              have := (hP' h _ hts).2.2; rw [hau'] at this; cases this; rfl
            subst this
            exact ⟨σ.n + 1, Nat.le_refl _, rfl⟩
          · have hts0 : ts ≤ σ.n := by have := (hP' h ts hts).2.1; omega
            obtain ⟨u, _, hu⟩ := hL.taker h ts ((hold_pr h ts hts0).1 hts) hph hts' t0 ht0 hnd hwin
            rw [hfree] at hu; cases hu
      · refine ⟨by simp only; have := hC.tstar_le; omega, hC.val, Nat.le_refl _, fun t h1 h2 h3 => ?_,
          fun t ht => ?_, fun t a ht h1 h2 => ?_⟩
        · by_cases e : t = σ.n + 1
          · subst e; exact absurd h3 hnX
          · rcases hC.later t h1 (by simp only at h2; omega) h3 with u | ⟨u1, _, ⟨b, u3, _⟩⟩ | ⟨a, u1, u2, u3⟩
            · exact .inl u
            · rw [hf2, u3] at u1; cases u1
            · exact .inr (.inr ⟨a, u1, (hpr' a t).2 (.inl u2), u3⟩)
        · obtain ⟨u1, u2, u3, u4⟩ := hC.dc t ht
          exact ⟨u1, by simp only; omega, (hpend t).2 (.inl u3), u4⟩
        · exact .inl (by simp only; have := (hC.dc t ht).2.1; omega)
    · -- an attempt: nothing pulled
      refine ⟨g, ⟨hP', fun t ht => ?_, hok.bad, hok.spoil, fun hsp => ?_, fun hsp => ?_, hok.cnt,
          done_congr (g := g) rfl rfl rfl hok.done, hok.ph3, hok.mk_bad⟩,
        rfl, rfl, rfl, rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
      · obtain ⟨u1, u2, u3, u4, u5⟩ := hok.dl t ht
        exact ⟨u1, by simp only; omega, (hpend t).2 (.inl u3), u4, u5⟩
      · have hL := hok.lock hsp
        have hnf : g.ls ≠ .free := fun e => hpull ⟨hsp, e⟩
        refine ⟨by simp only; have := hL.lc_le; omega, hL.lc_ok, fun t h1 h2 h3 => ?_, fun t a h1 h2 h3 h4 => ?_,
          ?_, fun h ts hts hph hts' t0 ht0 hnd hwin => ?_⟩
        · by_cases e : t = σ.n + 1
          · subst e; exact .inr (.inl ⟨i, hA'⟩)
          · exact hL.wrL_cls t h1 (by simp only at h2; omega) h3
        · by_cases e : t = σ.n + 1
          · subst e; rw [hA'] at h3; exact absurd (Option.some.inj h3) (acq_ne_rel i a)
          · exact hL.rel_ph t a h1 (by simp only at h2; omega) h3 h4
        · have hls := hL.ls_ok
          revert hls
          cases hg : g.ls with
          | free => exact absurd hg hnf
          | pulled a u =>
            rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
            exact ⟨⟨u1, by simp only; omega, u3, u4, u5, u6⟩, u7, u8⟩
          | owned a u =>
            rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
            exact ⟨⟨u1, by simp only; omega, u3, u4, u5, u6⟩, u7, u8⟩
        · by_cases e : ts = σ.n + 1
          · subst e
            have : h = i := by
              have := (hP' h _ hts).2.2; rw [hau'] at this; cases this; rfl
            subst this
            have hle := nd0_le hL (by omega) hnd
            have hls := hL.ls_ok
            revert hls
            cases hg : g.ls with
            | free => exact absurd hg hnf
            | pulled a u =>
              rintro ⟨⟨u1, u2, u3, _⟩, _⟩
              have := hwin u (by omega) (by omega) (acq_wrL0 u3)
              rw [au_acq u3] at this; cases this
              exact ⟨u, by omega, rfl⟩
            | owned a u =>
              rintro ⟨⟨u1, u2, u3, _⟩, u7, _⟩
              have := hwin u (by omega) (by omega) (acq_wrL0 u3)
              rw [au_acq u3] at this; cases this
              rw [u7] at hph; cases hph
          · have hts0 : ts ≤ σ.n := by have := (hP' h ts hts).2.1; omega
            exact hL.taker h ts ((hold_pr h ts hts0).1 hts) hph hts' t0 ht0 hnd hwin
      · have hC := hok.c hsp
        refine ⟨by simp only; have := hC.tstar_le; omega, hC.val, by simp only; have := hC.tstart_le; omega,
          fun t h1 h2 h3 => ?_, fun t ht => ?_, hC.dc_hold⟩
        · by_cases e : t = σ.n + 1
          · subst e; exact absurd h3 hnX
          · rcases hC.later t h1 (by simp only at h2; omega) h3 with u | ⟨u1, u2, u3⟩ | ⟨a, u1, u2, u3⟩
            · exact .inl u
            · exact .inr (.inl ⟨u1, u2, (hpend t).2 (.inl u3)⟩)
            · exact .inr (.inr ⟨a, u1, (hpr' a t).2 (.inl u2), u3⟩)
        · obtain ⟨u1, u2, u3, u4⟩ := hC.dc t ht
          exact ⟨u1, by simp only; omega, (hpend t).2 (.inl u3), u4⟩
  · have hnA : ¬ isAcq M (σ.n + 1) := by
      rintro ⟨a, ha⟩
      have : au M (σ.n + 1) = some a := au_acq ha
      rw [hau'] at this; cases this
      exact hA (by simpa using ha)
    -- a write that is not acquire-shaped: dead if it writes the lock byte, or if it writes the counter and its
    -- author is not the holder (b2-none); backed if it writes the counter and its author is the holder (b2-own)
    let dl : Prop := wrL M (σ.n + 1)
    let dc : Prop := wrX M (σ.n + 1) ∧ (dl ∨ g.cr.hold ≠ some i)
    let g' : LkS := { g with Dl := fun t => g.Dl t ∨ (t = σ.n + 1 ∧ dl), Dc := fun t => g.Dc t ∨ (t = σ.n + 1 ∧ dc) }
    refine ⟨g', ⟨hP', fun t ht => ?_, fun hb => ?_, fun hs => ?_, fun hsp => ?_, fun hsp => ?_,
        cnt_congr (g := g) rfl rfl rfl rfl hok.cnt, done_congr (g := g) rfl rfl rfl hok.done,
          hok.ph3, hok.mk_bad⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
    · rcases ht with ht | ⟨rfl, hd⟩
      · obtain ⟨u1, u2, u3, u4, u5⟩ := hok.dl t ht
        exact ⟨u1, by simp only; omega, (hpend t).2 (.inl u3), u4, u5⟩
      · exact ⟨by omega, Nat.le_refl _, (hpend _).2 (.inr rfl), hd, hnA⟩
    · rcases hok.bad hb with ⟨t, ht⟩ | ⟨h1, t, ht⟩
      · exact .inl ⟨t, .inl ht⟩
      · exact .inr ⟨h1, t, .inl ht⟩
    · obtain ⟨h1, t, ht⟩ := hok.spoil hs; exact ⟨h1, t, .inl ht⟩
    · have hL := hok.lock hsp
      have hnd : ∀ t0, nd0 M g' t0 → t0 ≤ σ.n → nd0 M g t0 := by
        rintro t0 (rfl | ⟨hr, hd⟩) _
        · exact .inl rfl
        · exact .inr ⟨hr, fun h => hd (.inl h)⟩
      refine ⟨by show g.lc ≤ σ.n + 1; have := hL.lc_le; omega, ?_, fun t h1 h2 h3 => ?_, fun t a h1 h2 h3 h4 => ?_, ?_,
        fun h ts hts hph hts' t0 ht0 hnd' hwin => ?_⟩
      · rcases hL.lc_ok with u | ⟨u1, u2⟩
        · exact .inl u
        · exact .inr ⟨u1, fun hh => by rcases hh with hh | ⟨hh, _⟩; exact u2 hh; (change g.lc = σ.n + 1 at hh); have := hL.lc_le; omega⟩
      · by_cases e : t = σ.n + 1
        · subst e; exact .inl (.inr ⟨rfl, h3⟩)
        · rcases hL.wrL_cls t h1 (by simp only at h2; omega) h3 with u | u | u
          · exact .inl (.inl u)
          · exact .inr (.inl u)
          · exact .inr (.inr u)
      · by_cases e : t = σ.n + 1
        · subst e; exact absurd (.inr ⟨rfl, rel_wrL h3⟩) h4
        · exact hL.rel_ph t a h1 (by simp only at h2; omega) h3 (fun hh => h4 (.inl hh))
      · have hls := hL.ls_ok
        revert hls
        cases hg : g.ls with
        | free =>
          rintro ⟨u1, u2, u3, u4⟩
          refine ⟨fun t h1 h2 h3 => ?_, u2, u3, u4⟩
          by_cases e : t = σ.n + 1
          · subst e; exact .inr ⟨rfl, h3⟩
          · exact .inl (u1 t h1 (by simp only at h2; omega) h3)
        | pulled a u =>
          rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
          exact ⟨⟨u1, by simp only; omega, u3, fun t h1 h2 h3 => .inl (u4 t h1 h2 h3), u5, u6⟩, u7, u8⟩
        | owned a u =>
          rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
          exact ⟨⟨u1, by simp only; omega, u3, fun t h1 h2 h3 => .inl (u4 t h1 h2 h3), u5, u6⟩, u7, u8⟩
      · have hts0 : ts ≤ σ.n := by
          by_cases e : ts = σ.n + 1
          · subst e
            have : h = i := by
              have := (hP' h _ hts).2.2; rw [hau'] at this; cases this; rfl
            subst this
            exact absurd (by simpa using hts') hA
          · have := (hP' h ts hts).2.1; omega
        exact hL.taker h ts ((hold_pr h ts hts0).1 hts) hph hts' t0 ht0 (hnd t0 hnd' (by omega)) hwin
    · have hC := hok.c hsp
      refine ⟨by show g.cr.tstar ≤ σ.n + 1; have := hC.tstar_le; omega, hC.val,
        by show g.cr.tstart ≤ σ.n + 1; have := hC.tstart_le; omega,
        fun t h1 h2 h3 => ?_, fun t ht => ?_, fun t a ht h1 h2 => ?_⟩
      · by_cases e : t = σ.n + 1
        · subst e
          by_cases hdc : dc
          · exact .inl (.inr ⟨rfl, hdc⟩)
          · have hh : g.cr.hold = some i := by
              exact Classical.byContradiction fun hne => hdc ⟨h3, .inr hne⟩
            exact .inr (.inl ⟨by rw [hh, hau'], by show g.cr.tstart < σ.n + 1; have := hC.tstart_le; omega,
              (hpend _).2 (.inr rfl)⟩)
        · rcases hC.later t h1 (by simp only at h2; omega) h3 with u | ⟨u1, u2, u3⟩ | ⟨a, u1, u2, u3⟩
          · exact .inl (.inl u)
          · exact .inr (.inl ⟨u1, u2, (hpend t).2 (.inl u3)⟩)
          · exact .inr (.inr ⟨a, u1, (hpr' a t).2 (.inl u2), u3⟩)
      · rcases ht with ht | ⟨rfl, hd⟩
        · obtain ⟨u1, u2, u3, u4⟩ := hC.dc t ht
          exact ⟨u1, by simp only; omega, (hpend t).2 (.inl u3), u4⟩
        · exact ⟨by omega, Nat.le_refl _, (hpend _).2 (.inr rfl), hd.1⟩
      · rcases ht with ht | ⟨rfl, hd⟩
        · exact hC.dc_hold t a ht h1 h2
        · rcases hd.2 with hdl | hne
          · exact .inr (.inr hdl)
          · rw [hau'] at h2; cases h2; exact absurd h1 hne

end agent


section steps

variable {img : Image} {M : List PMsg}

/-! ### Frames -/

/-- The P-level clauses across a fulfil of a message that is not a dead lock message. -/
theorem ful_dl {σ σ' : OSt (List Nat)} {g : LkS} {h ts : Nat} {rc : Prop} (hok : LkOk img M σ g)
    (hful : fulO M h σ rc ts σ') (hnd : ¬ g.Dl ts) :
    ∀ t, g.Dl t → 1 ≤ t ∧ t ≤ σ'.n ∧ pend M σ' t ∧ wrL M t ∧ ¬ isAcq M t := by
  obtain ⟨_, hn1, _, _, _, hpr, _⟩ := ful_facts hok.pr hful
  intro t ht
  obtain ⟨u1, u2, u3, u4, u5⟩ := hok.dl t ht
  exact ⟨u1, by omega, (pend_iff hpr t).2 ⟨u3, fun e => by subst e; exact hnd ht⟩, u4, u5⟩

theorem ful_pr {σ σ' : OSt (List Nat)} {g : LkS} {h ts : Nat} {rc : Prop} (hok : LkOk img M σ g)
    (hful : fulO M h σ rc ts σ') : ∀ a t, t ∈ σ'.pr a → 1 ≤ t ∧ t ≤ σ'.n ∧ au M t = some a := by
  obtain ⟨_, hn1, _, _, _, hpr, _⟩ := ful_facts hok.pr hful
  intro a t ht
  obtain ⟨u1, u2, u3⟩ := hok.pr a t ((hpr a t).1 ht).1
  exact ⟨u1, by omega, u3⟩

/-- THE COUNTER CLAUSES across a fulfil of a message that writes no counter byte, with the holder possibly set
(on a free lock, at a new tenure starting at `ts`) and phases changed only from 0 at hart `h`. -/
theorem ful_cok {σ σ' : OSt (List Nat)} {g g' : LkS} {h ts : Nat} {rc : Prop} (hok : LkOk img M σ g)
    (hful : fulO M h σ rc ts σ') (hC : COk img M σ g) (hnX : ¬ wrX M ts) (hph : g.ph h = 0)
    (hDc : g'.Dc = g.Dc) (hmk : g'.mark = g.mark) (hph' : ∀ a, a ≠ h → g'.ph a = g.ph a)
    (hcr : g'.cr = g.cr ∨ (g.cr.hold = none ∧ ts = σ.n + 1 ∧ g'.cr = { g.cr with hold := some h, tstart := ts })) :
    COk img M σ' g' := by
  obtain ⟨_, hn1, hn2, htsn, _, hpr, hcase⟩ := ful_facts hok.pr hful
  have hts : g'.cr.tstar = g.cr.tstar ∧ g'.cr.v = g.cr.v := by
    rcases hcr with e | ⟨_, _, e⟩ <;> rw [e] <;> exact ⟨rfl, rfl⟩
  have hlo : ∀ a, g.ph a = 2 → g'.ph a = 2 := by
    intro a ha
    have : a ≠ h := fun e => by subst e; rw [hph] at ha; cases ha
    rw [hph' a this]; exact ha
  refine ⟨by rw [hts.1]; have := hC.tstar_le; omega, by rw [hts.1, hts.2]; exact hC.val, ?_,
    fun t h1 h2 h3 => ?_, fun t ht => ?_, fun t a ht h1 h2 => ?_⟩
  · rcases hcr with e | ⟨_, _, e⟩ <;> rw [e]
    · have := hC.tstart_le; omega
    · exact htsn
  · rw [hts.1] at h1
    have hne : t ≠ ts := fun e => by subst e; exact hnX h3
    have ht2 : t ≤ σ.n := by
      rcases hcase with ⟨_, e, _⟩ | ⟨e1, e2, _⟩
      · omega
      · omega
    rw [hDc]
    rcases hC.later t h1 ht2 h3 with u | ⟨u1, u2, u3⟩ | ⟨a, u1, u2, u3⟩
    · exact .inl u
    · rcases hcr with e | ⟨eh, _, e⟩
      · rw [e]; exact .inr (.inl ⟨u1, u2, (pend_iff hpr t).2 ⟨u3, hne⟩⟩)
      · rw [eh] at u1; obtain ⟨b, hb, _⟩ := u3; rw [hb] at u1; cases u1
    · exact .inr (.inr ⟨a, u1, (hpr a t).2 ⟨u2, hne⟩, hlo a u3⟩)
  · rw [hDc] at ht
    obtain ⟨u1, u2, u3, u4⟩ := hC.dc t ht
    exact ⟨u1, by omega, (pend_iff hpr t).2 ⟨u3, fun e => by subst e; exact hnX u4⟩, u4⟩
  · rw [hDc] at ht
    rw [hmk]
    rcases hcr with e | ⟨_, ets, e⟩
    · rw [e] at h1 ⊢; exact hC.dc_hold t a ht h1 h2
    · left; rw [e, ets]; have := (hC.dc t ht).2.1; simp only; omega

theorem ph3_upd {σ : OSt (List Nat)} {g : LkS} {h k : Nat} (hok : LkOk img M σ g) (hk : k ≠ 3) :
    ∀ a, upd g.ph h k a = 3 → g.spoil = true := by
  intro a ha
  by_cases e : a = h
  · subst e; rw [upd_eq] at ha; exact absurd ha hk
  · rw [upd_ne _ _ e] at ha; exact hok.ph3 a ha

/-! ### The AMO leaf -/

/-- **THE AMO LEAF** (plan §4 (b1)): the acquire AMO of hart `h` (phase 0) fulfils its acquire-shaped message `ts`,
its byte-0 answer is `t0` with value `b0`, and no other hart writes the lock byte in `(t0, ts)` (atomicity). -/
theorem lk_acq {σ σ' : OSt (List Nat)} {g : LkS} {h ts t0 : Nat} {rc : Prop} {b0 : BitVec 8}
    (hok : LkOk img M σ g) (hz : img Lw = some 0) (hph : g.ph h = 0)
    (hful : fulO M h σ rc ts σ') (hM : M[ts - 1]? = some (acqMsg h))
    (hmb : memByte img M t0 Lw = some b0) (ht0 : t0 < ts)
    (hwin : ∀ t, t0 < t → t < ts → wrL0 M t → au M t = some h) :
    (b0 ≠ 0 ∧ ∃ g', LkOk img M σ' g' ∧ g'.ph = upd g.ph h 0 ∧ g'.rds = g.rds ∧ g'.mark = g.mark ∧
        g'.spoil = g.spoil ∧ ((g'.ls = g.ls ∧ g'.cr = g.cr) ∨
          (g.spoil = false ∧ g.ls = .free ∧ ∃ u, g'.ls = .pulled h u))) ∨
    (b0 = 0 ∧ ∃ g', LkOk img M σ' g' ∧ g'.spoil = true ∧ g'.ph = upd g.ph h 3 ∧ g'.rds = g.rds ∧
        g'.mark = g.mark ∧ g'.cr = g.cr) ∨
    (b0 = 0 ∧ g.spoil = false ∧ ∃ u g', LkOk img M σ' g' ∧ g'.spoil = false ∧ g'.ls = .owned h u ∧
        g'.ph = upd g.ph h 1 ∧ g'.rds = g.rds ∧ g'.mark = g.mark ∧ u ≤ ts ∧ g'.cr.hold = some h ∧
        g'.cr.tstart = u ∧ g'.cr.tstar < u ∧ g'.cr.tstar = g.cr.tstar ∧ g'.cr.v = g.cr.v ∧
        ((g.ls = .pulled h u ∧ g'.cr = g.cr) ∨ (g.ls = .free ∧ g'.cr = { g.cr with hold := some h, tstart := u }))) := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  have hnA : ¬ g.Dl ts := fun hd => (hok.dl ts hd).2.2.2.2 ⟨h, hM⟩
  have hnX : ¬ wrX M ts := acq_not_wrX hM
  have hpr' := ful_pr hok hful
  have hdl' := ful_dl hok hful hnA
  have ht0n : t0 ≤ σ.n := by
    rcases hcase with ⟨h1, _, _⟩ | ⟨e, _, _⟩
    · have := (hok.pr h ts h1).2.1; omega
    · omega
  -- the new phase map and its basic facts
  have uph : ∀ (k : Nat) a, a ≠ h → upd g.ph h k a = g.ph a := fun k a e => upd_ne _ _ e
  -- THE ROGUE: a spoiled protocol, phase 3
  have rogue : ∀ (w : g.spoil = true ∨ ∃ t, g.Dl t), ∃ g', LkOk img M σ' g' ∧ g'.spoil = true ∧
      g'.ph = upd g.ph h 3 ∧ g'.rds = g.rds ∧ g'.mark = g.mark ∧ g'.cr = g.cr := by
    intro w
    have hw : ∃ t, g.Dl t := by
      rcases w with w | w
      · exact (hok.spoil w).2
      · exact w
    refine ⟨{ g with bad := true, spoil := true, ph := upd g.ph h 3 }, ⟨hpr', hdl', fun _ => .inl hw,
      fun _ => ⟨rfl, hw⟩, fun e => (by cases e), fun e => (by cases e), fun e => (by cases e),
      fun hh gg hg => .inl rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hb0 : b0 = 0
  · -- answer 0
    by_cases hsp : g.spoil = true
    · exact .inr (.inl ⟨hb0, rogue (.inl hsp)⟩)
    have hsp' : g.spoil = false := by simpa using hsp
    have hL := hok.lock hsp'
    have hC := hok.c hsp'
    by_cases hdead : 1 ≤ t0 ∧ g.Dl t0
    · exact .inr (.inl ⟨hb0, rogue (.inr ⟨t0, hdead.2⟩)⟩)
    have hnd : nd0 M g t0 := by
      by_cases e : t0 = 0
      · exact .inl e
      · have h1 : 1 ≤ t0 := by omega
        have hwr : wrL M t0 := wrL_of_memByte h1 hmb
        rcases hL.wrL_cls t0 h1 ht0n hwr with u | ⟨a, ha⟩ | ⟨u1, _⟩
        · exact absurd ⟨h1, u⟩ hdead
        · exfalso
          have : memByte img M t0 Lw = some 1 := by
            obtain ⟨k, rfl⟩ : ∃ k, t0 = k + 1 := ⟨t0 - 1, by omega⟩
            simp only [memByte]; simp only [Nat.add_sub_cancel] at ha; rw [ha]; exact acq_b0 a
          rw [hmb] at this; cases this; exact absurd hb0 (by decide)
        · exact .inr ⟨u1, fun hd => hdead ⟨h1, hd⟩⟩
    have hle := nd0_le hL ht0n hnd
    -- the taker: pulled for `h` (or a free lock, taken in place)
    have key : (∃ u, u ≤ ts ∧ g.ls = .pulled h u) ∨ (ts = σ.n + 1 ∧ g.ls = .free) := by
      rcases hcase with ⟨hts, _, _⟩ | ⟨ets, _, _, _⟩
      · exact .inl (hL.taker h ts hts hph hM t0 ht0 hnd hwin)
      · have hls := hL.ls_ok
        revert hls
        cases hg : g.ls with
        | free => exact fun _ => .inr ⟨ets, rfl⟩
        | pulled a u =>
          rintro ⟨⟨u1, u2, u3, _⟩, _⟩
          have := hwin u (by omega) (by omega) (acq_wrL0 u3)
          rw [au_acq u3] at this; cases this
          exact .inl ⟨u, by omega, rfl⟩
        | owned a u =>
          rintro ⟨⟨u1, u2, u3, _⟩, u7, _⟩
          have := hwin u (by omega) (by omega) (acq_wrL0 u3)
          rw [au_acq u3] at this; cases this
          rw [u7] at hph; cases hph
    right; right
    refine ⟨hb0, hsp', ?_⟩
    rcases key with ⟨u, hu, hpl⟩ | ⟨ets, hfree⟩
    · -- CONSUME THE PULL
      have hls := hL.ls_ok; rw [hpl] at hls
      obtain ⟨⟨k1, k2, k3, k4, k5, k6⟩, k7, k8⟩ := hls
      refine ⟨u, { g with ls := .owned h u, ph := upd g.ph h 1 }, ⟨hpr', hdl', hok.bad, hok.spoil, fun _ => ?_,
        fun _ => ful_cok hok hful hC hnX hph rfl rfl (uph 1) (.inl rfl), cnt_congr (g := g) rfl rfl rfl rfl hok.cnt,
        done_congr (g := g) hdone rfl rfl hok.done,
        ph3_upd hok (by decide), hok.mk_bad⟩, hsp', rfl, rfl, rfl, rfl, hu, k5, k6, k7, rfl, rfl,
        .inl ⟨hpl, rfl⟩⟩
      refine ⟨by show g.lc ≤ σ'.n; have := hL.lc_le; omega, hL.lc_ok, fun t h1 h2 h3 => ?_, fun t a h1 h2 h3 h4 => ?_, ?_,
        fun h' ts' hts' hph' hM' t0' ht0' hnd' hwin' => ?_⟩
      · by_cases e : t = σ.n + 1
        · rcases hcase with ⟨_, e2, _⟩ | ⟨e2, _, _⟩
          · omega
          · rw [e2] at hM; subst e; exact .inr (.inl ⟨h, hM⟩)
        · exact hL.wrL_cls t h1 (by omega) h3
      · by_cases e : t = ts
        · subst e; rw [hM] at h3; exact absurd (Option.some.inj h3) (acq_ne_rel h a)
        · have ht : t ≤ σ.n := by rcases hcase with ⟨_, e2, _⟩ | ⟨e2, _, _⟩ <;> omega
          have := hL.rel_ph t a h1 ht h3 h4
          have hah : a ≠ h := fun e => by subst e; rw [hph] at this; cases this
          show upd g.ph h 1 a = 2; rw [uph 1 a hah]; exact this
      · exact ⟨⟨k1, by omega, k3, k4, k5, k6⟩, by show upd g.ph h 1 h = 1; simp [upd],
          fun a hah => by show upd g.ph h 1 a ≠ 1; rw [uph 1 a hah]; exact k8 a⟩
      · exfalso
        have hh' : h' ≠ h := fun e => by subst e; change upd g.ph _ _ _ = 0 at hph'; simp [upd] at hph'
        have hph0 : g.ph h' = 0 := by rw [← uph 1 h' hh']; exact hph'
        obtain ⟨u', _, hu'⟩ := hL.taker h' ts' ((hpr h' ts').1 hts').1 hph0 hM' t0' ht0' hnd' hwin'
        rw [hpl] at hu'; cases hu'; exact hh' rfl
    · -- A FREE LOCK, TAKEN IN PLACE
      subst ets
      have hls := hL.ls_ok; rw [hfree] at hls
      obtain ⟨f1, f2, f3, f4⟩ := hls
      have hn' : σ'.n = σ.n + 1 := by rcases hcase with ⟨_, e2, _⟩ | ⟨_, e2, _⟩ <;> omega
      let g' : LkS := { g with ls := .owned h (σ.n + 1), ph := upd g.ph h 1, cr := { g.cr with hold := some h, tstart := σ.n + 1 } }
      refine ⟨σ.n + 1, g',
        ⟨hpr', hdl', hok.bad, hok.spoil, fun _ => ?_,
        fun _ => ful_cok hok hful hC hnX hph rfl rfl (uph 1) (.inr ⟨f2, rfl, rfl⟩),
        cnt_congr (g := g) rfl rfl rfl rfl hok.cnt, done_congr (g := g) hdone rfl rfl hok.done,
        ph3_upd hok (by decide), hok.mk_bad⟩,
        hsp', rfl, rfl, rfl, rfl, Nat.le_refl _, rfl, rfl, by show g.cr.tstar < σ.n + 1; have := hL.lc_le; omega,
        rfl, rfl, .inr ⟨hfree, rfl⟩⟩
      refine ⟨by show g.lc ≤ σ'.n; have := hL.lc_le; omega, hL.lc_ok, fun t h1 h2 h3 => ?_, fun t a h1 h2 h3 h4 => ?_, ?_,
        fun h' ts' hts' hph' hM' t0' ht0' hnd' hwin' => ?_⟩
      · by_cases e : t = σ.n + 1
        · subst e; exact .inr (.inl ⟨h, hM⟩)
        · exact hL.wrL_cls t h1 (by omega) h3
      · by_cases e : t = σ.n + 1
        · subst e; rw [hM] at h3; exact absurd (Option.some.inj h3) (acq_ne_rel h a)
        · have := hL.rel_ph t a h1 (by omega) h3 h4
          have hah : a ≠ h := fun e => by subst e; rw [hph] at this; cases this
          show upd g.ph h 1 a = 2; rw [uph 1 a hah]; exact this
      · refine ⟨⟨by show g.lc < σ.n + 1; have := hL.lc_le; omega, by omega, hM, fun t h1 h2 h3 => f1 t h1 (by omega) h3,
          rfl, rfl⟩, by show upd g.ph h 1 h = 1; simp [upd], fun a hah => by show upd g.ph h 1 a ≠ 1; rw [uph 1 a hah]; exact f4 a⟩
      · exfalso
        have hh' : h' ≠ h := fun e => by subst e; change upd g.ph _ _ _ = 0 at hph'; simp [upd] at hph'
        have hph0 : g.ph h' = 0 := by rw [← uph 1 h' hh']; exact hph'
        obtain ⟨u', _, hu'⟩ := hL.taker h' ts' ((hpr h' ts').1 hts').1 hph0 hM' t0' ht0' hnd' hwin'
        rw [hfree] at hu'; cases hu'
  · -- a nonzero answer: RETRY (phase stays 0: the spin loop)
    left
    refine ⟨hb0, ?_⟩
    by_cases hpf : ts = σ.n + 1 ∧ g.spoil = false ∧ g.ls = .free
    · obtain ⟨ets, hsp', hfree⟩ := hpf
      subst ets
      have hL := hok.lock hsp'
      have hC := hok.c hsp'
      have hls := hL.ls_ok; rw [hfree] at hls
      obtain ⟨f1, f2, f3, f4⟩ := hls
      let g' : LkS := { g with ls := .pulled h (σ.n + 1), ph := upd g.ph h 0, cr := { g.cr with hold := some h, tstart := σ.n + 1 } }
      refine ⟨g',
        ⟨hpr', hdl', hok.bad, hok.spoil, fun _ => ?_,
        fun _ => ful_cok hok hful hC hnX hph rfl rfl (uph 0) (.inr ⟨f2, rfl, rfl⟩),
        cnt_congr (g := g) rfl rfl rfl rfl hok.cnt, done_congr (g := g) hdone rfl rfl hok.done,
        ph3_upd hok (by decide), hok.mk_bad⟩,
        rfl, rfl, rfl, rfl, .inr ⟨hsp', hfree, _, rfl⟩⟩
      refine ⟨by show g.lc ≤ σ'.n; have := hL.lc_le; omega, hL.lc_ok, fun t h1 h2 h3 => ?_, fun t a h1 h2 h3 h4 => ?_, ?_,
        fun h' ts' hts' hph' hM' t0' ht0' hnd' hwin' => ?_⟩
      · by_cases e : t = σ.n + 1
        · subst e; exact .inr (.inl ⟨h, hM⟩)
        · exact hL.wrL_cls t h1 (by omega) h3
      · by_cases e : t = σ.n + 1
        · subst e; rw [hM] at h3; exact absurd (Option.some.inj h3) (acq_ne_rel h a)
        · have := hL.rel_ph t a h1 (by omega) h3 h4
          have hah : a ≠ h := fun e => by subst e; rw [hph] at this; cases this
          show upd g.ph h 0 a = 2; rw [uph 0 a hah]; exact this
      · refine ⟨⟨by show g.lc < σ.n + 1; have := hL.lc_le; omega, by omega, hM, fun t h1 h2 h3 => f1 t h1 (by omega) h3,
          rfl, rfl⟩, by show g.cr.tstar < σ.n + 1; have := hL.lc_le; omega, fun a => ?_⟩
        by_cases hah : a = h
        · subst hah; show upd g.ph _ 0 _ ≠ 1; simp [upd]
        · show upd g.ph h 0 a ≠ 1; rw [uph 0 a hah]; exact f4 a
      · exfalso
        have hph0 : g.ph h' = 0 := by
          by_cases e : h' = h
          · subst e; exact hph
          · rw [← uph 0 h' e]; exact hph'
        obtain ⟨u', _, hu'⟩ := hL.taker h' ts' ((hpr h' ts').1 hts').1 hph0 hM' t0' ht0' hnd' hwin'
        rw [hfree] at hu'; cases hu'
    · refine ⟨{ g with ph := upd g.ph h 0 }, ⟨hpr', hdl', hok.bad, hok.spoil, fun hsp' => ?_,
        fun hsp' => ful_cok hok hful (hok.c hsp') hnX hph rfl rfl (uph 0) (.inl rfl),
        cnt_congr (g := g) rfl rfl rfl rfl hok.cnt, done_congr (g := g) hdone rfl rfl hok.done,
        ph3_upd hok (by decide), hok.mk_bad⟩,
        rfl, rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
      have hL := hok.lock hsp'
      refine ⟨by show g.lc ≤ σ'.n; have := hL.lc_le; omega, hL.lc_ok, fun t h1 h2 h3 => ?_, fun t a h1 h2 h3 h4 => ?_, ?_,
        fun h' ts' hts' hph' hM' t0' ht0' hnd' hwin' => ?_⟩
      · by_cases e : t = σ.n + 1
        · rcases hcase with ⟨_, e2, _⟩ | ⟨e2, _, _⟩
          · omega
          · rw [e2] at hM; subst e; exact .inr (.inl ⟨h, hM⟩)
        · exact hL.wrL_cls t h1 (by omega) h3
      · by_cases e : t = ts
        · subst e; rw [hM] at h3; exact absurd (Option.some.inj h3) (acq_ne_rel h a)
        · have ht : t ≤ σ.n := by rcases hcase with ⟨_, e2, _⟩ | ⟨e2, _, _⟩ <;> omega
          have := hL.rel_ph t a h1 ht h3 h4
          have hah : a ≠ h := fun e => by subst e; rw [hph] at this; cases this
          show upd g.ph h 0 a = 2; rw [uph 0 a hah]; exact this
      · have hls := hL.ls_ok
        revert hls
        cases hg : g.ls with
        | free =>
          rintro ⟨f1, f2, f3, f4⟩
          have hn' : σ'.n = σ.n := by
            rcases hcase with ⟨_, e2, _⟩ | ⟨e2, e3, _⟩
            · exact e2
            · exact absurd ⟨e2, hsp', hg⟩ hpf
          refine ⟨fun t h1 h2 h3 => f1 t h1 (by omega) h3, f2, f3, fun a => ?_⟩
          by_cases hah : a = h
          · subst hah; show upd g.ph _ 0 _ ≠ 1; simp [upd]
          · show upd g.ph h 0 a ≠ 1; rw [uph 0 a hah]; exact f4 a
        | pulled a u =>
          rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
          refine ⟨⟨u1, by omega, u3, u4, u5, u6⟩, u7, fun b => ?_⟩
          by_cases hbh : b = h
          · subst hbh; show upd g.ph _ 0 _ ≠ 1; simp [upd]
          · show upd g.ph h 0 b ≠ 1; rw [uph 0 b hbh]; exact u8 b
        | owned a u =>
          rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
          have hah : a ≠ h := fun e => by subst e; rw [hph] at u7; cases u7
          refine ⟨⟨u1, by omega, u3, u4, u5, u6⟩, by show upd g.ph h 0 a = 1; rw [uph 0 a hah]; exact u7,
            fun b hb => ?_⟩
          by_cases hbh : b = h
          · subst hbh; show upd g.ph _ 0 _ ≠ 1; simp [upd]
          · show upd g.ph h 0 b ≠ 1; rw [uph 0 b hbh]; exact u8 b hb
      · have hph0 : g.ph h' = 0 := by
          by_cases e : h' = h
          · subst e; exact hph
          · rw [← uph 0 h' e]; exact hph'
        exact hL.taker h' ts' ((hpr h' ts').1 hts').1 hph0 hM' t0' ht0' hnd' hwin'

end steps


section steps2

variable {img : Image} {M : List PMsg}

theorem specH_mono {gg : List Nat} {g g' : LkS} {h : Nat} (hr : ∀ a v, g.rds a = some v → g'.rds a = some v)
    (hb : g.bad = true → g'.bad = true) (hs : specH gg g h) : specH gg g' h := by
  rcases hs with u | ⟨v, u1, u2⟩
  · exact .inl (hb u)
  · exact .inr ⟨v, hr h v u1, u2⟩

/-- The LOCK clauses across a fulfil of a counter message (no lock byte written; lock fields unchanged). -/
theorem ful_lock_c {σ σ' : OSt (List Nat)} {g g' : LkS} {h ts : Nat} {rc : Prop} (hok : LkOk img M σ g)
    (hful : fulO M h σ rc ts σ') (hL : LockOk M σ g) (hnL : ¬ wrL M ts) (hnA : ¬ isAcq M ts)
    (e1 : g'.Dl = g.Dl) (e2 : g'.lc = g.lc) (e3 : g'.ls = g.ls) (e4 : g'.ph = g.ph)
    (e5 : g'.cr.hold = g.cr.hold) (e6 : g'.cr.tstart = g.cr.tstart)
    (e7 : g.ls = .free → g'.cr.tstar ≤ g.lc) (e8 : ∀ a u, g.ls = .pulled a u → g'.cr.tstar < u) :
    LockOk M σ' g' := by
  obtain ⟨_, hn1, hn2, htsn, _, hpr, hcase⟩ := ful_facts hok.pr hful
  have hnd : ∀ t0, nd0 M g' t0 → nd0 M g t0 := by
    rintro t0 (h0 | ⟨h1, h2⟩); exact .inl h0; exact .inr ⟨h1, by rw [← e1]; exact h2⟩
  refine ⟨by rw [e2]; have := hL.lc_le; omega, by rw [e2, e1]; exact hL.lc_ok, fun t h1 h2 h3 => ?_,
    fun t a h1 h2 h3 h4 => ?_, ?_, fun h' ts' hts' hph' hM' t0 ht0 hnd' hwin => ?_⟩
  · have hne : t ≠ ts := fun e => by subst e; exact hnL h3
    have ht : t ≤ σ.n := by rcases hcase with ⟨_, e, _⟩ | ⟨e, _, _⟩ <;> omega
    rw [e1, e2]; exact hL.wrL_cls t h1 ht h3
  · have hne : t ≠ ts := fun e => by subst e; exact hnL (rel_wrL h3)
    have ht : t ≤ σ.n := by rcases hcase with ⟨_, e, _⟩ | ⟨e, _, _⟩ <;> omega
    rw [e4]; exact hL.rel_ph t a h1 ht h3 (by rw [← e1]; exact h4)
  · have hls := hL.ls_ok
    rw [e3]
    revert hls
    cases hg : g.ls with
    | free =>
      rintro ⟨f1, f2, f3, f4⟩
      refine ⟨fun t h1 h2 h3 => ?_, by rw [e5]; exact f2, by rw [e2]; exact e7 hg, by rw [e4]; exact f4⟩
      have hne : t ≠ ts := fun e => by subst e; exact hnL h3
      have ht : t ≤ σ.n := by rcases hcase with ⟨_, e, _⟩ | ⟨e, _, _⟩ <;> omega
      rw [e1]; exact f1 t (by rw [← e2]; exact h1) ht h3
    | pulled a u =>
      rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
      exact ⟨⟨by rw [e2]; exact u1, by omega, u3, by rw [e1, e2]; exact u4, by rw [e5]; exact u5, by rw [e6]; exact u6⟩,
        e8 a u hg, by rw [e4]; exact u8⟩
    | owned a u =>
      rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
      exact ⟨⟨by rw [e2]; exact u1, by omega, u3, by rw [e1, e2]; exact u4, by rw [e5]; exact u5, by rw [e6]; exact u6⟩,
        by rw [e4]; exact u7, by rw [e4]; exact u8⟩
  · rw [e3]
    exact hL.taker h' ts' ((hpr h' ts').1 hts').1 (by rw [← e4]; exact hph') hM' t0 ht0 (hnd t0 hnd') hwin

/-- The lock clauses depend only on the lock fields. -/
theorem lockOk_congr {σ : OSt (List Nat)} {g g' : LkS} (e1 : g'.Dl = g.Dl) (e2 : g'.lc = g.lc)
    (e3 : g'.ls = g.ls) (e4 : g'.ph = g.ph) (e5 : g'.cr.hold = g.cr.hold) (e6 : g'.cr.tstart = g.cr.tstart)
    (e7 : g'.cr.tstar = g.cr.tstar) (h : LockOk M σ g) : LockOk M σ g' := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := h
  have hnd : ∀ t0, nd0 M g' t0 → nd0 M g t0 := by
    rintro t0 (h0 | ⟨h1, h2⟩); exact .inl h0; exact .inr ⟨h1, by rw [← e1]; exact h2⟩
  refine ⟨by rw [e2]; exact l1, by rw [e2, e1]; exact l2, fun t a b c => by rw [e1, e2]; exact l3 t a b c,
    fun t a b c d e => by rw [e4]; exact l4 t a b c d (by rw [← e1]; exact e), ?_,
    fun h ts a b c t0 d f k => by rw [e3]; exact l6 h ts a (by rw [← e4]; exact b) c t0 d (hnd t0 f) k⟩
  rw [e3]
  revert l5
  cases hg : g.ls with
  | free =>
    rintro ⟨f1, f2, f3, f4⟩
    exact ⟨fun t a b c => by rw [e1]; exact f1 t (by rw [← e2]; exact a) b c, by rw [e5]; exact f2,
      by rw [e7, e2]; exact f3, by rw [e4]; exact f4⟩
  | pulled a u =>
    rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
    exact ⟨⟨by rw [e2]; exact u1, u2, u3, fun t a b c => by rw [e1]; exact u4 t (by rw [← e2]; exact a) b c,
      by rw [e5]; exact u5, by rw [e6]; exact u6⟩, by rw [e7]; exact u7, by rw [e4]; exact u8⟩
  | owned a u =>
    rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
    exact ⟨⟨by rw [e2]; exact u1, u2, u3, fun t a b c => by rw [e1]; exact u4 t (by rw [← e2]; exact a) b c,
      by rw [e5]; exact u5, by rw [e6]; exact u6⟩, by rw [e4]; exact u7, by rw [e4]; exact u8⟩

/-- **THE HOLDER'S READ OF THE COUNTER**: every byte is the latest message's (value `cr.v`), or some byte is a later,
pending counter message, which is marked dead (`bad`). -/
theorem lk_ldc {σ : OSt (List Nat)} {g : LkS} {h u P : Nat} {tvs : List (Nat × BitVec 8)}
    (hok : LkOk img M σ g) (hsp : g.spoil = false) (hown : g.ls = .owned h u) (hmk : g.mark h = none)
    (hP : g.cr.tstar ≤ P) (hlen : tvs.length = 8)
    (hby : ∀ (j : Nat) t b, tvs[j]? = some (t, b) →
      memByte img M t (C + j) = some b ∧ t ≤ σ.n ∧ ¬ writesIn (M.take σ.n) (C + j) t P) :
    tvs.map Prod.snd = toBytes g.cr.v 8 ∨
    ∃ j t b, j < 8 ∧ tvs[j]? = some (t, b) ∧ ∃ g', LkOk img M σ g' ∧ g'.bad = true ∧ g'.spoil = false ∧
      g'.ls = g.ls ∧ g'.cr = g.cr ∧ g'.ph = g.ph ∧ g'.rds = g.rds ∧ g'.mark = upd g.mark h (some t) := by
  have hC := hok.c hsp
  have hL := hok.lock hsp
  have hhold : g.cr.hold = some h := by
    have hls := hL.ls_ok; rw [hown] at hls; exact hls.1.2.2.2.2.1
  by_cases hex : ∃ j t b, j < 8 ∧ tvs[j]? = some (t, b) ∧ (toBytes g.cr.v 8)[j]? ≠ some b
  · right
    obtain ⟨j, t, b, hj, htb, hne⟩ := hex
    obtain ⟨hmb, htn, hnw⟩ := hby j t b htb
    obtain ⟨b', hb'⟩ := toBytes_get g.cr.v j hj
    have hval := hC.val j hj
    rw [hb'] at hval
    -- the answer is above the latest message
    have hgt : g.cr.tstar < t := by
      rcases Nat.lt_trichotomy t g.cr.tstar with hlt | heq | hgt
      · exfalso; apply hnw
        have hwr : wrA M g.cr.tstar (C + j) := wrA_of_memByte (by omega) hval
        obtain ⟨m, hm, hb⟩ := hwr
        exact ⟨g.cr.tstar, hlt, hP, m, by rw [List.getElem?_take, if_pos (by have := hC.tstar_le; omega)]; exact hm, hb⟩
      · subst heq; rw [memByte_inj hmb hval] at hne; exact absurd hb' hne
      · exact hgt
    have hwx : wrX M t := ⟨j, hj, wrA_of_memByte (by omega) hmb⟩
    refine ⟨j, t, b, hj, htb, ?_⟩
    by_cases hbad : g.bad = true
    · refine ⟨{ g with mark := upd g.mark h (some t) }, ⟨hok.pr, hok.dl, hok.bad, hok.spoil,
        fun _ => lockOk_congr (g := g) rfl rfl rfl rfl rfl rfl rfl hL, fun _ => ?_, fun e => (by rw [hbad] at e; cases e),
        fun hh gg hg => .inl hbad, hok.ph3, fun _ _ _ => hbad⟩, hbad, hsp, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨hC.tstar_le, hC.val, hC.tstart_le, hC.later, hC.dc, fun x a hx h1 h2 => ?_⟩
      rcases hC.dc_hold x a hx h1 h2 with v | v | v
      · exact .inl v
      · change g.cr.hold = some a at h1; rw [hhold] at h1; cases h1; rw [hmk] at v; cases v
      · exact .inr (.inr v)
    have hbad' : g.bad = false := by simpa using hbad
    have hpt : pend M σ t := by
      rcases hC.later t hgt htn hwx with u1 | ⟨_, _, u3⟩ | ⟨a, u1, u2, _⟩
      · exact (hC.dc t u1).2.2.1
      · exact u3
      · exact ⟨a, u1, u2⟩
    let g' : LkS := { g with bad := true, Dc := fun x => g.Dc x ∨ x = t, mark := upd g.mark h (some t) }
    refine ⟨g', ⟨hok.pr, hok.dl, fun _ => .inr ⟨hsp, t, .inr rfl⟩, fun e => (by rw [hsp] at e; cases e),
      fun _ => lockOk_congr (g := g) rfl rfl rfl rfl rfl rfl rfl hL, fun _ => ?_, fun e => (by cases e),
      fun hh gg hg => .inl rfl, hok.ph3, fun _ _ _ => rfl⟩,
      rfl, hsp, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨hC.tstar_le, hC.val, hC.tstart_le, fun x h1 h2 h3 => ?_, fun x hx => ?_, fun x a hx h1 h2 => ?_⟩
    · rcases hC.later x h1 h2 h3 with v | v | v
      · exact .inl (.inl v)
      · exact .inr (.inl v)
      · exact .inr (.inr v)
    · rcases hx with hx | rfl
      · exact hC.dc x hx
      · exact ⟨by omega, htn, hpt, hwx⟩
    · change g.cr.hold = some a at h1
      rw [hhold] at h1; cases h1
      rcases hx with hx | rfl
      · rcases hC.dc_hold x h hx hhold h2 with v | v | v
        · exact .inl v
        · rw [hmk] at v; cases v
        · exact .inr (.inr v)
      · exact .inr (.inl (by show upd g.mark h (some x) h = some x; simp [upd]))
  · left
    refine map_snd_of (by rw [hlen]; rfl) (fun j hj t b htb => Classical.byContradiction fun hne => hex
      ⟨j, t, b, by simpa [toBytes, Weak.Prom.Ref.byteList] using hj, htb, hne⟩)

/-- **THE HOLDER'S STORE TO THE COUNTER** (a backed promise of its tenure, or in place): its message becomes the
counter's latest; with no `bad`, it records the hart's read value (the counter's value before). -/
theorem lk_sdc {σ σ' : OSt (List Nat)} {g : LkS} {h u ts v : Nat} {rc : Prop}
    (hok : LkOk img M σ g) (hh2 : h < 2) (hsp : g.spoil = false) (hown : g.ls = .owned h u)
    (hful : fulO M h σ rc ts σ') (hM : M[ts - 1]? = some (cMsg h v)) (hut : u < ts) (htst : g.cr.tstar < ts)
    (hmk : ∀ m, g.mark h = some m → m < ts)
    (hrd : g.bad = false → v = (g.cr.v % two64 + 1) % two64 ∧ g.rds h = none) :
    ∃ g', LkOk img M σ' g' ∧ g'.spoil = false ∧ g'.ls = g.ls ∧ g'.ph = g.ph ∧ g'.mark = g.mark ∧
      g'.cr = { g.cr with tstar := ts, v := v } ∧ g'.bad = g.bad ∧
      (g.bad = false → g'.rds = upd g.rds h (some g.cr.v)) ∧ (g.bad = true → g'.rds = g.rds) := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  have hC := hok.c hsp
  have hL := hok.lock hsp
  have hls := hL.ls_ok; rw [hown] at hls
  obtain ⟨⟨k1, k2, k3, k4, k5, k6⟩, k7, k8⟩ := hls
  have hnL : ¬ wrL M ts := c_not_wrL hM
  have hnA : ¬ isAcq M ts := c_not_acq hM
  have hnDl : ¬ g.Dl ts := fun hd => hnL (hok.dl ts hd).2.2.2.1
  have hnDc : ¬ g.Dc ts := by
    intro hd
    have hau : au M ts = some h := by simp [au, hM, cMsg]
    rcases hC.dc_hold ts h hd k5 hau with v1 | v1 | v1
    · rw [k6] at v1; omega
    · have := hmk ts v1; omega
    · exact hnL v1
  have hlock : LockOk M σ' { g with cr := { g.cr with tstar := ts, v := v } } :=
    ful_lock_c (g := g) hok hful hL hnL hnA rfl rfl rfl rfl rfl rfl
      (fun e => by rw [hown] at e; cases e) (fun a u e => by rw [hown] at e; cases e)
  -- the counter clauses for any record whose latest message is `ts` with value `v`
  have hcok : ∀ g' : LkS, g'.cr = { g.cr with tstar := ts, v := v } → g'.Dc = g.Dc → g'.mark = g.mark →
      g'.ph = g.ph → COk img M σ' g' := by
    intro g' ecr eDc emk eph
    refine ⟨by rw [ecr]; exact htsn, ?_, by rw [ecr]; show g.cr.tstart ≤ σ'.n; have := hC.tstart_le; omega,
      fun t h1 h2 h3 => ?_,
      fun t ht => ?_, fun t a ht h1 h2 => ?_⟩
    · rw [ecr]; intro j hj
      obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hM
      simp only [memByte, hM, Option.bind_some]; exact cMsg_byte h v j hj
    · rw [ecr] at h1; simp only at h1
      have ht : t ≤ σ.n := by rcases hcase with ⟨_, e, _⟩ | ⟨e, _, _⟩ <;> omega
      rw [eDc, ecr, eph]
      rcases hC.later t (by omega) ht h3 with w | ⟨w1, w2, w3⟩ | ⟨a, w1, w2, w3⟩
      · exact .inl w
      · exact .inr (.inl ⟨w1, w2, (pend_iff hpr t).2 ⟨w3, by omega⟩⟩)
      · exact .inr (.inr ⟨a, w1, (hpr a t).2 ⟨w2, by omega⟩, w3⟩)
    · rw [eDc] at ht
      obtain ⟨w1, w2, w3, w4⟩ := hC.dc t ht
      exact ⟨w1, by omega, (pend_iff hpr t).2 ⟨w3, fun e => by subst e; exact hnDc ht⟩, w4⟩
    · rw [eDc] at ht; rw [ecr] at h1 ⊢; rw [emk]; exact hC.dc_hold t a ht h1 h2
  by_cases hbad : g.bad = true
  · refine ⟨{ g with cr := { g.cr with tstar := ts, v := v } }, ⟨ful_pr hok hful, ful_dl (g := g) hok hful hnDl,
      fun hb => hok.bad hb, fun e => (by rw [hsp] at e; cases e), fun _ => hlock, fun _ => hcok _ rfl rfl rfl rfl,
      fun e => (by change g.bad = false at e; rw [hbad] at e; cases e), fun hh gg hg => .inl hbad, hok.ph3, hok.mk_bad⟩,
      hsp, rfl, rfl, rfl, rfl, rfl, fun e => (by rw [hbad] at e; cases e), fun _ => rfl⟩
  · have hbad' : g.bad = false := by simpa using hbad
    obtain ⟨hv, hrn⟩ := hrd hbad'
    have hcnt := hok.cnt hbad'
    have hc2 : g.cnt ≤ 2 := by
      have := hcnt.cnt_def; split at this <;> split at this <;> omega
    have hv' : v = g.cr.v + 1 := by
      rw [hv, hcnt.v_cnt]; simp only [two64]; omega
    let g' : LkS := { g with cr := { g.cr with tstar := ts, v := v }, cnt := g.cnt + 1, rds := upd g.rds h (some g.cr.v) }
    refine ⟨g', ⟨ful_pr hok hful, ful_dl (g := g) hok hful hnDl, fun e => (by change g.bad = true at e; rw [hbad'] at e; cases e),
      fun e => (by change g.spoil = true at e; rw [hsp] at e; cases e),
      fun _ => lockOk_congr (g := { g with cr := { g.cr with tstar := ts, v := v } }) rfl rfl rfl rfl rfl rfl rfl hlock,
      fun _ => hcok g' rfl rfl rfl rfl, fun _ => ?_, fun hh gg hg => ?_, hok.ph3, hok.mk_bad⟩, hsp, rfl, rfl, rfl, rfl, rfl,
      fun _ => rfl, fun e => (by rw [hbad'] at e; cases e)⟩
    · refine ⟨by show v = g.cnt + 1; rw [hv', hcnt.v_cnt], fun a w hw => ?_, fun a b w hab ha hb => ?_, ?_,
        fun a ha => ?_⟩
      · change upd g.rds h (some g.cr.v) a = some w at hw
        show w < g.cnt + 1
        by_cases e : a = h
        · subst e; simp [upd] at hw; rw [← hw, hcnt.v_cnt]; omega
        · rw [upd_ne _ _ e] at hw; have := hcnt.rds_lt a w hw; omega
      · change upd g.rds h (some g.cr.v) a = some w at ha
        change upd g.rds h (some g.cr.v) b = some w at hb
        by_cases ea : a = h
        · subst ea
          rw [upd_ne _ _ (Ne.symm hab)] at hb; simp [upd] at ha
          have := hcnt.rds_lt b w hb; rw [← ha, hcnt.v_cnt] at this; omega
        · by_cases eb : b = h
          · subst eb
            rw [upd_ne _ _ hab] at ha; simp [upd] at hb
            have := hcnt.rds_lt a w ha; rw [← hb, hcnt.v_cnt] at this; omega
          · rw [upd_ne _ _ ea] at ha; rw [upd_ne _ _ eb] at hb
            exact hcnt.rds_inj a b w hab ha hb
      · show g.cnt + 1 = (if (upd g.rds h (some g.cr.v) 0).isSome then 1 else 0) +
          (if (upd g.rds h (some g.cr.v) 1).isSome then 1 else 0)
        have hd := hcnt.cnt_def
        rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
        · simp only [upd_eq, upd_ne _ _ (show (1 : Nat) ≠ 0 by omega), Option.isSome_some, if_true]
          rw [hrn] at hd
          simp only [Option.isSome_none, Bool.false_eq_true, if_false, Nat.zero_add] at hd
          rw [hd]; by_cases hc : (g.rds 1).isSome = true <;> simp [hc]
        · simp only [upd_eq, upd_ne _ _ (show (0 : Nat) ≠ 1 by omega), Option.isSome_some, if_true]
          rw [hrn] at hd
          simp only [Option.isSome_none, Bool.false_eq_true, if_false, Nat.add_zero] at hd
          rw [hd]
      · show upd g.rds h (some g.cr.v) a = none
        rw [upd_ne _ _ (by omega)]; exact hcnt.rds_hi a ha
    · rw [hdone] at hg
      refine specH_mono (g := g) (fun a w hw => ?_) (fun e => e) (hok.done hh gg hg)
      show upd g.rds h (some g.cr.v) a = some w
      by_cases e : a = h
      · subst e; rw [hrn] at hw; cases hw
      · rw [upd_ne _ _ e]; exact hw

/-- A store to the counter in SPOILED mode (only the dead lock messages matter). -/
theorem lk_sdcS {σ σ' : OSt (List Nat)} {g : LkS} {h ts v : Nat} {rc : Prop}
    (hok : LkOk img M σ g) (hsp : g.spoil = true) (hful : fulO M h σ rc ts σ') (hM : M[ts - 1]? = some (cMsg h v)) :
    LkOk img M σ' g := by
  obtain ⟨hdone, _, _, _, _, _, _⟩ := ful_facts hok.pr hful
  have hnDl : ¬ g.Dl ts := fun hd => c_not_wrL hM (hok.dl ts hd).2.2.2.1
  exact ⟨ful_pr hok hful, ful_dl (g := g) hok hful hnDl, hok.bad, hok.spoil, fun e => (by rw [hsp] at e; cases e),
    fun e => (by rw [hsp] at e; cases e), hok.cnt, fun hh gg hg => hok.done hh gg (by rw [← hdone]; exact hg),
    hok.ph3, hok.mk_bad⟩

/-- The protocol state after the release of `h` at `ts`. -/
def relG (g : LkS) (h ts : Nat) : LkS := { g with lc := ts, ls := .free, cr := { g.cr with hold := none, tstart := ts }, ph := upd g.ph h 2 }

/-- **THE RELEASE** (`amoswap.w.rl x0,x0`, always release-class, so in place): R is DEPOSITED into the new live cell
`ts`; the holder's pending counter promises become leftovers (phase 2). -/
theorem lk_rel {σ σ' : OSt (List Nat)} {g : LkS} {h u ts : Nat} {rc : Prop}
    (hok : LkOk img M σ g) (hsp : g.spoil = false) (hown : g.ls = .owned h u) (hrc : rc)
    (hful : fulO M h σ rc ts σ') (hM : M[ts - 1]? = some (relMsg h)) :
    LkOk img M σ' (relG g h ts) := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  obtain ⟨ets, hn', _, _⟩ : ts = σ.n + 1 ∧ σ'.n = σ.n + 1 ∧ rc ∧ au M ts = some h := by
    rcases hcase with ⟨_, _, hnr⟩ | h4
    · exact absurd hrc hnr
    · exact h4
  have hC := hok.c hsp
  have hL := hok.lock hsp
  have hls := hL.ls_ok; rw [hown] at hls
  obtain ⟨⟨k1, k2, k3, k4, k5, k6⟩, k7, k8⟩ := hls
  have hnDl : ¬ g.Dl ts := fun hd => by have := (hok.dl ts hd).2.1; omega
  have hnX : ¬ wrX M ts := rel_not_wrX hM
  have uph : ∀ a, a ≠ h → upd g.ph h 2 a = g.ph a := fun a e => upd_ne _ _ e
  refine ⟨ful_pr hok hful, ful_dl (g := g) hok hful hnDl, fun hb => hok.bad hb, fun hs => hok.spoil hs,
    fun _ => ?_, fun _ => ?_, cnt_congr (g := g) rfl rfl rfl rfl hok.cnt, done_congr (g := g) hdone rfl rfl hok.done,
    ph3_upd hok (by decide), hok.mk_bad⟩
  · refine ⟨by show ts ≤ σ'.n; omega, .inr ⟨⟨h, hM⟩, hnDl⟩, fun t h1 h2 h3 => ?_, fun t a h1 h2 h3 h4 => ?_, ?_,
      fun h' ts' hts' hph' hM' t0 ht0 hnd hwin => ?_⟩
    · by_cases e : t = ts
      · subst e; exact .inr (.inr ⟨⟨h, hM⟩, Nat.le_refl _⟩)
      · rcases hL.wrL_cls t h1 (by omega) h3 with w | w | ⟨w1, w2⟩
        · exact .inl w
        · exact .inr (.inl w)
        · exact .inr (.inr ⟨w1, by show t ≤ ts; have := hL.lc_le; omega⟩)
    · show upd g.ph h 2 a = 2
      by_cases e : t = ts
      · subst e; rw [hM] at h3; cases h3; simp [upd]
      · have := hL.rel_ph t a h1 (by omega) h3 h4
        have hah : a ≠ h := fun e => by subst e; rw [k7] at this; cases this
        rw [uph a hah]; exact this
    · refine ⟨fun t h1 h2 _ => by change ts < t at h1; omega, rfl, by show g.cr.tstar ≤ ts; have := hC.tstar_le; omega,
        fun a => ?_⟩
      show upd g.ph h 2 a ≠ 1
      by_cases hah : a = h
      · subst hah; simp [upd]
      · rw [uph a hah]; exact k8 a hah
    · exfalso
      have hh' : h' ≠ h := fun e => by subst e; change upd g.ph _ _ _ = 0 at hph'; simp [upd] at hph'
      have hph0 : g.ph h' = 0 := by rw [← uph h' hh']; exact hph'
      obtain ⟨u', _, hu'⟩ := hL.taker h' ts' ((hpr h' ts').1 hts').1 hph0 hM' t0 ht0 hnd hwin
      rw [hown] at hu'; cases hu'
  · refine ⟨by show g.cr.tstar ≤ σ'.n; have := hC.tstar_le; omega, hC.val, by show ts ≤ σ'.n; omega,
      fun t h1 h2 h3 => ?_, fun t ht => ?_, fun t a ht h1 h2 => ?_⟩
    · have hne : t ≠ ts := fun e => by subst e; exact hnX h3
      rcases hC.later t h1 (by omega) h3 with w | ⟨w1, w2, ⟨b, w3, w4⟩⟩ | ⟨a, w1, w2, w3⟩
      · exact .inl w
      · rw [k5] at w1; rw [w3] at w1; cases w1
        exact .inr (.inr ⟨h, w3, (hpr h t).2 ⟨w4, hne⟩, by show upd g.ph h 2 h = 2; simp [upd]⟩)
      · have hah : a ≠ h := fun e => by subst e; rw [k7] at w3; cases w3
        exact .inr (.inr ⟨a, w1, (hpr a t).2 ⟨w2, hne⟩, by show upd g.ph h 2 a = 2; rw [uph a hah]; exact w3⟩)
    · obtain ⟨w1, w2, w3, w4⟩ := hC.dc t ht
      exact ⟨w1, by omega, (pend_iff hpr t).2 ⟨w3, by omega⟩, w4⟩
    · change none = some a at h1; cases h1

/-- A release in SPOILED mode (in place). -/
theorem lk_relS {σ σ' : OSt (List Nat)} {g : LkS} {h ts : Nat} {rc : Prop}
    (hok : LkOk img M σ g) (hsp : g.spoil = true) (hrc : rc) (hful : fulO M h σ rc ts σ') :
    LkOk img M σ' g := by
  obtain ⟨hdone, _, _, _, _, _, hcase⟩ := ful_facts hok.pr hful
  have hnDl : ¬ g.Dl ts := by
    rcases hcase with ⟨_, _, hnr⟩ | ⟨ets, _, _, _⟩
    · exact absurd hrc hnr
    · intro hd; have := (hok.dl ts hd).2.1; omega
  exact ⟨ful_pr hok hful, ful_dl hok hful hnDl, hok.bad, hok.spoil, fun e => (by rw [hsp] at e; cases e),
    fun e => (by rw [hsp] at e; cases e), hok.cnt, fun hh gg hg => hok.done hh gg (by rw [← hdone]; exact hg),
    hok.ph3, hok.mk_bad⟩

/-- THE END of hart `h`: its registers are recorded. -/
theorem lk_fin {σ : OSt (List Nat)} {g : LkS} {h : Nat} {gg : List Nat} (hok : LkOk img M σ g)
    (hk : specH gg g h) : LkOk img M { σ with done := upd σ.done h (some gg) } g := by
  refine ⟨hok.pr, hok.dl, hok.bad, hok.spoil, fun hs => let l := hok.lock hs; ⟨l.1, l.2, l.3, l.4, l.5, l.6⟩,
    fun hs => let c := hok.c hs; ⟨c.1, c.2, c.3, c.4, c.5, c.6⟩, hok.cnt, fun h' gg' hg => ?_, hok.ph3, hok.mk_bad⟩
  by_cases e : h' = h
  · subst e; simp only [upd_eq] at hg; cases hg; exact hk
  · simp only [upd_ne _ _ e] at hg; exact hok.done h' gg' hg

/-- **THE FINAL EXTRACTION** (G4 (1c) + (3)): at the end of a valid run (no promise left) nothing is dead, so not `bad`,
and the two harts recorded distinct counter values (their final `x7`s differ) and read the lock word as held. -/
theorem lk_final {σ : OSt (List Nat)} {g : LkS} (hok : LkOk img M σ g) (hpr : ∀ a, σ.pr a = ∅) :
    ∀ g0 g1, σ.done 0 = some g0 → σ.done 1 = some g1 → lkSpec g0 g1 := by
  have hnp : ∀ t, ¬ pend M σ t := fun t ⟨a, _, ha⟩ => by rw [hpr a] at ha; exact notElemOfEmpty ha
  have hbad : g.bad = false := by
    cases hb : g.bad with
    | false => rfl
    | true =>
      exfalso
      rcases hok.bad hb with ⟨t, ht⟩ | ⟨hsp, t, ht⟩
      · exact hnp t (hok.dl t ht).2.2.1
      · exact hnp t ((hok.c hsp).dc t ht).2.2.1
  have hcnt := hok.cnt hbad
  have hc2 : g.cnt ≤ 2 := by
    have := hcnt.cnt_def; split at this <;> split at this <;> omega
  intro g0 g1 h0 h1
  rcases hok.done 0 g0 h0 with u | ⟨v0, u1, u2, u3⟩
  · rw [hbad] at u; cases u
  rcases hok.done 1 g1 h1 with w | ⟨v1, w1, w2, w3⟩
  · rw [hbad] at w; cases w
  have l0 := hcnt.rds_lt 0 v0 u1
  have l1 := hcnt.rds_lt 1 v1 w1
  have hne : v0 ≠ v1 := fun e => by subst e; exact hcnt.rds_inj 0 1 v0 (by omega) u1 w1
  refine ⟨?_, u3, w3⟩
  rw [u2, w2]; simp only [two64]; omega

/-- In spoiled mode a hart may turn rogue (phase 3). -/
theorem lk_toRogue {σ : OSt (List Nat)} {g : LkS} {h : Nat} (hok : LkOk img M σ g) (hsp : g.spoil = true) :
    LkOk img M σ { g with ph := upd g.ph h 3 } :=
  ⟨hok.pr, hok.dl, hok.bad, hok.spoil, fun e => (by change g.spoil = false at e; rw [hsp] at e; cases e),
    fun e => (by change g.spoil = false at e; rw [hsp] at e; cases e), cnt_congr (g := g) rfl rfl rfl rfl hok.cnt,
    done_congr (g := g) rfl rfl rfl hok.done, fun _ _ => hsp, hok.mk_bad⟩

/-- A hart that sees `bad` may record a witness mark. -/
theorem lk_markBad {σ : OSt (List Nat)} {g : LkS} {h m : Nat} (hok : LkOk img M σ g) (hb : g.bad = true)
    (hmk : g.mark h = none) :
    LkOk img M σ { g with mark := upd g.mark h (some m) } := by
  refine ⟨hok.pr, hok.dl, hok.bad, hok.spoil,
    fun hs => lockOk_congr (g := g) rfl rfl rfl rfl rfl rfl rfl (hok.lock hs), fun hs => ?_,
    fun e => (by change g.bad = false at e; rw [hb] at e; cases e), fun hh gg hg => .inl hb, hok.ph3,
    fun _ _ _ => hb⟩
  have hC := hok.c hs
  refine ⟨hC.tstar_le, hC.val, hC.tstart_le, hC.later, hC.dc, fun x a hx h1 h2 => ?_⟩
  rcases hC.dc_hold x a hx h1 h2 with v | v | v
  · exact .inl v
  · by_cases e : a = h
    · subst e; rw [hmk] at v; cases v
    · exact .inr (.inl (by show upd g.mark h (some m) a = some x; rw [upd_ne _ _ e]; exact v))
  · exact .inr (.inr v)

/-- Phase 1 (with the protocol live) means: the lock is owned by the hart. -/
theorem owned_of_ph1 {σ : OSt (List Nat)} {g : LkS} {h : Nat} (hL : LockOk M σ g) (hph : g.ph h = 1) :
    ∃ u, g.ls = .owned h u := by
  have hls := hL.ls_ok
  revert hls
  cases hg : g.ls with
  | free => rintro ⟨_, _, _, f4⟩; exact absurd hph (f4 h)
  | pulled a u => rintro ⟨_, _, u8⟩; exact absurd hph (u8 h)
  | owned a u =>
    rintro ⟨_, _, u8⟩
    by_cases e : h = a
    · subst e; exact ⟨u, rfl⟩
    · exact absurd hph (u8 h e)

end steps2


section extra

variable {img : Image} {M : List PMsg}

/-- A dead lock message witnesses `bad`. -/
theorem lk_setBad {σ : OSt (List Nat)} {g : LkS} (hok : LkOk img M σ g) {t : Nat} (hd : g.Dl t) :
    LkOk img M σ { g with bad := true } :=
  ⟨hok.pr, hok.dl, fun _ => .inl ⟨t, hd⟩, fun hs => ⟨rfl, (hok.spoil hs).2⟩,
    fun hs => lockOk_congr (g := g) rfl rfl rfl rfl rfl rfl rfl (hok.lock hs),
    fun hs => let c := hok.c hs; ⟨c.1, c.2, c.3, c.4, c.5, c.6⟩, fun e => (by cases e),
    fun hh gg hg => .inl rfl, hok.ph3, fun _ _ _ => rfl⟩

/-- **THE `holding()` READ** (G4 (3)): the holder's racy read of the lock's byte 0, with a floor covering its tenure
start `u`, returns 1 (its own acquire or another hart's failed attempt) or a dead message. -/
theorem lk_ldL {σ : OSt (List Nat)} {g : LkS} {h u P t0 : Nat} {b0 : BitVec 8} (hok : LkOk img M σ g)
    (hsp : g.spoil = false) (hown : g.ls = .owned h u) (hP : u ≤ P) (hmb : memByte img M t0 Lw = some b0)
    (htn : t0 ≤ σ.n) (hnw : ¬ writesIn (M.take σ.n) Lw t0 P) : b0 = 1 ∨ g.Dl t0 := by
  have hL := hok.lock hsp
  have hls := hL.ls_ok; rw [hown] at hls
  obtain ⟨⟨k1, k2, k3, _, _, _⟩, _, _⟩ := hls
  have hut : u ≤ t0 := by
    refine Classical.byContradiction fun hlt => hnw ⟨u, by omega, hP, acqMsg h, ?_, ?_⟩
    · rw [List.getElem?_take, if_pos (by omega)]; exact k3
    · simp [acqMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList]
  have h1 : 1 ≤ t0 := by omega
  have hwr : wrL M t0 := wrL_of_memByte h1 hmb
  rcases hL.wrL_cls t0 h1 htn hwr with hd | ⟨a, ha⟩ | ⟨_, hle⟩
  · exact .inr hd
  · left
    obtain ⟨k, rfl⟩ : ∃ k, t0 = k + 1 := ⟨t0 - 1, by omega⟩
    have : memByte img M (k + 1) Lw = some 1 := by
      simp only [memByte]; simp only [Nat.add_sub_cancel] at ha; rw [ha]; exact acq_b0 a
    rw [hmb] at this; cases this; rfl
  · exfalso; omega

/-- **AN UNTRACKED FULFIL** (xv6's `cpu` field stores): a message that writes neither the lock byte nor a counter
byte keeps the protocol (in place or as a fulfilled promise). -/
theorem lk_untr {σ σ' : OSt (List Nat)} {g : LkS} {h ts : Nat} {rc : Prop} (hok : LkOk img M σ g)
    (hful : fulO M h σ rc ts σ') (hnL : ¬ wrL M ts) (hnX : ¬ wrX M ts) : LkOk img M σ' g := by
  obtain ⟨hdone, hn1, hn2, htsn, _, hpr, hcase⟩ := ful_facts hok.pr hful
  have hnA : ¬ isAcq M ts := fun ⟨a, ha⟩ => hnL (acq_wrL ha)
  have hnDl : ¬ g.Dl ts := fun hd => hnL (hok.dl ts hd).2.2.2.1
  refine ⟨ful_pr hok hful, ful_dl hok hful hnDl, hok.bad, hok.spoil, fun hs => ?_, fun hs => ?_, hok.cnt,
    fun hh gg hg => hok.done hh gg (by rw [← hdone]; exact hg), hok.ph3, hok.mk_bad⟩
  · have hL := hok.lock hs
    exact ful_lock_c (g := g) hok hful hL hnL hnA rfl rfl rfl rfl rfl rfl
      (fun e => by have hls := hL.ls_ok; rw [e] at hls; exact hls.2.2.1)
      (fun a u e => by have hls := hL.ls_ok; rw [e] at hls; exact hls.2.1)
  · have hC := hok.c hs
    refine ⟨by have := hC.tstar_le; omega, hC.val, by have := hC.tstart_le; omega, fun t h1 h2 h3 => ?_,
      fun t ht => ?_, hC.dc_hold⟩
    · have hne : t ≠ ts := fun e => by subst e; exact hnX h3
      have ht : t ≤ σ.n := by rcases hcase with ⟨_, e, _⟩ | ⟨e, _, _⟩ <;> omega
      rcases hC.later t h1 ht h3 with u | ⟨u1, u2, u3⟩ | ⟨a, u1, u2, u3⟩
      · exact .inl u
      · exact .inr (.inl ⟨u1, u2, (pend_iff hpr t).2 ⟨u3, hne⟩⟩)
      · exact .inr (.inr ⟨a, u1, (hpr a t).2 ⟨u2, hne⟩, u3⟩)
    · obtain ⟨u1, u2, u3, u4⟩ := hC.dc t ht
      exact ⟨u1, by omega, (pend_iff hpr t).2 ⟨u3, fun e => by subst e; exact hnX u4⟩, u4⟩

end extra

section extra2

variable {img : Image} {M : List PMsg}

/-- A lock HIGH BYTE (1–3) read by a live protocol: 0 (the image, an acquire's or a release's byte), or a dead
message (xv6's `sext.w a5,a5; bnez a5` tests the whole word). -/
theorem lk_hiByte {σ : OSt (List Nat)} {g : LkS} {t j : Nat} {b : BitVec 8} (hz : ∀ a, img a = some 0)
    (hok : LkOk img M σ g) (hsp : g.spoil = false) (hj1 : 1 ≤ j) (hj : j < 4)
    (hmb : memByte img M t (Lw + j) = some b) (htn : t ≤ σ.n) : b = 0 ∨ g.Dl t := by
  have hL := hok.lock hsp
  cases t with
  | zero =>
    left
    simp only [memByte] at hmb
    rw [hz] at hmb; cases hmb; rfl
  | succ k =>
    have hwr : wrL M (k + 1) := ⟨j, hj, wrA_of_memByte (by omega) hmb⟩
    have hb : ∀ m, M[k]? = some m → m.byteAt (Lw + j) = some b := by
      intro m hm; simp only [memByte, hm, Option.bind_some] at hmb; exact hmb
    have key : (toBytes 1 4)[j]? = some (0 : BitVec 8) ∧ (toBytes 0 4)[j]? = some (0 : BitVec 8) := by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
    have hix : (Lw + (j : Int) - Lw).toNat = j := by omega
    rcases hL.wrL_cls (k + 1) (by omega) htn hwr with hd | ⟨a, ha⟩ | ⟨⟨a, ha⟩, _⟩
    · exact .inr hd
    · left
      have h1 := hb _ (by simpa using ha)
      simp only [acqMsg, PMsg.byteAt, if_pos (show Lw ≤ Lw + (j : Int) by omega), hix, key.1] at h1
      cases h1; rfl
    · left
      have h1 := hb _ (by simpa using ha)
      simp only [relMsg, PMsg.byteAt, if_pos (show Lw ≤ Lw + (j : Int) by omega), hix, key.2] at h1
      cases h1; rfl

/-- SPOIL the protocol on a dead lock message: hart `h` turns rogue. -/
theorem lk_spoil {σ : OSt (List Nat)} {g : LkS} {h t : Nat} (hok : LkOk img M σ g) (hd : g.Dl t) :
    LkOk img M σ { g with bad := true, spoil := true, ph := upd g.ph h 3 } :=
  ⟨hok.pr, hok.dl, fun _ => .inl ⟨t, hd⟩, fun _ => ⟨rfl, ⟨t, hd⟩⟩, fun e => (by cases e), fun e => (by cases e),
    fun e => (by cases e), fun hh gg hg => .inl rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A fulfil in SPOILED mode (only the dead lock messages matter). -/
theorem lk_fulS {σ σ' : OSt (List Nat)} {g : LkS} {h ts : Nat} {rc : Prop}
    (hok : LkOk img M σ g) (hsp : g.spoil = true) (hful : fulO M h σ rc ts σ') (hnd : ¬ g.Dl ts) :
    LkOk img M σ' g := by
  obtain ⟨hdone, _, _, _, _, _, _⟩ := ful_facts hok.pr hful
  exact ⟨ful_pr hok hful, ful_dl (g := g) hok hful hnd, hok.bad, hok.spoil, fun e => (by rw [hsp] at e; cases e),
    fun e => (by rw [hsp] at e; cases e), hok.cnt, fun hh gg hg => hok.done hh gg (by rw [← hdone]; exact hg),
    hok.ph3, hok.mk_bad⟩

end extra2

end Weak.Prom.Own.Lk1c
