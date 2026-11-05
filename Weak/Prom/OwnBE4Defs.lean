/-
Weak/Prom: **E-b4 — the LOCK LIFECYCLE on track (b): the protocol** (stage E-b4; owner ruling [OWN.P16],
context.md item 24; G4-review3.md §5 B-3, B-5; plan rev 7 §4 "Pull rule", (b1) pull, (b2-own)/(b2-none), (b1-def)).

The test is E-a4's `t7` (OwnAE4Defs.lean, used read-only): two lifetimes of one lock at one address.  On track (b)
the lifecycle is a PURE STATE MACHINE `PS` over the prefix `M.take n`, advanced by the promise agent at each append
(the PULL and the backed/dead split, plan §4) and by the harts' steps (in-place releases, the publication, the
closing release), plus a per-hart ghost record `Loc` (the hart's stage) that the harts own half of:
* lifetime `lt`, lock state `ls`: `dead` (hart 0 owns word and field: kfree junk, initlock, field init are backed)
  → at the PUBLICATION (hart 0's in-place `sb`, the deferred deposit (b1-def)) `free` → `pulled h u` (the agent
  appended `h`'s acquire-shaped message `u` on a free lock: THE PULL) → `owned h u` (h's AMO read a live zero) →
  `free` at an in-place release → … → hart 0's CLOSING release (both done bytes seen) → `dead` of lifetime `lt+1`.
  A birth `sw zero` and a release `sw zero` are both just LIVE ZEROS (`nd0`): no reader ever needs to tell them
  apart — the taker invariant `tk1`/`tk2` says a clean window from ANY live zero to a fresh hart's acquire means the
  lock is pulled by that hart, and it is reset trivially at each publication (no acquire of the new lifetime exists
  below it: `pubT lt < ts`).
* the field's record: holder `hold` (hart 0 while dead), tenure start `tst`, latest live field write `tstar`;
  field messages appended by a non-holder are DEAD (`Dc`, never fulfilled while the protocol holds);
* ROBUST dead messages `Dr` (never fulfilled by any text, whatever happens): shapes no hart's text promises
  (`¬ okS`), and hart 0's lock-word stores appended outside its dead phase (`Rob`, via hart 0's close floor `cf`);
* flags: the in-place publications `pubT k` and done bytes `dnT i k`; a done byte of round `k` in the prefix means
  its author left round `k` (`dnk`) — this is what lets hart 0 close the lifetime (THE DEATH);
* `GoodT`: hart 0's trace has no field load; with no dead message in the prefix, both acquirers' traces satisfy
  `q7` (E-a4's verdict, OwnAE4Defs.lean, used read-only).
`Inv` = well-formed promise sets ∧ (`Good` ∨ a robust dead message is pending — SPOILED: only that is kept).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Kit
import Weak.Prom.OwnAE4Defs
import Weak.Prom.OwnLock1c

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach
open Weak.Prom.Own (OSt upd upd_eq upd_ne agentStep authorAt fulO)
open Weak.Prom.Own.MP (au)
open Weak.Prom.Own.Lk1c (pend)
open Weak.Prom.PF (Trace PEv msgAt tidAt)
open Weak.Prom.OA (Lk Ct clsB clsB_iff clsB_of)
open Weak.Prom.OA.P (L1 cAt5)
open Weak.Prom.OA.C (Pc)
open Weak.Prom.OA.E2 (cmP3 isC3 gd noLd latestC3)
open Weak.Prom.OA.E4 (q7 img7)
open PLabel

/-! ## 1. Shapes -/

/-- Message `m` overlaps the bytes `[a, a + n)`. -/
def ov (m : PMsg) (a : Int) (n : Nat) : Prop := m.pa < a + n ∧ a < m.pa + m.data.length

instance (m : PMsg) (a : Int) (n : Nat) : Decidable (ov m a n) := by unfold ov; infer_instance

/-- An acquire's message (`amoswap.w.aq` of 1). -/
def acqM (a : Nat) : PMsg := ⟨Lk, toBytes 1 4, some a, .excl⟩
/-- A publication (`sb a3,0(a2)` of hart 0, round `k`). -/
def pubM (k : Nat) : PMsg := ⟨L1, toBytes k 1, some 0, .plain⟩
/-- A done byte (`sb a3,0(a6)` of acquirer `i`, round `k`). -/
def dnM (i k : Nat) : PMsg := ⟨L1 + i, toBytes k 1, some i, .plain⟩

/-- A 4-byte plain store at the lock word by hart 0 (kfree junk, initlock — or its release, in place). -/
def plk0 (m : PMsg) : Prop := m.tid = some 0 ∧ m.pa = Lk ∧ m.data.length = 4 ∧ m.cls = .plain
/-- A 8-byte plain store at the cpu field. -/
def cpuS (m : PMsg) : Prop := m.pa = Pc ∧ m.data.length = 8 ∧ m.cls = .plain

/-- **THE SHAPES A HART'S TEXT MAY FULFIL FROM A PROMISE** (releases, publications and done bytes are always
release-class, hence in place). -/
def okS (m : PMsg) : Prop :=
  ∃ a, a < 3 ∧ m.tid = some a ∧ (plk0 m ∨ m = acqM a ∨ cmP3 m ∨ cpuS m)

/-- The stages of a hart's text (acquirers `W A H1 H2 R`, hart 0 `D0 D1 D2 P H0`). -/
inductive Stg where
  | W | A | H1 | H2 | R | D0 | D1 | D2 | P | H0
  deriving DecidableEq

def isD (s : Stg) : Prop := s = .D0 ∨ s = .D1 ∨ s = .D2

instance (s : Stg) : Decidable (isD s) := by unfold isD; infer_instance

/-- **A HART'S LOCAL RECORD** (half owned by the hart, half by the state interpretation). -/
structure Loc where
  k : Nat
  st : Stg
  u : Nat
  p : Nat
  ld : Option (List (Nat × BitVec 8))
  cf : Nat
  f : Nat
  d1 : Bool
  d2 : Bool

/-- The lock's state. -/
inductive LS where
  | dead | free
  | pulled (h u : Nat)
  | owned (h u : Nat)
  deriving DecidableEq

/-- **THE PROTOCOL STATE**. -/
structure PS where
  lt : Nat
  ls : LS
  hold : Option Nat
  tst : Nat
  tstar : Nat
  Dr : Nat → Prop
  Dc : Nat → Prop
  pubT : Nat → Nat
  dnT : Nat → Nat → Nat

/-! ## 2. The invariant -/

/-- Promise sets are within the prefix and authored. -/
def WFp (M : List PMsg) (o : OSt (List Nat)) : Prop := ∀ a t, t ∈ o.pr a → 1 ≤ t ∧ t ≤ o.n ∧ au M t = some a

/-- **A ROBUST DEAD MESSAGE**: pending, and no text will ever fulfil it — its shape is no hart's promise shape, or it
is hart 0's lock-word store appended outside hart 0's dead phase (below its close floor `cf` once dead again). -/
def Rob (M : List PMsg) (o : OSt (List Nat)) (l0 : Loc) (t : Nat) : Prop :=
  pend M o t ∧ ∃ m, msgAt M t = some m ∧ (¬ okS m ∨ (plk0 m ∧ (¬ isD l0.st ∨ t < l0.cf)))

/-- A LIVE ZERO of the lock's byte 0 (the image, a birth, a release …): not robust-dead, byte 0 is zero. -/
def nd0 (M : List PMsg) (S : PS) (t0 : Nat) : Prop := ¬ S.Dr t0 ∧ memByte img7 M t0 Lk = some 0

/-- No other hart writes the lock's byte 0 in `(t0, ts)`. -/
def clean (M : List PMsg) (h t0 ts : Nat) : Prop := ∀ t, t0 < t → t < ts → (∃ m, msgAt M t = some m ∧
  (m.byteAt Lk).isSome = true) → au M t = some h

/-- Hart `h` has not yet acquired in the current lifetime. -/
def fresh (S : PS) (ls : Nat → Loc) (h : Nat) : Prop :=
  (h = 0 ∧ (ls 0).st = .P) ∨ ((h = 1 ∨ h = 2) ∧ (ls h).k = S.lt ∧ ((ls h).st = .W ∨ (ls h).st = .A))

/-- **THE PROTOCOL** (`Good`'s trace-free part). -/
structure GoodP (M : List PMsg) (o : OSt (List Nat)) (S : PS) (ls : Nat → Loc) : Prop where
  dr : ∀ t, S.Dr t → Rob M o (ls 0) t
  dc : ∀ t, S.Dc t → pend M o t ∧ ∃ m, msgAt M t = some m ∧ cmP3 m
  dcH : ∀ t a, S.Dc t → S.hold = some a → au M t = some a → t < S.tst ∨
    (∃ tvs, (ls a).ld = some tvs ∧ t ∈ tvs.map Prod.fst) ∨ (a ≠ 0 ∧ S.tst < S.tstar ∧ t < S.tstar)
  tsle : S.tstar ≤ o.n ∧ S.tst ≤ o.n
  tsok : S.tstar = 0 ∨ ∃ m, msgAt M S.tstar = some m ∧ cmP3 m
  later : ∀ t m, S.tstar < t → t ≤ o.n → msgAt M t = some m → ov m Ct 8 → S.Dr t ∨ S.Dc t ∨
    (∃ a, S.hold = some a ∧ m.tid = some a ∧ S.tst < t ∧ pend M o t ∧ cmP3 m)
  hdead : S.ls = .dead → S.hold = some 0 ∧ S.tst = (ls 0).u
  hfree : S.ls = .free → S.hold = none
  hpo : ∀ h u, (S.ls = .pulled h u ∨ S.ls = .owned h u) → S.hold = some h ∧ S.tst = u
  gdp : S.ls ≠ .dead → gd M S.tstar
  h0f : ((ls 0).st = .D0 → S.tstar ≤ S.tst) ∧ (((ls 0).st = .D1 ∨ (ls 0).st = .D2) → S.tstar = (ls 0).f) ∧
    ((ls 0).st = .D2 → cAt5 M S.tstar)
  hpre : ∀ h u, S.ls = .pulled h u → S.tstar ≤ S.tst
  hown : ∀ h u, S.ls = .owned h u → ((h = 0 ∧ (ls 0).st = .H0 ∧ (ls 0).u = u) ∨
    ((h = 1 ∨ h = 2) ∧ ((ls h).st = .H1 ∨ (ls h).st = .H2) ∧ (ls h).u = u))
  h1 : ∀ i, (i = 1 ∨ i = 2) → (ls i).st = .H1 → S.tstar ≤ S.tst
  h0o : (ls 0).st = .H0 → S.tstar ≤ S.tst
  lk : ∀ h u, (S.ls = .pulled h u ∨ S.ls = .owned h u) → h < 3 ∧ 1 ≤ u ∧ u ≤ o.n ∧ msgAt M u = some (acqM h) ∧
    ∀ t m, u < t → t ≤ o.n → msgAt M t = some m → ov m Lk 4 → S.Dr t ∨ ∃ a, m = acqM a
  tk1 : ∀ h ts t0, S.ls ≠ .dead → fresh S ls h → S.pubT S.lt < ts → ts ∈ o.pr h → msgAt M ts = some (acqM h) →
    nd0 M S t0 → t0 < ts → clean M h t0 ts → ∃ u, u ≤ ts ∧ S.ls = .pulled h u
  tk2 : ∀ h t0, S.ls ≠ .dead → fresh S ls h → nd0 M S t0 → t0 ≤ o.n → clean M h t0 (o.n + 1) →
    S.ls = .free ∨ ∃ u, S.ls = .pulled h u
  fl : ∀ t m, 1 ≤ t → t ≤ o.n → msgAt M t = some m → ov m L1 4 → S.Dr t ∨ (∃ k, S.pubT k = t ∧ m = pubM k) ∨
    (∃ i k, (i = 1 ∨ i = 2) ∧ S.dnT i k = t ∧ m = dnM i k)
  pubk : ∀ k, S.pubT k ≠ 0 → k ≤ S.lt ∧ (k = S.lt → S.ls ≠ .dead)
  dnk : ∀ i k, (i = 1 ∨ i = 2) → S.dnT i k ≠ 0 → k < (ls i).k
  s0 : (ls 0).k = S.lt ∧ (1 ≤ S.lt ∧ S.lt ≤ 3) ∧ (isD (ls 0).st ↔ S.ls = .dead) ∧
    (isD (ls 0).st ∨ (ls 0).st = .P ∨ (ls 0).st = .H0) ∧
    (((ls 0).st = .P ∨ (ls 0).st = .H0) → S.pubT S.lt = (ls 0).p) ∧
    ((ls 0).st = .H0 → S.ls = .owned 0 (ls 0).u) ∧
    ((ls 0).d1 = true → S.lt < (ls 1).k) ∧ ((ls 0).d2 = true → S.lt < (ls 2).k) ∧ (ls 0).ld = none
  sA : ∀ i, (i = 1 ∨ i = 2) → ((ls i).k = S.lt ∨ ((ls i).k = S.lt + 1 ∧ (ls i).st = .W ∧ S.ls ≠ .dead)) ∧
    ((ls i).st = .W ∨ (ls i).st = .A ∨ (ls i).st = .H1 ∨ (ls i).st = .H2 ∨ (ls i).st = .R) ∧
    ((ls i).st ≠ .W → (ls i).k = S.lt ∧ S.ls ≠ .dead ∧ S.pubT S.lt = (ls i).p) ∧
    (((ls i).st = .H1 ∨ (ls i).st = .H2) → S.ls = .owned i (ls i).u) ∧
    ((ls i).ld ≠ none → (ls i).st = .H1)

/-- No dead message at all. -/
def clr (S : PS) : Prop := ∀ t, ¬ S.Dr t ∧ ¬ S.Dc t

/-- **THE TRACE CLAUSES**. -/
structure GoodT (M : List PMsg) (σ : TSt (List Nat)) (S : PS) (ls : Nat → Loc) : Prop where
  t0 : noLd (σ.tr 0)
  tq : clr S → q7 M (σ.tr 1) ∧ q7 M (σ.tr 2)
  tld : ∀ i tvs, (i = 1 ∨ i = 2) → (ls i).ld = some tvs →
    (∃ ev a, σ.tr i = ev ++ [(LLoad false false Ct tvs a, none)]) ∧ (clr S → ∀ p ∈ tvs, p.1 = S.tstar)

/-- **THE INVARIANT** of the state interpretation. -/
def Inv (M : List PMsg) (σ : TSt (List Nat)) (S : PS) (ls : Nat → Loc) : Prop :=
  WFp M σ.o ∧ ((GoodP M σ.o S ls ∧ GoodT M σ S ls) ∨ ∃ t, Rob M σ.o (ls 0) t)

/-! ## 3. Basic facts -/

theorem msgAt_sub {M : List PMsg} {t : Nat} (h : 1 ≤ t) : msgAt M t = M[t - 1]? := by
  cases t with
  | zero => omega
  | succ k => rfl

theorem au_msg {M : List PMsg} {t : Nat} {m : PMsg} (h1 : 1 ≤ t) (h : msgAt M t = some m) : au M t = m.tid := by
  rw [msgAt_sub h1] at h; simp [au, h]

theorem msgAt_take {M : List PMsg} {n t : Nat} {m : PMsg} (h : (M.take n)[t - 1]? = some m) (h1 : 1 ≤ t) :
    msgAt M t = some m ∧ t ≤ n := by
  rw [List.getElem?_take] at h
  split at h
  · exact ⟨by rw [msgAt_sub h1]; exact h, by omega⟩
  · cases h

theorem msgAt_ex {M : List PMsg} {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ M.length) : ∃ m, msgAt M t = some m := by
  rw [msgAt_sub h1]; exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- `memByte` against the prefix: the message is in `M`, inside the prefix. -/
theorem memByte_pre {M : List PMsg} {n t : Nat} {a : Int} {v : BitVec 8}
    (h : memByte img7 (M.take n) t a = some v) : memByte img7 M t a = some v ∧ t ≤ n :=
  Weak.Prom.Own.MP.memByte_take h

/-- A byte written by `m` lies in its range. -/
theorem byteAt_rng {m : PMsg} {a : Int} (h : (m.byteAt a).isSome = true) : m.pa ≤ a ∧ a < m.pa + m.data.length := by
  unfold PMsg.byteAt at h
  split at h
  · rename_i hle
    refine ⟨hle, ?_⟩
    rcases Nat.lt_or_ge (a - m.pa).toNat m.data.length with hl | hl
    · omega
    · rw [List.getElem?_eq_none hl] at h; cases h
  · cases h

theorem memByte_ov {M : List PMsg} {t : Nat} {a : Int} {v : BitVec 8} (h1 : 1 ≤ t) (h : memByte img7 M t a = some v) :
    ∃ m, msgAt M t = some m ∧ m.pa ≤ a ∧ a < m.pa + m.data.length ∧ m.byteAt a = some v := by
  cases t with
  | zero => omega
  | succ k =>
    simp only [memByte] at h
    cases hm : M[k]? with
    | none => rw [hm] at h; cases h
    | some m =>
      rw [hm] at h
      simp only [Option.bind_some] at h
      exact ⟨m, hm, (byteAt_rng (by rw [h]; rfl)).1, (byteAt_rng (by rw [h]; rfl)).2, h⟩

theorem toBytes_len (v n : Nat) : (toBytes v n).length = n := Weak.Prom.PF.toBytes_length v n

/-- The pending set after an agent append. -/
theorem pend_ag {M : List PMsg} {o : OSt (List Nat)} {i : Nat} (hau : au M (o.n + 1) = some i) (t : Nat) :
    pend M { o with n := o.n + 1, pr := upd o.pr i ({o.n + 1} ∪ o.pr i) } t ↔ (pend M o t ∨ t = o.n + 1) := by
  have hpr : ∀ a t, t ∈ upd o.pr i ({o.n + 1} ∪ o.pr i) a ↔ (t ∈ o.pr a ∨ (a = i ∧ t = o.n + 1)) := by
    intro a t
    by_cases e : a = i
    · subst e; simp only [upd_eq, elemOfUnion, elemOfSingleton]; constructor
      · rintro (h | h); exact .inr ⟨by simp, h⟩; exact .inl h
      · rintro (h | ⟨_, h⟩); exact .inr h; exact .inl h
    · simp only [upd_ne _ _ e]; constructor
      · exact .inl
      · rintro (h | ⟨h, _⟩); exact h; exact absurd h e
  constructor
  · rintro ⟨a, h1, h2⟩
    rcases (hpr a t).1 h2 with h | ⟨_, h⟩
    · exact .inl ⟨a, h1, h⟩
    · exact .inr h
  · rintro (⟨a, h1, h2⟩ | rfl)
    · exact ⟨a, h1, (hpr a t).2 (.inl h2)⟩
    · exact ⟨i, hau, (hpr i _).2 (.inr ⟨rfl, rfl⟩)⟩

theorem pend_le {M : List PMsg} {o : OSt (List Nat)} (hw : WFp M o) {t : Nat} (h : pend M o t) :
    1 ≤ t ∧ t ≤ o.n := by
  obtain ⟨a, _, ha⟩ := h; exact ⟨(hw a t ha).1, (hw a t ha).2.1⟩

/-! ## 4. The end -/

/-- **THE FINAL EXTRACTION**: with no promise left, nothing is pending, so the protocol is not spoiled, no dead
message exists, and every hart's trace satisfies `q7`. -/
theorem inv_final {M : List PMsg} {σ : TSt (List Nat)} {S : PS} {ls : Nat → Loc} (hI : Inv M σ S ls)
    (hpr : ∀ h, σ.o.pr h = ∅) : ∀ h, h < 3 → q7 M (σ.tr h) := by
  have hnp : ∀ t, ¬ pend M σ.o t := fun t ⟨a, _, ha⟩ => by rw [hpr a] at ha; exact notElemOfEmpty ha
  rcases hI.2 with ⟨hP, hT⟩ | ⟨t, ht, _⟩
  · have hc : clr S := fun t => ⟨fun hd => hnp t (hP.dr t hd).1, fun hd => hnp t (hP.dc t hd).1⟩
    intro h hh
    rcases (by omega : h = 0 ∨ h = 1 ∨ h = 2) with rfl | rfl | rfl
    · exact Weak.Prom.OA.E4.q7_noLd hT.t0
    · exact (hT.tq hc).1
    · exact (hT.tq hc).2
  · exact absurd ht (hnp t)

end Weak.Prom.OB.E4
