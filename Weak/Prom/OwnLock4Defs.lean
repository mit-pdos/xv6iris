/-
Weak/Prom: **G4 target (4) on track (b): a lock BORN BY A PLAIN STORE over kalloc junk, published by a release, its
resource DEPOSITED LATE (deferred) and named by ghost state allocated AT RUNTIME** (stage S4b part 3, tag S4b3; plan
rev 7 §4 "Gate G4" (4), §3 "Lock birth and deferred deposits" [R1.9], (b1-def)).

Test `lk4T` (real litmus front end; counter `c` = 0x1000 (8 bytes), lock word `lk` = 0x2000 (4 bytes), flag `f` =
0x3000 (8 bytes), image 0), the pipealloc shape:
```
H0 (allocator):  sw x6,0(x10)   kalloc junk (5) on the lock word (its first write: in place)
                 sw x0,0(x10)   initlock: THE LOCK IS BORN by a plain store — NOT release-class (vwOld ≥ junk)
                 sd x5,(x11)    the protected data: c := 42 (plain)
                 fence rw,w
                 sd x7,(x12)    publish (f := 1): release-class, in place — THE DEFERRED DEPOSIT for the birth store
H1 (user):       ld x5,(x12); fence r,rw; beq x5,x0,END    sees the publication
                 amoswap.w.aq x6,x7,(x10); bne x6,x0,END   acquires the born lock (reads the birth store)
                 ld x8,(x11)                               the critical section's read
```
Verdict: if H1 saw the publication (x5 ≠ 0) and acquired (x6 = 0), it read 42 (x8 = 42).

THE MECHANISM (plan §3, track (b)): the birth store `t_i` is a plain write, promised early, so it cannot carry the
deposit; its deposit happens at the fulfil of H0's NEXT release-class write r(t_i) = the publish `t_f` (in place),
which moves R (the counter's points-to, a ghost half named by γ_c allocated at H0's birth step) into the lock's cell.
H1's flag read of `t_f` shows `t_f` in the prefix — executed, so deposited — and (by `fence r,rw`) puts its frontier
above `t_f > r(t_i)`, so its acquire `t_a > t_f` reads the born cell (`t_i`, by `exclOk`: H0's `t_i` is the last
other-hart write below) and TAKES R (plan (b1-def): "s is plain and filled(s, r(s), _) holds with r(s) < ts").
No saved-proposition slot is needed on track (b): the state interpretation names γ_c once allocated.

THE AGENT'S SPLIT (R-b2, total): a promised message is a CANDIDATE iff it has the shape of H0's birth store or of
H0's data store (and H0 has not yet made that store); every other promise is DEAD (H0's junk and publish and H1's
acquire are always in place: `relClass_store0`, `relClass_fW`, `relClass_aq1`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLockDefs

namespace Weak.Prom.Own.L4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y XRec xVal wrX toBytes_get relPrG xMsg xMsg_byte bytesAll_get map_snd_of)
open Weak.Prom.Own.Lk (pend ful_facts pend_iff)
open Weak.Prom.Ref (Instr Test two64)
open PLabel

/-! ## 1. The test -/

/-- The flag (8 bytes). -/
def F : Int := (Weak.Prom.Ref.Lit.Z : Int)

def h0Prog : List Instr :=
  [Weak.Prom.Ref.Lit.sw 6 10, Weak.Prom.Ref.Lit.sw 0 10, Weak.Prom.Ref.Lit.sd 5 11, Weak.Prom.Ref.Lit.fRWW,
   Weak.Prom.Ref.Lit.sd 7 12]

def h1Prog : List Instr :=
  [Weak.Prom.Ref.Lit.ld 5 12, Weak.Prom.Ref.Lit.fRRW, .br .eq 5 0 6,
   Weak.Prom.Ref.Lit.amoswapW true false 6 7 10, .br .ne 6 0 6, Weak.Prom.Ref.Lit.ld 8 11]

def h0Regs : List (Nat × Nat) :=
  [(5, 42), (6, 5), (7, 1), (10, Weak.Prom.Ref.Lit.Y), (11, Weak.Prom.Ref.Lit.X), (12, Weak.Prom.Ref.Lit.Z)]

def h1Regs : List (Nat × Nat) :=
  [(7, 1), (10, Weak.Prom.Ref.Lit.Y), (11, Weak.Prom.Ref.Lit.X), (12, Weak.Prom.Ref.Lit.Z)]

/-- G4 (4): the allocator and the user. -/
def lk4T : Test :=
  { harts := [h0Prog, h1Prog]
    regs0 := [h0Regs, h1Regs]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev lk4Img : Image := testImg lk4T

theorem lk4Img_zero (a : Int) : lk4Img a = some 0 := by
  simp [lk4Img, testImg, Test.imgF, lk4T, bv8]

/-- THE (4) VERDICT for H1's final registers. -/
def spec4 (gg : List Nat) : Prop :=
  (gg[5]?).getD 0 ≠ 0 → (gg[6]?).getD 0 = 0 → (gg[8]?).getD 0 = 42

/-! ## 2. Messages and footprints -/

def junkMsg : PMsg := ⟨Y, toBytes 5 4, some 0, .plain⟩
def initMsg : PMsg := ⟨Y, toBytes 0 4, some 0, .plain⟩
def flagMsg : PMsg := ⟨F, toBytes 1 8, some 0, .plain⟩
def acq1 : PMsg := ⟨Y, toBytes 1 4, some 1, .excl⟩

/-- Message `t` writes one of the flag's 8 bytes. -/
def wrF (M : List PMsg) (t : Nat) : Prop := ∃ j : Nat, j < 8 ∧ wrA M t (F + j)
/-- Message `t` writes the lock's byte 0. -/
def wrL (M : List PMsg) (t : Nat) : Prop := wrA M t Y

theorem byteAt_lo {m : PMsg} {a : Int} (h : a < m.pa) : m.byteAt a = none := by
  simp [PMsg.byteAt, show ¬ m.pa ≤ a by omega]

theorem byteAt_hi {m : PMsg} {a : Int} (h : m.pa + m.data.length ≤ a) : m.byteAt a = none := by
  simp only [PMsg.byteAt]
  split
  · exact List.getElem?_eq_none (by omega)
  · rfl

theorem toBytes_len (v n : Nat) : (toBytes v n).length = n := by
  simp [toBytes, Weak.Prom.Ref.byteList]

/-- A message writes only inside its footprint. -/
theorem not_wr_of {M : List PMsg} {t : Nat} {m : PMsg} {a : Int} (hm : M[t - 1]? = some m)
    (h : a < m.pa ∨ m.pa + m.data.length ≤ a) : ¬ wrA M t a := by
  rintro ⟨m', hm', hb⟩
  rw [hm] at hm'; cases hm'
  rcases h with h | h
  · rw [byteAt_lo h] at hb; cases hb
  · rw [byteAt_hi h] at hb; cases hb

section fp
variable {M : List PMsg} {t : Nat} {m : PMsg}

theorem lockMsg_not_X (hm : M[t - 1]? = some m) (hp : m.pa = Y) (hl : m.data.length = 4) : ¬ wrX M t := by
  rintro ⟨j, hj, h⟩
  exact not_wr_of hm (.inl (by rw [hp]; simp only [X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]; omega)) h

theorem lockMsg_not_F (hm : M[t - 1]? = some m) (hp : m.pa = Y) (hl : m.data.length = 4) : ¬ wrF M t := by
  rintro ⟨j, hj, h⟩
  exact not_wr_of hm (.inr (by rw [hp, hl]; simp only [F, Y, Weak.Prom.Ref.Lit.Z, Weak.Prom.Ref.Lit.Y]; omega)) h

theorem xMsg_not_L (hm : M[t - 1]? = some xMsg) : ¬ wrL M t :=
  not_wr_of hm (.inr (by simp only [xMsg, toBytes_len, X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]; omega))

theorem xMsg_not_F (hm : M[t - 1]? = some xMsg) : ¬ wrF M t := by
  rintro ⟨j, hj, h⟩
  exact not_wr_of hm (.inr (by simp only [xMsg, toBytes_len, X, F, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Z]; omega)) h

theorem flag_not_L (hm : M[t - 1]? = some flagMsg) : ¬ wrL M t :=
  not_wr_of hm (.inl (by simp only [flagMsg, F, Y, Weak.Prom.Ref.Lit.Z, Weak.Prom.Ref.Lit.Y]; omega))

theorem flag_not_X (hm : M[t - 1]? = some flagMsg) : ¬ wrX M t := by
  rintro ⟨j, hj, h⟩
  exact not_wr_of hm (.inl (by simp only [flagMsg, F, X, Weak.Prom.Ref.Lit.Z, Weak.Prom.Ref.Lit.X]; omega)) h

theorem init_not_X (hm : M[t - 1]? = some initMsg) : ¬ wrX M t := lockMsg_not_X hm rfl (toBytes_len 0 4)
theorem init_not_F (hm : M[t - 1]? = some initMsg) : ¬ wrF M t := lockMsg_not_F hm rfl (toBytes_len 0 4)
theorem junk_not_X (hm : M[t - 1]? = some junkMsg) : ¬ wrX M t := lockMsg_not_X hm rfl (toBytes_len 5 4)
theorem junk_not_F (hm : M[t - 1]? = some junkMsg) : ¬ wrF M t := lockMsg_not_F hm rfl (toBytes_len 5 4)
theorem acq1_not_X (hm : M[t - 1]? = some acq1) : ¬ wrX M t := lockMsg_not_X hm rfl (toBytes_len 1 4)
theorem acq1_not_F (hm : M[t - 1]? = some acq1) : ¬ wrF M t := lockMsg_not_F hm rfl (toBytes_len 1 4)

end fp

theorem init_ne_x : initMsg ≠ xMsg := by
  intro h; have := congrArg PMsg.pa h; simp [initMsg, xMsg, X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at this

/-- The byte-0 values of the lock messages. -/
theorem junk_b0 : junkMsg.byteAt Y = some 5 := by simp [junkMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8]
theorem init_b0 : initMsg.byteAt Y = some 0 := by simp [initMsg, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8]
theorem acq1_b0 : acq1.byteAt Y = some 1 := by simp [acq1, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8]

theorem memByte_of {img : Image} {M : List PMsg} {t : Nat} {m : PMsg} {a : Int} (h1 : 1 ≤ t)
    (hm : M[t - 1]? = some m) : memByte img M t a = m.byteAt a := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hm
  simp [memByte, hm]

/-! ## 3. The protocol state and its clauses -/

/-- THE PURE PROTOCOL STATE. -/
structure S4 where
  bad : Bool
  /-- dead messages: pending, never fulfilled -/
  Dd : Nat → Prop
  /-- H0's progress: 0, 1 (junk at `tj`), 2 (born at `ti`), 3 (data at `tc`), 4 (published at `tf`) -/
  p0 : Nat
  tj : Nat
  ti : Nat
  tc : Nat
  tf : Nat
  /-- THE RUNTIME NAME of R's ghost (allocated at the birth store) -/
  γ : Option Nat
  /-- R's place: 0 with H0, 1 deposited in the born cell, 2 with H1 -/
  rp : Nat
  /-- H1's progress: 0, 1 (saw the publication `a1`), 2 (took R at `ta`), 3 (its AMO did not take R) -/
  p1 : Nat
  ta : Nat
  a1 : Nat
  b1 : Option Nat
  /-- H1 noticed `bad` -/
  bd1 : Bool

/-- R's record (the counter's latest message and value). -/
def rec4 (g : S4) : XRec := if 3 ≤ g.p0 then ⟨none, 0, g.tc, 42⟩ else ⟨none, 0, 0, 0⟩

/-- A candidate message: the shape of H0's birth store or data store. -/
def cand (M : List PMsg) (t : Nat) : Prop := M[t - 1]? = some initMsg ∨ M[t - 1]? = some xMsg

/-- THE PROTOCOL. -/
structure I4 (img : Image) (M : List PMsg) (σ : OSt (List Nat)) (g : S4) : Prop where
  pr : ∀ a t, t ∈ σ.pr a → 1 ≤ t ∧ t ≤ σ.n ∧ au M t = some a
  dd : ∀ t, g.Dd t → pend M σ t
  dd_i : ∀ t, g.Dd t → M[t - 1]? = some initMsg → 2 ≤ g.p0
  dd_c : ∀ t, g.Dd t → M[t - 1]? = some xMsg → 3 ≤ g.p0
  cls : ∀ t, pend M σ t → g.Dd t ∨ cand M t
  cand_i : ∀ t, pend M σ t → M[t - 1]? = some initMsg → g.p0 < 2 ∨ g.Dd t
  cand_c : ∀ t, pend M σ t → M[t - 1]? = some xMsg → g.p0 < 3 ∨ g.Dd t
  bad : g.bad = true → ∃ t, g.Dd t
  p0le : g.p0 ≤ 4
  h0j : 1 ≤ g.p0 → 1 ≤ g.tj ∧ g.tj ≤ σ.n ∧ M[g.tj - 1]? = some junkMsg
  h0i : 2 ≤ g.p0 → 1 ≤ g.ti ∧ g.ti ≤ σ.n ∧ M[g.ti - 1]? = some initMsg
  h0c : 3 ≤ g.p0 → 1 ≤ g.tc ∧ g.tc ≤ σ.n ∧ M[g.tc - 1]? = some xMsg
  h0f : 4 ≤ g.p0 → 1 ≤ g.tf ∧ g.tf ≤ σ.n ∧ M[g.tf - 1]? = some flagMsg ∧ g.ti < g.tf ∧ g.tc < g.tf
  /-- the fulfilled messages are the known ones -/
  ful : ∀ t, 1 ≤ t → t ≤ σ.n → ¬ pend M σ t →
    (1 ≤ g.p0 ∧ t = g.tj) ∨ (2 ≤ g.p0 ∧ t = g.ti) ∨ (3 ≤ g.p0 ∧ t = g.tc) ∨ (4 ≤ g.p0 ∧ t = g.tf) ∨
      (2 ≤ g.p1 ∧ t = g.ta)
  γ_ok : g.γ = none ↔ g.p0 < 2
  rp_ok : g.rp ≤ 2 ∧ (g.rp = 0 ↔ g.p0 < 4) ∧ (g.rp = 2 ↔ g.p1 = 2)
  p1le : g.p1 ≤ 3
  p1a : (g.p1 = 1 ∨ g.p1 = 2) → g.p0 = 4 ∧ g.a1 = g.tf
  p1t : 2 ≤ g.p1 → 1 ≤ g.ta ∧ g.ta ≤ σ.n ∧ M[g.ta - 1]? = some acq1
  b1 : g.p1 = 2 → g.b1 = g.γ
  bd1 : g.bd1 = true → g.bad = true
  done : ∀ gg, σ.done 1 = some gg → spec4 gg ∨ g.bad = true

/-! ## 4. Pure facts -/

section facts

variable {img : Image} {M : List PMsg}

/-- THE INITIAL STATE. -/
def g0 : S4 := ⟨false, fun _ => False, 0, 0, 0, 0, 0, none, 0, 0, 0, 0, none, false⟩

theorem i4_init : I4 img M σ0 g0 := by
  refine ⟨fun a t ht => absurd ht notElemOfEmpty, fun t h => False.elim h, fun t h => False.elim h,
    fun t h => False.elim h, fun t ⟨a, _, ha⟩ => absurd ha notElemOfEmpty,
    fun t ⟨a, _, ha⟩ => absurd ha notElemOfEmpty, fun t ⟨a, _, ha⟩ => absurd ha notElemOfEmpty,
    fun h => (by cases h), by simp [g0], fun h => (by simp [g0] at h), fun h => (by simp [g0] at h),
    fun h => (by simp [g0] at h), fun h => (by simp [g0] at h), fun t h1 h2 _ => (by simp [σ0] at h2; omega),
    by simp [g0], by simp [g0], by simp [g0], fun h => (by simp [g0] at h), fun h => (by simp [g0] at h),
    fun h => (by simp [g0] at h), fun h => (by cases h), fun gg h => (by simp [σ0] at h)⟩

theorem pend_le {σ : OSt (List Nat)} {g : S4} (hok : I4 img M σ g) {t : Nat} (h : pend M σ t) :
    1 ≤ t ∧ t ≤ σ.n := by
  obtain ⟨a, _, ha⟩ := h; exact ⟨(hok.pr a t ha).1, (hok.pr a t ha).2.1⟩

/-- THE PROMISE AGENT'S OBLIGATION: a candidate is kept, everything else is dead. -/
theorem i4_agent {σ σ' : OSt (List Nat)} {g : S4} (hok : I4 img M σ g) (ha : agentStep (litOW img M) σ σ') :
    ∃ g', I4 img M σ' g' ∧ g'.p0 = g.p0 ∧ g'.ti = g.ti ∧ g'.tc = g.tc ∧ g'.γ = g.γ ∧ g'.rp = g.rp ∧
      g'.p1 = g.p1 ∧ g'.a1 = g.a1 ∧ g'.b1 = g.b1 ∧ g'.bd1 = g.bd1 ∧ g'.tf = g.tf := by
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
  let σ' : OSt (List Nat) := { σ with n := σ.n + 1, pr := upd σ.pr i ({σ.n + 1} ∪ σ.pr i) }
  have hpend : ∀ t, pend M σ' t ↔ (pend M σ t ∨ t = σ.n + 1) := by
    intro t; constructor
    · rintro ⟨a, h1, h2⟩
      rcases (hpr' a t).1 h2 with h | ⟨_, h⟩
      · exact .inl ⟨a, h1, h⟩
      · exact .inr h
    · rintro (⟨a, h1, h2⟩ | rfl)
      · exact ⟨a, h1, (hpr' a t).2 (.inl h2)⟩
      · exact ⟨i, hau', (hpr' i _).2 (.inr ⟨rfl, rfl⟩)⟩
  have hold : ∀ t, t ≤ σ.n → (pend M σ' t ↔ pend M σ t) := by
    intro t ht; rw [hpend]; constructor
    · rintro (h | rfl); exact h; omega
    · exact .inl
  -- the new message: a live candidate, or dead
  let live : Prop := (M[σ.n]? = some initMsg ∧ g.p0 < 2) ∨ (M[σ.n]? = some xMsg ∧ g.p0 < 3)
  let g' : S4 := { g with Dd := fun t => g.Dd t ∨ (t = σ.n + 1 ∧ ¬ live) }
  have hM : M[σ.n + 1 - 1]? = M[σ.n]? := by simp
  refine ⟨g', ⟨fun a t ht => ?_, fun t ht => ?_, fun t ht hm => ?_, fun t ht hm => ?_, fun t ht => ?_,
    fun t ht hm => ?_, fun t ht hm => ?_, fun hb => ?_, hok.p0le, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun t h1 h2 h3 => ?_, hok.γ_ok, hok.rp_ok, hok.p1le, hok.p1a, fun h => ?_, hok.b1, hok.bd1,
    fun gg hg => hok.done gg hg⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rcases (hpr' a t).1 ht with h | ⟨rfl, rfl⟩
    · obtain ⟨u1, u2, u3⟩ := hok.pr a t h; exact ⟨u1, by simp only [σ']; omega, u3⟩
    · exact ⟨by omega, Nat.le_refl _, hau'⟩
  · rcases ht with ht | ⟨rfl, _⟩
    · exact (hpend t).2 (.inl (hok.dd t ht))
    · exact (hpend _).2 (.inr rfl)
  · rcases ht with ht | ⟨rfl, hl⟩
    · exact hok.dd_i t ht hm
    · rw [hM] at hm
      show 2 ≤ g.p0
      exact Classical.byContradiction fun hc => hl (.inl ⟨hm, by omega⟩)
  · rcases ht with ht | ⟨rfl, hl⟩
    · exact hok.dd_c t ht hm
    · rw [hM] at hm
      show 3 ≤ g.p0
      exact Classical.byContradiction fun hc => hl (.inr ⟨hm, by omega⟩)
  · rcases (hpend t).1 ht with h | rfl
    · rcases hok.cls t h with u | u
      · exact .inl (.inl u)
      · exact .inr u
    · by_cases hl : live
      · rcases hl with ⟨u, _⟩ | ⟨u, _⟩
        · exact .inr (.inl (by rw [hM]; exact u))
        · exact .inr (.inr (by rw [hM]; exact u))
      · exact .inl (.inr ⟨rfl, hl⟩)
  · rcases (hpend t).1 ht with h | rfl
    · rcases hok.cand_i t h hm with u | u
      · exact .inl u
      · exact .inr (.inl u)
    · by_cases hp : g.p0 < 2
      · exact .inl hp
      · right; right; refine ⟨rfl, ?_⟩
        rintro (⟨_, u⟩ | ⟨u, _⟩)
        · exact hp u
        · rw [hM] at hm; rw [hm] at u; exact init_ne_x (Option.some.inj u)
  · rcases (hpend t).1 ht with h | rfl
    · rcases hok.cand_c t h hm with u | u
      · exact .inl u
      · exact .inr (.inl u)
    · by_cases hp : g.p0 < 3
      · exact .inl hp
      · right; right; refine ⟨rfl, ?_⟩
        rintro (⟨u, _⟩ | ⟨_, u⟩)
        · rw [hM] at hm; rw [hm] at u; exact init_ne_x (Option.some.inj u).symm
        · exact hp u
  · obtain ⟨t, ht⟩ := hok.bad hb; exact ⟨t, .inl ht⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0j h; exact ⟨u1, by show g.tj ≤ σ.n + 1; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0i h; exact ⟨u1, by show g.ti ≤ σ.n + 1; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hok.h0c h; exact ⟨u1, by show g.tc ≤ σ.n + 1; omega, u3⟩
  · obtain ⟨u1, u2, u3, u4, u5⟩ := hok.h0f h; exact ⟨u1, by show g.tf ≤ σ.n + 1; omega, u3, u4, u5⟩
  · by_cases e : t = σ.n + 1
    · exact absurd ((hpend t).2 (.inr e)) h3
    · have ht : t ≤ σ.n := by simp only [σ'] at h2; omega
      exact hok.ful t h1 ht (fun hp => h3 ((hold t ht).2 hp))
  · obtain ⟨u1, u2, u3⟩ := hok.p1t h; exact ⟨u1, by show g.ta ≤ σ.n + 1; omega, u3⟩

end facts

end Weak.Prom.Own.L4

/-! ## 5. The hart steps -/

namespace Weak.Prom.Own.L4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y XRec xVal wrX toBytes_get relPrG xMsg xMsg_byte bytesAll_get map_snd_of)
open Weak.Prom.Own.Lk (pend ful_facts pend_iff)
open Weak.Prom.Ref (Instr Test two64)
open PLabel

section steps

variable {img : Image} {M : List PMsg}

/-- THE FRAME OF A FULFIL: the dead/pending clauses, for a new state whose dead set adds the pending candidates
that the new progress of H0 rules out. -/
theorem i4_frame {σ σ' : OSt (List Nat)} {g g' : S4} {h ts : Nat} {rc : Prop}
    (hok : I4 img M σ g) (hful : fulO M h σ rc ts σ') (hnd : ¬ g.Dd ts)
    (hD : ∀ t, g'.Dd t ↔ (g.Dd t ∨ (pend M σ' t ∧
      ((M[t - 1]? = some initMsg ∧ 2 ≤ g'.p0) ∨ (M[t - 1]? = some xMsg ∧ 3 ≤ g'.p0)))))
    (hp0 : g.p0 ≤ g'.p0) :
    (∀ a t, t ∈ σ'.pr a → 1 ≤ t ∧ t ≤ σ'.n ∧ au M t = some a) ∧ (∀ t, g'.Dd t → pend M σ' t) ∧
    (∀ t, g'.Dd t → M[t - 1]? = some initMsg → 2 ≤ g'.p0) ∧ (∀ t, g'.Dd t → M[t - 1]? = some xMsg → 3 ≤ g'.p0) ∧
    (∀ t, pend M σ' t → g'.Dd t ∨ cand M t) ∧
    (∀ t, pend M σ' t → M[t - 1]? = some initMsg → g'.p0 < 2 ∨ g'.Dd t) ∧
    (∀ t, pend M σ' t → M[t - 1]? = some xMsg → g'.p0 < 3 ∨ g'.Dd t) ∧
    (∀ t, pend M σ' t ↔ pend M σ t ∧ t ≠ ts) := by
  obtain ⟨_, hn1, _, _, _, hpr, _⟩ := ful_facts hok.pr hful
  have hp := pend_iff (M := M) hpr
  refine ⟨fun a t ht => ?_, fun t ht => ?_, fun t ht hm => ?_, fun t ht hm => ?_, fun t ht => ?_,
    fun t ht hm => ?_, fun t ht hm => ?_, hp⟩
  · obtain ⟨u1, u2, u3⟩ := hok.pr a t ((hpr a t).1 ht).1; exact ⟨u1, by omega, u3⟩
  · rcases (hD t).1 ht with u | ⟨u, _⟩
    · exact (hp t).2 ⟨hok.dd t u, fun e => by subst e; exact hnd u⟩
    · exact u
  · rcases (hD t).1 ht with u | ⟨_, ⟨_, u⟩ | ⟨u, _⟩⟩
    · have := hok.dd_i t u hm; omega
    · exact u
    · rw [hm] at u; exact absurd (Option.some.inj u) init_ne_x
  · rcases (hD t).1 ht with u | ⟨_, ⟨u, _⟩ | ⟨_, u⟩⟩
    · have := hok.dd_c t u hm; omega
    · rw [hm] at u; exact absurd (Option.some.inj u).symm init_ne_x
    · exact u
  · rcases hok.cls t ((hp t).1 ht).1 with u | u
    · exact .inl ((hD t).2 (.inl u))
    · exact .inr u
  · rcases hok.cand_i t ((hp t).1 ht).1 hm with u | u
    · by_cases e : g'.p0 < 2
      · exact .inl e
      · exact .inr ((hD t).2 (.inr ⟨ht, .inl ⟨hm, by omega⟩⟩))
    · exact .inr ((hD t).2 (.inl u))
  · rcases hok.cand_c t ((hp t).1 ht).1 hm with u | u
    · by_cases e : g'.p0 < 3
      · exact .inl e
      · exact .inr ((hD t).2 (.inr ⟨ht, .inr ⟨hm, by omega⟩⟩))
    · exact .inr ((hD t).2 (.inl u))

/-- The fulfilled messages after a fulfil at `ts`. -/
theorem ful_old {σ σ' : OSt (List Nat)} {g : S4} {h ts : Nat} {rc : Prop} (hok : I4 img M σ g)
    (hful : fulO M h σ rc ts σ') {t : Nat} (h2 : t ≤ σ'.n) (hne : t ≠ ts) (hnp : ¬ pend M σ' t) :
    t ≤ σ.n ∧ ¬ pend M σ t := by
  obtain ⟨_, hn1, _, _, _, hpr, hcase⟩ := ful_facts hok.pr hful
  have ht : t ≤ σ.n := by rcases hcase with ⟨_, e, _⟩ | ⟨e, e2, _⟩ <;> omega
  exact ⟨ht, fun hp => hnp ((pend_iff (M := M) hpr t).2 ⟨hp, hne⟩)⟩

/-- **H0's JUNK STORE** (its first write: in place). -/
theorem h0_junk {σ σ' : OSt (List Nat)} {g : S4} {ts : Nat} {rc : Prop} (hok : I4 img M σ g)
    (hp0 : g.p0 = 0) (hrc : rc) (hful : fulO M 0 σ rc ts σ') (hM : M[ts - 1]? = some junkMsg) :
    I4 img M σ' { g with p0 := 1, tj := ts } := by
  obtain ⟨hdone, hn1, hn2, htsn, hts1, hpr, hcase⟩ := ful_facts hok.pr hful
  obtain ⟨ets, hn', _, _⟩ : ts = σ.n + 1 ∧ σ'.n = σ.n + 1 ∧ rc ∧ au M ts = some 0 := by
    rcases hcase with ⟨_, _, hnr⟩ | h4
    · exact absurd hrc hnr
    · exact h4
  have hnd : ¬ g.Dd ts := fun hd => by have := (pend_le hok (hok.dd ts hd)).2; omega
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, hp⟩ := i4_frame (g' := { g with p0 := 1, tj := ts }) hok hful hnd
    (fun t => ⟨fun h => .inl h, fun h => by rcases h with h | ⟨_, ⟨_, u⟩ | ⟨_, u⟩⟩ <;> first | exact h | (simp at u)⟩)
    (by simp only; omega)
  refine ⟨f1, f2, f3, f4, f5, f6, f7, hok.bad, by simp, fun _ => ⟨hts1, htsn, hM⟩, fun h => by simp at h,
    fun h => by simp at h, fun h => by simp at h, fun t h1 h2 h3 => ?_, ?_, ?_, hok.p1le, fun h => ?_,
    fun h => ?_, hok.b1, hok.bd1, fun gg hg => hok.done gg (by rw [← hdone]; exact hg)⟩
  · by_cases e : t = ts
    · exact .inl ⟨by simp, e⟩
    · obtain ⟨u1, u2⟩ := ful_old hok hful h2 e h3
      rcases hok.ful t h1 u1 u2 with ⟨u, _⟩ | ⟨u, _⟩ | ⟨u, _⟩ | ⟨u, _⟩ | u
      · omega
      · omega
      · omega
      · omega
      · exact .inr (.inr (.inr (.inr u)))
  · show g.γ = none ↔ 1 < 2
    have := hok.γ_ok; rw [hp0] at this; simp at this; simp [this]
  · obtain ⟨r1, r2, r3⟩ := hok.rp_ok
    exact ⟨r1, by show g.rp = 0 ↔ 1 < 4; rw [r2, hp0]; simp, r3⟩
  · have := (hok.p1a h).1; omega
  · obtain ⟨u1, u2, u3⟩ := hok.p1t h; exact ⟨u1, by show g.ta ≤ σ'.n; omega, u3⟩

end steps

end Weak.Prom.Own.L4
