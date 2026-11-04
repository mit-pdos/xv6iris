/-
Weak/Prom: **G4 target (2′) on track (b) — the test and the pure protocol** (stage S4b part 2; plan rev 7 §4
"Gate G4" (2′): "MP-ownership in which the receiver *writes* x after the hand-off (`ld flag; fence r,rw; sd 2,(x)`).
This tests (b2-pull) …").

Test `mp2T` (real litmus front end, 8-byte accesses, image 0; x = 0x1000, flag = 0x2000):
H0 `sd x5,(x6); fence rw,w; sd x7,(x8)` (x5 = 42, x6 = x, x7 = 1, x8 = flag) ‖
H1 `ld x5,(x6); fence r,rw; sd x9,(x8)` (x6 = flag, x8 = x, x9 = 2).
Verdict: if H1 read flag = 1, H1's `sd 2` is the LAST write to x in the final memory (x's points-to moved to H1 and
H1 used it to write).

FINDING (machine v2 + plan §3's release-class definition): H1's `sd` after `fence r,rw` is ALWAYS release-class —
its pre-view is ≥ `vwNew ≥ vrOld` (the fence) and H1 has no earlier store (`vwOld = 0`) — so on track (b) it is
appended IN PLACE.  The plan's (b2-pull) case (a receiver's data promise appended BEFORE its `ld flag`) is therefore
never FULFILLED for this text: such promises are dead (or backed, if appended after the claim) and never fulfilled.
(b2-pull) is exercised only if the receiver has an earlier store that `fence r,rw` does not cover (e.g. `sd z` before
`ld flag`); see PROGRESS-S4b.md.

The protocol `mp2Ok` is MPL's (OwnMPLDefs.lean), with two additions:
* `sp` (SPOILED): a write to x by a non-holder (H1 writing without having claimed — then H1's x5 ≠ 1 or `bad`)
  switches x's record clause off;
* `own1`: H1 has written x as the holder; then x's record is (holder H1, value 2) for good.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnMPLDefs

namespace Weak.Prom.Own.MP2

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y xMsg fMsg wrX wrF xVal XRec xMsg_byte xMsg_not_Y fMsg_not_X toBytes_get)
open Weak.Prom.Ref (Instr Test two64)
open PLabel

/-! ## 1. The test -/

/-- MP-ownership with a writing receiver (G4 (2′)). -/
def mp2T : Test :=
  { harts := [[Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8],
              [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.sd 9 8]]
    regs0 := [[(5, 42), (6, Weak.Prom.Ref.Lit.X), (7, 1), (8, Weak.Prom.Ref.Lit.Y)],
              [(6, Weak.Prom.Ref.Lit.Y), (8, Weak.Prom.Ref.Lit.X), (9, 2)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

abbrev mp2Img : Image := testImg mp2T

theorem mp2Img_zero (a : Int) : mp2Img a = some 0 := by
  simp [mp2Img, testImg, Test.imgF, mp2T, bv8]

/-- H1's `sd x` message. -/
def x2Msg : PMsg := ⟨X, toBytes 2 8, some 1, .plain⟩

theorem x2Msg_byte (j : Nat) (hj : j < 8) : x2Msg.byteAt (X + j) = (toBytes 2 8)[j]? := by
  simp only [PMsg.byteAt, x2Msg]
  rw [if_pos (by omega)]
  congr 1; omega

theorem x2Msg_not_Y (j : Nat) : x2Msg.byteAt (Y + j) = none := by
  simp only [PMsg.byteAt, x2Msg, X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]
  rw [if_pos (by omega)]
  apply List.getElem?_eq_none
  simp [toBytes, Weak.Prom.Ref.byteList]; omega

/-- THE (2′) VERDICT on the final memory: some timestamp `T` holds x = 2 and no later message writes x. -/
def lastX2 (img : Image) (M : List PMsg) : Prop := ∃ T, xVal img M T 2 ∧ ∀ t, T < t → t ≤ M.length → ¬ wrX M t

/-! ## 2. The protocol -/

/-- THE PROTOCOL STATE (MPL's `mpOk`, x's record clause guarded by `sp = false`; `own1`). -/
def mp2Ok (img : Image) (M : List PMsg) (σ : OSt (List Nat)) (D : Nat → Prop) (rec : XRec) (f : Option Nat)
    (bad sp own1 : Bool) : Prop :=
  (∀ a t, t ∈ σ.pr a → 1 ≤ t ∧ t ≤ σ.n ∧ au M t = some a) ∧
  (∀ t, D t → 1 ≤ t ∧ t ≤ σ.n ∧ ∃ a, au M t = some a ∧ t ∈ σ.pr a) ∧
  (bad = true → ∃ t, D t) ∧
  (rec.tstar ≤ σ.n ∧ rec.tstart ≤ σ.n ∧ (sp = false → xVal img M rec.tstar rec.v ∧
    ∀ t, rec.tstar < t → t ≤ σ.n → wrX M t →
      D t ∨ (rec.hold = au M t ∧ rec.tstart < t ∧ ∃ a, au M t = some a ∧ t ∈ σ.pr a) ∨
      (au M t = some 0 ∧ (∃ r, f = some r ∧ t ≤ r) ∧ t ∈ σ.pr 0))) ∧
  (∀ t, 1 ≤ t → t ≤ σ.n → wrF M t → D t ∨ f = some t) ∧
  (∀ r, f = some r → 1 ≤ r ∧ r ≤ σ.n ∧ M[r - 1]? = some fMsg) ∧
  (own1 = true → sp = false ∧ rec.hold = some 1 ∧ rec.v = 2) ∧
  (∀ g, σ.done 1 = some g → (g[5]?).getD 0 ≠ 1 ∨ bad = true ∨ own1 = true)

section steps

variable {img : Image} {M : List PMsg}

theorem mp2Ok_agent {σ σ' : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad sp own1 : Bool}
    (hok : mp2Ok img M σ D rec f bad sp own1) (ha : agentStep (litOW img M) σ σ') :
    ∃ D', mp2Ok img M σ' D' rec f bad sp own1 := by
  obtain ⟨i, hn, hau, rfl⟩ := ha
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx3, hx4⟩, hcell, hf, ho, hdone⟩ := hok
  have hau' : au M (σ.n + 1) = some i := by simpa [au, authorAt] using hau
  let dead : Prop := wrF M (σ.n + 1) ∨ (wrX M (σ.n + 1) ∧ rec.hold ≠ some i)
  let D' : Nat → Prop := fun t => D t ∨ (t = σ.n + 1 ∧ dead)
  have hpr' : ∀ a t, t ∈ upd σ.pr i ({σ.n + 1} ∪ σ.pr i) a ↔ (t ∈ σ.pr a ∨ (a = i ∧ t = σ.n + 1)) := by
    intro a t
    by_cases e : a = i
    · subst e; simp only [upd_eq, elemOfUnion, elemOfSingleton]; constructor
      · rintro (h | h); exact .inr ⟨by simp, h⟩; exact .inl h
      · rintro (h | ⟨_, h⟩); exact .inr h; exact .inl h
    · simp only [upd_ne _ _ e]; constructor
      · exact .inl
      · rintro (h | ⟨h, _⟩); exact h; exact absurd h e
  refine ⟨D', ?_, ?_, ?_, ⟨by simp only; omega, by simp only; omega, fun hsp => ?_⟩, ?_, ?_, ho, hdone⟩
  · intro a t ht
    rcases (hpr' a t).1 ht with ht | ⟨rfl, rfl⟩
    · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by simp only; omega, u3⟩
    · exact ⟨by omega, by simp only; omega, hau'⟩
  · intro t ht
    rcases ht with ht | ⟨rfl, _⟩
    · obtain ⟨u1, u2, a, u3, u4⟩ := hD t ht
      exact ⟨u1, by simp only; omega, a, u3, (hpr' a t).2 (.inl u4)⟩
    · exact ⟨by omega, by simp only; omega, i, hau', (hpr' i _).2 (.inr ⟨rfl, rfl⟩)⟩
  · intro hb; obtain ⟨t, ht⟩ := hbad hb; exact ⟨t, .inl ht⟩
  · obtain ⟨hx2, hx4⟩ := hx4 hsp
    refine ⟨hx2, fun t h1 h2 h3 => ?_⟩
    by_cases e : t = σ.n + 1
    · subst e
      by_cases hh : rec.hold = some i
      · by_cases hF : wrF M (σ.n + 1)
        · exact .inl (.inr ⟨rfl, .inl hF⟩)
        · exact .inr (.inl ⟨by rw [hh, hau'], by omega, i, hau', (hpr' i _).2 (.inr ⟨rfl, rfl⟩)⟩)
      · exact .inl (.inr ⟨rfl, .inr ⟨h3, hh⟩⟩)
    · rcases hx4 t h1 (by simp only at h2; omega) h3 with u | ⟨u1, u2, a, u3, u4⟩ | ⟨u1, u2, u3⟩
      · exact .inl (.inl u)
      · exact .inr (.inl ⟨u1, u2, a, u3, (hpr' a t).2 (.inl u4)⟩)
      · exact .inr (.inr ⟨u1, u2, (hpr' 0 t).2 (.inl u3)⟩)
  · intro t h1 h2 h3
    by_cases e : t = σ.n + 1
    · subst e; exact .inl (.inr ⟨rfl, .inl h3⟩)
    · rcases hcell t h1 (by simp only at h2; omega) h3 with u | u
      · exact .inl (.inl u)
      · exact .inr u
  · intro r hr; obtain ⟨u1, u2, u3⟩ := hf r hr; exact ⟨u1, by simp only; omega, u3⟩

/-- THE FINAL EXTRACTION: at the end of a valid run, if H1 finished with `x5 = 1`, x's last write is H1's 2. -/
theorem mp2Ok_final {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad sp own1 : Bool}
    (hok : mp2Ok img M σ D rec f bad sp own1) (hn : σ.n = M.length) (hpr : ∀ h, σ.pr h = ∅) :
    ∀ g, σ.done 1 = some g → (g[5]?).getD 0 = 1 → lastX2 img M := by
  intro g hg h5
  obtain ⟨_, hD, hbad, ⟨_, _, hx4⟩, _, _, ho, hdone⟩ := hok
  have hnp : ∀ t a, t ∉ σ.pr a := fun t a ht => by rw [hpr a] at ht; exact notElemOfEmpty ht
  rcases hdone g hg with h | h | h
  · exact absurd h5 h
  · obtain ⟨t, ht⟩ := hbad h
    obtain ⟨_, _, a, _, ha⟩ := hD t ht
    exact absurd ha (hnp t a)
  · obtain ⟨hsp, _, hv⟩ := ho h
    obtain ⟨hx2, hx4⟩ := hx4 hsp
    rw [hv] at hx2
    refine ⟨rec.tstar, hx2, fun t h1 h2 h3 => ?_⟩
    rcases hx4 t h1 (by omega) h3 with u | ⟨_, _, a, _, u4⟩ | ⟨_, _, u3⟩
    · obtain ⟨_, _, a, _, ha⟩ := hD t u; exact hnp t a ha
    · exact hnp t a u4
    · exact hnp t 0 u3

theorem mp2Ok_setBad {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad sp own1 : Bool}
    {t : Nat} (hok : mp2Ok img M σ D rec f bad sp own1) (ht : D t) : mp2Ok img M σ D rec f true sp own1 := by
  obtain ⟨hpr, hD, _, hx, hcell, hf, ho, _⟩ := hok
  exact ⟨hpr, hD, fun _ => ⟨t, ht⟩, hx, hcell, hf, ho, fun _ _ => .inr (.inl rfl)⟩

/-- H0's `sd x` (in place): x's latest message (or nothing, if spoiled). -/
theorem h0_x2 {σ : OSt (List Nat)} {D : Nat → Prop} {bad sp own1 : Bool}
    (hok : mp2Ok img M σ D ⟨some 0, 0, 0, 0⟩ none bad sp own1) (hM : M[σ.n]? = some xMsg) :
    mp2Ok img M { σ with n := σ.n + 1 } D ⟨some 0, 0, σ.n + 1, 42⟩ none bad sp own1 := by
  obtain ⟨hpr, hD, hbad, _, hcell, _, ho, hdone⟩ := hok
  refine ⟨fun a t ht => ?_, fun t ht => ?_, hbad,
    ⟨Nat.le_refl _, Nat.zero_le _, fun _ => ⟨fun j hj => ?_, fun t h1 h2 _ => by simp only at h1 h2; omega⟩⟩,
    fun t h1 h2 h3 => ?_, fun r hr => (by cases hr), fun h => ?_, hdone⟩
  · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by simp only; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hD t ht; exact ⟨u1, by simp only; omega, u3⟩
  · simp only [memByte, hM, Option.bind_some]; exact xMsg_byte j hj
  · by_cases e : t = σ.n + 1
    · subst e
      obtain ⟨j, _, m, hm, hb⟩ := h3
      simp only [Nat.add_sub_cancel] at hm
      rw [hM] at hm; cases hm
      rw [xMsg_not_Y] at hb; cases hb
    · rcases hcell t h1 (by simp only at h2; omega) h3 with u | u
      · exact .inl u
      · cases u
  · obtain ⟨_, h2, _⟩ := ho h; cases h2

/-- H0's `sd flag` (in place): THE DEPOSIT. -/
theorem h0_f2 {σ : OSt (List Nat)} {D : Nat → Prop} {bad sp own1 : Bool} {tsx : Nat}
    (hok : mp2Ok img M σ D ⟨some 0, 0, tsx, 42⟩ none bad sp own1) (hM : M[σ.n]? = some fMsg) :
    tsx < σ.n + 1 ∧
      mp2Ok img M { σ with n := σ.n + 1 } D ⟨none, σ.n + 1, tsx, 42⟩ (some (σ.n + 1)) bad sp own1 := by
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx3, hx4⟩, hcell, hf, ho, hdone⟩ := hok
  have hnotX : ¬ wrX M (σ.n + 1) := by
    rintro ⟨j, hj, m, hm', hb⟩
    simp only [Nat.add_sub_cancel] at hm'
    rw [hM] at hm'; cases hm'
    rw [fMsg_not_X j hj] at hb; cases hb
  refine ⟨by simp only at hx1; omega, fun a t ht => ?_, fun t ht => ?_, hbad,
    ⟨by simp only at hx1 ⊢; omega, Nat.le_refl _, fun hsp => ?_⟩, fun t h1 h2 h3 => ?_,
    fun r hr => ?_, fun h => ?_, hdone⟩
  · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by simp only; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hD t ht; exact ⟨u1, by simp only; omega, u3⟩
  · obtain ⟨hx2, hx4⟩ := hx4 hsp
    refine ⟨hx2, fun t h1 h2 h3 => ?_⟩
    by_cases e2 : t = σ.n + 1
    · subst e2; exact absurd h3 hnotX
    · rcases hx4 t h1 (by simp only at h2; omega) h3 with u | ⟨u1, _, a, u3, u4⟩ | ⟨_, ⟨r, hr, _⟩, _⟩
      · exact .inl u
      · simp only at u1
        rw [u3] at u1; cases u1
        exact .inr (.inr ⟨u3, ⟨σ.n + 1, rfl, by simp only at h2; omega⟩, u4⟩)
      · cases hr
  · by_cases e2 : t = σ.n + 1
    · subst e2; exact .inr rfl
    · rcases hcell t h1 (by simp only at h2; omega) h3 with u | u
      · exact .inl u
      · cases u
  · cases hr
    exact ⟨by omega, Nat.le_refl _, by simpa using hM⟩
  · obtain ⟨_, h2, _⟩ := ho h; cases h2

/-- H1's CLAIM. -/
theorem h1_claim2 {σ : OSt (List Nat)} {D : Nat → Prop} {bad sp own1 : Bool} {r tsx : Nat} {f : Option Nat}
    (hok : mp2Ok img M σ D ⟨none, r, tsx, 42⟩ f bad sp own1) :
    mp2Ok img M σ D ⟨some 1, σ.n, tsx, 42⟩ f bad sp own1 := by
  obtain ⟨hpr, hD, hbad, ⟨hx1, _, hx4⟩, hcell, hf, ho, hdone⟩ := hok
  refine ⟨hpr, hD, hbad, ⟨hx1, Nat.le_refl _, fun hsp => ?_⟩, hcell, hf, fun h => ?_, hdone⟩
  · obtain ⟨hx2, hx4⟩ := hx4 hsp
    refine ⟨hx2, fun t h1 h2 h3 => ?_⟩
    rcases hx4 t h1 h2 h3 with u | ⟨u1, _, a, u3, _⟩ | u
    · exact .inl u
    · simp only at u1; rw [u3] at u1; cases u1
    · exact .inr (.inr u)
  · obtain ⟨_, h2, _⟩ := ho h; cases h2

/-- H1's `sd 2` AS THE HOLDER (in place): x's latest message, `own1`. -/
theorem h1_st_own {σ : OSt (List Nat)} {D : Nat → Prop} {bad sp own1 : Bool} {nc tsx : Nat} {f : Option Nat}
    (hok : mp2Ok img M σ D ⟨some 1, nc, tsx, 42⟩ f bad sp own1) (hsp : sp = false) (hM : M[σ.n]? = some x2Msg) :
    mp2Ok img M { σ with n := σ.n + 1 } D ⟨some 1, nc, σ.n + 1, 2⟩ f bad false true := by
  subst hsp
  obtain ⟨hpr, hD, hbad, ⟨_, hx3, _⟩, hcell, hf, _, hdone⟩ := hok
  refine ⟨fun a t ht => ?_, fun t ht => ?_, hbad,
    ⟨Nat.le_refl _, by simp only at hx3 ⊢; omega, fun _ => ⟨fun j hj => ?_, fun t h1 h2 _ => by simp only at h1 h2; omega⟩⟩,
    fun t h1 h2 h3 => ?_, fun r hr => ?_, fun _ => ⟨rfl, rfl, rfl⟩, fun g hg => .inr (.inr rfl)⟩
  · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by simp only; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hD t ht; exact ⟨u1, by simp only; omega, u3⟩
  · simp only [memByte, hM, Option.bind_some]; exact x2Msg_byte j hj
  · by_cases e : t = σ.n + 1
    · subst e
      obtain ⟨j, _, m, hm, hb⟩ := h3
      simp only [Nat.add_sub_cancel] at hm
      rw [hM] at hm; cases hm
      rw [x2Msg_not_Y] at hb; cases hb
    · exact hcell t h1 (by simp only at h2; omega) h3
  · obtain ⟨u1, u2, u3⟩ := hf r hr; exact ⟨u1, by simp only; omega, u3⟩

/-- H1's `sd 2` WITHOUT HAVING CLAIMED (in place): x is SPOILED. -/
theorem h1_st_spoil {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad sp own1 : Bool}
    (hok : mp2Ok img M σ D rec f bad sp own1) (ho : own1 = false) (hM : M[σ.n]? = some x2Msg) :
    mp2Ok img M { σ with n := σ.n + 1 } D rec f bad true own1 := by
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx3, _⟩, hcell, hf, _, hdone⟩ := hok
  refine ⟨fun a t ht => ?_, fun t ht => ?_, hbad, ⟨by simp only at hx1 ⊢; omega, by simp only at hx3 ⊢; omega,
    fun h => (by cases h)⟩, fun t h1 h2 h3 => ?_, fun r hr => ?_, fun h => (by rw [ho] at h; cases h), hdone⟩
  · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by simp only; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hD t ht; exact ⟨u1, by simp only; omega, u3⟩
  · by_cases e : t = σ.n + 1
    · subst e
      obtain ⟨j, _, m, hm, hb⟩ := h3
      simp only [Nat.add_sub_cancel] at hm
      rw [hM] at hm; cases hm
      rw [x2Msg_not_Y] at hb; cases hb
    · exact hcell t h1 (by simp only at h2; omega) h3
  · obtain ⟨u1, u2, u3⟩ := hf r hr; exact ⟨u1, by simp only; omega, u3⟩

/-- H1's FINAL VALUE. -/
theorem h1_fin2 {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad sp own1 : Bool}
    {g : List Nat} (hok : mp2Ok img M σ D rec f bad sp own1) (hg : (g[5]?).getD 0 ≠ 1 ∨ bad = true ∨ own1 = true) :
    mp2Ok img M { σ with done := upd σ.done 1 (some g) } D rec f bad sp own1 := by
  obtain ⟨hpr, hD, hbad, hx, hcell, hf, ho, _⟩ := hok
  refine ⟨hpr, hD, hbad, hx, hcell, hf, ho, fun g' hg' => ?_⟩
  simp only [upd_eq] at hg'
  cases hg'
  exact hg

/-- H0's FINAL VALUE. -/
theorem h0_fin2 {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad sp own1 : Bool}
    {g : List Nat} (hok : mp2Ok img M σ D rec f bad sp own1) :
    mp2Ok img M { σ with done := upd σ.done 0 (some g) } D rec f bad sp own1 := by
  obtain ⟨hpr, hD, hbad, hx, hcell, hf, ho, hdone⟩ := hok
  refine ⟨hpr, hD, hbad, hx, hcell, hf, ho, fun g' hg' => ?_⟩
  simp only [upd_ne _ _ (show (1 : Nat) ≠ 0 by omega)] at hg'
  exact hdone g' hg'

theorem mp2Ok_init (hz : ∀ a, img a = some 0) :
    mp2Ok img M σ0 (fun _ => False) ⟨some 0, 0, 0, 0⟩ none false false false := by
  obtain ⟨_, _, _, ⟨_, h2, _, _⟩, _, _, _⟩ := MPL.mpOk_init (M := M) hz
  refine ⟨fun a t ht => absurd ht notElemOfEmpty, fun t ht => False.elim ht, fun h => (by cases h),
    ⟨Nat.le_refl _, Nat.le_refl _, fun _ => ⟨h2, fun t h1 h2 _ => (by simp [σ0] at h2; omega)⟩⟩,
    fun t h1 h2 _ => (by simp [σ0] at h2; omega), fun r hr => (by cases hr), fun h => (by cases h),
    fun g hg => (by simp [σ0] at hg)⟩

end steps

end Weak.Prom.Own.MP2
