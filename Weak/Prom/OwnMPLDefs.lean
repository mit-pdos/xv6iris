/-
Weak/Prom: **G4 target (2) on track (b), on the REAL litmus front end — the test and the pure protocol** (stage S4b
part 2; plan rev 7 §4 "Gate G4" (2): `sd x; fence rw,w; sd flag` / `ld flag; fence r,rw; ld x`, "proving that x's
points-to moves").  Removes part 1's caveats for (2): the program half is `litStep` (MachCert.lean), the accesses
are the plan's 8-byte `sd`/`ld`, the image is the test's (`testImg`, every byte 0), the outcome is read off the
final REGISTERS (as MachCert.lean `allowedMach` / track (a)'s `mpOwnT`).

Test `mpT` (same text as track (a)'s OwnAMPDefs.lean `mpOwnT`; x = 0x1000, flag = y = 0x2000):
H0 `sd x5,(x6); fence rw,w; sd x7,(x8)` (x5 = 42, x6 = x, x7 = 1, x8 = y) ‖
H1 `ld x5,(x6); fence r,rw; ld x7,(x8)` (x6 = y, x8 = x).

The protocol `mpOk` is part 1's (OwnMPDefs.lean), lifted from one byte to the 8-byte footprints:
* a message is an X-MESSAGE (`wrX`) when it writes any of x's 8 bytes, a FLAG MESSAGE (`wrF`) likewise;
* x's ownership record `(hold, tstart, tstar, v)`: the latest x-message `tstar` holds the 8 bytes of `v`
  (`xVal`); every later x-message in the prefix is DEAD, BACKED by the holder (plan §4 (b2-own): "data promises need
  write permission"), or a LEFTOVER of the releasing holder H0 — in all three cases still pending;
* flag's release cell `f` and the dead set `D`, `bad` as in part 1.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnKit
import Weak.Prom.OwnMPDefs
import Weak.Prom.RefTests

namespace Weak.Prom.Own.MPL

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Ref (Instr Test two64)
open PLabel

/-! ## 1. The test -/

def X : Int := (Weak.Prom.Ref.Lit.X : Int)
def Y : Int := (Weak.Prom.Ref.Lit.Y : Int)

/-- MP with ownership transfer (G4 (2)), the plan's text with 8-byte accesses. -/
def mpT : Test :=
  { harts := [[Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8],
              [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.ld 7 8]]
    regs0 := [[(5, 42), (6, Weak.Prom.Ref.Lit.X), (7, 1), (8, Weak.Prom.Ref.Lit.Y)],
              [(6, Weak.Prom.Ref.Lit.Y), (8, Weak.Prom.Ref.Lit.X)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

/-- The test's image (every byte 0). -/
abbrev mpImg : Image := testImg mpT

theorem mpImg_zero (a : Int) : mpImg a = some 0 := by
  simp [mpImg, testImg, Test.imgF, mpT, bv8]

/-- H0's `sd x` message and `sd flag` message. -/
def xMsg : PMsg := ⟨X, toBytes 42 8, some 0, .plain⟩
def fMsg : PMsg := ⟨Y, toBytes 1 8, some 0, .plain⟩

/-- THE MP SPEC on H1's final registers: `x5 = 1 → x7 = 42`. -/
def mpSpec (g : List Nat) : Prop := (g[5]?).getD 0 = 1 → (g[7]?).getD 0 = 42

/-! ## 2. Footprints and the protocol -/

/-- Message `t` writes one of x's 8 bytes. -/
def wrX (M : List PMsg) (t : Nat) : Prop := ∃ j : Nat, j < 8 ∧ wrA M t (X + j)
/-- Message `t` writes one of flag's 8 bytes. -/
def wrF (M : List PMsg) (t : Nat) : Prop := ∃ j : Nat, j < 8 ∧ wrA M t (Y + j)

/-- The 8 bytes of x at timestamp `t` are those of `v`. -/
def xVal (img : Image) (M : List PMsg) (t v : Nat) : Prop :=
  ∀ j : Nat, j < 8 → memByte img M t (X + j) = (toBytes v 8)[j]?

/-- x's ownership record: holder, tenure start, latest returned x-message, its value. -/
structure XRec where
  hold : Option Nat
  tstart : Nat
  tstar : Nat
  v : Nat
  deriving DecidableEq

/-- THE PROTOCOL STATE (OwnMPDefs.lean `mpOk`, 8-byte footprints). -/
def mpOk (img : Image) (M : List PMsg) (σ : OSt (List Nat)) (D : Nat → Prop) (rec : XRec) (f : Option Nat)
    (bad : Bool) : Prop :=
  (∀ a t, t ∈ σ.pr a → 1 ≤ t ∧ t ≤ σ.n ∧ au M t = some a) ∧
  (∀ t, D t → 1 ≤ t ∧ t ≤ σ.n ∧ ∃ a, au M t = some a ∧ t ∈ σ.pr a) ∧
  (bad = true → ∃ t, D t) ∧
  (rec.tstar ≤ σ.n ∧ xVal img M rec.tstar rec.v ∧ rec.tstart ≤ σ.n ∧
    ∀ t, rec.tstar < t → t ≤ σ.n → wrX M t →
      D t ∨ (rec.hold = au M t ∧ rec.tstart < t ∧ ∃ a, au M t = some a ∧ t ∈ σ.pr a) ∨
      (au M t = some 0 ∧ (∃ r, f = some r ∧ t ≤ r) ∧ t ∈ σ.pr 0)) ∧
  (∀ t, 1 ≤ t → t ≤ σ.n → wrF M t → D t ∨ f = some t) ∧
  (∀ r, f = some r → 1 ≤ r ∧ r ≤ σ.n ∧ M[r - 1]? = some fMsg) ∧
  (∀ g, σ.done 1 = some g → mpSpec g ∨ bad = true)

/-! ## 3. Pure facts -/

theorem xMsg_byte (j : Nat) (hj : j < 8) : xMsg.byteAt (X + j) = (toBytes 42 8)[j]? := by
  simp only [PMsg.byteAt, xMsg]
  rw [if_pos (by omega)]
  congr 1; omega

theorem fMsg_byte (j : Nat) (hj : j < 8) : fMsg.byteAt (Y + j) = (toBytes 1 8)[j]? := by
  simp only [PMsg.byteAt, fMsg]
  rw [if_pos (by omega)]
  congr 1; omega

theorem xMsg_not_Y (j : Nat) : xMsg.byteAt (Y + j) = none := by
  simp only [PMsg.byteAt, xMsg, X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]
  rw [if_pos (by omega)]
  apply List.getElem?_eq_none
  simp [toBytes, Weak.Prom.Ref.byteList]; omega

theorem fMsg_not_X (j : Nat) (hj : j < 8) : fMsg.byteAt (X + j) = none := by
  simp only [PMsg.byteAt, fMsg, X, Y, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]
  rw [if_neg (by omega)]

theorem toBytes_get (v j : Nat) (hj : j < 8) : ∃ b, (toBytes v 8)[j]? = some b :=
  ⟨_, List.getElem?_eq_getElem (by simp [toBytes, Weak.Prom.Ref.byteList]; omega)⟩

theorem relPrG {V : Type} {σ : OSt V} {h : Nat} (hle : ∀ t, t ∈ σ.pr h → t ≤ σ.n) :
    upd σ.pr h (({σ.n + 1} ∪ σ.pr h) \ {σ.n + 1}) = σ.pr := by
  funext j
  by_cases e : j = h
  · subst e
    rw [upd_eq]
    apply setEq.2
    intro t
    rw [elemOfDifference, elemOfUnion, elemOfSingleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
    · intro h1
      exact ⟨.inr h1, fun e => by have := hle t h1; omega⟩
  · rw [upd_ne _ _ e]

/-- A byte of a list of answers satisfying `bytesAll`. -/
theorem bytesAll_get {P : Int → Nat → BitVec 8 → Prop} :
    ∀ {a : Int} {tvs : List (Nat × BitVec 8)}, bytesAll P a tvs →
      ∀ (j : Nat) {t : Nat} {v : BitVec 8}, tvs[j]? = some (t, v) → P (a + j) t v
  | _, [], _, j, _, _, hj => by cases hj
  | a, (t0, v0) :: r, h, 0, t, v, hj => by
    simp at hj; obtain ⟨rfl, rfl⟩ := hj; simpa using h.1
  | a, (t0, v0) :: r, h, j + 1, t, v, hj => by
    have := bytesAll_get h.2 j (by simpa using hj)
    have e : a + 1 + (j : Int) = a + ((j + 1 : Nat) : Int) := by push_cast; omega
    rw [e] at this; exact this

/-- **ONE BYTE OF A LOAD** against the prefix `M.take n` (machine v2's `loadOk`, M9), without the invalidate
clause (`invalFree`, R-b5): the value is the memory's at its timestamp `t ≤ n`, and no write to the byte lies in
`(t, vpre]`. -/
theorem loadOk_byte {img : Image} {M : List PMsg} {n : Nat} {ws : PState} {vpre : Nat} {base : Int}
    {tvs : List (Nat × BitVec 8)} (hinv : invalFree M) (h : loadOk img (M.take n) ws vpre base tvs) {j t : Nat}
    {v : BitVec 8} (hj : tvs[j]? = some (t, v)) :
    memByte img M t (base + j) = some v ∧ t ≤ n ∧ ¬ writesIn (M.take n) (base + j) t vpre := by
  obtain ⟨hmb, hw⟩ := bytesAll_get h j hj
  obtain ⟨hmb', htn⟩ := memByte_take hmb
  refine ⟨hmb', htn, ?_⟩
  rcases hw with hw | hw
  · intro hc; apply hw; refine PF.writesIn_mono hc ?_; split <;> omega
  · obtain ⟨ti, hc, _⟩ := hw
    obtain ⟨m, k, len, hm, hcl, hk, hle1, hle2⟩ := hc
    exact absurd ⟨m, k, len, take_get hm, hcl, hk, hle1, hle2⟩ (hinv ti _)

/-- The register value of an 8-byte signed load. -/
def val8 (tvs : List (Nat × BitVec 8)) : Nat := PF.ldVal true 8 tvs % two64

theorem val8_b0 {t : Nat} {b : BitVec 8} {r : List (Nat × BitVec 8)} (h : val8 ((t, b) :: r) = 1) : b = 1 := by
  have hb := b.isLt
  have e : PF.ldVal true 8 ((t, b) :: r) = b.toNat + 256 * ofBytes (r.map Prod.snd) := by
    simp [PF.ldVal, Weak.Prom.Ref.sext, ofBytes, Weak.Prom.Ref.bytesVal]
  unfold val8 at h
  rw [e] at h
  apply BitVec.eq_of_toNat_eq
  show b.toNat = 1
  simp only [two64] at h
  omega

theorem val8_42 {tvs : List (Nat × BitVec 8)} (h : tvs.map Prod.snd = toBytes 42 8) : val8 tvs = 42 := by
  simp only [val8, PF.ldVal, if_true, h]; decide

theorem map_snd_of {tvs : List (Nat × BitVec 8)} {d : List (BitVec 8)} (hl : tvs.length = d.length)
    (h : ∀ j, j < d.length → ∀ t b, tvs[j]? = some (t, b) → d[j]? = some b) : tvs.map Prod.snd = d := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map]
  by_cases hj : j < d.length
  · obtain ⟨⟨t, b⟩, htb⟩ : ∃ tb, tvs[j]? = some tb := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [htb, h j hj t b htb]; rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl

/-! ## 4. The protocol steps -/

section steps

variable {img : Image} {M : List PMsg}

/-- THE AGENT OBLIGATION, pure part: appending `M[n]` keeps the protocol (an x-message of the holder is backed; any
other x-message and every flag message is dead). -/
theorem mpOk_agent {σ σ' : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad : Bool}
    (hok : mpOk img M σ D rec f bad) (ha : agentStep (litOW img M) σ σ') : ∃ D', mpOk img M σ' D' rec f bad := by
  obtain ⟨i, hn, hau, rfl⟩ := ha
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hcell, hf, hdone⟩ := hok
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
  refine ⟨D', ?_, ?_, ?_, ⟨by simp only; omega, hx2, by simp only; omega, ?_⟩, ?_, ?_, hdone⟩
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
  · intro t h1 h2 h3
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

/-- THE FINAL EXTRACTION: at the end of a valid run every promise set is empty, so no message is dead, `bad` is
false, and H1's registers meet the spec. -/
theorem mpOk_final {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad : Bool}
    (hok : mpOk img M σ D rec f bad) (hpr : ∀ h, σ.pr h = ∅) : ∀ g, σ.done 1 = some g → mpSpec g := by
  intro g hg
  obtain ⟨_, hD, hbad, _, _, _, hdone⟩ := hok
  rcases hdone g hg with h | h
  · exact h
  · obtain ⟨t, ht⟩ := hbad h
    obtain ⟨_, _, a, _, ha⟩ := hD t ht
    rw [hpr a] at ha
    exact absurd ha notElemOfEmpty

theorem mpOk_setBad {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad : Bool} {t : Nat}
    (hok : mpOk img M σ D rec f bad) (ht : D t) : mpOk img M σ D rec f true := by
  obtain ⟨hpr, hD, _, hx, hcell, hf, _⟩ := hok
  exact ⟨hpr, hD, fun _ => ⟨t, ht⟩, hx, hcell, hf, fun _ _ => .inr rfl⟩

/-- READING A LATER X-MESSAGE marks it dead (it is pending: dead, backed or leftover), so `bad`. -/
theorem mpOk_markX {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad : Bool} {t : Nat}
    (hok : mpOk img M σ D rec f bad) (h1 : rec.tstar < t) (h2 : t ≤ σ.n) (h3 : wrX M t) :
    ∃ D', mpOk img M σ D' rec f true := by
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hcell, hf, hdone⟩ := hok
  have key : ∃ a, au M t = some a ∧ t ∈ σ.pr a := by
    rcases hx4 t h1 h2 h3 with u | ⟨_, _, a, u3, u4⟩ | ⟨u1, _, u3⟩
    · obtain ⟨_, _, a, u3, u4⟩ := hD t u; exact ⟨a, u3, u4⟩
    · exact ⟨a, u3, u4⟩
    · exact ⟨0, u1, u3⟩
  obtain ⟨a, ha, hta⟩ := key
  refine ⟨fun t' => D t' ∨ t' = t, hpr, fun t' ht' => ?_, fun _ => ⟨t, .inr rfl⟩,
    ⟨hx1, hx2, hx3, fun t' u1 u2 u3 => ?_⟩, fun t' u1 u2 u3 => ?_, hf, fun _ _ => .inr rfl⟩
  · rcases ht' with ht' | rfl
    · exact hD t' ht'
    · exact ⟨by omega, h2, a, ha, hta⟩
  · rcases hx4 t' u1 u2 u3 with u | u | u
    · exact .inl (.inl u)
    · exact .inr (.inl u)
    · exact .inr (.inr u)
  · rcases hcell t' u1 u2 u3 with u | u
    · exact .inl (.inl u)
    · exact .inr u

/-- H0's `sd x` (release-class: its first write), appended in place: x's latest message. -/
theorem h0_x {σ : OSt (List Nat)} {D : Nat → Prop} {bad : Bool} (hok : mpOk img M σ D ⟨some 0, 0, 0, 0⟩ none bad)
    (hM : M[σ.n]? = some xMsg) : mpOk img M { σ with n := σ.n + 1 } D ⟨some 0, 0, σ.n + 1, 42⟩ none bad := by
  obtain ⟨hpr, hD, hbad, _, hcell, _, hdone⟩ := hok
  refine ⟨fun a t ht => ?_, fun t ht => ?_, hbad,
    ⟨Nat.le_refl _, fun j hj => ?_, Nat.zero_le _, fun t h1 h2 _ => by simp only at h1 h2; omega⟩,
    fun t h1 h2 h3 => ?_, fun r hr => (by cases hr), hdone⟩
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

/-- H0's `sd flag` after `fence rw,w` (release-class), appended in place: THE DEPOSIT — x's record goes to "no
holder" (H0's pending x-messages become leftovers), flag's cell records the release. -/
theorem h0_f {σ : OSt (List Nat)} {D : Nat → Prop} {bad : Bool} {tsx : Nat}
    (hok : mpOk img M σ D ⟨some 0, 0, tsx, 42⟩ none bad) (hM : M[σ.n]? = some fMsg) :
    tsx < σ.n + 1 ∧ mpOk img M { σ with n := σ.n + 1 } D ⟨none, σ.n + 1, tsx, 42⟩ (some (σ.n + 1)) bad := by
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hcell, hf, hdone⟩ := hok
  have hnotX : ¬ wrX M (σ.n + 1) := by
    rintro ⟨j, hj, m, hm', hb⟩
    simp only [Nat.add_sub_cancel] at hm'
    rw [hM] at hm'; cases hm'
    rw [fMsg_not_X j hj] at hb; cases hb
  refine ⟨by simp only at hx1; omega, fun a t ht => ?_, fun t ht => ?_, hbad,
    ⟨by simp only at hx1 ⊢; omega, hx2, Nat.le_refl _, fun t h1 h2 h3 => ?_⟩, fun t h1 h2 h3 => ?_,
    fun r hr => ?_, hdone⟩
  · obtain ⟨u1, u2, u3⟩ := hpr a t ht; exact ⟨u1, by simp only; omega, u3⟩
  · obtain ⟨u1, u2, u3⟩ := hD t ht; exact ⟨u1, by simp only; omega, u3⟩
  · by_cases e2 : t = σ.n + 1
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

/-- H1's CLAIM: the designated claimant takes x's record out of the cell (no holder → holder H1, tenure now). -/
theorem h1_claim {σ : OSt (List Nat)} {D : Nat → Prop} {bad : Bool} {r tsx : Nat} {f : Option Nat}
    (hok : mpOk img M σ D ⟨none, r, tsx, 42⟩ f bad) : mpOk img M σ D ⟨some 1, σ.n, tsx, 42⟩ f bad := by
  obtain ⟨hpr, hD, hbad, ⟨hx1, hx2, hx3, hx4⟩, hcell, hf, hdone⟩ := hok
  refine ⟨hpr, hD, hbad, ⟨hx1, hx2, Nat.le_refl _, fun t h1 h2 h3 => ?_⟩, hcell, hf, hdone⟩
  rcases hx4 t h1 h2 h3 with u | ⟨u1, _, a, u3, _⟩ | u
  · exact .inl u
  · simp only at u1; rw [u3] at u1; cases u1
  · exact .inr (.inr u)

/-- **H1's READ OF ONE BYTE OF x** above the latest x-message `tstar`'s floor: its byte, or a later x-message. -/
theorem x_byte {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad : Bool}
    (hok : mpOk img M σ D rec f bad) (h1 : 1 ≤ rec.tstar) {j : Nat} (hj : j < 8) {t P : Nat} {b : BitVec 8}
    (hmb : memByte img M t (X + j) = some b) (htn : t ≤ σ.n) (hP : rec.tstar ≤ P)
    (hnw : ¬ writesIn (M.take σ.n) (X + j) t P) : (toBytes rec.v 8)[j]? = some b ∨ (rec.tstar < t ∧ wrX M t) := by
  obtain ⟨_, _, _, ⟨hx1, hx2, _, _⟩, _, _, _⟩ := hok
  obtain ⟨b', hb'⟩ := toBytes_get rec.v j hj
  have hval := hx2 j hj
  rw [hb'] at hval
  have hwr : wrA M rec.tstar (X + j) := wrA_of_memByte h1 hval
  rcases Nat.lt_trichotomy t rec.tstar with hlt | heq | hgt
  · exfalso; apply hnw
    obtain ⟨m, hm, hb⟩ := hwr
    exact ⟨rec.tstar, hlt, hP, m, by rw [List.getElem?_take, if_pos (by omega)]; exact hm, hb⟩
  · subst heq; rw [hb', memByte_inj hmb hval]; exact .inl rfl
  · exact .inr ⟨hgt, j, hj, wrA_of_memByte (by omega) hmb⟩

/-- H1's FINAL VALUE: recorded with the spec or `bad`. -/
theorem h1_fin {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad : Bool} {g : List Nat}
    (hok : mpOk img M σ D rec f bad) (hg : mpSpec g ∨ bad = true) :
    mpOk img M { σ with done := upd σ.done 1 (some g) } D rec f bad := by
  obtain ⟨hpr, hD, hbad, hx, hcell, hf, _⟩ := hok
  refine ⟨hpr, hD, hbad, hx, hcell, hf, fun g' hg' => ?_⟩
  simp only [upd_eq] at hg'
  cases hg'
  exact hg

/-- H0's FINAL VALUE: nothing to record. -/
theorem h0_fin {σ : OSt (List Nat)} {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad : Bool} {g : List Nat}
    (hok : mpOk img M σ D rec f bad) : mpOk img M { σ with done := upd σ.done 0 (some g) } D rec f bad := by
  obtain ⟨hpr, hD, hbad, hx, hcell, hf, hdone⟩ := hok
  refine ⟨hpr, hD, hbad, hx, hcell, hf, fun g' hg' => ?_⟩
  simp only [upd_ne _ _ (show (1 : Nat) ≠ 0 by omega)] at hg'
  exact hdone g' hg'

/-- THE INITIAL PROTOCOL STATE: H0 holds x (the image's zero bytes), no release yet. -/
theorem mpOk_init (hz : ∀ a, img a = some 0) : mpOk img M σ0 (fun _ => False) ⟨some 0, 0, 0, 0⟩ none false := by
  refine ⟨fun a t ht => absurd ht notElemOfEmpty, fun t ht => False.elim ht, fun h => (by cases h),
    ⟨Nat.le_refl _, fun j hj => ?_, Nat.le_refl _, fun t h1 h2 _ => (by simp [σ0] at h2; omega)⟩,
    fun t h1 h2 _ => (by simp [σ0] at h2; omega), fun r hr => (by cases hr), fun g hg => (by simp [σ0] at hg)⟩
  simp only [memByte, hz]
  obtain ⟨b, hb⟩ := toBytes_get 0 j hj
  rw [hb]
  have : b = 0 := by
    have := hb; simp [toBytes, Weak.Prom.Ref.byteList, bv8] at this
    obtain ⟨_, h⟩ := this; exact h.symm
  rw [this]

end steps

end Weak.Prom.Own.MPL
