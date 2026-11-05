/-
Weak/Prom: **E-b4 — the protocol's step lemmas, part 5: hart 0's lifetime transitions** (stage E-b4).

* `inv_h0fld` — hart 0's field store in the dead phase (kfree junk, then the initialisation 5);
* `inv_pub` — hart 0's in-place PUBLICATION: THE DEFERRED DEPOSIT (plan §3 (b1-def)) — the lock becomes free;
  hart 0's unfulfilled lock-word promises become robust dead, its unfulfilled field promises dead;
* `inv_close` — hart 0's in-place CLOSING release with both done bytes seen: THE DEATH — the lifetime ends, hart 0
  keeps the field and the word, its close floor is the release.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Steps4

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach
open Weak.Prom.Own (OSt upd upd_eq upd_ne agentStep authorAt fulO)
open Weak.Prom.Own.MP (au)
open Weak.Prom.Own.Lk1c (pend)
open Weak.Prom.PF (Trace PEv msgAt tidAt)
open Weak.Prom.OA (Lk Ct isCLd isCSt clsB_iff clsB_of)
open Weak.Prom.OA.P (L1 cAt5)
open Weak.Prom.OA.C (Pc)
open Weak.Prom.OA.E2 (cmP3 isC3 gd noLd noLd_snoc latestC3)
open Weak.Prom.OA.E4 (q7 img7 q7_snoc)
open PLabel

section h0

variable {M : List PMsg} {σ : TSt (List Nat)} {S : PS} {ls : Nat → Loc}

theorem dead_W {o : OSt (List Nat)} (hP : GoodP M o S ls) (hd : S.ls = .dead) {j : Nat} (hj : j = 1 ∨ j = 2) :
    (ls j).st = .W ∧ (ls j).k = S.lt ∧ (ls j).ld = none := by
  obtain ⟨b1, _, b3, _, b5⟩ := hP.sA j hj
  have hW : (ls j).st = .W := Classical.byContradiction fun h => (b3 h).2.1 hd
  refine ⟨hW, ?_, ?_⟩
  · rcases b1 with e | ⟨_, _, e⟩; exact e; exact absurd hd e
  · cases e : (ls j).ld with
    | none => rfl
    | some _ => have := b5 (by rw [e]; simp); rw [hW] at this; cases this

/-- **HART 0's FIELD STORE IN THE DEAD PHASE**. -/
theorem inv_h0fld {ts v : Nat} {rc : Prop} {o' : OSt (List Nat)} {a c : List Dsrc} (hI : Inv M σ S ls)
    (hst : (ls 0).st = .D0 ∨ (ls 0).st = .D1) (hf : fulO M 0 σ.o rc ts o')
    (hm : msgAt M ts = some ⟨Ct, toBytes v 8, some 0, .plain⟩) (hu : (ls 0).u < ts)
    (hf1 : (ls 0).st = .D1 → (ls 0).f < ts) (hv : (ls 0).st = .D1 → v = 5) :
    ∃ S', Inv M (nxT σ 0 o' (LStore false false Ct (toBytes v 8) a c, some ts)) S'
      (upd ls 0 { ls 0 with st := if (ls 0).st = .D0 then .D1 else .D2, f := ts }) := by
  obtain ⟨hw, hI⟩ := hI
  have hc3 : cmP3 ⟨Ct, toBytes v 8, some 0, .plain⟩ := ⟨rfl, toBytes_len v 8, rfl, .inl rfl⟩
  have hok : okS ⟨Ct, toBytes v 8, some 0, .plain⟩ := ⟨0, by omega, rfl, .inr (.inr (.inl hc3))⟩
  have hnp : ¬ plk0 ⟨Ct, toBytes v 8, some 0, .plain⟩ := fun h => by
    have := h.2.1; simp [Lk, Ct, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at this
  have hD : isD (ls 0).st := by rcases hst with e | e <;> simp [isD, e]
  have hD' : isD (if (ls 0).st = .D0 then Stg.D1 else Stg.D2) := by split <;> simp [isD]
  obtain ⟨hpe, hpr, hts1, hnn, hw'⟩ := ful_post hw hf
  have ei : upd ls 0 { ls 0 with st := if (ls 0).st = .D0 then .D1 else .D2, f := ts } 0 =
      { ls 0 with st := if (ls 0).st = .D0 then .D1 else .D2, f := ts } := upd_eq _ _ _
  have e0 : ∀ j, j ≠ 0 → upd ls 0 { ls 0 with st := if (ls 0).st = .D0 then .D1 else .D2, f := ts } j = ls j :=
    fun j hj => upd_ne _ _ hj
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · have hrob := rob_ful (l0' := { ls 0 with st := if (ls 0).st = .D0 then .D1 else .D2, f := ts }) hw hr hf hm
      (fun _ => ⟨hok, fun _ h => absurd h hnp⟩) (fun _ => .inl ⟨hD, Nat.le_refl _⟩)
    exact ⟨S, hw', .inr ⟨t', by rw [ei]; exact hrob⟩⟩
  have hdd : S.ls = .dead := (hP.s0.2.2.1).1 hD
  obtain ⟨hhold, htst⟩ := hP.hdead hdd
  have hgt : S.tstar < ts := by
    rcases hst with e | e
    · have := hP.h0f.1 e; omega
    · have := hP.h0f.2.1 (.inl e); have := hf1 e; omega
  have hnDr : ¬ S.Dr ts := fun d => by
    obtain ⟨_, m', hm', hc⟩ := hP.dr ts d
    rw [hm] at hm'; cases hm'
    rcases hc with hc | ⟨hc, _⟩; exact hc hok; exact hnp hc
  have hnDc : ¬ S.Dc ts := fun d => by
    rcases hP.dcH ts 0 d hhold (by rw [au_msg hts1 hm]) with e | ⟨tvs', e1, _⟩ | ⟨e, _⟩
    · omega
    · rw [hP.s0.2.2.2.2.2.2.2.2] at e1; cases e1
    · exact e rfl
  have hnew : ∀ t m', t ≤ o'.n → ¬ t ≤ σ.o.n → msgAt M t = some m' → t = ts ∧ m' = ⟨Ct, toBytes v 8, some 0, .plain⟩ :=
    fun t m' h1 h2 h3 => by
      rcases hnn with ⟨e, _⟩ | ⟨e, rfl⟩
      · omega
      · have : t = σ.o.n + 1 := by omega
        subst this; rw [hm] at h3; exact ⟨rfl, (Option.some.inj h3).symm⟩
  refine ⟨{ S with tstar := ts }, hw', .inl ⟨?_, ?_⟩⟩
  · constructor
    · intro t ht; rw [ei]
      obtain ⟨b1, m', b2, b3⟩ := hP.dr t ht
      refine ⟨(hpe t).2 ⟨b1, fun e => hnDr (e ▸ ht)⟩, m', b2, ?_⟩
      rcases b3 with b3 | ⟨b3, b4⟩
      · exact .inl b3
      · refine .inr ⟨b3, .inr ?_⟩; rcases b4 with b4 | b4; exact absurd hD b4; exact b4
    · intro t ht; exact ⟨(hpe t).2 ⟨(hP.dc t ht).1, fun e => hnDc (e ▸ ht)⟩, (hP.dc t ht).2⟩
    · intro t a ht hh ha
      have : a = 0 := by rw [hhold] at hh; cases hh; rfl
      subst this
      rcases hP.dcH t 0 ht hhold ha with e | ⟨tvs', e1, _⟩ | ⟨e, _⟩
      · exact .inl e
      · rw [hP.s0.2.2.2.2.2.2.2.2] at e1; cases e1
      · exact absurd rfl e
    · exact ⟨by rcases hnn with ⟨e, h2, _⟩ | ⟨e, h2⟩ <;> simp only <;> omega,
        by have := hP.tsle.2; rcases hnn with ⟨e, _⟩ | ⟨e, _⟩ <;> simp only <;> omega⟩
    · exact .inr ⟨_, hm, hc3⟩
    · intro t m' h1 h2 h3 h4
      have h1' : ts < t := h1
      have htn : t ≤ σ.o.n := by
        by_cases e : t ≤ σ.o.n; exact e
        exact absurd (hnew t m' h2 e h3).1 (by omega)
      rcases hP.later t m' (by omega) htn h3 h4 with c | c | ⟨b, b1, b2, b3, b4, b5⟩
      · exact .inl c
      · exact .inr (.inl c)
      · exact .inr (.inr ⟨b, b1, b2, b3, (hpe t).2 ⟨b4, by omega⟩, b5⟩)
    · intro _; rw [ei]; exact ⟨hhold, htst⟩
    · intro e; rw [hdd] at e; cases e
    · intro h u e; rcases e with e | e <;> rw [hdd] at e <;> cases e
    · intro e; exact absurd hdd e
    · rw [ei]; simp only
      refine ⟨fun e => ?_, fun _ => trivial, fun e => ?_⟩
      · split at e <;> cases e
      · split at e
        · cases e
        · rename_i hne
          have h1 : (ls 0).st = .D1 := by rcases hst with e' | e'; exact absurd e' hne; exact e'
          rw [hv h1] at hm; simp only [cAt5]; exact hm
    · intro h u e; rw [hdd] at e; cases e
    · intro h u e; rw [hdd] at e; cases e
    · intro j hj hj1
      rw [e0 j (by omega)] at hj1; rw [(dead_W hP hdd hj).1] at hj1; cases hj1
    · rw [ei]; simp only; intro e; split at e <;> cases e
    · intro h u e; rcases e with e | e <;> rw [hdd] at e <;> cases e
    · intro h ts' t0 a1; exact absurd hdd a1
    · intro h t0 a1; exact absurd hdd a1
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · exact hP.fl t m' h1 e h3 h4
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3; exact absurd h4 (c3_ovF hc3)
    · exact hP.pubk
    · intro j k hj hk; rw [e0 j (by omega)]; exact hP.dnk j k hj hk
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
      rw [ei, e0 1 (by omega), e0 2 (by omega)]
      refine ⟨b1, b2, ⟨fun _ => hdd, fun _ => hD'⟩, .inl hD', fun e => ?_, fun e => ?_, b7, b8, b9⟩
      · simp only at e; rcases e with e | e <;> split at e <;> cases e
      · simp only at e; split at e <;> cases e
    · intro j hj; rw [e0 j (by omega)]; exact hP.sA j hj
  · exact gT_snoc (h := 0) hT (fun tvs ⟨_, e⟩ => by cases e) (.inl rfl) (by simp only; exact hP.s0.2.2.2.2.2.2.2.2)
      (fun _ h => h) (fun _ h => h) (fun j tvs hj _ hl => absurd hl (by rw [(dead_W hP hdd hj).2.2]; simp))

/-- A point update. -/
def updK (f : Nat → Nat) (k v : Nat) : Nat → Nat := fun k' => if k' = k then v else f k'

/-- The publication's new state: THE DEFERRED DEPOSIT. -/
def pubS (S : PS) (M : List PMsg) (o : OSt (List Nat)) (ts : Nat) : PS where
  lt := S.lt
  ls := .free
  hold := none
  tst := S.tst
  tstar := S.tstar
  Dr x := S.Dr x ∨ (x ≤ o.n ∧ pend M o x ∧ ∃ m, msgAt M x = some m ∧ plk0 m)
  Dc x := S.Dc x ∨ (S.tstar < x ∧ x ≤ o.n ∧ pend M o x ∧ au M x = some 0 ∧ ∃ m, msgAt M x = some m ∧ cmP3 m)
  pubT := updK S.pubT S.lt ts
  dnT := S.dnT

/-- **THE PUBLICATION** (hart 0, in place). -/
theorem inv_pub {ts : Nat} {rc : Prop} {o' : OSt (List Nat)} {a c : List Dsrc} (hI : Inv M σ S ls)
    (hD2 : (ls 0).st = .D2) (hf : fulO M 0 σ.o rc ts o') (hrc : rc) (hm : msgAt M ts = some (pubM (ls 0).k)) :
    ∃ S', Inv M (nxT σ 0 o' (LStore false false L1 (toBytes (ls 0).k 1) a c, some ts)) S'
      (upd ls 0 { ls 0 with st := .P, p := ts, d1 := false, d2 := false }) := by
  obtain ⟨hw, hI⟩ := hI
  obtain ⟨rfl, rfl⟩ := ful_ip hw hf hrc
  have ei : upd ls 0 { ls 0 with st := .P, p := σ.o.n + 1, d1 := false, d2 := false } 0 =
      { ls 0 with st := .P, p := σ.o.n + 1, d1 := false, d2 := false } := upd_eq _ _ _
  have e0 : ∀ j, j ≠ 0 → upd ls 0 { ls 0 with st := .P, p := σ.o.n + 1, d1 := false, d2 := false } j = ls j :=
    fun j hj => upd_ne _ _ hj
  have hnP : ¬ isD Stg.P := by simp [isD]
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · have hrob := rob_ful (l0' := { ls 0 with st := .P, p := σ.o.n + 1, d1 := false, d2 := false }) hw hr hf hm
      (fun h => absurd (hw 0 _ h).2.1 (by omega)) (fun h => absurd h hnP)
    exact ⟨S, wf_ip hw, .inr ⟨t', by rw [ei]; exact hrob⟩⟩
  have hdd : S.ls = .dead := (hP.s0.2.2.1).1 (by simp [isD, hD2])
  obtain ⟨hhold, htst⟩ := hP.hdead hdd
  have hk : (ls 0).k = S.lt := hP.s0.1
  have hnew := ip_new (M := M) (o := σ.o) hm
  have hdl : (pubM (ls 0).k).pa = L1 + ((0 : Nat) : Int) ∧ (pubM (ls 0).k).data.length = 1 :=
    ⟨by simp [pubM], toBytes_len _ 1⟩
  have hp0 : S.pubT S.lt = 0 := by
    rcases Nat.eq_zero_or_pos (S.pubT S.lt) with h | h
    · exact h
    · exact absurd hdd ((hP.pubk S.lt (by omega)).2 rfl)
  refine ⟨pubS S M σ.o (σ.o.n + 1), wf_ip hw, .inl ⟨?_, ?_⟩⟩
  · constructor
    · intro t ht; rw [ei]
      rcases ht with ht | ⟨_, b1, m', b2, b3⟩
      · obtain ⟨b1, m', b2, b3⟩ := hP.dr t ht
        refine ⟨b1, m', b2, ?_⟩
        rcases b3 with b3 | ⟨b3, _⟩
        · exact .inl b3
        · exact .inr ⟨b3, .inl hnP⟩
      · exact ⟨b1, m', b2, .inr ⟨b3, .inl hnP⟩⟩
    · intro t ht
      rcases ht with ht | ⟨_, _, c1, _, c2⟩
      · exact hP.dc t ht
      · exact ⟨c1, c2⟩
    · intro t a _ hh _; simp [pubS] at hh
    · exact ⟨by have := hP.tsle.1; simp only [pubS]; omega, by have := hP.tsle.2; simp only [pubS]; omega⟩
    · exact hP.tsok
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · rcases hP.later t m' h1 e h3 h4 with c | c | ⟨b, b1, b2, b3, b4, b5⟩
        · exact .inl (.inl c)
        · exact .inr (.inl (.inl c))
        · rw [hhold] at b1; cases b1
          exact .inr (.inl (.inr ⟨h1, e, b4, by rw [au_msg (by omega) h3, b2], m', h3, b5⟩))
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3; exact absurd h4 (fw_ovC (by omega) hdl.1 hdl.2)
    · intro e; simp [pubS] at e
    · intro _; rfl
    · intro h u e; rcases e with e | e <;> simp [pubS] at e
    · intro _
      have h5 := hP.h0f.2.2 hD2
      exact ⟨by show Weak.Prom.OA.clsB cmP3 M S.tstar = true; rw [clsB_of h5]
                exact decide_eq_true ⟨rfl, toBytes_len 5 8, rfl, .inl rfl⟩, .inl h5⟩
    · rw [ei]; simp only
      exact ⟨fun e => (by cases e), fun e => (by rcases e with e | e <;> cases e), fun e => (by cases e)⟩
    · intro h u e; simp [pubS] at e
    · intro h u e; simp [pubS] at e
    · intro j hj hj1; rw [e0 j (by omega), (dead_W hP hdd hj).1] at hj1; cases hj1
    · rw [ei]; intro e; cases e
    · intro h u e; rcases e with e | e <;> simp [pubS] at e
    · intro h ts' t0 _ _ a3 a4
      have e3 : (pubS S M σ.o (σ.o.n + 1)).pubT (pubS S M σ.o (σ.o.n + 1)).lt = σ.o.n + 1 := by
        simp [pubS, updK]
      have := (hw h ts' a4).2.1; omega
    · intro h t0 _ _ _ _ _; exact .inl rfl
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · rcases hP.fl t m' h1 e h3 h4 with c | ⟨k, hk', hm'⟩ | c
        · exact .inl (.inl c)
        · refine .inr (.inl ⟨k, ?_, hm'⟩)
          simp only [pubS, updK]; rw [if_neg]; exact hk'
          rintro rfl; rw [hp0] at hk'; omega
        · exact .inr (.inr c)
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3
        exact .inr (.inl ⟨S.lt, by simp [pubS, updK], by rw [hk]⟩)
    · intro k hk'
      simp only [pubS, updK] at hk' ⊢
      by_cases e : k = S.lt
      · subst e; exact ⟨Nat.le_refl _, fun _ => by simp⟩
      · rw [if_neg e] at hk'
        exact ⟨(hP.pubk k hk').1, fun e' => absurd e' e⟩
    · intro j k hj hk'; rw [e0 j (by omega)]; exact hP.dnk j k hj hk'
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
      rw [ei, e0 1 (by omega), e0 2 (by omega)]
      refine ⟨b1, b2, ⟨fun h => absurd h hnP, fun e => by simp [pubS] at e⟩, .inr (.inl rfl),
        fun _ => (by simp [pubS, updK]), fun e => (by cases e), fun e => (by cases e), fun e => (by cases e), b9⟩
    · intro j hj
      rw [e0 j (by omega)]
      obtain ⟨hW, hkj, hld⟩ := dead_W hP hdd hj
      refine ⟨.inl hkj, .inl hW, fun e => absurd hW e, fun e => ?_, fun e => absurd hld e⟩
      rcases e with e | e <;> rw [hW] at e <;> cases e
  · exact gT_snoc (h := 0) hT (fun tvs ⟨_, e⟩ => by cases e) (.inl rfl) (by simp only; exact hP.s0.2.2.2.2.2.2.2.2)
      (fun _ h => .inl h) (fun _ h => .inl h) (fun _ _ _ _ _ => rfl)

/-- Hart 0's record after its closing release. -/
abbrev closeL (l : Loc) (ts : Nat) : Loc := { l with k := l.k + 1, st := .D0, cf := ts, d1 := false, d2 := false }

/-- **THE CLOSING RELEASE** (hart 0, in place, both done bytes seen): THE DEATH of the lifetime. -/
theorem inv_close {ts : Nat} {rc : Prop} {o' : OSt (List Nat)} {a c : List Dsrc} (hI : Inv M σ S ls)
    (hH0 : (ls 0).st = .H0) (hd1 : (ls 0).d1 = true) (hd2 : (ls 0).d2 = true) (hk : (ls 0).k ≤ 2)
    (hf : fulO M 0 σ.o rc ts o') (hrc : rc) (hm : msgAt M ts = some ⟨Lk, toBytes 0 4, some 0, .plain⟩) :
    ∃ S', Inv M (nxT σ 0 o' (LStore false false Lk (toBytes 0 4) a c, some ts)) S'
      (upd ls 0 (closeL (ls 0) ts)) := by
  obtain ⟨hw, hI⟩ := hI
  obtain ⟨rfl, rfl⟩ := ful_ip hw hf hrc
  have ei : upd ls 0 (closeL (ls 0) (σ.o.n + 1)) 0 = closeL (ls 0) (σ.o.n + 1) := upd_eq _ _ _
  have e0 : ∀ j, j ≠ 0 → upd ls 0 (closeL (ls 0) (σ.o.n + 1)) j = ls j := fun j hj => upd_ne _ _ hj
  have hD0 : isD Stg.D0 := by simp [isD]
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · have hrob := rob_ful (l0' := closeL (ls 0) (σ.o.n + 1)) hw hr hf hm (fun h => absurd (hw 0 _ h).2.1 (by omega))
      (fun _ => .inr (by simp))
    exact ⟨S, wf_ip hw, .inr ⟨t', by rw [ei]; exact hrob⟩⟩
  have hown := hP.s0.2.2.2.2.2.1 hH0
  obtain ⟨hhold, htst⟩ := hP.hpo 0 _ (.inr hown)
  have hk' : (ls 0).k = S.lt := hP.s0.1
  have hnew := ip_new (M := M) (o := σ.o) hm
  have hacq : ∀ j, (j = 1 ∨ j = 2) → (ls j).k = S.lt + 1 ∧ (ls j).st = .W := fun j hj => by
    have hgt : S.lt < (ls j).k := by
      rcases hj with rfl | rfl
      · exact hP.s0.2.2.2.2.2.2.1 hd1
      · exact hP.s0.2.2.2.2.2.2.2.1 hd2
    rcases (hP.sA j hj).1 with e | ⟨e, e', _⟩
    · omega
    · exact ⟨e, e'⟩
  refine ⟨{ S with ls := .dead, lt := S.lt + 1 }, wf_ip hw, .inl ⟨?_, ?_⟩⟩
  · constructor
    · intro t ht; rw [ei]
      obtain ⟨b1, m', b2, b3⟩ := hP.dr t ht
      refine ⟨b1, m', b2, ?_⟩
      rcases b3 with b3 | ⟨b3, _⟩
      · exact .inl b3
      · exact .inr ⟨b3, .inr (by have := (pend_le hw b1).2; simp only; omega)⟩
    · exact hP.dc
    · intro t a ht hh ha
      by_cases ea : a = 0
      · subst ea; rw [ei]; exact hP.dcH t _ ht hh ha
      · rw [e0 a ea]; exact hP.dcH t a ht hh ha
    · exact ⟨by have := hP.tsle.1; simp only; omega, by have := hP.tsle.2; simp only; omega⟩
    · exact hP.tsok
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · exact hP.later t m' h1 e h3 h4
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3; exact absurd h4 (lkw_ovC rfl (toBytes_len 0 4))
    · intro _; rw [ei]; exact ⟨hhold, htst⟩
    · intro e; cases e
    · intro h u e; rcases e with e | e <;> cases e
    · intro e; exact absurd rfl e
    · rw [ei]; simp only
      exact ⟨fun _ => hP.h0o hH0, fun e => (by rcases e with e | e <;> cases e), fun e => (by cases e)⟩
    · intro h u e; cases e
    · intro h u e; cases e
    · intro j hj hj1; rw [e0 j (by omega), (hacq j hj).2] at hj1; cases hj1
    · rw [ei]; intro e; cases e
    · intro h u e; rcases e with e | e <;> cases e
    · intro h ts' t0 a1; exact absurd rfl a1
    · intro h t0 a1; exact absurd rfl a1
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · exact hP.fl t m' h1 e h3 h4
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3; exact absurd h4 (lkw_ovF rfl (toBytes_len 0 4))
    · intro k hk2
      obtain ⟨c1, _⟩ := hP.pubk k hk2
      exact ⟨by simp only; omega, fun e => by simp only at e; omega⟩
    · intro j k hj hk2; rw [e0 j (by omega)]; exact hP.dnk j k hj hk2
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
      rw [ei, e0 1 (by omega), e0 2 (by omega)]
      refine ⟨by simp only; omega, ⟨by simp only; omega, by simp only; omega⟩, ⟨fun _ => rfl, fun _ => hD0⟩,
        .inl hD0, fun e => (by rcases e with e | e <;> cases e), fun e => (by cases e), fun e => (by cases e),
        fun e => (by cases e), b9⟩
    · intro j hj
      rw [e0 j (by omega)]
      obtain ⟨hkj, hW⟩ := hacq j hj
      obtain ⟨_, _, _, _, b5⟩ := hP.sA j hj
      have hld : (ls j).ld = none := by
        cases e : (ls j).ld with
        | none => rfl
        | some _ => have := b5 (by rw [e]; simp); rw [hW] at this; cases this
      refine ⟨.inl (by simp only; omega), .inl hW, fun e => absurd hW e, fun e => ?_, fun e => absurd hld e⟩
      rcases e with e | e <;> rw [hW] at e <;> cases e
  · exact gT_snoc (h := 0) hT (fun tvs ⟨_, e⟩ => by cases e) (.inl rfl) (by simp only; exact hP.s0.2.2.2.2.2.2.2.2)
      (fun _ h => h) (fun _ h => h) (fun _ _ _ _ _ => rfl)

end h0

end Weak.Prom.OB.E4
