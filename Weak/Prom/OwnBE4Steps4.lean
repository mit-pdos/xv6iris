/-
Weak/Prom: **E-b4 — the protocol's step lemmas, part 4: the in-place transitions** (stage E-b4).

* `inv_rel` — an acquirer's in-place release: the lock is free again (a LIVE ZERO), the holder's unfulfilled field
  promises are dead;
* `inv_done` — an acquirer's in-place done byte: it leaves the round;
* `inv_h0fld` — hart 0's field store in the dead phase (kfree junk, then the initialisation 5);
* `inv_pub` — hart 0's in-place PUBLICATION: the DEFERRED DEPOSIT (b1-def) — the lock becomes free; hart 0's
  unfulfilled lock-word and field promises are dead;
* `inv_close` — hart 0's in-place CLOSING release, both done bytes seen: THE DEATH — the lifetime ends, hart 0
  keeps the field, its close floor is the release.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Steps3

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

theorem lkw_ovC {m : PMsg} (hp : m.pa = Lk) (hl : m.data.length = 4) : ¬ ov m Ct 8 := by
  simp [ov, hp, hl, Lk, Ct, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]
theorem lkw_ovF {m : PMsg} (hp : m.pa = Lk) (hl : m.data.length = 4) : ¬ ov m L1 4 := by
  simp [ov, hp, hl, Lk, L1, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Z]
theorem fw_ovL {m : PMsg} {o : Nat} (ho : o < 3) (hp : m.pa = L1 + o) (hl : m.data.length = 1) : ¬ ov m Lk 4 := by
  simp [ov, hp, hl, Lk, L1, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Z]; omega
theorem fw_ovC {m : PMsg} {o : Nat} (ho : o < 3) (hp : m.pa = L1 + o) (hl : m.data.length = 1) : ¬ ov m Ct 8 := by
  simp [ov, hp, hl, Ct, L1, Weak.Prom.Ref.Lit.Y, Weak.Prom.Ref.Lit.Z]; omega

section ip

variable {M : List PMsg} {σ : TSt (List Nat)} {S : PS} {ls : Nat → Loc}

/-- An in-place fulfil. -/
theorem ful_ip {o o' : OSt (List Nat)} (hw : WFp M o) {h ts : Nat} {rc : Prop} (hf : fulO M h o rc ts o')
    (hrc : rc) : ts = o.n + 1 ∧ o' = { o with n := o.n + 1 } := by
  rcases ful_cases hw hf with ⟨_, _, hn⟩ | ⟨e1, e2, _⟩
  · exact absurd hrc hn
  · exact ⟨e1, e2⟩

/-- A new in-place message is the only message between `n` and `n + 1`. -/
theorem ip_new {o : OSt (List Nat)} {m : PMsg} (hm : msgAt M (o.n + 1) = some m) :
    ∀ t m', t ≤ o.n + 1 → ¬ t ≤ o.n → msgAt M t = some m' → t = o.n + 1 ∧ m' = m := fun t m' h1 h2 h3 => by
  have : t = o.n + 1 := by omega
  subst this; rw [hm] at h3; exact ⟨rfl, (Option.some.inj h3).symm⟩

/-- An in-place message that does not write the lock's byte 0 leaves the hypothetical windows alone. -/
theorem tk2_ip {o : OSt (List Nat)} (hP : GoodP M o S ls) {m : PMsg} (hm : msgAt M (o.n + 1) = some m)
    (hnL : ¬ ov m Lk 4) {S' : PS} {ls' : Nat → Loc} (hls : S'.ls = S.ls) (hfr : ∀ h, fresh S' ls' h → fresh S ls h)
    (hnd : ∀ t, nd0 M S' t → nd0 M S t) :
    ∀ h t0, S'.ls ≠ .dead → fresh S' ls' h → nd0 M S' t0 → t0 ≤ o.n + 1 → clean M h t0 (o.n + 1 + 1) →
      S'.ls = .free ∨ ∃ u, S'.ls = .pulled h u := by
  intro h t0 a1 a2 a3 a4 a5
  rw [hls] at a1 ⊢
  by_cases hle : t0 ≤ o.n
  · exact hP.tk2 h t0 a1 (hfr h a2) (hnd t0 a3) hle (clean_le a5 (by omega))
  · exfalso
    have : t0 = o.n + 1 := by omega
    subst this
    obtain ⟨m0, hm0, _, _, hb⟩ := memByte_ov (by omega) a3.2
    rw [hm] at hm0; cases hm0
    exact hnL (ovL_b0 (by rw [hb]; rfl))

/-- The release's new state. -/
def relS (S : PS) (M : List PMsg) (o : OSt (List Nat)) (i : Nat) : PS :=
  { S with ls := .free, hold := none, Dc := fun x => S.Dc x ∨ (S.tstar < x ∧ x ≤ o.n ∧ pend M o x ∧
      au M x = some i ∧ ∃ m, msgAt M x = some m ∧ cmP3 m) }

/-- **THE RELEASE** of acquirer `i` (in place). -/
theorem inv_rel {i ts : Nat} {rc : Prop} {o' : OSt (List Nat)} {a c : List Dsrc} (hI : Inv M σ S ls)
    (hi : i = 1 ∨ i = 2) (hH : (ls i).st = .H2) (hf : fulO M i σ.o rc ts o') (hrc : rc)
    (hm : msgAt M ts = some ⟨Lk, toBytes 0 4, some i, .plain⟩) :
    ∃ S', Inv M (nxT σ i o' (LStore false false Lk (toBytes 0 4) a c, some ts)) S'
      (upd ls i { ls i with st := .R }) := by
  obtain ⟨hw, hI⟩ := hI
  have hi0 : i ≠ 0 := by omega
  obtain ⟨rfl, rfl⟩ := ful_ip hw hf hrc
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · have hrob := rob_ful (l0' := ls 0) hw hr hf hm (fun h => absurd (hw i _ h).2.1 (by omega))
      (fun hd => .inl ⟨hd, Nat.le_refl _⟩)
    exact ⟨S, wf_ip hw, .inr ⟨t', by rw [upd0 hi0]; exact hrob⟩⟩
  have hown := (hP.sA i hi).2.2.2.1 (.inr hH)
  obtain ⟨hhold, htst⟩ := hP.hpo i _ (.inr hown)
  have hnd : S.ls ≠ .dead := by rw [hown]; simp
  have hnD0 : ¬ isD (ls 0).st := fun d => hnd ((hP.s0.2.2.1).1 d)
  have e0 : ∀ j, j ≠ i → upd ls i { ls i with st := .R } j = ls j := fun j hj => upd_ne _ _ hj
  have ei : upd ls i { ls i with st := .R } i = { ls i with st := .R } := upd_eq _ _ _
  have hnew := ip_new (M := M) (o := σ.o) hm
  have hoth : ∀ j, (j = 1 ∨ j = 2) → j ≠ i → (ls j).st ≠ .H1 ∧ (ls j).st ≠ .H2 := fun j hj hne => by
    constructor <;> intro e <;> have := (hP.sA j hj).2.2.2.1 (by simp [e]) <;> rw [hown] at this <;>
      cases this <;> exact hne rfl
  have hfr : ∀ h, fresh (relS S M σ.o i) (upd ls i { ls i with st := .R }) h → fresh S ls h := by
    intro h hf'
    unfold fresh at hf' ⊢
    by_cases eh : h = i
    · subst eh; rw [ei] at hf'; rcases hf' with ⟨e, _⟩ | ⟨_, _, e | e⟩ <;> first | omega | cases e
    · rw [e0 h eh, e0 0 (by omega)] at hf'; exact hf'
  have hld : (ls i).ld = none := by
    cases e : (ls i).ld with
    | none => rfl
    | some _ => have := (hP.sA i hi).2.2.2.2 (by rw [e]; simp); rw [hH] at this; cases this
  refine ⟨relS S M σ.o i, wf_ip hw, .inl ⟨?_, ?_⟩⟩
  · constructor
    · intro t ht; rw [e0 0 (by omega)]; exact hP.dr t ht
    · intro t ht
      rcases ht with ht | ⟨_, _, c1, _, c2⟩
      · exact hP.dc t ht
      · exact ⟨c1, c2⟩
    · intro t a _ hh _; simp [relS] at hh
    · exact ⟨by have := hP.tsle.1; simp only [relS]; omega, by have := hP.tsle.2; simp only [relS]; omega⟩
    · exact hP.tsok
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · rcases hP.later t m' h1 e h3 h4 with c | c | ⟨b, b1, b2, b3, b4, b5⟩
        · exact .inl c
        · exact .inr (.inl (.inl c))
        · rw [hhold] at b1; cases b1
          exact .inr (.inl (.inr ⟨h1, e, b4, by rw [au_msg (by omega) h3, b2], m', h3, b5⟩))
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3; exact absurd h4 (lkw_ovC rfl (toBytes_len 0 4))
    · intro e; simp [relS] at e
    · intro _; rfl
    · intro h u e; rcases e with e | e <;> simp [relS] at e
    · intro _; exact hP.gdp hnd
    · rw [e0 0 (by omega)]
      refine ⟨fun e => absurd (by simp [isD, e]) hnD0, fun e => absurd (by rcases e with e | e <;> simp [isD, e]) hnD0,
        fun e => absurd (by simp [isD, e]) hnD0⟩
    · intro h u e; simp [relS] at e
    · intro h u e; simp [relS] at e
    · intro j hj hj1
      by_cases ej : j = i
      · subst ej; rw [ei] at hj1; cases hj1
      · rw [e0 j ej] at hj1; exact absurd hj1 (hoth j hj ej).1
    · intro e; rw [e0 0 (by omega)] at e
      have := hP.s0.2.2.2.2.2.1 e; rw [hown] at this; cases this; omega
    · intro h u e; rcases e with e | e <;> simp [relS] at e
    · intro h ts t0 a1 a2 a3 a4 a5 a6 a7 a8
      obtain ⟨u, _, e⟩ := hP.tk1 h ts t0 hnd (hfr h a2) a3 a4 a5 ⟨a6.1, a6.2⟩ a7 a8
      rw [hown] at e; cases e
    · intro h t0 _ _ _ _ _; exact .inl rfl
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · exact hP.fl t m' h1 e h3 h4
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3; exact absurd h4 (lkw_ovF rfl (toBytes_len 0 4))
    · intro k hk; exact ⟨(hP.pubk k hk).1, fun _ => by simp [relS]⟩
    · intro j k hj hk
      by_cases ej : j = i
      · subst ej; rw [ei]; exact hP.dnk j k hj hk
      · rw [e0 j ej]; exact hP.dnk j k hj hk
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
      rw [e0 0 (by omega)]
      refine ⟨b1, b2, ⟨fun d => absurd d hnD0, fun e => by simp [relS] at e⟩, b4, b5,
        fun e => absurd (b6 e) (by rw [hown]; simp; omega), fun d => ?_, fun d => ?_, b9⟩
      · by_cases e : (1 : Nat) = i
        · subst e; rw [ei]; exact b7 d
        · rw [e0 1 e]; exact b7 d
      · by_cases e : (2 : Nat) = i
        · subst e; rw [ei]; exact b8 d
        · rw [e0 2 e]; exact b8 d
    · intro j hj
      by_cases ej : j = i
      · subst ej; rw [ei]
        obtain ⟨b1, _, b3, _, _⟩ := hP.sA j hj
        obtain ⟨c1, _, c3⟩ := b3 (by rw [hH]; simp)
        refine ⟨.inl c1, .inr (.inr (.inr (.inr rfl))), fun _ => ⟨c1, by simp [relS], c3⟩,
          fun e => (by rcases e with e | e <;> cases e), fun e => (by simp only at e; rw [hld] at e; exact absurd rfl e)⟩
      · rw [e0 j ej]
        obtain ⟨b1, b2, b3, b4, b5⟩ := hP.sA j hj
        have hno : ¬ ((ls j).st = .H1 ∨ (ls j).st = .H2) := fun e => by
          rcases e with e | e
          · exact (hoth j hj ej).1 e
          · exact (hoth j hj ej).2 e
        refine ⟨?_, b2, fun e => ?_, fun e => absurd e hno, b5⟩
        · rcases b1 with b1 | ⟨b1, b1', _⟩
          · exact .inl b1
          · exact .inr ⟨b1, b1', by simp [relS]⟩
        · obtain ⟨c1, _, c3⟩ := b3 e; exact ⟨c1, by simp [relS], c3⟩
  · exact gT_snoc (h := i) hT (fun tvs ⟨_, e⟩ => by cases e) (.inr fun ts ⟨_, _, _, e⟩ => by
        simp only [Prod.mk.injEq, LStore.injEq] at e; simp [Lk, Ct, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at e)
      (by simpa using hld) (fun _ h => h) (fun _ h => .inl h) (fun _ _ _ _ _ => rfl)

/-- The done byte's new state. -/
def dnS (S : PS) (i k ts : Nat) : PS := { S with dnT := fun j k' => if j = i ∧ k' = k then ts else S.dnT j k' }

/-- **THE DONE BYTE** of acquirer `i` (in place). -/
theorem inv_done {i ts : Nat} {rc : Prop} {o' : OSt (List Nat)} {a c : List Dsrc} (hI : Inv M σ S ls)
    (hi : i = 1 ∨ i = 2) (hR : (ls i).st = .R) (hf : fulO M i σ.o rc ts o') (hrc : rc)
    (hm : msgAt M ts = some (dnM i (ls i).k)) :
    ∃ S', Inv M (nxT σ i o' (LStore false false (L1 + i) (toBytes (ls i).k 1) a c, some ts)) S'
      (upd ls i { ls i with k := (ls i).k + 1, st := .W }) := by
  obtain ⟨hw, hI⟩ := hI
  have hi0 : i ≠ 0 := by omega
  obtain ⟨rfl, rfl⟩ := ful_ip hw hf hrc
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · have hrob := rob_ful (l0' := ls 0) hw hr hf hm (fun h => absurd (hw i _ h).2.1 (by omega))
      (fun hd => .inl ⟨hd, Nat.le_refl _⟩)
    exact ⟨S, wf_ip hw, .inr ⟨t', by rw [upd0 hi0]; exact hrob⟩⟩
  obtain ⟨hA1, _, hA3, _, hA5⟩ := hP.sA i hi
  obtain ⟨hkl, hnd, hpp⟩ := hA3 (by rw [hR]; simp)
  have e0 : ∀ j, j ≠ i → upd ls i { ls i with k := (ls i).k + 1, st := .W } j = ls j := fun j hj => upd_ne _ _ hj
  have ei : upd ls i { ls i with k := (ls i).k + 1, st := .W } i = { ls i with k := (ls i).k + 1, st := .W } :=
    upd_eq _ _ _
  have hnew := ip_new (M := M) (o := σ.o) hm
  have hdl : (dnM i (ls i).k).pa = L1 + i ∧ (dnM i (ls i).k).data.length = 1 := ⟨rfl, toBytes_len _ 1⟩
  have hfr : ∀ h, fresh (dnS S i (ls i).k (σ.o.n + 1)) (upd ls i { ls i with k := (ls i).k + 1, st := .W }) h ↔
      fresh S ls h := by
    intro h; unfold fresh
    by_cases eh : h = i
    · subst eh; rw [ei, e0 0 (by omega), hR]; simp only [dnS]
      constructor
      · rintro (⟨e, _⟩ | ⟨_, e, _⟩); omega; omega
      · rintro (⟨e, _⟩ | ⟨_, _, e | e⟩); omega; cases e; cases e
    · rw [e0 h eh, e0 0 (by omega)]; rfl
  have hld : (ls i).ld = none := by
    cases e : (ls i).ld with
    | none => rfl
    | some _ => have := hA5 (by rw [e]; simp); rw [hR] at this; cases this
  have hown : ∀ h u, S.ls = .owned h u → h ≠ i := fun h u ho e => by
    subst e; rcases hP.hown h u ho with ⟨e, _⟩ | ⟨_, e | e, _⟩; omega; rw [hR] at e; cases e; rw [hR] at e; cases e
  refine ⟨dnS S i (ls i).k (σ.o.n + 1), wf_ip hw, .inl ⟨?_, ?_⟩⟩
  · constructor
    · intro t ht; rw [e0 0 (by omega)]; exact hP.dr t ht
    · exact hP.dc
    · intro t a ht hh ha
      by_cases ea : a = i
      · subst ea; rw [ei]; exact hP.dcH t _ ht hh ha
      · rw [e0 a ea]; exact hP.dcH t a ht hh ha
    · exact ⟨by have := hP.tsle.1; simp only [dnS]; omega, by have := hP.tsle.2; simp only [dnS]; omega⟩
    · exact hP.tsok
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · exact hP.later t m' h1 e h3 h4
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3; exact absurd h4 (fw_ovC (by omega) hdl.1 hdl.2)
    · intro e; rw [e0 0 (by omega)]; exact hP.hdead e
    · exact hP.hfree
    · exact hP.hpo
    · exact hP.gdp
    · rw [e0 0 (by omega)]; exact hP.h0f
    · exact hP.hpre
    · intro h u ho
      rw [e0 h (hown h u ho)]
      rcases hP.hown h u ho with ⟨rfl, b⟩ | b
      · rw [e0 0 (by omega)]; exact .inl ⟨rfl, b⟩
      · exact .inr b
    · intro j hj hj1
      by_cases ej : j = i
      · subst ej; rw [ei] at hj1; cases hj1
      · rw [e0 j ej] at hj1; exact hP.h1 j hj hj1
    · rw [e0 0 (by omega)]; exact hP.h0o
    · intro h u hu
      obtain ⟨b1, b2, b3, b4, b5⟩ := hP.lk h u hu
      refine ⟨b1, b2, by simp only; omega, b4, fun t m' c1 c2 c3 c4 => ?_⟩
      by_cases e : t ≤ σ.o.n
      · exact b5 t m' c1 e c3 c4
      · obtain ⟨rfl, rfl⟩ := hnew t m' c2 e c3; exact absurd c4 (fw_ovL (by omega) hdl.1 hdl.2)
    · intro h ts t0 a1 a2; exact hP.tk1 h ts t0 a1 ((hfr h).1 a2)
    · exact tk2_ip hP hm (fw_ovL (by omega) hdl.1 hdl.2) rfl (fun h a => (hfr h).1 a) (fun _ x => x)
    · intro t m' h1 h2 h3 h4
      by_cases e : t ≤ σ.o.n
      · rcases hP.fl t m' h1 e h3 h4 with c | c | ⟨j, k', hj, hk', hm'⟩
        · exact .inl c
        · exact .inr (.inl c)
        · refine .inr (.inr ⟨j, k', hj, ?_, hm'⟩)
          simp only [dnS]
          rw [if_neg]; exact hk'
          rintro ⟨rfl, rfl⟩
          have := hP.dnk j (ls j).k hj (by omega); omega
      · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3
        exact .inr (.inr ⟨i, (ls i).k, hi, by simp [dnS], rfl⟩)
    · exact hP.pubk
    · intro j k hj hk
      simp only [dnS] at hk
      by_cases ej : j = i
      · subst ej; rw [ei]; simp only
        by_cases ek : k = (ls j).k
        · omega
        · rw [if_neg (fun e => ek e.2)] at hk; have := hP.dnk j k hj hk; omega
      · rw [if_neg (fun e => ej e.1)] at hk; rw [e0 j ej]; exact hP.dnk j k hj hk
    · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
      rw [e0 0 (by omega)]
      refine ⟨b1, b2, b3, b4, b5, b6, fun d => ?_, fun d => ?_, b9⟩
      · by_cases e : (1 : Nat) = i
        · subst e; rw [ei]; simp only [dnS]; omega
        · rw [e0 1 e]; exact b7 d
      · by_cases e : (2 : Nat) = i
        · subst e; rw [ei]; simp only [dnS]; omega
        · rw [e0 2 e]; exact b8 d
    · intro j hj
      by_cases ej : j = i
      · subst ej; rw [ei]
        refine ⟨.inr ⟨by simp only [dnS]; omega, rfl, hnd⟩, .inl rfl, fun e => absurd rfl e,
          fun e => (by rcases e with e | e <;> cases e), fun e => (by simp only at e; rw [hld] at e; exact absurd rfl e)⟩
      · rw [e0 j ej]; exact hP.sA j hj
  · exact gT_snoc (h := i) hT (fun tvs ⟨_, e⟩ => by cases e) (.inr fun ts ⟨_, _, _, e⟩ => by
        simp only [Prod.mk.injEq, LStore.injEq] at e
        simp [L1, Ct, Weak.Prom.Ref.Lit.Z, Weak.Prom.Ref.Lit.Y] at e; omega)
      (by simpa using hld) (fun _ h => h) (fun _ h => h) (fun _ _ _ _ _ => rfl)

end ip

end Weak.Prom.OB.E4
