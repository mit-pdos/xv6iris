/-
Weak/Prom: **G4 (1a) on track (b): the initial state and THE PROMISE AGENT'S OBLIGATION with the (b1) PULL**
(stage S4b part 2; plan rev 7 §4 "Pull rule": "(b1) An acquiring AMO on lock L by hart h, promised at ts … h *pulls*
R into a ghost token `pulled(γ, ts)` … (b1-none) otherwise"; "(b2) A data message t to x by h … (b2-own) h holds the
write permission W(x) now, owned or pulled … (b2-none) otherwise t is *unbacked*").

`lk_agent`: appending `M[n]` (author `i`) keeps the protocol; the TOTAL case split (R-b2):
* acquire-shaped, lock FREE → THE PULL: R goes to `pulled(i, n+1)`, `i` becomes the counter's holder (b1);
* acquire-shaped, lock pulled/owned → an attempt, nothing pulled (b1-none);
* any other write to the lock byte → dead (releases are appended in place, never promised);
* a counter write → BACKED if `i` is the holder (b2-own), else dead (b2-none);
* anything else → untracked.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLockDefs

namespace Weak.Prom.Own.Lk

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y XRec xVal wrX toBytes_get relPrG)
open PLabel

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
              have := hwin u (by omega) (by omega) (acq_wrL u3)
              rw [au_acq u3] at this; cases this
              exact ⟨u, by omega, rfl⟩
            | owned a u =>
              rintro ⟨⟨u1, u2, u3, _⟩, u7, _⟩
              have := hwin u (by omega) (by omega) (acq_wrL u3)
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

end Weak.Prom.Own.Lk
