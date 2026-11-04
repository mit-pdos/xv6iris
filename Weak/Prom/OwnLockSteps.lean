/-
Weak/Prom: **G4 (1a) on track (b): the hart steps of the lock protocol** (stage S4b part 2; plan rev 7 §4 "Pull
rule" (b1): "In both cases h *pulls* R into a ghost token `pulled(γ, ts)`, which the AMO leaf consumes at execution.
The leaf keeps the statement 'amoswap.aq on L gives R'").

* `lk_acq` — THE AMO LEAF: an acquire AMO whose byte-0 answer is 0 from a live message CONSUMES the pull (or, in
  place on a free lock, takes R itself): R moves to the hart (`owned`); a nonzero answer gives up (phase 2); an
  answer 0 from a dead message makes the hart a rogue and spoils the protocol;
* `lk_ldc` — the holder's read of the counter: its latest message's value, or a later pending message (marked dead,
  `bad`);
* `lk_sdc` / `lk_sdcS` — the holder's store (a backed promise, or in place) becomes the counter's latest message and
  records the hart's read value; a store in spoiled mode;
* `lk_rel` / `lk_relS` — THE RELEASE, in place: R is DEPOSITED into a new live cell;
* `lk_fin`, `lk_final` — the end of a hart; the final extraction (mutual exclusion of the critical sections).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLockAgent

namespace Weak.Prom.Own.Lk

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y XRec xVal wrX toBytes_get relPrG)
open Weak.Prom.Ref (two64)
open PLabel

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
    (hwin : ∀ t, t0 < t → t < ts → wrL M t → au M t = some h) :
    (b0 ≠ 0 ∧ ∃ g', LkOk img M σ' g' ∧ g'.ph = upd g.ph h 2 ∧ g'.rds = g.rds ∧ g'.mark = g.mark ∧
        g'.spoil = g.spoil ∧ ((g'.ls = g.ls ∧ g'.cr = g.cr) ∨
          (g.spoil = false ∧ g.ls = .free ∧ ∃ u, g'.ls = .pulled h u))) ∨
    (∃ g', LkOk img M σ' g' ∧ g'.spoil = true ∧ g'.ph = upd g.ph h 3 ∧ g'.rds = g.rds ∧ g'.mark = g.mark ∧
        g'.cr = g.cr) ∨
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
      fun hh gg hg => .inr (.inl rfl), fun _ _ => rfl, fun _ _ _ => rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hb0 : b0 = 0
  · -- answer 0
    by_cases hsp : g.spoil = true
    · exact .inr (.inl (rogue (.inl hsp)))
    have hsp' : g.spoil = false := by simpa using hsp
    have hL := hok.lock hsp'
    have hC := hok.c hsp'
    by_cases hdead : 1 ≤ t0 ∧ g.Dl t0
    · exact .inr (.inl (rogue (.inr ⟨t0, hdead.2⟩)))
    have hnd : nd0 M g t0 := by
      by_cases e : t0 = 0
      · exact .inl e
      · have h1 : 1 ≤ t0 := by omega
        have hwr : wrL M t0 := wrA_of_memByte h1 hmb
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
          have := hwin u (by omega) (by omega) (acq_wrL u3)
          rw [au_acq u3] at this; cases this
          exact .inl ⟨u, by omega, rfl⟩
        | owned a u =>
          rintro ⟨⟨u1, u2, u3, _⟩, u7, _⟩
          have := hwin u (by omega) (by omega) (acq_wrL u3)
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
  · -- a nonzero answer: GIVE UP (phase 2)
    left
    refine ⟨hb0, ?_⟩
    by_cases hpf : ts = σ.n + 1 ∧ g.spoil = false ∧ g.ls = .free
    · obtain ⟨ets, hsp', hfree⟩ := hpf
      subst ets
      have hL := hok.lock hsp'
      have hC := hok.c hsp'
      have hls := hL.ls_ok; rw [hfree] at hls
      obtain ⟨f1, f2, f3, f4⟩ := hls
      let g' : LkS := { g with ls := .pulled h (σ.n + 1), ph := upd g.ph h 2, cr := { g.cr with hold := some h, tstart := σ.n + 1 } }
      refine ⟨g',
        ⟨hpr', hdl', hok.bad, hok.spoil, fun _ => ?_,
        fun _ => ful_cok hok hful hC hnX hph rfl rfl (uph 2) (.inr ⟨f2, rfl, rfl⟩),
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
          show upd g.ph h 2 a = 2; rw [uph 2 a hah]; exact this
      · refine ⟨⟨by show g.lc < σ.n + 1; have := hL.lc_le; omega, by omega, hM, fun t h1 h2 h3 => f1 t h1 (by omega) h3,
          rfl, rfl⟩, by show g.cr.tstar < σ.n + 1; have := hL.lc_le; omega, fun a => ?_⟩
        by_cases hah : a = h
        · subst hah; show upd g.ph _ 2 _ ≠ 1; simp [upd]
        · show upd g.ph h 2 a ≠ 1; rw [uph 2 a hah]; exact f4 a
      · exfalso
        have hh' : h' ≠ h := fun e => by subst e; change upd g.ph _ _ _ = 0 at hph'; simp [upd] at hph'
        have hph0 : g.ph h' = 0 := by rw [← uph 2 h' hh']; exact hph'
        obtain ⟨u', _, hu'⟩ := hL.taker h' ts' ((hpr h' ts').1 hts').1 hph0 hM' t0' ht0' hnd' hwin'
        rw [hfree] at hu'; cases hu'
    · refine ⟨{ g with ph := upd g.ph h 2 }, ⟨hpr', hdl', hok.bad, hok.spoil, fun hsp' => ?_,
        fun hsp' => ful_cok hok hful (hok.c hsp') hnX hph rfl rfl (uph 2) (.inl rfl),
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
          show upd g.ph h 2 a = 2; rw [uph 2 a hah]; exact this
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
          · subst hah; show upd g.ph _ 2 _ ≠ 1; simp [upd]
          · show upd g.ph h 2 a ≠ 1; rw [uph 2 a hah]; exact f4 a
        | pulled a u =>
          rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
          refine ⟨⟨u1, by omega, u3, u4, u5, u6⟩, u7, fun b => ?_⟩
          by_cases hbh : b = h
          · subst hbh; show upd g.ph _ 2 _ ≠ 1; simp [upd]
          · show upd g.ph h 2 b ≠ 1; rw [uph 2 b hbh]; exact u8 b
        | owned a u =>
          rintro ⟨⟨u1, u2, u3, u4, u5, u6⟩, u7, u8⟩
          have hah : a ≠ h := fun e => by subst e; rw [hph] at u7; cases u7
          refine ⟨⟨u1, by omega, u3, u4, u5, u6⟩, by show upd g.ph h 2 a = 1; rw [uph 2 a hah]; exact u7,
            fun b hb => ?_⟩
          by_cases hbh : b = h
          · subst hbh; show upd g.ph _ 2 _ ≠ 1; simp [upd]
          · show upd g.ph h 2 b ≠ 1; rw [uph 2 b hbh]; exact u8 b hb
      · have hh' : h' ≠ h := fun e => by subst e; change upd g.ph _ _ _ = 0 at hph'; simp [upd] at hph'
        have hph0 : g.ph h' = 0 := by rw [← uph 2 h' hh']; exact hph'
        exact hL.taker h' ts' ((hpr h' ts').1 hts').1 hph0 hM' t0' ht0' hnd' hwin'

end steps

end Weak.Prom.Own.Lk
