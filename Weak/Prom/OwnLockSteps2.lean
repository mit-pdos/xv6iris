/-
Weak/Prom: **G4 (1a) on track (b): the critical section, the release, the end** (stage S4b part 2; plan rev 7 §4
"Pull rule", "Points-to (b)").  See OwnLockSteps.lean for the AMO leaf.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLockSteps

namespace Weak.Prom.Own.Lk

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au memByte_take wrA_of_memByte memByte_inj take_get)
open Weak.Prom.Own.MPL (X Y XRec xVal wrX toBytes_get relPrG map_snd_of)
open Weak.Prom.Ref (two64)
open PLabel

section steps2

variable {img : Image} {M : List PMsg}

theorem specH_mono {gg : List Nat} {g g' : LkS} {h : Nat} (hr : ∀ a v, g.rds a = some v → g'.rds a = some v)
    (hb : g.bad = true → g'.bad = true) (hs : specH gg g h) : specH gg g' h := by
  rcases hs with u | u | ⟨v, u1, u2⟩
  · exact .inl u
  · exact .inr (.inl (hb u))
  · exact .inr (.inr ⟨v, hr h v u1, u2⟩)

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
        fun hh gg hg => .inr (.inl hbad), hok.ph3, fun _ _ _ => hbad⟩, hbad, hsp, rfl, rfl, rfl, rfl, rfl⟩
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
      fun hh gg hg => .inr (.inl rfl), hok.ph3, fun _ _ _ => rfl⟩,
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
      fun e => (by change g.bad = false at e; rw [hbad] at e; cases e), fun hh gg hg => .inr (.inl hbad), hok.ph3, hok.mk_bad⟩,
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

/-- **THE FINAL EXTRACTION** (G4 (1a)): at the end of a valid run (no promise left) nothing is dead, so not `bad`,
and two harts that both acquired recorded distinct counter values: their final `x7`s differ. -/
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
  intro g0 g1 h0 h1 x0 x1
  rcases hok.done 0 g0 h0 with u | u | ⟨v0, u1, u2⟩
  · exact absurd x0 u
  · rw [hbad] at u; cases u
  rcases hok.done 1 g1 h1 with w | w | ⟨v1, w1, w2⟩
  · exact absurd x1 w
  · rw [hbad] at w; cases w
  have l0 := hcnt.rds_lt 0 v0 u1
  have l1 := hcnt.rds_lt 1 v1 w1
  have hne : v0 ≠ v1 := fun e => by subst e; exact hcnt.rds_inj 0 1 v0 (by omega) u1 w1
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
    fun e => (by change g.bad = false at e; rw [hb] at e; cases e), fun hh gg hg => .inr (.inl hb), hok.ph3,
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

end Weak.Prom.Own.Lk
