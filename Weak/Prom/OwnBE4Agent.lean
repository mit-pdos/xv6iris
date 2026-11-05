/-
Weak/Prom: **E-b4 — THE PROMISE AGENT'S OBLIGATION on the lifecycle protocol** (stage E-b4; plan rev 7 §4 "the
promise agent's wp is the invariant", (b1) THE PULL, (b2-own)/(b2-none)).

`agentOk`: every append of `M[n]` (author `i`) preserves `Inv`.  The split is TOTAL over any final memory, by the
appended message's shape and the CURRENT protocol state only (never `M` above `n`):
* not a shape any hart's text fulfils from a promise (`¬ okS`) → ROBUST dead (`Dr`);
* hart 0's 4-byte plain lock-word store: backed while the lock is dead (kfree junk, initlock), else robust dead;
* an acquire-shaped message on a FREE lock → THE PULL (`pulled i (n+1)`, `i` becomes the field's holder);
  otherwise an attempt (no change);
* a field store: backed iff its author is the holder, else dead (`Dc`);
* a cpu-field store: untracked.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Defs

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach
open Weak.Prom.Own (OSt upd upd_eq upd_ne agentStep authorAt fulO)
open Weak.Prom.Own.MP (au)
open Weak.Prom.Own.Lk1c (pend)
open Weak.Prom.PF (Trace PEv msgAt tidAt)
open Weak.Prom.OA (Lk Ct)
open Weak.Prom.OA.P (L1 cAt5)
open Weak.Prom.OA.C (Pc)
open Weak.Prom.OA.E2 (cmP3 isC3 gd noLd)
open Weak.Prom.OA.E4 (q7 img7)

/-! ## 1. Geometry -/

theorem acq_ovC (a : Nat) : ¬ ov (acqM a) Ct 8 := by
  simp [ov, acqM, Lk, Ct, toBytes_len, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]
theorem acq_ovF (a : Nat) : ¬ ov (acqM a) L1 4 := by
  simp [ov, acqM, Lk, L1, toBytes_len, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Z]
theorem acq_ovL (a : Nat) : ov (acqM a) Lk 4 := by
  simp [ov, acqM, toBytes_len]; omega
theorem acq_b0 (a : Nat) : (acqM a).byteAt Lk = some 1 := by
  simp [acqM, PMsg.byteAt, toBytes, Weak.Prom.Ref.byteList, bv8]

theorem plk0_ovC {m : PMsg} (h : plk0 m) : ¬ ov m Ct 8 := by
  obtain ⟨_, hp, hl, _⟩ := h; simp [ov, hp, hl, Lk, Ct, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]
theorem plk0_ovF {m : PMsg} (h : plk0 m) : ¬ ov m L1 4 := by
  obtain ⟨_, hp, hl, _⟩ := h; simp [ov, hp, hl, Lk, L1, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Z]

theorem c3_ovL {m : PMsg} (h : cmP3 m) : ¬ ov m Lk 4 := by
  obtain ⟨hp, hl, _⟩ := h; simp [ov, hp, hl, Lk, Ct, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]
theorem c3_ovF {m : PMsg} (h : cmP3 m) : ¬ ov m L1 4 := by
  obtain ⟨hp, hl, _⟩ := h; simp [ov, hp, hl, L1, Ct, Weak.Prom.Ref.Lit.Z, Weak.Prom.Ref.Lit.Y]

theorem cpu_ovL {m : PMsg} (h : cpuS m) : ¬ ov m Lk 4 := by
  obtain ⟨hp, hl, _⟩ := h; simp [ov, hp, hl, Pc, Lk, Weak.Prom.Ref.Lit.X]
theorem cpu_ovC {m : PMsg} (h : cpuS m) : ¬ ov m Ct 8 := by
  obtain ⟨hp, hl, _⟩ := h; simp [ov, hp, hl, Pc, Lk, Ct, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]
theorem cpu_ovF {m : PMsg} (h : cpuS m) : ¬ ov m L1 4 := by
  obtain ⟨hp, hl, _⟩ := h; simp [ov, hp, hl, Pc, Lk, L1, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Z]

/-- A message writing a byte of `[a, a + n)` overlaps it. -/
theorem ov_of {m : PMsg} {a x : Int} {n : Nat} (hx : a ≤ x ∧ x < a + n) (h : (m.byteAt x).isSome = true) : ov m a n := by
  have := byteAt_rng h; unfold ov; omega

theorem ovL_b0 {m : PMsg} (h : (m.byteAt Lk).isSome = true) : ov m Lk 4 := ov_of (by omega) h

/-- The okS shapes are disjoint. -/
theorem okS_cases {m : PMsg} (h : okS m) : ∃ a, a < 3 ∧ m.tid = some a ∧
    ((plk0 m ∧ ¬ ov m Ct 8 ∧ ¬ ov m L1 4) ∨ (m = acqM a ∧ ¬ ov m Ct 8 ∧ ¬ ov m L1 4) ∨
     (cmP3 m ∧ ¬ ov m Lk 4 ∧ ¬ ov m L1 4) ∨ (cpuS m ∧ ¬ ov m Lk 4 ∧ ¬ ov m Ct 8 ∧ ¬ ov m L1 4)) := by
  obtain ⟨a, ha, ht, hc⟩ := h
  refine ⟨a, ha, ht, ?_⟩
  rcases hc with h | h | h | h
  · exact .inl ⟨h, plk0_ovC h, plk0_ovF h⟩
  · subst h; exact .inr (.inl ⟨rfl, acq_ovC a, acq_ovF a⟩)
  · exact .inr (.inr (.inl ⟨h, c3_ovL h, c3_ovF h⟩))
  · exact .inr (.inr (.inr ⟨h, cpu_ovL h, cpu_ovC h, cpu_ovF h⟩))

theorem okS_acq {a : Nat} (ha : a < 3) : okS (acqM a) := ⟨a, ha, rfl, .inr (.inl rfl)⟩

theorem plk0_ne_acq {m : PMsg} {a : Nat} (h : plk0 m) : m ≠ acqM a := by
  intro e; subst e; obtain ⟨_, _, _, hc⟩ := h; cases hc

/-! ## 2. Monotonicity -/

theorem rob_mono {M : List PMsg} {o o' : OSt (List Nat)} {l0 : Loc} {t : Nat} (h : Rob M o l0 t)
    (hp : ∀ t, pend M o t → pend M o' t) : Rob M o' l0 t := ⟨hp t h.1, h.2⟩

theorem goodT_mono {M : List PMsg} {σ σ' : TSt (List Nat)} {S S' : PS} {ls : Nat → Loc} (h : GoodT M σ S ls)
    (htr : σ'.tr = σ.tr) (hr : ∀ t, S.Dr t → S'.Dr t) (hc : ∀ t, S.Dc t → S'.Dc t) (hs : S'.tstar = S.tstar) :
    GoodT M σ' S' ls := by
  have hcl : clr S' → clr S := fun h t => ⟨fun d => (h t).1 (hr t d), fun d => (h t).2 (hc t d)⟩
  refine ⟨by rw [htr]; exact h.t0, fun c => by rw [htr]; exact h.tq (hcl c), fun i tvs hi hl => ?_⟩
  obtain ⟨a1, a2⟩ := h.tld i tvs hi hl
  exact ⟨by rw [htr]; exact a1, fun c => by rw [hs]; exact a2 (hcl c)⟩

/-! ## 3. The agent obligation -/

section agent

variable {M : List PMsg} {o : OSt (List Nat)} {S : PS} {ls : Nat → Loc} {i : Nat} {m : PMsg}

/-- **THE LOCK WINDOW**: a clean window from a live zero to past a pulled/owned acquire `u` is the holder's own. -/
theorem lkwin (hP : GoodP M o S ls) {j u h t0 ts : Nat} (hl : S.ls = .pulled j u ∨ S.ls = .owned j u)
    (hn : nd0 M S t0) (ht0 : t0 ≤ o.n) (hc : clean M h t0 ts) (hu : u < ts) : j = h := by
  obtain ⟨_, hu1, hun, hmu, hrest⟩ := hP.lk j u hl
  rcases Nat.lt_or_ge t0 u with hlt | hge
  · have := hc u hlt hu ⟨_, hmu, by rw [acq_b0]; rfl⟩
    rw [au_msg hu1 hmu] at this; simp [acqM] at this; exact this
  · exfalso
    obtain ⟨m0, hm0, _, _, hb⟩ := memByte_ov (by omega) hn.2
    rcases Nat.lt_or_eq_of_le hge with hgt | heq
    · rcases hrest t0 m0 hgt ht0 hm0 (ovL_b0 (by rw [hb]; rfl)) with hd | ⟨a, rfl⟩
      · exact hn.1 hd
      · rw [acq_b0] at hb; cases hb
    · subst heq; rw [hmu] at hm0; cases hm0; rw [acq_b0] at hb; cases hb

/-- The appended message's byte-0 class: a live zero at `n + 1` is hart 0's plain word appended while dead, or
robust dead. -/
theorem nz_new {hm : msgAt M (o.n + 1) = some m} (hz : memByte img7 M (o.n + 1) Lk = some 0) :
    ¬ okS m ∨ plk0 m := by
  by_cases hk : okS m
  · obtain ⟨a, _, _, hc⟩ := okS_cases hk
    obtain ⟨m0, hm0, _, _, hb⟩ := memByte_ov (by omega) hz
    rw [hm] at hm0; cases hm0
    rcases hc with ⟨h, _⟩ | ⟨rfl, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
    · exact .inr h
    · rw [acq_b0] at hb; cases hb
    · exact absurd (ovL_b0 (by rw [hb]; rfl)) h
    · exact absurd (ovL_b0 (by rw [hb]; rfl)) h
  · exact .inl hk

theorem pr_ag {o : OSt (List Nat)} {i h ts : Nat} (h1 : ts ∈ upd o.pr i ({o.n + 1} ∪ o.pr i) h) :
    ts ∈ o.pr h ∨ (h = i ∧ ts = o.n + 1) := by
  by_cases e : h = i
  · subst e; simp only [upd_eq, elemOfUnion, elemOfSingleton] at h1
    rcases h1 with h1 | h1
    · exact .inr ⟨rfl, h1⟩
    · exact .inl h1
  · simp only [upd_ne _ _ e] at h1; exact .inl h1

theorem pend_le' {S : PS} {ls : Nat → Loc} (hdc : ∀ t, S.Dc t → pend M o t ∧ ∃ m, msgAt M t = some m ∧ cmP3 m)
    (t : Nat) (h : S.Dc t) : ∃ a, au M t = some a ∧ t ∈ o.pr a := (hdc t h).1

theorem fresh_not_own {S : PS} {ls : Nat → Loc} (hP : GoodP M o S ls) {h u : Nat} (hf : fresh S ls h)
    (ho : S.ls = .owned h u) : False := by
  rcases hP.hown h u ho with ⟨rfl, h2, _⟩ | ⟨hh, h2, _⟩
  · rcases hf with ⟨_, h3⟩ | ⟨h3, _⟩
    · rw [h2] at h3; cases h3
    · omega
  · rcases hf with ⟨h3, _⟩ | ⟨_, _, h4⟩
    · omega
    · rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4 <;> rw [h2] at h4 <;> cases h4

/-- The clean window restricted. -/
theorem clean_le {h t0 ts ts' : Nat} (hc : clean M h t0 ts) (hle : ts' ≤ ts) : clean M h t0 ts' :=
  fun t a b c => hc t a (by omega) c

/-- The agent's split without a pull: `Dr`/`Dc` extended at `n + 1`. -/
def agS (S : PS) (n : Nat) (m : PMsg) (i : Nat) : PS :=
  { S with Dr := fun x => S.Dr x ∨ (x = n + 1 ∧ (¬ okS m ∨ (plk0 m ∧ S.ls ≠ .dead))),
           Dc := fun x => S.Dc x ∨ (x = n + 1 ∧ cmP3 m ∧ S.hold ≠ some i) }

theorem agent_np (hP : GoodP M o S ls) (hm : msgAt M (o.n + 1) = some m) (hti : m.tid = some i)
    (hnp : ¬ (m = acqM i ∧ i < 3 ∧ S.ls = .free)) :
    GoodP M { o with n := o.n + 1, pr := upd o.pr i ({o.n + 1} ∪ o.pr i) } (agS S o.n m i) ls := by
  have hau : au M (o.n + 1) = some i := by rw [au_msg (by omega) hm, hti]
  have hpe := pend_ag (M := M) (o := o) hau
  have hpm : ∀ t, pend M o t → pend M { o with n := o.n + 1, pr := upd o.pr i ({o.n + 1} ∪ o.pr i) } t :=
    fun t h => (hpe t).2 (.inl h)
  have hpn : pend M { o with n := o.n + 1, pr := upd o.pr i ({o.n + 1} ∪ o.pr i) } (o.n + 1) := (hpe _).2 (.inr rfl)
  have hnd : ∀ t0, nd0 M (agS S o.n m i) t0 → nd0 M S t0 :=
    fun t0 h => ⟨fun d => h.1 (.inl d), h.2⟩
  have hnew : ∀ t m', t ≤ o.n + 1 → msgAt M t = some m' → ¬ t ≤ o.n → m' = m := fun t m' h1 h2 h3 => by
    have : t = o.n + 1 := by omega
    subst this; rw [hm] at h2; exact (Option.some.inj h2).symm
  unfold agS
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t a ht hh ha => ?_, ⟨by have := hP.tsle.1; simp only; omega,
    by have := hP.tsle.2; simp only; omega⟩, hP.tsok, fun t m' h1 h2 h3 h4 => ?_, hP.hdead, hP.hfree, hP.hpo,
    hP.gdp, hP.h0f, hP.hpre, hP.hown, hP.h1, hP.h0o, fun h u hu => ?_, fun h ts t0 a1 a2 a3 a4 a5 a6 a7 a8 => ?_,
    fun h t0 a1 a2 a3 a4 a5 => ?_, fun t m' h1 h2 h3 h4 => ?_, hP.pubk, hP.dnk, hP.s0, hP.sA⟩
  · rcases ht with ht | ⟨rfl, hc⟩
    · exact rob_mono (hP.dr t ht) hpm
    · refine ⟨hpn, m, hm, ?_⟩
      rcases hc with hc | ⟨hc1, hc2⟩
      · exact .inl hc
      · exact .inr ⟨hc1, .inl (fun hd => hc2 ((hP.s0.2.2.1).1 hd))⟩
  · rcases ht with ht | ⟨rfl, hc, _⟩
    · exact ⟨hpm t (hP.dc t ht).1, (hP.dc t ht).2⟩
    · exact ⟨hpn, m, hm, hc⟩
  · rcases ht with ht | ⟨rfl, _, hne⟩
    · exact hP.dcH t a ht hh ha
    · rw [hau] at ha; cases ha; exact absurd hh hne
  · by_cases hle : t ≤ o.n
    · rcases hP.later t m' h1 hle h3 h4 with a | a | ⟨a, b1, b2, b3, b4, b5⟩
      · exact .inl (.inl a)
      · exact .inr (.inl (.inl a))
      · exact .inr (.inr ⟨a, b1, b2, b3, hpm _ b4, b5⟩)
    · obtain rfl := hnew t m' h2 h3 hle
      have ht : t = o.n + 1 := by simp only at h2; omega
      subst ht
      by_cases hk : okS m'
      · obtain ⟨a, _, hta, hc⟩ := okS_cases hk
        rcases hc with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨hc, _, _⟩ | ⟨_, _, h, _⟩
        · exact absurd h4 h
        · exact absurd h4 h
        · by_cases hh : S.hold = some i
          · exact .inr (.inr ⟨i, hh, hti, by have := hP.tsle.2; simp only; omega, hpn, hc⟩)
          · exact .inr (.inl (.inr ⟨rfl, hc, hh⟩))
        · exact absurd h4 h
      · exact .inl (.inr ⟨rfl, .inl hk⟩)
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hP.lk h u hu
    refine ⟨a1, a2, by simp only; omega, a4, fun t m' b1 b2 b3 b4 => ?_⟩
    by_cases hle : t ≤ o.n
    · rcases a5 t m' b1 hle b3 b4 with c | c
      · exact .inl (.inl c)
      · exact .inr c
    · obtain rfl := hnew t m' b2 b3 hle
      have ht : t = o.n + 1 := by simp only at b2; omega
      subst ht
      by_cases hk : okS m'
      · obtain ⟨a, _, hta, hc⟩ := okS_cases hk
        rcases hc with ⟨hc, _⟩ | ⟨rfl, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
        · exact .inl (.inr ⟨rfl, .inr ⟨hc, by rcases hu with e | e <;> rw [e] <;> simp⟩⟩)
        · exact .inr ⟨a, rfl⟩
        · exact absurd b4 h
        · exact absurd b4 h
      · exact .inl (.inr ⟨rfl, .inl hk⟩)
  · rcases pr_ag a4 with a4 | ⟨rfl, rfl⟩
    · exact hP.tk1 h ts t0 a1 a2 a3 a4 a5 (hnd t0 a6) a7 a8
    · rw [hm] at a5; cases a5
      have hi3 : h < 3 := by rcases a2 with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
      have hnf : S.ls ≠ .free := fun e => hnp ⟨rfl, hi3, e⟩
      have ht0 : t0 ≤ o.n := by omega
      cases hl : S.ls with
      | dead => exact absurd hl a1
      | free => exact absurd hl hnf
      | pulled j u =>
        obtain rfl := lkwin hP (.inl hl) (hnd t0 a6) ht0 a8 (by have := (hP.lk j u (.inl hl)).2.2.1; omega)
        exact ⟨u, by have := (hP.lk j u (.inl hl)).2.2.1; omega, rfl⟩
      | owned j u =>
        obtain rfl := lkwin hP (.inr hl) (hnd t0 a6) ht0 a8 (by have := (hP.lk j u (.inr hl)).2.2.1; omega)
        exact (fresh_not_own hP a2 hl).elim
  · by_cases hle : t0 ≤ o.n
    · exact hP.tk2 h t0 a1 a2 (hnd t0 a3) hle (clean_le a5 (by simp only; omega))
    · have ht : t0 = o.n + 1 := by simp only at a4; omega
      subst ht
      exfalso
      rcases nz_new (hm := hm) a3.2 with hk | hk
      · exact a3.1 (.inr ⟨rfl, .inl hk⟩)
      · exact a3.1 (.inr ⟨rfl, .inr ⟨hk, a1⟩⟩)
  · by_cases hle : t ≤ o.n
    · rcases hP.fl t m' h1 hle h3 h4 with c | c | c
      · exact .inl (.inl c)
      · exact .inr (.inl c)
      · exact .inr (.inr c)
    · obtain rfl := hnew t m' h2 h3 hle
      have ht : t = o.n + 1 := by simp only at h2; omega
      subst ht
      by_cases hk : okS m'
      · obtain ⟨a, _, hta, hc⟩ := okS_cases hk
        rcases hc with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> exact absurd h4 h
      · exact .inl (.inr ⟨rfl, .inl hk⟩)

/-- **THE PULL**: an acquire-shaped message on a free lock moves the lock (and the field) to its author. -/
theorem agent_p (hw : WFp M o) (hP : GoodP M o S ls) (hm : msgAt M (o.n + 1) = some (acqM i)) (hi : i < 3)
    (hfr : S.ls = .free) :
    GoodP M { o with n := o.n + 1, pr := upd o.pr i ({o.n + 1} ∪ o.pr i) }
      { S with ls := .pulled i (o.n + 1), hold := some i, tst := o.n + 1 } ls := by
  have hau : au M (o.n + 1) = some i := by rw [au_msg (by omega) hm]; rfl
  have hpe := pend_ag (M := M) (o := o) hau
  have hpm : ∀ t, pend M o t → pend M { o with n := o.n + 1, pr := upd o.pr i ({o.n + 1} ∪ o.pr i) } t :=
    fun t h => (hpe t).2 (.inl h)
  have hnew : ∀ t m', t ≤ o.n + 1 → msgAt M t = some m' → ¬ t ≤ o.n → m' = acqM i := fun t m' h1 h2 h3 => by
    have : t = o.n + 1 := by omega
    subst this; rw [hm] at h2; exact (Option.some.inj h2).symm
  have hnd : ¬ isD (ls 0).st := fun h => by rw [(hP.s0.2.2.1).1 h] at hfr; cases hfr
  constructor
  · exact fun t ht => rob_mono (hP.dr t ht) hpm
  · exact fun t ht => ⟨hpm t (hP.dc t ht).1, (hP.dc t ht).2⟩
  · intro t a ht _ _
    left; have := (pend_le hw (hP.dc t ht).1).2; simp only; omega
  · exact ⟨by have := hP.tsle.1; simp only; omega, by simp only; omega⟩
  · exact hP.tsok
  · intro t m' h1 h2 h3 h4
    by_cases hle : t ≤ o.n
    · rcases hP.later t m' h1 hle h3 h4 with a | a | ⟨a, b1, _⟩
      · exact .inl a
      · exact .inr (.inl a)
      · rw [hP.hfree hfr] at b1; cases b1
    · obtain rfl := hnew t m' h2 h3 hle; exact absurd h4 (acq_ovC i)
  · intro e; simp at e
  · intro e; simp at e
  · intro h u hu
    simp only at hu
    rcases hu with e | e <;> cases e; exact ⟨rfl, rfl⟩
  · intro _; exact hP.gdp (by rw [hfr]; simp)
  · refine ⟨fun e => absurd (.inl e) hnd, fun e => absurd ?_ hnd, fun e => absurd ?_ hnd⟩
    · rcases e with e | e <;> simp [isD, e]
    · simp [isD, e]
  · intro h u _; have := hP.tsle.1; simp only; omega
  · intro h u e; simp at e
  · intro j hj e
    have := (hP.sA j hj).2.2.2.1 (.inl e); rw [hfr] at this; cases this
  · intro e
    have := hP.s0.2.2.2.2.2.1 e; rw [hfr] at this; cases this
  · intro h u hu
    simp only at hu
    rcases hu with e | e <;> cases e
    refine ⟨hi, by omega, by simp only; omega, hm, fun t m' b1 b2 _ _ => ?_⟩
    simp only at b2; omega
  · intro h ts t0 a1 a2 a3 a4 a5 a6 a7 a8
    rcases pr_ag a4 with a4 | ⟨rfl, rfl⟩
    · obtain ⟨u, _, e⟩ := hP.tk1 h ts t0 (by rw [hfr]; simp) a2 a3 a4 a5 a6 a7 a8
      rw [hfr] at e; cases e
    · exact ⟨o.n + 1, Nat.le_refl _, rfl⟩
  · intro h t0 a1 a2 a3 a4 a5
    by_cases e : h = i
    · subst e; exact .inr ⟨_, rfl⟩
    · exfalso
      by_cases hle : t0 ≤ o.n
      · have := a5 (o.n + 1) (by omega) (by simp only; omega) ⟨_, hm, by rw [acq_b0]; rfl⟩
        rw [hau] at this; cases this; exact e rfl
      · have ht : t0 = o.n + 1 := by simp only at a4; omega
        subst ht
        obtain ⟨m0, hm0, _, _, hb⟩ := memByte_ov (by omega) a3.2
        rw [hm] at hm0; cases hm0; rw [acq_b0] at hb; cases hb
  · intro t m' h1 h2 h3 h4
    by_cases hle : t ≤ o.n
    · exact hP.fl t m' h1 hle h3 h4
    · obtain rfl := hnew t m' h2 h3 hle; exact absurd h4 (acq_ovF i)
  · intro k hk; exact ⟨(hP.pubk k hk).1, fun _ => by simp⟩
  · exact hP.dnk
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
    refine ⟨b1, b2, ⟨fun h => absurd h hnd, fun e => by simp at e⟩, b4, b5, fun e => ?_, b7, b8, b9⟩
    have := b6 e; rw [hfr] at this; cases this
  · intro j hj
    obtain ⟨b1, b2, b3, b4, b5⟩ := hP.sA j hj
    refine ⟨?_, b2, fun e => ?_, fun e => ?_, b5⟩
    · rcases b1 with b1 | ⟨b1, b1', _⟩
      · exact .inl b1
      · exact .inr ⟨b1, b1', by simp⟩
    · obtain ⟨c1, _, c3⟩ := b3 e; exact ⟨c1, by simp, c3⟩
    · have := b4 e; rw [hfr] at this; cases this

/-- **THE AGENT OBLIGATION** (plan §4 "the promise agent's wp is the invariant"). -/
theorem agentOk {σ : TSt (List Nat)} {o' : OSt (List Nat)} {Xs : List (List Weak.Prom.OA.XI)} {img : Image}
    (hI : Inv M σ S ls) (ha : agentStep (Weak.Prom.Own.X.xOW Xs img M) σ.o o') :
    ∃ S', Inv M ⟨o', σ.tr⟩ S' ls := by
  obtain ⟨i, hn, hau', rfl⟩ := ha
  obtain ⟨m, hm0⟩ : ∃ m, M[σ.o.n]? = some m := ⟨_, List.getElem?_eq_getElem hn⟩
  have hm : msgAt M (σ.o.n + 1) = some m := hm0
  have hti : m.tid = some i := by simpa [authorAt, hm0] using hau'
  have hau : au M (σ.o.n + 1) = some i := by rw [au_msg (by omega) hm, hti]
  have hpe := pend_ag (M := M) (o := σ.o) hau
  have hw : WFp M { σ.o with n := σ.o.n + 1, pr := upd σ.o.pr i ({σ.o.n + 1} ∪ σ.o.pr i) } := by
    intro a t ht
    rcases pr_ag ht with ht | ⟨rfl, rfl⟩
    · obtain ⟨u1, u2, u3⟩ := hI.1 a t ht; exact ⟨u1, by simp only; omega, u3⟩
    · exact ⟨by omega, by simp only; omega, hau⟩
  rcases hI.2 with ⟨hP, hT⟩ | ⟨t, ht⟩
  · by_cases hpl : m = acqM i ∧ i < 3 ∧ S.ls = .free
    · obtain ⟨rfl, hi, hfr⟩ := hpl
      exact ⟨_, hw, .inl ⟨agent_p hI.1 hP hm hi hfr, goodT_mono hT rfl (fun _ h => h) (fun _ h => h) rfl⟩⟩
    · exact ⟨_, hw, .inl ⟨agent_np hP hm hti hpl, goodT_mono hT rfl (fun _ h => .inl h) (fun _ h => .inl h) rfl⟩⟩
  · exact ⟨S, hw, .inr ⟨t, rob_mono ht (fun t h => (hpe t).2 (.inl h))⟩⟩

end agent

end Weak.Prom.OB.E4
