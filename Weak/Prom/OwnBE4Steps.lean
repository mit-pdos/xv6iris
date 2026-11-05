/-
Weak/Prom: **E-b4 — the protocol's step lemmas, part 1: frames** (stage E-b4).

Pure facts about one hart step against `Inv` (OwnBE4Defs.lean): the promise set after a fulfil, the SPOILED mode
(`rob_ful`: a robust dead message stays pending whatever a hart's text does), the two FRAMES (a fulfil from a promise
or an in-place append that touches no tracked state keeps the protocol), and the trace clauses for an entry that is
not a field access.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Agent

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach
open Weak.Prom.Own (OSt upd upd_eq upd_ne agentStep authorAt fulO)
open Weak.Prom.Own.MP (au)
open Weak.Prom.Own.Lk1c (pend)
open Weak.Prom.PF (Trace PEv msgAt tidAt)
open Weak.Prom.OA (Lk Ct isCLd isCSt)
open Weak.Prom.OA.P (L1 cAt5)
open Weak.Prom.OA.C (Pc)
open Weak.Prom.OA.E2 (cmP3 isC3 gd noLd noLd_snoc)
open Weak.Prom.OA.E4 (q7 img7 q7_snoc)
open PLabel

section frames

variable {M : List PMsg} {o : OSt (List Nat)} {S : PS} {ls : Nat → Loc}

/-- The OwnLang state after a fulfil from a promise. -/
abbrev pfO (o : OSt (List Nat)) (h ts : Nat) : OSt (List Nat) := { o with pr := upd o.pr h (o.pr h \ {ts}) }

theorem pend_pf (hw : WFp M o) {h ts t : Nat} (hts : ts ∈ o.pr h) : pend M (pfO o h ts) t ↔ pend M o t ∧ t ≠ ts := by
  constructor
  · rintro ⟨a, h1, h2⟩
    by_cases e : a = h
    · subst e; simp only [upd_eq, elemOfDifference, elemOfSingleton] at h2; exact ⟨⟨a, h1, h2.1⟩, h2.2⟩
    · simp only [upd_ne _ _ e] at h2
      refine ⟨⟨a, h1, h2⟩, fun e2 => ?_⟩
      subst e2; rw [(hw h t hts).2.2] at h1; cases h1; exact e rfl
  · rintro ⟨⟨a, h1, h2⟩, hne⟩
    refine ⟨a, h1, ?_⟩
    by_cases e : a = h
    · subst e; simp only [upd_eq, elemOfDifference, elemOfSingleton]; exact ⟨h2, hne⟩
    · simp only [upd_ne _ _ e]; exact h2

theorem wf_pf (hw : WFp M o) {h ts : Nat} : WFp M (pfO o h ts) := by
  intro a t ht
  by_cases e : a = h
  · subst e; simp only [upd_eq, elemOfDifference] at ht; exact hw a t ht.1
  · simp only [upd_ne _ _ e] at ht; exact hw a t ht

/-- The in-place fulfil leaves the promise sets alone. -/
theorem ip_eq (hw : WFp M o) (h : Nat) :
    ({ o with n := o.n + 1, pr := upd o.pr h (({o.n + 1} ∪ o.pr h) \ {o.n + 1}) } : OSt (List Nat)) =
      { o with n := o.n + 1 } := by
  rw [Weak.Prom.Own.MPL.relPrG (fun t ht => (hw h t ht).2.1)]

theorem wf_ip (hw : WFp M o) : WFp M { o with n := o.n + 1 } := fun a t ht => by
  obtain ⟨u1, u2, u3⟩ := hw a t ht; exact ⟨u1, by simp only; omega, u3⟩

/-- A fulfil, as one of the two shapes. -/
theorem ful_cases (hw : WFp M o) {h ts : Nat} {rc : Prop} {o' : OSt (List Nat)} (hf : fulO M h o rc ts o') :
    (ts ∈ o.pr h ∧ o' = pfO o h ts ∧ ¬ rc) ∨ (ts = o.n + 1 ∧ o' = { o with n := o.n + 1 } ∧ rc ∧
      authorAt M o.n = some h ∧ o.n < M.length) := by
  rcases hf with ⟨hnr, hts, rfl⟩ | ⟨hrc, hn, hau, rfl, rfl⟩
  · exact .inl ⟨hts, rfl, hnr⟩
  · exact .inr ⟨rfl, ip_eq hw h, hrc, hau, hn⟩

/-- **SPOILED MODE**: a robust dead message stays robust dead across a hart's fulfil. -/
theorem rob_ful (hw : WFp M o) {l0 l0' : Loc} {t h ts : Nat} {rc : Prop} {o' : OSt (List Nat)} {m : PMsg}
    (hr : Rob M o l0 t) (hf : fulO M h o rc ts o') (hm : msgAt M ts = some m)
    (hok : ts ∈ o.pr h → okS m ∧ (h = 0 → plk0 m → isD l0.st ∧ l0.cf < ts))
    (hl0 : isD l0'.st → (isD l0.st ∧ l0.cf ≤ l0'.cf) ∨ o.n < l0'.cf) : Rob M o' l0' t := by
  obtain ⟨hp, m', hm', hc⟩ := hr
  have htn := (pend_le hw hp).2
  have hc' : ¬ okS m' ∨ (plk0 m' ∧ (¬ isD l0'.st ∨ t < l0'.cf)) := by
    rcases hc with hc | ⟨hc1, hc2⟩
    · exact .inl hc
    · refine .inr ⟨hc1, ?_⟩
      by_cases hd : isD l0'.st
      · rcases hl0 hd with ⟨h1, h2⟩ | h1
        · rcases hc2 with hc2 | hc2
          · exact absurd h1 hc2
          · exact .inr (by omega)
        · exact .inr (by omega)
      · exact .inl hd
  refine ⟨?_, m', hm', hc'⟩
  rcases ful_cases hw hf with ⟨hts, rfl, _⟩ | ⟨rfl, rfl, _⟩
  · refine (pend_pf hw hts).2 ⟨hp, fun e => ?_⟩
    subst e
    rw [hm] at hm'; cases hm'
    obtain ⟨hk, h0⟩ := hok hts
    rcases hc with hc | ⟨hc1, hc2⟩
    · exact hc hk
    · have hh : h = 0 := by
        have h1 := (hw h t hts).2.2
        rw [au_msg (pend_le hw hp).1 hm, hc1.1] at h1; cases h1; rfl
      obtain ⟨hd, hcf⟩ := h0 hh hc1
      rcases hc2 with hc2 | hc2
      · exact hc2 hd
      · omega
  · obtain ⟨a, h1, h2⟩ := hp; exact ⟨a, h1, h2⟩

/-- **THE PROMISE-FULFIL FRAME**: fulfilling a promise that is not a field store, not dead, keeps the protocol. -/
theorem pf_frame (hw : WFp M o) (hP : GoodP M o S ls) {h ts : Nat} {m : PMsg} (hts : ts ∈ o.pr h)
    (hm : msgAt M ts = some m) (hnC : ¬ ov m Ct 8) (hnr : ¬ S.Dr ts) (hnc : ¬ S.Dc ts) :
    GoodP M (pfO o h ts) S ls := by
  have hpe := fun t => pend_pf (M := M) (o := o) (t := t) hw hts
  have hpm : ∀ t, pend M o t → t ≠ ts → pend M (pfO o h ts) t := fun t a b => (hpe t).2 ⟨a, b⟩
  refine ⟨fun t ht => ⟨hpm t (hP.dr t ht).1 (fun e => hnr (e ▸ ht)), (hP.dr t ht).2⟩,
    fun t ht => ⟨hpm t (hP.dc t ht).1 (fun e => hnc (e ▸ ht)), (hP.dc t ht).2⟩, hP.dcH, hP.tsle, hP.tsok,
    fun t m' h1 h2 h3 h4 => ?_, hP.hdead, hP.hfree, hP.hpo, hP.gdp, hP.h0f, hP.hpre, hP.hown, hP.h1, hP.h0o, hP.lk,
    fun h' ts' t0 a1 a2 a3 a4 a5 a6 a7 a8 => ?_, hP.tk2, hP.fl, hP.pubk, hP.dnk, hP.s0, hP.sA⟩
  · rcases hP.later t m' h1 h2 h3 h4 with a | a | ⟨a, b1, b2, b3, b4, b5⟩
    · exact .inl a
    · exact .inr (.inl a)
    · refine .inr (.inr ⟨a, b1, b2, b3, hpm t b4 (fun e => ?_), b5⟩)
      subst e; rw [hm] at h3; cases h3; exact hnC h4
  · have : ts' ∈ o.pr h' := by
      by_cases e : h' = h
      · subst e; simp only [upd_eq, elemOfDifference] at a4; exact a4.1
      · simp only [upd_ne _ _ e] at a4; exact a4
    exact hP.tk1 h' ts' t0 a1 a2 a3 this a5 a6 a7 a8

/-- **THE IN-PLACE FRAME**: an in-place append that touches neither the field nor the flags, and touches the lock
word only as hart 0's dead-phase store or an attempt, keeps the protocol. -/
theorem ip_frame (hw : WFp M o) (hP : GoodP M o S ls) {m : PMsg} (hm : msgAt M (o.n + 1) = some m)
    (hnC : ¬ ov m Ct 8) (hnF : ¬ ov m L1 4)
    (hL : ov m Lk 4 → (S.ls = .dead ∧ plk0 m) ∨ ((∃ a, m = acqM a) ∧ ∃ j u, S.ls = .pulled j u ∨ S.ls = .owned j u)) :
    GoodP M { o with n := o.n + 1 } S ls := by
  have hnew : ∀ t m', t ≤ o.n + 1 → msgAt M t = some m' → ¬ t ≤ o.n → t = o.n + 1 ∧ m' = m := fun t m' h1 h2 h3 => by
    have : t = o.n + 1 := by omega
    subst this; rw [hm] at h2; exact ⟨rfl, (Option.some.inj h2).symm⟩
  refine ⟨hP.dr, hP.dc, hP.dcH, ⟨by have := hP.tsle.1; simp only; omega, by have := hP.tsle.2; simp only; omega⟩,
    hP.tsok, fun t m' h1 h2 h3 h4 => ?_, hP.hdead, hP.hfree, hP.hpo, hP.gdp, hP.h0f, hP.hpre, hP.hown, hP.h1, hP.h0o,
    fun j u hu => ?_, hP.tk1, fun h t0 a1 a2 a3 a4 a5 => ?_, fun t m' h1 h2 h3 h4 => ?_, hP.pubk, hP.dnk, hP.s0,
    hP.sA⟩
  · by_cases hle : t ≤ o.n
    · exact hP.later t m' h1 hle h3 h4
    · obtain ⟨rfl, rfl⟩ := hnew t m' h2 h3 hle; exact absurd h4 hnC
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hP.lk j u hu
    refine ⟨a1, a2, by simp only; omega, a4, fun t m' b1 b2 b3 b4 => ?_⟩
    by_cases hle : t ≤ o.n
    · exact a5 t m' b1 hle b3 b4
    · obtain ⟨rfl, rfl⟩ := hnew t m' b2 b3 hle
      rcases hL b4 with ⟨hd, _⟩ | ⟨ha, _⟩
      · rcases hu with e | e <;> rw [e] at hd <;> cases hd
      · exact .inr ha
  · by_cases hle : t0 ≤ o.n
    · exact hP.tk2 h t0 a1 a2 a3 hle (clean_le a5 (by simp only; omega))
    · exfalso
      obtain ⟨rfl, -⟩ : t0 = o.n + 1 ∧ True := ⟨by simp only at a4; omega, trivial⟩
      obtain ⟨m0, hm0, _, _, hb⟩ := memByte_ov (by omega) a3.2
      rw [hm] at hm0; cases hm0
      rcases hL (ovL_b0 (by rw [hb]; rfl)) with ⟨hd, _⟩ | ⟨⟨a, rfl⟩, _⟩
      · exact a1 hd
      · rw [acq_b0] at hb; cases hb
  · by_cases hle : t ≤ o.n
    · exact hP.fl t m' h1 hle h3 h4
    · obtain ⟨rfl, rfl⟩ := hnew t m' h2 h3 hle; exact absurd h4 hnF

end frames

/-! ## The trace clauses for a non-field entry -/

theorem upd_same {α : Type} (f : Nat → α) (h : Nat) : upd f h (f h) = f := by
  funext j; by_cases e : j = h <;> simp [upd, e]

theorem gT_snoc {M : List PMsg} {σ : TSt (List Nat)} {S S' : PS} {ls : Nat → Loc} {h : Nat} {o' : OSt (List Nat)}
    {e : PEv} {l' : Loc} (hT : GoodT M σ S ls) (he : ∀ tvs, ¬ isCLd e tvs) (hs : h = 0 ∨ ∀ ts, ¬ isCSt e ts)
    (hld : l'.ld = none) (hdr : ∀ t, S.Dr t → S'.Dr t) (hdc : ∀ t, S.Dc t → S'.Dc t)
    (hts : ∀ i tvs, (i = 1 ∨ i = 2) → i ≠ h → (ls i).ld = some tvs → S'.tstar = S.tstar) :
    GoodT M (nxT σ h o' e) S' (upd ls h l') := by
  have hcl : clr S' → clr S := fun c t => ⟨fun d => (c t).1 (hdr t d), fun d => (c t).2 (hdc t d)⟩
  refine ⟨?_, fun c => ?_, fun i tvs hi hl => ?_⟩
  · by_cases e0 : h = 0
    · subst e0; simp only [upd_eq]; exact noLd_snoc hT.t0 he
    · simp only [upd_ne _ _ (Ne.symm e0)]; exact hT.t0
  · have := hT.tq (hcl c)
    have hq : ∀ i, (i = 1 ∨ i = 2) → q7 M ((nxT σ h o' e).tr i) := by
      intro i hi
      by_cases ei : i = h
      · subst ei
        have hs' : ∀ ts, ¬ isCSt e ts := by rcases hs with hs | hs; omega; exact hs
        simp only [upd_eq]
        rcases hi with rfl | rfl
        · exact q7_snoc this.1 he hs'
        · exact q7_snoc this.2 he hs'
      · simp only [upd_ne _ _ ei]; rcases hi with rfl | rfl; exact this.1; exact this.2
    exact ⟨hq 1 (.inl rfl), hq 2 (.inr rfl)⟩
  · by_cases ei : i = h
    · subst ei; simp only [upd_eq] at hl; rw [hld] at hl; cases hl
    · simp only [upd_ne _ _ ei] at hl
      obtain ⟨a1, a2⟩ := hT.tld i tvs hi hl
      refine ⟨by simp only [upd_ne _ _ ei]; exact a1, fun c => ?_⟩
      rw [hts i tvs hi ei hl]; exact a2 (hcl c)

/-! ## Inv-level steps: loads and untracked fulfils -/

section invsteps

variable {M : List PMsg} {σ : TSt (List Nat)} {S : PS} {ls : Nat → Loc}

theorem upd0 {f : Nat → Loc} {h : Nat} {l : Loc} (hh : h ≠ 0) : upd f h l 0 = f 0 := upd_ne _ _ (Ne.symm hh)

/-- **A LOAD THAT IS NOT A FIELD LOAD**, no change of the hart's record. -/
theorem inv_ld {h : Nat} {e : PEv} (hI : Inv M σ S ls) (he : ∀ tvs, ¬ isCLd e tvs) (hs : ∀ ts, ¬ isCSt e ts)
    (hld : (ls h).ld = none) : Inv M (nxT σ h σ.o e) S ls := by
  obtain ⟨hw, hI⟩ := hI
  refine ⟨hw, ?_⟩
  rcases hI with ⟨hP, hT⟩ | ⟨t, hr⟩
  · refine .inl ⟨hP, ?_⟩
    have := gT_snoc (h := h) (o' := σ.o) (l' := ls h) hT he (.inr hs) hld (fun _ h => h) (fun _ h => h) (fun _ _ _ _ _ => rfl)
    rwa [upd_same] at this
  · exact .inr ⟨t, hr⟩

/-- **AN UNTRACKED FULFIL** (a cpu-field store; hart 0's lock-word store in its dead phase), from a promise or in
place, no change of the hart's record. -/
theorem inv_ful {h ts : Nat} {rc : Prop} {o' : OSt (List Nat)} {e : PEv} {m : PMsg} (hI : Inv M σ S ls)
    (hf : fulO M h σ.o rc ts o') (hm : msgAt M ts = some m) (hok : okS m) (hnC : ¬ ov m Ct 8) (hnF : ¬ ov m L1 4)
    (hL : ov m Lk 4 → h = 0 ∧ plk0 m ∧ isD (ls 0).st ∧ (ls 0).cf < ts)
    (he : ∀ tvs, ¬ isCLd e tvs) (hs : h = 0 ∨ ∀ ts, ¬ isCSt e ts) (hld : (ls h).ld = none) :
    Inv M (nxT σ h o' e) S ls := by
  obtain ⟨hw, hI⟩ := hI
  have h0 : h = 0 → plk0 m → isD (ls 0).st ∧ (ls 0).cf < ts := fun hh hp => by
    have := hL (by obtain ⟨_, hp1, hp2, _⟩ := hp; unfold ov; rw [hp1, hp2]; omega); exact this.2.2
  rcases ful_cases hw hf with ⟨hts, rfl, _⟩ | ⟨rfl, rfl, _, _, _⟩
  · refine ⟨wf_pf hw, ?_⟩
    rcases hI with ⟨hP, hT⟩ | ⟨t, hr⟩
    · refine .inl ⟨pf_frame hw hP hts hm hnC (fun hd => ?_) (fun hd => ?_), ?_⟩
      · obtain ⟨_, m', hm', hc⟩ := hP.dr ts hd
        rw [hm] at hm'; cases hm'
        rcases hc with hc | ⟨hc1, hc2⟩
        · exact hc hok
        · have hh : h = 0 := by
            have h1 := (hw h ts hts).2.2
            rw [au_msg (hw h ts hts).1 hm, hc1.1] at h1; cases h1; rfl
          obtain ⟨hd', hcf⟩ := h0 hh hc1
          rcases hc2 with hc2 | hc2; exact hc2 hd'; omega
      · obtain ⟨_, m', hm', hc⟩ := hP.dc ts hd
        rw [hm] at hm'; cases hm'
        exact hnC (by obtain ⟨hp, hl, _⟩ := hc; unfold ov; rw [hp, hl]; omega)
      · have := gT_snoc (h := h) (o' := pfO σ.o h ts) (l' := ls h) hT he hs hld (fun _ h => h) (fun _ h => h)
          (fun _ _ _ _ _ => rfl)
        rwa [upd_same] at this
    · exact .inr ⟨t, rob_ful hw hr hf hm (fun _ => ⟨hok, h0⟩) (fun hd => .inl ⟨hd, Nat.le_refl _⟩)⟩
  · refine ⟨wf_ip hw, ?_⟩
    rcases hI with ⟨hP, hT⟩ | ⟨t, hr⟩
    · refine .inl ⟨ip_frame hw hP hm hnC hnF (fun hov => .inl ⟨(hP.s0.2.2.1).1 (hL hov).2.2.1, (hL hov).2.1⟩), ?_⟩
      have := gT_snoc (h := h) (o' := { σ.o with n := σ.o.n + 1 }) (l' := ls h) hT he hs hld (fun _ h => h) (fun _ h => h)
        (fun _ _ _ _ _ => rfl)
      rwa [upd_same] at this
    · refine .inr ⟨t, rob_ful hw hr hf hm (fun hts => ?_) (fun hd => .inl ⟨hd, Nat.le_refl _⟩)⟩
      exact absurd (hw h _ hts).2.1 (by omega)

end invsteps

end Weak.Prom.OB.E4
