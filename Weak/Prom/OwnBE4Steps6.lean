/-
Weak/Prom: **E-b4 — the protocol's step lemmas, part 6: the AMO leaf, the initial state** (stage E-b4; plan rev 7
§4 "(b1) pull": the agent pulled the lock for the acquirer at the append of its acquire-shaped message; the AMO
that reads a live zero through a clean window CONSUMES the pull).

* `own_good` — consuming a pull: `pulled h u` → `owned h u` at `h`'s AMO fulfil;
* `inv_amoS` — a SUCCESSFUL acquire (byte 0 read zero from `t0`, no other hart's write to it in `(t0, ts)`): the
  source is robust dead (spoiled), or a live zero, and then the taker invariant (`tk1` for a promise, `tk2` +
  an in-place pull for an in-place AMO) makes the hart the owner;
* `inv_amoF` — a failed attempt;
* `inv_init` — the initial state: lifetime 1, dead, hart 0 holds everything.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Steps5

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

/-- The holding stage of hart `h`. -/
def hS (h : Nat) : Stg := if h = 0 then .H0 else .H1

theorem upd_upd {α : Type} (f : Nat → α) (h : Nat) (a b : α) : upd (upd f h a) h b = upd f h b := by
  funext j; by_cases e : j = h <;> simp [upd, e]

section amo

variable {M : List PMsg} {σ : TSt (List Nat)} {S : PS} {ls : Nat → Loc}

/-- The acquiring stage. -/
def acqSt (ls : Nat → Loc) (h : Nat) : Prop := (h = 0 ∧ (ls 0).st = .P) ∨ ((h = 1 ∨ h = 2) ∧ (ls h).st = .A)

theorem acq_fresh {o : OSt (List Nat)} (hP : GoodP M o S ls) {h : Nat} (ha : acqSt ls h) : fresh S ls h := by
  rcases ha with ⟨rfl, e⟩ | ⟨hh, e⟩
  · exact .inl ⟨rfl, e⟩
  · exact .inr ⟨hh, ((hP.sA h hh).2.2.1 (by rw [e]; simp)).1, .inr e⟩

theorem acq_nd {o : OSt (List Nat)} (hP : GoodP M o S ls) {h : Nat} (ha : acqSt ls h) : S.ls ≠ .dead := by
  rcases ha with ⟨rfl, e⟩ | ⟨hh, e⟩
  · exact fun d => by have := (hP.s0.2.2.1).2 d; rw [e] at this; simp [isD] at this
  · exact ((hP.sA h hh).2.2.1 (by rw [e]; simp)).2.1

theorem acq_pub {o : OSt (List Nat)} (hP : GoodP M o S ls) {h : Nat} (ha : acqSt ls h) : S.pubT S.lt = (ls h).p := by
  rcases ha with ⟨rfl, e⟩ | ⟨hh, e⟩
  · exact hP.s0.2.2.2.2.1 (.inl e)
  · exact ((hP.sA h hh).2.2.1 (by rw [e]; simp)).2.2

theorem acq_h3 {h : Nat} (ha : acqSt ls h) : h < 3 := by rcases ha with ⟨e, _⟩ | ⟨e, _⟩ <;> omega

/-- **CONSUMING THE PULL**: the pulled hart's AMO fulfil from a promise makes it the owner. -/
theorem own_good {o : OSt (List Nat)} (hw : WFp M o) (hP : GoodP M o S ls) {h u ts : Nat}
    (hpl : S.ls = .pulled h u) (hts : ts ∈ o.pr h) (hm : msgAt M ts = some (acqM h)) (ha : acqSt ls h) :
    GoodP M (pfO o h ts) { S with ls := .owned h u } (upd ls h { ls h with st := hS h, u := u }) := by
  have hpe := fun t => pend_pf (M := M) (o := o) (t := t) hw hts
  have hh3 := acq_h3 ha
  have hfr := acq_fresh hP ha
  obtain ⟨hhold, htst⟩ := hP.hpo h u (.inl hpl)
  have ei : upd ls h { ls h with st := hS h, u := u } h = { ls h with st := hS h, u := u } := upd_eq _ _ _
  have e0 : ∀ j, j ≠ h → upd ls h { ls h with st := hS h, u := u } j = ls j := fun j hj => upd_ne _ _ hj
  have hnDr : ¬ S.Dr ts := fun d => by
    obtain ⟨_, m', hm', hc⟩ := hP.dr ts d
    rw [hm] at hm'; cases hm'
    rcases hc with hc | ⟨hc, _⟩
    · exact hc (okS_acq hh3)
    · exact plk0_ne_acq hc rfl
  have hnDc : ¬ S.Dc ts := fun d => by
    obtain ⟨_, m', hm', hc⟩ := hP.dc ts d
    rw [hm] at hm'; cases hm'; exact c3_ovL hc (acq_ovL h)
  have hnD : ¬ isD (upd ls h { ls h with st := hS h, u := u } 0).st := by
    by_cases eh : h = 0
    · subst eh; rw [ei]; simp [hS, isD]
    · rw [e0 0 (Ne.symm eh)]; exact fun d => acq_nd hP ha ((hP.s0.2.2.1).1 d)
  have hnd := acq_nd hP ha
  constructor
  · intro t ht
    obtain ⟨b1, m', b2, b3⟩ := hP.dr t ht
    refine ⟨(hpe t).2 ⟨b1, fun e => hnDr (e ▸ ht)⟩, m', b2, ?_⟩
    rcases b3 with b3 | ⟨b3, _⟩
    · exact .inl b3
    · exact .inr ⟨b3, .inl hnD⟩
  · intro t ht; exact ⟨(hpe t).2 ⟨(hP.dc t ht).1, fun e => hnDc (e ▸ ht)⟩, (hP.dc t ht).2⟩
  · intro t a ht hh ha'
    by_cases ea : a = h
    · subst ea; rw [ei]; exact hP.dcH t _ ht hh ha'
    · rw [e0 a ea]; exact hP.dcH t a ht hh ha'
  · exact hP.tsle
  · exact hP.tsok
  · intro t m' h1 h2 h3 h4
    rcases hP.later t m' h1 h2 h3 h4 with c | c | ⟨b, b1, b2, b3, b4, b5⟩
    · exact .inl c
    · exact .inr (.inl c)
    · refine .inr (.inr ⟨b, b1, b2, b3, (hpe t).2 ⟨b4, fun e => ?_⟩, b5⟩)
      subst e; rw [hm] at h3; cases h3; exact acq_ovC h h4
  · intro e; cases e
  · intro e; cases e
  · intro j v e; rcases e with e | e <;> cases e; exact ⟨hhold, htst⟩
  · intro _; exact hP.gdp hnd
  · refine ⟨fun e => absurd (by simp [isD, e]) hnD, fun e => absurd (by rcases e with e | e <;> simp [isD, e]) hnD,
      fun e => absurd (by simp [isD, e]) hnD⟩
  · intro j v e; cases e
  · intro j v e; cases e
    by_cases e0' : h = 0
    · subst e0'; rw [ei]; exact .inl ⟨rfl, by simp [hS], rfl⟩
    · rw [ei]; exact .inr ⟨by omega, .inl (by simp [hS, e0']), rfl⟩
  · intro j hj hj1
    by_cases ej : j = h
    · subst ej; exact hP.hpre j u hpl
    · rw [e0 j ej] at hj1
      have := (hP.sA j hj).2.2.2.1 (.inl hj1); rw [hpl] at this; cases this
  · intro e
    by_cases eh : h = 0
    · subst eh; exact hP.hpre 0 u hpl
    · rw [e0 0 (Ne.symm eh)] at e; have := hP.s0.2.2.2.2.2.1 e; rw [hpl] at this; cases this
  · intro j v e; rcases e with e | e <;> cases e; exact hP.lk h u (.inl hpl)
  · intro j ts' t0 a1 a2 a3 a4 a5 a6 a7 a8
    have hj : j ≠ h := fun e => by
      subst e; unfold fresh at a2
      rcases a2 with ⟨e, e'⟩ | ⟨e, _, e' | e'⟩
      · subst e; rw [ei] at e'; simp [hS] at e'
      · rw [ei] at e'; simp [hS, show j ≠ 0 by omega] at e'
      · rw [ei] at e'; simp [hS, show j ≠ 0 by omega] at e'
    have a2' : fresh S ls j := by
      unfold fresh at a2 ⊢
      rw [e0 j hj] at a2
      by_cases e : h = 0
      · subst e; rw [ei] at a2; rcases a2 with ⟨e', _⟩ | a2
        · omega
        · exact .inr a2
      · rw [e0 0 (Ne.symm e)] at a2; exact a2
    have a4' : ts' ∈ o.pr j := by
      by_cases e : j = h
      · exact absurd e hj
      · simp only [upd_ne _ _ e] at a4; exact a4
    obtain ⟨u', _, e⟩ := hP.tk1 j ts' t0 hnd a2' a3 a4' a5 a6 a7 a8
    rw [hpl] at e; cases e; exact absurd rfl hj
  · intro j t0 a1 a2 a3 a4 a5
    have hj : j ≠ h := fun e => by
      subst e; unfold fresh at a2
      rcases a2 with ⟨e, e'⟩ | ⟨e, _, e' | e'⟩
      · subst e; rw [ei] at e'; simp [hS] at e'
      · rw [ei] at e'; simp [hS, show j ≠ 0 by omega] at e'
      · rw [ei] at e'; simp [hS, show j ≠ 0 by omega] at e'
    have a2' : fresh S ls j := by
      unfold fresh at a2 ⊢
      rw [e0 j hj] at a2
      by_cases e : h = 0
      · subst e; rw [ei] at a2; rcases a2 with ⟨e', _⟩ | a2
        · omega
        · exact .inr a2
      · rw [e0 0 (Ne.symm e)] at a2; exact a2
    rcases hP.tk2 j t0 hnd a2' a3 a4 a5 with e | ⟨u', e⟩ <;> rw [hpl] at e <;> cases e; exact absurd rfl hj
  · exact hP.fl
  · intro k hk; exact ⟨(hP.pubk k hk).1, fun _ => by simp⟩
  · intro j k hj hk
    by_cases ej : j = h
    · subst ej; rw [ei]; exact hP.dnk j k hj hk
    · rw [e0 j ej]; exact hP.dnk j k hj hk
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
    by_cases eh : h = 0
    · subst eh
      rw [ei, e0 1 (by omega), e0 2 (by omega)]
      obtain ⟨_, hP0⟩ : 0 = 0 ∧ (ls 0).st = .P := by rcases ha with h' | ⟨h', _⟩; exact h'; omega
      refine ⟨b1, b2, ⟨fun d => absurd d (by simp [hS, isD]), fun e => (by cases e)⟩, .inr (.inr (by simp [hS])),
        fun _ => b5 (.inl hP0), fun _ => rfl, b7, b8, b9⟩
    · rw [e0 0 (Ne.symm eh)]
      refine ⟨b1, b2, ⟨fun d => absurd d (fun d' => hnd (b3.1 d')), fun e => (by cases e)⟩, b4, b5,
        fun e => (by have := b6 e; rw [hpl] at this; cases this), fun d => ?_, fun d => ?_, b9⟩
      · by_cases e : (1 : Nat) = h
        · subst e; rw [ei]; exact b7 d
        · rw [e0 1 e]; exact b7 d
      · by_cases e : (2 : Nat) = h
        · subst e; rw [ei]; exact b8 d
        · rw [e0 2 e]; exact b8 d
  · intro j hj
    by_cases ej : j = h
    · subst ej; rw [ei]
      obtain ⟨b1, _, b3, _, b5⟩ := hP.sA j hj
      have hA : (ls j).st = .A := by rcases ha with ⟨e, _⟩ | ⟨_, e⟩; omega; exact e
      obtain ⟨c1, _, c3⟩ := b3 (by rw [hA]; simp)
      have hld : (ls j).ld = none := by
        cases e : (ls j).ld with
        | none => rfl
        | some _ => have := b5 (by rw [e]; simp); rw [hA] at this; cases this
      refine ⟨.inl c1, .inr (.inr (.inl (by simp [hS, show j ≠ 0 by omega]))), fun _ => ⟨c1, by simp, c3⟩,
        fun _ => rfl, fun e => (by simp only at e; rw [hld] at e; exact absurd rfl e)⟩
    · rw [e0 j ej]
      obtain ⟨b1, b2, b3, b4, b5⟩ := hP.sA j hj
      refine ⟨?_, b2, fun e => ?_, fun e => ?_, b5⟩
      · rcases b1 with b1 | ⟨b1, b1', _⟩
        · exact .inl b1
        · exact .inr ⟨b1, b1', by simp⟩
      · obtain ⟨c1, _, c3⟩ := b3 e; exact ⟨c1, by simp, c3⟩
      · have := b4 e; rw [hpl] at this; cases this

/-- The state after an agent append of hart `h`'s message. -/
abbrev agO (o : OSt (List Nat)) (h : Nat) : OSt (List Nat) := { o with n := o.n + 1, pr := upd o.pr h ({o.n + 1} ∪ o.pr h) }

theorem wf_ag {o : OSt (List Nat)} (hw : WFp M o) {h : Nat} (hau : au M (o.n + 1) = some h) : WFp M (agO o h) := by
  intro a t ht
  rcases pr_ag ht with ht | ⟨rfl, rfl⟩
  · obtain ⟨u1, u2, u3⟩ := hw a t ht; exact ⟨u1, by simp only; omega, u3⟩
  · exact ⟨by omega, by simp only; omega, hau⟩

theorem ag_ful_eq {o : OSt (List Nat)} (hw : WFp M o) (h : Nat) : pfO (agO o h) h (o.n + 1) = { o with n := o.n + 1 } := by
  have := ip_eq (o := o) hw h
  simp only [pfO, agO, upd_eq, upd_upd]
  exact this

theorem mem_agO {o : OSt (List Nat)} (h : Nat) : o.n + 1 ∈ (agO o h).pr h := by
  simp only [agO, upd_eq, elemOfUnion, elemOfSingleton]; exact .inl trivial

/-- A SUCCESSFUL ACQUIRE. -/
theorem inv_amoS {h ts t0 : Nat} {rc : Prop} {o' : OSt (List Nat)} {e : PEv} (hI : Inv M σ S ls) (ha : acqSt ls h)
    (hf : fulO M h σ.o rc ts o') (hm : msgAt M ts = some (acqM h))
    (hz : memByte img7 (M.take o'.n) t0 Lk = some 0) (ht0 : t0 < ts) (hcl : clean M h t0 ts) (hp : (ls h).p < ts)
    (he : ∀ tvs, ¬ isCLd e tvs) (hs : ∀ ts, ¬ isCSt e ts) :
    ∃ S' u, u ≤ ts ∧ Inv M (nxT σ h o' e) S' (upd ls h { ls h with st := hS h, u := u }) := by
  obtain ⟨hw, hI⟩ := hI
  have hh3 := acq_h3 ha
  obtain ⟨hpe, hpr, hts1, hnn, hw'⟩ := ful_post hw hf
  have hl0 : isD (upd ls h { ls h with st := hS h, u := ts } 0).st → isD (ls 0).st ∧ (ls 0).cf ≤
      (upd ls h { ls h with st := hS h, u := ts } 0).cf ∨ σ.o.n < (upd ls h { ls h with st := hS h, u := ts } 0).cf :=
    fun d => by
      by_cases eh : h = 0
      · subst eh; rw [upd_eq] at d; simp [hS, isD] at d
      · rw [upd_ne _ _ (Ne.symm eh)] at d ⊢; exact .inl ⟨d, Nat.le_refl _⟩
  have hl0' : ∀ u, (upd ls h { ls h with st := hS h, u := u } 0).st = (upd ls h { ls h with st := hS h, u := ts } 0).st ∧
      (upd ls h { ls h with st := hS h, u := u } 0).cf = (upd ls h { ls h with st := hS h, u := ts } 0).cf := by
    intro u; by_cases eh : h = 0
    · subst eh; simp [upd_eq]
    · simp [upd_ne _ _ (Ne.symm eh)]
  have hrob : ∀ t, Rob M σ.o (ls 0) t → ∀ u, Rob M o' (upd ls h { ls h with st := hS h, u := u } 0) t := by
    intro t hr u
    have := rob_ful (l0' := upd ls h { ls h with st := hS h, u := ts } 0) hw hr hf hm
      (fun _ => ⟨okS_acq hh3, fun _ h => absurd rfl (plk0_ne_acq h)⟩) hl0
    obtain ⟨c1, m', c2, c3⟩ := this
    refine ⟨c1, m', c2, ?_⟩
    rw [(hl0' u).1, (hl0' u).2]; exact c3
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · exact ⟨S, ts, Nat.le_refl _, hw', .inr ⟨t', hrob t' hr ts⟩⟩
  obtain ⟨hz1, hz2⟩ := memByte_pre hz
  by_cases hdr : S.Dr t0
  · exact ⟨S, ts, Nat.le_refl _, hw', .inr ⟨t0, hrob t0 (hP.dr t0 hdr) ts⟩⟩
  have hnd0 : nd0 M S t0 := ⟨hdr, hz1⟩
  have hfr := acq_fresh hP ha
  have hnd := acq_nd hP ha
  have hpub : S.pubT S.lt < ts := by rw [acq_pub hP ha]; exact hp
  have hgT : ∀ (S' : PS) (o2 : OSt (List Nat)) (u : Nat), (∀ t, S.Dr t → S'.Dr t) → (∀ t, S.Dc t → S'.Dc t) →
      S'.tstar = S.tstar → GoodT M (nxT σ h o2 e) S' (upd ls h { ls h with st := hS h, u := u }) :=
    fun S' o2 u a b c => gT_snoc (h := h) hT he (.inr hs) (by
      simp only
      rcases ha with ⟨rfl, _⟩ | ⟨hh, hA⟩
      · exact hP.s0.2.2.2.2.2.2.2.2
      · cases e' : (ls h).ld with
        | none => rfl
        | some _ => have := (hP.sA h hh).2.2.2.2 (by rw [e']; simp); rw [hA] at this; cases this) a b
      (fun _ _ _ _ _ => c)
  rcases ful_cases hw hf with ⟨hts, rfl, _⟩ | ⟨rfl, rfl, _, hau, hn⟩
  · obtain ⟨u, hu, hpl⟩ := hP.tk1 h ts t0 hnd hfr hpub hts hm hnd0 ht0 hcl
    exact ⟨_, u, hu, hw', .inl ⟨own_good hw hP hpl hts hm ha, hgT _ _ _ (fun _ h => h) (fun _ h => h) rfl⟩⟩
  · have hau' : au M (σ.o.n + 1) = some h := by rw [au_msg (by omega) hm]; rfl
    have hwa := wf_ag hw hau'
    rcases hP.tk2 h t0 hnd hfr hnd0 (by omega) hcl with hfr' | ⟨u, hpl⟩
    · have hP1 := agent_p hw hP hm hh3 hfr'
      have hP2 := own_good (S := { S with ls := .pulled h (σ.o.n + 1), hold := some h, tst := σ.o.n + 1 }) hwa hP1 rfl
        (mem_agO h) hm (by unfold acqSt at ha ⊢; exact ha)
      rw [ag_ful_eq hw h] at hP2
      exact ⟨_, σ.o.n + 1, Nat.le_refl _, hw', .inl ⟨hP2, hgT _ _ _ (fun _ h => h) (fun _ h => h) rfl⟩⟩
    · have hP1 := agent_np hP hm rfl (fun ⟨_, _, e'⟩ => by rw [hpl] at e'; cases e')
      have hP2 := own_good hwa hP1 (by simp only [agS]; exact hpl) (mem_agO h) hm ha
      rw [ag_ful_eq hw h] at hP2
      refine ⟨_, u, ?_, hw', .inl ⟨hP2, hgT _ _ _ (fun _ h => .inl h) (fun _ h => .inl h) rfl⟩⟩
      have := (hP.lk h u (.inl hpl)).2.2.1; omega

/-- A FAILED ATTEMPT. -/
theorem inv_amoF {h ts : Nat} {rc : Prop} {o' : OSt (List Nat)} {e : PEv} (hI : Inv M σ S ls) (ha : acqSt ls h)
    (hf : fulO M h σ.o rc ts o') (hm : msgAt M ts = some (acqM h))
    (he : ∀ tvs, ¬ isCLd e tvs) (hs : ∀ ts, ¬ isCSt e ts) :
    ∃ S', Inv M (nxT σ h o' e) S' ls := by
  obtain ⟨hw, hI⟩ := hI
  have hh3 := acq_h3 ha
  obtain ⟨hpe, hpr, hts1, hnn, hw'⟩ := ful_post hw hf
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · exact ⟨S, hw', .inr ⟨t', rob_ful hw hr hf hm (fun _ => ⟨okS_acq hh3, fun _ h => absurd rfl (plk0_ne_acq h)⟩)
      (fun d => .inl ⟨d, Nat.le_refl _⟩)⟩⟩
  have hld : (ls h).ld = none := by
    rcases ha with ⟨rfl, _⟩ | ⟨hh, hA⟩
    · exact hP.s0.2.2.2.2.2.2.2.2
    · cases e' : (ls h).ld with
      | none => rfl
      | some _ => have := (hP.sA h hh).2.2.2.2 (by rw [e']; simp); rw [hA] at this; cases this
  have hgT : ∀ (S' : PS) (o2 : OSt (List Nat)), (∀ t, S.Dr t → S'.Dr t) → (∀ t, S.Dc t → S'.Dc t) →
      S'.tstar = S.tstar → GoodT M (nxT σ h o2 e) S' ls := fun S' o2 a b c => by
    have := gT_snoc (h := h) (o' := o2) (l' := ls h) hT he (.inr hs) hld a b (fun _ _ _ _ _ => c)
    rwa [upd_same] at this
  have hnd := acq_nd hP ha
  have hnDr : ¬ S.Dr ts := fun d => by
    obtain ⟨_, m', hm', hc⟩ := hP.dr ts d
    rw [hm] at hm'; cases hm'
    rcases hc with hc | ⟨hc, _⟩
    · exact hc (okS_acq hh3)
    · exact plk0_ne_acq hc rfl
  have hnDc : ¬ S.Dc ts := fun d => by
    obtain ⟨_, m', hm', hc⟩ := hP.dc ts d
    rw [hm] at hm'; cases hm'; exact c3_ovL hc (acq_ovL h)
  rcases ful_cases hw hf with ⟨hts, rfl, _⟩ | ⟨rfl, rfl, _, hau, hn⟩
  · exact ⟨S, hw', .inl ⟨pf_frame hw hP hts hm (acq_ovC h) hnDr hnDc, hgT _ _ (fun _ h => h) (fun _ h => h) rfl⟩⟩
  · have hau' : au M (σ.o.n + 1) = some h := by rw [au_msg (by omega) hm]; rfl
    have hwa := wf_ag hw hau'
    by_cases hfr : S.ls = .free
    · have hP1 := agent_p hw hP hm hh3 hfr
      have hP2 := pf_frame hwa hP1 (mem_agO h) hm (acq_ovC h) (fun d => by
        obtain ⟨_, m', hm', hc⟩ := hP1.dr _ d
        rw [hm] at hm'; cases hm'
        rcases hc with hc | ⟨hc, _⟩
        · exact hc (okS_acq hh3)
        · exact plk0_ne_acq hc rfl) (fun d => by
        obtain ⟨_, m', hm', hc⟩ := hP1.dc _ d
        rw [hm] at hm'; cases hm'; exact c3_ovL hc (acq_ovL h))
      rw [ag_ful_eq hw h] at hP2
      exact ⟨_, hw', .inl ⟨hP2, hgT _ _ (fun _ h => h) (fun _ h => h) rfl⟩⟩
    · have hL : ∃ j u, S.ls = .pulled j u ∨ S.ls = .owned j u := by
        cases e' : S.ls with
        | dead => exact absurd e' hnd
        | free => exact absurd e' hfr
        | pulled j u => exact ⟨j, u, .inl rfl⟩
        | owned j u => exact ⟨j, u, .inr rfl⟩
      exact ⟨S, hw', .inl ⟨ip_frame hw hP hm (acq_ovC h) (acq_ovF h) (fun _ => .inr ⟨⟨h, rfl⟩, hL⟩),
        hgT _ _ (fun _ h => h) (fun _ h => h) rfl⟩⟩

end amo

end Weak.Prom.OB.E4
