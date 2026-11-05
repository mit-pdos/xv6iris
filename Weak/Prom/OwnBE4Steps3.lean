/-
Weak/Prom: **E-b4 — the protocol's step lemmas, part 3: the critical section, the release, the done byte**
(stage E-b4; plan rev 7 §4 (b2-own): the holder's field promises are backed, everyone else's are dead).

* `inv_csld` — the holder's field load: every byte is the latest live field write's, or the prefix holds a dead
  message (the hart's own pending field promise read early is reclassified dead: it can never be fulfilled);
* `inv_csst` — the holder's field store: it becomes the latest live write; with no dead message the pair is
  mutually exclusive (`pairOk`: its load read the LATEST text-shaped field store below it);
* `inv_rel` — the in-place release: the lock is free again, the holder's unfulfilled field promises are dead;
* `inv_done` — the in-place done byte: the acquirer leaves the round.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Steps2

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
open Weak.Prom.OA.E4 (q7 img7 q7_snoc q7_ld q7_pair pairOk)
open PLabel

section cs

variable {M : List PMsg} {σ : TSt (List Nat)} {S : PS} {ls : Nat → Loc}

theorem c3_byte {m : PMsg} (h : cmP3 m) {j : Nat} (hj : j < 8) : (m.byteAt (Ct + j)).isSome = true := by
  obtain ⟨hp, hl, _⟩ := h
  rw [← hp, Weak.Prom.OA.byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl

theorem c3_ovC {m : PMsg} (h : cmP3 m) : ov m Ct 8 := by
  obtain ⟨hp, hl, _⟩ := h; unfold ov; rw [hp, hl]; omega

theorem gd_msg {t : Nat} (h : gd M t) : 1 ≤ t ∧ ∃ m, msgAt M t = some m ∧ cmP3 m := by
  obtain ⟨m, hm, hc⟩ := clsB_iff.1 h.1
  refine ⟨?_, m, hm, hc⟩
  rcases Nat.eq_zero_or_pos t with rfl | h; · cases hm
  · exact h

/-- **A FIELD BYTE'S SOURCE** read below a floor covering the latest live write. -/
theorem fsrc {o : OSt (List Nat)} (hP : GoodP M o S ls) (hnd : S.ls ≠ .dead) {j t W : Nat} {b : BitVec 8}
    (hj : j < 8) (hb1 : memByte img7 M t (Ct + j) = some b) (htn : t ≤ o.n)
    (hnw : ¬ writesIn (M.take o.n) (Ct + j) t W) (hW : S.tstar ≤ W) :
    t = S.tstar ∨ (S.tstar < t ∧ t ≤ o.n ∧ ∃ m, msgAt M t = some m ∧ (S.Dr t ∨ S.Dc t ∨
      (∃ a, S.hold = some a ∧ m.tid = some a ∧ S.tst < t ∧ pend M o t ∧ cmP3 m))) := by
  obtain ⟨hs1, ms, hms, hcs⟩ := gd_msg (hP.gdp hnd)
  rcases Nat.lt_trichotomy t S.tstar with hlt | heq | hgt
  · exfalso; apply hnw
    refine ⟨S.tstar, hlt, hW, ms, ?_, c3_byte hcs hj⟩
    rw [List.getElem?_take, if_pos (by have := hP.tsle.1; omega)]; rw [← msgAt_sub hs1]; exact hms
  · exact .inl heq
  · obtain ⟨m, hm, _, _, hbm⟩ := memByte_ov (by omega) hb1
    exact .inr ⟨hgt, htn, m, hm, hP.later t m hgt htn hm (ov_of (a := Ct) (n := 8) (x := Ct + j) (by omega)
      (by rw [hbm]; rfl))⟩

/-- The field-load's new dead set: the hart's own pending field promises it read. -/
def ldS (S : PS) (tvs : List (Nat × BitVec 8)) : PS :=
  { S with Dc := fun x => S.Dc x ∨ (x ∈ tvs.map Prod.fst ∧ S.tstar < x ∧ ¬ S.Dr x ∧ ¬ S.Dc x) }

/-- **THE HOLDER'S FIELD LOAD**. -/
theorem inv_csld {i : Nat} {tvs : List (Nat × BitVec 8)} {a : List Dsrc} (hI : Inv M σ S ls) (hi : i = 1 ∨ i = 2)
    (hH : (ls i).st = .H1) (hld0 : (ls i).ld = none)
    (hby : ∀ (j : Nat) t b, tvs[j]? = some (t, b) → j < 8 ∧ memByte img7 M t (Ct + j) = some b ∧ t ≤ σ.o.n ∧
      ¬ writesIn (M.take σ.o.n) (Ct + j) t (ls i).u) :
    ∃ S', Inv M (nxT σ i σ.o (LLoad false false Ct tvs a, none)) S' (upd ls i { ls i with ld := some tvs }) := by
  obtain ⟨hw, hI⟩ := hI
  have hi0 : i ≠ 0 := by omega
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · exact ⟨S, hw, .inr ⟨t', by rw [upd0 hi0]; exact hr⟩⟩
  have hown := (hP.sA i hi).2.2.2.1 (.inl hH)
  obtain ⟨hhold, htst⟩ := hP.hpo i _ (.inr hown)
  have hts := hP.h1 i hi hH
  have hnd : S.ls ≠ .dead := by rw [hown]; simp
  have e0 : ∀ j, j ≠ i → upd ls i { ls i with ld := some tvs } j = ls j := fun j hj => upd_ne _ _ hj
  have ei : upd ls i { ls i with ld := some tvs } i = { ls i with ld := some tvs } := upd_eq _ _ _
  -- every byte: the latest live write, or a dead / own pending message
  have hsrc : ∀ p ∈ tvs, p.1 = S.tstar ∨ (S.tstar < p.1 ∧ (S.Dr p.1 ∨ S.Dc p.1 ∨
      (pend M σ.o p.1 ∧ ∃ m, msgAt M p.1 = some m ∧ cmP3 m))) := by
    intro p hp
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hp
    obtain ⟨hj8, hmb, htn, hnw⟩ := hby j p.1 p.2 (by rw [hj])
    rcases fsrc hP hnd hj8 hmb htn hnw (by omega) with e | ⟨hgt, _, m, hm, c | c | ⟨_, _, _, _, c1, c2⟩⟩
    · exact .inl e
    · exact .inr ⟨hgt, .inl c⟩
    · exact .inr ⟨hgt, .inr (.inl c)⟩
    · exact .inr ⟨hgt, .inr (.inr ⟨c1, m, hm, c2⟩)⟩
  have hfr : ∀ h, fresh S (upd ls i { ls i with ld := some tvs }) h ↔ fresh S ls h := by
    intro h; unfold fresh
    by_cases eh : h = i
    · subst eh; rw [ei, e0 0 (by omega)]
    · rw [e0 h eh, e0 0 (by omega)]
  refine ⟨ldS S tvs, hw, .inl ⟨⟨fun t ht => by rw [e0 0 (by omega)]; exact hP.dr t ht, fun t ht => ?_,
    fun t a ht hh ha => ?_, hP.tsle, hP.tsok, fun t m h1 h2 h3 h4 => ?_,
    fun e => (by rw [e0 0 (by omega)]; exact hP.hdead e), hP.hfree, hP.hpo, hP.gdp, by rw [e0 0 (by omega)]; exact hP.h0f, hP.hpre, fun h u ho => ?_,
    fun j hj hj1 => ?_, by rw [e0 0 (by omega)]; exact hP.h0o, hP.lk,
    fun h ts t0 a1 a2 a3 a4 a5 a6 => hP.tk1 h ts t0 a1 ((hfr h).1 a2) a3 a4 a5 ⟨fun d => a6.1 d, a6.2⟩,
    fun h t0 a1 a2 a3 => hP.tk2 h t0 a1 ((hfr h).1 a2) ⟨fun d => a3.1 d, a3.2⟩, hP.fl, hP.pubk,
    fun j k hj hk => ?_, ?_, fun j hj => ?_⟩, ?_⟩⟩
  · rcases ht with ht | ⟨hmem, hgt, hnr, hnc⟩
    · exact hP.dc t ht
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hmem
      rcases hsrc p hp with e | ⟨_, c | c | ⟨c1, c2⟩⟩
      · omega
      · exact absurd c hnr
      · exact absurd c hnc
      · exact ⟨c1, c2⟩
  · rcases ht with ht | ⟨hmem, hgt, hnr, hnc⟩
    · by_cases ea : a = i
      · subst ea; rw [ei]
        rcases hP.dcH t _ ht hh ha with c | ⟨tvs', c, _⟩ | c
        · exact .inl c
        · rw [hld0] at c; cases c
        · exact .inr (.inr c)
      · rw [e0 a ea]; exact hP.dcH t a ht hh ha
    · have : a = i := by have hh' : S.hold = some a := hh; rw [hhold] at hh'; cases hh'; rfl
      subst this; rw [ei]; exact .inr (.inl ⟨tvs, rfl, hmem⟩)
  · rcases hP.later t m h1 h2 h3 h4 with c | c | c
    · exact .inl c
    · exact .inr (.inl (.inl c))
    · exact .inr (.inr c)
  · rcases hP.hown h u ho with ⟨rfl, b⟩ | ⟨hh, b1, b2⟩
    · rw [e0 0 (by omega)]; exact .inl ⟨rfl, b⟩
    · by_cases eh : h = i
      · subst eh; rw [ei]; exact .inr ⟨hh, b1, b2⟩
      · rw [e0 h eh]; exact .inr ⟨hh, b1, b2⟩
  · by_cases ej : j = i
    · subst ej; exact hts
    · rw [e0 j ej] at hj1; exact hP.h1 j hj hj1
  · by_cases ej : j = i
    · subst ej; rw [ei]; exact hP.dnk j k hj hk
    · rw [e0 j ej]; exact hP.dnk j k hj hk
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
    rw [e0 0 (by omega)]
    refine ⟨b1, b2, b3, b4, b5, b6, fun d => ?_, fun d => ?_, b9⟩
    · by_cases e : (1 : Nat) = i
      · subst e; rw [ei]; exact b7 d
      · rw [e0 1 e]; exact b7 d
    · by_cases e : (2 : Nat) = i
      · subst e; rw [ei]; exact b8 d
      · rw [e0 2 e]; exact b8 d
  · by_cases ej : j = i
    · subst ej; rw [ei]
      obtain ⟨b1, b2, b3, b4, _⟩ := hP.sA j hj
      exact ⟨b1, b2, b3, b4, fun _ => hH⟩
    · rw [e0 j ej]; exact hP.sA j hj
  · -- the trace clauses
    have hcl : clr (ldS S tvs) → clr S := fun c t => ⟨(c t).1, fun d => (c t).2 (.inl d)⟩
    have hall : clr (ldS S tvs) → ∀ p ∈ tvs, p.1 = S.tstar := by
      intro c p hp
      rcases hsrc p hp with e | ⟨hgt, d | d | ⟨d1, d2⟩⟩
      · exact e
      · exact absurd d (c _).1
      · exact absurd (.inl d) (c _).2
      · exfalso; apply (c p.1).2; right
        refine ⟨List.mem_map.2 ⟨p, hp, rfl⟩, hgt, fun d => (c _).1 d, fun d => (c _).2 (.inl d)⟩
    refine ⟨by simp only [nxT, upd_ne _ _ (Ne.symm hi0)]; exact hT.t0, fun c => ?_, fun j tvs' hj hl => ?_⟩
    · have hq := hT.tq (hcl c)
      have hg : ∀ p ∈ tvs, gd M p.1 := fun p hp => by rw [hall c p hp]; exact hP.gdp hnd
      rcases hi with rfl | rfl
      · simp only [nxT, upd_eq, upd_ne _ _ (show (2 : Nat) ≠ 1 by decide)]; exact ⟨q7_ld hq.1 hg, hq.2⟩
      · simp only [nxT, upd_eq, upd_ne _ _ (show (1 : Nat) ≠ 2 by decide)]; exact ⟨hq.1, q7_ld hq.2 hg⟩
    · by_cases ej : j = i
      · subst ej
        rw [ei] at hl; simp only [Option.some.injEq] at hl; subst hl
        exact ⟨⟨σ.tr j, a, by simp only [nxT, upd_eq]⟩, fun c => hall c⟩
      · rw [e0 j ej] at hl
        obtain ⟨b1, b2⟩ := hT.tld j tvs' hj hl
        exact ⟨by simp only [nxT, upd_ne _ _ ej]; exact b1, fun c => b2 (hcl c)⟩

/-- The facts of a fulfil, either shape. -/
theorem ful_post {o o' : OSt (List Nat)} (hw : WFp M o) {h ts : Nat} {rc : Prop} (hf : fulO M h o rc ts o') :
    (∀ x, pend M o' x ↔ pend M o x ∧ x ≠ ts) ∧ (∀ a x, x ∈ o'.pr a → x ∈ o.pr a) ∧ 1 ≤ ts ∧
    ((o'.n = o.n ∧ ts ≤ o.n ∧ ts ∈ o.pr h) ∨ (o'.n = o.n + 1 ∧ ts = o.n + 1)) ∧ WFp M o' := by
  rcases ful_cases hw hf with ⟨hts, rfl, _⟩ | ⟨rfl, rfl, _, _, _⟩
  · refine ⟨fun x => pend_pf hw hts, fun a x hx => ?_, (hw h ts hts).1, .inl ⟨rfl, (hw h ts hts).2.1, hts⟩,
      wf_pf hw⟩
    by_cases e : a = h
    · subst e; simp only [upd_eq, elemOfDifference] at hx; exact hx.1
    · simp only [upd_ne _ _ e] at hx; exact hx
  · refine ⟨fun x => ⟨fun hx => ⟨hx, fun e => by subst e; have := (pend_le hw hx).2; omega⟩, fun hx => hx.1⟩,
      fun a x hx => hx, by omega, .inr ⟨rfl, rfl⟩, wf_ip hw⟩

/-- The field-store's new state: the latest write is `ts`; the hart's other unfulfilled field promises below it
are dead. -/
def stS (S : PS) (M : List PMsg) (o' : OSt (List Nat)) (i ts : Nat) : PS :=
  { S with tstar := ts, Dc := fun x => S.Dc x ∨ (S.tstar < x ∧ x < ts ∧ pend M o' x ∧ au M x = some i ∧
      ∃ m, msgAt M x = some m ∧ cmP3 m) }

/-- **THE HOLDER'S FIELD STORE**. -/
theorem inv_csst {i ts v : Nat} {rc : Prop} {o' : OSt (List Nat)} {tvs : List (Nat × BitVec 8)} {a c : List Dsrc}
    (hI : Inv M σ S ls) (hi : i = 1 ∨ i = 2) (hH : (ls i).st = .H1) (hld : (ls i).ld = some tvs)
    (hf : fulO M i σ.o rc ts o') (hm : msgAt M ts = some ⟨Ct, toBytes v 8, some i, .plain⟩)
    (hut : (ls i).u < ts) (hlt : ∀ p ∈ tvs, p.1 < ts) :
    ∃ S', Inv M (nxT σ i o' (LStore false false Ct (toBytes v 8) a c, some ts)) S'
      (upd ls i { ls i with st := .H2, ld := none }) := by
  obtain ⟨hw, hI⟩ := hI
  have hi0 : i ≠ 0 := by omega
  have hc3 : cmP3 ⟨Ct, toBytes v 8, some i, .plain⟩ :=
    ⟨rfl, toBytes_len v 8, rfl, by rcases hi with rfl | rfl <;> simp⟩
  have hok : okS ⟨Ct, toBytes v 8, some i, .plain⟩ := ⟨i, by omega, rfl, .inr (.inr (.inl hc3))⟩
  have hnp : ¬ plk0 ⟨Ct, toBytes v 8, some i, .plain⟩ := fun h => by
    have := h.2.1; simp [Lk, Ct, Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y] at this
  obtain ⟨hpe, hpr, hts1, hnn, hw'⟩ := ful_post hw hf
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · have hrob := rob_ful (l0' := ls 0) hw hr hf hm (fun _ => ⟨hok, fun e => absurd e hi0⟩)
      (fun hd => .inl ⟨hd, Nat.le_refl _⟩)
    exact ⟨S, hw', .inr ⟨t', by rw [upd0 hi0]; exact hrob⟩⟩
  have hown := (hP.sA i hi).2.2.2.1 (.inl hH)
  obtain ⟨hhold, htst⟩ := hP.hpo i _ (.inr hown)
  have hts := hP.h1 i hi hH
  have hnd : S.ls ≠ .dead := by rw [hown]; simp
  have hgt : S.tstar < ts := by omega
  have hnDr : ¬ S.Dr ts := fun d => by
    obtain ⟨_, m', hm', hc⟩ := hP.dr ts d
    rw [hm] at hm'; cases hm'
    rcases hc with hc | ⟨hc, _⟩; exact hc hok; exact hnp hc
  have hnDc : ¬ S.Dc ts := fun d => by
    rcases hP.dcH ts i d hhold (by rw [au_msg hts1 hm]) with e | ⟨tvs', e1, e2⟩ | ⟨_, e1, e2⟩
    · omega
    · rw [hld] at e1; cases e1; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 e2; have := hlt p hp; omega
    · omega
  have hnew : ∀ t m', t ≤ o'.n → ¬ t ≤ σ.o.n → msgAt M t = some m' → t = ts ∧ m' = ⟨Ct, toBytes v 8, some i, .plain⟩ :=
    fun t m' h1 h2 h3 => by
      rcases hnn with ⟨e, _⟩ | ⟨e, rfl⟩
      · omega
      · have : t = σ.o.n + 1 := by omega
        subst this; rw [hm] at h3; exact ⟨rfl, (Option.some.inj h3).symm⟩
  have hnle : ∀ x, x < ts → x ≤ σ.o.n := fun x hx => by rcases hnn with ⟨_, e, _⟩ | ⟨_, e⟩ <;> omega
  have e0 : ∀ j, j ≠ i → upd ls i { ls i with st := .H2, ld := none } j = ls j := fun j hj => upd_ne _ _ hj
  have ei : upd ls i { ls i with st := .H2, ld := none } i = { ls i with st := .H2, ld := none } := upd_eq _ _ _
  have hoth : ∀ j, (j = 1 ∨ j = 2) → j ≠ i → (ls j).st ≠ .H1 ∧ (ls j).st ≠ .H2 := fun j hj hne => by
    constructor <;> intro e <;> have := (hP.sA j hj).2.2.2.1 (by simp [e]) <;> rw [hown] at this <;>
      cases this <;> exact hne rfl
  have hfr : ∀ h, fresh S (upd ls i { ls i with st := .H2, ld := none }) h → fresh S ls h := by
    intro h hf'
    unfold fresh at hf' ⊢
    by_cases eh : h = i
    · subst eh; rw [ei] at hf'; rcases hf' with ⟨e, _⟩ | ⟨_, _, e | e⟩ <;> first | omega | cases e
    · rw [e0 h eh, e0 0 (by omega)] at hf'; exact hf'
  refine ⟨stS S M o' i ts, hw', .inl ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t a' ht hh ha => ?_,
    ⟨by simp only [stS]; rcases hnn with ⟨e, h2, _⟩ | ⟨e, h2⟩ <;> omega,
     by simp only [stS]; have := hP.tsle.2; rcases hnn with ⟨e, _⟩ | ⟨e, _⟩ <;> omega⟩,
    .inr ⟨_, hm, hc3⟩, fun t m' h1 h2 h3 h4 => ?_, fun e => absurd e hnd,
    fun e => absurd (show S.ls = .free from e) (by rw [hown]; simp),
    hP.hpo, fun _ => ⟨by show isC3 M ts = true; rw [isC3, clsB_of hm]; exact decide_eq_true hc3,
      .inr (by show tidAt M ts ≠ some 0; rw [tidAt, hm]; simpa using hi0)⟩,
    ?_, fun h u e => absurd (show S.ls = .pulled h u from e) (by rw [hown]; simp), fun h u ho => ?_, fun j hj hj1 => ?_,
    fun e => ?_, fun h u hu => ?_, fun h ts' t0 a1 a2 a3 a4 a5 a6 => hP.tk1 h ts' t0 a1 (hfr h a2) a3 (hpr h ts' a4) a5
      ⟨a6.1, a6.2⟩, fun h t0 a1 a2 a3 a4 a5 => ?_, fun t m' h1 h2 h3 h4 => ?_, hP.pubk,
    fun j k hj hk => ?_, ?_, fun j hj => ?_⟩, ?_⟩⟩
  · rw [e0 0 (by omega)]
    exact ⟨(hpe t).2 ⟨(hP.dr t ht).1, fun e => hnDr (e ▸ ht)⟩, (hP.dr t ht).2⟩
  · rcases ht with ht | ⟨_, _, c1, _, c2⟩
    · exact ⟨(hpe t).2 ⟨(hP.dc t ht).1, fun e => hnDc (e ▸ ht)⟩, (hP.dc t ht).2⟩
    · exact ⟨c1, c2⟩
  · have ha' : a' = i := by have hh' : S.hold = some a' := hh; rw [hhold] at hh'; cases hh'; rfl
    subst ha'
    rw [ei]
    rcases ht with ht | ⟨_, c1, _, _, _⟩
    · rcases hP.dcH t _ ht hh ha with e | ⟨tvs', e1, e2⟩ | ⟨_, e1, e2⟩
      · exact .inl e
      · rw [hld] at e1; cases e1; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 e2
        exact .inr (.inr ⟨hi0, by simp only [stS]; omega, by simp only [stS]; exact hlt p hp⟩)
      · exact .inr (.inr ⟨hi0, by simp only [stS]; omega, by simp only [stS]; omega⟩)
    · exact .inr (.inr ⟨hi0, by simp only [stS]; omega, c1⟩)
  · have h1' : ts < t := h1
    have htn : t ≤ σ.o.n := by
      by_cases e : t ≤ σ.o.n; exact e
      exact absurd (hnew t m' h2 e h3).1 (by omega)
    rcases hP.later t m' (by omega) htn h3 h4 with c | c | ⟨b, b1, b2, b3, b4, b5⟩
    · exact .inl c
    · exact .inr (.inl (.inl c))
    · exact .inr (.inr ⟨b, b1, b2, b3, (hpe t).2 ⟨b4, by omega⟩, b5⟩)
  · rw [e0 0 (by omega)]
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
      exact absurd ((hP.s0.2.2.1).1 (by simp [isD, e])) hnd
  · rcases hP.hown h u ho with ⟨rfl, b⟩ | ⟨hh, b1, b2⟩
    · rw [e0 0 (by omega)]; exact .inl ⟨rfl, b⟩
    · by_cases eh : h = i
      · subst eh; rw [ei]; exact .inr ⟨hh, .inr rfl, b2⟩
      · rw [e0 h eh]; exact .inr ⟨hh, b1, b2⟩
  · by_cases ej : j = i
    · subst ej; rw [ei] at hj1; cases hj1
    · rw [e0 j ej] at hj1; exact absurd hj1 (hoth j hj ej).1
  · rw [e0 0 (by omega)] at e
    have := hP.s0.2.2.2.2.2.1 e; rw [hown] at this; cases this; omega
  · obtain ⟨b1, b2, b3, b4, b5⟩ := hP.lk h u hu
    refine ⟨b1, b2, by show u ≤ o'.n; rcases hnn with ⟨e, _⟩ | ⟨e, _⟩ <;> omega, b4, fun t m' c1 c2 c3 c4 => ?_⟩
    by_cases e : t ≤ σ.o.n
    · exact b5 t m' c1 e c3 c4
    · obtain ⟨rfl, rfl⟩ := hnew t m' c2 e c3; exact absurd c4 (c3_ovL hc3)
  · rcases hnn with ⟨e, _⟩ | ⟨e, rfl⟩
    · exact hP.tk2 h t0 a1 (hfr h a2) ⟨a3.1, a3.2⟩ (by have : t0 ≤ o'.n := a4; omega) (by rw [← e]; exact a5)
    · by_cases hle : t0 ≤ σ.o.n
      · exact hP.tk2 h t0 a1 (hfr h a2) ⟨a3.1, a3.2⟩ hle (clean_le a5 (by show σ.o.n + 1 ≤ o'.n + 1; omega))
      · exfalso
        have : t0 = σ.o.n + 1 := by have : t0 ≤ o'.n := a4; omega
        subst this
        obtain ⟨m0, hm0, _, _, hb⟩ := memByte_ov (by omega) a3.2
        rw [hm] at hm0; cases hm0
        exact c3_ovL hc3 (ovL_b0 (by rw [hb]; rfl))
  · by_cases e : t ≤ σ.o.n
    · exact hP.fl t m' h1 e h3 h4
    · obtain ⟨rfl, rfl⟩ := hnew t m' h2 e h3; exact absurd h4 (c3_ovF hc3)
  · by_cases ej : j = i
    · subst ej; rw [ei]; exact hP.dnk j k hj hk
    · rw [e0 j ej]; exact hP.dnk j k hj hk
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
    rw [e0 0 (by omega)]
    refine ⟨b1, b2, b3, b4, b5, b6, fun d => ?_, fun d => ?_, b9⟩
    · by_cases e : (1 : Nat) = i
      · subst e; rw [ei]; exact b7 d
      · rw [e0 1 e]; exact b7 d
    · by_cases e : (2 : Nat) = i
      · subst e; rw [ei]; exact b8 d
      · rw [e0 2 e]; exact b8 d
  · by_cases ej : j = i
    · subst ej; rw [ei]
      obtain ⟨b1, b2, b3, b4, _⟩ := hP.sA j hj
      refine ⟨.inl ?_, .inr (.inr (.inr (.inl rfl))), fun _ => b3 (by rw [hH]; simp), fun _ => hown,
        fun e => absurd rfl e⟩
      rcases b1 with e | ⟨_, e, _⟩
      · exact e
      · rw [hH] at e; cases e
    · rw [e0 j ej]; exact hP.sA j hj
  · -- the trace: the pair is mutually exclusive
    have hcl : clr (stS S M o' i ts) → clr S := fun c t => ⟨(c t).1, fun d => (c t).2 (.inl d)⟩
    obtain ⟨⟨ev, a0, hev⟩, hall⟩ := hT.tld i tvs hi hld
    refine ⟨by simp only [nxT, upd_ne _ _ (Ne.symm hi0)]; exact hT.t0, fun cl => ?_, fun j tvs' hj hl => ?_⟩
    · have hq := hT.tq (hcl cl)
      have hpair : pairOk M tvs ts := by
        refine ⟨S.tstar, hall (hcl cl), ?_⟩
        refine ⟨(hP.gdp hnd).1, hgt, fun u hu1 hu2 => ?_⟩
        cases hu : isC3 M u with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨m', hm', hc'⟩ := clsB_iff.1 hu
          rcases hP.later u m' hu1 (hnle u hu2) hm' (c3_ovC hc') with d | d | ⟨b, b1, b2, _, b4, _⟩
          · exact (hcl cl u).1 d
          · exact (hcl cl u).2 d
          · apply (cl u).2; right
            have hb : b = i := by rw [hhold] at b1; cases b1; rfl
            subst hb
            exact ⟨hu1, hu2, (hpe u).2 ⟨b4, by omega⟩, by rw [au_msg (by omega) hm', b2], m', hm', hc'⟩
      have hst : ∀ x, x = (nxT σ i o' (LStore false false Ct (toBytes v 8) a c, some ts)).tr i →
          q7 M x := by
        intro x hx; rw [hx]; simp only [nxT, upd_eq]; rw [hev]
        rcases hi with rfl | rfl
        · rw [hev] at hq; exact q7_pair hq.1 hpair
        · rw [hev] at hq; exact q7_pair hq.2 hpair
      rcases hi with rfl | rfl
      · exact ⟨hst _ rfl, by simp only [nxT, upd_ne _ _ (show (2 : Nat) ≠ 1 by decide)]; exact hq.2⟩
      · exact ⟨by simp only [nxT, upd_ne _ _ (show (1 : Nat) ≠ 2 by decide)]; exact hq.1, hst _ rfl⟩
    · by_cases ej : j = i
      · subst ej; rw [ei] at hl; cases hl
      · rw [e0 j ej] at hl
        exact absurd ((hP.sA j hj).2.2.2.2 (by rw [hl]; simp)) (hoth j hj ej).1

end cs

end Weak.Prom.OB.E4
