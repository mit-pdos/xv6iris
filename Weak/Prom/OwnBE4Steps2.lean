/-
Weak/Prom: **E-b4 — the protocol's step lemmas, part 2: the flag reads** (stage E-b4).

* `inv_pubRd` — an acquirer waiting for round `k` reads the publication byte as `k`: the source is hart 0's
  in-place publication of round `k` = the current lifetime (or a robust dead message: spoiled); the hart moves to
  its acquiring stage, recording the publication's timestamp.
* `inv_dnRd` — hart 0 reads acquirer `j`'s done byte as its round: that acquirer has left the round (`dnk`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Steps

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
open Weak.Prom.OA.E4 (q7 img7 q7_snoc img7_eq)
open PLabel

theorem flag_byte {k : Nat} {v : BitVec 8} {o : Nat} {m : PMsg} (hm : m.pa = L1 + o) (hd : m.data = toBytes k 1)
    (hb : m.byteAt (L1 + o) = some v) : v.toNat = k % 256 := by
  rw [← hm, show m.pa = m.pa + ((0 : Nat) : Int) by simp, Weak.Prom.OA.byteAt_off rfl, hd] at hb
  simp [toBytes, Weak.Prom.Ref.byteList, bv8] at hb
  rw [← hb]; simp [BitVec.toNat_ofNat]

theorem flag_far {k j o : Nat} {v : BitVec 8} {m : PMsg} (hm : m.pa = L1 + j) (hd : m.data = toBytes k 1)
    (hne : o ≠ j) (hb : m.byteAt (L1 + o) = some v) : False := by
  rw [Weak.Prom.OA.E.byteAt_none (by rw [hm, hd, toBytes_len]; omega)] at hb; cases hb

section rd

variable {M : List PMsg} {σ : TSt (List Nat)} {S : PS} {ls : Nat → Loc}

theorem lt_le3 (hP : GoodP M σ.o S ls) : S.lt ≤ 3 := hP.s0.2.1.2

/-- **THE PUBLICATION READ**. -/
theorem inv_pubRd {i t : Nat} {v : BitVec 8} {a : List Dsrc} (hI : Inv M σ S ls) (hi : i = 1 ∨ i = 2)
    (hW : (ls i).st = .W) (hb : memByte img7 (M.take σ.o.n) t L1 = some v) (hv : v.toNat = (ls i).k) :
    Inv M (nxT σ i σ.o (LLoad false false L1 [(t, v)] a, none)) S (upd ls i { ls i with st := .A, p := t }) := by
  obtain ⟨hw, hI⟩ := hI
  have hi0 : i ≠ 0 := by omega
  refine ⟨hw, ?_⟩
  obtain ⟨hb1, htn⟩ := memByte_pre hb
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · exact .inr ⟨t', by rw [upd0 hi0]; exact hr⟩
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := hP.sA i hi
  have hk1 : 1 ≤ (ls i).k := by have := hP.s0.2.1.1; omega
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp only [memByte] at hb1; rw [img7_eq] at hb1; cases hb1; simp at hv; omega
    · exact h
  obtain ⟨m, hm, hp1, hp2, hbm⟩ := memByte_ov ht1 hb1
  rcases hP.fl t m ht1 htn hm (ov_of (a := L1) (n := 4) (x := L1) (by omega) (by rw [hbm]; rfl)) with hd | ⟨k', hk', rfl⟩ | ⟨j, k', hj, _, rfl⟩
  · exact .inr ⟨t, by rw [upd0 hi0]; exact hP.dr t hd⟩
  rotate_left
  · exact (flag_far (j := j) (o := 0) rfl rfl (by omega) (by simpa using hbm)).elim
  have hvk := flag_byte (m := pubM k') (o := 0) (by simp [pubM]) rfl (by simpa using hbm)
  have hk'0 : S.pubT k' ≠ 0 := by omega
  obtain ⟨hkl, hkd⟩ := hP.pubk k' hk'0
  have hl3 := lt_le3 hP
  have hkk : k' = (ls i).k := by omega
  have hlt : (ls i).k = S.lt := by rcases hA1 with e | ⟨e, _⟩ <;> omega
  have hnd : S.ls ≠ .dead := hkd (by omega)
  have hpt : S.pubT S.lt = t := by rw [← hlt, ← hkk]; exact hk'
  have hld : (ls i).ld = none := by
    cases e : (ls i).ld with
    | none => rfl
    | some _ => have := hA5 (by rw [e]; simp); rw [hW] at this; cases this
  -- the relabelled records
  have e0 : ∀ j, j ≠ i → upd ls i { ls i with st := .A, p := t } j = ls j := fun j hj => upd_ne _ _ hj
  have ei : upd ls i { ls i with st := .A, p := t } i = { ls i with st := .A, p := t } := upd_eq _ _ _
  have hfr : ∀ h, fresh S (upd ls i { ls i with st := .A, p := t }) h ↔ fresh S ls h := by
    intro h
    by_cases eh : h = i
    · subst eh
      unfold fresh; rw [ei]; simp only
      constructor
      · rintro (⟨e, _⟩ | ⟨a1, a2, _⟩); omega; exact .inr ⟨a1, a2, .inl hW⟩
      · rintro (⟨e, _⟩ | ⟨a1, a2, _⟩); omega; exact .inr ⟨a1, a2, by simp⟩
    · unfold fresh; rw [e0 h eh, e0 0 (by omega)]
  refine .inl ⟨⟨fun t ht => by rw [e0 0 (by omega)]; exact hP.dr t ht, hP.dc, fun t a ht hh ha => ?_, hP.tsle,
    hP.tsok, hP.later, fun e => by rw [e0 0 (by omega)]; exact hP.hdead e, hP.hfree, hP.hpo, hP.gdp,
    by rw [e0 0 (by omega)]; exact hP.h0f, hP.hpre, fun h u ho => ?_, fun j hj hj1 => ?_,
    by rw [e0 0 (by omega)]; exact hP.h0o, hP.lk,
    fun h ts t0 a1 a2 => hP.tk1 h ts t0 a1 ((hfr h).1 a2), fun h t0 a1 a2 => hP.tk2 h t0 a1 ((hfr h).1 a2), hP.fl,
    hP.pubk, fun j k hj hk => ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · by_cases ea : a = i
    · subst ea; rw [ei]; exact hP.dcH t _ ht hh ha
    · rw [e0 a ea]; exact hP.dcH t a ht hh ha
  · rcases hP.hown h u ho with ⟨rfl, b⟩ | ⟨hh, b1, b2⟩
    · rw [e0 0 (by omega)]; exact .inl ⟨rfl, b⟩
    · have : h ≠ i := fun e => by subst e; rw [hW] at b1; rcases b1 with b1 | b1 <;> cases b1
      rw [e0 h this]; exact .inr ⟨hh, b1, b2⟩
  · by_cases ej : j = i
    · subst ej; rw [ei] at hj1; simp at hj1
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
      refine ⟨.inl hlt, .inr (.inl rfl), fun _ => ⟨hlt, hnd, hpt⟩, fun e => (by rcases e with e | e <;> cases e),
        fun e => (by simp only at e; rw [hld] at e; exact absurd rfl e)⟩
    · rw [e0 j ej]; exact hP.sA j hj
  · exact gT_snoc (h := i) hT (fun tvs ⟨_, e⟩ => by
        simp only [Prod.mk.injEq, LLoad.injEq] at e; simp [L1, Ct, Weak.Prom.Ref.Lit.Z, Weak.Prom.Ref.Lit.Y] at e)
      (.inr fun ts ⟨_, _, _, e⟩ => by cases e) (by simpa using hld) (fun _ h => h) (fun _ h => h)
      (fun _ _ _ _ _ => rfl)

/-- hart 0's record with a done flag set. -/
def setD (l : Loc) (j : Nat) : Loc := if j = 1 then { l with d1 := true } else { l with d2 := true }

theorem setD_st (l : Loc) (j : Nat) : (setD l j).st = l.st ∧ (setD l j).u = l.u ∧ (setD l j).cf = l.cf ∧
    (setD l j).f = l.f ∧ (setD l j).p = l.p ∧ (setD l j).k = l.k ∧ (setD l j).ld = l.ld := by
  unfold setD; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **THE DONE-BYTE READ** (hart 0, publication stage): acquirer `j` has left the round. -/
theorem inv_dnRd {j t : Nat} {v : BitVec 8} {a : List Dsrc} (hI : Inv M σ S ls) (hj : j = 1 ∨ j = 2)
    (hP0 : (ls 0).st = .P) (hb : memByte img7 (M.take σ.o.n) t (L1 + j) = some v) (hv : v.toNat = (ls 0).k) :
    Inv M (nxT σ 0 σ.o (LLoad false false (L1 + j) [(t, v)] a, none)) S (upd ls 0 (setD (ls 0) j)) := by
  obtain ⟨hw, hI⟩ := hI
  refine ⟨hw, ?_⟩
  obtain ⟨hb1, htn⟩ := memByte_pre hb
  obtain ⟨s1, s2, s3, s4, s5, s6, s9⟩ := setD_st (ls 0) j
  have ei : upd ls 0 (setD (ls 0) j) 0 = setD (ls 0) j := upd_eq _ _ _
  have e0 : ∀ x, x ≠ 0 → upd ls 0 (setD (ls 0) j) x = ls x := fun x hx => upd_ne _ _ hx
  rcases hI with ⟨hP, hT⟩ | ⟨t', hr⟩
  rotate_left
  · exact .inr ⟨t', by rw [ei]; exact ⟨hr.1, hr.2.imp fun m h => ⟨h.1, by rw [s1, s3]; exact h.2⟩⟩⟩
  have hk1 : 1 ≤ (ls 0).k := by have := hP.s0.2.1.1; have := hP.s0.1; omega
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp only [memByte] at hb1; rw [img7_eq] at hb1; cases hb1; simp at hv; omega
    · exact h
  obtain ⟨m, hm, hp1, hp2, hbm⟩ := memByte_ov ht1 hb1
  have hrob : ∀ x, S.Dr x → Rob M σ.o (upd ls 0 (setD (ls 0) j) 0) x := fun x hx => by
    rw [ei]; exact ⟨(hP.dr x hx).1, (hP.dr x hx).2.imp fun m h => ⟨h.1, by rw [s1, s3]; exact h.2⟩⟩
  rcases hP.fl t m ht1 htn hm (ov_of (a := L1) (n := 4) (x := L1 + j) (by omega) (by rw [hbm]; rfl)) with
    hd | ⟨k', hk', rfl⟩ | ⟨j', k', hj', hk', rfl⟩
  · exact .inr ⟨t, hrob t hd⟩
  · exact (flag_far (j := 0) (o := j) (by simp [pubM]) rfl (by omega) hbm).elim
  have hjj : j' = j := by
    by_cases e : j = j'
    · exact e.symm
    · exact (flag_far (j := j') (o := j) rfl rfl e hbm).elim
  subst hjj
  have hvk := flag_byte (m := dnM j' k') (o := j') rfl rfl hbm
  have hdk := hP.dnk j' k' hj (by omega)
  have hl3 := lt_le3 hP
  have hkj : (ls j').k ≤ S.lt + 1 := by rcases (hP.sA j' hj).1 with e | ⟨e, _⟩ <;> omega
  have hkk : k' = (ls 0).k := by omega
  have hlt : S.lt < (ls j').k := by rw [← hP.s0.1, ← hkk]; exact hdk
  have hfr : ∀ h, fresh S (upd ls 0 (setD (ls 0) j')) h ↔ fresh S ls h := by
    intro h
    unfold fresh
    by_cases eh : h = 0
    · subst eh; rw [ei, s1, s6]
    · rw [e0 h eh, ei, s1]
  refine .inl ⟨⟨hrob, hP.dc, fun t a ht hh ha => ?_, hP.tsle, hP.tsok, hP.later, fun e => by rw [ei, s2]; exact hP.hdead e,
    hP.hfree, hP.hpo, hP.gdp, by rw [ei, s1, s4]; exact hP.h0f, hP.hpre, fun h u ho => ?_,
    fun x hx => by rw [e0 x (by omega)]; exact hP.h1 x hx, by rw [ei, s1]; exact hP.h0o, hP.lk,
    fun h ts t0 a1 a2 => hP.tk1 h ts t0 a1 ((hfr h).1 a2), fun h t0 a1 a2 => hP.tk2 h t0 a1 ((hfr h).1 a2), hP.fl,
    hP.pubk, fun x k hx => by rw [e0 x (by omega)]; exact hP.dnk x k hx, ?_,
    fun x hx => by rw [e0 x (by omega)]; exact hP.sA x hx⟩, ?_⟩
  · by_cases ea : a = 0
    · subst ea; rw [ei, s9]; exact hP.dcH t _ ht hh ha
    · rw [e0 a ea]; exact hP.dcH t a ht hh ha
  · rcases hP.hown h u ho with ⟨rfl, b⟩ | ⟨hh, b⟩
    · rw [ei, s1, s2]; exact .inl ⟨rfl, b⟩
    · rw [e0 h (by omega)]; exact .inr ⟨hh, b⟩
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hP.s0
    rw [ei, s1, s2, s5, s6, s9, e0 1 (by omega), e0 2 (by omega)]
    refine ⟨b1, b2, b3, b4, b5, b6, fun d => ?_, fun d => ?_, b9⟩
    · unfold setD at d; split at d
      · rename_i e; subst e; exact hlt
      · exact b7 d
    · unfold setD at d; split at d
      · exact b8 d
      · rename_i e; have : j' = 2 := by omega
        subst this; exact hlt
  · exact gT_snoc (h := 0) hT (fun tvs ⟨_, e⟩ => by
        simp only [Prod.mk.injEq, LLoad.injEq] at e; simp [L1, Ct, Weak.Prom.Ref.Lit.Z, Weak.Prom.Ref.Lit.Y] at e; omega)
      (.inl rfl) (by rw [s9]; exact hP.s0.2.2.2.2.2.2.2.2) (fun _ h => h) (fun _ h => h) (fun _ _ _ _ _ => rfl)

end rd

end Weak.Prom.OB.E4
