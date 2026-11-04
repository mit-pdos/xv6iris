/-
Weak/Prom: **S3d — the cut execution conforms to preserved program order** (plan rev 7 §6 S3d).
`ppoAx_XC`: every rule 1–13 edge of the cut execution `XC` (Ref.lean `ppoB`, computed over the cut, with the
re-sourced late loads) is an edge of `E`'s gmo, so `gC` (gmo restricted to the cut) conforms to it.
* Rule 1 and the static rules 4–11, 13: every event of the cut keeps its skeleton and its address (PfxVal.lean
  `XC_sk`, `XC_pa`), and the events between two events of the cut are in the cut, so they are `E`'s own edges.
* Rule 2 (`rule2_XC`) and rule 12 (`rule12_XC`): the cut's load value axiom picks the gmo-latest candidate OF THE
  CUT; if gmo ordered the two events the other way, the candidate sets and `E`'s own load value axiom (and `E`'s
  rule 2 / rule 12) give a contradiction.  (rvwmo.adoc:279–281, :298–300.)
* Rule 3, pairing (rule 8), the atomicity axiom and the §zalrsc conditions are vacuous: the S3a scope has no AMO,
  LR or SC.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.PfxVal

noncomputable section

namespace Weak.Prom.Pfx

open Classical
open Weak.Prom.Ref
open Weak.Prom.Cmp (writesB_store)
open Cut

section lemmas

variable {E : IExec} {O : List EvId} (H : Hyp E O)
include H

theorem kind_frag {e : EvId} (he : E.has e) :
    (E.sk e).kind = .ld ∨ (E.sk e).kind = .st ∨ ∃ f, (E.sk e).kind = .fence f := by
  obtain ⟨h, i⟩ := e
  rcases fragEv H.conf H.frag he.1 he with hk | hk | ⟨f, hk, _⟩
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr ⟨f, hk⟩)

theorem poX_XC {a b : EvId} (ha : inD E O a) (hb : inD E O b) : poX (XC E O) a b = poS E.sk a b :=
  poS_congr (XC_sk H ha) (XC_sk H hb)

theorem inD_of_po {w b : EvId} (hb : inD E O b) (hw : E.has w) (hp : poS E.sk w b = true) : inD E O w := by
  obtain ⟨b1, b2⟩ := b
  obtain ⟨w1, w2⟩ := w
  have hsame : w1 = b1 := by simp [poS] at hp; exact hp.1
  subst hsame
  exact inD_of_le H hb (Nat.le_of_lt (po_idx H.conf H.frag hb.1 hw (inD_has H hb) hp))

theorem po_trans' {a b c : EvId} (h1 : poS E.sk a b = true) (h2 : poS E.sk b c = true) : poS E.sk a c = true := by
  simp only [poS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2 ⊢
  exact ⟨h1.1.trans h2.1, Nat.lt_trans h1.2 h2.2⟩

theorem po_irrefl' (a : EvId) : poS E.sk a a = false := by simp [poS]

theorem store_ne_load {w r : EvId} (hw : E.has w) (hws : (E.sk w).kind.isStore = true)
    (hrl : (E.sk r).kind.isLoad = true) : w ≠ r := by
  intro he; subst he
  rw [not_ld_st H hw hrl] at hws; cases hws

theorem rfI_exists {r : EvId} (hr : E.has r) (hl : (E.sk r).kind.isLoad = true) {x : Nat}
    (ht : touches (E.ev r) x = true) : ∃ o, E.rfI r x o := by
  simp only [touches, decide_eq_true_eq] at ht
  obtain ⟨o, ho, _⟩ := H.ref.2.2.2.1 r hr hl (isIoI_f H r) (x - (E.ev r).pa) (by
    have : (E.ev r).sk.sz = (E.sk r).sz := rfl
    omega)
  refine ⟨o, ?_⟩
  rw [show (E.ev r).pa + (x - (E.ev r).pa) = x by omega] at ho
  exact ho

/-- "`a` is `b` or gmo-before it". -/
def leG (E : IExec) (a b : EvId) : Prop := a = b ∨ E.gmo a b

theorem leG_trans {a b c : EvId} (h1 : leG E a b) (h2 : leG E b c) : leG E a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (IExec.gmo_trans (H_gmo H) h1 h2)

theorem not_gmo_of_leG {a b : EvId} (h1 : leG E a b) (h2 : E.gmo b a) : False := by
  rcases h1 with rfl | h1
  · exact IExec.gmo_irrefl (H_gmo H) _ h2
  · exact IExec.gmo_asymm (H_gmo H) h1 h2

/-- **Rule 2 of the cut is an edge of `E`'s gmo.** -/
theorem rule2_XC {a b : EvId} (ha : inD E O a) (hb : inD E O b) (hpo : poS E.sk a b = true)
    (h2 : rule2 (XC E O) a b = true) : E.gmo a b := by
  unfold rule2 at h2
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨hla, hlb⟩, -⟩, -⟩, hany⟩ := h2
  rw [XC_sk H ha] at hla hany
  rw [XC_sk H hb] at hlb
  obtain ⟨k, hkm, hk3⟩ := List.any_eq_true.1 hany
  rw [Bool.and_eq_true, Bool.and_eq_true] at hk3
  obtain ⟨⟨htb, hall⟩, hne⟩ := hk3
  have hk : k < (E.sk a).sz := List.mem_range.1 hkm
  rw [XC_pa H ha, XC_touches H hb] at htb
  rw [XC_pa H ha] at hall hne
  rw [rfSrc_XC H a ha, rfSrc_XC H b hb] at hne
  have hne' : rfSrc (Y E O) a ((E.ev a).pa + k) ≠ rfSrc (Y E O) b ((E.ev a).pa + k) := by
    simpa using hne
  generalize hx : (E.ev a).pa + k = x at htb hall hne'
  have hah := inD_has H ha
  have hbh := inD_has H hb
  have ham : E.isMem a := ⟨hah, Kind.isMem_of_isLoad _ hla⟩
  have hbm : E.isMem b := ⟨hbh, Kind.isMem_of_isLoad _ hlb⟩
  have haD : a ∈ Dm E O := (mem_Dm H a).2 ⟨ha, ham.2⟩
  have hbD : b ∈ Dm E O := (mem_Dm H b).2 ⟨hb, hbm.2⟩
  -- no store to x between a and b (in E)
  have hnone : ∀ m, E.has m → poS E.sk a m = true → poS E.sk m b = true → writesB (E.ev m) x = false := by
    intro m hm h1 h2
    have hmi := inD_of_po H hb hm h2
    have := List.all_eq_true.1 hall m ((XC_ids H m).2 hmi)
    rw [poX_XC H ha hmi, poX_XC H hmi hb, XC_writes H hmi, h1, h2] at this
    simpa using this
  apply Classical.byContradiction
  intro hng
  have hab : a ≠ b := by intro he; subst he; rw [po_irrefl' H] at hpo; cases hpo
  have hba : E.gmo b a := by
    rcases IExec.gmo_total (H_gmo H) ham hbm hab with h | h
    · exact absurd h hng
    · exact h
  obtain ⟨oa, hoa⟩ := rfI_exists H hah hla (x := x) (by
    rw [← hx]; simp only [touches, decide_eq_true_eq]; exact ⟨by omega, by have : (E.ev a).sk.sz = (E.sk a).sz := rfl; omega⟩)
  obtain ⟨ob, hob⟩ := rfI_exists H hbh hlb htb
  by_cases hoo : oa = ob
  · subst hoo
    -- every cut candidate of b is one of a
    have hcand : ∀ w, E.candI b x w → E.candI a x w := by
      intro w hw
      refine ⟨hw.1, hw.2.1, ?_⟩
      rcases hw.2.2 with hg | hp
      · exact Or.inl (IExec.gmo_trans (H_gmo H) hg hba)
      · right
        have hws : (E.sk w).kind.isStore = true := writesB_store hw.2.1
        have hwm : (E.sk w).kind.isMem = true := Kind.isMem_of_isStore _ hws
        obtain ⟨a1, a2⟩ := a
        obtain ⟨b1, b2⟩ := b
        obtain ⟨w1, w2⟩ := w
        have hwb : w1 = b1 := by simp [poS] at hp; exact hp.1
        have hab' : a1 = b1 := by simp [poS] at hpo; exact hpo.1
        subst hwb; subst hab'
        rcases Nat.lt_trichotomy w2 a2 with h1 | h1 | h1
        · exact idx_po H.conf H.frag hb.1 hah h1 hwm
        · subst h1; exact absurd rfl (store_ne_load H hw.1 hws hla)
        · have := hnone _ hw.1 (idx_po H.conf H.frag hb.1 hw.1 h1 ham.2) hp
          rw [hw.2.1] at this; cases this
    apply hne'
    cases hsb : rfSrc (Y E O) b x with
    | none =>
      cases hsa : rfSrc (Y E O) a x with
      | none => rfl
      | some sa =>
        exfalso
        obtain ⟨saD, sac, _⟩ := rfSrcY_some H haD hsa
        have sai := ((mem_Dm H sa).1 saD).1
        have hnb := rfSrcY_none H hbD hsb
        rcases sac.2.2 with hg | hp
        · have hng' : ¬ E.gmo sa b := fun h => hnb sa sai ⟨sac.1, sac.2.1, Or.inl h⟩
          have hbs : E.gmo b sa := by
            rcases IExec.gmo_total (H_gmo H) ⟨sac.1, Kind.isMem_of_isStore _ (writesB_store sac.2.1)⟩ hbm
              (store_ne_load H sac.1 (writesB_store sac.2.1) hlb) with h | h
            · exact absurd h hng'
            · exact h
          cases oa with
          | none => exact hoa sa sac
          | some w =>
            have h1 : leG E sa w := hoa.2 sa sac
            rcases hob.1.2.2 with hg' | hp'
            · exact not_gmo_of_leG H (leG_trans H h1 (Or.inr hg')) hbs
            · exact hnb w (inD_of_po H hb hob.1.1 hp') hob.1
        · exact hnb sa sai ⟨sac.1, sac.2.1, Or.inr (po_trans' H hp hpo)⟩
    | some sb =>
      obtain ⟨sbD, sbc, sbmax⟩ := rfSrcY_some H hbD hsb
      have sbi := ((mem_Dm H sb).1 sbD).1
      cases hsa : rfSrc (Y E O) a x with
      | none => exact absurd (hcand sb sbc) (rfSrcY_none H haD hsa sb sbi)
      | some sa =>
        obtain ⟨saD, sac, samax⟩ := rfSrcY_some H haD hsa
        have sai := ((mem_Dm H sa).1 saD).1
        rcases samax sb sbi (hcand sb sbc) with h1 | h1
        · rw [h1]
        · exfalso
          -- sb gmo-before sa
          rcases sac.2.2 with hg | hp
          · by_cases hsab : E.gmo sa b
            · rcases sbmax sa sai ⟨sac.1, sac.2.1, Or.inl hsab⟩ with h2 | h2
              · rw [h2] at h1; exact IExec.gmo_irrefl (H_gmo H) _ h1
              · exact IExec.gmo_asymm (H_gmo H) h1 h2
            · have hbs : E.gmo b sa := by
                rcases IExec.gmo_total (H_gmo H) ⟨sac.1, Kind.isMem_of_isStore _ (writesB_store sac.2.1)⟩ hbm
                  (store_ne_load H sac.1 (writesB_store sac.2.1) hlb) with h | h
                · exact absurd h hsab
                · exact h
              cases oa with
              | none => exact hoa sa sac
              | some w =>
                have h3 : leG E sa w := hoa.2 sa sac
                rcases hob.1.2.2 with hg' | hp'
                · exact not_gmo_of_leG H (leG_trans H h3 (Or.inr hg')) hbs
                · have h4 : leG E w sb := sbmax w (inD_of_po H hb hob.1.1 hp') hob.1
                  exact not_gmo_of_leG H (leG_trans H h3 h4) h1
          · rcases sbmax sa sai ⟨sac.1, sac.2.1, Or.inr (po_trans' H hp hpo)⟩ with h2 | h2
            · rw [h2] at h1; exact IExec.gmo_irrefl (H_gmo H) _ h1
            · exact IExec.gmo_asymm (H_gmo H) h1 h2
  · apply hng
    apply H_ppo H
    refine ⟨ham, hbm, hpo, Or.inr (Or.inl ⟨hla, hlb, isIoI_f H a, isIoI_f H b, k, hk, ?_, ?_, oa, ob, ?_, ?_, hoo⟩)⟩
    · rw [hx]; exact htb
    · intro m hm h1 h2; rw [hx]; exact hnone m hm h1 h2
    · rw [hx]; exact hoa
    · rw [hx]; exact hob

/-- **Rule 12 of the cut is an edge of `E`'s gmo.** -/
theorem rule12_XC {a b : EvId} (ha : inD E O a) (hb : inD E O b) (ham : E.isMem a) (hpo : poS E.sk a b = true)
    (h12 : rule12 (XC E O) a b = true) : E.gmo a b := by
  unfold rule12 at h12
  rw [Bool.and_eq_true, Bool.and_eq_true] at h12
  obtain ⟨⟨hlb, -⟩, hany⟩ := h12
  rw [XC_sk H hb] at hlb
  obtain ⟨m, hmi, hm⟩ := List.any_eq_true.1 hany
  have hmD := (XC_ids H m).1 hmi
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hm
  rw [poX_XC H ha hmD] at h1
  rw [poX_XC H hmD hb] at h2
  rw [XC_sk H hmD] at h3 h4
  rw [XC_sk H hb] at h5
  obtain ⟨k, hkm, hk⟩ := List.any_eq_true.1 h5
  have hk' : k < (E.sk b).sz := List.mem_range.1 hkm
  rw [XC_pa H hb, rfSrc_XC H b hb] at hk
  have hs : rfSrc (Y E O) b ((E.ev b).pa + k) = some m := by simpa using hk
  have hbh := inD_has H hb
  have hbm : E.isMem b := ⟨hbh, Kind.isMem_of_isLoad _ hlb⟩
  have hbD : b ∈ Dm E O := (mem_Dm H b).2 ⟨hb, hbm.2⟩
  have hmh := inD_has H hmD
  have hmm : E.isMem m := ⟨hmh, Kind.isMem_of_isStore _ h3⟩
  obtain ⟨_, mc, mmax⟩ := rfSrcY_some H hbD hs
  -- a is ppo-before m (rule 9 or 10)
  have ham' : E.gmo a m := by
    apply H_ppo H
    refine ⟨ham, hmm, h1, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
    have hsame : a.1 = m.1 := by simp [poS] at h1; exact h1.1
    rcases Bool.or_eq_true _ _ ▸ h4 with h4 | h4
    · right; right; right; right; right; left
      simp only [rule9, hsame, beq_self_eq_true, Bool.true_and]; exact h4
    · right; right; right; right; right; right; left
      simp only [rule10, h3, hsame, beq_self_eq_true, Bool.true_and, Bool.and_true]; exact h4
  by_cases hmb : E.gmo m b
  · exact IExec.gmo_trans (H_gmo H) ham' hmb
  have hbm' : E.gmo b m := by
    rcases IExec.gmo_total (H_gmo H) hmm hbm (store_ne_load H hmh h3 hlb) with h | h
    · exact absurd h hmb
    · exact h
  obtain ⟨o, ho, _⟩ := H.ref.2.2.2.1 b hbh hlb (isIoI_f H b) k hk'
  have hsrc : E.rfI b ((E.ev b).pa + k) (some m) := by
    cases o with
    | none => exact absurd mc (ho m)
    | some w =>
      have h6 : leG E m w := ho.2 m mc
      rcases ho.1.2.2 with hg | hp
      · exfalso; exact not_gmo_of_leG H (leG_trans H h6 (Or.inr hg)) hbm'
      · have h7 : leG E w m := mmax w (inD_of_po H hb ho.1.1 hp) ho.1
        rcases h7 with h7 | h7
        · rw [← h7]; exact ho
        · exfalso; exact not_gmo_of_leG H h6 h7
  apply H_ppo H
  refine ⟨ham, hbm, hpo, Or.inr (Or.inr (Or.inr (Or.inr ⟨hlb, isIoI_f H b, m, hmh, h1, h2, h3, ?_, k, hk', hsrc⟩)))⟩
  rcases Bool.or_eq_true _ _ ▸ h4 with h4 | h4
  · exact Or.inl h4
  · exact Or.inr h4

/-- The static rules of the cut are `E`'s. -/
theorem static_XC {a b : EvId} (ha : inD E O a) (hb : inD E O b)
    (hs : staticRules (XC E O).ids (XC E O).sk (isIo (XC E O)) a b = true) : E.staticI a b := by
  have hio : isIo (XC E O) = E.isIoI := by
    funext e; rw [isIoI_f H e]; exact isIo_nil _ H.io e
  rw [hio] at hs
  have hka := XC_sk H ha
  have hkb := XC_sk H hb
  unfold staticRules at hs
  simp only [Bool.or_eq_true] at hs
  rcases hs with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · -- rule 4
    left
    obtain ⟨m, hmi, hm⟩ := List.any_eq_true.1 h
    have hmD := (XC_ids H m).1 hmi
    rw [XC_sk H hmD] at hm
    split at hm
    · rename_i f hf
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hm
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hm
      rw [poS_congr hka (XC_sk H hmD)] at h1
      rw [poS_congr (XC_sk H hmD) hkb] at h2
      refine ⟨m, f, inD_has H hmD, hf, h1, h2, ?_, ?_⟩
      · unfold inPred at h3 ⊢; rw [hka] at h3; exact h3
      · unfold inSucc at h4 ⊢; rw [hkb] at h4; exact h4
    · cases hm
  · right; left; unfold rule5 at h ⊢; rw [hka] at h; exact h
  · right; right; left; unfold rule6 at h ⊢; rw [hkb] at h; exact h
  · right; right; right; left; unfold rule7 at h ⊢; rw [hka, hkb] at h; exact h
  · exfalso
    unfold rule8 pairedS at h
    rw [hka] at h
    rcases kind_frag H (inD_has H ha) with hk | hk | ⟨f, hk⟩ <;> simp [hk] at h
  · right; right; right; right; right; left; unfold rule9 at h ⊢; rw [hkb] at h; exact h
  · right; right; right; right; right; right; left; unfold rule10 at h ⊢; rw [hkb] at h; exact h
  · right; right; right; right; right; right; right; left; unfold rule11 at h ⊢; rw [hkb] at h; exact h
  · right; right; right; right; right; right; right; right
    unfold rule13 at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨m, hmi, hm⟩ := List.any_eq_true.1 h2
    have hmD := (XC_ids H m).1 hmi
    rw [XC_sk H hmD, poS_congr hka (XC_sk H hmD), poS_congr (XC_sk H hmD) hkb] at hm
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hm
    obtain ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩ := hm
    rw [hkb] at h1
    exact ⟨h1, m, inD_has H hmD, m1, m2, m3, m4⟩

/-- **THE CUT EXECUTION CONFORMS TO PRESERVED PROGRAM ORDER.** -/
theorem ppoAx_XC : ppoAx (XC E O) := by
  intro a ha b hb hord
  have hai := (XC_ids H a).1 ha
  have hbi := (XC_ids H b).1 hb
  have hio : ioOrdB (XC E O) a b = false := by
    unfold ioOrdB regionOf
    have : (XC E O).io = [] := H.io
    simp [this]
  unfold orderedB at hord
  rw [hio, Bool.or_false] at hord
  unfold ppoB at hord
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hord
  obtain ⟨⟨⟨hma, hmb⟩, hpo⟩, hr⟩ := hord
  rw [XC_sk H hai] at hma
  rw [XC_sk H hbi] at hmb
  rw [poX_XC H hai hbi] at hpo
  have ham : E.isMem a := ⟨inD_has H hai, hma⟩
  have hbm : E.isMem b := ⟨inD_has H hbi, hmb⟩
  have haD : a ∈ Dm E O := (mem_Dm H a).2 ⟨hai, hma⟩
  have hbD : b ∈ Dm E O := (mem_Dm H b).2 ⟨hbi, hmb⟩
  show gB (gC E O) a b = true
  rw [gB_C H haD hbD]
  simp only [Bool.or_eq_true] at hr
  rcases hr with (((h | h) | h) | h) | h
  · apply H_ppo H
    refine ⟨ham, hbm, hpo, Or.inl ⟨?_, ?_⟩⟩
    · unfold rule1 at h; rw [Bool.and_eq_true, XC_sk H hbi] at h; exact h.1
    · unfold rule1 at h; rw [Bool.and_eq_true] at h
      have := h.2
      unfold overlapB at this ⊢
      have hka : ((XC E O).ev a).sk = (E.ev a).sk := XC_sk H hai
      have hkb : ((XC E O).ev b).sk = (E.ev b).sk := XC_sk H hbi
      rw [XC_pa H hai, XC_pa H hbi, hka, hkb] at this
      exact this
  · exact rule2_XC H hai hbi hpo h
  · exfalso
    unfold rule3 at h
    rw [XC_sk H hai] at h
    rcases kind_frag H ham.1 with hk | hk | ⟨f, hk⟩ <;> simp [hk, Kind.isRmwW] at h
  · exact H_ppo H ⟨ham, hbm, hpo, Or.inr (Or.inr (Or.inr (Or.inl (static_XC H hai hbi h))))⟩
  · exact rule12_XC H hai hbi ham hpo h

end lemmas

end Weak.Prom.Pfx

end
