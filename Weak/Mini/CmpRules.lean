/-
Weak/Mini: **L4 MiniCmp — the ppo rules the simulation uses, and coherence of reads** (mini plan rev 4 §2 L4).

Each `gmo_rN` packages "rule N gives ppo, ppo gives gmo" (rvwmo.adoc:278–302, :307–310) for a finite execution
`C` of `P`.  `kts_corr`: two po-ordered loads of one word read stores in non-decreasing timestamp order (rules 1, 2
and the load value axiom: the CoRR shape).  The invariant transport lemmas for steps that move no view
(`inv_nomem`), and over one event (`fwdOk_mono`, `prom_mono`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.CmpInv

namespace Weak.Mini.Cmp

open Weak.Mini Weak.Mini.Mach

variable {P : MProg} {C : MCut}

/-! ## 1. Program order on one hart -/

theorem po_trans {a b c : EvId} (h1 : (C.evs P).po a b) (h2 : (C.evs P).po b c) : (C.evs P).po a c :=
  ⟨h1.1.trans h2.1, Nat.lt_trans h1.2 h2.2⟩

theorem po_idx {h j0 j : Nat} (hpo : (C.evs P).po (h, j0) (h, j)) (h0 : j0 < NN P C h) (hj : j < NN P C h) :
    j0 < j := by
  rcases Nat.lt_trichotomy j0 j with h1 | h1 | h1
  · exact h1
  · subst h1; exact absurd hpo.2 (Nat.lt_irrefl _)
  · exact absurd hpo.2 (Nat.lt_asymm (po_hj h1 h0).2)

/-! ## 2. Rules → gmo -/

section rules

variable (hC : miniCut P C)
include hC

theorem gmo_r1 {a b : EvId} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b) (hpo : (C.evs P).po a b)
    (hst : (C.evs P).isSt b) (hpa : ((C.evs P).ev a).pa = ((C.evs P).ev b).pa) : (C.evs P).gmo a b :=
  ppoG hC ha hb hpo (.inl ⟨hst, hpa⟩)

theorem gmo_r2 {a b : EvId} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b) (hpo : (C.evs P).po a b)
    (hr : (C.evs P).rule2 a b) : (C.evs P).gmo a b :=
  ppoG hC ha hb hpo (.inr (.inl hr))

theorem gmo_r4 {a b m : EvId} {f : MFence} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b)
    (hpo : (C.evs P).po a b) (hm : (C.evs P).has m) (hk : ((C.evs P).ev m).kind = .fence f)
    (h1 : (C.evs P).po a m) (h2 : (C.evs P).po m b) (hp : (C.evs P).inPred f a) (hs : (C.evs P).inSucc f b) :
    (C.evs P).gmo a b :=
  ppoG hC ha hb hpo (.inr (.inr (.inl ⟨m, f, hm, hk, h1, h2, hp, hs⟩)))

theorem gmo_r9 {a b : EvId} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b) (hpo : (C.evs P).po a b)
    (hd : a.2 ∈ ((C.evs P).ev b).adep) : (C.evs P).gmo a b :=
  ppoG hC ha hb hpo (.inr (.inr (.inr (.inl ⟨hpo.1, hd⟩))))

theorem gmo_r10 {a b : EvId} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b) (hpo : (C.evs P).po a b)
    (hst : (C.evs P).isSt b) (hd : a.2 ∈ ((C.evs P).ev b).ddep) : (C.evs P).gmo a b :=
  ppoG hC ha hb hpo (.inr (.inr (.inr (.inr (.inl ⟨hst, hpo.1, hd⟩)))))

theorem gmo_r11 {a b : EvId} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b) (hpo : (C.evs P).po a b)
    (hst : (C.evs P).isSt b) (hd : a.2 ∈ ((C.evs P).ev b).cdep) : (C.evs P).gmo a b :=
  ppoG hC ha hb hpo (.inr (.inr (.inr (.inr (.inr (.inl ⟨hst, hpo.1, hd⟩))))))

theorem gmo_r12 {a b m : EvId} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b) (hpo : (C.evs P).po a b)
    (hl : (C.evs P).isLd b) (hm : (C.evs P).has m) (h1 : (C.evs P).po a m) (h2 : (C.evs P).po m b)
    (hs : (C.evs P).isSt m) (hd : a.2 ∈ ((C.evs P).ev m).adep ∨ a.2 ∈ ((C.evs P).ev m).ddep)
    (hrf : (C.evs P).rf b (some m)) : (C.evs P).gmo a b :=
  ppoG hC ha hb hpo (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hl, m, hm, h1, h2, hs, hd, hrf⟩)))))))

theorem gmo_r13 {a b m : EvId} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b) (hpo : (C.evs P).po a b)
    (hst : (C.evs P).isSt b) (hm : (C.evs P).isMem m) (h1 : (C.evs P).po a m) (h2 : (C.evs P).po m b)
    (hd : a.2 ∈ ((C.evs P).ev m).adep) : (C.evs P).gmo a b :=
  ppoG hC ha hb hpo (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hst, m, hm, h1, h2, hd⟩)))))))

/-! ## 3. Coherence of reads -/

/-- **CoRR**: po-ordered loads of one word read in non-decreasing timestamp order. -/
theorem kts_corr {r r' : EvId} {o o' : Option EvId} (hr : (C.evs P).isMem r) (hr' : (C.evs P).isMem r')
    (hl : (C.evs P).isLd r) (hl' : (C.evs P).isLd r') (hpo : (C.evs P).po r r')
    (hpa : ((C.evs P).ev r).pa = ((C.evs P).ev r').pa) (ho : (C.evs P).rf r o) (ho' : (C.evs P).rf r' o') :
    kts P C o ≤ kts P C o' := by
  have hg := hgmo hC
  match o, ho with
  | none, _ => exact Nat.zero_le _
  | some w0, ho =>
    obtain ⟨hw0, hs0, hpa0, hord⟩ := ho.1
    have hc : ∀ (_ : (C.evs P).gmo w0 r' ∨ (C.evs P).po w0 r'), vo P C w0 ≤ kts P C o' :=
      fun hh => kts_ge hC ho' ⟨hw0, hs0, hpa0.trans hpa, hh⟩
    rcases hord with hg0 | hp0
    · by_cases hrr : (C.evs P).gmo r r'
      · exact hc (.inl (MEvsF.gmo_trans hg hg0 hrr))
      · have hrr' : (C.evs P).gmo r' r := by
          rcases MEvsF.gmo_total hg hr hr' (fun he => by subst he; exact Nat.lt_irrefl _ hpo.2) with h | h
          · exact absurd h hrr
          · exact h
        by_cases hm : ∃ m, (C.evs P).has m ∧ (C.evs P).po r m ∧ (C.evs P).po m r' ∧ (C.evs P).isSt m ∧
            ((C.evs P).ev m).pa = ((C.evs P).ev r).pa
        · obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ := hm
          have hmm : (C.evs P).isMem m := ⟨hm1, .inr hm4⟩
          have h1 := gmo_r1 hC hr hmm hm2 hm4 hm5.symm
          have h2 := vo_gmo_st hC (MEvsF.gmo_trans hg hg0 h1) hm4
          have h3 := kts_ge hC ho' ⟨hm1, hm4, hm5.trans hpa, .inr hm3⟩
          show vo P C w0 ≤ _; omega
        · by_cases heq : some w0 = o'
          · rw [← heq]; exact Nat.le_refl _
          · have := gmo_r2 hC hr hr' hpo ⟨hl, hl', hpa, fun m h1 h2 h3 h4 => hm ⟨m, h1, h2, h3, h4⟩,
              some w0, o', ho, ho', heq⟩
            exact absurd (MEvsF.gmo_asymm hg this hrr') id
    · exact hc (.inr (po_trans hp0 hpo))

/-- Two stores with the same timestamp are the same store. -/
theorem vo_inj {w w' : EvId} (hw : (C.evs P).isMem w) (hw' : (C.evs P).isMem w')
    (hs : ((C.evs P).ev w).kind = .st) (hs' : ((C.evs P).ev w').kind = .st) (he : vo P C w = vo P C w') :
    w = w' := by
  rcases st_of_vo hC hw' hw hs (Nat.le_of_eq he) with h | h
  · exact h
  · rcases st_of_vo hC hw hw' hs' (Nat.le_of_eq he.symm) with h' | h'
    · exact h'.symm
    · exact absurd (MEvsF.gmo_asymm (hgmo hC) h h') id

end rules

/-! ## 4. Invariant transport -/

theorem fwdOk_mono {h n a : Nat} {o : Option (Nat × Nat)} (hf : fwdOk P C h n a o)
    (hn : ¬ (kd P C h n = .st ∧ pa P C h n = a)) : fwdOk P C h (n + 1) a o := by
  match o, hf with
  | none, hf =>
    intro j hj hs
    rcases Nat.lt_or_ge j n with h1 | h1
    · exact hf j h1 hs
    · have : j = n := by omega
      subst this; exact fun hp => hn ⟨hs, hp⟩
  | some (tf, vf), ⟨j, hj, hs, hpa, hl, htf, hv⟩ =>
    refine ⟨j, by omega, hs, hpa, fun j2 h1 h2 hs2 => ?_, htf, fun j' h1 h2 => hv j' (by omega) h2⟩
    rcases Nat.lt_or_ge j2 n with h3 | h3
    · exact hl j2 h1 h3 hs2
    · have : j2 = n := by omega
      subst this; exact fun hp => hn ⟨hs2, hp⟩

theorem prom_mono {h n : Nat} {prom : List Nat}
    (hp : ∀ t, t ∈ prom ↔ ∃ j, n ≤ j ∧ j < NN P C h ∧ kd P C h j = .st ∧ vo P C (h, j) = t)
    (hn : kd P C h n ≠ .st) :
    ∀ t, t ∈ prom ↔ ∃ j, n + 1 ≤ j ∧ j < NN P C h ∧ kd P C h j = .st ∧ vo P C (h, j) = t := by
  intro t; rw [hp t]
  constructor
  · rintro ⟨j, h1, h2, h3, h4⟩
    refine ⟨j, ?_, h2, h3, h4⟩
    rcases Nat.lt_or_ge n j with h5 | h5
    · exact h5
    · have : j = n := by omega
      subst this; exact absurd h3 hn
  · rintro ⟨j, h1, h2, h3, h4⟩; exact ⟨j, by omega, h2, h3, h4⟩

/-- Transport over a step that emits no event and moves no view but the register views and `vcap`. -/
theorem inv_nomem {h : Nat} {s s' : Weak.Mini.MSt} {H H' : MHart} (hI : Inv P C h s H) (hevs : s'.evs = s.evs)
    (hpc : H'.fr.pc = s'.pc) (hq : H'.fr.q = []) (hlen : H'.fr.regs.length = 32)
    (hregs : ∀ r, H'.fr.rd r = (s'.rd r).1) (hlt : ∀ r, (s'.rd r).1 < two64)
    (hregv : ∀ r, 0 < r → r < 32 → dom P C h (· ∈ (s'.rd r).2) (H'.ws.regv r))
    (hvcap : ∀ j, s.evs.length ≤ j → j < NN P C h → kd P C h j = .st → H'.ws.vcap < vo P C (h, j))
    (h1 : H'.ws.vrOld = H.ws.vrOld) (h2 : H'.ws.vwOld = H.ws.vwOld) (h3 : H'.ws.vrNew = H.ws.vrNew)
    (h4 : H'.ws.vwNew = H.ws.vwNew) (h5 : H'.ws.coh = H.ws.coh) (h6 : H'.ws.fwd = H.ws.fwd)
    (h7 : H'.ws.ldv = 0) (h8 : H'.prom = H.prom) : Inv P C h s' H' := by
  refine ⟨hpc, hq, hlen, hregs, hlt, hregv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h7, ?_⟩
  · rw [h1, hevs]; exact hI.vrOld
  · rw [h2, hevs]; exact hI.vwOld
  · rw [h3, hevs]; exact hI.vrNew
  · rw [h4, hevs]; exact hI.vwNew
  · rw [hevs]; exact hvcap
  · rw [h5, hevs]; exact hI.coh1
  · rw [h5, hevs]; exact hI.coh2
  · rw [h6, hevs]; exact hI.fwd
  · rw [h8, hevs]; exact hI.prom

end Weak.Mini.Cmp
