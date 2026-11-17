/-
Weak/Mini: **L5 MiniPfx — THE PREFIX LEMMA, and completeness for infinite executions** (mini plan rev 4 §2 L5;
owner ruling [OWN.P4] "prove the prefix lemma").

* `mini_prefix`: every infinite execution `X` of `P` and every finite list `O` of its memory operations give a
  FINITE execution `C` (`miniCut`) that has every event of `X` up to each observed one, unchanged (po-down(O)), and
  whose harts are at the same steps of the same paths as `X`'s (same pc, control taint, and events up to their
  values; only the values of "late" loads, and what they feed, may differ: re-sourcing, PfxCut.lean header).
* `mini_inf_complete` (L5 then L4): a valid run of MiniMach whose every hart's load values extend `X`'s up to each
  observed event, and whose harts end where `X`'s harts are after `ks h` steps.  The run's harts execute `P`'s own
  texts (`mInit P`; the mini front end loops), so no unrolled program and no `unrollOf` gap (Weak/Prom/PfxUnroll.lean)
  arises.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.PfxAx
import Weak.Mini.CmpMain

namespace Weak.Mini.Pfx

open Weak.Mini Weak.Mini.Cmp Weak.Mini.Mach

noncomputable section

open Classical

section lemmas

variable {P : MProg} {X : MExec} {O : List EvId} (H : Hyp P X O)
include H

theorem cut_miniCut : miniCut P (cutC P X O) := by
  have hX := H.ex
  refine ⟨(List.mergeSort_perm _ _).nodup_iff.2 (nodup_ndL _), fun e => ?_, fun e he => ?_, c_gmoOk H, ?_, ?_,
    progress_of_list (gC P X O) (fun a b h => h.1)⟩
  · show e ∈ (Dm P X O).mergeSort _ ↔ _
    rw [List.mem_mergeSort, mem_Dm, c_isMem H]
  · obtain ⟨hd, hm⟩ := (c_isMem H e).1 he
    rw [c_pa H hd]; exact hX.1 e hm
  · -- preserved program order
    intro a b ⟨ha, hb, hpo, hr⟩
    obtain ⟨haD, haM⟩ := (c_isMem H a).1 ha
    obtain ⟨hbD, hbM⟩ := (c_isMem H b).1 hb
    have hpo' := (c_po H haD hbD).1 hpo
    refine (c_gmo H a b).2 ⟨(mem_Dm a).2 ⟨haD, haM⟩, (mem_Dm b).2 ⟨hbD, hbM⟩, ?_⟩
    have hk : ∀ {e}, inD P X O e → (((cutC P X O).evs P).ev e).kind = ((X.evs P).ev e).kind :=
      fun he => c_kind H he
    have hst : ∀ {e}, inD P X O e → ((cutC P X O).evs P).isSt e → (X.evs P).isSt e := fun he h => by
      unfold MEvs.isSt at h ⊢; rw [← hk he]; exact h
    have hld : ∀ {e}, inD P X O e → ((cutC P X O).evs P).isLd e → (X.evs P).isLd e := fun he h => by
      unfold MEvs.isLd at h ⊢; rw [← hk he]; exact h
    rcases hr with h1 | h2 | h4 | h9 | h10 | h11 | h12 | h13
    · exact ppoX hX haM hbM hpo' (.inl ⟨hst hbD h1.1, by rw [← c_pa H haD, ← c_pa H hbD]; exact h1.2⟩)
    · obtain ⟨hla, hlb, hpa, hno, oa, ob, hra, hrb, hne⟩ := h2
      refine rule2_X H ⟨haD, hld haD hla⟩ ⟨hbD, hld hbD hlb⟩ hpo' (by rw [← c_pa H haD, ← c_pa H hbD]; exact hpa)
        (fun m hm h1 h2 hsm => ?_) (by rw [← c_rf_eq H haD hra, ← c_rf_eq H hbD hrb]; exact hne)
      have hmD := inD_po H hbD hm h2
      exact hno m ((c_has H m).2 hmD) ((c_po H haD hmD).2 h1) ((c_po H hmD hbD).2 h2)
        ⟨by unfold MEvs.isSt; rw [hk hmD]; exact hsm.1, by rw [c_pa H hmD, c_pa H haD]; exact hsm.2⟩
    · obtain ⟨m, f, hm, hkm, h1, h2, hp, hs⟩ := h4
      have hmD := (c_has H m).1 hm
      refine ppoX hX haM hbM hpo' (.inr (.inr (.inl ⟨m, f, inD_has H hmD, by rw [← hk hmD]; exact hkm,
        (c_po H haD hmD).1 h1, (c_po H hmD hbD).1 h2, ?_, ?_⟩)))
      · rcases hp with hp | hp
        · exact .inl ⟨hld haD hp.1, hp.2⟩
        · exact .inr ⟨hst haD hp.1, hp.2⟩
      · rcases hs with hs | hs
        · exact .inl ⟨hld hbD hs.1, hs.2⟩
        · exact .inr ⟨hst hbD hs.1, hs.2⟩
    · exact ppoX hX haM hbM hpo' (.inr (.inr (.inr (.inl ⟨h9.1, by rw [← c_adep H hbD]; exact h9.2⟩))))
    · exact ppoX hX haM hbM hpo'
        (.inr (.inr (.inr (.inr (.inl ⟨hst hbD h10.1, h10.2.1, by rw [← c_ddep H hbD]; exact h10.2.2⟩)))))
    · exact ppoX hX haM hbM hpo'
        (.inr (.inr (.inr (.inr (.inr (.inl ⟨hst hbD h11.1, h11.2.1, by rw [← c_cdep H hbD]; exact h11.2.2⟩))))))
    · obtain ⟨hl, m, hm, h1, h2, hs, hd, hrf⟩ := h12
      have hmD := (c_has H m).1 hm
      exact rule12_X H haM ⟨hbD, hld hbD hl⟩ hmD ((c_po H haD hmD).1 h1) ((c_po H hmD hbD).1 h2)
        (by have := hst hmD hs; exact this) (by rw [← c_adep H hmD, ← c_ddep H hmD]; exact hd)
        (c_rf_eq H hbD hrf).symm
    · obtain ⟨hs, m, hm, h1, h2, hd⟩ := h13
      obtain ⟨hmD, hmM⟩ := (c_isMem H m).1 hm
      exact ppoX hX haM hbM hpo' (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hst hbD hs, m, hmM,
        (c_po H haD hmD).1 h1, (c_po H hmD hbD).1 h2, by rw [← c_adep H hmD]; exact hd⟩)))))))
  · -- the load value axiom
    intro r hr hl
    have hrD := (c_has H r).1 hr
    have hd : isDLd P X O r := ⟨hrD, by rw [← c_kind H hrD]; exact hl⟩
    refine ⟨csrc P X O r, c_rf H hrD, ?_⟩
    obtain ⟨_, hlen⟩ := c_noV H hrD
    have hv : (((cutC P X O).evs P).ev r).v = VC P X O r % 2 ^ (8 * P.sz) := by
      show ((((cutC P X O).st P r.1).evs[r.2]?).getD default).v = _
      have hl' : (((cutC P X O).st P r.1).evs[r.2]).kind = .ld := by
        have := hl; unfold MEvs.isLd at this
        change ((((cutC P X O).st P r.1).evs[r.2]?).getD default).kind = .ld at this
        rwa [List.getElem?_eq_getElem hlen] at this
      rw [List.getElem?_eq_getElem hlen]
      exact (mrun_new P (VC P X O) r.1 _ r.2 _ (List.getElem?_eq_getElem hlen)).1 hl'
    rw [hv, ← VC_fix H hd]
    unfold FV; rw [if_pos hd]
    cases hc : csrc P X O r with
    | none => simp only [MEvs.valOf, MProg.ini, Nat.mod_mod]; rw [c_pa H hrD]
    | some w =>
      show evV P X O (VC P X O) w % _ = (((cutC P X O).evs P).ev w).v
      have hwD := ((mem_candL r w).1 ((csrc_spec H r).2 w hc).1).1
      obtain ⟨_, hwl⟩ := c_noV H hwD
      have hlt := mrun_v P (VC P X O) w.1 (ksOf P X O w.1) _ (List.getElem_mem hwl)
      change ((((cutC P X O).st P w.1).evs[w.2]?).getD default).v % _ =
        ((((cutC P X O).st P w.1).evs[w.2]?).getD default).v
      rw [List.getElem?_eq_getElem hwl]
      exact Nat.mod_eq_of_lt hlt

omit H in
theorem ev_ext {a b : MEv} (h1 : noV a = noV b) (h2 : a.v = b.v) : a = b := by
  cases a; cases b; simp only [noV, MEv.mk.injEq] at h1 h2 ⊢; exact ⟨h1.1, h1.2.1, h1.2.2.1, h2, h1.2.2.2.2⟩

/-- The cut has po-down(O) unchanged. -/
theorem cut_agree {o : EvId} (ho : o ∈ O) {i : Nat} (hi : i ≤ o.2) :
    ((cutC P X O).evs P).has (o.1, i) ∧ ((cutC P X O).evs P).ev (o.1, i) = (X.evs P).ev (o.1, i) := by
  have hoM := H.obs o ho
  have hD : inD P X O (o.1, i) :=
    ⟨hoM.1.1, (lt_cutOf _ _ _).2 ⟨o, List.mem_append_left _ ho, rfl, hi⟩⟩
  refine ⟨(c_has H _).2 hD, ev_ext (c_noV H hD).1 ?_⟩
  have hA := agree_good H (good_itV H (Rm P X O + 1)) hD.1
  obtain ⟨hl, he⟩ := run_ev H hD
  obtain ⟨_, hl'⟩ := c_noV H hD
  have hv := hA.evV i _ _ (List.getElem?_eq_getElem hl) (List.getElem?_eq_getElem hl')
  have hPl : ∀ j, j ≤ o.2 → (X.evs P).isMem (o.1, j) → BB P X O o.1 j := fun j hj hm =>
    ⟨Pl_Gl H ((mem_Pl _).2 ⟨o, ho, rfl, hj⟩) hm, (lt_cutOf _ _ _).2 ⟨o, List.mem_append_left _ ho, rfl, hj⟩⟩
  show ((((cutC P X O).st P o.1).evs[i]?).getD default).v = _
  rw [List.getElem?_eq_getElem hl', ← he]
  simp only at he
  cases hk : ((X.evs P).ev (o.1, i)).kind with
  | ld =>
    exact (hv.1 (by rw [he]; exact hk) (hPl i hi ⟨inD_has H hD, .inl hk⟩)).symm
  | st =>
    refine (hv.2.1 (by rw [he]; exact hk) (fun d hd => ?_)).symm
    rw [he] at hd
    obtain ⟨hdl, _, hdm⟩ := ddep_ld H hD hd
    exact hPl d (by simp only at hdl; omega) hdm
  | fence f => exact (hv.2.2 f (by rw [he]; exact hk)).symm

end lemmas

end

end Weak.Mini.Pfx

namespace Weak.Mini

open Weak.Mini.Mach Weak.Mini.Cmp Weak.Mini.Pfx

/-- **L5 — THE PREFIX LEMMA (mini plan rev 4 §2 L5).**  An infinite execution `X` of `P` and a finite list `O` of
its memory operations give a finite execution `C` containing, unchanged, every event of `X` up to each observed
one; every hart of `C` has run as many steps as `X`'s hart in `C` and is at the same pc with the same control taint
and the same events up to their values (`noV`; the values of loads outside po-down(O) may be re-sourced). -/
theorem mini_prefix (P : MProg) (X : MExec) (hX : miniExec P X) (O : List EvId)
    (hO : ∀ e ∈ O, (X.evs P).isMem e) :
    ∃ C : MCut, miniCut P C ∧
      (∀ o ∈ O, ∀ i ≤ o.2, (C.evs P).has (o.1, i) ∧ (C.evs P).ev (o.1, i) = (X.evs P).ev (o.1, i)) ∧
      ∀ h < P.harts.length, (C.st P h).pc = (mrun P X.V h (C.ks h)).pc ∧
        (C.st P h).ctl = (mrun P X.V h (C.ks h)).ctl ∧
        (C.st P h).evs.map noV = (mrun P X.V h (C.ks h)).evs.map noV := by
  have H : Hyp P X O := ⟨hX, hO⟩
  refine ⟨cutC P X O, cut_miniCut H, fun o ho i hi => cut_agree H ho hi, fun h hh => ?_⟩
  have hA := agree_good H (good_itV H (Rm P X O + 1)) hh
  exact ⟨hA.pc.symm, hA.ctl.symm, hA.evs.symm⟩

/-- The load values of `X`'s hart `h` among its first `n` events, in program order. -/
noncomputable def rowX (P : MProg) (X : MExec) (h n : Nat) : List Nat :=
  ldVals ((List.range n).map (fun i => (X.evs P).ev (h, i)))

/-- The proof of `mini_inf_complete`. -/
theorem Pfx.infCompleteRun (P : MProg) (hwf : P.wf) (himm : P.immOk) (X : MExec) (hX : miniExec P X)
    (O : List EvId) (hO : ∀ e ∈ O, (X.evs P).isMem e) :
    ∃ (ks : Nat → Nat) (Mm : List MMsg) (r : MRun), miniValidRun P Mm r ∧
      (∀ o ∈ O, rowX P X o.1 (o.2 + 1) <+: loadVals (r.trace o.1)) ∧
      ∃ c, mSteps P (mInit P) r.evs c ∧ ∀ h < P.harts.length, ∃ H, c.hs[h]? = some H ∧
        H.fr.pc = (mrun P X.V h (ks h)).pc := by
  obtain ⟨C, hC, hag, hst⟩ := mini_prefix P X hX O hO
  obtain ⟨r, hr, hld, c, hc, hpc⟩ := mini_complete P hwf himm C hC
  refine ⟨C.ks, _, r, hr, fun o ho => ?_, c, hc, fun h hh => ?_⟩
  · rw [hld o.1]
    unfold cutLoads rowX ldVals
    apply List.IsPrefix.filterMap
    have hlen : o.2 + 1 ≤ (C.st P o.1).evs.length := (hag o ho o.2 (Nat.le_refl _)).1.2
    have : (List.range (o.2 + 1)).map (fun i => (X.evs P).ev (o.1, i)) = (C.st P o.1).evs.take (o.2 + 1) := by
      apply List.ext_getElem (by simp; omega)
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_take]
      simp only [List.length_map, List.length_range] at h1
      rw [← (hag o ho i (by omega)).2]
      show ((C.st P o.1).evs[i]?).getD default = _
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [this]; exact List.take_prefix _ _
  · obtain ⟨H, h1, h2, _⟩ := hpc h hh
    exact ⟨H, h1, by rw [h2]; exact (hst h hh).1⟩

/-- **L5 then L4 — COMPLETENESS FOR INFINITE EXECUTIONS.**  For a well-formed F program with 64-bit immediates, an
infinite execution `X` and a finite list `O` of its memory operations: a valid run of MiniMach in which every
observed hart's load values extend `X`'s load values up to the observed event, and every hart ends where `X`'s hart
is after `ks h` steps.  The run executes `P`'s own texts (`mInit P`; the front end loops): no unrolling. -/
theorem mini_inf_complete (P : MProg) (hwf : P.wf) (himm : P.immOk) (X : MExec) (hX : miniExec P X)
    (O : List EvId) (hO : ∀ e ∈ O, (X.evs P).isMem e) :
    ∃ (ks : Nat → Nat) (Mm : List MMsg) (r : MRun), miniValidRun P Mm r ∧
      (∀ o ∈ O, rowX P X o.1 (o.2 + 1) <+: loadVals (r.trace o.1)) ∧
      ∃ c, mSteps P (mInit P) r.evs c ∧ ∀ h < P.harts.length, ∃ H, c.hs[h]? = some H ∧
        H.fr.pc = (mrun P X.V h (ks h)).pc :=
  Pfx.infCompleteRun P hwf himm X hX O hO

end Weak.Mini
