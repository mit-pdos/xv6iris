/-
Weak/Mini: **E1 for loop-free programs — the corollary against `progExec`** (mini plan rev 4 §2 L1 "for loop-free
programs a corollary against `progExec`/`rvwmoRef`").  `progExec` (RefProg.lean) runs each hart to its end with
`symRun` (the forward-only front end `stepI`, one choice per branch) and checks `rvwmoRef`.

* `e1aLF` — a loop-free program's mini cut whose harts have all halted is a `progExec` execution, along the choices
  its states recorded (`chsOf`).
* `e1bLF` — every `progExec` execution of an F program is a halted mini cut, with `runAll chs = some (toCut P cond C)`
  (the same states, so the same `finalReg`), the same events and contents, the same gmo.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqRefCut

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx

/-- The branch choices a state's path recorded. -/
def chOf (s : SSt) : List Bool := s.conds.map (fun c => c.2.2.2)

/-! ## 1. `symRun` and `LReach` -/

theorem stepL_of_stepI {h n : Nat} {s : SSt} {i : Instr} (hs : stepI h n s i ≠ .stuck) : stepL h n s i = stepI h n s i := by
  cases i with
  | br c rs1 rs2 tgt =>
    simp only [stepL, stepI] at hs ⊢
    split at hs
    · exact absurd rfl hs
    · rename_i hc
      have h2 : ¬ n < tgt := fun h' => hc (.inr h')
      simp only [if_neg hc, if_neg h2]
  | jmp tgt =>
    simp only [stepL, stepI] at hs ⊢
    split at hs
    · exact absurd rfl hs
    · rename_i hc
      have h2 : ¬ n < tgt := fun h' => hc (.inr h')
      simp only [if_neg hc, if_neg h2]
  | _ => rfl

/-- A `symRun` result is reachable and halted. -/
theorem symRun_reach (p : List Instr) (h : Nat) (s0 : SSt) :
    ∀ fuel s ch s', symRun p h fuel s ch = some s' → LReach p h s0 s → LReach p h s0 s' ∧ s'.pc = p.length
  | 0, _, _, _, hr, _ => by cases hr
  | fuel + 1, s, ch, s', hr, hreach => by
    unfold symRun at hr
    split at hr
    · rename_i hp; split at hr
      · cases hr; exact ⟨hreach, hp⟩
      · cases hr
    · cases hi : p[s.pc]? with
      | none => rw [hi] at hr; cases hr
      | some i =>
        rw [hi] at hr
        simp only at hr
        cases hst : stepI h p.length s i with
        | stuck => rw [hst] at hr; cases hr
        | next s1 =>
          rw [hst] at hr
          have hl : stepL h p.length s i = .next s1 := by rw [stepL_of_stepI (by rw [hst]; exact StepR.noConfusion), hst]
          exact symRun_reach p h s0 fuel s1 ch s' hr (.step hreach (.inr ⟨i, hi, .inl hl⟩))
        | fork t f =>
          rw [hst] at hr
          have hl : stepL h p.length s i = .fork t f := by
            rw [stepL_of_stepI (by rw [hst]; exact StepR.noConfusion), hst]
          rcases ch with _ | ⟨b, ch'⟩
          · cases hr
          · cases b
            · exact symRun_reach p h s0 fuel f ch' s' hr (.step hreach (.inr ⟨i, hi, .inr ⟨t, f, hl, .inr rfl⟩⟩))
            · exact symRun_reach p h s0 fuel t ch' s' hr (.step hreach (.inr ⟨i, hi, .inr ⟨t, f, hl, .inl rfl⟩⟩))

theorem runFrom_get (T : Test) : ∀ (chs : List (List Bool)) (k : Nat) (trs : List SSt), T.runFrom k chs = some trs →
    trs.length = chs.length ∧ ∀ j (hj : j < trs.length) (hj' : j < chs.length), T.runH (k + j) chs[j] = some trs[j]
  | [], _, trs, h => by cases h; exact ⟨rfl, fun _ hj => by simp at hj⟩
  | c :: cs, k, trs, h => by
    unfold Test.runFrom at h
    cases h1 : T.runH k c with
    | none => rw [h1] at h; cases h
    | some s =>
      cases h2 : T.runFrom (k + 1) cs with
      | none => rw [h1, h2] at h; cases h
      | some r =>
        rw [h1, h2] at h; cases h
        obtain ⟨ih1, ih2⟩ := runFrom_get T cs (k + 1) r h2
        refine ⟨by simp [ih1], fun j hj hj' => ?_⟩
        cases j with
        | zero => simpa using h1
        | succ j =>
          have := ih2 j (by simpa using hj) (by simpa using hj')
          rw [show k + 1 + j = k + (j + 1) by omega] at this
          simpa using this

theorem runFrom_of (T : Test) : ∀ (L : List SSt) (k : Nat),
    (∀ j (hj : j < L.length), T.runH (k + j) (chOf L[j]) = some L[j]) → T.runFrom k (L.map chOf) = some L
  | [], _, _ => rfl
  | s :: L, k, h => by
    have h0 := h 0 (by simp)
    have ih := runFrom_of T L (k + 1) (fun j hj => by
      have := h (j + 1) (by simp; omega)
      rw [show k + (j + 1) = k + 1 + j by omega] at this; simpa using this)
    simp only [List.map_cons, Test.runFrom]
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0, ih]

/-! ## 2. The replay of a loop-free program is a `symRun` -/

section lf

variable {P : MProg} {cond : OC} {h : Nat} {V : EvId → Nat}

theorem replay_halted (hs : ∀ k, FStep ((P.toTest cond).prog h) h (nuOf P.sz V)
      (replay (P.toTest cond) h (nuOf P.sz V) k) (replay (P.toTest cond) h (nuOf P.sz V) (k + 1)))
    {j : Nat} (hj : (replay (P.toTest cond) h (nuOf P.sz V) j).pc = ((P.toTest cond).prog h).length) :
    ∀ d, replay (P.toTest cond) h (nuOf P.sz V) (j + d) = replay (P.toTest cond) h (nuOf P.sz V) j
  | 0 => rfl
  | d + 1 => by
    have ih := replay_halted hs hj d
    show rstep _ h _ (replay _ h _ (j + d)) = _
    rw [ih]; unfold rstep; rw [hj]; simp

theorem replay_conds (hs : ∀ k, FStep ((P.toTest cond).prog h) h (nuOf P.sz V)
      (replay (P.toTest cond) h (nuOf P.sz V) k) (replay (P.toTest cond) h (nuOf P.sz V) (k + 1)))
    (j : Nat) : ∀ d, (replay (P.toTest cond) h (nuOf P.sz V) j).conds <+:
      (replay (P.toTest cond) h (nuOf P.sz V) (j + d)).conds
  | 0 => List.prefix_refl _
  | d + 1 => (replay_conds hs j d).trans (lstep_conds (lstep_of_fstep (hs (j + d))))

theorem drop_chOf {l L : List PCond} {x : PCond} (hp : l ++ [x] <+: L) :
    (L.map (fun c => c.2.2.2)).drop l.length = x.2.2.2 :: (L.map (fun c => c.2.2.2)).drop (l.length + 1) := by
  obtain ⟨r, rfl⟩ := hp
  simp [List.drop_append]

/-- **A loop-free replay to a halted state is the `symRun` along its recorded choices.** -/
theorem symRun_replay (hwf : P.wf) (hfwd : P.fwd) {k : Nat}
    (hk : (replay (P.toTest cond) h (nuOf P.sz V) k).pc = ((P.toTest cond).prog h).length) :
    ∀ fuel j, j ≤ k → ((P.toTest cond).prog h).length - (replay (P.toTest cond) h (nuOf P.sz V) j).pc < fuel →
      symRun ((P.toTest cond).prog h) h fuel (replay (P.toTest cond) h (nuOf P.sz V) j)
        ((chOf (replay (P.toTest cond) h (nuOf P.sz V) k)).drop
          (replay (P.toTest cond) h (nuOf P.sz V) j).conds.length) =
        some (replay (P.toTest cond) h (nuOf P.sz V) k) := by
  have hrs := fun k => replay_sim (cond := cond) (agree_nuOf P.sz V) (tgtOk_of_wf hwf h) k
  have hs := fun k => (hrs k).2.1
  intro fuel
  induction fuel with
  | zero => intro j _ hj; omega
  | succ fuel ih =>
    intro j hjk hj
    unfold symRun
    split
    · rename_i hp
      have : replay (P.toTest cond) h (nuOf P.sz V) k = replay (P.toTest cond) h (nuOf P.sz V) j := by
        have := replay_halted hs hp (k - j); rwa [Nat.add_sub_cancel' hjk] at this
      rw [this]
      simp [chOf]
    · rename_i hp
      have hjk' : j < k := by
        rcases Nat.lt_or_eq_of_le hjk with h' | h'
        · exact h'
        · subst h'; exact absurd hk hp
      rcases hs j with ⟨hp', _⟩ | ⟨i, hi, hc⟩
      · exact absurd hp' hp
      rw [hi]
      simp only
      have hlt := (List.getElem?_eq_some_iff.1 hi).1
      obtain ⟨mi, hmi, rfl⟩ := instr_at hi
      have hok := tgtOk_of_wf hwf h mi (List.mem_of_getElem? hmi)
      have hnst : stepI h ((P.toTest cond).prog h).length (replay (P.toTest cond) h (nuOf P.sz V) j)
          (mi.toInstr P.sz) ≠ .stuck := by
        cases mi with
        | br c rs1 rs2 tgt =>
          have := hfwd h _ c rs1 rs2 tgt (.inl hmi)
          simp only [MI.tgtOk] at hok
          simp only [MI.toInstr, stepI, prog_toTest, List.length_map]
          rw [if_neg (by omega)]; exact StepR.noConfusion
        | jmp tgt =>
          have := hfwd h _ .eq 0 0 tgt (.inr hmi)
          simp only [MI.tgtOk] at hok
          simp only [MI.toInstr, stepI, prog_toTest, List.length_map]
          rw [if_neg (by omega)]; exact StepR.noConfusion
        | _ => exact StepR.noConfusion
      rw [← stepL_of_stepI hnst]
      have hpre := replay_conds hs (j + 1) (k - (j + 1))
      rw [show j + 1 + (k - (j + 1)) = k by omega] at hpre
      have hpc : (replay (P.toTest cond) h (nuOf P.sz V) j).pc <
          (replay (P.toTest cond) h (nuOf P.sz V) (j + 1)).pc := by
        have hS := (hrs j).1; have hS' := (hrs (j + 1)).1
        rw [hS.pc, hS'.pc]
        show (mrun P V h j).pc < (mstep P V h (mrun P V h j)).pc
        rw [hS.pc] at hmi
        unfold mstep; rw [hmi]
        cases mi with
        | br c rs1 rs2 tgt =>
          have := hfwd h _ c rs1 rs2 tgt (.inl hmi)
          simp only [exec]; split <;> omega
        | jmp tgt => have := hfwd h _ .eq 0 0 tgt (.inr hmi); simp only [exec]; omega
        | alui => simp only [exec]; unfold MSt.wr; split <;> simp [MSt.adv]
        | alu => simp only [exec]; unfold MSt.wr; split <;> simp [MSt.adv]
        | load => simp only [exec]; unfold MSt.wr; split <;> simp [MSt.adv, MSt.emit]
        | store => simp [exec, MSt.adv, MSt.emit]
        | fence => simp [exec, MSt.adv, MSt.emit]
        | nop => simp [exec, MSt.adv]
      have ih' := ih (j + 1) (by omega) (by omega)
      cases hst : stepL h ((P.toTest cond).prog h).length (replay (P.toTest cond) h (nuOf P.sz V) j)
          (mi.toInstr P.sz) with
      | stuck => rw [hst] at hc; cases hc
      | next s1 =>
        rw [hst] at hc
        simp only [chosen, Option.some.injEq] at hc
        subst hc
        simp only
        rw [← (stepL_conds mi).1 _ hst]; exact ih'
      | fork t f =>
        rw [hst] at hc
        simp only [chosen, Option.some.injEq] at hc
        obtain ⟨c, rs1, rs2, ht, hf⟩ := (stepL_conds mi).2 t f hst
        simp only
        split at hc
        · rw [← hc, ht] at hpre
          rw [chOf, drop_chOf hpre]
          simp only
          rw [← hc] at ih'; rw [ht] at ih'
          simpa [chOf] using ih'
        · rw [← hc, hf] at hpre
          rw [chOf, drop_chOf hpre]
          simp only
          rw [← hc] at ih'; rw [hf] at ih'
          simpa [chOf] using ih'

end lf

/-! ## 3. The corollary -/

/-- **E1a (loop-free)**: a halted mini cut of a loop-free F program is a `progExec` execution. -/
theorem e1aLF (P : MProg) (hwf : P.wf) (hfwd : P.fwd) (cond : OC) (C : MCut) (hC : miniCut P C)
    (hh : C.halted P) :
    progExec (P.toTest cond) ((toCut P cond C).map chOf) (nuOf P.sz C.V) C.g ∧
      (P.toTest cond).runAll ((toCut P cond C).map chOf) = some (toCut P cond C) := by
  obtain ⟨_, _, hcond, href⟩ := (e1aCut P hwf cond C).1 hC
  have hrun : (P.toTest cond).runAll ((toCut P cond C).map chOf) = some (toCut P cond C) := by
    unfold Test.runAll
    rw [if_pos (by simp [toCut_len, harts_toTest])]
    apply runFrom_of
    intro j hj
    have hjn : j < P.harts.length := by rw [← toCut_len P cond C]; exact hj
    rw [Nat.zero_add, toCut_get]
    have hS := (simC_toCut hwf cond C).sim j hj
    rw [toCut_get] at hS
    have hk : (replay (P.toTest cond) j (nuOf P.sz C.V) (C.ks j)).pc = ((P.toTest cond).prog j).length := by
      rw [hS.pc, prog_toTest, List.length_map]; exact hh j hjn
    have := symRun_replay (cond := cond) hwf hfwd hk ((P.toTest cond).prog j).length.succ 0 (Nat.zero_le _)
      (by simp only [replay, Test.init, Nat.sub_zero]; omega)
    have h0 : (replay (P.toTest cond) j (nuOf P.sz C.V) 0).conds.length = 0 := rfl
    rw [h0, List.drop_zero] at this
    exact this
  refine ⟨?_, hrun⟩
  unfold progExec; rw [hrun]; exact ⟨hcond, href⟩

/-- **E1b (loop-free)**: every `progExec` execution of an F program is a halted mini cut: `runAll chs` gives exactly
`toCut P cond C`, with the same events, contents and gmo. -/
theorem e1bLF (P : MProg) (hwf : P.wf) (cond : OC) (chs : List (List Bool)) (ν : Val) (g : List EvId)
    (hE : progExec (P.toTest cond) chs ν g) :
    ∃ C, miniCut P C ∧ C.halted P ∧ (P.toTest cond).runAll chs = some (toCut P cond C) ∧
      (∀ e, e ∈ (conc (P.toTest cond) (toCut P cond C) ν g).ids ↔
        e ∈ (conc (P.toTest cond) (toCut P cond C) (nuOf P.sz C.V) C.g).ids) ∧
      (∀ e ∈ (conc (P.toTest cond) (toCut P cond C) ν g).ids, (conc (P.toTest cond) (toCut P cond C) ν g).ev e =
        (conc (P.toTest cond) (toCut P cond C) (nuOf P.sz C.V) C.g).ev e) ∧ g = C.g := by
  unfold progExec at hE
  cases hr : (P.toTest cond).runAll chs with
  | none => rw [hr] at hE; exact hE.elim
  | some trs =>
    rw [hr] at hE
    obtain ⟨hc, href⟩ := hE
    unfold Test.runAll at hr
    split at hr
    · rename_i hl
      obtain ⟨hlen, hget⟩ := runFrom_get _ chs 0 trs hr
      have hreach : ∀ h (hh : h < trs.length), LReach ((P.toTest cond).prog h) h ((P.toTest cond).init h) trs[h] ∧
          trs[h].pc = ((P.toTest cond).prog h).length := by
        intro h hh
        have := hget h hh (by rw [← hlen]; exact hh)
        rw [Nat.zero_add] at this
        exact symRun_reach _ h _ _ _ _ _ this .refl
      obtain ⟨C, hC, htrs, hids, hev, hg⟩ := e1bCut P hwf cond trs ν g
        ⟨by rw [hlen, hl], fun h hh => (hreach h hh).1, hc, href⟩
      subst htrs
      refine ⟨C, hC, fun h hh => ?_, rfl, hids, hev, hg⟩
      have hh' : h < (toCut P cond C).length := by rw [toCut_len]; exact hh
      have := (hreach h hh').2
      rw [((simC_toCut hwf cond C).sim h hh').pc, prog_toTest, List.length_map] at this
      exact this
    · cases hr

end Weak.Mini
