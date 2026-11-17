/-
Weak/Mini: **L4 MiniCmp — the machine side: one hart running alone, promises first** (mini plan rev 4 §2 L4;
Pulte AtoP's run shape: every promise first, then each hart along its path, hart after hart).

* `hSteps P log i H τ H'`: hart `i`'s state steps from `H` to `H'` with trace `τ` against a FIXED log (after the
  promise phase no step changes the log); `hSteps_lift` embeds them into `mSteps` of any configuration with that log.
* `promAll`: a list of messages promised in order; what each hart's promise set becomes.
* `hSteps_go1`, `hSteps_q`: the answer-free labels (register write, control, instruction boundary, fence).
Imports: only `Weak.Mini.Mach`.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Mach

namespace Weak.Mini.Cmp

open Weak.Mini Weak.Mini.Mach

/-! ## 1. One hart alone -/

/-- Hart `i`'s state steps against the fixed log `log`. -/
inductive hSteps (P : MProg) (log : List MMsg) (i : Nat) : MHart → List (MLab × Option Nat) → MHart → Prop
  | refl (H : MHart) : hSteps P log i H [] H
  | step (H : MHart) (l : MLab) (o : Option Nat) (fr' : MFront) (ws' : MSt) (prom' : List Nat)
      (τ : List (MLab × Option Nat)) (H' : MHart) :
      mNext P i H.fr l = some fr' → mMem P log i H.prom H.ws l o ws' prom' →
      hSteps P log i ⟨fr', ws', prom'⟩ τ H' → hSteps P log i H ((l, o) :: τ) H'

variable {P : MProg}

theorem hSteps.trans {log : List MMsg} {i : Nat} {H H1 H2 : MHart} {τ1 τ2 : List (MLab × Option Nat)}
    (h1 : hSteps P log i H τ1 H1) (h2 : hSteps P log i H1 τ2 H2) : hSteps P log i H (τ1 ++ τ2) H2 := by
  induction h1 with
  | refl => exact h2
  | step H l o fr' ws' prom' τ H' hn hm _ ih => exact .step _ _ _ _ _ _ _ _ hn hm (ih h2)

/-- The state events of hart `i` with trace `τ`. -/
def stEvs (i : Nat) (τ : List (MLab × Option Nat)) : List MEvt := τ.map (fun p => .st i p.1 p.2)

theorem mSteps_trans {c c1 c2 : MCfg} {es1 es2 : List MEvt} (h1 : mSteps P c es1 c1) (h2 : mSteps P c1 es2 c2) :
    mSteps P c (es1 ++ es2) c2 := by
  induction h1 with
  | refl => exact h2
  | step c0 c1 c2' e es hs _ ih => exact .step _ _ _ _ _ hs (ih h2)

theorem set_self_of {l : List MHart} {i : Nat} {x : MHart} (h : l[i]? = some x) : l.set i x = l := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  split
  · rename_i hij; subst hij; rw [h]; simp [(List.getElem?_eq_some_iff.1 h).1]
  · rfl

/-- A lone hart's steps are machine steps of any configuration with the same log. -/
theorem hSteps_lift {log : List MMsg} {i : Nat} {H H' : MHart} {τ : List (MLab × Option Nat)}
    (hs : hSteps P log i H τ H') : ∀ (hs0 : List MHart), hs0[i]? = some H →
      mSteps P ⟨log, hs0⟩ (stEvs i τ) ⟨log, hs0.set i H'⟩ := by
  induction hs with
  | refl H => intro hs0 hh; rw [set_self_of hh]; exact .refl _
  | step H l o fr' ws' prom' τ H' hn hm _ ih =>
    intro hs0 hh
    have hi := (List.getElem?_eq_some_iff.1 hh).1
    have h1 := mStep.state ⟨log, hs0⟩ i H l o fr' ws' prom' hh hn hm
    have h2 := ih (hs0.set i ⟨fr', ws', prom'⟩) (by simp [hi])
    rw [List.set_set] at h2
    exact .step _ _ _ _ _ h1 h2

/-! ## 2. Traces -/

theorem traceOf_append (h : Nat) : ∀ (es1 es2 : List MEvt), traceOf h (es1 ++ es2) = traceOf h es1 ++ traceOf h es2
  | [], _ => rfl
  | .prom _ _ :: es1, es2 => by simp only [List.cons_append, traceOf]; exact traceOf_append h es1 es2
  | .st i l o :: es1, es2 => by
    simp only [List.cons_append, traceOf]; split <;> simp [traceOf_append h es1 es2]

theorem traceOf_stEvs (h i : Nat) : ∀ (τ : List (MLab × Option Nat)),
    traceOf h (stEvs i τ) = if i = h then τ else []
  | [] => by simp [stEvs, traceOf]
  | p :: τ => by
    have := traceOf_stEvs h i τ
    simp only [stEvs, List.map_cons, traceOf] at this ⊢
    rw [this]; split <;> simp

theorem traceOf_proms (h : Nat) : ∀ (ms : List MMsg), traceOf h (ms.map (fun m => .prom m.tid m)) = []
  | [] => rfl
  | _ :: ms => traceOf_proms h ms

theorem loadVals_append (a b : List (MLab × Option Nat)) : loadVals (a ++ b) = loadVals a ++ loadVals b := by
  simp [loadVals, List.filterMap_append]

/-! ## 3. The promise phase -/

/-- PROMISE every message of `ms` in order (each by its own hart). -/
theorem promAll : ∀ (ms : List MMsg) (c : MCfg),
    (∀ m ∈ ms, m.tid < c.hs.length ∧ m.pa % P.sz = 0 ∧ m.v < wordW P) →
    ∃ c', mSteps P c (ms.map (fun m => .prom m.tid m)) c' ∧ c'.log = c.log ++ ms ∧
      c'.hs.length = c.hs.length ∧
      ∀ i H, c.hs[i]? = some H → ∃ prom', c'.hs[i]? = some ⟨H.fr, H.ws, prom'⟩ ∧
        ∀ t, t ∈ prom' ↔ t ∈ H.prom ∨ (c.log.length < t ∧ ∃ m, (c.log ++ ms)[t - 1]? = some m ∧ m.tid = i)
  | [], c, _ => by
    refine ⟨c, .refl _, by simp, rfl, fun i H hH => ⟨H.prom, hH, fun t => ⟨Or.inl, ?_⟩⟩⟩
    rintro (h | ⟨h1, m, h2, _⟩)
    · exact h
    · have := (List.getElem?_eq_some_iff.1 h2).1; simp at this; omega
  | m :: ms, c, hok => by
    obtain ⟨hlt, hpa, hv⟩ := hok m List.mem_cons_self
    obtain ⟨H0, hH0⟩ : ∃ H0, c.hs[m.tid]? = some H0 := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hs1 := mStep.promise c m.tid H0 m hH0 rfl hpa hv
    let c1 : MCfg := ⟨c.log ++ [m], c.hs.set m.tid { H0 with prom := (c.log.length + 1) :: H0.prom }⟩
    have hlen : c1.hs.length = c.hs.length := by simp [c1]
    obtain ⟨c', hs', hlog, hl', hHc⟩ := promAll ms c1 (fun m' hm' => by
      rw [hlen]; exact hok m' (List.mem_cons_of_mem _ hm'))
    refine ⟨c', .step _ _ _ _ _ hs1 hs', by rw [hlog]; simp [c1], by rw [hl', hlen], ?_⟩
    intro i H hH
    have hi := (List.getElem?_eq_some_iff.1 hH).1
    by_cases him : i = m.tid
    · subst him
      rw [hH0] at hH; cases hH
      obtain ⟨prom', h1, h2⟩ := hHc m.tid { H0 with prom := (c.log.length + 1) :: H0.prom } (by simp [c1, hi])
      refine ⟨prom', h1, fun t => ?_⟩
      rw [h2 t]
      simp only [List.mem_cons, c1, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
      constructor
      · rintro ((rfl | h) | ⟨h3, m', h4, h5⟩)
        · right; refine ⟨by omega, m, ?_, rfl⟩
          rw [show c.log.length + 1 - 1 = c.log.length by omega]; simp
        · exact Or.inl h
        · exact Or.inr ⟨by omega, m', h4, h5⟩
      · rintro (h | ⟨h3, m', h4, h5⟩)
        · exact Or.inl (Or.inr h)
        · by_cases ht : t = c.log.length + 1
          · exact Or.inl (Or.inl ht)
          · exact Or.inr ⟨by omega, m', h4, h5⟩
    · obtain ⟨prom', h1, h2⟩ := hHc i H (by simp [c1, Ne.symm him, hH])
      refine ⟨prom', h1, fun t => ?_⟩
      rw [h2 t]
      simp only [c1, List.length_append, List.length_singleton, List.append_assoc, List.singleton_append]
      constructor
      · rintro (h | ⟨h3, m', h4, h5⟩)
        · exact Or.inl h
        · exact Or.inr ⟨by omega, m', h4, h5⟩
      · rintro (h | ⟨h3, m', h4, h5⟩)
        · exact Or.inl h
        · right
          refine ⟨?_, m', h4, h5⟩
          rcases Nat.lt_or_ge (c.log.length + 1) t with h6 | h6
          · exact h6
          · have ht : t - 1 = c.log.length := by omega
            rw [ht] at h4; simp at h4; subst h4; exact absurd h5.symm him

/-! ## 4. Answer-free labels -/

/-- The labels that need no answer and fulfil nothing. -/
def AF : MLab → Prop
  | .regW _ _ => True
  | .ctrl _ => True
  | .instr => True
  | .fence _ _ _ _ => True
  | _ => False

/-- Their memory effect (the `mMem` arms). -/
def eff (ws : MSt) : MLab → MSt
  | .regW rd srcs => { ws with regv := fun r => if r = rd then srcsView ws srcs else ws.regv r }
  | .ctrl srcs => { ws with vcap := max (srcsView ws srcs) ws.vcap }
  | .instr => { ws with ldv := 0 }
  | .fence pr pw sr sw => fencePost ws pr pw sr sw
  | _ => ws

theorem mMem_eff {log : List MMsg} {i : Nat} {prom : List Nat} {ws : MSt} {l : MLab} (hl : AF l) :
    mMem P log i prom ws l none (eff ws l) prom := by
  cases l with
  | regW rd srcs => exact .regW _ _ _ _
  | ctrl srcs => exact .ctrl _ _ _
  | instr => exact .instr _ _
  | fence pr pw sr sw => exact .fence _ _ _ _ _ _
  | _ => cases hl

/-- The queued answer-free labels. -/
theorem hSteps_q {log : List MMsg} {i : Nat} : ∀ (labs : List MLab), (∀ l ∈ labs, AF l) →
    ∀ (fr : MFront) (ws : MSt) (prom : List Nat), fr.q = labs →
      hSteps P log i ⟨fr, ws, prom⟩ (labs.map (fun l => (l, none))) ⟨⟨fr.pc, fr.regs, []⟩, labs.foldl eff ws, prom⟩
  | [], _, fr, ws, prom, hq => by
    cases fr; simp only at hq; subst hq; exact .refl _
  | l :: rest, hAF, fr, ws, prom, hq => by
    have hn : mNext P i fr l = some ⟨fr.pc, fr.regs, rest⟩ := by simp [mNext, hq]
    exact .step _ _ _ _ _ _ _ _ hn (mMem_eff (hAF l List.mem_cons_self))
      (hSteps_q rest (fun l' hl' => hAF l' (List.mem_cons_of_mem _ hl')) ⟨fr.pc, fr.regs, rest⟩ _ prom rfl)

/-- An instruction all of whose labels are answer-free. -/
theorem hSteps_go1 {log : List MMsg} {i : Nat} {H : MHart} {ins : MI} {regs' : List Nat} {pc' : Nat}
    {l0 : MLab} {rest : List MLab} (hq : H.fr.q = []) (hi : (P.prog i)[H.fr.pc]? = some ins)
    (hn : instrNext P (P.prog i).length H.fr ins l0 = go1 H.fr regs' pc' (l0 :: rest) l0)
    (hAF : ∀ l ∈ l0 :: rest, AF l) :
    hSteps P log i H ((l0 :: rest).map (fun l => (l, none)))
      ⟨⟨pc', regs', []⟩, (l0 :: rest).foldl eff H.ws, H.prom⟩ := by
  have hn' : mNext P i H.fr l0 = some ⟨pc', regs', rest⟩ := by
    simp only [mNext, hq, hi]; rw [hn]; simp [go1]
  exact .step _ _ _ _ _ _ _ _ hn' (mMem_eff (hAF l0 List.mem_cons_self))
    (hSteps_q rest (fun l hl => hAF l (List.mem_cons_of_mem _ hl)) ⟨pc', regs', rest⟩ _ _ rfl)

theorem loadVals_af : ∀ (labs : List MLab), (∀ l ∈ labs, AF l) → loadVals (labs.map (fun l => (l, none))) = []
  | [], _ => rfl
  | l :: rest, h => by
    have := loadVals_af rest (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    have hl := h l List.mem_cons_self
    simp only [List.map_cons, loadVals, List.filterMap_cons] at this ⊢
    cases l <;> first | exact this | cases hl

end Weak.Mini.Cmp
