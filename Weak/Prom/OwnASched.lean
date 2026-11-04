/-
Weak/Prom: **track (a), THE SCHEDULE LEMMA** (stage S4a; plan rev 7 §3 "Schedule lemma (to prove, program-agnostic,
S4a)", "`stage`, defined once", "Claim (frontier)"; R-a2).

Plan §3: "Thread runs in the state phase are independent given M (§2) … So adequacy may *choose* their
interleaving.  Choose the timestamp-ordered schedule over non-A/D messages".  Machine v2 has no A/D class
([OWN.P3]), so every timestamp is a segment target.

The lemma proved here (`sched_main`, `sched`): given every hart's SOLO RUN against `M` (CoreRun.lean
`validRun_soloD`) and the partition (every timestamp of `M` is fulfilled in some hart's trace), there is an
execution of the GUARDED concurrent language (OwnALang.lean `cstep`: every step keeps the stepping hart's frontier
claim `fOk`) from every hart's initial state to every hart's final state, with every hart's trace the given one.

The schedule is the plan's, phrased as a progress argument: at every point step the AUTHOR OF THE LEAST UNFULFILLED
TIMESTAMP `i` (plan: "For each nᵢ in turn, run M[nᵢ]'s author up to and including its fulfil of nᵢ"); once every
timestamp is fulfilled, step any hart ("Then run every hart to its end").  The frontier claim holds after each step
(plan "Claim (frontier)"): the author's fulfil of `i` is still ahead or is this step, so its frontier after the step
is at most `i` (`solo_floor`: EXT through `floor_le_fulPv`; `post_floor_le` for the fulfil step itself); every
`t < i` is fulfilled (least), and `i` is fulfilled if the frontier reached it.
No program premise.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALang

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF
open PLabel
open Iris Iris.ProgramLogic Iris.ProgramLogic.Language

variable {P D V : Type}

/-! ## 1. Solo-run facts -/

/-- The frontier before a solo run that fulfils `t` is below `t` (plan §3 "Claim (frontier)": "In segment nᵢ the
fulfil of nᵢ is a later non-A/D step of h.  Its pre-view contains `vcap ⊔ vwNew` … both are monotone"). -/
theorem solo_floor {pst : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat} :
    ∀ {x y : P × PState × GSet Nat} {tr : Trace}, soloSteps pst img M i x tr y →
      ∀ t, (∃ e ∈ tr, e.2 = some t) → stFloor x.2.1 < t := by
  intro x y tr h
  induction h with
  | refl x => intro t ⟨e, he, _⟩; cases he
  | step x l ots p' ws' prom' tr y hp hm hrest ih =>
    intro t ⟨e, he, het⟩
    rcases List.mem_cons.1 he with rfl | he
    · simp only at het; subst het; exact floor_lt_ts hm
    · exact Nat.lt_of_le_of_lt (floors_mono hm) (ih t ⟨e, he, het⟩)

/-- A solo run with no steps does not move. -/
theorem soloSteps_nil {pst : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat}
    {x y : P × PState × GSet Nat} (h : soloSteps pst img M i x [] y) : x = y := by
  cases h; rfl

/-- A least element. -/
theorem exists_least {p : Nat → Prop} (h : ∃ n, p n) : ∃ n, p n ∧ ∀ m, m < n → ¬ p m := by
  apply Classical.byContradiction
  intro hno
  have key : ∀ n, ∀ k, k ≤ n → ¬ p k := by
    intro n
    induction n with
    | zero => intro k hk hp; exact hno ⟨k, hp, fun m hm => by omega⟩
    | succ n ih =>
      intro k hk hp
      exact hno ⟨k, hp, fun m hm hpm => ih m (by omega) hpm⟩
  obtain ⟨n, hn⟩ := h
  exact key n n (Nat.le_refl _) hn

/-! ## 2. Configurations -/

section cfg

variable (pstep : P → D → PLabel → P → D → Prop) (pdone : P → Option V) (img : Image) (M : List PMsg)

/-- Hart `h`'s world. -/
def hw (h : Nat) : HW P D V := ⟨pstep, pdone, img, M, h⟩

/-- THE CONFIGURATION of `n` harts at program/state/promise positions `z` with traces `pre`; harts outside the
domain keep the initial state with no promises and the empty trace. -/
def cfgOf (n : Nat) (z : Nat → P × PState × GSet Nat) (pre : Nat → Trace) : List (CExpr P D V) × CSt :=
  ((List.range n).map (fun h => CExpr.run (hw pstep pdone img M h) (z h).1),
   fun h => if h < n then ((z h).2.1, (z h).2.2, pre h) else (psInit, ∅, []))

end cfg

/-- Update a function at one point. -/
def fupd {α : Type} (f : Nat → α) (a : Nat) (b : α) : Nat → α := fun k => if k = a then b else f k

/-- The measure: the total length of the remaining runs. -/
def msr (n : Nat) (rest : Nat → Trace) : Nat := ((List.range n).map (fun h => (rest h).length)).sum

theorem msr_fupd (rest : Nat → Trace) (A : Nat) (r : Trace) :
    ∀ n, A < n → msr n (fupd rest A r) + (rest A).length = msr n rest + r.length := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hA
    unfold msr at *
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases hn : A = n
    · subst hn
      have hs : ((List.range A).map (fun h => (fupd rest A r h).length)) =
          ((List.range A).map (fun h => (rest h).length)) :=
        List.map_congr_left (fun k hk => by
          have : k ≠ A := by have := List.mem_range.1 hk; omega
          simp [fupd, this])
      rw [hs]; simp [fupd]; omega
    · have := ih (by omega)
      have hn' : n ≠ A := fun h => hn h.symm
      simp only [fupd, if_neg hn'] at this ⊢
      omega

theorem msr_succ (n : Nat) (rest : Nat → Trace) : msr (n + 1) rest = msr n rest + (rest n).length := by
  unfold msr; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem msr_zero {n : Nat} {rest : Nat → Trace} (h : msr n rest = 0) : ∀ h', h' < n → rest h' = [] := by
  induction n with
  | zero => intro h' hh; omega
  | succ n ih =>
    intro h' hh
    rw [msr_succ] at h
    by_cases e : h' = n
    · subst e; exact List.eq_nil_of_length_eq_zero (by omega)
    · exact ih (by omega) h' (by omega)

theorem msr_pos {n : Nat} {rest : Nat → Trace} {m : Nat} (h : msr n rest = m + 1) : ∃ h', h' < n ∧ rest h' ≠ [] := by
  induction n generalizing m with
  | zero => simp [msr] at h
  | succ n ih =>
    rw [msr_succ] at h
    by_cases e : rest n = []
    · rw [e] at h; simp only [List.length_nil, Nat.add_zero] at h
      obtain ⟨h', h1, h2⟩ := ih h
      exact ⟨h', by omega, h2⟩
    · exact ⟨n, by omega, e⟩

/-- Splitting a mapped range at `A`, for two maps that agree off `A`. -/
theorem map_range_split {α : Type} (g g' : Nat → α) (A : Nat) (hg : ∀ k, k ≠ A → g' k = g k) :
    ∀ n, A < n → ∃ t₁ t₂, (List.range n).map g = t₁ ++ g A :: t₂ ∧ (List.range n).map g' = t₁ ++ g' A :: t₂ := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hA
    rw [List.range_succ, List.map_append, List.map_append]
    by_cases hn : A = n
    · subst hn
      refine ⟨(List.range A).map g, [], by simp, ?_⟩
      have : (List.range A).map g' = (List.range A).map g :=
        List.map_congr_left (fun k hk => hg k (by have := List.mem_range.1 hk; omega))
      rw [this]; simp
    · obtain ⟨t₁, t₂, h1, h2⟩ := ih (by omega)
      refine ⟨t₁, t₂ ++ [g n], by rw [h1]; simp, ?_⟩
      rw [h2]; simp [hg n (fun h => hn h.symm)]

/-! ## 3. The schedule lemma -/

section sched

variable {pstep : P → D → PLabel → P → D → Prop} {pdone : P → Option V} {img : Image} {M : List PMsg}

/-- ONE SCHEDULED STEP of hart `A` (a thread step of the concurrent language), given the frontier claim after it. -/
theorem cfg_step {n : Nat} {z : Nat → P × PState × GSet Nat} {pre : Nat → Trace} {A : Nat} (hA : A < n)
    {l : PLabel} {ots : Option Nat} {p' : P} {ws' : PState} {prom' : GSet Nat}
    (hp : anyFab pstep (z A).1 () l p' ()) (hm : memStep img M A (z A).2.2 (z A).2.1 l ots ws' prom')
    (hok : fOk M (updS (cfgOf pstep pdone img M n z pre).2 A (ws', prom', pre A ++ [(l, ots)])) A) :
    Language.Step (cfgOf pstep pdone img M n z pre) []
      (cfgOf pstep pdone img M n (fupd z A (p', ws', prom')) (fupd pre A (pre A ++ [(l, ots)]))) := by
  obtain ⟨d, d', hp⟩ := hp
  have hσA : (cfgOf pstep pdone img M n z pre).2 A = ((z A).2.1, (z A).2.2, pre A) := by
    simp [cfgOf, hA]
  have hσ' : updS (cfgOf pstep pdone img M n z pre).2 A (ws', prom', pre A ++ [(l, ots)]) =
      (cfgOf pstep pdone img M n (fupd z A (p', ws', prom')) (fupd pre A (pre A ++ [(l, ots)]))).2 := by
    funext k
    by_cases hk : k = A
    · subst hk; simp [updS, cfgOf, fupd, hA]
    · simp only [updS, if_neg hk, cfgOf, fupd]
  have hs : cstep (CExpr.run (hw pstep pdone img M A) (z A).1, (cfgOf pstep pdone img M n z pre).2) []
      (CExpr.run (hw pstep pdone img M A) p',
        updS (cfgOf pstep pdone img M n z pre).2 A (ws', prom', pre A ++ [(l, ots)]), []) := by
    have := cstep.lab (hw pstep pdone img M A) (z A).1 (cfgOf pstep pdone img M n z pre).2 l ots p' ws' prom' d d'
      hp (by show memStep img M A ((cfgOf pstep pdone img M n z pre).2 A).2.1
              ((cfgOf pstep pdone img M n z pre).2 A).1 l ots ws' prom'
             rw [hσA]; exact hm)
        (by show fOk M (updS (cfgOf pstep pdone img M n z pre).2 A
              (ws', prom', ((cfgOf pstep pdone img M n z pre).2 A).2.2 ++ [(l, ots)])) A
            rw [hσA]; exact hok)
    change cstep (CExpr.run (hw pstep pdone img M A) (z A).1, (cfgOf pstep pdone img M n z pre).2) []
      (CExpr.run (hw pstep pdone img M A) p', updS (cfgOf pstep pdone img M n z pre).2 A
        (ws', prom', ((cfgOf pstep pdone img M n z pre).2 A).2.2 ++ [(l, ots)]), []) at this
    rw [hσA] at this
    exact this
  obtain ⟨t₁, t₂, h1, h2⟩ := map_range_split (fun h => CExpr.run (hw pstep pdone img M h) (z h).1)
    (fun h => CExpr.run (hw pstep pdone img M h) (fupd z A (p', ws', prom') h).1) A
    (fun k hk => by simp [fupd, hk]) n hA
  have hS := Language.Step.atomic (Λ := (inferInstance : Language (CExpr P D V) CSt Unit V)) hs t₁ t₂
  simp only [List.append_nil] at hS
  have e1 : (cfgOf pstep pdone img M n z pre) =
      (t₁ ++ CExpr.run (hw pstep pdone img M A) (z A).1 :: t₂, (cfgOf pstep pdone img M n z pre).2) := by
    rw [← h1]; rfl
  have e2 : (cfgOf pstep pdone img M n (fupd z A (p', ws', prom')) (fupd pre A (pre A ++ [(l, ots)]))) =
      (t₁ ++ CExpr.run (hw pstep pdone img M A) p' :: t₂,
        updS (cfgOf pstep pdone img M n z pre).2 A (ws', prom', pre A ++ [(l, ots)])) := by
    rw [hσ']
    refine Prod.ext ?_ rfl
    show (List.range n).map (fun h => CExpr.run (hw pstep pdone img M h) (fupd z A (p', ws', prom') h).1) = _
    rw [h2]; simp [fupd]
  rw [e1, e2]
  exact hS

/-- **THE SCHEDULE LEMMA, main induction** (plan §3): from any positions whose remaining runs complete every hart's
trace, the guarded concurrent language reaches every hart's final state. -/
theorem sched_main (n : Nat) (y : Nat → P × PState × GSet Nat) (tr : Nat → Trace)
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → ∃ h, h < n ∧ ∃ e ∈ tr h, e.2 = some t) :
    ∀ m (z : Nat → P × PState × GSet Nat) (pre rest : Nat → Trace), msr n rest = m →
      (∀ h, h < n → soloSteps (anyFab pstep) img M h (z h) (rest h) (y h)) →
      (∀ h, h < n → pre h ++ rest h = tr h) →
      ∃ k, NSteps k (cfgOf pstep pdone img M n z pre) [] (cfgOf pstep pdone img M n y tr) := by
  intro m
  induction m with
  | zero =>
    intro z pre rest hm hs hpre
    refine ⟨0, ?_⟩
    have hr := msr_zero hm
    have hz : ∀ h, h < n → z h = y h := fun h hh => soloSteps_nil (by rw [← hr h hh]; exact hs h hh)
    have hp : ∀ h, h < n → pre h = tr h := fun h hh => by rw [← hpre h hh, hr h hh, List.append_nil]
    have : cfgOf pstep pdone img M n z pre = cfgOf pstep pdone img M n y tr := by
      unfold cfgOf
      congr 1
      · exact List.map_congr_left (fun k hk => by rw [hz k (List.mem_range.1 hk)])
      · funext k
        by_cases hk : k < n
        · simp [hk, hz k hk, hp k hk]
        · simp [hk]
    rw [this]; exact .refl _
  | succ m ih =>
    intro z pre rest hm hs hpre
    -- the shared state
    have hσ : ∀ h, h < n → (cfgOf pstep pdone img M n z pre).2 h = ((z h).2.1, (z h).2.2, pre h) := by
      intro h hh; simp [cfgOf, hh]
    -- choose the hart to step
    have hchoose : ∃ A, A < n ∧ rest A ≠ [] ∧
        ((∀ t, 1 ≤ t → t ≤ M.length → fulAt (cfgOf pstep pdone img M n z pre).2 t) ∨
         ∃ i, 1 ≤ i ∧ i ≤ M.length ∧ (∀ t, 1 ≤ t → t < i → fulAt (cfgOf pstep pdone img M n z pre).2 t) ∧
           ∃ e ∈ rest A, e.2 = some i) := by
      by_cases hall : ∀ t, 1 ≤ t → t ≤ M.length → fulAt (cfgOf pstep pdone img M n z pre).2 t
      · obtain ⟨A, hA, hne⟩ := msr_pos hm
        exact ⟨A, hA, hne, .inl hall⟩
      · have hex : ∃ t, 1 ≤ t ∧ t ≤ M.length ∧ ¬ fulAt (cfgOf pstep pdone img M n z pre).2 t := by
          apply Classical.byContradiction; intro hno
          exact hall (fun t h1 h2 => Classical.byContradiction (fun hn => hno ⟨t, h1, h2, hn⟩))
        obtain ⟨i, ⟨hi1, hi2, hin⟩, hleast⟩ := exists_least hex
        obtain ⟨A, hA, e, he, het⟩ := hpart i hi1 hi2
        have hnotpre : e ∉ pre A := fun hep => hin ⟨A, e, by rw [hσ A hA]; exact hep, het⟩
        rw [← hpre A hA] at he
        have her : e ∈ rest A := by
          rcases List.mem_append.1 he with h | h
          · exact absurd h hnotpre
          · exact h
        refine ⟨A, hA, (fun h => by rw [h] at her; cases her), .inr ⟨i, hi1, hi2, fun t h1 h2 => ?_, e, her, het⟩⟩
        exact Classical.byContradiction (fun hn => hleast t h2 ⟨h1, by omega, hn⟩)
    obtain ⟨A, hA, hne, hcase⟩ := hchoose
    obtain ⟨⟨l, ots⟩, rest', hra⟩ : ∃ e r, rest A = e :: r := by
      cases h : rest A with
      | nil => exact absurd h hne
      | cons e r => exact ⟨e, r, rfl⟩
    have hsA := hs A hA
    rw [hra] at hsA
    cases hsA with
    | step _ _ _ p' ws' prom' _ _ hp hmem hrest =>
      -- the frontier claim after the step
      have hok : fOk M (updS (cfgOf pstep pdone img M n z pre).2 A (ws', prom', pre A ++ [(l, ots)])) A := by
        unfold fOk
        rw [updS_self]
        intro t h1 h2 h3
        have hσA := hσ A hA
        have hlift : ∀ t, fulAt (cfgOf pstep pdone img M n z pre).2 t →
            fulAt (updS (cfgOf pstep pdone img M n z pre).2 A (ws', prom', pre A ++ [(l, ots)])) t := by
          intro t ht
          have := fulAt_updS (σ := (cfgOf pstep pdone img M n z pre).2) (h := A) (ws' := ws') (pr' := prom')
            (e := (l, ots)) ht
          rw [hσA] at this; exact this
        rcases hcase with hall | ⟨i, hi1, hi2, hlt, e, he, het⟩
        · exact hlift t (hall t h1 h2)
        · simp only [wfr] at h3
          rcases List.mem_cons.1 (hra ▸ he) with rfl | he'
          · -- this step is the fulfil of `i`
            simp only at het
            subst het
            have hfl := post_floor_le hmem
            by_cases hti : t < i
            · exact hlift t (hlt t h1 hti)
            · have : t = i := by omega
              subst this
              exact ⟨A, (l, some t), by rw [updS_self]; exact List.mem_append_right _ (List.mem_singleton_self _),
                rfl⟩
          · have hfl := solo_floor hrest i ⟨e, he', het⟩
            exact hlift t (hlt t h1 (by simp only at hfl; omega))
      have hS := cfg_step (pdone := pdone) (pre := pre) hA hp hmem hok
      have hm' : msr n (fupd rest A rest') = m := by
        have := msr_fupd rest A rest' n hA
        rw [hra] at this; simp only [List.length_cons] at this; omega
      obtain ⟨k, hk⟩ := ih (fupd z A (p', ws', prom')) (fupd pre A (pre A ++ [(l, ots)])) (fupd rest A rest') hm'
        (fun h hh => by
          by_cases hhA : h = A
          · subst hhA; simp only [fupd, if_true]; exact hrest
          · simp only [fupd, if_neg hhA]; exact hs h hh)
        (fun h hh => by
          by_cases hhA : h = A
          · subst hhA; simp only [fupd, if_true]; rw [← hpre h hh, hra]; simp
          · simp only [fupd, if_neg hhA]; exact hpre h hh)
      exact ⟨k + 1, by simpa using NSteps.cons hS hk⟩

/-- **THE SCHEDULE LEMMA** (plan §3): every hart's solo run against `M` plus the partition give an execution of
the guarded concurrent language from every hart's initial state (empty trace) to every hart's final state (its
full trace). -/
theorem sched (n : Nat) (x y : Nat → P × PState × GSet Nat) (tr : Nat → Trace)
    (hs : ∀ h, h < n → soloSteps (anyFab pstep) img M h (x h) (tr h) (y h))
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → ∃ h, h < n ∧ ∃ e ∈ tr h, e.2 = some t) :
    ∃ k, NSteps k (cfgOf pstep pdone img M n x (fun _ => [])) [] (cfgOf pstep pdone img M n y tr) :=
  sched_main n y tr hpart _ x (fun _ => []) tr rfl hs (fun _ _ => List.nil_append _)

end sched

end Weak.Prom.OA
