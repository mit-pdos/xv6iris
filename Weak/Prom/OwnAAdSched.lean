/-
Weak/Prom: **SchedAD — THE SCHEDULE LEMMA over E-c's A/D variant** (owner ruling [OWN.P14]; G4-review3.md §5 A-2;
plan rev 7 §3 "Schedule lemma (to prove, program-agnostic, S4a)" rev 5 [R4.4]).

Plan §3: "Choose the timestamp-ordered schedule over non-A/D messages: Let n₁ < n₂ < … be the timestamps t with
`M[t].class ≠ WCad`.  For each nᵢ in turn, run M[nᵢ]'s author up to and including its fulfil of nᵢ … Then run every
hart to its end … A/D messages (`WCad`, M20 (5)) are not segment targets.  Their author fulfils them whenever its own
steps reach them, inside some segment or in the final phase."

`schedV`: given every hart's solo run of the variant against `M` (NfrAd.lean `soloQV`, from `Ad.validRunV_solo`) and
the NON-A/D partition (every non-A/D timestamp is fulfilled by a v2-label entry of some hart's trace), the guarded
language `cstepV` (OwnAAdLang.lean) reaches every hart's final state, with every hart's (projected) trace.  The
schedule steps the author of the LEAST UNFULFILLED NON-A/D timestamp `i`; A/D steps are taken whenever they are the
scheduled hart's next step and need no guard.  The frontier claim after a v2-label step (plan "Claim (frontier)"):
the author's fulfil of `i` is a v2 fulfil still ahead (`solo_floorV`: its pre-view contains the frontier, and A/D
steps do not raise it) or is this step (`post_floor_le`); so `WF ≤ i`, every non-A/D `t < i` is fulfilled (least),
and `i` too if reached.  `prjT` drops the A/D entries of a variant trace (the shared state's traces are v2 traces).
No program premise.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAAdLang

namespace Weak.Prom.OAd

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.OA
open PLabel
open Iris Iris.ProgramLogic Iris.ProgramLogic.Language

variable {P D V : Type}

/-! ## 1. Projected traces, solo-run facts -/

/-- The v2-label entries of a variant trace (A/D updates dropped). -/
def prjT : List (Ad.VLabel × Option Nat) → Trace
  | [] => []
  | (.v l, o) :: r => (l, o) :: prjT r
  | (.ad .., _) :: r => prjT r

theorem prjT_append : ∀ a b : List (Ad.VLabel × Option Nat), prjT (a ++ b) = prjT a ++ prjT b
  | [], _ => rfl
  | (.v l, o) :: a, b => by simp only [List.cons_append, prjT, prjT_append a b]
  | (.ad .., _) :: a, b => by simp only [List.cons_append, prjT, prjT_append a b]

theorem prjT_mem {l : PLabel} {o : Option Nat} :
    ∀ {τ : List (Ad.VLabel × Option Nat)}, (Ad.VLabel.v l, o) ∈ τ → (l, o) ∈ prjT τ
  | [], h => by cases h
  | (.v l', o') :: r, h => by
    rcases List.mem_cons.1 h with e | h
    · cases e; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (prjT_mem (τ := r) h)
  | (.ad .., _) :: r, h => by
    rcases List.mem_cons.1 h with e | h
    · cases e
    · exact prjT_mem (τ := r) h

section solo

variable {pst : P → Unit → Ad.VLabel → P → Unit → Prop} {img : Image} {M : List PMsg} {i : Nat}
  {Q : PState → Ad.VLabel → Option Nat → Prop}

/-- The frontier before a solo run with a v2 fulfil of `t` is below `t` (plan §3 "Claim (frontier)": the fulfil's
pre-view contains `vcap ⊔ vwNew`, "both are monotone, and no A/D step changes them"). -/
theorem solo_floorV : ∀ {x y : P × PState × GSet Nat} {tr : List (Ad.VLabel × Option Nat)},
    Ad.soloQV pst img M i Q x tr y → ∀ l t, (Ad.VLabel.v l, some t) ∈ tr → stFloor x.2.1 < t := by
  intro x y tr h
  induction h with
  | refl x => intro l t he; cases he
  | step x l' ots p' ws' prom' tr y _ _ hm _ ih =>
    intro l t he
    rcases List.mem_cons.1 he with e | he
    · cases e; exact floor_lt_ts (memStepV_v_some hm)
    · exact Nat.lt_of_le_of_lt (floorsV_mono hm) (ih l t he)

/-- An A/D entry of a solo trace fulfils an A/D message. -/
theorem solo_adAt : ∀ {x y : P × PState × GSet Nat} {tr : List (Ad.VLabel × Option Nat)},
    Ad.soloQV pst img M i Q x tr y → ∀ b tvs d t, (Ad.VLabel.ad b tvs d, some t) ∈ tr → Ad.adAt M t := by
  intro x y tr h
  induction h with
  | refl x => intro _ _ _ _ he; cases he
  | step x l' ots p' ws' prom' tr y _ _ hm _ ih =>
    intro b tvs d t he
    rcases List.mem_cons.1 he with e | he
    · cases e; exact memStepV_ad_at hm
    · exact ih b tvs d t he

theorem soloQV_nil {x y : P × PState × GSet Nat} (h : Ad.soloQV pst img M i Q x [] y) : x = y := by
  cases h; rfl

end solo

/-! ## 2. Configurations, the measure -/

section cfg

variable (pstep : P → Unit → Ad.VLabel → P → Unit → Prop) (pdone : P → Option V) (img : Image) (M : List PMsg)

/-- Hart `h`'s world. -/
def hwV (h : Nat) : HWV P Unit V := ⟨pstep, pdone, img, M, h⟩

/-- THE CONFIGURATION of `n` harts at positions `z` with variant traces `pre` (the shared state holds their v2
projections). -/
def cfgOfV (n : Nat) (z : Nat → P × PState × GSet Nat) (pre : Nat → List (Ad.VLabel × Option Nat)) :
    List (CExprV P Unit V) × CSt :=
  ((List.range n).map (fun h => CExprV.run (hwV pstep pdone img M h) (z h).1),
   fun h => if h < n then ((z h).2.1, (z h).2.2, prjT (pre h)) else (psInit, ∅, []))

end cfg

/-- The measure: the total length of the remaining runs. -/
def msrV {α : Type} (n : Nat) (rest : Nat → List α) : Nat := ((List.range n).map (fun h => (rest h).length)).sum

theorem msrV_succ {α : Type} (n : Nat) (rest : Nat → List α) : msrV (n + 1) rest = msrV n rest + (rest n).length := by
  unfold msrV; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem msrV_fupd {α : Type} (rest : Nat → List α) (A : Nat) (r : List α) :
    ∀ n, A < n → msrV n (OA.fupd rest A r) + (rest A).length = msrV n rest + r.length := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hA
    rw [msrV_succ, msrV_succ]
    by_cases hn : A = n
    · subst hn
      have hs : msrV A (OA.fupd rest A r) = msrV A rest := by
        unfold msrV
        exact congrArg List.sum (List.map_congr_left (fun k hk => by
          have : k ≠ A := by have := List.mem_range.1 hk; omega
          simp [OA.fupd, this]))
      rw [hs]; simp [OA.fupd]; omega
    · have := ih (by omega)
      have hn' : n ≠ A := fun h => hn h.symm
      simp only [OA.fupd, if_neg hn'] at this ⊢
      omega

theorem msrV_zero {α : Type} {n : Nat} {rest : Nat → List α} (h : msrV n rest = 0) : ∀ h', h' < n → rest h' = [] := by
  induction n with
  | zero => intro h' hh; omega
  | succ n ih =>
    intro h' hh
    rw [msrV_succ] at h
    by_cases e : h' = n
    · subst e; exact List.eq_nil_of_length_eq_zero (by omega)
    · exact ih (by omega) h' (by omega)

theorem msrV_pos {α : Type} {n : Nat} {rest : Nat → List α} {m : Nat} (h : msrV n rest = m + 1) :
    ∃ h', h' < n ∧ rest h' ≠ [] := by
  induction n generalizing m with
  | zero => simp [msrV] at h
  | succ n ih =>
    rw [msrV_succ] at h
    by_cases e : rest n = []
    · rw [e] at h; simp only [List.length_nil, Nat.add_zero] at h
      obtain ⟨h', h1, h2⟩ := ih h
      exact ⟨h', by omega, h2⟩
    · exact ⟨n, by omega, e⟩

/-! ## 3. The schedule lemma -/

section sched

variable {pstep : P → Unit → Ad.VLabel → P → Unit → Prop} {pdone : P → Option V} {img : Image} {M : List PMsg}

/-- ONE SCHEDULED STEP of hart `A`, given its thread step against the shared state. -/
theorem cfg_stepV {n : Nat} {z : Nat → P × PState × GSet Nat} {pre : Nat → List (Ad.VLabel × Option Nat)} {A : Nat}
    (hA : A < n) {z' : P × PState × GSet Nat} {e : Ad.VLabel × Option Nat}
    (hs : cstepV (CExprV.run (hwV pstep pdone img M A) (z A).1, (cfgOfV pstep pdone img M n z pre).2) []
      (CExprV.run (hwV pstep pdone img M A) z'.1,
        (cfgOfV pstep pdone img M n (OA.fupd z A z') (OA.fupd pre A (pre A ++ [e]))).2, [])) :
    Language.Step (cfgOfV pstep pdone img M n z pre) []
      (cfgOfV pstep pdone img M n (OA.fupd z A z') (OA.fupd pre A (pre A ++ [e]))) := by
  obtain ⟨t₁, t₂, h1, h2⟩ := map_range_split (fun h => CExprV.run (hwV pstep pdone img M h) (z h).1)
    (fun h => CExprV.run (hwV pstep pdone img M h) (OA.fupd z A z' h).1) A
    (fun k hk => by simp [OA.fupd, hk]) n hA
  have hS := Language.Step.atomic (Λ := (inferInstance : Language (CExprV P Unit V) CSt Unit V)) hs t₁ t₂
  simp only [List.append_nil] at hS
  have e1 : (cfgOfV pstep pdone img M n z pre) =
      (t₁ ++ CExprV.run (hwV pstep pdone img M A) (z A).1 :: t₂, (cfgOfV pstep pdone img M n z pre).2) := by
    rw [← h1]; rfl
  have e2 : (cfgOfV pstep pdone img M n (OA.fupd z A z') (OA.fupd pre A (pre A ++ [e]))) =
      (t₁ ++ CExprV.run (hwV pstep pdone img M A) z'.1 :: t₂,
        (cfgOfV pstep pdone img M n (OA.fupd z A z') (OA.fupd pre A (pre A ++ [e]))).2) := by
    refine Prod.ext ?_ rfl
    show (List.range n).map (fun h => CExprV.run (hwV pstep pdone img M h) (OA.fupd z A z' h).1) = _
    rw [h2]; simp [OA.fupd]
  rw [e1, e2]
  exact hS

/-- The shared state after a step of `A` (a v2 label: the projected trace grows; an A/D update: it does not). -/
theorem cfgOfV_upd {n : Nat} {z : Nat → P × PState × GSet Nat} {pre : Nat → List (Ad.VLabel × Option Nat)}
    {A : Nat} (hA : A < n) (z' : P × PState × GSet Nat) (e : Ad.VLabel × Option Nat) :
    (cfgOfV pstep pdone img M n (OA.fupd z A z') (OA.fupd pre A (pre A ++ [e]))).2 =
      updS (cfgOfV pstep pdone img M n z pre).2 A (z'.2.1, z'.2.2, prjT (pre A) ++ prjT [e]) := by
  funext k
  by_cases hk : k = A
  · subst hk; simp [updS, cfgOfV, OA.fupd, hA, prjT_append]
  · simp only [updS, if_neg hk, cfgOfV, OA.fupd]

/-- A v2-label thread step, stated at hart index `A` and its component `x`. -/
theorem cstepV_lab' {w : HWV P Unit V} {A : Nat} (hA : w.h = A) {s : P} {σ : CSt} {x : HSt} (hx : σ A = x)
    {l : PLabel} {ots : Option Nat} {s' : P} {ws' : PState} {pr' : GSet Nat}
    (hp : w.pstep s () (.v l) s' ()) (hm : Ad.memStepV w.img w.M A x.2.1 x.1 (.v l) ots ws' pr')
    (hok : fOkV w.M (updS σ A (ws', pr', x.2.2 ++ [(l, ots)])) A) :
    cstepV (.run w s, σ) [] (.run w s', updS σ A (ws', pr', x.2.2 ++ prjT [(.v l, ots)]), []) := by
  subst hA; subst hx; exact .lab w s σ l ots s' ws' pr' () () hp hm hok

/-- An A/D thread step, stated at hart index `A` and its component `x`. -/
theorem cstepV_ad' {w : HWV P Unit V} {A : Nat} (hA : w.h = A) {s : P} {σ : CSt} {x : HSt} (hx : σ A = x)
    {b : Int} {tvs : List (Nat × BitVec 8)} {d : List (BitVec 8)} {ots : Option Nat} {s' : P} {pr' : GSet Nat}
    (hp : w.pstep s () (.ad b tvs d) s' ()) (hm : Ad.memStepV w.img w.M A x.2.1 x.1 (.ad b tvs d) ots x.1 pr') :
    cstepV (.run w s, σ) [] (.run w s', updS σ A (x.1, pr', x.2.2 ++ prjT [(.ad b tvs d, ots)]), []) := by
  subst hA; subst hx
  have := cstepV.ad w s σ b tvs d ots s' pr' () () hp hm
  simpa [prjT] using this

/-- **THE SCHEDULE LEMMA over the variant, main induction** (plan §3 rev 5). -/
theorem sched_mainV (n : Nat) (y : Nat → P × PState × GSet Nat) (tr : Nat → List (Ad.VLabel × Option Nat))
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t → ∃ h, h < n ∧ ∃ l, (Ad.VLabel.v l, some t) ∈ tr h) :
    ∀ m (z : Nat → P × PState × GSet Nat) (pre rest : Nat → List (Ad.VLabel × Option Nat)), msrV n rest = m →
      (∀ h, h < n → Ad.soloQV pstep img M h Ad.QTV (z h) (rest h) (y h)) →
      (∀ h, h < n → pre h ++ rest h = tr h) →
      ∃ k, NSteps k (cfgOfV pstep pdone img M n z pre) [] (cfgOfV pstep pdone img M n y tr) := by
  intro m
  induction m with
  | zero =>
    intro z pre rest hm hs hpre
    refine ⟨0, ?_⟩
    have hr := msrV_zero hm
    have hz : ∀ h, h < n → z h = y h := fun h hh => soloQV_nil (by rw [← hr h hh]; exact hs h hh)
    have hp : ∀ h, h < n → pre h = tr h := fun h hh => by rw [← hpre h hh, hr h hh, List.append_nil]
    have : cfgOfV pstep pdone img M n z pre = cfgOfV pstep pdone img M n y tr := by
      unfold cfgOfV
      congr 1
      · exact List.map_congr_left (fun k hk => by rw [hz k (List.mem_range.1 hk)])
      · funext k
        by_cases hk : k < n
        · simp [hk, hz k hk, hp k hk]
        · simp [hk]
    rw [this]; exact .refl _
  | succ m ih =>
    intro z pre rest hm hs hpre
    have hσ : ∀ h, h < n → (cfgOfV pstep pdone img M n z pre).2 h = ((z h).2.1, (z h).2.2, prjT (pre h)) := by
      intro h hh; simp [cfgOfV, hh]
    -- choose the hart to step: the author of the least unfulfilled NON-A/D timestamp, or any hart
    have hchoose : ∃ A, A < n ∧ rest A ≠ [] ∧
        ((∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t → fulAt (cfgOfV pstep pdone img M n z pre).2 t) ∨
         ∃ i, 1 ≤ i ∧ i ≤ M.length ∧ ¬ Ad.adAt M i ∧
           (∀ t, 1 ≤ t → t < i → ¬ Ad.adAt M t → fulAt (cfgOfV pstep pdone img M n z pre).2 t) ∧
           ∃ l, (Ad.VLabel.v l, some i) ∈ rest A) := by
      by_cases hall : ∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t → fulAt (cfgOfV pstep pdone img M n z pre).2 t
      · obtain ⟨A, hA, hne⟩ := msrV_pos hm
        exact ⟨A, hA, hne, .inl hall⟩
      · have hex : ∃ t, 1 ≤ t ∧ t ≤ M.length ∧ ¬ Ad.adAt M t ∧ ¬ fulAt (cfgOfV pstep pdone img M n z pre).2 t := by
          apply Classical.byContradiction; intro hno
          exact hall (fun t h1 h2 h3 => Classical.byContradiction (fun hn => hno ⟨t, h1, h2, h3, hn⟩))
        obtain ⟨i, ⟨hi1, hi2, hia, hin⟩, hleast⟩ := exists_least hex
        obtain ⟨A, hA, l, he⟩ := hpart i hi1 hi2 hia
        have hnotpre : (Ad.VLabel.v l, some i) ∉ pre A := fun hep =>
          hin ⟨A, (l, some i), by rw [hσ A hA]; exact prjT_mem hep, rfl⟩
        rw [← hpre A hA] at he
        have her : (Ad.VLabel.v l, some i) ∈ rest A := by
          rcases List.mem_append.1 he with h | h
          · exact absurd h hnotpre
          · exact h
        refine ⟨A, hA, (fun h => by rw [h] at her; cases her), .inr ⟨i, hi1, hi2, hia, fun t h1 h2 h3 => ?_, l, her⟩⟩
        exact Classical.byContradiction (fun hn => hleast t h2 ⟨h1, by omega, h3, hn⟩)
    obtain ⟨A, hA, hne, hcase⟩ := hchoose
    obtain ⟨⟨lab, ots⟩, rest', hra⟩ : ∃ e r, rest A = e :: r := by
      cases h : rest A with
      | nil => exact absurd h hne
      | cons e r => exact ⟨e, r, rfl⟩
    have hsA := hs A hA
    rw [hra] at hsA
    have hσA := hσ A hA
    cases hsA with
    | step _ _ _ p' ws' prom' _ _ _ hp hmem hrest =>
      -- the step and the measure
      have hm' : msrV n (OA.fupd rest A rest') = m := by
        have := msrV_fupd rest A rest' n hA
        rw [hra] at this; simp only [List.length_cons] at this; omega
      have hS : Language.Step (cfgOfV pstep pdone img M n z pre) []
          (cfgOfV pstep pdone img M n (OA.fupd z A (p', ws', prom')) (OA.fupd pre A (pre A ++ [(lab, ots)]))) := by
        apply cfg_stepV hA
        rw [cfgOfV_upd hA]
        cases lab with
        | v l =>
          -- THE FRONTIER CLAIM after a v2-label step
          have hok : fOkV M (updS (cfgOfV pstep pdone img M n z pre).2 A (ws', prom', prjT (pre A) ++ [(l, ots)])) A := by
            unfold fOkV
            rw [updS_self]
            intro t h1 h2 h3 hna
            have hlift : ∀ t, fulAt (cfgOfV pstep pdone img M n z pre).2 t →
                fulAt (updS (cfgOfV pstep pdone img M n z pre).2 A (ws', prom', prjT (pre A) ++ [(l, ots)])) t := by
              intro t ht
              have := fulAt_updS (σ := (cfgOfV pstep pdone img M n z pre).2) (h := A) (ws' := ws') (pr' := prom')
                (e := (l, ots)) ht
              rw [hσA] at this; exact this
            rcases hcase with hall | ⟨i, hi1, hi2, hia, hlt, l0, he⟩
            · exact hlift t (hall t h1 h2 hna)
            · simp only [wfr] at h3
              rcases List.mem_cons.1 (hra ▸ he) with e0 | he'
              · -- this step is the fulfil of `i`
                simp only [Prod.mk.injEq, Ad.VLabel.v.injEq] at e0
                obtain ⟨hl0, hots⟩ := e0
                subst hl0 hots
                have hfl := post_floor_le (memStepV_v_some hmem)
                by_cases hti : t < i
                · exact hlift t (hlt t h1 hti hna)
                · have : t = i := by omega
                  subst this
                  exact ⟨A, (l0, some t), by
                    rw [updS_self]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
              · have hfl := solo_floorV hrest l0 i he'
                exact hlift t (hlt t h1 (by simp only at hfl; omega) hna)
          exact cstepV_lab' (w := hwV pstep pdone img M A) (A := A) rfl hσA hp hmem hok
        | ad b tvs d =>
          obtain ⟨ts, _, hws, _⟩ := Ad.memStepV_ad_inv hmem
          subst hws
          exact cstepV_ad' (w := hwV pstep pdone img M A) (A := A) rfl hσA hp hmem
      obtain ⟨k, hk⟩ := ih (OA.fupd z A (p', ws', prom')) (OA.fupd pre A (pre A ++ [(lab, ots)])) (OA.fupd rest A rest') hm'
        (fun h hh => by
          by_cases hhA : h = A
          · subst hhA; simp only [OA.fupd, if_true]; exact hrest
          · simp only [OA.fupd, if_neg hhA]; exact hs h hh)
        (fun h hh => by
          by_cases hhA : h = A
          · subst hhA; simp only [OA.fupd, if_true]; rw [← hpre h hh, hra]; simp
          · simp only [OA.fupd, if_neg hhA]; exact hpre h hh)
      exact ⟨k + 1, by simpa using NSteps.cons hS hk⟩

/-- **THE SCHEDULE LEMMA over the A/D variant** (plan §3 rev 5): every hart's solo run against `M` plus the
non-A/D partition give an execution of the guarded language from every hart's initial state to its final state. -/
theorem schedV (n : Nat) (x y : Nat → P × PState × GSet Nat) (tr : Nat → List (Ad.VLabel × Option Nat))
    (hs : ∀ h, h < n → Ad.soloQV pstep img M h Ad.QTV (x h) (tr h) (y h))
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → ¬ Ad.adAt M t → ∃ h, h < n ∧ ∃ l, (Ad.VLabel.v l, some t) ∈ tr h) :
    ∃ k, NSteps k (cfgOfV pstep pdone img M n x (fun _ => [])) [] (cfgOfV pstep pdone img M n y tr) :=
  sched_mainV n y tr hpart _ x (fun _ => []) tr rfl hs (fun _ _ => List.nil_append _)

end sched

end Weak.Prom.OAd
