/-
Weak/Prom: **hart separation for machine v2** (S0-P part (2), milestone 2b, statement 2).

After the promise phase of the promises-first normal form (MachFactor.lean) the log is the final memory `M` and no
step changes it, and a state step of agent `i` reads only the log and `i`'s own state.  So each hart's events form
a SOLO RUN against `M` (`soloSteps`: the program half and `memStep` against `M`, one hart), from its initial
program state, `psInit` and the promise set "every own message of `M`", to its final agent state.

* `sep` — a run of state events projects to every hart's solo run (the direction the explorer's completeness uses).
* `validRun_solo` — every valid run (with no device fabric, `D = Unit`) gives, for every hart `h`, a solo run of
  `h` against the final log from `(ps[h], psInit, own messages)` to the final agent, with trace `traceOf h evs`.
* `solo_fulfil` — a promise that is gone at the end of a solo run was fulfilled by one of its steps.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachFactor

namespace Weak.Prom

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open PLabel

section solo

variable {P : Type} (pstep : P → Unit → PLabel → P → Unit → Prop) (img : Image) (M : List PMsg) (i : Nat)

/-- A SOLO RUN of agent `i` against the fixed memory `M`: program state, `PState`, promise set; labelled by the
trace (label, fulfil timestamp). -/
inductive soloSteps : P × PState × GSet Nat → List (PLabel × Option Nat) → P × PState × GSet Nat → Prop
  | refl (x : P × PState × GSet Nat) : soloSteps x [] x
  | step (x : P × PState × GSet Nat) (l : PLabel) (ots : Option Nat) (p' : P) (ws' : PState) (prom' : GSet Nat)
      (tr : List (PLabel × Option Nat)) (y : P × PState × GSet Nat) :
      pstep x.1 () l p' () → memStep img M i x.2.2 x.2.1 l ots ws' prom' →
      soloSteps (p', ws', prom') tr y → soloSteps x ((l, ots) :: tr) y

end solo

/-- HART SEPARATION: a run of state events against the fixed log `M` projects to each hart's solo run. -/
theorem sep {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {M : List PMsg} :
    ∀ {c c'' : PCfg P Unit} {sts : List PEvt}, pmSteps pstep c sts c'' → (∀ e ∈ sts, e.isSt = true) →
      c.pcLog = M → ∀ h ag, c.pcAgs[h]? = some ag → ∃ ag'', c''.pcAgs[h]? = some ag'' ∧
        soloSteps pstep c.pcImg M h (ag.paSt, ag.paWs, ag.paProm) (traceOf h sts)
          (ag''.paSt, ag''.paWs, ag''.paProm) := by
  intro c c'' sts hrun
  induction hrun with
  | refl => intro _ _ h ag hag; exact ⟨ag, hag, .refl _⟩
  | step c0 c1 c2 e es hst hrest ih =>
    intro hst' hM h ag hag
    cases hst with
    | promise => exact absurd (hst' _ (List.mem_cons_self ..)) (by simp [PEvt.isSt])
    | state i ag0 l ots st' d' ws' prom' hag0 hp hm =>
      have hst1 : ∀ e ∈ es, e.isSt = true := fun e he => hst' e (List.mem_cons_of_mem _ he)
      by_cases hih : i = h
      · subst hih
        rw [hag] at hag0
        cases hag0
        obtain ⟨ag'', h1, h2⟩ := ih hst1 hM i ⟨st', ws', prom'⟩ (getElem?_set_eq_of hag)
        refine ⟨ag'', h1, ?_⟩
        simp only [traceOf, if_true]
        cases d'
        exact .step _ l ots st' ws' prom' _ _ hp (hM ▸ hm) h2
      · obtain ⟨ag'', h1, h2⟩ := ih hst1 hM h ag (by simp only [List.getElem?_set_ne hih]; exact hag)
        refine ⟨ag'', h1, ?_⟩
        simp only [traceOf, if_neg hih]
        exact h2

/-- The STATE PHASE of the promises-first normal form: from the configuration after all promises (log = the final
memory, each agent at its initial program state, `psInit`, every own message promised), the state events reach
the final configuration. -/
theorem validRun_statePhase {P D : Type} {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D}
    {ps : List P} {evs : List PEvt} {cfg : PCfg P D} (h : validRun pstep img d0 ps evs cfg) :
    ∃ c0 : PCfg P D, c0.pcImg = img ∧ c0.pcLog = cfg.pcLog ∧ c0.pcDev = d0 ∧
      (∀ i p, ps[i]? = some p → ∃ ag, c0.pcAgs[i]? = some ag ∧ ag.paSt = p ∧ ag.paWs = psInit ∧
        ∀ t, t ∈ ag.paProm ↔ 0 < t ∧ ownTs cfg.pcLog i t) ∧
      pmSteps pstep c0 (evs.filter PEvt.isSt) cfg := by
  obtain ⟨hrun, hno⟩ := h
  have hwf := pmSteps_wf hrun (pmInit_wf img d0 ps)
  have hlen := pmSteps_len hrun
  obtain ⟨c0', hp, himg, hlog, hdev, hlen', hags⟩ := promsRun (pstep := pstep) cfg.pcLog
    (pmInit img d0 ps) (fun m hm => by rw [← hlen]; exact hwf.2 m hm)
  have hfr : FRel cfg.pcLog (pmInit img d0 ps) c0' := by
    refine ⟨himg, by rw [hlog]; rfl, hdev, List.nil_prefix, hlen', fun i ag hi => ?_⟩
    obtain ⟨ag', h1, h2, h3, h4⟩ := hags i ag hi
    exact ⟨ag', h1, h2, h3, fun t => by rw [h4 t]; rfl⟩
  obtain ⟨c'', hs, hfr''⟩ := sim hrun (pmInit_wf img d0 ps) rfl hfr
  have he := FRel_final hfr'' rfl
  subst he
  refine ⟨c0', himg, by rw [hlog]; rfl, hdev, fun i p hpi => ?_, hs⟩
  have hi : (pmInit img d0 ps).pcAgs[i]? = some ⟨p, psInit, ∅⟩ := by
    simp only [pmInit, List.getElem?_map, hpi, Option.map_some]
  obtain ⟨ag', h1, h2, h3, h4⟩ := hags i _ hi
  refine ⟨ag', h1, h2, h3, fun t => ?_⟩
  rw [h4 t]
  simp only [pmInit, List.length_nil, List.nil_append]
  constructor
  · rintro (h | h)
    · exact absurd h notElemOfEmpty
    · exact h
  · exact .inr

theorem filter_isSt (evs : List PEvt) : ∀ e ∈ evs.filter PEvt.isSt, e.isSt = true := by
  intro e he
  exact (List.mem_filter.1 he).2

/-- EVERY VALID RUN SEPARATES (statement 2, the direction the explorer uses): each hart `h` has a solo run against
the final log, from `(ps[h], psInit, own messages)`, with the run's trace of `h`, to its final agent state. -/
theorem validRun_solo {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P Unit} (h : validRun pstep img () ps evs cfg) :
    ∀ hh p, ps[hh]? = some p → ∃ ag, cfg.pcAgs[hh]? = some ag ∧ ∃ P0 : GSet Nat,
      (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs cfg.pcLog hh t) ∧
      soloSteps pstep img cfg.pcLog hh (p, psInit, P0) (traceOf hh evs) (ag.paSt, ag.paWs, ag.paProm) := by
  intro hh p hp
  obtain ⟨c0, himg, hlog, _, hags, hs⟩ := validRun_statePhase h
  obtain ⟨ag0, h1, h2, h3, h4⟩ := hags hh p hp
  obtain ⟨ag'', k1, k2⟩ := sep hs (filter_isSt evs) hlog hh ag0 h1
  refine ⟨ag'', k1, ag0.paProm, h4, ?_⟩
  rw [himg, h2, h3, traceOf_filter] at k2
  exact k2

/-! ## Promise bookkeeping along a solo run -/

/-- A state step's promise set is unchanged, or loses exactly its fulfil timestamp. -/
theorem memStep_prom {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l ots ws' prom') :
    (ots = none ∧ prom' = prom) ∨ (∃ ts, ots = some ts ∧ ts ∈ prom ∧ prom' = prom \ {ts}) := by
  cases h with
  | store _ _ _ _ _ _ ts hts => exact .inr ⟨ts, rfl, hts, rfl⟩
  | rmw _ _ _ _ _ _ _ ts _ hts => exact .inr ⟨ts, rfl, hts, rfl⟩
  | amoSt _ _ _ _ _ ts _ _ _ _ hts => exact .inr ⟨ts, rfl, hts, rfl⟩
  | sc _ _ _ _ _ _ ts _ _ hts => exact .inr ⟨ts, rfl, hts, rfl⟩
  | cmo _ _ _ _ ts hts => exact .inr ⟨ts, rfl, hts, rfl⟩
  | _ => exact .inl ⟨rfl, rfl⟩

/-- A FULFILLED PROMISE has its step: if `θ` is promised at the start of a solo run and not at the end, some step
of the run fulfils `θ`. -/
theorem solo_fulfil {P : Type} {pstep : P → Unit → PLabel → P → Unit → Prop} {img : Image} {M : List PMsg}
    {i : Nat} {θ : Nat} : ∀ {x y : P × PState × GSet Nat} {tr : List (PLabel × Option Nat)},
      soloSteps pstep img M i x tr y → θ ∈ x.2.2 → θ ∉ y.2.2 →
      ∃ (z : P × PState × GSet Nat) (tr1 : List (PLabel × Option Nat)) (l : PLabel) (p' : P) (ws' : PState)
        (prom' : GSet Nat), soloSteps pstep img M i x tr1 z ∧ pstep z.1 () l p' () ∧
        memStep img M i z.2.2 z.2.1 l (some θ) ws' prom' := by
  intro x y tr h
  induction h with
  | refl => intro h1 h2; exact absurd h1 h2
  | step x l ots p' ws' prom' tr y hp hm hrest ih =>
    intro h1 h2
    rcases memStep_prom hm with ⟨_, he⟩ | ⟨ts, hts, _, he⟩
    · subst he
      obtain ⟨z, tr1, l', p'', ws'', prom'', k1, k2, k3⟩ := ih h1 h2
      exact ⟨z, (l, ots) :: tr1, l', p'', ws'', prom'', .step _ _ _ _ _ _ _ _ hp hm k1, k2, k3⟩
    · by_cases e : θ = ts
      · subst e hts
        exact ⟨x, [], l, p', ws', prom', .refl _, hp, hm⟩
      · have : θ ∈ prom' := by rw [he]; exact elemOfDifference.2 ⟨h1, by rw [elemOfSingleton]; exact e⟩
        obtain ⟨z, tr1, l', p'', ws'', prom'', k1, k2, k3⟩ := ih this h2
        exact ⟨z, (l, ots) :: tr1, l', p'', ws'', prom'', .step _ _ _ _ _ _ _ _ hp hm k1, k2, k3⟩

end Weak.Prom
