/-
Weak/Prom: **HAVOC — the run-level semantics of a remaining Sail `.error` site** (FIX MachFix-havoc, 2026-11-04;
owner rulings [OWN.P8] "fix every reachable Sail `.error` site faithfully; any site left afterwards is HAVOC: after
`.error` the machine may do anything (WEAKER, sound)" and [OWN.P9] Havoc = "Global — once any hart reaches a
remaining Sail error site, the run may produce any outcome"; context.md items 15–16).

Machine v2 is parametric in the program half `pstep`; an ERROR NODE is a program state satisfying a predicate
`perr` (for the Sail instance, `Emit.lean`'s residual computation `.impure (.error _) _`: `sailErr`,
EmitHavoc.lean).  The program half has no step out of an error node (Emit.lean's `.error` arm is `False`), so a
hart that reaches one stays there (`errCfg_persist`, given `errStable`): "a run reaches an error" is the same as
"its final configuration has a hart at an error node".

* `havocRun` — a VALID run (machine.lean `validRun`: from `pmInit`, no promise outstanding at its end) whose final
  configuration has a hart at an error node; `havocs` — some havoc run exists.
* `allowedH O` — THE OBSERVATIONS UNDER HAVOC: an outcome predicate `O` on final configurations is allowed iff some
  valid run's final configuration satisfies it, OR some valid run reaches an error (then EVERY observation is
  possible: `allowedH_of_havocs`).  The "outcome constraints" of `validRun` are void after a havoc run.
* `forbiddenH_iff` — `O` is FORBIDDEN under havoc iff no valid run satisfies it AND no valid run reaches an error:
  a "forbidden" verdict needs both (the second is what the logic proves by showing every error node unreachable,
  CoreHavoc.lean `adequacyH`; the Sail-level explorer reports `HAVOC` and never a forbidden verdict when it finds a
  havoc run, MachSail.lean).
* `noErr_noHavoc` — a program half with no error node (every litmus front end: `perr := fun _ => False`) has no
  havoc run, so its outcome sets are unchanged.
Fidelity note (HAVOC-PROM): the erroring hart is stuck, so a run in which a hart reaches an error while one of ITS
OWN promises is still outstanding is not valid and is not counted (the brief's "a valid run reaching a Sail
error"); under [OWN.P8]'s "may do anything" that hart could still fulfil it — recorded in PROGRESS-MachFix.md as an
owner question.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachFactor   -- `pmSteps_append`

namespace Weak.Prom

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)

section havoc

variable {P D : Type} (pstep : P → D → PLabel → P → D → Prop) (perr : P → Prop)

/-- Some agent of the configuration is at an error node. -/
def errCfg (cfg : PCfg P D) : Prop := ∃ (i : Nat) (ag : PAgent P), cfg.pcAgs[i]? = some ag ∧ perr ag.paSt

/-- A HAVOC RUN: a valid run that reaches an error node (at its end; errors persist, `errCfg_persist`). -/
def havocRun (img : Image) (d0 : D) (ps : List P) (evs : List PEvt) (cfg : PCfg P D) : Prop :=
  validRun pstep img d0 ps evs cfg ∧ errCfg perr cfg

/-- Some valid run reaches an error node. -/
def havocs (img : Image) (d0 : D) (ps : List P) : Prop :=
  ∃ evs cfg, havocRun pstep perr img d0 ps evs cfg

/-- THE OBSERVATIONS UNDER HAVOC ([OWN.P9] "Global"): `O` is allowed iff a valid run satisfies it, or a valid run
reaches an error (then every observation is possible). -/
def allowedH (img : Image) (d0 : D) (ps : List P) (O : PCfg P D → Prop) : Prop :=
  (∃ evs cfg, validRun pstep img d0 ps evs cfg ∧ O cfg) ∨ havocs pstep perr img d0 ps

/-- The program half never leaves an error node. -/
def errStable : Prop := ∀ s d l s' d', perr s → pstep s d l s' d' → perr s'

variable {pstep perr}

/-- After a havoc run, every observation is allowed. -/
theorem allowedH_of_havocs {img : Image} {d0 : D} {ps : List P} (h : havocs pstep perr img d0 ps)
    (O : PCfg P D → Prop) : allowedH pstep perr img d0 ps O := .inr h

/-- A FORBIDDEN verdict under havoc: no valid run satisfies `O`, and no valid run reaches an error. -/
theorem forbiddenH_iff {img : Image} {d0 : D} {ps : List P} {O : PCfg P D → Prop} :
    ¬ allowedH pstep perr img d0 ps O ↔
      (∀ evs cfg, validRun pstep img d0 ps evs cfg → ¬ O cfg) ∧ ¬ havocs pstep perr img d0 ps := by
  unfold allowedH
  constructor
  · intro h
    exact ⟨fun evs cfg hv ho => h (.inl ⟨evs, cfg, hv, ho⟩), fun hh => h (.inr hh)⟩
  · rintro ⟨h1, h2⟩ (⟨evs, cfg, hv, ho⟩ | hh)
    · exact h1 evs cfg hv ho
    · exact h2 hh

/-- No error node, no havoc: the outcome sets are those of the valid runs. -/
theorem noErr_noHavoc {img : Image} {d0 : D} {ps : List P} (h : ∀ s, ¬ perr s) :
    ¬ havocs pstep perr img d0 ps := by
  rintro ⟨_, _, _, _, ag, _, he⟩
  exact h _ he

/-- No valid run reaches an error ⇒ `allowedH` is plain reachability. -/
theorem allowedH_iff_of_noHavoc {img : Image} {d0 : D} {ps : List P} (h : ¬ havocs pstep perr img d0 ps)
    {O : PCfg P D → Prop} :
    allowedH pstep perr img d0 ps O ↔ ∃ evs cfg, validRun pstep img d0 ps evs cfg ∧ O cfg :=
  ⟨fun h' => h'.elim id (fun hh => absurd hh h), .inl⟩

theorem errCfg_step (hst : errStable pstep perr) {c c' : PCfg P D} {e : PEvt} (h : pmStep pstep c e c')
    (he : errCfg perr c) : errCfg perr c' := by
  obtain ⟨j, agj, hj, hpj⟩ := he
  have hlt : j < c.pcAgs.length := (List.getElem?_eq_some_iff.1 hj).1
  cases h with
  | promise i ag m hag _ _ =>
    by_cases hji : j = i
    · subst hji
      rw [hj] at hag; cases hag
      exact ⟨j, ⟨agj.paSt, agj.paWs, {c.pcLog.length + 1} ∪ agj.paProm⟩,
        by simp only [List.getElem?_set_self hlt], hpj⟩
    · exact ⟨j, agj, by simp only [List.getElem?_set_ne (Ne.symm hji)]; exact hj, hpj⟩
  | state i ag l ots st' d' ws' prom' hag hp _ =>
    by_cases hji : j = i
    · subst hji
      rw [hj] at hag; cases hag
      exact ⟨j, ⟨st', ws', prom'⟩, by simp only [List.getElem?_set_self hlt], hst _ _ _ _ _ hpj hp⟩
    · exact ⟨j, agj, by simp only [List.getElem?_set_ne (Ne.symm hji)]; exact hj, hpj⟩

/-- ERRORS PERSIST: once a hart is at an error node it stays there (the program half has no step out of it). -/
theorem errCfg_persist (hst : errStable pstep perr) {c c' : PCfg P D} {evs : List PEvt}
    (h : pmSteps pstep c evs c') (he : errCfg perr c) : errCfg perr c' := by
  induction h with
  | refl => exact he
  | step c0 c1 c2 e es h1 _ ih => exact ih (errCfg_step hst h1 he)

/-- A valid run that passes through a configuration with a hart at an error node is a havoc run. -/
theorem havocRun_of_prefix (hst : errStable pstep perr) {img : Image} {d0 : D} {ps : List P}
    {evs1 evs2 : List PEvt} {c cfg : PCfg P D} (h1 : pmSteps pstep (pmInit img d0 ps) evs1 c)
    (he : errCfg perr c) (h2 : pmSteps pstep c evs2 cfg) (hno : noPromises cfg) :
    havocRun pstep perr img d0 ps (evs1 ++ evs2) cfg :=
  ⟨⟨pmSteps_append h1 h2, hno⟩, errCfg_persist hst h2 he⟩

end havoc

end Weak.Prom
