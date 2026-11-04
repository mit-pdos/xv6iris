/-
Weak/Prom: **HAVOC — the run-level semantics of a remaining Sail `.error` site** (FIX MachFix-havoc, 2026-11-04;
owner rulings [OWN.P8] "fix every reachable Sail `.error` site faithfully; any site left afterwards is HAVOC: after
`.error` the machine may do anything (WEAKER, sound)" and [OWN.P9] Havoc = "Global — once any hart reaches a
remaining Sail error site, the run may produce any outcome"; context.md items 15–16; HavocProm 2026-11-04:
[OWN.P10], item 17, a run reaching an error with the erroring hart's own promise outstanding is havoc too).

Machine v2 is parametric in the program half `pstep`; an ERROR NODE is a program state satisfying a predicate
`perr` (for the Sail instance, `Emit.lean`'s residual computation `.impure (.error _) _`: `sailErr`,
EmitHavoc.lean).  The program half has no step out of an error node (Emit.lean's `.error` arm is `False`), so a
hart that reaches one stays there (`errCfg_persist`, given `errStable`): "a run reaches an error" is the same as
"its final configuration has a hart at an error node".

* `havocRun` — (HavocProm, [OWN.P10]) a run from `pmInit` whose final configuration has a hart at an error node
  and whose OUTSTANDING PROMISES all belong to harts at error nodes (`promsAtErr`); `havocs` — some havoc run
  exists.  Every valid run reaching an error is one (`havocRun_of_valid`, the MachFix-havoc notion); so is a run
  in which a hart reaches an error while one of ITS OWN promises is still outstanding ([OWN.P10], context.md
  item 17: "also counts as havoc (any outcome) — WEAKER, sound").  Promises of a hart NOT at an error node must
  be fulfilled, as in a valid run: the ruling covers the erroring hart's own promises only, and the machine's
  promise step is unconditional, so a run ending with a never-fulfilled promise of a live hart is not a run of
  the program (it would make every program whose error branch depends on a read value havoc).
* `allowedH O` — THE OBSERVATIONS UNDER HAVOC: an outcome predicate `O` on final configurations is allowed iff some
  valid run's final configuration satisfies it, OR some havoc run exists (then EVERY observation is possible:
  `allowedH_of_havocs`).  The "outcome constraints" of `validRun` are void after a havoc run.
* `forbiddenH_iff` — `O` is FORBIDDEN under havoc iff no valid run satisfies it AND no havoc run exists (none of
  the runs above, outstanding own promises included): a "forbidden" verdict needs both (the second is what the
  logic proves by showing every error node unreachable, CoreHavocP.lean `noHavoc_of_adequacyHP`; the Sail-level
  explorer reports `HAVOC` and never a forbidden verdict when it finds a havoc run, MachSail.lean).
* `noErr_noHavoc` — a program half with no error node (every litmus front end: `perr := fun _ => False`) has no
  havoc run, so its outcome sets are unchanged.
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

/-- HavocProm: every outstanding promise belongs to an agent at an error node. -/
def promsAtErr (cfg : PCfg P D) : Prop :=
  ∀ (i : Nat) (ag : PAgent P) (t : Nat), cfg.pcAgs[i]? = some ag → t ∈ ag.paProm → perr ag.paSt

/-- A HAVOC RUN (HavocProm, [OWN.P10]): a run from the initial configuration that reaches an error node (at its
end; errors persist, `errCfg_persist`), whose outstanding promises all belong to harts at error nodes. -/
def havocRun (img : Image) (d0 : D) (ps : List P) (evs : List PEvt) (cfg : PCfg P D) : Prop :=
  pmSteps pstep (pmInit img d0 ps) evs cfg ∧ promsAtErr perr cfg ∧ errCfg perr cfg

/-- Some havoc run exists. -/
def havocs (img : Image) (d0 : D) (ps : List P) : Prop :=
  ∃ evs cfg, havocRun pstep perr img d0 ps evs cfg

/-- THE OBSERVATIONS UNDER HAVOC ([OWN.P9] "Global", [OWN.P10]): `O` is allowed iff a valid run satisfies it, or
a havoc run exists (then every observation is possible). -/
def allowedH (img : Image) (d0 : D) (ps : List P) (O : PCfg P D → Prop) : Prop :=
  (∃ evs cfg, validRun pstep img d0 ps evs cfg ∧ O cfg) ∨ havocs pstep perr img d0 ps

/-- The program half never leaves an error node. -/
def errStable : Prop := ∀ s d l s' d', perr s → pstep s d l s' d' → perr s'

variable {pstep perr}

/-- After a havoc run, every observation is allowed. -/
theorem allowedH_of_havocs {img : Image} {d0 : D} {ps : List P} (h : havocs pstep perr img d0 ps)
    (O : PCfg P D → Prop) : allowedH pstep perr img d0 ps O := .inr h

/-- A FORBIDDEN verdict under havoc: no valid run satisfies `O`, and no havoc run exists. -/
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
  rintro ⟨_, _, _, _, _, ag, _, he⟩
  exact h _ he

/-- No havoc run ⇒ `allowedH` is plain reachability. -/
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

theorem promsAtErr_of_noPromises {cfg : PCfg P D} (h : noPromises cfg) : promsAtErr perr cfg := by
  intro i ag t hag ht
  rw [h i ag hag] at ht
  exact absurd ht notElemOfEmpty

/-- Every valid run reaching an error node is a havoc run (the MachFix-havoc notion). -/
theorem havocRun_of_valid {img : Image} {d0 : D} {ps : List P} {evs : List PEvt} {cfg : PCfg P D}
    (hv : validRun pstep img d0 ps evs cfg) (he : errCfg perr cfg) : havocRun pstep perr img d0 ps evs cfg :=
  ⟨hv.1, promsAtErr_of_noPromises hv.2, he⟩

/-- A valid run that passes through a configuration with a hart at an error node is a havoc run. -/
theorem havocRun_of_prefix (hst : errStable pstep perr) {img : Image} {d0 : D} {ps : List P}
    {evs1 evs2 : List PEvt} {c cfg : PCfg P D} (h1 : pmSteps pstep (pmInit img d0 ps) evs1 c)
    (he : errCfg perr c) (h2 : pmSteps pstep c evs2 cfg) (hno : noPromises cfg) :
    havocRun pstep perr img d0 ps (evs1 ++ evs2) cfg :=
  ⟨pmSteps_append h1 h2, promsAtErr_of_noPromises hno, errCfg_persist hst h2 he⟩

/-- HavocProm: a run that passes through an error node and ends with every outstanding promise at an error node
(e.g. the erroring hart's own) is a havoc run. -/
theorem havocRun_of_prefixE (hst : errStable pstep perr) {img : Image} {d0 : D} {ps : List P}
    {evs1 evs2 : List PEvt} {c cfg : PCfg P D} (h1 : pmSteps pstep (pmInit img d0 ps) evs1 c)
    (he : errCfg perr c) (h2 : pmSteps pstep c evs2 cfg) (hpa : promsAtErr perr cfg) :
    havocRun pstep perr img d0 ps (evs1 ++ evs2) cfg :=
  ⟨pmSteps_append h1 h2, hpa, errCfg_persist hst h2 he⟩

end havoc

end Weak.Prom
