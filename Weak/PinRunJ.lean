/-
Weak: **W11-F [OWN.102], A13 (a) increment 1 — HART RUNS WITH FABRIC JUMPS** (`PROGRESS-W11F.md` §2
A13; coordinator's provisional decision (a)).  Lean-only, no Rocq twin.

The published bundle (`xv6ConfS` / `GraphFabConf.gfexecConfZF`) gives each row a `hartConff`
emission: item `k` runs from the fabric `dvi k` to `dvo k`, and OTHER agents (devices, other harts'
I/O) move the fabric between the hart's items, so `dvo k ≠ dvi (k + 1)` in general.  The B5 pin chain
was stated over `hartConf` (one threaded fabric).  This file is the run vocabulary for the restatement:

* `prunJ ls p d p' d'` — a run of the hart's labels `ls` where, besides `pstepEv` steps (`more`, the
  constructor shape of `pevrun`), the fabric may JUMP (`jump`) to any value between steps.
  `prunJOfPevrun`, `prunJApp`, `prunJSplit`, `prunJNil`.
* (in `Weak/PinConfF.lean`) `hemitfPrunJ` / `hartConffPrunJ` — a `hemitf` emission is a jump run of
  its labels from ANY start fabric; `hemitfFeNone` / `hartConffFeNone`.

Spec: FAITHFUL — the hart's view of the shared device fabric is exactly "whatever the other agents
left"; a jump run is what a realized row is (no constraint dropped from Sail's hart step).
Every name is file-qualified (`PinRunJ.*`) except `prunJ` (grepped: new).
-/
import Weak.WeakEvProv

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Wlabel

/-- **A HART RUN WITH FABRIC JUMPS**: `pevrun`'s steps, and a free fabric change between steps. -/
inductive prunJ : List Wlabel → Pexv6 → Efab → Pexv6 → Efab → Prop where
  | nil (p : Pexv6) (d : Efab) : prunJ [] p d p d
  | more {l : Wlabel} {ls : List Wlabel} {p : Pexv6} {d : Efab} {p1 : Pexv6}
      {d1 : Efab} {p2 : Pexv6} {d2 : Efab} :
      pstepEv p d l p1 d1 → prunJ ls p1 d1 p2 d2 → prunJ (l :: ls) p d p2 d2
  | jump {ls : List Wlabel} {p : Pexv6} {d e : Efab} {p2 : Pexv6} {d2 : Efab} :
      prunJ ls p e p2 d2 → prunJ ls p d p2 d2

theorem PinRunJ.prunJOfPevrun {ls : List Wlabel} {p : Pexv6} {d : Efab} {p' : Pexv6} {d' : Efab}
    (h : pevrun ls p d p' d') : prunJ ls p d p' d' := by
  induction h with
  | nil p d => exact .nil p d
  | more hs _ ih => exact .more hs ih

theorem PinRunJ.prunJApp {l1 l2 : List Wlabel} {p : Pexv6} {d : Efab} {p1 : Pexv6} {d1 : Efab}
    {p2 : Pexv6} {d2 : Efab} :
    prunJ l1 p d p1 d1 → prunJ l2 p1 d1 p2 d2 → prunJ (l1 ++ l2) p d p2 d2 := by
  intro h1 h2
  induction h1 with
  | nil => exact h2
  | more hs _ ih => exact .more hs (ih h2)
  | jump _ ih => exact .jump (ih h2)

theorem PinRunJ.prunJSplit (l1 l2 : List Wlabel) :
    ∀ {ls : List Wlabel} {p : Pexv6} {d : Efab} {p2 : Pexv6} {d2 : Efab}, prunJ ls p d p2 d2 →
      ls = l1 ++ l2 → ∃ p1 d1, prunJ l1 p d p1 d1 ∧ prunJ l2 p1 d1 p2 d2 := by
  intro ls p d p2 d2 h
  induction h generalizing l1 with
  | nil p d =>
    intro e
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 e.symm
    exact ⟨p, d, .nil p d, .nil p d⟩
  | @more l ls p d p1 d1 p2 d2 hs hr ih =>
    intro e
    cases l1 with
    | nil =>
      simp only [List.nil_append] at e
      exact ⟨p, d, .nil p d, e ▸ prunJ.more hs hr⟩
    | cons a l1 =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      obtain ⟨q, dq, h1, h2⟩ := ih l1 e
      exact ⟨q, dq, .more hs h1, h2⟩
  | @jump ls p d e p2 d2 hr ih =>
    intro he
    obtain ⟨q, dq, h1, h2⟩ := ih l1 he
    exact ⟨q, dq, .jump h1, h2⟩

theorem PinRunJ.prunJNil {p : Pexv6} {d : Efab} {p' : Pexv6} {d' : Efab} :
    prunJ [] p d p' d' → p' = p := by
  intro h
  generalize e : ([] : List Wlabel) = ls at h
  induction h with
  | nil => rfl
  | more _ _ _ => cases e
  | jump _ ih => exact ih e

end Weak
