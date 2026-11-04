/-
Weak/Prom: **the Sail instance's error nodes and havoc** (FIX MachFix-havoc, 2026-11-04; [OWN.P8], [OWN.P9];
MachHavoc.lean for the run-level semantics).

`sailErr h` — the hart's residual Sail computation is an `.error` outcome (Emit.lean `hnodeStep`'s `.error` arm,
reached from a REMAINING Sail error site, the "b after c" of [OWN.P8]).  Emission v2 has no step out of it
(`sailErr_stable`: the arm is `False`; the parked FENCE.TSO half is still applied and keeps the error), so every
valid run of `pstepV2` that reaches one is a havoc run (MachHavoc.lean `havocRun_of_prefix`) and makes every
observation possible (`allowedH_of_havocs`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.Emit
import Weak.Prom.MachHavoc

namespace Weak.Prom

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image)
open Sail Sail.ConcurrencyInterfaceV1

/-- The hart is at a Sail `.error` node. -/
def sailErr (h : HState) : Prop := ∃ e k, h.m = .impure (.error e) k

/-- Emission v2 never leaves an error node. -/
theorem sailErr_stable : errStable pstepV2 sailErr := by
  intro h d l h' d' ⟨e, k, hm⟩ ⟨_, hs⟩
  unfold hstep at hs
  split at hs
  · obtain ⟨_, _, rfl⟩ := hs; exact ⟨e, k, hm⟩
  · simp only [hnodeStep, hm] at hs

/-- THE SAIL INSTANCE UNDER HAVOC: an outcome predicate is allowed iff a valid run satisfies it or a valid run
reaches a Sail error. -/
abbrev allowedSail (img : Image) (d0 : DevStates) (ps : List HState) (O : PCfg HState DevStates → Prop) : Prop :=
  allowedH pstepV2 sailErr img d0 ps O

end Weak.Prom
