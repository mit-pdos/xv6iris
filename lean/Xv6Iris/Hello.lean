/-
Smoke test: confirms the iris-lean dependency resolves and the MoSeL proof
mode + BI logic are usable in this project. This de-risks the toolchain and
dependency integration before any RISC-V-specific work; it has nothing to do
with the model and should stay tiny.

Note: iris-lean uses Lean's module system (`module` / `public import` /
`@[expose] public section`), which downstream files must mirror.
-/
module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Xv6Iris

open Iris Iris.BI

/-- A trivial separation-logic entailment, proved with the MoSeL proof mode,
just to confirm `iintro`/`iframe` are wired up against the iris-lean BI. -/
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ Q ∗ P := by
  iintro ⟨HP, HQ⟩
  iframe

end Xv6Iris
