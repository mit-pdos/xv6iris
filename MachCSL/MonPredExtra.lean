/-
MachCSL: PROOFMODE GAPS of iris-lean's `MonPred` support (`Iris.ProofMode.MonPred`), filled for the
weak-memory port (the MonPred spike, `Weak/WeakView.lean`, `Weak/WeakVProp.lean`;
`notes/weak-port-iris-gaps.md` G8).

THE GAP (measured at iris-lean 728a171).  A hypothesis or goal of the shape
`(iprop(∃ x, Φ x)).monPred_at i` — an existential evaluated at an index, which is what unfolding
any `def`-level `MonPred` with an `∃` body (`Weak.wpt`) and reading it at an index gives — is NOT
destructed by `iintro ⟨%x, …⟩` / `icases` ("is not an existential quantifier") nor introduced by
`iexists` ("cannot turn … into an existential quantifier").  Upstream's `intoExists_monPred_at` /
`fromExists_monPred_at` route the body through `∀ a, MakeMonPredAt .indexToProp i (Φ a) (Ψ a)`,
whose higher-order output `Ψ` the IPM synthesis does not solve (the `∀` twins,
`intoForall_monPred_at`, are marked `ipm_backtrack` and do fire).  The instances below hand the
proofmode the body at the index directly, `fun x => (Φ x).monPred_at i`, which the existing
`IntoSep`/`MakeMonPredAt` instances then take apart.

After `istart` the gap does not arise (`makeMonPredAt_exists` evaluates the `∃` eagerly); it bites
exactly at the iProp altitude of a `monPred_at` hypothesis, i.e. the `vwp_hold` discipline.

Rocq: no counterpart (Rocq's `into_exist_monPred_at` handles this case).
-/
import Iris.ProofMode.MonPred

namespace MachCSL

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode

variable {I : BiIndex} {PROP : Type _} [BI PROP]

instance intoExists_monPred_at_exists {α : Sort _} (Φ : α → MonPred I PROP) (i : I.car) :
    IntoExists ((iprop(∃ x, Φ x) : MonPred I PROP).monPred_at i)
      (fun x => (Φ x).monPred_at i) where
  into_exists := (monPred_at_exist i Φ).mp

instance fromExists_monPred_at_exists {α : Sort _} (Φ : α → MonPred I PROP) (i : I.car) :
    FromExists ((iprop(∃ x, Φ x) : MonPred I PROP).monPred_at i)
      (fun x => (Φ x).monPred_at i) where
  from_exists := (monPred_at_exist i Φ).mpr

end MachCSL
