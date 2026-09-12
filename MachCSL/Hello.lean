import Iris.ProofMode
import Iris.Instances.IProp

/-! A smoke test that iris-lean's proof mode is wired up. -/

open Iris BI ProofMode

theorem sep_comm_test [BI PROP] (P Q : PROP) : P ∗ Q ⊢ Q ∗ P := by
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP
