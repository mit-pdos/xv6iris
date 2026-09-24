import Xv6.BcacheInv
open Xv6 in
example (l : List Nat) (P : List Nat → Prop) (h0 : P []) (hs : ∀ l a, P l → P (l ++ [a])) : P l := by
  induction l using FromMathlib.List.reverseRec with
  | nil => exact h0
  | append_singleton l a ih => exact hs l a ih
open Xv6 in
example (Ls : Nat → List Nat) (k : Nat) : updAtB Ls k (Ls k) = Ls := by
  funext j; unfold updAtB; by_cases h : j = k <;> simp [h]
open Xv6 in
example (l : List Nat) (a : Nat) (d : BitVec 64) (f : Nat → BitVec 64) :
    blast ((l ++ [a]).map f) d = f a := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [blast_app]
  rfl
