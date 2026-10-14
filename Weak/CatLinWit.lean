/-
Weak: **W12 (6) — non-vacuity: a FORWARDING witness through `rvwmoCatAD`** (plan
`notes/weak-allocproc-plan.md` §C W12 (6), acceptance gate [R6.s2]).

Lean-only, no Rocq twin.  SB+rfi-pos, with the global memory order riscv.cat allows and RVWMO⁻
forbids (both forwarded reads gmo-BEFORE the stores they read):

    H0: (0,0) W x=1;  (0,1) R x = 1 (forwarded from (0,0));  (0,2) R y = 0
    H1: (1,0) W y=1;  (1,1) R y = 1 (forwarded from (1,0));  (1,2) R x = 0
    gmo = [(0,1); (0,2); (1,1); (1,2); (0,0); (1,0)]      (writes: (0,0) = 1, (1,0) = 2)

  * `sbrfiCatT`: the TAGGED model `rvwmoCatConsistentT` holds (computed, `catTConsistentBSound`),
    so `sbrfiCatAD`: the chain's hypothesis `rvwmoCatAD` holds by `catADOfCatT` — the published
    quantifier's entry point, exercised;
  * `sbrfiNotMinus`: RVWMO⁻ FAILS (`gpoloc` W x → R x demands the store gmo-before its own read);
  * `sbrfiForwarded`: the read (0,1)'s source is the own po-earlier store, gmo-AFTER it;
  * `sbrfiAcyclic`: `racyD` is acyclic (a rank, computed), so `sbrfiNormalizes`: the RESTATED
    `normalizeOfAcyclic` (W12 (1), core hypothesis) consumes this non-RVWMO⁻ graph and returns an
    RVWMO⁻ + rule-14 graph with the same rows up to renaming, which is ALSO cat-consistent in its
    six arms ([R21.2]).

The rank check (`racyChk`, `acyclicOfRank`) is a general Lean-only helper: a Boolean
over-approximation of `racyD`, checked on the gmo carrier.  D35-fix [OWN.54]: its rule-7 arm is
`grcscB` (RVWMO⁻'s rule-7 arm is riscv.cat's RCsc `grcsc`, `WeakRvwmoGraph` deviation 7); the
`sbrfi*` verdicts are recomputed under it (unchanged: `sbrfi` carries no annotated access).
-/
import Weak.CatLin
import Weak.AxGraphWit
import Weak.AxLitmus

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatLin

/-! # 1. An acyclicity check for `racyD` by a rank -/

/-- A Boolean OVER-approximation of `racyD` (each arm by its computed checker). -/
def racyChk (GD : Gdexec) (x y : Geid) : Bool :=
  (gpoB GD.gdG x y && glblB GD.gdG x lbIsMem && gisW GD.gdG y) || grfB GD.gdG x y ||
  gcoB GD.gdG x y || gfrB GD.gdG x y || gpolocB GD.gdG x y || gfenceB GD.gdG x y ||
  gacqB GD.gdG x y || grcscB GD.gdG x y || decide ((x, y) ∈ GD.gdDeps)

theorem racyChkOf (GD : Gdexec) (x y : Geid) : racyD GD x y → racyChk GD x y = true := by
  unfold racyChk
  rintro ((⟨hpo, hm, hw⟩ | h | h | h | (h | h | h | h)) | h) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl
      ⟨⟨(gpoBSpec _ _ _).2 hpo, (glblBSpec _ _ _).2 hm⟩, hw⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ((grfBSpec _ _ _).2 h))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ((gcoBSpec _ _ _).2 h)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr ((gfrBSpec _ _ _).2 h))))))
  · exact .inl (.inl (.inl (.inl (.inr ((gpolocBSpec _ _ _).2 h)))))
  · exact .inl (.inl (.inl (.inr ((gfenceBSpec _ _ _).2 h))))
  · exact .inl (.inl (.inr ((gacqBSpec _ _ _).2 h)))
  · exact .inl (.inr ((grcscBSpec _ _ _).2 h))
  · exact .inr h

/-- A rank strictly increasing along every checked edge of the carrier kills every `racyD`
cycle (the core puts both endpoints in the carrier, `racyDMem`). -/
theorem acyclicOfRank (GD : Gdexec) (rk : Geid → Nat) :
    rvwmoCoreD GD →
    GD.gdG.gxGmo.all (fun x => GD.gdG.gxGmo.all (fun y => !racyChk GD x y || decide (rk x < rk y)))
      = true →
    ∀ x, ¬ tc (racyD GD) x x := by
  intro hc hchk
  have step : ∀ a b, racyD GD a b → rk a < rk b := by
    intro a b h
    obtain ⟨ha, hb⟩ := racyDMem GD a b hc h
    have h1 := List.all_eq_true.1 hchk a ha
    have h2 := List.all_eq_true.1 h1 b hb
    rw [racyChkOf GD a b h] at h2
    simpa using h2
  have key : ∀ a b, tc (racyD GD) a b → rk a < rk b := by
    intro a b h
    induction h with
    | single h => exact step _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (step _ _ h)
  intro x hx
  exact Nat.lt_irrefl _ (key x x hx)

/-! # 2. SB+rfi-pos -/

def sbrfiProg : List (List Lbl) :=
  [[LStore false 0 [b1] .WCplain, LLoad false 0 [1] [b1], LLoad false 1 [0] [b0]],
   [LStore false 1 [b1] .WCplain, LLoad false 1 [2] [b1], LLoad false 0 [0] [b0]]]

def sbrfiGmo : List Geid := [(0, 1), (0, 2), (1, 1), (1, 2), (0, 0), (1, 0)]

def sbrfi : Gdexec := AxGraphWit.mkgd sbrfiProg sbrfiGmo []

/-- The same graph, TAGGED (no dependencies). -/
def sbrfiT : GdexecT := ⟨sbrfi.gdG, [], []⟩

theorem sbrfiCatT : rvwmoCatConsistentT sbrfiT :=
  catTConsistentBSound _ (by decide +kernel)

theorem sbrfiForget : forget sbrfiT = sbrfi := rfl

/-- THE GATE: the chain's hypothesis holds, through the published quantifier's entry. -/
theorem sbrfiCatAD : rvwmoCatAD sbrfi (gtAd sbrfiT.gtG sbrfiT.gtDeps) := by
  have h := catADOfCatT sbrfiT sbrfiCatT
  rw [sbrfiForget] at h
  exact h

theorem sbrfiCat : rvwmoCatConsistent sbrfi :=
  catConsistentBSound _ (by decide +kernel)

/-- … and RVWMO⁻ FAILS: the forwarded read precedes its source in gmo. -/
theorem sbrfiNotMinus : ¬ rvwmoMinusDepsConsistent sbrfi := by
  rintro ⟨h, _⟩
  exact notMinusOfPoloc _ (0, 0) (0, 1) (by decide +kernel) (by decide +kernel) h

/-- The forwarding shape: (0,1) reads the own po-earlier (0,0), which is gmo-AFTER it. -/
theorem sbrfiForwarded :
    grfAt sbrfi.gdG 0 (0, 0) (0, 1) ∧ WeakRvwmoGraph.gpo sbrfi.gdG (0, 0) (0, 1) ∧
    gmoLt sbrfi.gdG (0, 1) (0, 0) :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), (gpoBSpec _ _ _).1 (by decide +kernel),
    (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩

/-- Reads of the other hart's old value rank 0, stores 1, forwarded reads 2. -/
def sbrfiRank (e : Geid) : Nat := if e.2 = 2 then 0 else if e.2 = 0 then 1 else 2

theorem sbrfiAcyclic : ∀ x, ¬ tc (racyD sbrfi) x x :=
  acyclicOfRank sbrfi sbrfiRank (catADCore _ _ sbrfiCatAD) (by decide +kernel)

/-- THE RESTATED `normalizeOfAcyclic` CONSUMES A NON-RVWMO⁻ GRAPH. -/
theorem sbrfiNormalizes :
    ∃ (GD' : Gdexec) (pi : Nat → Nat),
      rvwmoMinusDepsConsistent GD' ∧ grule14 GD'.gdG ∧ rowsRel pi sbrfi.gdG GD'.gdG ∧
      GD'.gdDeps = sbrfi.gdDeps ∧ wperm pi sbrfi.gdG GD'.gdG ∧ gppoCat6Gmo GD'.gdG :=
  normalizeOfAcyclic sbrfi (catADCore _ _ sbrfiCatAD) (fun x y => racyDDec _ x y) sbrfiAcyclic

end CatLin

end Weak
