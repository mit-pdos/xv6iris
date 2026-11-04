/-
Weak/Prom: **E-c — the A/D arm is exercised: a valid run that fix (ii) cannot replay** (G4 experiment E-c).

One hart: a speculative A update of the PTE byte `p` (`ad`, timestamp 2), then a release store to `x` (timestamp 1).
The A/D write raises no view (supervisor.adoc:1625–1627; AdMachine.lean), so the release's pre-view stays 0 < 1:
the run is valid, and in the hart's trace the A/D update at 2 precedes the release at 1.  Any NF run fulfils the
release in place at log length 0 → 1 (NF_R's release shape), so the A/D step runs while the log has length 0 < 2:
it must be the prophecy-fed `adF` (fix (i)); deferring it (fix (ii)) would reorder the trace.  `nfRAd` applies
(`witness_nf`).  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.NfrAd

namespace Weak.Prom.Ad.Witness

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image)
open Weak.Prom Weak.Prom.Nfr
open PLabel

def xA : Int := 0x100
def pA : Int := 0x200
def img2 : Image := fun _ => some 0
def mX : PMsg := ⟨xA, [1], some 0, .rel⟩
def mAd : PMsg := ⟨pA, [1], some 0, PClass.ad⟩
def lAd : VLabel := .ad pA [(0, 0)] [1]
def lRel : VLabel := .v (LStore false true xA [1] [] [])

/-- The program: the A/D update, then the release store. -/
def prog : Nat → Unit → VLabel → Nat → Unit → Prop :=
  fun s _ l s' _ => (s = 0 ∧ l = lAd ∧ s' = 1) ∨ (s = 1 ∧ l = lRel ∧ s' = 2)

def evs2 : List VEvt := [.prom 0 mX, .prom 0 mAd, .st 0 lAd (some 2), .st 0 lRel (some 1)]

theorem witness : ∃ cfg, validRunV prog img2 () [0] evs2 cfg ∧ cfg.pcLog = [mX, mAd] ∧
    traceOfV 0 evs2 = [(lAd, some 2), (lRel, some 1)] := by
  let P2 : GSet Nat := {[mX].length + 1} ∪ ({([] : List PMsg).length + 1} ∪ ∅)
  have h2 : 2 ∈ P2 := elemOfUnion.2 (.inl (elemOfSingleton.2 rfl))
  have h1 : 1 ∈ P2 \ {2} :=
    elemOfDifference.2 ⟨elemOfUnion.2 (.inr (elemOfUnion.2 (.inl (elemOfSingleton.2 rfl)))),
      fun h => by rw [elemOfSingleton] at h; omega⟩
  have hrd : bytesAll (adReadOk img2 [mX, mAd] 2) pA [(0, 0)] := by
    refine ⟨⟨rfl, by omega, ?_⟩, trivial⟩
    rintro ⟨t, ht1, ht2, m, hm, hb⟩
    obtain rfl : t = 1 := by omega
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hm
    subst hm
    simp [PMsg.byteAt, mX, xA, pA] at hb
  have hcoh : cohBelow psInit xA [(1 : BitVec 8)].length 1 := by
    simp [cohBelow, coh, psInit, lookupEmpty]
  have hpv : stPreA psInit false true (srcsView psInit []) (srcsView psInit []) < 1 := by
    simp [stPreA, stPre, psInit, srcsView]
  refine ⟨_, ⟨.step _ _ _ _ _ (.promise _ 0 _ mX rfl (.inl (by simp [mX])) rfl)
    (.step _ _ _ _ _ (.promise _ 0 _ mAd rfl (.inl (by simp [mAd])) rfl)
    (.step _ _ _ _ _ (.state _ 0 _ lAd (some 2) 1 () psInit (P2 \ {2}) rfl (.inl ⟨rfl, rfl, rfl⟩)
      (.ad _ _ pA [(0, 0)] [1] 2 rfl (by omega) h2 rfl hrd))
    (.step _ _ _ _ _ (.state _ 0 _ lRel (some 1) 2 () _ ((P2 \ {2}) \ {1}) rfl (.inr ⟨rfl, rfl, rfl⟩)
      (.v2 _ _ _ _ _ _ (.store _ _ false true xA [1] [] [] 1 h1 rfl hcoh hpv) (fun ⟨_, _, e⟩ => by cases e)))
    (.refl _)))), ?_⟩, rfl, rfl⟩
  intro i ag hag
  cases i with
  | zero =>
    simp [pmInit] at hag
    subst hag
    refine setEq.2 (fun t => ⟨fun ht => ?_, fun ht => absurd ht notElemOfEmpty⟩)
    simp [P2, elemOfDifference, elemOfUnion, elemOfSingleton, notElemOfEmpty] at ht
    omega
  | succ k => simp [pmInit] at hag

/-- `nfRAd` applies to the witness; its NF run keeps the trace `[A/D at 2, release at 1]`. -/
theorem witness_nf : ∃ cfg evs', nfRunV relClass prog cfg.pcLog img2 () [0] evs' cfg ∧
    traceOfV 0 evs' = [(lAd, some 2), (lRel, some 1)] := by
  obtain ⟨cfg, hv, _, htr⟩ := witness
  obtain ⟨evs', h1, h2⟩ := nfRAd hv
  exact ⟨cfg, evs', h1, by rw [h2, htr]⟩

end Weak.Prom.Ad.Witness
