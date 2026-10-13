/-
Weak: **W12b acceptance [R7.s5] — the forwarding read the old floor invariant mis-states,
certified by the per-byte one** (plan `notes/weak-allocproc-plan.md` §C W12b).

Lean-only, no Rocq twin.  On `CatLinWit.sbrfi` (SB+rfi-pos, cat-consistent, NOT RVWMO⁻): hart 0's
own store `w = (0,0)` to byte 0 is forwarded to the po-later read `r = (0,1)`, and `w` is
gmo-AFTER `r` — exactly `finvStep`'s coh-hook case (`WeakRvwmoFloor`, the `LStore` arm's coh
clause through `gpolocGmo`).

  * `sbrfiOldUbFails`: `gvisUb G r (gwix G w)` is FALSE; so after the store the OLD invariant
    `finv` fails (`sbrfiOldFinvFails`) — its coh clause would need `w` gmo-before `r`;
  * `sbrfiNewFinv`: the NEW invariant `finvC` holds at the same state (`finvCStep` from
    `finvCInit`: the store is po-visible to `r`, so its index is ≤ `r`'s timestamp);
  * `sbrfiCertified`: the floor is discharged by `gtraceSnocReadConsistentC` — the sRVWMO candidate
    `[W x=1 (hart 0); R x (hart 0)]` that this G-trace prefix builds is consistent with the read
    appended, its floor obligation discharged over cat.
-/
import Weak.CatFloor
import Weak.CatLinWit

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace CatLin

/-- No label of `sbrfi` carries `rl`: the D35 premise holds vacuously. -/
theorem sbrfiNoRl (e : Geid) (l : Lbl) : gxLbl sbrfi.gdG e = some l → lbRl l = false := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | _ | k <;>
    simp [gxLbl, sbrfi, AxGraphWit.mkgd, sbrfiProg] at hl <;> subst hl <;> rfl

theorem sbrfiRel7 : grelAcqGmoC sbrfi.gdG := by
  rintro e1 e2 ⟨_, _, ⟨l, hl, hrl⟩, _, _⟩
  rw [sbrfiNoRl e1 l hl] at hrl
  cases hrl

theorem sbrfiFloorFacts : gwf sbrfi.gdG ∧ gppoCat6Gmo sbrfi.gdG ∧ gloadValue sbrfi.gdG :=
  catADFloor _ _ sbrfiCatAD

def sbrfiStore : Lbl := LStore false 0 [b1] .WCplain

def sbrfiRead : Lbl := LLoad false 0 [1] [b1]

theorem sbrfiLblW : gxLbl sbrfi.gdG (0, 0) = some sbrfiStore := rfl

theorem sbrfiLblR : gxLbl sbrfi.gdG (0, 1) = some sbrfiRead := rfl

theorem sbrfiGwixW : gwix sbrfi.gdG (0, 0) = 1 := by decide

theorem sbrfiReads : greadsByte sbrfi.gdG (0, 1) 0 1 b1 :=
  ⟨sbrfiRead, 0, [1], [b1], 0, sbrfiLblR, rfl, rfl, rfl, by simp [accAddr]⟩

/-- THE MIS-STATEMENT: the forwarded own store is NOT gmo-before the read. -/
theorem sbrfiOldUbFails : ¬ gvisUb sbrfi.gdG (0, 1) (gwix sbrfi.gdG (0, 0)) := by
  intro h
  have hlt : gmoLt sbrfi.gdG (0, 0) (0, 1) :=
    h 1 (0, 0) (by decide) (by rw [sbrfiGwixW]; exact Nat.le_refl 1)
  have hf : gmoLtB sbrfi.gdG (0, 0) (0, 1) = false := by decide +kernel
  rw [(gmoLtBSpec _ _ _).2 hlt] at hf
  cases hf

/-- The state of hart 0 after its store (timestamp 1). -/
def sbrfiWs1 : Wstate := WeakRvwmoFloor.lstep 1 wsInit sbrfiStore

theorem sbrfiCoh1 : coh sbrfiWs1 0 = 1 := by decide +kernel

/-- … so the OLD invariant fails right after the store. -/
theorem sbrfiOldFinvFails : ¬ finv sbrfi.gdG (0, 1) 0 1 sbrfiWs1 := by
  rintro ⟨_, hcoh, _⟩
  rw [sbrfiCoh1, ← sbrfiGwixW] at hcoh
  exact sbrfiOldUbFails hcoh

/-- … while the NEW one holds there. -/
theorem sbrfiNewFinv : finvC sbrfi.gdG (0, 1) 0 1 1 sbrfiWs1 := by
  obtain ⟨hwf, h6, hlv⟩ := sbrfiFloorFacts
  exact finvCStep sbrfi.gdG hwf h6 hlv sbrfiRel7 (0, 1) 0 1 b1 sbrfiReads 0 sbrfiStore wsInit 1
    (by decide) sbrfiLblW (fun _ => sbrfiGwixW) (fun base ts vs h => by cases h)
    (finvCInit _ _ _ _)

/-- The G-trace prefix of the store, and its candidate. -/
def sbrfiC0 : Cand := ⟨sbrfi.gdG.gxImg, []⟩

def sbrfiC1 : Cand := candSnoc sbrfiC0 ⟨0, sbrfiStore⟩

def sbrfiEv1 : Nat → Geid := evSnoc sbrfiC0 (fun _ => (0, 0)) (0, 0)

theorem sbrfiC0Cons : srvwmoConsistent sbrfiC0 :=
  srvwmoOfWf _ (candReachable _ (fun k s hs => by simp [sbrfiC0] at hs)).1

theorem sbrfiC1Gt : srvwmoConsistent sbrfiC1 ∧ GtracePrefix sbrfi.gdG sbrfiC1 sbrfiEv1 :=
  gtraceSnocWriteConsistent sbrfi.gdG sbrfiC0 (fun _ => (0, 0)) 0 false 0 [b1] .WCplain
    sbrfiFloorFacts.1 sbrfiC0Cons (gtracePrefixEmpty _) sbrfiLblW sbrfiGwixW

/-- **THE ACCEPTANCE**: the forwarded read, appended to the store's G-trace prefix, is admitted
by the sRVWMO candidate — its floor certified over cat by the per-byte invariant. -/
theorem sbrfiCertified :
    srvwmoConsistent (candSnoc sbrfiC1 ⟨0, sbrfiRead⟩) ∧
    GtracePrefix sbrfi.gdG (candSnoc sbrfiC1 ⟨0, sbrfiRead⟩) (evSnoc sbrfiC1 sbrfiEv1 (0, 1)) := by
  obtain ⟨hwf, h6, hlv⟩ := sbrfiFloorFacts
  have h := gtraceSnocReadConsistentC sbrfi.gdG sbrfiC1 sbrfiEv1 0 false 0 [1] [b1] hwf h6 hlv
    sbrfiRel7 ?_ sbrfiC1Gt.1 sbrfiC1Gt.2 sbrfiLblR ?_
  · exact h
  · intro k hk base ts vs heq
    have hk0 : k = 0 := by simp [sbrfiC1, sbrfiC0, candSnoc, gcnt] at hk; omega
    subst hk0
    rw [sbrfiLblW] at heq
    cases heq
  · intro j t hj
    rcases j with _ | j
    · simp at hj; subst hj; decide
    · simp at hj

end CatLin

end Weak
