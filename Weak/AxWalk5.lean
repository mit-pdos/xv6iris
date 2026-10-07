/-
Weak: **walker TAGGING and the sfence.vma MARKER** (task items 4, 5): what the opax step
relation can and cannot express.

Rocq: `iris/AxWalk5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

ITEM 4 (walker events vs explicit loads).  The Sail tree does not distinguish a walker PTE
read from a data load (both are the same `memRead` node; the access type only feeds
register-only PMA/PMP checks), and the opax label is `LLoad` either way.  So the tag can only
be ROW-SIDE: the certificate constructor (`CertWP.pWrd` vs `pDrd`) and the row positions the
bridge reports (`ws`).  `gpForRow i kd ws` (§1) is the `gpFor`-style map built from them;
`gpForRowWf` discharges the first clause of `ptwWf` for it.  Full riscv.cat is forced on
walker reads not by the step relation but by the GRAPH QUANTIFIER of the logic and its
adequacy (`rvwmoCatConsistent GD`) — stronger than hardware under H5'.1; the fix would
quantify over `ptwModelRow i kd ws sf GD` (§2, a definition only: AxWp/AxWpD are not edited).

ITEM 5 (sfence.vma).  Sail's `execute_SFENCE_VMA` tree is register-only
(`rfFExecuteSFENCEVMA`: no memory, no barrier node).  A row-side marker item
(`LFence false false false false` at row position `k`) cannot be consumed silently by the opax
step relation: no read step matches it (`markerNoRead`) and every opax step that moves past it
emits a FENCE label (`markerStepIsFence`).  §3 also states the proposed derived relation
`astepSf` (a silent marker step at the positions `sfk` the certificate marks) and its
conservativity `astepInclSf`.

LEAN NOTE (Q7, see `Weak/AxSfence.lean`'s header): in the Lean tree the SFENCE.VMA ANNOUNCE
node itself emits the label `LFence false false false false` (`WeakEvLang.annLabel`), so the
marker IS consumed by `AStepFence` — the route Rocq's header calls "the fence label the sfence
tree never emits" is taken by the announce, not by `execute_SFENCE_VMA`.  The statements here
are unchanged by that; they remain true facts about the relations.

## Deviations from Rocq

1. O2 STAGE C: `astepProg`/`astep` have no oracle parameters `T`/`img` (AxOpsem deviation 2),
   so the section `marker` has only `row`, and `astepSf`/`astepInclSf` take no `T`/`img`.
   `markerStepIsFence` has three constructor cases (no `AStep_fetch`).
2. `ws.*1` ↦ `ws.map Prod.fst`; `bool_decide (…)` ↦ `if … then … else …`; `is_Some o` ↦
   `o.isSome = true`; `gx_lbl` ↦ `gxLbl`; `gpo` ↦ `WeakRvwmoGraph.gpo`; `GPtw GD f sf` ↦
   `Gptw.mk GD f sf`; `S k` ↦ `k + 1`; `agent` ↦ `Nat`; `rs1 rs2 : regidx`.

**Rocq → Lean name map.**  `gp_for_row` `gpForRow`, `gp_for_row_wf` `gpForRowWf`,
`ptw_model_row` `ptwModelRow`, `rfF_execute_SFENCE_VMA` `rfFExecuteSFENCEVMA`,
`marker_no_read` `markerNoRead`, `marker_step_is_fence` `markerStepIsFence`, `astep_sf`
`astepSf`, `astep_incl_sf` `astepInclSf`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 3 definitions + 5 lemmas; Lean the same).  **Not ported:** the
`Print Assumptions` lines.
-/
import Weak.AxWalk
import Weak.AxSpineOk2
import Weak.AxPtProt
import Weak.AxOpsem

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. Row-side tagging -/

/-- `gpFor` built from the walker events the bridge reports for hart `i`: every walker row
position serves the explicit access at `kd`. -/
def gpForRow (i : Nat) (kd : Nat) (ws : List (Nat × Wev)) (e : Geid) : Option Geid :=
  if e.1 = i ∧ e.2 ∈ ws.map Prod.fst then some (i, kd) else none

theorem gpForRowWf (G : Gexec) (i kd : Nat) (ws : List (Nat × Wev)) :
    (∀ k, k ∈ ws.map Prod.fst → k < kd ∧ (gxLbl G (i, k)).isSome = true) →
    (gxLbl G (i, kd)).isSome = true → kd ∉ ws.map Prod.fst →
    ∀ u e, gpForRow i kd ws u = some e →
      WeakRvwmoGraph.gpo G u e ∧ gpForRow i kd ws e = none := by
  intro Hws Hd Hnd ⟨i', k⟩ e
  unfold gpForRow
  by_cases Hc : (i', k).1 = i ∧ (i', k).2 ∈ ws.map Prod.fst
  · rw [if_pos Hc]
    intro h
    cases h
    obtain ⟨h1, Hk⟩ := Hc
    simp only at h1 Hk
    subst h1
    obtain ⟨Hlt, Hl⟩ := Hws k Hk
    refine ⟨⟨rfl, Hlt, Hl, Hd⟩, ?_⟩
    rw [if_neg]
    intro ⟨_, Hk'⟩
    exact Hnd Hk'
  · rw [if_neg Hc]
    intro h
    cases h

/-! ## 2. The derived graph quantifier (proposal; definition only) -/

def ptwModelRow (i : Nat) (kd : Nat) (ws : List (Nat × Wev)) (sf : Geid → Bool)
    (GD : Gdexec) : Prop :=
  ptwModel (Gptw.mk GD (gpForRow i kd ws) sf)

/-! ## 3. sfence.vma -/

theorem rfFExecuteSFENCEVMA (rs1 rs2 : regidx) : rfF (execute_SFENCE_VMA rs1 rs2) := by
  rff_auto

section marker

variable (row : List Lbl)

theorem markerNoRead (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread) (lb : Lbl)
    (pr pw sr sw : Bool) :
    row[s.atK]? = some lb → aident lb = .IFence pr pw sr sw → ¬ areadStep row s id K := by
  intro Hl Hid ⟨lb', Hl', Hid', Hrd, _⟩
  rw [Hl] at Hl'
  cases Hl'
  rw [Hid] at Hid'
  subst Hid'
  simp [aidentRd] at Hrd

theorem markerStepIsFence (p : Pexv6) (k : Nat) (lb : Lbl) (pr pw sr sw : Bool) (l : Wlabel)
    (s' : Athread) :
    row[k]? = some lb → aident lb = .IFence pr pw sr sw →
    AxOpsem.astepProg row ⟨p, k⟩ l s' → s'.atK = k ∨ (wlFence l).isSome = true := by
  intro Hl Hid Hst
  cases Hst with
  | AStepAdmin _ _ _ _ _ _ _ _ => exact .inl rfl
  | AStepWrite _ _ _ _ lb' _ _ Hrow Hwr Hid' _ _ =>
    exfalso
    rw [Hl] at Hrow
    cases Hrow
    rw [Hid] at Hid'
    simp only [aidentWr] at Hid'
    rw [Hid'] at Hwr
    exact Bool.noConfusion Hwr
  | AStepFence _ _ _ _ _ _ _ _ Hf _ _ => exact .inr Hf

/-- The proposed derived relation: a SILENT MARKER STEP at the positions `sfk` the
certificate marks. -/
def astepSf (sfk : Nat → Prop) (s s' : Athread) : Prop :=
  astep row s s' ∨
  (sfk s.atK ∧ (∃ lb, row[s.atK]? = some lb ∧ aident lb = .IFence false false false false) ∧
   s'.atP = s.atP ∧ s'.atK = s.atK + 1)

theorem astepInclSf (sfk : Nat → Prop) (s s' : Athread) :
    astep row s s' → astepSf row sfk s s' :=
  fun h => .inl h

end marker

end Weak
