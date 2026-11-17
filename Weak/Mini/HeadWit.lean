/-
Weak/Mini: **K4 — the headlines are NOT vacuous** (mini plan rev 4 §4 K4: "every mini execution/run notion has a
Lean vacuity witness"; the P1 gate review §1 "a misaligned program has NO execution, so a `mini_forbidden` of it
would be vacuous — K4 witnesses are the guard; keep them next to each headline").

The STATEMENTS are MiniRef-only (Ref.lean, Head.lean); the proofs check the full reference by kernel evaluation or
reuse the full witness (Weak/Prom/InfLoopWit.lean) and transfer it with E1 (`e1aCut`, `transfer` = `e1b`).
* `mini_lbdd_witness` (`mini_forbidden_lbdd`): a finite execution of `lbddP` in which both harts' first loads
  exist (they return 0: both loads before both stores in gmo).
* `mini_mpFF_witness` (`mini_forbidden_mpFF`): a finite execution of `mpFFP` in which hart 1's two loads exist
  (both return 0: hart 1 runs before hart 0 in gmo).
* `mini_infExec_witness` (`mini_inf_mpLoop`): an infinite execution of `loopP` exists; `mini_inf_mpLoop_exercised`:
  one in which EVERY premise of `mini_inf_mpLoop` holds at once (hart 1's second flag load `(1, 3)` returned 1, its
  next memory operation `(1, 5)` is the data load), and `mini_inf_mpLoop_exercised_concl` adds the conclusion.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqHead
import Weak.Prom.InfLoopWit

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx
open Weak.Mini.Logic (lbddP mpFFP loopP)

/-! ## 1. Finite executions -/

theorem lbddCut_ok : miniCut lbddP lbddCut := by
  rw [lbddP_eq]
  refine (e1aCut lbddM lbddM_wf .tt lbddCut).2 ⟨by decide, fun h hh => ?_, by decide, ?_⟩
  · rw [toCut_get]
    exact reach_of_replay (fun k => (replay_sim (agree_nuOf _ _) (tgtOk_of_wf lbddM_wf h) k).2.1) _
  · exact refCoreB_sound _ (by decide +kernel)

/-- **K4 for `mini_forbidden_lbdd`**: `lbddP` has a finite execution, in which both harts' first loads exist. -/
theorem mini_lbdd_witness :
    ∃ C, miniCut lbddP C ∧ C.obsLoad lbddP 0 0 = some 0 ∧ C.obsLoad lbddP 1 0 = some 0 :=
  ⟨lbddCut, lbddCut_ok, rfl, rfl⟩

/-- Both harts ran their three instructions; every load reads 0; gmo = hart 1's two loads, then hart 0's stores. -/
def mpFFCut : MCut := ⟨fun _ => 3, fun _ => 0, [(1, 0), (1, 2), (0, 0), (0, 2)]⟩

theorem mpFFCut_ok : miniCut mpFFP mpFFCut := by
  refine (e1aCut mpFFP mpFFP_wf .tt mpFFCut).2 ⟨by decide, fun h hh => ?_, by decide, ?_⟩
  · rw [toCut_get]
    exact reach_of_replay (fun k => (replay_sim (agree_nuOf _ _) (tgtOk_of_wf mpFFP_wf h) k).2.1) _
  · exact refCoreB_sound _ (by decide +kernel)

/-- **K4 for `mini_forbidden_mpFF`**: `mpFFP` has a finite execution, in which hart 1's two loads exist. -/
theorem mini_mpFF_witness :
    ∃ C, miniCut mpFFP C ∧ C.obsLoad mpFFP 1 0 = some 0 ∧ C.obsLoad mpFFP 1 1 = some 0 :=
  ⟨mpFFCut, mpFFCut_ok, rfl, rfl⟩

/-! ## 2. Infinite executions -/

/-- **K4 for `mini_inf_mpLoop`**: `loopP` has an infinite execution (the SC interleaving `E_SC` of InfLoopWit.lean,
through E1b). -/
theorem mini_infExec_witness : ∃ X, miniExec loopP X := by
  obtain ⟨X, hX, _⟩ := transfer (cond := Weak.Prom.PF.Loop.tLoop.cond) loopP_wf
    (by rw [loopP_toTest]; exact Weak.Prom.InfLoop.Wit.infExec_witness)
  exact ⟨X, hX⟩

/-- **Every premise of `mini_inf_mpLoop` is met at once** (hart 1, flag load `(1, 3)`, data load `(1, 5)`). -/
theorem mini_inf_mpLoop_exercised : ∃ X h i j, miniExec loopP X ∧
    (X.evs loopP).isMem (h, i) ∧ (X.evs loopP).isMem (h, j) ∧ i < j ∧
    (∀ k, i < k → k < j → ¬ (X.evs loopP).isMem (h, k)) ∧
    (X.evs loopP).isLd (h, i) ∧ ((X.evs loopP).ev (h, i)).pa = 0x2000 ∧ ((X.evs loopP).ev (h, i)).v = 1 ∧
    (X.evs loopP).isLd (h, j) ∧ ((X.evs loopP).ev (h, j)).pa = 0x1000 := by
  obtain ⟨E, h, i, j, hE, hi, hj, hij, hn, hfl, hfa, hfv, hdl, hda⟩ := Weak.Prom.InfLoop.Wit.inf_mpLoop_exercised
  obtain ⟨X, hX, _, hmem, hld, hpa, hrd⟩ := transfer (cond := Weak.Prom.PF.Loop.tLoop.cond) loopP_wf
    (by rw [loopP_toTest]; exact hE)
  have hfl' := (hld _ hi.1).1 hfl
  exact ⟨X, h, i, j, hX, (hmem _).1 hi, (hmem _).1 hj, hij, fun k h1 h2 hk => hn k h1 h2 ((hmem _).2 hk), hfl',
    by rw [← hpa _ hi.1]; exact hfa, word_one (hrd _ hi.1 hfl').2 ((hrd _ hi.1 hfl').1.symm.trans hfv),
    (hld _ hj.1).1 hdl, by rw [← hpa _ hj.1]; exact hda⟩

/-- **Premises and conclusion together**: some infinite execution of `loopP` meets every premise of
`mini_inf_mpLoop`, and its data load returned 1. -/
theorem mini_inf_mpLoop_exercised_concl : ∃ X h i j, miniExec loopP X ∧
    (X.evs loopP).isMem (h, i) ∧ (X.evs loopP).isMem (h, j) ∧ i < j ∧
    (∀ k, i < k → k < j → ¬ (X.evs loopP).isMem (h, k)) ∧
    (X.evs loopP).isLd (h, i) ∧ ((X.evs loopP).ev (h, i)).pa = 0x2000 ∧ ((X.evs loopP).ev (h, i)).v = 1 ∧
    (X.evs loopP).isLd (h, j) ∧ ((X.evs loopP).ev (h, j)).pa = 0x1000 ∧ ((X.evs loopP).ev (h, j)).v = 1 := by
  obtain ⟨X, h, i, j, hX, hi, hj, hij, hn, hfl, hfa, hfv, hdl, hda⟩ := mini_inf_mpLoop_exercised
  exact ⟨X, h, i, j, hX, hi, hj, hij, hn, hfl, hfa, hfv, hdl, hda,
    mini_inf_mpLoop hX h i j hi hj hij hn hfl hfa hfv hdl hda⟩

end Weak.Mini
