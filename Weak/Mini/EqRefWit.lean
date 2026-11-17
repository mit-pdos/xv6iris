/-
Weak/Mini: **K4 — MiniRef's finite cut is not vacuous** (mini plan rev 4 §4 K4: "a mini finite execution").

`mini_cut_witness`: `lbdd` (RefTests.lean row 2: `lw x5,0(x6); sw x5,0(x8)` on both harts, X/Y swapped) has a mini
finite execution: both harts run to the end, both loads read the initial 0, gmo = [ld₀, ld₁, st₀, st₁].  The
statement is MiniRef-only; the proof checks the full reference's `partExec` of `toCut` by kernel evaluation
(`refCoreB`, Ref.lean: `decide`, never `native_decide`) and transfers it with E1 (`e1aCut`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqRefCut

namespace Weak.Mini

open Weak.Prom.Ref
open Weak.Prom.Pfx

/-- `lbdd` as an F program (word size 4; X = 0x1000, Y = 0x2000). -/
def lbddM : MProg :=
  { harts := [[.load true 5 6 0, .store 5 8 0], [.load true 5 6 0, .store 5 8 0]]
    regs0 := [[(6, 0x1000), (8, 0x2000)], [(6, 0x2000), (8, 0x1000)]]
    img := []
    sz := 4 }

/-- Both harts ran their two instructions; every load reads 0; gmo = the two loads, then the two stores. -/
def lbddCut : MCut := ⟨fun _ => 2, fun _ => 0, [(0, 0), (1, 0), (0, 1), (1, 1)]⟩

theorem lbddM_wf : lbddM.wf := by
  refine ⟨by decide, by simp [lbddM], fun h i hi => ?_⟩
  simp only [MProg.prog, lbddM] at hi
  match h, hi with
  | 0, hi => simp at hi; rcases hi with rfl | rfl <;> exact ⟨trivial, by simp [MI.regOk], trivial⟩  -- [MiniP3 (0)]
  | 1, hi => simp at hi; rcases hi with rfl | rfl <;> exact ⟨trivial, by simp [MI.regOk], trivial⟩  -- [MiniP3 (0)]
  | n + 2, hi => simp at hi

/-- **K4**: lbdd has a MiniRef finite execution. -/
theorem mini_cut_witness : ∃ C, miniCut lbddM C := by
  refine ⟨lbddCut, (e1aCut lbddM lbddM_wf .tt lbddCut).2 ⟨by decide, fun h hh => ?_, by decide, ?_⟩⟩
  · rw [toCut_get]
    exact reach_of_replay (fun k => (replay_sim (agree_nuOf _ _) (tgtOk_of_wf lbddM_wf h) k).2.1) _
  · exact refCoreB_sound _ (by decide +kernel)

end Weak.Mini
