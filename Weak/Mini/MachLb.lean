/-
Weak/Mini: **a hand-built valid run of MiniMach: `lb` ALLOWED** (mini plan rev 4 §4 K4: every mini run notion has a
Lean vacuity witness; §1: "`lb` (ALLOWED) is `mini_lb_allowed`, a HAND-BUILT mini valid run").

`lbP` is RefTests.lean `lb` (:76) as an F program: hart 0 `lw x5,0(x6); sw x7,0(x8)` with `x6 = X, x7 = 1, x8 = Y`;
hart 1 the same with `x6 = Y, x8 = X`; image 0; size 4.  The run: both harts promise their stores first (hart 0:
`Y := 1` at timestamp 1, hart 1: `X := 1` at 2), then each hart's load reads the OTHER hart's promised store, then
each fulfils its promise.  `mini_lb_valid`: a valid run in which both loads return 1.
Imports: only `Weak.Mini.Mach`.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Mach

namespace Weak.Mini.Mach

open Weak.Mini

/-- Address `X` (RefTests.lean:23). -/
def lbX : Nat := 0x1000
/-- Address `Y` (RefTests.lean:24). -/
def lbY : Nat := 0x2000

/-- RefTests.lean `lb` (:76) as an F program. -/
def lbP : MProg where
  harts := [[.load true 5 6 0, .store 7 8 0], [.load true 5 6 0, .store 7 8 0]]
  regs0 := [[(6, lbX), (7, 1), (8, lbY)], [(6, lbY), (7, 1), (8, lbX)]]
  img := []
  sz := 4

/-- The run's events. -/
def lbEvs : List MEvt :=
  [.prom 0 ⟨lbY, 1, 0⟩, .prom 1 ⟨lbX, 1, 1⟩,
   .st 0 (.load lbX 2 1 [.reg 6]) none, .st 0 (.regW 5 [.ldres]) none, .st 0 .instr none,
   .st 0 (.store lbY 1 [.reg 8] [.reg 7]) (some 1), .st 0 .instr none,
   .st 1 (.load lbY 1 1 [.reg 6]) none, .st 1 (.regW 5 [.ldres]) none, .st 1 .instr none,
   .st 1 (.store lbX 1 [.reg 8] [.reg 7]) (some 2), .st 1 .instr none]

theorem writesIn_empty {log : List MMsg} {a lo hi : Nat} (h : hi ≤ lo) : ¬ writesIn log a lo hi :=
  fun ⟨_, h1, h2, _⟩ => by omega

theorem noProm_of {c : MCfg} (h : (c.hs.all (fun h => h.prom.isEmpty)) = true) : noProm c := by
  intro i hi hh
  have hm := List.mem_of_getElem? hh
  have := List.all_eq_true.1 h hi hm
  simpa using this

/-- The events reach a configuration with no outstanding promise. -/
theorem lb_run : ∃ c, mSteps lbP (mInit lbP) lbEvs c ∧ noProm c := by
  refine ⟨?c, ?run, ?np⟩
  case run =>
    refine .step _ _ _ _ _ (.promise _ 0 _ _ rfl rfl (by decide) (by decide)) ?_
    refine .step _ _ _ _ _ (.promise _ 1 _ _ rfl rfl (by decide) (by decide)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl
      (.load _ _ _ _ _ _ ⟨rfl, writesIn_empty (by decide)⟩)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.regW _ _ _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl
      (.store _ _ _ _ _ _ _ (by decide) rfl (by decide) (by decide))) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl
      (.load _ _ _ _ _ _ ⟨rfl, writesIn_empty (by decide)⟩)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.regW _ _ _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl
      (.store _ _ _ _ _ _ _ (by decide) rfl (by decide) (by decide))) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    exact .refl _
  case np => exact noProm_of rfl

/-- **`lb` is ALLOWED by MiniMach**: a valid run in which both harts' loads return 1 (the vacuity witness of
`miniValidRun`, K4). -/
theorem mini_lb_valid :
    ∃ Mm r, miniValidRun lbP Mm r ∧ r.obsLoad 0 0 = some 1 ∧ r.obsLoad 1 0 = some 1 := by
  obtain ⟨c, h1, h2⟩ := lb_run
  exact ⟨c.log, ⟨lbEvs⟩, ⟨c, h1, h2, rfl⟩, rfl, rfl⟩

end Weak.Mini.Mach
