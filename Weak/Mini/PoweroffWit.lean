/-
Weak/Mini: **the power-off witness pair** — whether a run prefix with an outstanding promise can be extended to a
run with no outstanding promise depends on the program order the machine must preserve (here a fence).

Two F programs on the addresses `lbX`/`lbY` of MachLb.lean (image empty, size 4, harts 0-indexed, timestamps from 1):
* `pwrA` (LB, hart 0 data-dependent): hart 0 `lw x5,0(x6); sw x5,0(x8)` with `x6 = X`, `x8 = Y` (the store's DATA is
  the loaded register); hart 1 `lw x5,0(x6); sw x7,0(x8)` with `x6 = Y`, `x7 = 1`, `x8 = X`.
* `pwrB`: the same, except hart 1 is `lw x5,0(x6); fence r,w; sw x7,0(x8)`.

THE PREFIX `pwrPre` (the same events in both programs): (1) hart 1 promises `X := 1` (timestamp 1); (2) hart 0's
`lw` reads timestamp 1 (value 1); (3) hart 0 promises `Y := 1` (timestamp 2) and its `sw` fulfils it (data view
1 < 2); (4) hart 1's `lw` reads timestamp 2 (value 1), so hart 1's `vrOld` is 2.  Power off here: hart 1 still owes
timestamp 1.
* `pwrA_extendable`: in A the prefix EXTENDS — hart 1's `sw` fulfils timestamp 1 (pre-view 0 < 1, coherence
  0 < 1).  RVWMO ALLOWS `r1 = r2 = 1` for LB with one data dependency.
* `pwrB_dead`: in B NO continuation reaches a configuration with no outstanding promise.  Invariant (`Inv1`): hart 1
  still owes timestamp 1, its `vrOld ≥ 2`, its pc is past the load, once past the fence its `vwNew ≥ 2`, and its
  queue holds only bookkeeping labels; hart 1's store is reached only through the fence, so its pre-view is
  `≥ vwNew ≥ 2` and it can fulfil only a timestamp `≥ 3`.  RVWMO FORBIDS the outcome: the cycle
  ld X(h0) -data-> sd Y(h0) -rf-> ld Y(h1) -fence r,w-> sd X(h1) -rf-> ld X(h0).
* `pwrB_alt_extendable`: in B the prefix whose step (4) reads timestamp 0 (value 0) DOES extend: the dead end
  comes from the state, not from the program.

So `mini_adequacy_poweroff`'s extendability premise (AdeqPoweroff.lean) is exactly what excludes B's prefix: it is a
run prefix of B with both loads returning 1, but no continuation fulfils its promise.
The instantiation of `mini_adequacy_poweroff` on A (optional item D) is not done here: it needs wp proofs of both
harts of `pwrA` (the `lbdd_hart` route of LitLbdd.lean, re-done for this program), not ready-made.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.MachLb

namespace Weak.Mini.Mach

open Weak.Mini

/-! ## 1. The programs and the events -/

/-- `fence r,w`. -/
def fenceRW : MFence :=
  { pr := true, pw := false, pi := false, po := false, sr := false, sw := true, si := false, so := false }

/-- Program A: LB, hart 0 data-dependent. -/
def pwrA : MProg where
  harts := [[.load true 5 6 0, .store 5 8 0], [.load true 5 6 0, .store 7 8 0]]
  regs0 := [[(6, lbX), (8, lbY)], [(6, lbY), (7, 1), (8, lbX)]]
  img := []
  sz := 4

/-- Program B: A with `fence r,w` between hart 1's load and store. -/
def pwrB : MProg where
  harts := [[.load true 5 6 0, .store 5 8 0], [.load true 5 6 0, .fence fenceRW, .store 7 8 0]]
  regs0 := [[(6, lbX), (8, lbY)], [(6, lbY), (7, 1), (8, lbX)]]
  img := []
  sz := 4

/-- The shared prefix: hart 1 promises `X := 1` (ts 1); hart 0 reads it, promises `Y := 1` (ts 2) and fulfils it;
hart 1 reads ts 2. -/
def pwrPre : List MEvt :=
  [.prom 1 ⟨lbX, 1, 1⟩,
   .st 0 (.load lbX 1 1 [.reg 6]) none, .st 0 (.regW 5 [.ldres]) none, .st 0 .instr none,
   .prom 0 ⟨lbY, 1, 0⟩, .st 0 (.store lbY 1 [.reg 8] [.reg 5]) (some 2), .st 0 .instr none,
   .st 1 (.load lbY 2 1 [.reg 6]) none]

/-- A's continuation: hart 1 finishes its load and its store fulfils ts 1. -/
def pwrAcont : List MEvt :=
  [.st 1 (.regW 5 [.ldres]) none, .st 1 .instr none,
   .st 1 (.store lbX 1 [.reg 8] [.reg 7]) (some 1), .st 1 .instr none]

/-- The alternative prefix of B: step (4) reads ts 0 (value 0). -/
def pwrPreAlt : List MEvt :=
  [.prom 1 ⟨lbX, 1, 1⟩,
   .st 0 (.load lbX 1 1 [.reg 6]) none, .st 0 (.regW 5 [.ldres]) none, .st 0 .instr none,
   .prom 0 ⟨lbY, 1, 0⟩, .st 0 (.store lbY 1 [.reg 8] [.reg 5]) (some 2), .st 0 .instr none,
   .st 1 (.load lbY 0 0 [.reg 6]) none]

/-- B's continuation of the alternative prefix: hart 1 passes the fence and its store fulfils ts 1. -/
def pwrBcontAlt : List MEvt :=
  [.st 1 (.regW 5 [.ldres]) none, .st 1 .instr none,
   .st 1 (.fence true false false true) none, .st 1 .instr none,
   .st 1 (.store lbX 1 [.reg 8] [.reg 7]) (some 1), .st 1 .instr none]

theorem not_noProm_of {c : MCfg} {i : Nat} {h : MHart} (hh : c.hs[i]? = some h) (hp : h.prom ≠ []) :
    ¬ noProm c := fun hnp => hp (hnp i h hh)

/-! ## 2. A: the prefix extends -/

/-- **A's power-off prefix extends**: a run of `pwrA` from its initial configuration with an outstanding promise
(hart 1 owes ts 1), in which both harts' first loads return 1, and a continuation reaching no outstanding promise. -/
theorem pwrA_extendable :
    ∃ c₁, mSteps pwrA (mInit pwrA) pwrPre c₁ ∧ ¬ noProm c₁ ∧
      (MRun.mk pwrPre).obsLoad 0 0 = some 1 ∧ (MRun.mk pwrPre).obsLoad 1 0 = some 1 ∧
      ∃ c, mSteps pwrA c₁ pwrAcont c ∧ noProm c := by
  refine ⟨?c1, ?run1, ?np1, rfl, rfl, ?c, ?run2, ?np2⟩
  case run1 =>
    refine .step _ _ _ _ _ (.promise _ 1 _ _ rfl rfl (by decide) (by decide)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl
      (.load _ _ _ _ _ _ ⟨rfl, writesIn_empty (by decide)⟩)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.regW _ _ _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.promise _ 0 _ _ rfl rfl (by decide) (by decide)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl
      (.store _ _ _ _ _ _ _ (by decide) rfl (by decide) (by decide))) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl
      (.load _ _ _ _ _ _ ⟨rfl, writesIn_empty (by decide)⟩)) ?_
    exact .refl _
  case run2 =>
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.regW _ _ _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl
      (.store _ _ _ _ _ _ _ (by decide) rfl (by decide) (by decide))) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    exact .refl _
  case np1 => exact not_noProm_of (i := 1) rfl (List.cons_ne_nil _ _)
  case np2 => exact noProm_of rfl

/-! ## 3. B: no continuation -/

/-- Bookkeeping labels (the only ones a queue of `pwrB`'s hart 1 holds). -/
def isBook : MLab → Bool
  | .instr => true
  | .regW _ _ => true
  | _ => false

/-- Hart 1's invariant: it owes ts 1, `vrOld ≥ 2`, it is past its load, past the fence `vwNew ≥ 2`, and its queue
holds bookkeeping labels only. -/
def InvH (h : MHart) : Prop :=
  1 ∈ h.prom ∧ 2 ≤ h.ws.vrOld ∧ 1 ≤ h.fr.pc ∧ (2 ≤ h.fr.pc → 2 ≤ h.ws.vwNew) ∧ h.fr.q.all isBook = true

/-- The configuration invariant: hart 1 exists and satisfies `InvH`. -/
def Inv1 (c : MCfg) : Prop := ∃ h, c.hs[1]? = some h ∧ InvH h

theorem go1_some {f fr' : MFront} {regs : List Nat} {pc : Nat} {labs : List MLab} {l : MLab}
    (h : go1 f regs pc labs l = some fr') : ∃ rest, labs = l :: rest ∧ fr' = ⟨pc, regs, rest⟩ := by
  cases labs with
  | nil => simp [go1] at h
  | cons l0 rest =>
    simp only [go1] at h
    split at h
    · rename_i hl
      subst hl
      cases h
      exact ⟨rest, rfl, rfl⟩
    · cases h

theorem instrNext_store {P : MProg} {n : Nat} {f fr' : MFront} {rs2 rs1 off : Nat} {l : MLab}
    (h : instrNext P n f (.store rs2 rs1 off) l = some fr') :
    ∃ b v asrc vsrc, l = .store b v asrc vsrc ∧ fr' = ⟨f.pc + 1, f.regs, [.instr]⟩ := by
  cases l with
  | store b v asrc vsrc =>
    refine ⟨b, v, asrc, vsrc, rfl, ?_⟩
    simp only [instrNext] at h
    split at h
    · cases h
    · split at h
      · cases h
        rfl
      · cases h
  | _ => all_goals (simp only [instrNext] at h; try (split at h <;> cases h))

/-- One step of hart 1 preserves `InvH`. -/
theorem invH_step {h : MHart} {l : MLab} {f' : MFront} {log : List MMsg} {ots : Option Nat} {ws' : MSt}
    {prom' : List Nat} (hI : InvH h) (hn : mNext pwrB 1 h.fr l = some f')
    (hm : mMem pwrB log 1 h.prom h.ws l ots ws' prom') : InvH ⟨f', ws', prom'⟩ := by
  obtain ⟨⟨pc, regs, q⟩, ws, prom⟩ := h
  obtain ⟨hp, hr, h1, h2, hq⟩ := hI
  dsimp only at hp hr h1 h2 hq hn hm
  cases q with
  | cons l0 rest =>
    have hn' : (if l = l0 then some (MFront.mk pc regs rest) else none) = some f' := hn
    split at hn'
    · rename_i hl
      subst hl
      cases hn'
      simp only [List.all_cons, Bool.and_eq_true] at hq
      obtain ⟨hl, hrest⟩ := hq
      cases hm <;> first
        | (simp [isBook] at hl; done)
        | exact ⟨hp, hr, h1, h2, hrest⟩
    · cases hn'
  | nil =>
    obtain rfl | rfl | hpc : pc = 1 ∨ pc = 2 ∨ 3 ≤ pc := by omega
    · -- the fence
      have hn' : go1 ⟨1, regs, []⟩ regs (1 + 1) [.fence true false false true, .instr] l = some f' := hn
      obtain ⟨rest, hl, rfl⟩ := go1_some hn'
      injection hl with hl1 hl2
      subst hl1 hl2
      cases hm
      refine ⟨hp, hr, Nat.le_add_left 1 1, fun _ => ?_, rfl⟩
      show 2 ≤ max ws.vwNew (max ws.vrOld 0)
      omega
    · -- the store: its pre-view is `≥ vwNew ≥ 2`, so it fulfils a timestamp `≠ 1`
      have hn' : instrNext pwrB 3 ⟨2, regs, []⟩ (.store 7 8 0) l = some f' := hn
      obtain ⟨b, v, asrc, vsrc, rfl, rfl⟩ := instrNext_store hn'
      cases hm with
      | store _ _ _ _ ts _ _ _ hpre =>
        have hw := h2 (Nat.le_refl 2)
        simp only [stPre] at hpre
        refine ⟨List.mem_filter.2 ⟨hp, ?_⟩, hr, Nat.le_add_left 1 2, fun _ => hw, rfl⟩
        simp only [bne_iff_ne, ne_eq]
        omega
    · -- past the text
      have h3 : (pwrB.prog 1)[pc]? = none := List.getElem?_eq_none (by show 3 ≤ pc; exact hpc)
      simp [mNext, h3] at hn

theorem getElem?_set_of {l : List MHart} {i : Nat} {x h : MHart} (hh : l[i]? = some h) :
    (l.set i x)[i]? = some x := by
  apply List.getElem?_set_self
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · exact hlt
  · rw [List.getElem?_eq_none hge] at hh
    cases hh

/-- Every step of `pwrB` preserves `Inv1`. -/
theorem inv1_step {c c' : MCfg} {e : MEvt} (hs : mStep pwrB c e c') (hI : Inv1 c) : Inv1 c' := by
  obtain ⟨h1, hh1, hI1⟩ := hI
  cases hs with
  | promise i h m hh _ _ _ =>
    by_cases hi : i = 1
    · subst hi
      rw [hh] at hh1
      cases hh1
      obtain ⟨hp, hr, ha, hb, hq⟩ := hI1
      exact ⟨_, getElem?_set_of hh, List.mem_cons_of_mem _ hp, hr, ha, hb, hq⟩
    · exact ⟨h1, by rw [List.getElem?_set_ne hi]; exact hh1, hI1⟩
  | state i h l ots fr' ws' prom' hh hn hm =>
    by_cases hi : i = 1
    · subst hi
      rw [hh] at hh1
      cases hh1
      exact ⟨_, getElem?_set_of hh, invH_step hI1 hn hm⟩
    · exact ⟨h1, by rw [List.getElem?_set_ne hi]; exact hh1, hI1⟩

theorem inv1_steps {c c' : MCfg} {es : List MEvt} (hs : mSteps pwrB c es c') (hI : Inv1 c) : Inv1 c' := by
  induction hs with
  | refl => exact hI
  | step _ _ _ _ _ h1 _ ih => exact ih (inv1_step h1 hI)

theorem Inv1.not_noProm {c : MCfg} (hI : Inv1 c) : ¬ noProm c := by
  obtain ⟨h, hh, hp, -⟩ := hI
  intro hnp
  rw [hnp 1 h hh] at hp
  exact List.not_mem_nil hp

/-- The prefix is a run of `pwrB` reaching a configuration satisfying `Inv1`. -/
theorem pwrB_pre : ∃ c₁, mSteps pwrB (mInit pwrB) pwrPre c₁ ∧ Inv1 c₁ := by
  refine ⟨?c1, ?run, ?inv⟩
  case run =>
    refine .step _ _ _ _ _ (.promise _ 1 _ _ rfl rfl (by decide) (by decide)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl
      (.load _ _ _ _ _ _ ⟨rfl, writesIn_empty (by decide)⟩)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.regW _ _ _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.promise _ 0 _ _ rfl rfl (by decide) (by decide)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl
      (.store _ _ _ _ _ _ _ (by decide) rfl (by decide) (by decide))) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl
      (.load _ _ _ _ _ _ ⟨rfl, writesIn_empty (by decide)⟩)) ?_
    exact .refl _
  case inv => exact ⟨_, rfl, by decide, by decide, by decide, by decide, rfl⟩

/-- **B's power-off prefix is a dead end**: the same prefix is a run of `pwrB` with an outstanding promise in which
both harts' first loads return 1, and NO continuation reaches a configuration with no outstanding promise. -/
theorem pwrB_dead :
    ∃ c₁, mSteps pwrB (mInit pwrB) pwrPre c₁ ∧ ¬ noProm c₁ ∧
      (MRun.mk pwrPre).obsLoad 0 0 = some 1 ∧ (MRun.mk pwrPre).obsLoad 1 0 = some 1 ∧
      ∀ evs₂ c, mSteps pwrB c₁ evs₂ c → ¬ noProm c := by
  obtain ⟨c₁, hrun, hI⟩ := pwrB_pre
  exact ⟨c₁, hrun, hI.not_noProm, rfl, rfl, fun _ _ hs => (inv1_steps hs hI).not_noProm⟩

/-! ## 4. B: the alternative prefix extends -/

/-- **B's alternative prefix extends**: with hart 1's load reading ts 0 (value 0), the prefix of `pwrB` (with an
outstanding promise) has a continuation reaching no outstanding promise. -/
theorem pwrB_alt_extendable :
    ∃ c₁, mSteps pwrB (mInit pwrB) pwrPreAlt c₁ ∧ ¬ noProm c₁ ∧
      (MRun.mk pwrPreAlt).obsLoad 0 0 = some 1 ∧ (MRun.mk pwrPreAlt).obsLoad 1 0 = some 0 ∧
      ∃ c, mSteps pwrB c₁ pwrBcontAlt c ∧ noProm c := by
  refine ⟨?c1, ?run1, ?np1, rfl, rfl, ?c, ?run2, ?np2⟩
  case run1 =>
    refine .step _ _ _ _ _ (.promise _ 1 _ _ rfl rfl (by decide) (by decide)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl
      (.load _ _ _ _ _ _ ⟨rfl, writesIn_empty (by decide)⟩)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.regW _ _ _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.promise _ 0 _ _ rfl rfl (by decide) (by decide)) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl
      (.store _ _ _ _ _ _ _ (by decide) rfl (by decide) (by decide))) ?_
    refine .step _ _ _ _ _ (.state _ 0 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl
      (.load _ _ _ _ _ _ ⟨rfl, writesIn_empty (by decide)⟩)) ?_
    exact .refl _
  case run2 =>
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.regW _ _ _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.fence _ _ _ _ _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl
      (.store _ _ _ _ _ _ _ (by decide) rfl (by decide) (by decide))) ?_
    refine .step _ _ _ _ _ (.state _ 1 _ _ _ _ _ _ rfl rfl (.instr _ _)) ?_
    exact .refl _
  case np1 => exact not_noProm_of (i := 1) rfl (List.cons_ne_nil _ _)
  case np2 => exact noProm_of rfl

end Weak.Mini.Mach
