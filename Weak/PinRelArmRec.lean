/-
Weak: **W11-C2′ (a3) relArmed — from W4's record to the hart-local trace, and the assembly**
(`PROGRESS-relArmed.md`).  Lean-only.

* `jtrace j r`: agent `j`'s own (program state, label) steps of a record; `WbPrimed.armFold` of
  `j` IS the hart-local fold `afold` of its trace (`armFoldEq`).
* The steps from a cycle boundary (`.pure`): a PLIC write, a parked fence, or the boundary step
  `LInstr` — none consumes the flag, a parked arming fence arms it (`pureStepAm`, `bdSegArm`).

Every helper is `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmStore
import Weak.WeakRobustBlocks

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel KernelPinsDef MachOfPf RelSiteProvPc

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp PinDataflow

/-! ## 1. The agent's trace of a record -/

/-- Agent `j`'s own steps of a record, with its program state before each. -/
def jtrace (j : Nat) : List PfRec → List (Pexv6 × Wlabel)
  | [] => []
  | x :: r =>
    if x.ag = j then
      match x.pre.pcAgs[j]? with
      | some ag => (ag.paSt, x.lb) :: jtrace j r
      | none => jtrace j r
    else jtrace j r

/-- **The fold is the hart-local fold** (header). -/
theorem armFoldEq (j : Nat) : ∀ (r : List PfRec) (b : Bool),
    WbPrimed.armFold j r b = afold (jtrace j r) b := by
  intro r
  induction r with
  | nil => intro b; rfl
  | cons x r ih =>
    intro b
    simp only [WbPrimed.armFold, jtrace, WbPrimed.armAt]
    by_cases h : x.ag = j
    · subst h
      simp only [↓reduceIte]
      cases hl : x.pre.pcAgs[x.ag]? with
      | none => simp only [Option.elim]; exact ih b
      | some ag => simp only [Option.elim, afold]; exact ih _
    · simp only [h, ↓reduceIte]; exact ih b

/-! ## 2. Steps from a cycle boundary -/

theorem cfgAgPinSet (rs : RegFile) (mm bb : Bool) (h : cfgAg rs) : cfgAg (pinSet rs mm bb) := by
  unfold pinSet
  split
  · exact cfgAgSet rs _ _ h rfl
  · exact cfgAgSet rs _ _ h rfl

/-- **A step from a cycle boundary** (header): the boundary step `LInstr` (no parked fence) into a
fresh cycle, or a parked fence / PLIC write staying at the boundary; the latter keep the
configuration, and an armed fold (or a pending arming fence) stays armed (or pending). -/
theorem pureStepAm (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch)
    (d : Efab) (l : Wlabel) (p1 : Pexv6) (d1 : Efab)
    (h : pstepEv (.PHart cpu (.pure ()) rs fn ib) d l p1 d1) :
    (l = LInstr ∧ fn = none ∧ ∃ tick, p1 = .PHart cpu (riscvStep tick) rs none ibNone) ∨
    (∃ rs1 fn1, p1 = .PHart cpu (.pure ()) rs1 fn1 ib ∧ (RbootAll rs → RbootAll rs1) ∧
      (cfgAg rs → cfgAg rs1) ∧
      ∀ w b, (b = true ∨ parkArms fn) → (WbPrimed.armStep w l b = true ∨ parkArms fn1)) := by
  cases p1 with
  | PDisk dp => exact (show False from h).elim
  | PHart cpu1 m1 rs1 fn1 ib1 =>
  obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := h
  rcases hh with ⟨H, -⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := H
      refine Or.inr ⟨rs, none, rfl, id, id, fun w b hb => Or.inl ?_⟩
      rcases hb with hb | ⟨pr', pw', sr', sw', e, hps⟩
      · exact armStepFence _ _ _ _ _ _ hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨-, rfl, -, rfl⟩ := e
        exact armStepFenceArms _ _ _ _ _ _ hps
    | none =>
      obtain ⟨tick, rfl, rfl, rfl, rfl, -, rfl, -⟩ := H
      exact Or.inl ⟨rfl, rfl, tick, rfl⟩
  · obtain ⟨mm, b, k, -, rfl, rfl, rfl, -, rfl, -, rfl⟩ := H
    refine Or.inr ⟨_, _, rfl, ?_, cfgAgPinSet rs mm b, fun w b0 hb => ?_⟩
    · intro hrb
      show RbootAll (pinSet rs mm b)
      unfold pinSet
      split
      · exact rbootAllSet rs _ _ hrb trivial
      · exact rbootAllSet rs _ _ hrb trivial
    · rw [armStepNeutral _ _ _ rfl rfl]; exact hb

/-- A fresh cycle is not at its boundary. -/
theorem riscvStepNotPure (tick : Bool) (x : Unit) : riscvStep tick ≠ FreeM.pure x := by
  unfold riscvStep
  rw [uc_tryStep_eq]
  unfold ucPrelude
  simp only [bind_assoc]
  intro h
  cases h

/-- A step from a boundary is neither a fetch nor a plain store. -/
theorem pureStepLab (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch)
    (d : Efab) (l : Wlabel) (p1 : Pexv6) (d1 : Efab)
    (h : pstepEv (.PHart cpu (.pure ()) rs fn ib) d l p1 d1) :
    isFeLab l = false ∧ RelSiteProvPc.lbStore l = false := by
  cases p1 with
  | PDisk dp => exact (show False from h).elim
  | PHart cpu1 m1 rs1 fn1 ib1 =>
  obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := h
  rcases hh with ⟨H, -⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, -⟩ := H
      exact ⟨rfl, rfl⟩
    | none =>
      obtain ⟨tick, rfl, -⟩ := H
      exact ⟨rfl, rfl⟩
  · obtain ⟨mm, b, k, -, rfl, -⟩ := H
    exact ⟨rfl, rfl⟩

/-- Every pre-state of a trace segment is at a boundary. -/
def bdSeg (t : List (Pexv6 × Wlabel)) : Prop := ∀ q, q ∈ t.map Prod.fst → atPureS q

/-- **A boundary segment** (header): along steps from boundaries, either the run stays at a
boundary (the configuration kept, an armed fold or a pending arming fence kept), or it took the
boundary step into a fresh cycle (the configuration kept; an armed start gives an armed fold). -/
theorem bdSegArm : ∀ (p : Pexv6) (t : List (Pexv6 × Wlabel)) (p' : Pexv6), htr p t p' → bdSeg t →
    ∀ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (a : Bool),
      p = .PHart cpu (.pure ()) rs fn ib → RbootAll rs → cfgAg rs →
      (∃ rs' fn' ib', p' = .PHart cpu (.pure ()) rs' fn' ib' ∧ RbootAll rs' ∧ cfgAg rs' ∧
        ((a = true ∨ parkArms fn) → (afold t a = true ∨ parkArms fn'))) ∨
      (∃ tick rs', p' = .PHart cpu (riscvStep tick) rs' none ibNone ∧ RbootAll rs' ∧ cfgAg rs' ∧
        ((a = true ∨ parkArms fn) → afold t a = true)) := by
  intro p t p' h
  induction h with
  | nil p =>
    intro _ cpu rs fn ib a hp hrb hcfg
    exact Or.inl ⟨rs, fn, ib, hp, hrb, hcfg, id⟩
  | @cons p l p1 t p2 hs hr ih =>
    intro hbd cpu rs fn ib a hp hrb hcfg
    subst hp
    obtain ⟨d, d', hst⟩ := hs
    rcases pureStepAm cpu rs fn ib d l p1 d' hst with ⟨rfl, rfl, tick, rfl⟩ |
      ⟨rs1, fn1, rfl, hrb1, hcfg1, harm⟩
    · -- the boundary step: the rest of the segment is empty
      cases hr with
      | nil =>
        refine Or.inr ⟨tick, rs, rfl, hrb, hcfg, fun ha => ?_⟩
        show afold [] (WbPrimed.armStep _ LInstr a) = true
        rw [armStepNeutral _ _ _ rfl rfl]
        rcases ha with h | ⟨_, _, _, _, e, _⟩
        · exact h
        · cases e
      | cons _ _ =>
        exfalso
        obtain ⟨c1, r1, f1, i1, e⟩ := hbd _ (List.mem_cons_of_mem _ List.mem_cons_self)
        injection e with _ e2
        exact riscvStepNotPure tick () e2
    · have hbd' : bdSeg t := fun q hq => hbd q (List.mem_cons_of_mem _ hq)
      rcases ih hbd' cpu rs1 fn1 ib (WbPrimed.armStep (WbPrimed.pwbEv _) l a) rfl (hrb1 hrb)
          (hcfg1 hcfg) with ⟨rs', fn', ib', e, h1, h2, h3⟩ | ⟨tick, rs', e, h1, h2, h3⟩
      · exact Or.inl ⟨rs', fn', ib', e, h1, h2, fun ha => h3 (harm _ _ ha)⟩
      · refine Or.inr ⟨tick, rs', e, h1, h2, fun ha => ?_⟩
        rcases h3' : harm (WbPrimed.pwbEv _) a ha with h | h
        · exact h3 (Or.inl h)
        · exact h3 (Or.inr h)

theorem htrSnoc : ∀ (p : Pexv6) (t : List (Pexv6 × Wlabel)) (q : Pexv6), htr p t q →
    ∀ (l : Wlabel) (q' : Pexv6) (d d' : Efab), pstepEv q d l q' d' → htr p (t ++ [(q, l)]) q' := by
  intro p t q h
  induction h with
  | nil p => intro l q' d d' hs; exact .cons ⟨d, d', hs⟩ (.nil _)
  | cons hs hr ih => intro l q' d d' hs'; exact .cons hs (ih l q' d d' hs')

/-! ## 3. The record's projection onto one agent -/

section rec
variable {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
  {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}

/-- **The projection** (header): along a record, agent `j`'s trace up to entry `n` is a hart-local
trace from its initial state to its state at entry `n`'s pre-configuration. -/
theorem htrPrefix (j : Nat) {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec}
    {cN : Wpcfg Pexv6 Efab} (h : contRC fok fcutT c st r cN) :
    ∀ (n : Nat) (x : PfRec) (ag0 ag : Wpagent Pexv6), r[n]? = some x → c.pcAgs[j]? = some ag0 →
      x.pre.pcAgs[j]? = some ag → htr ag0.paSt (jtrace j (r.take n)) ag.paSt := by
  induction h with
  | nil => intro n x _ _ hx; simp at hx
  | cons c c' st i l k r cN hs _ _ _ _ _ ih =>
    intro n x ag0 ag hx h0 hag
    obtain ⟨agi, p', d', ws', hli, hps, -, -, hset⟩ := wpPfStepInv pstepEv pclsEv i l c c' hs
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      simp only [List.take_zero, jtrace]
      rw [h0] at hag; cases hag; exact .nil _
    | succ n =>
      simp only [List.getElem?_cons_succ] at hx
      simp only [List.take_succ_cons, jtrace]
      by_cases hij : i = j
      · subst hij
        have e : agi = ag0 := by rw [hli] at h0; exact Option.some.inj h0
        subst e
        simp only [↓reduceIte, hli]
        have h0' : c'.pcAgs[i]? = some ⟨p', ws', agi.paProm⟩ := by
          rw [hset]
          have hlt : i < c.pcAgs.length := (List.getElem?_eq_some_iff.1 hli).1
          simp [List.getElem?_set, hlt]
        exact .cons ⟨_, _, hps⟩ (ih n x _ ag hx h0' hag)
      · simp only [hij, ↓reduceIte]
        have h0' : c'.pcAgs[j]? = some ag0 := by
          rw [wpPfStepFrame pstepEv pclsEv i l c c' j hs (Ne.symm hij)]; exact h0
        exact ih n x ag0 ag hx h0' hag

/-- Every entry of a record is a step of its agent from its pre-configuration. -/
theorem contRStepAt {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec}
    {cN : Wpcfg Pexv6 Efab} (h : contRC fok fcutT c st r cN) :
    ∀ (n : Nat) (x : PfRec), r[n]? = some x → ∃ c', wpPfStep pstepEv pclsEv x.ag x.lb x.pre c' := by
  induction h with
  | nil => intro n x hx; simp at hx
  | cons c c' st i l k r cN hs _ _ _ _ _ ih =>
    intro n x hx
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx; exact ⟨c', hs⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hx
      exact ih n x hx

end rec

end PinRelArm
end Weak
