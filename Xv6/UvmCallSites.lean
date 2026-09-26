/-
Xv6: the call-site facts `uvmcreate` and `uvmcopy` share (the `uc_` helpers):
the interrupt-state rewrites, the `beqz` branch on a known value, and
`kalloc`'s contract as a rule.
-/
import Xv6.SpecKalloc

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedSectionVars false

theorem uc_withSpie_withSpie (k : KCtx) (a b c d : Bool) :
    (k.withSpie a b).withSpie c d = k.withSpie c d := rfl

theorem uc_pushed_withSpie (k : KCtx) (m : Nat) (a b : Bool) :
    (k.pushed m).withSpie a b = (k.withSpie a b).pushed m := rfl

/-- A branch on a value known to be zero: taken. -/
theorem uc_beq_zero {α : Type} (x : BitVec 64) (h : x = 0#64) (p q : α) :
    (if bcond bop.BEQ x 0#64 then p else q) = p := by
  rw [if_pos (by simp only [bcond, beq_iff_eq]; exact h)]

/-- A branch on a value known to be nonzero: not taken. -/
theorem uc_beq_ne {α : Type} (x : BitVec 64) (h : x ≠ 0#64) (p q : α) :
    (if bcond bop.BEQ x 0#64 then p else q) = q := by
  rw [if_neg (by simp only [bcond, beq_iff_eq]; exact h)]

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

set_option maxHeartbeats 1000000 in
/-- `kalloc`'s contract as a rule. -/
theorem uc_kalloc_call (KAL : KALLOC) [CurCtx] (c : CPU) (k' : KCtx)
    (γl : GName) (γk : KmemNames) (on : Option Nat)
    (hnoff : k'.noff + 1 < 2 ^ 31) (hK : 14 ≤ k'.avail) (hlk : "kmem" ∉ k'.locks) :
    kctx c k' ∗ pcIs c KA.«kalloc» ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗
    kallocAvail γk on ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      kallocPost γk on (R' 10#5) -∗ ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := KAL.wp_kalloc (hlc := hlc) (GF := GF) c k' γl γk on hnoff hK hlk
  unfold wp_kalloc_body at h
  simp only [kallocAddr] at h
  exact h

end

end Xv6
