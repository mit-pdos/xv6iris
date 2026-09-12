/-
MachCSL: frames of many slots.

`wp_s_push m` hands out `stackOwn sp m`, the `m` words below the caller's
`sp` as a list.  A function with a large frame (printk: 24 slots) addresses
them individually, so the list is opened into named cells here, one per
offset (each a `wordPointsTo`, carrying its own RAM/alignment facts).
GENERATED for 24 slots.
-/
import MachCSL.CallConv

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A 24-slot frame, opened into its cells (`wi` at `sp - 8(i+1)`). -/
theorem stackOwn_24_cases [CurCtx] (sp : BitVec 64) :
    stackOwn (GF := GF) sp 24 ⊢
      ⌜stackFacts sp 24⌝ ∗ ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : BitVec 64),
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFF8#64) 8 (DFrac.own 1) w0 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFF0#64) 8 (DFrac.own 1) w1 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFE8#64) 8 (DFrac.own 1) w2 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFE0#64) 8 (DFrac.own 1) w3 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFD8#64) 8 (DFrac.own 1) w4 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFD0#64) 8 (DFrac.own 1) w5 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFC8#64) 8 (DFrac.own 1) w6 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFC0#64) 8 (DFrac.own 1) w7 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFB8#64) 8 (DFrac.own 1) w8 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFB0#64) 8 (DFrac.own 1) w9 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFA8#64) 8 (DFrac.own 1) w10 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFFA0#64) 8 (DFrac.own 1) w11 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF98#64) 8 (DFrac.own 1) w12 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF90#64) 8 (DFrac.own 1) w13 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF88#64) 8 (DFrac.own 1) w14 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF80#64) 8 (DFrac.own 1) w15 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF78#64) 8 (DFrac.own 1) w16 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF70#64) 8 (DFrac.own 1) w17 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF68#64) 8 (DFrac.own 1) w18 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF60#64) 8 (DFrac.own 1) w19 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF58#64) 8 (DFrac.own 1) w20 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF50#64) 8 (DFrac.own 1) w21 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF48#64) 8 (DFrac.own 1) w22 ∗
        wordPointsTo (sp + 0xFFFFFFFFFFFFFF40#64) 8 (DFrac.own 1) w23 := by
  unfold stackOwn stackSlots
  iintro ⟨%hf, %ws, %hlen, H⟩
  match ws, hlen with
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23], _ =>
    simp only [Iris.Algebra.BigOpL.bigOpL_cons, Iris.Algebra.BigOpL.bigOpL_nil, BitVec.sub_eq_add_neg,
      BitVec.reduceMul, BitVec.reduceNeg, Nat.reduceAdd]
    icases H with ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, _⟩
    iframe H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23
    ipureintro; exact hf

theorem stackOwn_24_intro [CurCtx] (sp : BitVec 64) (hf : stackFacts sp 24) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : BitVec 64) :
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFF8#64) 8 (DFrac.own 1) w0 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFF0#64) 8 (DFrac.own 1) w1 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFE8#64) 8 (DFrac.own 1) w2 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFE0#64) 8 (DFrac.own 1) w3 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFD8#64) 8 (DFrac.own 1) w4 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFD0#64) 8 (DFrac.own 1) w5 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFC8#64) 8 (DFrac.own 1) w6 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFC0#64) 8 (DFrac.own 1) w7 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFB8#64) 8 (DFrac.own 1) w8 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFB0#64) 8 (DFrac.own 1) w9 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFA8#64) 8 (DFrac.own 1) w10 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFFA0#64) 8 (DFrac.own 1) w11 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF98#64) 8 (DFrac.own 1) w12 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF90#64) 8 (DFrac.own 1) w13 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF88#64) 8 (DFrac.own 1) w14 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF80#64) 8 (DFrac.own 1) w15 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF78#64) 8 (DFrac.own 1) w16 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF70#64) 8 (DFrac.own 1) w17 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF68#64) 8 (DFrac.own 1) w18 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF60#64) 8 (DFrac.own 1) w19 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF58#64) 8 (DFrac.own 1) w20 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF50#64) 8 (DFrac.own 1) w21 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF48#64) 8 (DFrac.own 1) w22 ∗
    wordPointsTo (sp + 0xFFFFFFFFFFFFFF40#64) 8 (DFrac.own 1) w23 ⊢ stackOwn (GF := GF) sp 24 := by
  unfold stackOwn stackSlots
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23⟩
  isplitr
  · ipureintro; exact hf
  · iexists [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23]
    simp only [Iris.Algebra.BigOpL.bigOpL_cons, Iris.Algebra.BigOpL.bigOpL_nil, BitVec.sub_eq_add_neg,
      BitVec.reduceMul, BitVec.reduceNeg, Nat.reduceAdd]
    iframe H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23
    ipureintro; rfl

end MachCSL
