/-
MachCSL: frames of many slots.

`wp_s_push m` hands out `stackOwn sp m`, the `m` words below the caller's
`sp` as a list.  A function with a large frame (printk: 24 slots) addresses
them individually, so the list is opened into named cells here, one per
offset, together with the RAM/alignment facts each `sd`/`ld` needs.
GENERATED for 24 slots.
-/
import MachCSL.CallConv

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

theorem slot8_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFF8#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFF8#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFF8#64).toNat = sp.toNat - 8 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot16_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFF0#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFF0#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFF0#64).toNat = sp.toNat - 16 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot24_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFE8#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFE8#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFE8#64).toNat = sp.toNat - 24 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot32_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFE0#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFE0#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFE0#64).toNat = sp.toNat - 32 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot40_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFD8#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFD8#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFD8#64).toNat = sp.toNat - 40 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot48_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFD0#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFD0#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFD0#64).toNat = sp.toNat - 48 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot56_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFC8#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFC8#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFC8#64).toNat = sp.toNat - 56 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot64_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFC0#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFC0#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFC0#64).toNat = sp.toNat - 64 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot72_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFB8#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFB8#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFB8#64).toNat = sp.toNat - 72 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot80_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFB0#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFB0#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFB0#64).toNat = sp.toNat - 80 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot88_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFA8#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFA8#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFA8#64).toNat = sp.toNat - 88 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot96_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFFA0#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFFA0#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFFA0#64).toNat = sp.toNat - 96 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot104_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF98#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF98#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF98#64).toNat = sp.toNat - 104 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot112_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF90#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF90#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF90#64).toNat = sp.toNat - 112 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot120_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF88#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF88#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF88#64).toNat = sp.toNat - 120 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot128_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF80#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF80#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF80#64).toNat = sp.toNat - 128 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot136_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF78#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF78#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF78#64).toNat = sp.toNat - 136 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot144_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF70#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF70#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF70#64).toNat = sp.toNat - 144 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot152_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF68#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF68#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF68#64).toNat = sp.toNat - 152 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot160_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF60#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF60#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF60#64).toNat = sp.toNat - 160 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot168_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF58#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF58#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF58#64).toNat = sp.toNat - 168 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot176_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF50#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF50#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF50#64).toNat = sp.toNat - 176 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot184_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF48#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF48#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF48#64).toNat = sp.toNat - 184 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

theorem slot192_ok (sp : BitVec 64) (hf : stackFacts sp 24) :
    inRam (sp + 0xFFFFFFFFFFFFFF40#64) 8 ∧ (sp + 0xFFFFFFFFFFFFFF40#64).toNat % 8 = 0 := by
  unfold stackFacts ramBase ramEnd at hf
  have h : (sp + 0xFFFFFFFFFFFFFF40#64).toNat = sp.toNat - 192 := by bv_omega
  unfold inRam ramBase ramEnd; rw [h]; omega

/-- A 24-slot frame, opened into its cells (`wi` at `sp - 8(i+1)`). -/
theorem stackOwn_24_cases [CurCtx] (sp : BitVec 64) :
    stackOwn (GF := GF) sp 24 ⊢
      ⌜stackFacts sp 24⌝ ∗ ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : BitVec 64),
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFF8#64) 8 (DFrac.own 1) w0 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFF0#64) 8 (DFrac.own 1) w1 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFE8#64) 8 (DFrac.own 1) w2 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFE0#64) 8 (DFrac.own 1) w3 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFD8#64) 8 (DFrac.own 1) w4 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFD0#64) 8 (DFrac.own 1) w5 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFC8#64) 8 (DFrac.own 1) w6 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFC0#64) 8 (DFrac.own 1) w7 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFB8#64) 8 (DFrac.own 1) w8 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFB0#64) 8 (DFrac.own 1) w9 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFA8#64) 8 (DFrac.own 1) w10 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFFA0#64) 8 (DFrac.own 1) w11 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF98#64) 8 (DFrac.own 1) w12 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF90#64) 8 (DFrac.own 1) w13 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF88#64) 8 (DFrac.own 1) w14 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF80#64) 8 (DFrac.own 1) w15 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF78#64) 8 (DFrac.own 1) w16 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF70#64) 8 (DFrac.own 1) w17 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF68#64) 8 (DFrac.own 1) w18 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF60#64) 8 (DFrac.own 1) w19 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF58#64) 8 (DFrac.own 1) w20 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF50#64) 8 (DFrac.own 1) w21 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF48#64) 8 (DFrac.own 1) w22 ∗
        bytesPointsTo (sp + 0xFFFFFFFFFFFFFF40#64) 8 (DFrac.own 1) w23 := by
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
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFF8#64) 8 (DFrac.own 1) w0 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFF0#64) 8 (DFrac.own 1) w1 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFE8#64) 8 (DFrac.own 1) w2 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFE0#64) 8 (DFrac.own 1) w3 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFD8#64) 8 (DFrac.own 1) w4 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFD0#64) 8 (DFrac.own 1) w5 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFC8#64) 8 (DFrac.own 1) w6 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFC0#64) 8 (DFrac.own 1) w7 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFB8#64) 8 (DFrac.own 1) w8 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFB0#64) 8 (DFrac.own 1) w9 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFA8#64) 8 (DFrac.own 1) w10 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFFA0#64) 8 (DFrac.own 1) w11 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF98#64) 8 (DFrac.own 1) w12 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF90#64) 8 (DFrac.own 1) w13 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF88#64) 8 (DFrac.own 1) w14 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF80#64) 8 (DFrac.own 1) w15 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF78#64) 8 (DFrac.own 1) w16 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF70#64) 8 (DFrac.own 1) w17 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF68#64) 8 (DFrac.own 1) w18 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF60#64) 8 (DFrac.own 1) w19 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF58#64) 8 (DFrac.own 1) w20 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF50#64) 8 (DFrac.own 1) w21 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF48#64) 8 (DFrac.own 1) w22 ∗
    bytesPointsTo (sp + 0xFFFFFFFFFFFFFF40#64) 8 (DFrac.own 1) w23 ⊢ stackOwn (GF := GF) sp 24 := by
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
