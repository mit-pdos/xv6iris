/-
Proof of `strlen`'s specification (`SpecStrlen.STRLEN`): the prologue and
epilogue rules, the loop by induction on the remaining length, the
instruction rules chained -- no symbolic execution.
-/
import MachCSL.WpSmodeFrame
import Xv6.SpecStrlen
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-! ## Arithmetic facts -/

/-- A zero-extended byte is zero iff the byte is. -/
theorem setWidth64_eq_zero (b : BitVec 8) : (BitVec.setWidth 64 b = 0#64) ↔ b = 0#8 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod] at this
    have hb := b.isLt
    rw [Nat.mod_eq_of_lt (by omega)] at this
    simpa using this
  · intro h; subst h; rfl

/-- `bnez` on a zero-extended byte. -/
theorem ite_bne_byte {α : Type} (b : BitVec 8) (x y : α) :
    (if bcond bop.BNE (BitVec.setWidth 64 b) 0#64 then x else y) = if b = 0#8 then y else x := by
  by_cases hb : b = 0#8
  · subst hb; simp [bcond]
  · have : BitVec.setWidth 64 b ≠ 0#64 := fun h => hb ((setWidth64_eq_zero b).mp h)
    simp [bcond, hb, this]

/-- `beqz` on a zero-extended byte. -/
theorem ite_beq_byte {α : Type} (b : BitVec 8) (x y : α) :
    (if bcond bop.BEQ (BitVec.setWidth 64 b) 0#64 then x else y) = if b = 0#8 then x else y := by
  by_cases hb : b = 0#8
  · subst hb; simp [bcond]
  · have : BitVec.setWidth 64 b ≠ 0#64 := fun h => hb ((setWidth64_eq_zero b).mp h)
    simp [bcond, hb, this]

/-- `subw a0, a3, a0` with `a3 = s + n`, `a0 = s` yields `n` (`n < 2^31`). -/
theorem subw_len (s : BitVec 64) (n : Nat) (hn : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (s + BitVec.ofNat 64 n) + -BitVec.extractLsb' 0 32 s) =
      BitVec.ofNat 64 n := by
  rw [← BitVec.sub_eq_add_neg]
  have h32 : BitVec.extractLsb' 0 32 (s + BitVec.ofNat 64 n) - BitVec.extractLsb' 0 32 s = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftRight_zero, Nat.reducePow]
    omega
  rw [h32]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; rw [Nat.mod_eq_of_lt (by omega)]
    simp; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega : n < 4294967296), Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]

theorem cstrAt_len {bs : List (BitVec 8)} {n : Nat} (h : cstrAt bs n) : n < bs.length :=
  (List.getElem?_eq_some_iff.mp h.2).1

/-! ## The loop -/

set_option maxHeartbeats 4000000 in
/-- One iteration of the loop at `80000e16` (`mv a3,a5; addi a5,a5,1;
lbu a4,-1(a5); bnez a4,e16`): with `a5 = s + i`, reads byte `i`, lands at
`e16` if it is nonzero and at `e20` otherwise. -/
theorem strlen_iter {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (kb : KCtx) (hsie : kb.sie = false) (htier : kb.tier = KTier.bare)
    (s : BitVec 64) (dq : DFrac) (bs : List (BitVec 8)) (i : Nat) (b : BitVec 8) (hb : bs[i]? = some b)
    (R : RegMap) (h15 : R 15#5 = s + BitVec.ofNat 64 i) :
    kernelText ∗ kctx cpu (kb.withRegs R) ∗ pcIs cpu 0x80000e16#64 ∗ byteBuf s dq bs ∗
    (kctx cpu (kb.withRegs (((R.set 13#5 (s + BitVec.ofNat 64 i)).set 15#5 (s + BitVec.ofNat 64 i + 1#64)).set 14#5
        (BitVec.setWidth 64 b))) -∗
      pcIs cpu (if b = 0#8 then 0x80000e20#64 else 0x80000e16#64) -∗ byteBuf s dq bs -∗
      wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨#HT, Hk, Hpc, Hbuf, HΦ⟩
  -- mv a3,a5
  k_step (wp_s_add cpu _ ?hs ?ht 0x80000e16#64 true 13#5 0#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
    with [h15]
  iintro Hk Hpc
  -- addi a5,a5,1
  k_step (wp_s_addi cpu _ ?hs ?ht 0x80000e18#64 true 1#12 15#5 15#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
    with [h15]
  iintro Hk Hpc
  -- lbu a4,-1(a5)
  icases byteBuf_acc s dq bs i b hb $$ Hbuf with ⟨Hb, Hclose⟩
  k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000e1a#64 false 4095#12 14#5 15#5 (by decide) dq b) from (text_instr _ _ _ _ rfl rfl) HT
    $$ [- $Hk $Hpc] with [h15]
  iintro Hk Hpc Hb
  ihave Hbuf := Hclose $$ Hb
  -- bnez a4,e16
  k_step (wp_s_branch cpu _ ?hs ?ht 0x80000e1e#64 true 8184#13 14#5 0#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) HT
    $$ [- $Hk $Hpc] with [h15, ite_bne_byte]
  case htgt => k_tgt
  iintro Hk Hpc
  iapply HΦ $$ Hk Hpc Hbuf

set_option maxHeartbeats 4000000 in
/-- The loop from `e16` with `a5 = s + i` (`1 ≤ i ≤ n`) runs to `e20` with
`a3 = s + n`; only `a3`, `a4`, `a5` change. -/
theorem strlen_loop {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (kb : KCtx) (hsie : kb.sie = false) (htier : kb.tier = KTier.bare)
    (s : BitVec 64) (dq : DFrac) (bs : List (BitVec 8)) (n : Nat) (hcstr : cstrAt bs n)
    (d : Nat) :
    ∀ (i : Nat) (_ : 1 ≤ i) (_ : i ≤ n) (_ : n - i = d) (R : RegMap) (_ : R 15#5 = s + BitVec.ofNat 64 i),
    kernelText ∗ kctx cpu (kb.withRegs R) ∗ pcIs cpu 0x80000e16#64 ∗ byteBuf s dq bs ∗
    (∀ R' : RegMap, kctx cpu (kb.withRegs R') -∗ pcIs cpu 0x80000e20#64 -∗ byteBuf s dq bs -∗
      ⌜R' 13#5 = s + BitVec.ofNat 64 n ∧ ∀ r, r ≠ 13#5 → r ≠ 14#5 → r ≠ 15#5 → R' r = R r⌝ -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  have hn := cstrAt_len hcstr
  induction d with
  | zero =>
    intro i hi1 hin hd R h15
    have hi : i = n := by omega
    subst hi
    iintro ⟨#HT, Hk, Hpc, Hbuf, HΦ⟩
    iapply (strlen_iter cpu kb hsie htier s dq bs i 0#8 hcstr.2 R h15)
    iframe
    iframe #
    simp only [ite_true]
    iintro Hk Hpc Hbuf
    iapply HΦ $$ %_ Hk Hpc Hbuf
    ipureintro
    refine ⟨by simp [RegMap.set_apply], ?_⟩
    intro r h13 h14 h15'
    simp [RegMap.set_apply, h13, h14, h15']
  | succ d ih =>
    intro i hi1 hin hd R h15
    have hlt : i < n := by omega
    obtain ⟨b, hb, hb0⟩ := hcstr.1 i hlt
    iintro ⟨#HT, Hk, Hpc, Hbuf, HΦ⟩
    iapply (strlen_iter cpu kb hsie htier s dq bs i b hb R h15)
    iframe
    iframe #
    simp only [hb0, ite_false]
    iintro Hk Hpc Hbuf
    iapply (ih (i + 1) (by omega) (by omega) (by omega)
      (((R.set 13#5 (s + BitVec.ofNat 64 i)).set 15#5 (s + BitVec.ofNat 64 i + 1#64)).set 14#5 (BitVec.setWidth 64 b))
      (by simp only [RegMap.set_apply, BitVec.reduceEq, ite_true, ite_false]; rw [BitVec.ofNat_add, ← BitVec.add_assoc]))
    iframe
    iframe #
    iintro %R' Hk Hpc Hbuf %⟨h13, hother⟩
    iapply HΦ $$ %R' Hk Hpc Hbuf
    ipureintro
    refine ⟨h13, ?_⟩
    intro r hr13 hr14 hr15
    rw [hother r hr13 hr14 hr15]
    simp [RegMap.set_apply, hr13, hr14, hr15]

/-! ## The function -/

set_option maxHeartbeats 4000000 in
theorem strlen_proof : STRLEN := ⟨fun cpu k bs n dq hsie htier hK hcstr hn31 => by
  unfold wp_strlen_body
  have hn := cstrAt_len hcstr
  iintro ⟨Hk, #Htext, Hpc, Hbuf, HΦ⟩
  -- the spec's continuation, at this hart
  simp only [strlenAddr, KernelSyms.«strlen»]
  k_norm
  ihave HΦ := wpNext_off _ _ _ $$ HΦ
  -- prologue
  iapply (wp_prologue2 cpu k hsie htier 0x80000e04#64 hK)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc Hframe
  -- lbu a5,0(a0)
  obtain ⟨b0, hb0, hb0ne⟩ : ∃ b0, bs[0]? = some b0 ∧ (0 < n → b0 ≠ 0#8) := by
    by_cases h0 : 0 < n
    · obtain ⟨b, hb, hbne⟩ := hcstr.1 0 h0; exact ⟨b, hb, fun _ => hbne⟩
    · have : n = 0 := by omega
      subst this; exact ⟨0#8, hcstr.2, fun h => absurd h (by omega)⟩
  icases byteBuf_acc (k.regs 10#5) dq bs 0 b0 hb0 $$ Hbuf with ⟨Hb, Hclose⟩
  k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000e0c#64 false 0#12 15#5 10#5 (by decide) dq b0) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc]
  k_norm
  iintro Hk Hpc Hb
  ihave Hbuf := Hclose $$ Hb
  -- beqz a5,e2c
  k_step (wp_s_branch cpu _ ?hs ?ht 0x80000e10#64 true 28#13 15#5 0#5 (by decide) bop.BEQ ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [ite_beq_byte]
  case htgt => k_tgt
  iintro Hk Hpc
  by_cases hn0 : n = 0
  · -- the empty string: a0 := 0, jump to the epilogue
    subst hn0
    have hb0z : b0 = 0#8 := by
      have := hcstr.2; rw [hb0] at this; exact (Option.some.inj this)
    subst hb0z
    simp only [ite_true]
    k_step (wp_s_addi cpu _ ?hs ?ht 0x80000e2c#64 true 0#12 10#5 0#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    iintro Hk Hpc
    k_step (wp_s_j cpu _ ?hs ?ht 0x80000e2e#64 true 2097142#21 ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    case htgt => k_tgt
    iintro Hk Hpc
    iapply (wp_epilogue2 cpu k hsie htier 0x80000e24#64 hK _ ?hR2 (k.regs 1#5) (k.regs 8#5)) $$ [- $Hk $Hpc]
    rotate_right 1
    k_code (text_instr _ _ _ _ rfl rfl) Htext
    k_norm
    iframe
    inext
    iintro Hk Hpc
    iapply HΦ $$ %_ Hk Hpc Hbuf
    ipureintro
    constructor
    · unfold calleeSaved; simp [RegMap.set_apply]
    · simp [RegMap.set_apply]
    case hR2 => simp [RegMap.set_apply]
  · -- a nonempty string: into the loop
    have hb0ne' : b0 ≠ 0#8 := hb0ne (by omega)
    simp only [hb0ne', ite_false]
    k_step (wp_s_addi cpu _ ?hs ?ht 0x80000e12#64 false 1#12 15#5 10#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    iintro Hk Hpc
    iapply (strlen_loop cpu (k.pushed 2) (by k_norm) (by k_norm) (k.regs 10#5) dq bs n hcstr (n - 1) 1
      (by omega) (by omega) rfl _ ?h15) $$ [- $Hk $Hpc]
    rotate_right 1
    iframe
    iframe #
    case h15 => simp [RegMap.set_apply]
    iintro %R' Hk Hpc Hbuf %⟨h13, hother⟩
    have h10 : R' 10#5 = k.regs 10#5 := by
      rw [hother 10#5 (by decide) (by decide) (by decide)]; simp [RegMap.set_apply]
    -- subw a0,a3,a0
    k_step (wp_s_subw cpu _ ?hs ?ht 0x80000e20#64 false 10#5 13#5 10#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [h13, h10, subw_len (k.regs 10#5) n hn31]
    iintro Hk Hpc
    have hR2 : R' 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64 := by
      rw [hother 2#5 (by decide) (by decide) (by decide)]; simp [RegMap.set_apply]
    iapply (wp_epilogue2 cpu k hsie htier 0x80000e24#64 hK _ ?hR2 (k.regs 1#5) (k.regs 8#5)) $$ [- $Hk $Hpc]
    rotate_right 1
    k_code (text_instr _ _ _ _ rfl rfl) Htext
    k_norm
    iframe
    inext
    iintro Hk Hpc
    iapply HΦ $$ %_ Hk Hpc Hbuf
    ipureintro
    have hcs : ∀ r : BitVec 5, r ≠ 13#5 → r ≠ 14#5 → r ≠ 15#5 → r ≠ 10#5 → r ≠ 2#5 → r ≠ 8#5 →
        R' r = k.regs r := by
      intro r h13' h14' h15' h10' h2' h8'
      rw [hother r h13' h14' h15']
      simp [RegMap.set_apply, h10', h2', h8', h15']
    constructor
    · unfold calleeSaved
      simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
      exact ⟨hcs 9#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 18#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 19#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 20#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 21#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 22#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 23#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 24#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 25#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 26#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcs 27#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
    · simp [RegMap.set_apply, h13, h10, subw_len (k.regs 10#5) n hn31]
    case hR2 => simp [RegMap.set_apply, hR2]⟩

end Xv6
