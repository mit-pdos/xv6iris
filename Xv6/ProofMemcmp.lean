/-
Proof of `memcmp`'s specification (`SpecMemcmp.MEMCMP`): the prologue and
epilogue rules, the loop by induction on the remaining length, the
instruction rules chained -- no symbolic execution.
-/
import MachCSL.WpSmodeFrame
import Xv6.SpecMemcmp
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-! ## Arithmetic facts -/

theorem setWidth64_inj (a b : BitVec 8) : BitVec.setWidth 64 a = BitVec.setWidth 64 b ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    have ha := a.isLt; have hb := b.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · intro h; rw [h]

/-- `bne` on two zero-extended bytes. -/
theorem ite_bne_bytes {α : Type} (a b : BitVec 8) (x y : α) :
    (if bcond bop.BNE (BitVec.setWidth 64 a) (BitVec.setWidth 64 b) then x else y) = if a = b then y else x := by
  by_cases h : a = b
  · subst h; simp [bcond]
  · have : BitVec.setWidth 64 a ≠ BitVec.setWidth 64 b := fun h' => h ((setWidth64_inj a b).mp h')
    simp [bcond, h, this]

/-- `bne` on two words. -/
theorem ite_bne {α : Type} (x y : BitVec 64) (p q : α) :
    (if bcond bop.BNE x y then p else q) = if x = y then q else p := by
  by_cases h : x = y <;> simp [bcond, h]

/-- Two offsets from the same base agree iff the offsets do (no wrap). -/
theorem ptr_add_eq (s : BitVec 64) (i n : Nat) (hi : i < 2 ^ 64) (hn : n < 2 ^ 64) :
    (s + BitVec.ofNat 64 i = s + BitVec.ofNat 64 n) ↔ i = n := by
  constructor
  · intro h
    have h' : BitVec.ofNat 64 i = BitVec.ofNat 64 n := (BitVec.add_right_inj s).mp h
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hn] at this
  · intro h; rw [h]

/-- The same, for the incremented pointer as the rules leave it. -/
theorem ptr_next_eq (s : BitVec 64) (i n : Nat) (hi : i + 1 < 2 ^ 64) (hn : n < 2 ^ 64) :
    (s + (BitVec.ofNat 64 i + 1#64) = s + BitVec.ofNat 64 n) ↔ i + 1 = n := by
  rw [← BitVec.ofNat_add]
  exact ptr_add_eq s (i + 1) n hi hn

/-- `beqz` on a small count. -/
theorem ite_beq_ofNat {α : Type} (n : Nat) (hn : n < 2 ^ 64) (x y : α) :
    (if bcond bop.BEQ (BitVec.ofNat 64 n) 0#64 then x else y) = if n = 0 then x else y := by
  by_cases h : n = 0
  · subst h; simp [bcond]
  · have : BitVec.ofNat 64 n ≠ 0#64 := by
      intro h'; have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt hn] at this; simp at this; exact h this
    simp [bcond, h, this]

/-- The `slli`/`srli` round trip that truncates the count to 32 bits. -/
theorem shl_shr32 (n : Nat) (hn : n < 2 ^ 32) : (BitVec.ofNat 64 n <<< 32) >>> 32 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- `subw a0, a5, a4` on two zero-extended bytes: their difference as a C `int`. -/
theorem subw_bytes (a b : BitVec 8) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (BitVec.setWidth 64 a) + -BitVec.extractLsb' 0 32 (BitVec.setWidth 64 b)) =
      BitVec.ofInt 64 ((a.toNat : Int) - b.toNat) := by
  rw [← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth,
    BitVec.toNat_ofInt, Nat.shiftRight_zero, Nat.reducePow, Nat.reduceSub]
  have ha := a.isLt; have hb := b.isLt
  split <;> rename_i hc <;> simp only [decide_eq_true_eq] at hc <;> omega

/-! ## The loop -/

set_option maxHeartbeats 4000000 in
/-- One iteration of the loop at `80000cb2` (`lbu a5,0(a0); lbu a4,0(a1);
bne a5,a4,cca`): with `a0 = s1 + i`, `a1 = s2 + i`, reads both bytes `i`
and lands at `cca` if they differ, at `cbe` otherwise. -/
theorem memcmp_iter {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (kb : KCtx) (hsie : kb.sie = false) (htier : kb.tier = KTier.bare)
    (s1 s2 : BitVec 64) (dq1 dq2 : DFrac) (bs1 bs2 : List (BitVec 8)) (i : Nat) (a b : BitVec 8)
    (ha : bs1[i]? = some a) (hb : bs2[i]? = some b)
    (hram1 : inRam (s1 + BitVec.ofNat 64 i) 1) (hram2 : inRam (s2 + BitVec.ofNat 64 i) 1)
    (R : RegMap) (h10 : R 10#5 = s1 + BitVec.ofNat 64 i) (h11 : R 11#5 = s2 + BitVec.ofNat 64 i) :
    kernelText ∗ kctx cpu (kb.withRegs R) ∗ pcIs cpu 0x80000cb2#64 ∗
    byteBuf s1 dq1 bs1 ∗ byteBuf s2 dq2 bs2 ∗
    (kctx cpu (kb.withRegs ((R.set 15#5 (BitVec.setWidth 64 a)).set 14#5 (BitVec.setWidth 64 b))) -∗
      pcIs cpu (if a = b then 0x80000cbe#64 else 0x80000cca#64) -∗
      byteBuf s1 dq1 bs1 -∗ byteBuf s2 dq2 bs2 -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨#HT, Hk, Hpc, Hbuf1, Hbuf2, HΦ⟩
  -- lbu a5,0(a0)
  icases byteBuf_acc s1 dq1 bs1 i a ha $$ Hbuf1 with ⟨Hb1, Hclose1⟩
  k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000cb2#64 false 0#12 15#5 10#5 (by decide) dq1 a ?hram) from (text_instr _ _ _ _ rfl rfl) HT
    $$ [- $Hk $Hpc] with [h10]
  case hram => k_norm [h10]; exact hram1
  iintro Hk Hpc Hb1
  ihave Hbuf1 := Hclose1 $$ Hb1
  -- lbu a4,0(a1)
  icases byteBuf_acc s2 dq2 bs2 i b hb $$ Hbuf2 with ⟨Hb2, Hclose2⟩
  k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000cb6#64 false 0#12 14#5 11#5 (by decide) dq2 b ?hram) from (text_instr _ _ _ _ rfl rfl) HT
    $$ [- $Hk $Hpc] with [h11]
  case hram => k_norm [h11]; exact hram2
  iintro Hk Hpc Hb2
  ihave Hbuf2 := Hclose2 $$ Hb2
  -- bne a5,a4,cca
  k_step (wp_s_branch cpu _ ?hs ?ht 0x80000cba#64 false 16#13 15#5 14#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) HT
    $$ [- $Hk $Hpc] with [ite_bne_bytes]
  case htgt => k_tgt
  iintro Hk Hpc
  iapply HΦ $$ Hk Hpc Hbuf1 Hbuf2

/-- What the loop leaves in the registers: either the first differing
pair, at `cca`, or agreement on all `n` bytes, at `cc6`. -/
def memcmpLoopPost {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (bs1 bs2 : List (BitVec 8)) (n : Nat) (R' : RegMap) : IProp GF := iprop%
  (pcIs cpu 0x80000cca#64 ∗
    ⌜∃ k a b, k < n ∧ (∀ j, j < k → bs1[j]? = bs2[j]?) ∧ bs1[k]? = some a ∧ bs2[k]? = some b ∧ a ≠ b ∧
      R' 15#5 = BitVec.setWidth 64 a ∧ R' 14#5 = BitVec.setWidth 64 b⌝) ∨
  (pcIs cpu 0x80000cc6#64 ∗ ⌜∀ j, j < n → bs1[j]? = bs2[j]?⌝)

set_option maxHeartbeats 4000000 in
/-- The loop from `cb2` with `a0 = s1 + i`, `a1 = s2 + i`, `a3 = s1 + n`
(`i < n`, the first `i` bytes agreeing) runs to `cca` or `cc6`; only
`a0`, `a1`, `a4`, `a5` change. -/
theorem memcmp_loop {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (kb : KCtx) (hsie : kb.sie = false) (htier : kb.tier = KTier.bare)
    (s1 s2 : BitVec 64) (dq1 dq2 : DFrac) (bs1 bs2 : List (BitVec 8)) (n : Nat) (hn32 : n < 2 ^ 32)
    (hl1 : n ≤ bs1.length) (hl2 : n ≤ bs2.length)
    (hbuf1 : inRam s1 bs1.length) (hbuf2 : inRam s2 bs2.length) (d : Nat) :
    ∀ (i : Nat) (_ : i < n) (_ : n - i = d + 1) (_ : ∀ j, j < i → bs1[j]? = bs2[j]?) (R : RegMap)
      (_ : R 10#5 = s1 + BitVec.ofNat 64 i) (_ : R 11#5 = s2 + BitVec.ofNat 64 i)
      (_ : R 13#5 = s1 + BitVec.ofNat 64 n),
    kernelText ∗ kctx cpu (kb.withRegs R) ∗ pcIs cpu 0x80000cb2#64 ∗
    byteBuf s1 dq1 bs1 ∗ byteBuf s2 dq2 bs2 ∗
    (∀ R' : RegMap, kctx cpu (kb.withRegs R') -∗ byteBuf s1 dq1 bs1 -∗ byteBuf s2 dq2 bs2 -∗
      ⌜∀ r, r ≠ 10#5 → r ≠ 11#5 → r ≠ 14#5 → r ≠ 15#5 → R' r = R r⌝ -∗
      memcmpLoopPost cpu bs1 bs2 n R' -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  induction d with
  | zero =>
    intro i hin hd heq R h10 h11 h13
    have hi : i + 1 = n := by omega
    have ha : bs1[i]? = some bs1[i] := List.getElem?_eq_getElem (by omega)
    have hb : bs2[i]? = some bs2[i] := List.getElem?_eq_getElem (by omega)
    iintro ⟨#HT, Hk, Hpc, Hbuf1, Hbuf2, HΦ⟩
    iapply (memcmp_iter cpu kb hsie htier s1 s2 dq1 dq2 bs1 bs2 i bs1[i] bs2[i] ha hb
      (inRam_byte hbuf1 i (by omega)) (inRam_byte hbuf2 i (by omega)) R h10 h11)
    iframe
    iframe #
    iintro Hk Hpc Hbuf1 Hbuf2
    by_cases hab : bs1[i] = bs2[i]
    · simp only [hab, ite_true]
      -- addi a0,a0,1 ; addi a1,a1,1 ; bne a0,a3,cb2 (not taken: the last byte)
      k_step (wp_s_addi cpu _ ?hs ?ht 0x80000cbe#64 true 1#12 10#5 10#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
        with [h10]
      iintro Hk Hpc
      k_step (wp_s_addi cpu _ ?hs ?ht 0x80000cc0#64 true 1#12 11#5 11#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
        with [h11]
      iintro Hk Hpc
      k_step (wp_s_branch cpu _ ?hs ?ht 0x80000cc2#64 false 8176#13 10#5 13#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) HT
        $$ [- $Hk $Hpc] with [h13, ite_bne, ptr_next_eq s1 i n (by omega) (by omega), hi]
      case htgt => k_tgt
      iintro Hk Hpc
      iapply HΦ $$ %_ Hk Hbuf1 Hbuf2
      · ipureintro
        intro r h10' h11' h14' h15'
        simp [RegMap.set_apply, h10', h11', h14', h15']
      · unfold memcmpLoopPost
        iright
        iframe
        ipureintro
        intro j hj
        by_cases hji : j < i
        · exact heq j hji
        · have : j = i := by omega
          subst this
          rw [ha, hb, hab]
    · simp only [hab, ite_false]
      iapply HΦ $$ %_ Hk Hbuf1 Hbuf2
      · ipureintro
        intro r h10' h11' h14' h15'
        simp [RegMap.set_apply, h14', h15']
      · unfold memcmpLoopPost
        ileft
        iframe
        ipureintro
        exact ⟨i, bs1[i], bs2[i], hin, heq, ha, hb, hab, by simp [RegMap.set_apply], by simp [RegMap.set_apply]⟩
  | succ d ih =>
    intro i hin hd heq R h10 h11 h13
    have hi : i + 1 < n := by omega
    have ha : bs1[i]? = some bs1[i] := List.getElem?_eq_getElem (by omega)
    have hb : bs2[i]? = some bs2[i] := List.getElem?_eq_getElem (by omega)
    iintro ⟨#HT, Hk, Hpc, Hbuf1, Hbuf2, HΦ⟩
    iapply (memcmp_iter cpu kb hsie htier s1 s2 dq1 dq2 bs1 bs2 i bs1[i] bs2[i] ha hb
      (inRam_byte hbuf1 i (by omega)) (inRam_byte hbuf2 i (by omega)) R h10 h11)
    iframe
    iframe #
    iintro Hk Hpc Hbuf1 Hbuf2
    by_cases hab : bs1[i] = bs2[i]
    · simp only [hab, ite_true]
      k_step (wp_s_addi cpu _ ?hs ?ht 0x80000cbe#64 true 1#12 10#5 10#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
        with [h10]
      iintro Hk Hpc
      k_step (wp_s_addi cpu _ ?hs ?ht 0x80000cc0#64 true 1#12 11#5 11#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) HT $$ [- $Hk $Hpc]
        with [h11]
      iintro Hk Hpc
      have hne : ¬ (i + 1 = n) := by omega
      k_step (wp_s_branch cpu _ ?hs ?ht 0x80000cc2#64 false 8176#13 10#5 13#5 (by decide) bop.BNE ?htgt) from (text_instr _ _ _ _ rfl rfl) HT
        $$ [- $Hk $Hpc] with [h13, ite_bne, ptr_next_eq s1 i n (by omega) (by omega), hne]
      case htgt => k_tgt
      iintro Hk Hpc
      iapply (ih (i + 1) hi (by omega)
        (fun j hj => by
          by_cases hji : j < i
          · exact heq j hji
          · have : j = i := by omega
            subst this; rw [ha, hb, hab])
        _ ?h10 ?h11 ?h13) $$ [- $Hk $Hpc]
      rotate_right 1
      iframe
      iframe #
      case h10 => simp only [RegMap.set_apply, BitVec.reduceEq, ite_true, ite_false]; rw [BitVec.ofNat_add]
      case h11 => simp only [RegMap.set_apply, BitVec.reduceEq, ite_true, ite_false]; rw [BitVec.ofNat_add]
      case h13 => simp [RegMap.set_apply, h13]
      iintro %R' Hk Hbuf1 Hbuf2 %hother Hpost
      iapply HΦ $$ %R' Hk Hbuf1 Hbuf2
      · ipureintro
        intro r h10' h11' h14' h15'
        rw [hother r h10' h11' h14' h15']
        simp [RegMap.set_apply, h10', h11', h14', h15']
      · iexact Hpost
    · simp only [hab, ite_false]
      iapply HΦ $$ %_ Hk Hbuf1 Hbuf2
      · ipureintro
        intro r h10' h11' h14' h15'
        simp [RegMap.set_apply, h14', h15']
      · unfold memcmpLoopPost
        ileft
        iframe
        ipureintro
        exact ⟨i, bs1[i], bs2[i], hin, heq, ha, hb, hab, by simp [RegMap.set_apply], by simp [RegMap.set_apply]⟩

/-! ## The function -/

set_option maxHeartbeats 4000000 in
theorem memcmp_proof : MEMCMP := ⟨fun cpu k bs1 bs2 n dq1 dq2 hsie htier hK hn hn32 hl1 hl2 hbuf1 hbuf2 => by
  unfold wp_memcmp_body
  iintro ⟨Hk, #Htext, Hpc, Hbuf1, Hbuf2, HΦ⟩
  -- the spec's continuation, at this hart
  simp only [memcmpAddr, KernelSyms.«memcmp»]
  k_norm
  ihave HΦ := wpNext_off _ _ _ $$ HΦ
  -- prologue
  iapply (wp_prologue2 cpu k hsie htier 0x80000ca0#64 hK)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  inext
  iintro Hk Hpc Hframe
  -- beqz a2,cd6
  k_step (wp_s_branch cpu _ ?hs ?ht 0x80000ca8#64 true 46#13 12#5 0#5 (by decide) bop.BEQ ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [hn, ite_beq_ofNat n (by omega)]
  case htgt => k_tgt
  iintro Hk Hpc
  by_cases hn0 : n = 0
  · -- n = 0: a0 := 0, jump to the epilogue
    simp only [hn0, ite_true]
    k_step (wp_s_addi cpu _ ?hs ?ht 0x80000cd6#64 true 0#12 10#5 0#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    iintro Hk Hpc
    k_step (wp_s_j cpu _ ?hs ?ht 0x80000cd8#64 true 2097142#21 ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    case htgt => k_tgt
    iintro Hk Hpc
    iapply (wp_epilogue2 cpu k hsie htier 0x80000cce#64 hK _ ?hR2 (k.regs 1#5) (k.regs 8#5)) $$ [- $Hk $Hpc]
    rotate_right 1
    k_code (text_instr _ _ _ _ rfl rfl) Htext
    k_norm
    iframe
    inext
    iintro Hk Hpc
    iapply HΦ $$ %_ Hk Hpc Hbuf1 Hbuf2
    ipureintro
    constructor
    · unfold calleeSaved; simp [RegMap.set_apply]
    · right
      exact ⟨fun j hj => absurd hj (by omega), by simp [RegMap.set_apply]⟩
    case hR2 => simp [RegMap.set_apply]
  · -- n > 0: truncate the count, compute the end pointer, run the loop
    simp only [hn0, ite_false]
    k_step (wp_s_slli cpu _ ?hs ?ht 0x80000caa#64 true 32#6 12#5 12#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [hn]
    iintro Hk Hpc
    k_step (wp_s_srli cpu _ ?hs ?ht 0x80000cac#64 true 32#6 12#5 12#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [shl_shr32 n hn32]
    iintro Hk Hpc
    k_step (wp_s_add cpu _ ?hs ?ht 0x80000cae#64 false 13#5 10#5 12#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    iintro Hk Hpc
    iapply (memcmp_loop cpu (k.pushed 2) (by k_norm) (by k_norm) (k.regs 10#5) (k.regs 11#5) dq1 dq2 bs1 bs2 n
      hn32 hl1 hl2 hbuf1 hbuf2 (n - 1) 0 (by omega) (by omega) (fun j hj => absurd hj (by omega)) _ ?h10 ?h11 ?h13)
      $$ [- $Hk $Hpc]
    rotate_right 1
    iframe
    iframe #
    case h10 => simp [RegMap.set_apply]
    case h11 => simp [RegMap.set_apply]
    case h13 => simp [RegMap.set_apply]
    iintro %R' Hk Hbuf1 Hbuf2 %hother
    have hcs : ∀ r : BitVec 5, r ≠ 10#5 → r ≠ 11#5 → r ≠ 12#5 → r ≠ 13#5 → r ≠ 14#5 → r ≠ 15#5 →
        r ≠ 2#5 → r ≠ 8#5 → R' r = k.regs r := by
      intro r h10' h11' h12' h13' h14' h15' h2' h8'
      rw [hother r h10' h11' h14' h15']
      simp [RegMap.set_apply, h12', h13', h2', h8']
    have hR2 : R' 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64 := by
      rw [hother 2#5 (by decide) (by decide) (by decide) (by decide)]; simp [RegMap.set_apply]
    unfold memcmpLoopPost
    iintro (⟨Hpc, %hdiff⟩ | ⟨Hpc, %heqall⟩)
    · -- the differing pair: subw a0,a5,a4, epilogue
      obtain ⟨j, a, b, hj, hpre, ha, hb, hab, h15, h14⟩ := hdiff
      k_step (wp_s_subw cpu _ ?hs ?ht 0x80000cca#64 false 10#5 15#5 14#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [h15, h14, subw_bytes a b]
      iintro Hk Hpc
      iapply (wp_epilogue2 cpu k hsie htier 0x80000cce#64 hK _ ?hR2 (k.regs 1#5) (k.regs 8#5)) $$ [- $Hk $Hpc]
      rotate_right 1
      k_code (text_instr _ _ _ _ rfl rfl) Htext
      k_norm
      iframe
      inext
      iintro Hk Hpc
      iapply HΦ $$ %_ Hk Hpc Hbuf1 Hbuf2
      ipureintro
      constructor
      · unfold calleeSaved
        simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
        exact ⟨hcs 9#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 18#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 19#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 20#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 21#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 22#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 23#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 24#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 25#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 26#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 27#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
      · left
        exact ⟨j, a, b, hj, hpre, ha, hb, hab, by simp [RegMap.set_apply]⟩
      case hR2 => simp [RegMap.set_apply, hR2]
    · -- all equal: a0 := 0, jump to the epilogue
      k_step (wp_s_addi cpu _ ?hs ?ht 0x80000cc6#64 true 0#12 10#5 0#5 (by decide)) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      iintro Hk Hpc
      k_step (wp_s_j cpu _ ?hs ?ht 0x80000cc8#64 true 6#21 ?htgt) from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      case htgt => k_tgt
      iintro Hk Hpc
      iapply (wp_epilogue2 cpu k hsie htier 0x80000cce#64 hK _ ?hR2 (k.regs 1#5) (k.regs 8#5)) $$ [- $Hk $Hpc]
      rotate_right 1
      k_code (text_instr _ _ _ _ rfl rfl) Htext
      k_norm
      iframe
      inext
      iintro Hk Hpc
      iapply HΦ $$ %_ Hk Hpc Hbuf1 Hbuf2
      ipureintro
      constructor
      · unfold calleeSaved
        simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, eq_self_iff_true, true_and, and_true]
        exact ⟨hcs 9#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 18#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 19#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 20#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 21#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 22#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 23#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 24#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 25#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 26#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hcs 27#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
      · right
        exact ⟨heqall, by simp [RegMap.set_apply]⟩
      case hR2 => simp [RegMap.set_apply, hR2]⟩

end Xv6
