/-
MachCSL: the standard two-slot frame of the kernel's leaf functions
(`addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp); addi s0,sp,16` ...
`ld ra,8(sp); ld s0,0(sp); addi sp,sp,16; ret`), as two derived rules over
`kctx`, and the normalisation tactics the whole-function proofs use.  No
symbolic execution here: the rules are chained.

Inside a function body every context is `(k.pushed 2).withRegs R` (`k` the
caller's context, `R` the current map), which is what the tactics
normalise to; reads become map applications, decided on literal indices.
-/
import MachCSL.WpSmodeRules
import MachCSL.CallConv


namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- A two-slot frame at `sp` holding `ra` and `s0`. -/
def frame2 [CurCtx] (sp ra s0 : BitVec 64) : IProp GF := iprop%
  wordPointsTo (sp + 0xFFFFFFFFFFFFFFF8#64) 8 (DFrac.own 1) ra ∗
  wordPointsTo (sp + 0xFFFFFFFFFFFFFFF0#64) 8 (DFrac.own 1) s0

theorem KCtx.sp_eq (k : KCtx) : k.sp = k.regs 2#5 := rfl

/-- The immediates of the two-slot frame. -/
theorem imm_m16 : BitVec.signExtend 64 4080#12 = -(8#64 * BitVec.ofNat 64 2) := by
  simp only [BitVec.reduceSignExtend, BitVec.reduceMul, BitVec.reduceNeg]
theorem imm_p16 : BitVec.signExtend 64 16#12 = 8#64 * BitVec.ofNat 64 2 := by
  simp only [BitVec.reduceSignExtend, BitVec.reduceMul]

/-- Normalise: contexts to `(k.pushed m).withRegs R`, reads to map
applications decided on literal indices, the instruction lengths, literal
arithmetic; optionally with extra lemmas, optionally at a hypothesis.
Uses `hsie`/`htier` if present. -/
syntax "k_norm" : tactic
syntax "k_norm" " [" term,* "]" : tactic
syntax "k_norm" " at " ident : tactic
syntax "k_norm" " [" term,* "]" " at " ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| k_norm) => `(tactic| k_norm [])
  | `(tactic| k_norm at $h:ident) => `(tactic| k_norm [] at $h:ident)
  | `(tactic| k_norm [$extra:term,*]) => do
    let lems ← extra.getElems.mapM fun l => `(Lean.Parser.Tactic.simpLemma| $l:term)
    `(tactic| try simp only [KCtx.push_eq, KCtx.setReg_withRegs, KCtx.withRegs_withRegs, KCtx.rget_withRegs',
      KCtx.sp_withRegs, KCtx.sp_eq, RegMap.set_apply,
      KCtx.pushed_regs, KCtx.pushed_sie, KCtx.pushed_avail, KCtx.pushed_noff, KCtx.pushed_intena,
      KCtx.pushed_locks, KCtx.pushed_tier, KCtx.pushed_root, KCtx.pushed_proc,
      KCtx.withRegs_regs, KCtx.withRegs_sie, KCtx.withRegs_avail, KCtx.withRegs_noff, KCtx.withRegs_intena,
      KCtx.withRegs_locks, KCtx.withRegs_tier, KCtx.withRegs_root, KCtx.withRegs_proc,
      KCtx.pushOff_withRegs, KCtx.popOff_withRegs, KCtx.pushOff_pushed, KCtx.popOff_pushed, KCtx.popOff_pushOff,
      KCtx.pushOff_sie, KCtx.pushOff_tier, KCtx.pushOff_proc, KCtx.pushOff_avail, KCtx.pushOff_noff, KCtx.pushOff_intena,
      KCtx.pushOff_locks, KCtx.pushOff_root, KCtx.pushOff_regs, KCtx.pushOff_sp,
      KCtx.popOff_sie, KCtx.popOff_tier, KCtx.popOff_proc, KCtx.popOff_avail, KCtx.popOff_noff, KCtx.popOff_intena,
      KCtx.popOff_locks, KCtx.popOff_root, KCtx.popOff_regs, KCtx.popOff_sp,
      KCtx.withRegs_withLocks, KCtx.pushed_withLocks, KCtx.pushOff_withLocks, KCtx.popOff_withLocks,
      KCtx.withLocks_withLocks, KCtx.setReg_withLocks, KCtx.rget_withLocks, KCtx.withLocks_self,
      KCtx.withLocks_regs, KCtx.withLocks_sie, KCtx.withLocks_avail, KCtx.withLocks_noff, KCtx.withLocks_intena,
      KCtx.withLocks_locks, KCtx.withLocks_tier, KCtx.withLocks_root, KCtx.withLocks_proc, KCtx.sp_withLocks,
      BitVec.reduceEq, ite_true, ite_false, instrLen,
      BitVec.sub_eq_add_neg, BitVec.reduceNeg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.zero_add, BitVec.reduceMul, BitVec.reduceOfNat, BitVec.reduceSignExtend, BitVec.reduceSetWidth,
      BitVec.reduceExtractLsb', BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceNot,
      BitVec.reduceShiftLeft, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Bool.false_eq_true, hsie, htier, $lems,*])
  | `(tactic| k_norm [$extra:term,*] at $h:ident) => do
    let lems ← extra.getElems.mapM fun l => `(Lean.Parser.Tactic.simpLemma| $l:term)
    `(tactic| try simp only [KCtx.push_eq, KCtx.setReg_withRegs, KCtx.withRegs_withRegs, KCtx.rget_withRegs',
      KCtx.sp_withRegs, KCtx.sp_eq, RegMap.set_apply,
      KCtx.pushed_regs, KCtx.pushed_sie, KCtx.pushed_avail, KCtx.pushed_noff, KCtx.pushed_intena,
      KCtx.pushed_locks, KCtx.pushed_tier, KCtx.pushed_root, KCtx.pushed_proc,
      KCtx.withRegs_regs, KCtx.withRegs_sie, KCtx.withRegs_avail, KCtx.withRegs_noff, KCtx.withRegs_intena,
      KCtx.withRegs_locks, KCtx.withRegs_tier, KCtx.withRegs_root, KCtx.withRegs_proc,
      KCtx.pushOff_withRegs, KCtx.popOff_withRegs, KCtx.pushOff_pushed, KCtx.popOff_pushed, KCtx.popOff_pushOff,
      KCtx.pushOff_sie, KCtx.pushOff_tier, KCtx.pushOff_proc, KCtx.pushOff_avail, KCtx.pushOff_noff, KCtx.pushOff_intena,
      KCtx.pushOff_locks, KCtx.pushOff_root, KCtx.pushOff_regs, KCtx.pushOff_sp,
      KCtx.popOff_sie, KCtx.popOff_tier, KCtx.popOff_proc, KCtx.popOff_avail, KCtx.popOff_noff, KCtx.popOff_intena,
      KCtx.popOff_locks, KCtx.popOff_root, KCtx.popOff_regs, KCtx.popOff_sp,
      KCtx.withRegs_withLocks, KCtx.pushed_withLocks, KCtx.pushOff_withLocks, KCtx.popOff_withLocks,
      KCtx.withLocks_withLocks, KCtx.setReg_withLocks, KCtx.rget_withLocks, KCtx.withLocks_self,
      KCtx.withLocks_regs, KCtx.withLocks_sie, KCtx.withLocks_avail, KCtx.withLocks_noff, KCtx.withLocks_intena,
      KCtx.withLocks_locks, KCtx.withLocks_tier, KCtx.withLocks_root, KCtx.withLocks_proc, KCtx.sp_withLocks,
      BitVec.reduceEq, ite_true, ite_false, instrLen,
      BitVec.sub_eq_add_neg, BitVec.reduceNeg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.zero_add, BitVec.reduceMul, BitVec.reduceOfNat, BitVec.reduceSignExtend, BitVec.reduceSetWidth,
      BitVec.reduceExtractLsb', BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceNot,
      BitVec.reduceShiftLeft, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Bool.false_eq_true, hsie, htier, $lems,*] at $h:ident)

/-- One instruction: apply its rule (written with `?hs ?ht` for the
interrupt/tier facts) with the pattern `[- $Hk $Hpc]` (frame the
context, clock and pc, carry the rest); normalise (optionally with extra
lemmas), frame the rest, strip the later, land on this hart (interrupts
off).  Side goals other than `hs`/`ht` (RAM range, alignment) are
left for the caller, after the main goal. -/
syntax "k_step" term:max " $$ " specPat : tactic
syntax "k_step" term:max " $$ " specPat " with " "[" term,* "]" : tactic
syntax "k_step" term:max " from " term:max ident " $$ " specPat : tactic
syntax "k_step" term:max " from " term:max ident " $$ " specPat " with " "[" term,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| k_step $rule:term $$ $pat:specPat) => `(tactic| k_step $rule:term $$ $pat:specPat with [])
  | `(tactic| k_step $rule:term $$ $pat:specPat with [$extra,*]) =>
    `(tactic| (iapply $rule:term $$ $pat:specPat
               rotate_right 1
               iframe #
               k_norm [$extra,*]
               iframe
               inext
               k_norm [$extra,*]
               iapply wpNext_off_intro
               case hs => k_norm
               case ht => k_norm))

/-- `k_code code HT`: discharge the leading `instr` conjuncts of the goal, each
by `code` (a proof of `instr ...` from the persistent text hypothesis `HT`,
e.g. `(text_instr _ _ _ _ rfl rfl) Htext`), in subgoals; stops at the first
conjunct that is not an instruction.  Use it after the rest of a
multi-instruction lemma's premise has been framed. -/
syntax "k_code" term:max ident : tactic
macro_rules
  | `(tactic| k_code $code:term $ht:ident) =>
    `(tactic| repeat (isplitr; · iapply $code:term; iexact $ht:ident))

set_option hygiene false in
/-- `k_step rule from code HT $$ pat`: as `k_step`, with the rule's `instr`
premises (one per instruction of the rule) derived from the text `HT`
(`code : text ⊢ instr ...`) in subgoals under the `iapply`, so the code facts
never sit in the context. -/
macro_rules
  | `(tactic| k_step $rule:term from $code:term $ht:ident $$ $pat:specPat) =>
    `(tactic| k_step $rule:term from $code:term $ht:ident $$ $pat:specPat with [])
  | `(tactic| k_step $rule:term from $code:term $ht:ident $$ $pat:specPat with [$extra,*]) =>
    `(tactic| (iapply $rule:term $$ $pat:specPat
               rotate_right 1
               k_code $code:term $ht:ident
               iframe #
               k_norm [$extra,*]
               iframe
               inext
               k_norm [$extra,*]
               iapply wpNext_off_intro
               case hs => k_norm
               case ht => k_norm))

set_option maxHeartbeats 4000000 in
/-- The standard prologue at `pc`: push two slots, save `ra`/`s0`, `s0 := sp₀`. -/
theorem wp_prologue2 [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (hK : 2 ≤ k.avail) :
    instr (GF := GF) pc true (instruction.ITYPE (4080#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instr (GF := GF) (pc + 2#64) true (instruction.STORE (8#12, regidx.Regidx 1#5, regidx.Regidx 2#5, 8)) ∗
    instr (GF := GF) (pc + 4#64) true (instruction.STORE (0#12, regidx.Regidx 8#5, regidx.Regidx 2#5, 8)) ∗
    instr (GF := GF) (pc + 6#64) true (instruction.ITYPE (16#12, regidx.Regidx 2#5, regidx.Regidx 8#5, iop.ADDI)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ (kctx cpu ((k.pushed 2).withRegs
          ((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64)).set 8#5 (k.regs 2#5))) -∗
        pcIs cpu (pc + 8#64) -∗
        frame2 (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) -∗ wpLoop cpu)
    ⊢ wpLoop cpu := by
  iintro ⟨#Hi0, #Hi2, #Hi4, #Hi6, Hk, Hpc, HΦ⟩
  k_step (wp_s_push cpu _ ?hs ?ht pc true 4080#12 2 hK imm_m16) $$ [- $Hk $Hpc]
  iintro Hk Hpc Hframe
  irevert Hframe
  stack_cells
  iintro ⟨⟨%w₁, Hf8⟩, ⟨%w₂, Hf16⟩, _⟩
  k_step (wp_s_sd cpu _ ?hs ?ht (pc + 2#64) true 8#12 2#5 1#5 w₁) $$ [- $Hk $Hpc]
  iintro Hk Hpc Hf8
  k_step (wp_s_sd cpu _ ?hs ?ht (pc + 4#64) true 0#12 2#5 8#5 w₂) $$ [- $Hk $Hpc]
  iintro Hk Hpc Hf16
  k_step (wp_s_addi cpu _ ?hs ?ht (pc + 6#64) true 16#12 8#5 2#5 (by decide)) $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_norm
  iapply HΦ $$ Hk Hpc [Hf8 Hf16]
  unfold frame2
  iframe

set_option maxHeartbeats 4000000 in
/-- The standard epilogue at `pc`: restore `ra`/`s0`, pop, return.  The body
left the context at `(k.pushed 2).withRegs R` with `sp` untouched. -/
theorem wp_epilogue2 [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (hK : 2 ≤ k.avail) (R : RegMap)
    (hR2 : R 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64) (ra s0 : BitVec 64) :
    instr (GF := GF) pc true (instruction.LOAD (8#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 8)) ∗
    instr (GF := GF) (pc + 2#64) true (instruction.LOAD (0#12, regidx.Regidx 2#5, regidx.Regidx 8#5, false, 8)) ∗
    instr (GF := GF) (pc + 4#64) true (instruction.ITYPE (16#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instr (GF := GF) (pc + 6#64) true (instruction.JALR (0#12, regidx.Regidx 1#5, regidx.Regidx 0#5)) ∗
    kctx cpu ((k.pushed 2).withRegs R) ∗ pcIs cpu pc ∗ frame2 (k.regs 2#5) ra s0 ∗
    ▷ (kctx cpu (k.withRegs (((R.set 1#5 ra).set 8#5 s0).set 2#5 (k.regs 2#5))) -∗
        pcIs cpu (jumpPc ra) -∗ wpLoop cpu)
    ⊢ wpLoop cpu := by
  unfold frame2
  iintro ⟨#Hi0, #Hi2, #Hi4, #Hi6, Hk, Hpc, ⟨Hf8, Hf16⟩, HΦ⟩
  k_step (wp_s_ld cpu _ ?hs ?ht pc true 8#12 1#5 2#5 (by decide) (DFrac.own 1) ra)
    $$ [- $Hk $Hpc] with [hR2]
  iintro Hk Hpc Hf8
  k_step (wp_s_ld cpu _ ?hs ?ht (pc + 2#64) true 0#12 8#5 2#5 (by decide) (DFrac.own 1) s0)
    $$ [- $Hk $Hpc] with [hR2]
  iintro Hk Hpc Hf16
  ihave Hframe : stackOwn (k.regs 2#5) 2 $$ [Hf8 Hf16]
  case' _ => stack_cells; iframe
  k_step (wp_s_pop cpu _ ?hs ?ht (pc + 4#64) true 16#12 2 imm_p16) $$ [- $Hk $Hpc]
    with [KCtx.pop_pushed _ _ _ hK, hR2]
  iintro Hk Hpc
  k_step (wp_s_ret cpu _ ?hs ?ht (pc + 6#64) true 1#5) $$ [- $Hk $Hpc]
  iintro Hk Hpc
  iapply HΦ $$ Hk Hpc

/-! ## The four-slot frame with `s1` saved -/

/-- A four-slot frame at `sp` holding `ra`, `s0`, `s1` (slot `0(sp)` unused). -/
def frame4s1 [CurCtx] (sp ra s0 s1 : BitVec 64) : IProp GF := iprop%
  wordPointsTo (sp + 0xFFFFFFFFFFFFFFF8#64) 8 (DFrac.own 1) ra ∗
  wordPointsTo (sp + 0xFFFFFFFFFFFFFFF0#64) 8 (DFrac.own 1) s0 ∗
  wordPointsTo (sp + 0xFFFFFFFFFFFFFFE8#64) 8 (DFrac.own 1) s1 ∗
  ∃ w : BitVec 64, wordPointsTo (sp + 0xFFFFFFFFFFFFFFE0#64) 8 (DFrac.own 1) w

theorem imm_m32 : BitVec.signExtend 64 4064#12 = -(8#64 * BitVec.ofNat 64 4) := by
  simp only [BitVec.reduceSignExtend, BitVec.reduceMul, BitVec.reduceNeg]
theorem imm_p32 : BitVec.signExtend 64 32#12 = 8#64 * BitVec.ofNat 64 4 := by
  simp only [BitVec.reduceSignExtend, BitVec.reduceMul]

set_option maxHeartbeats 4000000 in
/-- The prologue `addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp);
addi s0,sp,32` at `pc`. -/
theorem wp_prologue4s1 [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (hK : 4 ≤ k.avail) :
    instr (GF := GF) pc true (instruction.ITYPE (4064#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instr (GF := GF) (pc + 2#64) true (instruction.STORE (24#12, regidx.Regidx 1#5, regidx.Regidx 2#5, 8)) ∗
    instr (GF := GF) (pc + 4#64) true (instruction.STORE (16#12, regidx.Regidx 8#5, regidx.Regidx 2#5, 8)) ∗
    instr (GF := GF) (pc + 6#64) true (instruction.STORE (8#12, regidx.Regidx 9#5, regidx.Regidx 2#5, 8)) ∗
    instr (GF := GF) (pc + 8#64) true (instruction.ITYPE (32#12, regidx.Regidx 2#5, regidx.Regidx 8#5, iop.ADDI)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ (kctx cpu ((k.pushed 4).withRegs
          ((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)).set 8#5 (k.regs 2#5))) -∗
        pcIs cpu (pc + 10#64) -∗
        frame4s1 (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) -∗ wpLoop cpu)
    ⊢ wpLoop cpu := by
  iintro ⟨#Hi0, #Hi2, #Hi4, #Hi6, #Hi8, Hk, Hpc, HΦ⟩
  k_step (wp_s_push cpu _ ?hs ?ht pc true 4064#12 4 hK imm_m32) $$ [- $Hk $Hpc]
  iintro Hk Hpc Hframe
  irevert Hframe
  stack_cells
  iintro ⟨⟨%w₁, Hf8⟩, ⟨%w₂, Hf16⟩, ⟨%w₃, Hf24⟩, ⟨%w₄, Hf32⟩, _⟩
  k_step (wp_s_sd cpu _ ?hs ?ht (pc + 2#64) true 24#12 2#5 1#5 w₁) $$ [- $Hk $Hpc]
  iintro Hk Hpc Hf8
  k_step (wp_s_sd cpu _ ?hs ?ht (pc + 4#64) true 16#12 2#5 8#5 w₂) $$ [- $Hk $Hpc]
  iintro Hk Hpc Hf16
  k_step (wp_s_sd cpu _ ?hs ?ht (pc + 6#64) true 8#12 2#5 9#5 w₃) $$ [- $Hk $Hpc]
  iintro Hk Hpc Hf24
  k_step (wp_s_addi cpu _ ?hs ?ht (pc + 8#64) true 32#12 8#5 2#5 (by decide)) $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_norm
  iapply HΦ $$ Hk Hpc [Hf8 Hf16 Hf24 Hf32]
  unfold frame4s1
  iframe

set_option maxHeartbeats 4000000 in
/-- The epilogue `ld ra,24(sp); ld s0,16(sp); ld s1,8(sp); addi sp,sp,32; ret`
at `pc`, from the body context `(k.pushed 4).withRegs R` (`sp` untouched). -/
theorem wp_epilogue4s1 [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (hK : 4 ≤ k.avail) (R : RegMap)
    (hR2 : R 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64) (ra s0 s1 : BitVec 64) :
    instr (GF := GF) pc true (instruction.LOAD (24#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 8)) ∗
    instr (GF := GF) (pc + 2#64) true (instruction.LOAD (16#12, regidx.Regidx 2#5, regidx.Regidx 8#5, false, 8)) ∗
    instr (GF := GF) (pc + 4#64) true (instruction.LOAD (8#12, regidx.Regidx 2#5, regidx.Regidx 9#5, false, 8)) ∗
    instr (GF := GF) (pc + 6#64) true (instruction.ITYPE (32#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instr (GF := GF) (pc + 8#64) true (instruction.JALR (0#12, regidx.Regidx 1#5, regidx.Regidx 0#5)) ∗
    kctx cpu ((k.pushed 4).withRegs R) ∗ pcIs cpu pc ∗ frame4s1 (k.regs 2#5) ra s0 s1 ∗
    ▷ (kctx cpu (k.withRegs ((((R.set 1#5 ra).set 8#5 s0).set 9#5 s1).set 2#5 (k.regs 2#5))) -∗
        pcIs cpu (jumpPc ra) -∗ wpLoop cpu)
    ⊢ wpLoop cpu := by
  unfold frame4s1
  iintro ⟨#Hi0, #Hi2, #Hi4, #Hi6, #Hi8, Hk, Hpc, ⟨Hf8, Hf16, Hf24, %w₄, Hf32⟩, HΦ⟩
  k_step (wp_s_ld cpu _ ?hs ?ht pc true 24#12 1#5 2#5 (by decide) (DFrac.own 1) ra)
    $$ [- $Hk $Hpc] with [hR2]
  iintro Hk Hpc Hf8
  k_step (wp_s_ld cpu _ ?hs ?ht (pc + 2#64) true 16#12 8#5 2#5 (by decide) (DFrac.own 1) s0)
    $$ [- $Hk $Hpc] with [hR2]
  iintro Hk Hpc Hf16
  k_step (wp_s_ld cpu _ ?hs ?ht (pc + 4#64) true 8#12 9#5 2#5 (by decide) (DFrac.own 1) s1)
    $$ [- $Hk $Hpc] with [hR2]
  iintro Hk Hpc Hf24
  ihave Hframe : stackOwn (k.regs 2#5) 4 $$ [Hf8 Hf16 Hf24 Hf32]
  case' _ => stack_cells; iframe
  k_step (wp_s_pop cpu _ ?hs ?ht (pc + 6#64) true 32#12 4 imm_p32) $$ [- $Hk $Hpc]
    with [KCtx.pop_pushed _ _ _ hK, hR2]
  iintro Hk Hpc
  k_step (wp_s_ret cpu _ ?hs ?ht (pc + 8#64) true 1#5) $$ [- $Hk $Hpc]
  iintro Hk Hpc
  iapply HΦ $$ Hk Hpc

end MachCSL
