/-
Weak: **the `execEff` twin of the PMP-check cone** (M4 batch 0): the SC PMP
lemmas of `Weak/ExecSC3.lean` (Rocq `RiscvTryStep` / `RiscvFetchExec`) replayed
at the instrumented interpreter, every trace LITERALLY `[]`.

Rocq: `iris/WeakPmpEff.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Everything a leaf's `WeakCert.wPEff` obligation
reaches through the fetch and the load/store path eventually runs `pmpCheck`,
so the PMP cone needs its instrumented twin.  This file is that twin and
nothing else: the SC scripts with `WeakEff`'s / `WeakEffSkel`'s composition kit
in place of `exec`'s / `execR`'s.  The pure side conditions
(`ExecSC3.pmpRangeMatch_cell`) are REUSED, since they say nothing about the
interpreter.  The whole PMP cone is register-only (`pmpReadAddrReg` reads
`pmpcfg`/`pmpaddr`, `pmpMatchAddr`/`pmpRangeMatch` are pure, `pmpCheckRWX` is
a field test, the loop touches no memory), so each conclusion carries the
EMPTY trace, not `WeakEff.quietTrace` (a quiet trace admits a zero-width write,
which `wcertStoreGen`/`_LoadGen`/`_AmoAqGen` cannot consume).

**Deviations from Rocq.**
1. NAMES: the tree's camelCase (map below); vocabulary as `Weak/ExecSC3.lean`
   (conventions and deviations 1, 3) and `Weak/WeakEffSkel.lean` deviation 1
   (`Defs.monadR R exception X` ↦ `SailME R X`, `vec_access_dec v i` ↦
   `v[i]!`, `uint x` ↦ `x.toNat`, `Z` widths ↦ `Nat`).
2. LOOPS: Rocq's `Defs.foreach_ZM_up'` (fuel `n`, start `from`) and
   `Defs.foreach_ZM_up` are lean-sail's `IntRange` `forIn` (step 1), as in
   `Weak/ExecSC2.lean` (`execRForInAllow`/`Const`): the `up'` lemmas are stated
   over the loop `IntRange.forIn'.loop range _ () i hs` from any index `i`, the
   `up` lemmas over the whole `forIn`; the body is `Int → Unit → SailME R
   (ForInStep Unit)` and "returns its vars" is "yields `()`"; the body premise
   is required only for `i ∈ range` (Rocq: every `i`; weaker premise).
3. §2: `exec_eff_pmpReadAddrReg_ex` is the corollary of the Lean-only value
   form `execEffPmpReadAddrReg` (grain 0, as `ExecSC3.execPmpReadAddrReg`).
4. §3/§4: PMP entry facts are stated at `Nat` indices (`(s.regs .pmpcfg_n)[i]!`,
   as `ExecSC3` deviation 1); the cell premise of
   `execEffPmpCheckMachineUnlocked` is
   `(bits_of_physaddr addr).toNat % 4 + (to_bits (l := 64) width).toNat ≤ 4`
   (as `ExecSC3` deviation 3).  `execEffPureCell` (Lean-only) is the
   `execEff` twin of `ExecSC3.execPureCell`.
5. §0: Rocq's two `Local Lemma`s are ordinary theorems.
6. The tactic `eff_run` (Lean-only) is the `execEff` twin of `exec_run`.
7. Rocq's `Print Assumptions` command is not a declaration (no Lean twin).

**Rocq → Lean name map.**  `wpe_exec_eff_returnM` `wpeExecEffReturnM`,
`wpe_execR_eff_returnm_fwd` `wpeExecREffReturnmFwd`,
`execR_eff_foreach_ZM_up'_allow` `execREffForInLoopAllow`,
`execR_eff_foreach_ZM_up_allow` `execREffForInAllow`,
`execR_eff_foreach_ZM_up'_const` `execREffForInLoopConst`,
`execR_eff_foreach_ZM_up_const` `execREffForInConst`,
`exec_eff_pmpReadAddrReg_ex` `execEffPmpReadAddrRegEx`,
`exec_eff_pmpMatchAddr_OFF` `execEffPmpMatchAddrOFF`,
`exec_eff_pmpCheck_machine_none` `execEffPmpCheckMachineNone`,
`exec_eff_pmpMatchAddr_machine_cell` `execEffPmpMatchAddrMachineCell`,
`exec_eff_pmpCheck_machine_unlocked` `execEffPmpCheckMachineUnlocked`,
`exec_eff_pmpCheck_machine_unlocked_ifetch4`
`execEffPmpCheckMachineUnlockedIfetch4`.  Lean-only: `execEffPmpReadAddrReg`,
`execEffPureCell`, the tactic `eff_run`.

**Dropped:** nothing (12 Rocq `Lemma`s; Lean 12 + 2 Lean-only).
-/
import Weak.WeakEffSkel
import Weak.ExecSC3

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- `exec_run` at the instrumented interpreter: the bind equations of
`execEff`/`execREff`, the register arms, and the closed-guard reductions. -/
syntax "eff_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| eff_run) => `(tactic| simp (config := { decide := true }) only [execEffBindEq, effThen,
      readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff, execEffReturnm,
      ↓reduceIte, ite_true, ite_false, Bool.false_eq_true, assert, PreSail.assert, execREffBindEq,
      execREffLiftR, execREffReturnR, execREffThrow, decide_false, decide_true, Bool.and_false,
      Bool.false_and, Bool.and_true, Bool.true_and, List.nil_append, List.append_nil])
  | `(tactic| eff_run [$ls,*]) => `(tactic| simp (config := { decide := true }) only [execEffBindEq,
      effThen, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff,
      execEffReturnm, ↓reduceIte, ite_true, ite_false, Bool.false_eq_true, assert, PreSail.assert,
      execREffBindEq, execREffLiftR, execREffReturnR, execREffThrow, decide_false, decide_true,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, List.nil_append,
      List.append_nil, $ls,*])

/-! ## 0. The two trivial twins -/

theorem wpeExecEffReturnM {X : Type} (x : X) (s : ExecSt) :
    execEff (pure x : SailM X) s = some (x, s, []) := rfl

theorem wpeExecREffReturnmFwd {R X : Type} (x : X) (s : ExecSt) :
    execREff (pure x : SailME R X) s = some (.inr x, s, []) := rfl

/-! ## 1. The two loop invariants, instrumented -/

/-- Rocq `execR_eff_foreach_ZM_up'_allow` (deviation 2): from any index, a loop
whose every iteration yields or returns `r` early, without moving the state and
with an empty trace, either finishes or returns `r`, with an empty trace. -/
theorem execREffForInLoopAllow {R : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s : ExecSt) (r : R)
    (hf : ∀ i, i ∈ range → execREff (f i ()) s = some (.inr (.yield ()), s, []) ∨
      execREff (f i ()) s = some (.inl r, s, [])) :
    ∀ (i : Int) (hs : (i - range.start) % range.step = 0),
      execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inr (), s, []) ∨
      execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inl r, s, []) := by
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0),
      (range.stop - i + 1).toNat = n →
      execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inr (), s, []) ∨
      execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inl r, s, []) from
    fun i hs => H _ i hs rfl
  intro n
  induction n with
  | zero =>
    intro i hs hn
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    exact Or.inl rfl
  | succ n ih =>
    intro i hs hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      rcases hf i h with e | e
      · rw [execREffBindNil _ _ _ _ _ e]
        have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
          simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
          rw [hstep]
          omega
        exact ih _ _ hn'
      · rw [execREffBindEq, e]; exact Or.inr rfl
    · simp only [dif_neg h]
      exact Or.inl rfl

/-- Rocq `execR_eff_foreach_ZM_up_allow`. -/
theorem execREffForInAllow {R : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s : ExecSt) (r : R)
    (hf : ∀ i, i ∈ range → execREff (f i ()) s = some (.inr (.yield ()), s, []) ∨
      execREff (f i ()) s = some (.inl r, s, [])) :
    execREff (forIn range () f) s = some (.inr (), s, []) ∨
      execREff (forIn range () f) s = some (.inl r, s, []) :=
  execREffForInLoopAllow range hstep f s r hf range.start (by simp)

/-- Rocq `execR_eff_foreach_ZM_up'_const` (deviation 2). -/
theorem execREffForInLoopConst {R : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s : ExecSt)
    (hf : ∀ i, i ∈ range → execREff (f i ()) s = some (.inr (.yield ()), s, [])) :
    ∀ (i : Int) (hs : (i - range.start) % range.step = 0),
      execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inr (), s, []) := by
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0),
      (range.stop - i + 1).toNat = n →
      execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) s = some (.inr (), s, []) from
    fun i hs => H _ i hs rfl
  intro n
  induction n with
  | zero =>
    intro i hs hn
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    rfl
  | succ n ih =>
    intro i hs hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      rw [execREffBindNil _ _ _ _ _ (hf i h)]
      have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
        simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
        rw [hstep]
        omega
      exact ih _ _ hn'
    · simp only [dif_neg h]
      rfl

/-- Rocq `execR_eff_foreach_ZM_up_const`. -/
theorem execREffForInConst {R : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s : ExecSt)
    (hf : ∀ i, i ∈ range → execREff (f i ()) s = some (.inr (.yield ()), s, [])) :
    execREff (forIn range () f) s = some (.inr (), s, []) :=
  execREffForInLoopConst range hstep f s hf range.start (by simp)

/-! ## 2. The leaf lemmas of the PMP body -/

/-- The value form (Lean-only, deviation 3): with grain 0 the address register
reads as stored, with an empty trace. -/
theorem execEffPmpReadAddrReg (n : Nat) (s : ExecSt) :
    execEff (pmpReadAddrReg n) s = some ((s.regs .pmpaddr_n)[n]!, s, []) := by
  unfold pmpReadAddrReg
  eff_run
  generalize BitVec.access _ 1 = b
  rcases (by decide : ∀ b : BitVec 1, b = 1#1 ∨ b = 0#1) b with rfl | rfl <;> rfl

/-- Rocq `exec_eff_pmpReadAddrReg_ex`. -/
theorem execEffPmpReadAddrRegEx (n : Nat) (s : ExecSt) :
    ∃ v, execEff (pmpReadAddrReg n) s = some (v, s, []) :=
  ⟨_, execEffPmpReadAddrReg n s⟩

/-- Rocq `exec_eff_pmpMatchAddr_OFF`. -/
theorem execEffPmpMatchAddrOFF (pa : physaddr) (width : BitVec 64) (ent : BitVec 8)
    (pmpaddr prev : BitVec 64) (s : ExecSt)
    (h : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = .OFF) :
    execEff (pmpMatchAddr pa width ent pmpaddr prev) s = some (.PMP_NoMatch, s, []) := by
  unfold pmpMatchAddr
  simp only [h]
  rfl

/-! ## 3. The all-OFF reduction -/

/-- Rocq `exec_eff_pmpCheck_machine_none`. -/
theorem execEffPmpCheckMachineNone (addr : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (s : ExecSt)
    (hoff : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF) :
    execEff (pmpCheck addr width access .Machine) s = some (none, s, []) := by
  unfold pmpCheck
  rw [execEffCatchEarlyReturn]
  eff_run
  have hoff' : ∀ i : Int,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF :=
    fun i => hoff i.toNat
  rw [execREffForInConst _ rfl _ s]
  intro i _
  split
  all_goals
    eff_run [execEffPmpReadAddrReg, execEffPmpMatchAddrOFF _ _ _ _ _ s (hoff' i)]

/-! ## 4. The cell dichotomy, and the unlocked-M-mode reduction -/

/-- The `execEff` twin of `ExecSC3.execPureCell` (Lean-only). -/
theorem execEffPureCell (b e a w : Nat) (s : ExecSt) (hb : b % 4 = 0) (he : e % 4 = 0)
    (h : a % 4 + w ≤ 4) :
    execEff (pure (pmpRangeMatch b e a w) : SailM pmpAddrMatch) s = some (.PMP_NoMatch, s, []) ∨
      execEff (pure (pmpRangeMatch b e a w) : SailM pmpAddrMatch) s = some (.PMP_Match, s, []) := by
  rcases pmpRangeMatch_cell b e a w hb he h with r | r <;> simp only [r]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Rocq `exec_eff_pmpMatchAddr_machine_cell`. -/
theorem execEffPmpMatchAddrMachineCell (pa : physaddr) (wbv : BitVec 64) (ent : BitVec 8)
    (paddr prev : BitVec 64) (s : ExecSt) (h : (bits_of_physaddr pa).toNat % 4 + wbv.toNat ≤ 4) :
    execEff (pmpMatchAddr pa wbv ent paddr prev) s = some (.PMP_NoMatch, s, []) ∨
      execEff (pmpMatchAddr pa wbv ent paddr prev) s = some (.PMP_Match, s, []) := by
  obtain ⟨a⟩ := pa
  have h' : (BitVec.toNatInt a).toNat % 4 + (BitVec.toNatInt wbv).toNat ≤ 4 := by
    simp only [toNatInt_toNat]; exact h
  unfold pmpMatchAddr
  dsimp only
  have hb : ∀ x : BitVec 64, (BitVec.toNatInt x * 4).toNat % 4 = 0 := fun x => by
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]; omega
  have hb4 : ∀ x : BitVec 64, (BitVec.toNatInt x * 4 + 4).toNat % 4 = 0 := fun x => by
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]; omega
  have hb2 : ∀ x y : BitVec 64, ((BitVec.toNatInt x + BitVec.toNatInt y + 1) * 4).toNat % 4 = 0 :=
    fun x y => by simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]; omega
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact execEffPureCell _ _ _ _ s (hb _) (hb _) h'
  · eff_run
    exact execEffPureCell _ _ _ _ s (hb _) (hb4 _) h'
  · exact execEffPureCell _ _ _ _ s (hb _) (hb2 _ _) h'

/-- Rocq `exec_eff_pmpCheck_machine_unlocked`. -/
theorem execEffPmpCheckMachineUnlocked (addr : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (s : ExecSt)
    (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hrwx : ∀ ent, ∃ b, execEff (pmpCheckRWX ent access) s = some (b, s, []))
    (hcell : (bits_of_physaddr addr).toNat % 4 + (to_bits (l := 64) width).toNat ≤ 4) :
    execEff (pmpCheck addr width access .Machine) s = some (none, s, []) := by
  unfold pmpCheck
  rw [execEffCatchEarlyReturn]
  eff_run
  generalize hx : execREff (R := Option ExceptionType)
    (forIn (m := SailME (Option ExceptionType)) (_ : IntRange) () _) s = x
  have hf : x = some (.inr (), s, []) ∨ x = some (.inl none, s, []) :=
    hx ▸ execREffForInAllow _ rfl _ s none (fun i _ => by
      have hu : pmpLocked (s.regs .pmpcfg_n)[i]! = false := hunl i.toNat
      obtain ⟨b, hb⟩ := hrwx (s.regs .pmpcfg_n)[i]!
      have hmm : (Privilege.Machine == Privilege.Machine) = true := rfl
      split
      · eff_run [execEffPmpReadAddrReg]
        rcases execEffPmpMatchAddrMachineCell addr (to_bits (l := 64) width) (s.regs .pmpcfg_n)[i]!
          (s.regs .pmpaddr_n)[i.toNat]! (s.regs .pmpaddr_n)[(i - 1).toNat]! s hcell with e | e <;>
        simp only [e] <;> eff_run [hb, hu, Functions.not, hmm, Bool.not_false, Bool.and_true,
          Bool.or_true, true_or, or_true]
      · eff_run [execEffPmpReadAddrReg]
        rcases execEffPmpMatchAddrMachineCell addr (to_bits (l := 64) width) (s.regs .pmpcfg_n)[i]!
          (s.regs .pmpaddr_n)[i.toNat]! zeros s hcell with e | e <;>
        simp only [e] <;> eff_run [hb, hu, Functions.not, hmm, Bool.not_false, Bool.and_true,
          Bool.or_true, true_or, or_true])
  rcases hf with rfl | rfl <;> rfl

/-! ## 5. The fetch-shaped corollary -/

/-- Rocq `exec_eff_pmpCheck_machine_unlocked_ifetch4`. -/
theorem execEffPmpCheckMachineUnlockedIfetch4 (addr : BitVec 64) (s : ExecSt)
    (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true) :
    execEff (pmpCheck (.Physaddr addr) 4 (.InstructionFetch ()) .Machine) s = some (none, s, []) := by
  have h4 := isAlignedVaddrMod addr 4 (by decide) hal
  exact execEffPmpCheckMachineUnlocked _ 4 _ s hunl (fun ent => ⟨_, rfl⟩)
    (by show addr.toNat % 4 + (to_bits (l := 64) 4).toNat ≤ 4
        rw [show (to_bits (l := 64) 4).toNat = 4 from rfl]; omega)

end Weak

