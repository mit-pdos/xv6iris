/-
Weak: **the shared `execEff` skeleton** (M4 batch 0): the instrumented
early-return interpreter `execREff`, its composition kit, the bridge back
through `SailME.run`, the two `run_hart_active` progress mirrors, the whole-step
assembly, the window rule for `wPEff`, and the completeness check.

Rocq: `iris/WeakEffSkel.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  A leaf's whole remaining obligation is
`WeakCert.wPEff tid es σ` ("the confined run of `riscvStep tick` succeeds, with
effect trace `es`").  `WeakEff` supplied the toolkit and the `try_step` wrapper
`WeakEff.execEffRiscvStepHartActive`; this file supplies what the wrapper
stands on:
* §1 `execREff` -- `execR` with the trace threaded, plus the two agreement
  lemmas (`execREff` and `execR` compute the same value and state; every
  `execR` success has SOME trace);
* §2 THE COMPOSITION KIT mirroring `execR`'s: `execREffBind` / `Bind0` /
  `ReturnR` / `LiftR`, their equation forms, and the `_nil` DROP-IN
  replacements for `execRBindSome` / `execRBind0Some` / `execRLiftRSeq` when
  the sub-run has an empty trace (every register-only sub-run does);
* §3 `execEffCatchEarlyReturn` -- the bridge back into the base monad;
* §4 THE TWO PROGRESS MIRRORS, whose trace is `es_f ++ es_x`: the decode,
  the landing-pad check, the privilege read and the interrupt dispatch are
  register-only and contribute nothing;
* §5 the whole `riscvStep false`, from the fetch's trace and the `execute`'s;
* §6 the window rule `wPEffOfWindow` and the completeness check (the
  certificates' traces are EXACTLY `es_f ++ es_x`).
What is deliberately NOT here: the fetch's own `execEff` reduction (a
HYPOTHESIS of §4), and the `tick_clock` mirror (Rocq §6b's prose).
Nothing reduces a model function by computation beyond what the SC
originals (`Weak/ExecSC6.lean`) do.

**Deviations from Rocq.**
1. NAMES: the tree's camelCase (map below).  Vocabulary as `Weak/WeakEff.lean`
   deviation 1; `Defs.monadR R exception X` ↦ `SailME R X`, `Defs.liftR` ↦
   `liftM`, `Defs.catch_early_return` ↦ `SailME.run`, `Defs.returnR` ↦ `pure`,
   `Defs.bind0 m n` ↦ `m >>= fun _ => n`, `add_vec_int` ↦ `BitVec.addInt`,
   `eq_vec x y = false` ↦ `(x == y) = false`, `RETIRE_SUCCESS` ↦
   `.Retire_Success ()`, `zero_extend' 32 w` ↦ `zero_extend (m := 32) w`.
2. `execREff` is not a second `Fixpoint` (as `Weak/Exec.lean` deviation 5 for
   `execR`): Lean's `SailME R X` is `ExceptT (Error ⊕ R) SailM X`, so
   `execREff m s` is `execEff` of `m.run`, with `.error (.inr r)` the early
   return (`inl r`), `.ok x` the value (`inr x`) and a model exception
   (`.error (.inl _)`; Rocq's stuck `ExtraOutcome (inr _)`) mapped to `none`.
   Consequently every kit lemma is proved from `WeakEff.execEffBindEq` rather
   than by its own induction.
3. §3b `exec_eff_dispatchInterrupt_none` is privilege-generic as in Rocq;
   `exec_eff_is_landing_pad` reads `s.regs .elp == landing_pad_bits_backwards
   .LP_EXPECTED` (as `ExecSC6.execIsLandingPad`).
4. §4: the Lean model's base-instruction landing-pad test is an inline `&&`
   (no `and_boolM`), so `is_lpad_instruction instr = false` is kept as a premise
   (as in `ExecSC6.execHartActiveProgressBaseGen`) but unused by the proof.
5. §5: the section hypotheses are premises, and the `Let`s `s_a`/`s_tick`/
   `s_final` are `Weak/ExecLib.lean`'s `hartActiveSA`/`hartActiveSTick`/
   `hartActiveSFinal` (as `Weak/WeakEff.lean` deviation 9).
6. `wPEffOfWindow`: Lean's `wPEff` carries the O2 fetch obligation
   `fetchPin σ es` (`Weak/WeakCert.lean` deviation 4), so it is an extra
   premise; the window facts are `paZ a ≠ 0`, `pinnedRead σ (paZ a)` and
   `bmDomSub t'.mem W` (Rocq `dom (mem t') ⊆ W`).
7. §6c: Rocq `ak_coh akl = false` is `akl.akIfetch = false`, as in
   `WeakCert.wcertLoad`/`wcertAmoAq` (O2).
8. Rocq §7's `Print Assumptions` commands are not declarations (no Lean twin).

**Rocq → Lean name map.**  `execR_eff` `execREff`, `execR_eff_execR`
`execREffExecR`, `execR_execR_eff` `execRExecREff`, `execR_eff_bind`
`execREffBind`, `execR_eff_returnR` `execREffReturnR`, `execR_eff_None`
`execREffNone`, `execR_eff_bind_eq` `execREffBindEq`, `execR_eff_bind0`
`execREffBind0`, `execR_eff_bind0_eq` `execREffBind0Eq`, `execR_eff_liftR`
`execREffLiftR`, `execR_eff_bind_cat` `execREffBindCat`, `execR_eff_bind_nil`
`execREffBindNil`, `execR_eff_bind0_cat` `execREffBind0Cat`,
`execR_eff_bind0_nil` `execREffBind0Nil`, `execR_eff_liftR_cat`
`execREffLiftRCat`, `execR_eff_liftR_seq` `execREffLiftRSeq`,
`exec_eff_catch_early_return` `execEffCatchEarlyReturn`,
`exec_eff_dispatchInterrupt_none` `execEffDispatchInterruptNone`,
`exec_eff_is_landing_pad` `execEffIsLandingPad`,
`exec_eff_hart_active_progress_base_gen` `execEffHartActiveProgressBaseGen`,
`exec_eff_hart_active_progress_RVC_gen` `execEffHartActiveProgressRVCGen`,
`s_a`/`s_tick`/`s_final` `hartActiveSA`/`hartActiveSTick`/`hartActiveSFinal`
(ExecLib, deviation 5), `exec_eff_riscv_step_base` `execEffRiscvStepBase`,
`exec_eff_riscv_step_rvc` `execEffRiscvStepRvc`, `wP_eff_of_window`
`wPEffOfWindow`, `wcert_load_via_skeleton` `wcertLoadViaSkeleton`,
`wcert_store_via_skeleton` `wcertStoreViaSkeleton`, `wcert_amo_aq_via_skeleton`
`wcertAmoAqViaSkeleton`.  Lean-only: `execREffThrow`.

**Dropped:** nothing -- every Rocq definition and lemma has a Lean twin (27
Rocq `Fixpoint`/`Lemma`s + 6 `Let`s; Lean 27 + 1 Lean-only, the `Let`s reused
from ExecLib).

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakEff

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. `execREff` -- the early-return interpreter, instrumented -/

section execREff
variable {R X Y : Type}

/-- Rocq `execR_eff` (deviation 2): `execEff` of the `ExceptT` run, the early
return `inl`, the value `inr`, a model exception stuck. -/
def execREff (m : SailME R X) (s : ExecSt) : Option ((R ⊕ X) × ExecSt × List Weff) :=
  match execEff (ExceptT.run m) s with
  | some (.ok x, s', es) => some (.inr x, s', es)
  | some (.error (.inr r), s', es) => some (.inl r, s', es)
  | some (.error (.inl _), _, _) => none
  | none => none

theorem execREffExecR (m : SailME R X) :
    ∀ s r s' es, execREff m s = some (r, s', es) → execR m s = some (r, s') := by
  intro s r s' es h
  unfold execREff at h
  unfold execR
  rcases he : execEff (ExceptT.run m) s with _ | ⟨e | x, s1, es1⟩
  · simp [he] at h
  · rw [execEffExec _ _ _ _ _ he]
    rcases e with e | r0
    · simp [he] at h
    · simp only [he, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      rfl
  · rw [execEffExec _ _ _ _ _ he]
    simp only [he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    rfl

theorem execRExecREff (m : SailME R X) :
    ∀ s r s', execR m s = some (r, s') → ∃ es, execREff m s = some (r, s', es) := by
  intro s r s' h
  unfold execR at h
  unfold execREff
  rcases he : exec (ExceptT.run m) s with _ | ⟨e | x, s1⟩
  · simp [he] at h
  · obtain ⟨es, hes⟩ := execExecEff _ _ _ _ he
    rw [hes]
    rcases e with e | r0
    · simp [he] at h
    · simp only [he, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨es, rfl⟩
  · obtain ⟨es, hes⟩ := execExecEff _ _ _ _ he
    rw [hes]
    simp only [he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨es, rfl⟩

/-! ## 2. THE COMPOSITION KIT -/

theorem execREffReturnR (x : X) (s : ExecSt) :
    execREff (pure x : SailME R X) s = some (.inr x, s, []) := rfl

/-- An early return (Lean-only). -/
theorem execREffThrow (r : R) (s : ExecSt) :
    execREff (SailME.throw r : SailME R X) s = some (.inl r, s, []) := rfl

theorem execREffNone (m : SailME R X) (s : ExecSt) :
    execREff m s = none → execR m s = none := by
  intro h
  rcases hE : execR m s with _ | ⟨r, s'⟩
  · rfl
  · obtain ⟨es, hee⟩ := execRExecREff m s r s' hE
    rw [hee] at h
    cases h

theorem execREffBindEq (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) :
    execREff (m >>= f) s =
      match execREff m s with
      | some (.inl e, st, es) => some (.inl e, st, es)
      | some (.inr a, st, es) =>
        match execREff (f a) st with
        | some (y, s', es') => some (y, s', es ++ es')
        | none => none
      | none => none := by
  unfold execREff
  rw [ExceptT.run_bind, execEffBindEq]
  rcases he : execEff (ExceptT.run m) s with _ | ⟨e | a, s1, es1⟩
  · rfl
  · rcases e with e | r0
    · rfl
    · simp only [effThen]
      show some (Sum.inl r0, s1, es1 ++ []) = _
      rw [List.append_nil]
  · simp only [effThen]
    rcases hf : execEff (ExceptT.run (f a)) s1 with _ | ⟨e | b, s2, es2⟩
    · rfl
    · rcases e with e | r0 <;> rfl
    · rfl

theorem execREffBind (m : SailME R Y) (f : Y → SailME R X) :
    ∀ s r st es, execREff m s = some (r, st, es) →
      execREff (m >>= f) s =
        match r with
        | .inl e => some (.inl e, st, es)
        | .inr a =>
          match execREff (f a) st with
          | some (y, s', es') => some (y, s', es ++ es')
          | none => none := by
  intro s r st es hm
  rw [execREffBindEq, hm]
  cases r <;> rfl

theorem execREffBind0 (m : SailME R Unit) (n : SailME R X) :
    ∀ s r st es, execREff m s = some (r, st, es) →
      execREff (m >>= fun _ => n) s =
        match r with
        | .inl e => some (.inl e, st, es)
        | .inr _ =>
          match execREff n st with
          | some (y, s', es') => some (y, s', es ++ es')
          | none => none := by
  intro s r st es hm
  rw [execREffBind m (fun _ => n) s r st es hm]
  cases r <;> rfl

theorem execREffBind0Eq (m : SailME R Unit) (n : SailME R X) (s : ExecSt) :
    execREff (m >>= fun _ => n) s =
      match execREff m s with
      | some (.inl e, st, es) => some (.inl e, st, es)
      | some (.inr _, st, es) =>
        match execREff n st with
        | some (y, s', es') => some (y, s', es ++ es')
        | none => none
      | none => none := by
  rw [execREffBindEq m (fun _ => n) s]
  rcases execREff m s with _ | ⟨_ | _, _, _⟩ <;> rfl

/-- A lifted base computation never early-returns. -/
theorem execREffLiftR (m : SailM X) (s : ExecSt) :
    execREff (liftM m : SailME R X) s =
      match execEff m s with
      | some (x, s', es) => some (.inr x, s', es)
      | none => none := by
  unfold execREff
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e, execEffBindEq]
  rcases execEff m s with _ | ⟨x, s', es⟩
  · rfl
  · show some (Sum.inr x, s', es ++ []) = _
    rw [List.append_nil]

/-! ### 2b. The forward forms -- the drop-in replacements -/

theorem execREffBindCat (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y) (st : ExecSt)
    (es : List Weff) :
    execREff m s = some (.inr a, st, es) →
    execREff (m >>= f) s =
      match execREff (f a) st with
      | some (y, s', es') => some (y, s', es ++ es')
      | none => none :=
  fun h => execREffBind m f s (.inr a) st es h

theorem execREffBindNil (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y) (st : ExecSt) :
    execREff m s = some (.inr a, st, []) → execREff (m >>= f) s = execREff (f a) st := by
  intro h
  rw [execREffBindCat m f s a st [] h]
  rcases execREff (f a) st with _ | ⟨y, s', es'⟩ <;> rfl

theorem execREffBind0Cat (m : SailME R Unit) (n : SailME R X) (s st : ExecSt) (es : List Weff) :
    execREff m s = some (.inr (), st, es) →
    execREff (m >>= fun _ => n) s =
      match execREff n st with
      | some (y, s', es') => some (y, s', es ++ es')
      | none => none :=
  fun h => execREffBind0 m n s (.inr ()) st es h

theorem execREffBind0Nil (m : SailME R Unit) (n : SailME R X) (s st : ExecSt) :
    execREff m s = some (.inr (), st, []) → execREff (m >>= fun _ => n) s = execREff n st := by
  intro h
  rw [execREffBind0Cat m n s st [] h]
  rcases execREff n st with _ | ⟨y, s', es'⟩ <;> rfl

theorem execREffLiftRCat (m : SailM Y) (f : Y → SailME R X) (s st : ExecSt) (x : Y) (es : List Weff) :
    execEff m s = some (x, st, es) →
    execREff (liftM m >>= f) s =
      match execREff (f x) st with
      | some (y, s', es') => some (y, s', es ++ es')
      | none => none := by
  intro hm
  apply execREffBindCat _ f s x st es
  rw [execREffLiftR, hm]

theorem execREffLiftRSeq (m : SailM Y) (f : Y → SailME R X) (s st : ExecSt) (x : Y) :
    execEff m s = some (x, st, []) → execREff (liftM m >>= f) s = execREff (f x) st := by
  intro hm
  apply execREffBindNil _ f s x st
  rw [execREffLiftR, hm]

end execREff

/-! ## 3. THE BRIDGE BACK: `SailME.run` -/

theorem execEffCatchEarlyReturn {X : Type} (body : SailME X X) (s : ExecSt) :
    execEff (SailME.run body) s =
      match execREff body s with
      | some (.inl r, s', es) => some (r, s', es)
      | some (.inr r, s', es) => some (r, s', es)
      | none => none := by
  unfold execREff
  show execEff (ExceptT.run body >>= _) s = _
  rw [execEffBindEq]
  rcases execEff (ExceptT.run body) s with _ | ⟨e | a, s', es⟩
  · rfl
  · rcases e with e | r
    · rfl
    · show some (r, s', es ++ []) = _
      rw [List.append_nil]
  · show some (a, s', es ++ []) = _
    rw [List.append_nil]

/-! ### 3b. The two cheap leaf twins `run_hart_active` needs -/

theorem execEffDispatchInterruptNone (p : Privilege) (s : ExecSt) :
    execEff (getPendingSet p) s = some (none, s, []) →
    execEff (dispatchInterrupt p) s = some (none, s, []) := by
  intro hgp
  unfold dispatchInterrupt
  rw [execEffBindNil _ _ _ _ _ hgp]
  rfl

theorem execEffIsLandingPad (s : ExecSt) :
    execEff (is_landing_pad_expected ()) s =
      some (s.regs .elp == landing_pad_bits_backwards .LP_EXPECTED, s, []) := rfl

/-! ## 4. THE TWO `run_hart_active` PROGRESS MIRRORS -/

theorem execEffHartActiveProgressBaseGen (priv : Privilege) (s s_f s_x : ExecSt) (w : BitVec 32)
    (instr : instruction) (pc : BitVec 64) (resf : ExecutionResult) (es_f es_x : List Weff)
    (hpriv : s.regs .cur_privilege = priv)
    (hdisp : execEff (dispatchInterrupt priv) s = some (none, s, []))
    (hfetch : execEff (fetch ()) s = some (.F_Base w, s_f, es_f))
    (hdec : execEff (ext_decode w) s_f = some (instr, s_f, []))
    (hlpad : (s_f.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false)
    (_hnotlpad : is_lpad_instruction instr = false) (hpc : s_f.regs .PC = pc)
    (hexec : execEff (execute instr) (s_f.setReg .nextPC (BitVec.addInt pc 4)) = some (resf, s_x, es_x))
    (hnot : match resf with | .ExecuteAs _ => False | _ => True) :
    execEff (run_hart_active 0) s =
      some (.Step_Execute (resf, zero_extend (m := 32) w), s_x, es_f ++ es_x) := by
  unfold run_hart_active ext_fetch_hook get_config_print_instr
  rw [execEffCatchEarlyReturn]
  simp (config := { decide := true }) only [execREffBindEq, execREffLiftR, execREffReturnR,
    readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff,
    ↓reduceIte, Bool.false_eq_true, hpriv, hdisp, hfetch, execEffInstrAnnounce, hdec,
    execEffIsLandingPad, hlpad, hpc, hexec, Bool.false_and, List.nil_append, List.append_nil]
  cases resf <;> simp at hnot <;> simp [execREffReturnR, List.append_nil]

theorem execEffHartActiveProgressRVCGen (priv : Privilege) (s s_f s_x : ExecSt) (h : BitVec 16)
    (instr other : instruction) (pc : BitVec 64) (resf : ExecutionResult) (es_f es_x : List Weff)
    (hpriv : s.regs .cur_privilege = priv)
    (hdisp : execEff (dispatchInterrupt priv) s = some (none, s, []))
    (hfetch : execEff (fetch ()) s = some (.F_RVC h, s_f, es_f))
    (hdec : execEff (ext_decode_compressed h) s_f = some (instr, s_f, []))
    (hlpad : (s_f.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false)
    (hpc : s_f.regs .PC = pc)
    (hzca : execEff (currentlyEnabled .Ext_Zca) s_f = some (true, s_f, []))
    (hexec : execEff (execute instr) (s_f.setReg .nextPC (BitVec.addInt pc 2)) =
      some (.ExecuteAs other, s_f.setReg .nextPC (BitVec.addInt pc 2), []))
    (hother : execEff (execute other) (s_f.setReg .nextPC (BitVec.addInt pc 2)) =
      some (resf, s_x, es_x)) :
    execEff (run_hart_active 0) s =
      some (.Step_Execute (resf, zero_extend (m := 32) h), s_x, es_f ++ es_x) := by
  unfold run_hart_active ext_fetch_hook get_config_print_instr
  rw [execEffCatchEarlyReturn]
  simp (config := { decide := true }) only [execREffBindEq, execREffLiftR, execREffReturnR,
    readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff,
    ↓reduceIte, hpriv, hdisp, hfetch, execEffInstrAnnounce, hdec,
    execEffIsLandingPad, hlpad, hzca, hpc, hexec, hother, List.nil_append, List.append_nil]

/-! ## 5. THE ASSEMBLY: one whole `riscvStep`, from the fetch's trace and the
`execute`'s -/

/-- Rocq `exec_eff_riscv_step_base` (section `StepBaseEff`, deviation 5). -/
theorem execEffRiscvStepBase (s sExec : ExecSt) (w : BitVec 32) (i : instruction) (pc : BitVec 64)
    (b : Bool) (es_f es_x : List Weff)
    (hsi : execEff (should_inc_minstret (s.regs .cur_privilege)) s = some (b, s, []))
    (hhartA : (hartActiveSA s b).regs .hart_state = .HART_ACTIVE ())
    (hpriv : (hartActiveSA s b).regs .cur_privilege = .Machine)
    (hdisp : execEff (dispatchInterrupt .Machine) (hartActiveSA s b) =
      some (none, hartActiveSA s b, []))
    (hfetch : execEff (fetch ()) (hartActiveSA s b) = some (.F_Base w, hartActiveSA s b, es_f))
    (hdec : execEff (ext_decode w) (hartActiveSA s b) = some (i, hartActiveSA s b, []))
    (hlpad : ((hartActiveSA s b).regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false)
    (hnotlpad : is_lpad_instruction i = false)
    (hpc : (hartActiveSA s b).regs .PC = pc)
    (hexec : execEff (execute i) ((hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 4)) =
      some (.Retire_Success (), sExec, es_x))
    (hhartExec : sExec.regs .hart_state = .HART_ACTIVE ())
    (hmiExec : sExec.regs .minstret_increment = b) :
    execEff (riscvStep false) s = some ((), hartActiveSFinal sExec b, es_f ++ es_x) :=
  execEffRiscvStepHartActive s sExec (zero_extend (m := 32) w) b (es_f ++ es_x) hsi hhartA
    (execEffHartActiveProgressBaseGen .Machine (hartActiveSA s b) (hartActiveSA s b) sExec w i pc
      (.Retire_Success ()) es_f es_x hpriv hdisp hfetch hdec hlpad hnotlpad hpc hexec trivial)
    hhartExec hmiExec

/-- Rocq `exec_eff_riscv_step_rvc` (section `StepRVCEff`, deviation 5). -/
theorem execEffRiscvStepRvc (s sExec : ExecSt) (h : BitVec 16) (i other : instruction) (pc : BitVec 64)
    (b : Bool) (es_f es_x : List Weff)
    (hsi : execEff (should_inc_minstret (s.regs .cur_privilege)) s = some (b, s, []))
    (hhartA : (hartActiveSA s b).regs .hart_state = .HART_ACTIVE ())
    (hpriv : (hartActiveSA s b).regs .cur_privilege = .Machine)
    (hdisp : execEff (dispatchInterrupt .Machine) (hartActiveSA s b) =
      some (none, hartActiveSA s b, []))
    (hfetch : execEff (fetch ()) (hartActiveSA s b) = some (.F_RVC h, hartActiveSA s b, es_f))
    (hdec : execEff (ext_decode_compressed h) (hartActiveSA s b) = some (i, hartActiveSA s b, []))
    (hlpad : ((hartActiveSA s b).regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false)
    (hpc : (hartActiveSA s b).regs .PC = pc)
    (hzca : execEff (currentlyEnabled .Ext_Zca) (hartActiveSA s b) = some (true, hartActiveSA s b, []))
    (hexp : execEff (execute i) ((hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 2)) =
      some (.ExecuteAs other, (hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 2), []))
    (hexec : execEff (execute other) ((hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 2)) =
      some (.Retire_Success (), sExec, es_x))
    (hhartExec : sExec.regs .hart_state = .HART_ACTIVE ())
    (hmiExec : sExec.regs .minstret_increment = b) :
    execEff (riscvStep false) s = some ((), hartActiveSFinal sExec b, es_f ++ es_x) :=
  execEffRiscvStepHartActive s sExec (zero_extend (m := 32) h) b (es_f ++ es_x) hsi hhartA
    (execEffHartActiveProgressRVCGen .Machine (hartActiveSA s b) (hartActiveSA s b) sExec h i other pc
      (.Retire_Success ()) es_f es_x hpriv hdisp hfetch hdec hlpad hpc hzca hexp hexec)
    hhartExec hmiExec

/-! ## 6. THE RECIPE, NAMED -- and the completeness check

### 6a. The window obligation, as an `apply`-able rule (deviation 6) -/

theorem wPEffOfWindow (cid : Nat) (es : List Weff) (σ : Wmstate) (W : GSet PAddr) :
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ es →
    (∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ = some ((), t', es) ∧
      bmDomSub t'.mem W) →
    wPEff (some cid) es σ :=
  fun hwf hW0 hWp hfp hrun => ⟨hwf, W, hW0, hWp, hfp, hrun⟩

/-! ### 6c. COMPLETENESS CHECK: the certificates at the trace the skeleton
produces (`es_f ++ es_x`, on the nose) -/

theorem wcertLoadViaSkeleton (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (akl : AkInfo) (ea : PAddr) :
    akl.akIfetch = false →
    wstepCert cid pc (wPEff (some cid) ([.WEread akf pf nf] ++ [.WEread akl ea 4])) (wQLoad ea) :=
  fun hcoh => wcertLoad cid pc akf pf nf akl ea hcoh

theorem wcertStoreViaSkeleton (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    wstepCert cid pc (wPEff (some cid) ([.WEread akf pf nf] ++ [.WEwrite akw ea 4 v]))
      (wQStore (some cid) ea v) :=
  wcertStore cid pc akf pf nf akw ea v

theorem wcertAmoAqViaSkeleton (cid : Nat) (pc : BitVec 64) (akf : AkInfo) (pf : PAddr) (nf : Nat)
    (aka akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false → aka.akSync = true → akw.akLatest = true →
    wstepCert cid pc
      (wPEff (some cid) ([.WEread akf pf nf] ++ [.WEread aka ea 4, .WEwrite akw ea 4 v]))
      (wQAmoAq (some cid) ea v) :=
  fun hcoh hsync hlat => wcertAmoAq cid pc akf pf nf aka akw ea v hcoh hsync hlat

end Weak
