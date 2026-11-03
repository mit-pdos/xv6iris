/-
Weak/Prom: **run certificates for machine v2 on litmus programs** (S0-P part (2), milestone 2).

* `litStep` — the PROGRAM HALF of a litmus hart at label level (machine v2's `pstep` parameter): the litmus ISA of
  `Weak/Prom/RefProg.lean`, each instruction emitting the label sequence of MachLitmus.lean's table (its first label
  carries the memory answers; the rest are queued in `q` and must follow in order).  It is a definition by a
  function (`litNext`), so a reader checks it against the table, not a proof.
* `allowedMach T` — machine v2 ALLOWS test `T`'s outcome: a VALID RUN of `pmStep litStep` (Machine.lean
  `validRun`: from the initial configuration, every promise fulfilled) in which every hart has run its whole
  program, whose final registers and final memory satisfy `T.cond`.
* `certOk T evs` — the CHECKER: replays the event list `evs` with `stepF` (`pmStep` as a function: the promise arm,
  or `litNext` + `memStepF`), then checks no outstanding promise, every hart done, and the condition.
* `certOk_sound : certOk T evs = true → allowedMach T`.  A certificate theorem is
  `certOk_sound T evs (by decide +kernel)`: the kernel replays the run.

No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachSound
import Weak.Prom.MachLitmus

namespace Weak.Prom.Mach.Cert

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

deriving instance DecidableEq for PLabel

/-! ## 1. The program half of a litmus hart -/

/-- A litmus hart's program state: its program, pc, concrete registers (64-bit), and the labels its current
instruction still has to emit (in order). -/
structure LP where
  prog : List Instr
  pc : Nat
  regs : List Nat
  q : List PLabel

def LP.rd (s : LP) (r : Nat) : Nat := if r = 0 then 0 else (s.regs[r]?).getD 0

def LP.wr (s : LP) (r v : Nat) : List Nat := if r = 0 then s.regs else s.regs.set r (v % two64)

/-- Emit the first of the answer-free labels `labs` (the label must be it), queue the rest. -/
def go1 (s : LP) (regs' : List Nat) (pc' : Nat) (labs : List PLabel) (l : PLabel) : Option LP :=
  match labs with
  | l0 :: rest => if l = l0 then some { s with regs := regs', pc := pc', q := rest } else none
  | [] => none

/-- THE FIRST LABEL OF AN INSTRUCTION (MachLitmus.lean's table): the memory label with its answers (any answers of
the right width: the memory half decides which are admissible), or the first answer-free label. -/
def instrNext (n : Nat) (s : LP) (ins : Instr) (l : PLabel) : Option LP :=
  match ins with
  | .alui op rd rs1 imm => go1 s (s.wr rd (aluOp op (s.rd rs1) imm)) (s.pc + 1) (regWL rd (srcR rs1) ++ [LInstr]) l
  | .alu op rd rs1 rs2 =>
      go1 s (s.wr rd (aluOp op (s.rd rs1) (s.rd rs2))) (s.pc + 1) (regWL rd (srcR rs1 ++ srcR rs2) ++ [LInstr]) l
  | .load sz sgn rd rs1 off =>
      let a := (s.rd rs1 + off) % two64
      if !aligned a sz then none else
      match l with
      | LLoad aq rl b tvs asrc =>
          if aq = false ∧ rl = false ∧ b = (a : Int) ∧ tvs.length = sz ∧ asrc = srcR rs1 then
            let raw := ofBytes (tvs.map Prod.snd)
            some { s with regs := s.wr rd (if sgn then sext sz raw else raw), pc := s.pc + 1,
                          q := regWL rd [.DLdRes] ++ [LInstr] }
          else none
      | _ => none
  | .store sz rs2 rs1 off =>
      let a := (s.rd rs1 + off) % two64
      if !aligned a sz then none else
      match l with
      | LStore aq rl b data asrc vsrc =>
          if aq = false ∧ rl = false ∧ b = (a : Int) ∧ data = toBytes (s.rd rs2) sz ∧ asrc = srcR rs1 ∧
              vsrc = srcR rs2 then
            some { s with pc := s.pc + 1, q := [LInstr] }
          else none
      | _ => none
  | .loadAq sz rl0 rd rs1 =>
      let a := s.rd rs1
      if !aligned a sz then none else
      match l with
      | LLoad aq rl b tvs asrc =>
          if aq = true ∧ rl = rl0 ∧ b = (a : Int) ∧ tvs.length = sz ∧ asrc = srcR rs1 then
            some { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1,
                          q := regWL rd [.DLdRes] ++ [LInstr] }
          else none
      | _ => none
  | .storeRl sz aq0 rs2 rs1 =>
      let a := s.rd rs1
      if !aligned a sz then none else
      match l with
      | LStore aq rl b data asrc vsrc =>
          if aq = aq0 ∧ rl = true ∧ b = (a : Int) ∧ data = toBytes (s.rd rs2) sz ∧ asrc = srcR rs1 ∧
              vsrc = srcR rs2 then
            some { s with pc := s.pc + 1, q := [LInstr] }
          else none
      | _ => none
  | .loadAqPc .. => none
  | .storeRlPc .. => none
  | .lr sz aq0 rl0 rd rs1 =>
      let a := s.rd rs1
      if !aligned a sz then none else
      match l with
      | LExLoad aq rl b tvs asrc =>
          if aq = aq0 ∧ rl = (aq0 && rl0) ∧ b = (a : Int) ∧ tvs.length = sz ∧ asrc = srcR rs1 then
            some { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1,
                          q := regWL rd [.DLdRes] ++ [LInstr] }
          else none
      | _ => none
  | .sc sz aq0 rl0 rd rs2 rs1 =>
      let a := s.rd rs1
      if !aligned a sz then none else
      match l with
      | LExStore aq rl b data asrc vsrc =>
          if aq = (aq0 && rl0) ∧ rl = rl0 ∧ b = (a : Int) ∧ data = toBytes (s.rd rs2) sz ∧ asrc = srcR rs1 ∧
              vsrc = srcR rs2 then
            some { s with regs := s.wr rd 0, pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LExFail, LInstr] }
          else none
      | LExFail => some { s with regs := s.wr rd 1, pc := s.pc + 1, q := regWL rd [] ++ [LExFail, LInstr] }
      | _ => none
  | .amo op sz aq0 rl0 rd rs2 rs1 =>
      let a := s.rd rs1
      if !aligned a sz then none else
      match l with
      | LRmw aq rl b tvs data asrc vsrc =>
          if aq = aq0 ∧ rl = rl0 ∧ b = (a : Int) ∧ tvs.length = sz ∧
              data = toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd)) (s.rd rs2 % 2 ^ (8 * sz))) sz ∧
              asrc = srcR rs1 ∧ vsrc = srcR rs2 then
            some { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1,
                          q := regWL rd [.DLdRes] ++ [LInstr] }
          else none
      | _ => none
  | .fence f => go1 s s.regs (s.pc + 1) [LFence f.pr f.pw f.sr f.sw, LInstr] l
  | .fenceTso => go1 s s.regs (s.pc + 1) [LFence true false true true, LFence false true false true, LInstr] l
  | .br c rs1 rs2 tgt =>
      if tgt ≤ s.pc ∨ n < tgt then none else
      go1 s s.regs (if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1) [LCtrl (srcR rs1 ++ srcR rs2), LInstr] l
  | .jmp tgt => if tgt ≤ s.pc ∨ n < tgt then none else go1 s s.regs tgt [LInstr] l
  | .csrr rd v => go1 s (s.wr rd v) (s.pc + 1) (regWL rd [] ++ [LInstr]) l
  | .fencei => go1 s s.regs (s.pc + 1) [LFenceI, LInstr] l
  | .nop => go1 s s.regs (s.pc + 1) [LInstr] l

/-- ONE LABEL of a litmus hart: the next queued label, or the next instruction's first label. -/
def litNext (s : LP) (l : PLabel) : Option LP :=
  match s.q with
  | l0 :: rest => if l = l0 then some { s with q := rest } else none
  | [] =>
    match s.prog[s.pc]? with
    | some ins => instrNext s.prog.length s ins l
    | none => none

/-- THE PROGRAM HALF (machine v2's `pstep`; no device fabric). -/
def litStep (s : LP) (_ : Unit) (l : PLabel) (s' : LP) (_ : Unit) : Prop := litNext s l = some s'

/-- The initial program states of a test. -/
def progs (T : Test) : List LP :=
  (List.range T.harts.length).map (fun i =>
    { prog := T.prog i, pc := 0, q := []
      regs := (List.range 32).map (fun r => ((((T.regs0[i]?).getD []).lookup r).getD 0) % two64) })

/-! ## 2. The outcome -/

/-- Final register `r` of hart `h`. -/
def regOf (cfg : PCfg LP Unit) (h r : Nat) : Nat :=
  match cfg.pcAgs[h]? with
  | some ag => ag.paSt.rd r
  | none => 0

/-- Final byte at `x`: the latest message writing it, else the image (`finalMem`, one byte). -/
def memOf (T : Test) (cfg : PCfg LP Unit) (x : Nat) : Nat := finalMem (testImg T) cfg.pcLog x 1

/-- Every hart ran its whole program. -/
def allDone (cfg : PCfg LP Unit) : Prop :=
  ∀ (i : Nat) (ag : PAgent LP), cfg.pcAgs[i]? = some ag → ag.paSt.pc = ag.paSt.prog.length ∧ ag.paSt.q = []

/-- MACHINE V2 ALLOWS the outcome of `T`: a valid run (every promise fulfilled) in which every hart finished, whose
final registers and memory satisfy the condition. -/
def allowedMach (T : Test) : Prop :=
  ∃ (evs : List PEvt) (cfg : PCfg LP Unit),
    validRun litStep (testImg T) () (progs T) evs cfg ∧ allDone cfg ∧
    T.cond.eval (regOf cfg) (memOf T cfg) = true

/-! ## 3. The checker -/

/-- ONE MACHINE STEP as a function (`pmStep litStep`). -/
def stepF (cfg : PCfg LP Unit) : PEvt → Option (PCfg LP Unit)
  | .prom i m =>
    match cfg.pcAgs[i]? with
    | some ag =>
      okIf (msgNonTrivB m && m.tid == some i)
        ⟨cfg.pcImg, cfg.pcLog ++ [m], cfg.pcDev,
         cfg.pcAgs.set i ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩⟩
    | none => none
  | .st i l ots =>
    match cfg.pcAgs[i]? with
    | some ag =>
      match litNext ag.paSt l, memStepF cfg.pcImg cfg.pcLog i ag.paProm ag.paWs l ots with
      | some st', some (ws', prom') => some ⟨cfg.pcImg, cfg.pcLog, (), cfg.pcAgs.set i ⟨st', ws', prom'⟩⟩
      | _, _ => none
    | none => none

/-- Replay an event list. -/
def runF : PCfg LP Unit → List PEvt → Option (PCfg LP Unit)
  | cfg, [] => some cfg
  | cfg, e :: es =>
    match stepF cfg e with
    | some c1 => runF c1 es
    | none => none

/-- No outstanding promise, as a Bool. -/
def noPromB (cfg : PCfg LP Unit) : Bool := cfg.pcAgs.all (fun ag => ag.paProm.isEmpty)

/-- Every hart done, as a Bool. -/
def doneB (cfg : PCfg LP Unit) : Bool :=
  cfg.pcAgs.all (fun ag => ag.paSt.pc == ag.paSt.prog.length && ag.paSt.q.isEmpty)

/-- THE CERTIFICATE CHECKER. -/
def certOk (T : Test) (evs : List PEvt) : Bool :=
  match runF (pmInit (testImg T) () (progs T)) evs with
  | some cfg => noPromB cfg && doneB cfg && T.cond.eval (regOf cfg) (memOf T cfg)
  | none => false

/-! ## 4. Soundness -/

theorem stepF_sound {cfg cfg' : PCfg LP Unit} {e : PEvt} (h : stepF cfg e = some cfg') :
    pmStep litStep cfg e cfg' := by
  cases e with
  | prom i m =>
    simp only [stepF] at h
    cases hag : cfg.pcAgs[i]? with
    | none => rw [hag] at h; cases h
    | some ag =>
      rw [hag] at h
      obtain ⟨hc, he⟩ := okIf_eq_some h
      subst he
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact .promise cfg i ag m hag (msgNonTriv_sound hc.1) hc.2
  | st i l ots =>
    simp only [stepF] at h
    cases hag : cfg.pcAgs[i]? with
    | none => rw [hag] at h; cases h
    | some ag =>
      simp only [hag] at h
      revert h
      cases hl : litNext ag.paSt l with
      | none => intro h; cases h
      | some st' =>
        cases hm : memStepF cfg.pcImg cfg.pcLog i ag.paProm ag.paWs l ots with
        | none => intro h; cases h
        | some p =>
          obtain ⟨ws', prom'⟩ := p
          intro h
          cases h
          exact .state cfg i ag l ots st' () ws' prom' hag hl (memStepF_sound hm)

theorem runF_sound : ∀ {cfg cfg' : PCfg LP Unit} {evs : List PEvt}, runF cfg evs = some cfg' →
    pmSteps litStep cfg evs cfg' := by
  intro cfg cfg' evs
  induction evs generalizing cfg with
  | nil => intro h; simp only [runF, Option.some.injEq] at h; subst h; exact .refl _
  | cons e es ih =>
    intro h
    simp only [runF] at h
    cases hs : stepF cfg e with
    | none => rw [hs] at h; cases h
    | some c1 => rw [hs] at h; exact .step _ _ _ _ _ (stepF_sound hs) (ih h)

theorem noPromB_sound {cfg : PCfg LP Unit} (h : noPromB cfg = true) : noPromises cfg := by
  intro i ag hag
  have hmem := List.mem_of_getElem? hag
  exact Std.ExtTreeSet.isEmpty_iff.1 (List.all_eq_true.1 h ag hmem)

theorem doneB_sound {cfg : PCfg LP Unit} (h : doneB cfg = true) : allDone cfg := by
  intro i ag hag
  have hmem := List.mem_of_getElem? hag
  have := List.all_eq_true.1 h ag hmem
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at this
  exact this

/-- THE CHECKER IS SOUND. -/
theorem certOk_sound (T : Test) (evs : List PEvt) (h : certOk T evs = true) : allowedMach T := by
  unfold certOk at h
  cases hr : runF (pmInit (testImg T) () (progs T)) evs with
  | none => rw [hr] at h; cases h
  | some cfg =>
    rw [hr] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨evs, cfg, ⟨runF_sound hr, noPromB_sound h.1.1⟩, doneB_sound h.1.2, h.2⟩

end Weak.Prom.Mach.Cert
