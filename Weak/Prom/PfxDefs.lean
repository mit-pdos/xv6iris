/-
Weak/Prom: **S3d — executions that never stop, and the prefix lemma (NA-1): definitions** (plan rev 7 §6 S3d,
§8 S3d, §9 Q1; owner ruling [OWN.P4], context.md item 11: "Q1: A" — prove the prefix lemma and state theorems over
ALL executions the reference allows, infinite ones included).

## What an infinite execution of the reference is

rvwmo.adoc:46–47 "a total ordering of the memory operations produced by all harts", :307–310 "An execution of a
RISC-V program obeys the RVWMO memory consistency model only if there exists a global memory order conforming to
preserved program order and satisfying the load value axiom, the atomicity axiom, and the progress axiom", :350–351
the progress axiom "No memory operation may be preceded in the global memory order by an infinite sequence of other
memory operations".  Nothing in the text bounds the number of memory operations of a hart: a hart that loops forever
produces infinitely many.

* THE PROGRAM SIDE.  `Weak/Prom/RefProg.lean`'s front end is loop-free (`stepI`'s `.br`/`.jmp` arms refuse
  `tgt ≤ pc`).  `stepL` is the same symbolic interpreter with branches and jumps to ANY target `≤ |prog|` (the
  loop front end; machine side: `Weak/Prom/OwnAFront.lean` `xNext`); every other instruction is `stepI`.  A hart's
  infinite run is a sequence of symbolic states `st h 0, st h 1, …` from `T.init h`, each one `LStep` from the
  previous (a halted hart stays put: `pc = |prog|`).  Its events are the events of the states (each state's event
  list is a prefix of the next one's).  Choices (branch outcomes, SC success) are existential per step, as in
  `symRun`'s choice list.
* THE MEMORY SIDE (`rvwmoRefInf`).  The same axioms as `Weak/Prom/Ref.lean`'s `rvwmoRef`, stated over the
  (possibly infinite) set of events: `gmo` is a RELATION — a strict total order of exactly the memory operations
  (`gmoOk`); "the store that is the latest in global memory order among" the candidates of the load value axiom is
  `rfI` (a relation: the latest candidate, or none = the initial value); rules 1–13 (`ppoI`), the I/O orderings
  (`ioOrdI`), the load value axiom (`loadValueAxI`), the atomicity axiom (`atomicityAxI`), the §zalrsc success
  conditions (`scAxI`) and the PROGRESS AXIOM read literally (`progressAxI`: no memory operation has an injective
  sequence of gmo-predecessors — Ref.lean's `progressAx`).  Each definition below cites the `Ref.lean` definition
  it transcribes; the only change is that "every event" ranges over `E.has` instead of a list.
* A FINITE PARTIAL EXECUTION (`partExec`): every hart has run a finite number of `LStep`s from its initial state
  ("each hart stopped at some instruction", plan §9 Q1), the path conditions hold, and the concretised execution
  (`conc`, RefProg.lean) satisfies Ref.lean's `rvwmoRef` — the finite reference that `rvwmo_complete`
  (CmpMain.lean) consumes.

No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpSym

noncomputable section

namespace Weak.Prom.Pfx

open Classical
open Weak.Prom.Ref
open Weak.Prom.Cmp (SymWf okIdx depsOf progS3aB instrS3a)

/-! ## 1. The loop front end of the reference -/

/-- ONE INSTRUCTION of the LOOP front end: `stepI` (RefProg.lean), except that a branch or jump may go to ANY target
`≤ |prog|` (backward included).  The branch arm is `stepI`'s with the forward guard `tgt ≤ s.pc` dropped: the same
fork, the same path condition, the same control taint ("the union of the taints of the sources of every po-earlier
branch", RefProg.lean header, rvwmo.adoc:242–246). -/
def stepL (h n : Nat) (s : SSt) : Instr → StepR
  | .br c rs1 rs2 tgt =>
      if n < tgt then .stuck else
      let (e1, t1) := s.rd rs1
      let (e2, t2) := s.rd rs2
      let s' := { s with ii := s.ii + 1, ctl := s.ctl ++ t1 ++ t2 }
      .fork { s' with pc := tgt, conds := s.conds ++ [(c, e1, e2, true)] }
        { s' with pc := s.pc + 1, conds := s.conds ++ [(c, e1, e2, false)] }
  | .jmp tgt => if n < tgt then .stuck else .next { s with pc := tgt, ii := s.ii + 1 }
  | i => stepI h n s i

/-- ONE STEP of hart `h` running program `p`: halted (`pc = |p|`, the state stays), or the instruction at `pc`
(`.next`, or either side of a `.fork` — a branch outcome or an SC's success/failure, chosen by the execution). -/
def LStep (p : List Instr) (h : Nat) (s s' : SSt) : Prop :=
  (s.pc = p.length ∧ s' = s) ∨
  ∃ i, p[s.pc]? = some i ∧
    (stepL h p.length s i = .next s' ∨ ∃ t f, stepL h p.length s i = .fork t f ∧ (s' = t ∨ s' = f))

/-- Finitely many steps of hart `h` from `s0`. -/
inductive LReach (p : List Instr) (h : Nat) (s0 : SSt) : SSt → Prop
  | refl : LReach p h s0 s0
  | step {s s' : SSt} : LReach p h s0 s → LStep p h s s' → LReach p h s0 s'

/-! ## 2. Infinite executions -/

/-- A (possibly infinite) CANDIDATE EXECUTION of test `T`: every hart's sequence of symbolic states, the bytes every
load returns (`ν`, as RefProg.lean's `Val`), and the global memory order as a relation. -/
structure IExec where
  T : Test
  st : Nat → Nat → SSt
  ν : Val
  gmo : EvId → EvId → Prop

namespace IExec

variable (E : IExec)

/-- Event `(h, i)` exists: `h` is a hart of the test and some state of its run has more than `i` events. -/
def has (e : EvId) : Prop := e.1 < E.T.harts.length ∧ ∃ k, e.2 < (E.st e.1 k).evs.length

/-- The symbolic event `e` (any state of the run that has it; they agree, PfxSym.lean `sev_eq`). -/
def sev (e : EvId) : SEv :=
  if h : E.has e then (E.st e.1 (Classical.choose h.2)).evs[e.2]'(Classical.choose_spec h.2) else default

/-- The concrete event (RefProg.lean `concEv`). -/
def ev (e : EvId) : Ev := concEv E.ν e.1 e.2 (E.sev e)

def sk (e : EvId) : Skel := (E.ev e).sk

/-- A memory operation of the execution. -/
def isMem (e : EvId) : Prop := E.has e ∧ (E.sk e).kind.isMem = true

/-- The hart runs `T`'s program from its initial state (RefProg.lean `Test.init`). -/
def conforms : Prop :=
  ∀ h < E.T.harts.length, E.st h 0 = E.T.init h ∧ ∀ k, LStep (E.T.prog h) h (E.st h k) (E.st h (k + 1))

/-- Every state's path conditions hold and every access is naturally aligned (RefProg.lean `condsOk`). -/
def condsOkI : Prop := ∀ h < E.T.harts.length, ∀ k, condsOk E.ν [E.st h k] = true

/-- An access to an I/O region (Ref.lean `isIo`). -/
def isIoI (e : EvId) : Bool :=
  E.T.io.any (fun r => decide (r.lo ≤ (E.ev e).pa ∧ (E.ev e).pa < r.hi))

/-- The I/O region of an access (Ref.lean `regionOf`). -/
def regionOfI (e : EvId) : Option IoRegion :=
  E.T.io.find? (fun r => decide (r.lo ≤ (E.ev e).pa ∧ (E.ev e).pa < r.hi))

/-! ### The load value axiom's store (Ref.lean `rfSrc`, rvwmo.adoc:315–324) -/

/-- `w` is a candidate for byte `x` of load `r`: "Stores that write that byte and that precede i in the global
memory order", "Stores that write that byte and that precede i in program order". -/
def candI (r : EvId) (x : Nat) (w : EvId) : Prop :=
  E.has w ∧ writesB (E.ev w) x = true ∧ (E.gmo w r ∨ poS E.sk w r = true)

/-- "the store that is the latest in global memory order among the following stores": `some w`, or `none` (no
candidate: the initial value). -/
def rfI (r : EvId) (x : Nat) : Option EvId → Prop
  | some w => E.candI r x w ∧ ∀ w', E.candI r x w' → w' = w ∨ E.gmo w' w
  | none => ∀ w, ¬ E.candI r x w

/-- The value a source gives byte `x` (Ref.lean `lvVal`). -/
def valI (x : Nat) : Option EvId → Nat
  | some w => wbyte (E.ev w) x
  | none => E.T.imgF x

/-! ### Preserved program order (Ref.lean §2–3, rvwmo.adoc:267–302) -/

/-- Rule 1 (Ref.lean `rule1`). -/
def rule1I (a b : EvId) : Prop := (E.sk b).kind.isStore = true ∧ overlapB (E.ev a) (E.ev b) = true

/-- Rule 2 (Ref.lean `rule2`): "a and b are loads, x is a byte read by both a and b, there is no store to x between
a and b in program order, and a and b return values for x written by different memory operations". -/
def rule2I (a b : EvId) : Prop :=
  (E.sk a).kind.isLoad = true ∧ (E.sk b).kind.isLoad = true ∧ E.isIoI a = false ∧ E.isIoI b = false ∧
    ∃ k < (E.sk a).sz, touches (E.ev b) ((E.ev a).pa + k) = true ∧
      (∀ m, E.has m → poS E.sk a m = true → poS E.sk m b = true → writesB (E.ev m) ((E.ev a).pa + k) = false) ∧
      ∃ oa ob, E.rfI a ((E.ev a).pa + k) oa ∧ E.rfI b ((E.ev a).pa + k) ob ∧ oa ≠ ob

/-- Rule 3 (Ref.lean `rule3`). -/
def rule3I (a b : EvId) : Prop :=
  (E.sk a).kind.isRmwW = true ∧ (E.sk b).kind.isLoad = true ∧ E.isIoI b = false ∧
    ∃ k < (E.sk b).sz, E.rfI b ((E.ev b).pa + k) (some a)

/-- Rule 4 (Ref.lean `rule4`). -/
def rule4I (a b : EvId) : Prop :=
  ∃ m f, E.has m ∧ (E.sk m).kind = .fence f ∧ poS E.sk a m = true ∧ poS E.sk m b = true ∧
    inPred E.sk E.isIoI f a = true ∧ inSucc E.sk E.isIoI f b = true

/-- Pairing (Ref.lean `pairedS`). -/
def pairedI (a b : EvId) : Prop :=
  (E.sk a).kind = .lr ∧ (E.sk b).kind = .sc ∧ poS E.sk a b = true ∧
    ∀ m, E.has m → poS E.sk a m = true → poS E.sk m b = true → (E.sk m).kind.isLrSc = false

/-- Rule 13 (Ref.lean `rule13`, the memory-operation reading [OWN.P6]). -/
def rule13I (a b : EvId) : Prop :=
  (E.sk b).kind.isStore = true ∧
    ∃ m, E.has m ∧ (E.sk m).kind.isMem = true ∧ poS E.sk a m = true ∧ poS E.sk m b = true ∧
      (E.sk m).adep.contains a.2 = true

/-- Rule 12 (Ref.lean `rule12`). -/
def rule12I (a b : EvId) : Prop :=
  (E.sk b).kind.isLoad = true ∧ E.isIoI b = false ∧
    ∃ m, E.has m ∧ poS E.sk a m = true ∧ poS E.sk m b = true ∧ (E.sk m).kind.isStore = true ∧
      ((E.sk m).adep.contains a.2 = true ∨ (E.sk m).ddep.contains a.2 = true) ∧
      ∃ k < (E.sk b).sz, E.rfI b ((E.ev b).pa + k) (some m)

/-- The value-independent rules 4–11 and 13 (Ref.lean `staticRules`; rules 5–7, 9–11 are Ref.lean's own). -/
def staticI (a b : EvId) : Prop :=
  E.rule4I a b ∨ rule5 E.sk E.isIoI a b = true ∨ rule6 E.sk E.isIoI a b = true ∨ rule7 E.sk E.isIoI a b = true ∨
    E.pairedI a b ∨ rule9 E.sk a b = true ∨ rule10 E.sk a b = true ∨ rule11 E.sk a b = true ∨ E.rule13I a b

/-- PRESERVED PROGRAM ORDER (Ref.lean `ppoB`). -/
def ppoI (a b : EvId) : Prop :=
  E.isMem a ∧ E.isMem b ∧ poS E.sk a b = true ∧
    (E.rule1I a b ∨ E.rule2I a b ∨ E.rule3I a b ∨ E.staticI a b ∨ E.rule12I a b)

/-- The I/O orderings (Ref.lean `ioOrdB`). -/
def ioOrdI (a b : EvId) : Prop :=
  E.isMem a ∧ E.isMem b ∧ poS E.sk a b = true ∧
    match E.regionOfI a, E.regionOfI b with
    | some ra, some rb =>
        (overlapB (E.ev a) (E.ev b) || (ra == rb && ra.strong) || ra.chan == 1 || rb.chan == 1 ||
          (ra.chan == rb.chan && ra.chan != 0)) = true
    | _, _ => False

/-! ### The axioms (Ref.lean §4) -/

/-- gmo is a strict total order of exactly the memory operations (Ref.lean `gmoWf`). -/
def gmoOk : Prop :=
  (∀ a b, E.gmo a b → E.isMem a ∧ E.isMem b) ∧ (∀ a, ¬ E.gmo a a) ∧
    (∀ a b c, E.gmo a b → E.gmo b c → E.gmo a c) ∧
    (∀ a b, E.isMem a → E.isMem b → a ≠ b → E.gmo a b ∨ E.gmo b a)

/-- Ref.lean `evWf`. -/
def evWfI : Prop :=
  ∀ e, E.has e → ((E.sk e).kind.isLoad = true → (E.ev e).rdat.length = (E.sk e).sz) ∧
    ((E.sk e).kind.isStore = true → (E.ev e).wdat.length = (E.sk e).sz)

/-- gmo conforms to preserved program order and the I/O orderings (Ref.lean `ppoAx`). -/
def ppoAxI : Prop := ∀ a b, E.ppoI a b ∨ E.ioOrdI a b → E.gmo a b

/-- THE LOAD VALUE AXIOM (Ref.lean `loadValueAx`). -/
def loadValueAxI : Prop :=
  ∀ r, E.has r → (E.sk r).kind.isLoad = true → E.isIoI r = false →
    ∀ k < (E.sk r).sz, ∃ o, E.rfI r ((E.ev r).pa + k) o ∧ (E.ev r).rdat[k]? = some (E.valI ((E.ev r).pa + k) o)

/-- THE ATOMICITY AXIOM (Ref.lean `atomicityAx`). -/
def atomicityAxI : Prop :=
  ∀ r w, E.has r → E.has w → E.pairedI r w → aligned (E.ev r) = true → aligned (E.ev w) = true →
    ∀ k < (E.sk r).sz, ∀ s, E.rfI r ((E.ev r).pa + k) (some s) →
      E.gmo s w ∧ ∀ s', E.has s' → writesB (E.ev s') ((E.ev r).pa + k) = true → s'.1 ≠ r.1 →
        ¬ (E.gmo s s' ∧ E.gmo s' w)

/-- Ref.lean `resvOk`. -/
def resvOkI (r w : EvId) : Prop :=
  ∃ R : List Nat, (∀ x, touches (E.ev r) x = true → x ∈ R) ∧ (∀ x, touches (E.ev w) x = true → x ∈ R) ∧
    ∀ s, E.has s → (E.sk s).kind.isStore = true → s.1 ≠ w.1 → (∃ x ∈ R, writesB (E.ev s) x = true) →
      ¬ (E.gmo r s ∧ E.gmo s w)

/-- THE §zalrsc SUCCESS CONDITIONS (Ref.lean `scAx`). -/
def scAxI : Prop := ∀ w, E.has w → (E.sk w).kind = .sc → ∃ r, E.has r ∧ E.pairedI r w ∧ E.resvOkI r w

/-- THE PROGRESS AXIOM (rvwmo.adoc:350–351; Ref.lean `progressAx`, literally). -/
def progressAxI : Prop :=
  ∀ e, E.isMem e → ¬ ∃ f : Nat → EvId, (∀ n m, f n = f m → n = m) ∧ ∀ n, E.gmo (f n) e

/-- **`rvwmoRefInf`**: the RVWMO reference over a possibly infinite execution (Ref.lean `rvwmoRef`). -/
def rvwmoRefInf : Prop :=
  E.gmoOk ∧ E.evWfI ∧ E.ppoAxI ∧ E.loadValueAxI ∧ E.atomicityAxI ∧ E.scAxI ∧ E.progressAxI

end IExec

/-- **AN EXECUTION OF TEST `T` THAT MAY NEVER STOP**: the harts run `T`'s program (loops allowed), the path conditions
hold, and the memory model holds. -/
def infExec (T : Test) (E : IExec) : Prop := E.T = T ∧ E.conforms ∧ E.condsOkI ∧ E.rvwmoRefInf

/-- **A FINITE PARTIAL EXECUTION of test `T`** (plan §9 Q1 "each hart has run a finite prefix of its instruction
stream, and that is itself legal"): every hart's state is reached in finitely many `LStep`s, the path conditions
hold, and the concrete execution satisfies Ref.lean's `rvwmoRef`. -/
def partExec (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) : Prop :=
  trs.length = T.harts.length ∧ (∀ h (hh : h < trs.length), LReach (T.prog h) h (T.init h) trs[h]) ∧
    condsOk ν trs = true ∧ rvwmoRef (conc T trs ν g)

end Weak.Prom.Pfx

end
