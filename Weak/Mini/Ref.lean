/-
Weak/Mini: **MiniRef — the RVWMO memory model for the fragment F** (mini plan rev 4 §2 L1; owner ruling [OWN.P18]
"I still want the semantics and the logic. Just want them minimial").

Quotes: the RISC-V ISA manual @ `e17d92a1`: the memory model `rvwmo.adoc` (copy `promising/spec/rvwmo.adoc`, i.e.
`~/dev/weak-orch/promising/spec/rvwmo.adoc`) and the base-ISA FENCE text `unpriv_rv32.adoc` (copy
`promising/spec/unpriv_rv32.adoc`, same directory).  Equal to the full reference on F: `Weak/Mini/EqRef*.lean` (E1).

## What an execution is

* EVENTS are WORD-valued: the program has ONE access size `sz` and every access is naturally aligned, so two memory
  operations access overlapping bytes iff they have the same address, and a load reads ONE value (the bytes of one
  store, or of the initial memory).  Why one store: the load value axiom picks, PER BYTE, the gmo-latest candidate
  store writing that byte; on F every store that writes one byte of the word writes ALL `sz` bytes of it (it is an
  aligned access of the same size at the same address), so every byte of the load has the same candidate set, hence
  the same latest store (or none: the initial memory for every byte).  An event id `(h, i)` is "the `i`-th load,
  store or fence of hart `h`" in program order (ALU instructions, branches, jumps and `nop` create no event).
* THE HARTS (§3) run CONCRETELY: registers hold values, a load takes the value the execution assigns to it (`V`),
  and every register carries its TAINT, the list of this hart's loads it syntactically depends on (rvwmo.adoc:
  156–246; the lists are built exactly as the full reference's `stepI` builds them).  Branches and jumps go anywhere
  (loops).  A halted hart (`pc` past its text) stays put.
* THE MEMORY MODEL (§2) is ONE axiom block `MEvs.ax` over a set of events `has`, their contents `ev` and a relation
  `gmo` (rvwmo.adoc:46–47 "the _global memory order_, a total ordering of the memory operations produced by all
  harts"); it is used twice (§4): by the possibly-infinite execution (`miniExec`, every hart runs forever) and by
  the finite cut (`miniCut`, every hart has run a finite number of steps; gmo is a list).
* RULES 3, 5, 6, 7, 8 of preserved program order are VACUOUS on F and absent: rule 3 needs an AMO or SC, rules 5–7 an
  acquire/release annotation (only AMO, LR/SC and Zalasr instructions carry one, rvwmo.adoc:124–128), rule 8 an
  LR/SC pair; none is in F.  The atomicity axiom (paired LR/SC) is vacuous for the same reason; I/O (mm-explanatory.adoc
  §I/O) is vacuous (F has no I/O region).
No `sorry`, no axiom, no `native_decide`.  Imports only `Weak.Mini.Prog` (plan §2 import discipline).
-/
import Weak.Mini.Prog

namespace Weak.Mini

/-! ## 1. Events -/

/-- An event identifier: (hart, index among that hart's loads, stores and fences). -/
abbrev EvId := Nat × Nat

/-- The kind of an event: a load operation, a store operation, or a FENCE instruction (rule 4 mentions it). -/
inductive MK where
  | ld
  | st
  | fence (f : MFence)
  deriving DecidableEq, Repr, Inhabited

/-- An event: kind, dynamic instruction index (program order), address, the value read (a load: the `sz` bytes it
returns) or written (a store: the `sz` bytes it writes), and its syntactic address, data and control dependencies as
indices of this hart's events (rvwmo.adoc:232–246).  A FENCE event's `pa` and `v` are dummies (`0`, `exec` §3): a
fence is never `isMem`, and only rule 4 looks at it, through its `kind` and `ii`. -/
structure MEv where
  kind : MK
  ii : Nat
  pa : Nat
  v : Nat
  adep : List Nat
  ddep : List Nat
  cdep : List Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. THE AXIOM BLOCK -/

/-- A candidate execution's memory side: which events exist, what they are, and the global memory order. -/
structure MEvs where
  has : EvId → Prop
  ev : EvId → MEv
  gmo : EvId → EvId → Prop

namespace MEvs

variable (A : MEvs)

/-- A load operation. -/
def isLd (e : EvId) : Prop := (A.ev e).kind = .ld

/-- A store operation. -/
def isSt (e : EvId) : Prop := (A.ev e).kind = .st

/-- A memory operation of the execution (rvwmo.adoc:66–67 "A memory operation can be either a _load operation_, a
_store operation_, or both simultaneously"; on F never both). -/
def isMem (e : EvId) : Prop := A.has e ∧ (A.isLd e ∨ A.isSt e)

/-- Program order (rvwmo.adoc:60–63 "the order in which the instructions that generate each load and store are
logically laid out in that hart's dynamic instruction stream"): same hart, earlier dynamic instruction. -/
def po (a b : EvId) : Prop := a.1 = b.1 ∧ (A.ev a).ii < (A.ev b).ii

/-- `w` is a candidate store for load `r` (rvwmo.adoc:316–324 "Stores that write that byte and that precede _i_ in
the global memory order", "Stores that write that byte and that precede _i_ in program order"; on F a store writes
the bytes of `r` iff it has `r`'s address). -/
def cand (r w : EvId) : Prop :=
  A.has w ∧ A.isSt w ∧ (A.ev w).pa = (A.ev r).pa ∧ (A.gmo w r ∨ A.po w r)

/-- THE STORE LOAD `r` READS (rvwmo.adoc:316–318 "the store that is the latest in global memory order among the
following stores"): `some w`, or `none` (no candidate: the initial memory).  FAITHFUL (one store for all bytes of an
aligned single-size load). -/
def rf (r : EvId) : Option EvId → Prop
  | some w => A.cand r w ∧ ∀ w', A.cand r w' → w' = w ∨ A.gmo w' w
  | none => ∀ w, ¬ A.cand r w

/-- Rule 1 (rvwmo.adoc:278): "_b_ is a store, and _a_ and _b_ access overlapping memory addresses".  FAITHFUL
(aligned, one size: overlapping = same address). -/
def rule1 (a b : EvId) : Prop := A.isSt b ∧ (A.ev a).pa = (A.ev b).pa

/-- Rule 2 (rvwmo.adoc:279–281): "_a_ and _b_ are loads, _x_ is a byte read by both _a_ and _b_, there is no store
to _x_ between _a_ and _b_ in program order, and _a_ and _b_ return values for _x_ written by different memory
operations".  FAITHFUL (a byte read by both = same address).  The writers are `rf`'s answers: `some w` (the store
`w`) or `none` (the INITIAL MEMORY as writer, the standard herd reading of "different memory operations").  `rf` is
functional under `gmoOk` (gmo is irreflexive and transitive, so two gmo-latest candidates coincide; `some` and
`none` exclude each other), so inside the axiom block `ax` the existential `∃ oa ob` names THE writers of `a` and
`b`. -/
def rule2 (a b : EvId) : Prop :=
  A.isLd a ∧ A.isLd b ∧ (A.ev a).pa = (A.ev b).pa ∧
    (∀ m, A.has m → A.po a m → A.po m b → ¬ (A.isSt m ∧ (A.ev m).pa = (A.ev a).pa)) ∧
    ∃ oa ob, A.rf a oa ∧ A.rf b ob ∧ oa ≠ ob

/-- FENCE predecessor set (`promising/spec/unpriv_rv32.adoc`:770–776): memory reads (R) and writes (W); F has no I/O
access, so the I and O bits order nothing. -/
def inPred (f : MFence) (e : EvId) : Prop := (A.isLd e ∧ f.pr = true) ∨ (A.isSt e ∧ f.pw = true)

/-- FENCE successor set. -/
def inSucc (f : MFence) (e : EvId) : Prop := (A.isLd e ∧ f.sr = true) ∨ (A.isSt e ∧ f.sw = true)

/-- Rule 4 (rvwmo.adoc:286): "There is a FENCE instruction that orders _a_ before _b_";
`promising/spec/unpriv_rv32.adoc`:818–819 "A FENCE (with fm=0000) orders all memory operations in its predecessor
set before all memory operations in its successor set".  FAITHFUL. -/
def rule4 (a b : EvId) : Prop :=
  ∃ m f, A.has m ∧ (A.ev m).kind = .fence f ∧ A.po a m ∧ A.po m b ∧ A.inPred f a ∧ A.inSucc f b

/-- Rule 9 (rvwmo.adoc:293): "_b_ has a syntactic address dependency on _a_".  FAITHFUL. -/
def rule9 (a b : EvId) : Prop := a.1 = b.1 ∧ a.2 ∈ (A.ev b).adep

/-- Rule 10 (rvwmo.adoc:294): "_b_ has a syntactic data dependency on _a_" (rvwmo.adoc:237–238: "_b_ is a store
operation").  FAITHFUL. -/
def rule10 (a b : EvId) : Prop := A.isSt b ∧ a.1 = b.1 ∧ a.2 ∈ (A.ev b).ddep

/-- Rule 11 (rvwmo.adoc:295): "_b_ is a store, and _b_ has a syntactic control dependency on _a_".  FAITHFUL. -/
def rule11 (a b : EvId) : Prop := A.isSt b ∧ a.1 = b.1 ∧ a.2 ∈ (A.ev b).cdep

/-- Rule 12 (rvwmo.adoc:298–300): "_b_ is a load, and there exists some store _m_ between _a_ and _b_ in program
order such that _m_ has an address or data dependency on _a_, and _b_ returns a value written by _m_".  FAITHFUL. -/
def rule12 (a b : EvId) : Prop :=
  A.isLd b ∧ ∃ m, A.has m ∧ A.po a m ∧ A.po m b ∧ A.isSt m ∧ (a.2 ∈ (A.ev m).adep ∨ a.2 ∈ (A.ev m).ddep) ∧
    A.rf b (some m)

/-- Rule 13 (rvwmo.adoc:301–302): "_b_ is a store, and there exists some instruction _m_ between _a_ and _b_ in
program order such that _m_ has an address dependency on _a_"; `m` ranges over memory operations (the manual's
formal reading `[R];addr;[M];po;[W]`, owner ruling [OWN.P6]).  FAITHFUL to [OWN.P6]'s `[R];addr;[M];po;[W]`; it
would be STRONGER than the letter only if a non-memory instruction `m` could carry an address dependency on `a`, and
on F none can (only loads and stores have an address operand). -/
def rule13 (a b : EvId) : Prop :=
  A.isSt b ∧ ∃ m, A.isMem m ∧ A.po a m ∧ A.po m b ∧ a.2 ∈ (A.ev m).adep

/-- PRESERVED PROGRAM ORDER (rvwmo.adoc:269–274 "memory operation _a_ precedes memory operation _b_ in preserved
program order (and hence also in the global memory order) if _a_ precedes _b_ in program order, _a_ and _b_ both
access regular main memory (rather than I/O regions), and any of the following hold"): rules 1, 2, 4, 9–13 (3, 5–8
vacuous on F, file header). -/
def ppo (a b : EvId) : Prop :=
  A.isMem a ∧ A.isMem b ∧ A.po a b ∧
    (A.rule1 a b ∨ A.rule2 a b ∨ A.rule4 a b ∨ A.rule9 a b ∨ A.rule10 a b ∨ A.rule11 a b ∨ A.rule12 a b ∨
      A.rule13 a b)

/-- gmo is a strict total order of exactly the memory operations (rvwmo.adoc:46–47). -/
def gmoOk : Prop :=
  (∀ a b, A.gmo a b → A.isMem a ∧ A.isMem b) ∧ (∀ a, ¬ A.gmo a a) ∧
    (∀ a b c, A.gmo a b → A.gmo b c → A.gmo a c) ∧
    (∀ a b, A.isMem a → A.isMem b → a ≠ b → A.gmo a b ∨ A.gmo b a)

/-- gmo conforms to preserved program order (rvwmo.adoc:307–310). -/
def ppoAx : Prop := ∀ a b, A.ppo a b → A.gmo a b

/-- The value source `o` gives load `r`: the store's value, or (`none`) the initial word at `r`'s address. -/
def valOf (ini : Nat → Nat) (r : EvId) : Option EvId → Nat
  | some w => (A.ev w).v
  | none => ini (A.ev r).pa

/-- THE LOAD VALUE AXIOM (rvwmo.adoc:316–324): "Each byte of each load _i_ returns the value written to that byte by
the store that is the latest in global memory order among the following stores: 1. Stores that write that byte and
that precede _i_ in the global memory order 2. Stores that write that byte and that precede _i_ in program order";
no such store: the initial memory `ini` (the word at the load's address). -/
def loadValueAx (ini : Nat → Nat) : Prop :=
  ∀ r, A.has r → A.isLd r → ∃ o, A.rf r o ∧ (A.ev r).v = A.valOf ini r o

/-- THE PROGRESS AXIOM (rvwmo.adoc:350–351): "No memory operation may be preceded in the global memory order by an
infinite sequence of other memory operations" (an injective sequence of gmo-predecessors). -/
def progressAx : Prop :=
  ∀ e, A.isMem e → ¬ ∃ f : Nat → EvId, (∀ n m, f n = f m → n = m) ∧ ∀ n, A.gmo (f n) e

/-- **THE AXIOM BLOCK** (rvwmo.adoc:307–310 "An execution of a RISC-V program obeys the RVWMO memory consistency
model only if there exists a global memory order conforming to preserved program order and satisfying the _load
value axiom_, the _atomicity axiom_, and the _progress axiom_"; atomicity vacuous on F). -/
def ax (ini : Nat → Nat) : Prop := A.gmoOk ∧ A.ppoAx ∧ A.loadValueAx ini ∧ A.progressAx

/-- Every memory operation is naturally aligned (F's scope: aligned accesses only). -/
def aligned (sz : Nat) : Prop := ∀ e, A.isMem e → (A.ev e).pa % sz = 0

end MEvs

/-! ## 3. The harts (concrete, with loops) -/

/-! The values (`two64`, `MAlu.eval`, `MBrC.eval`, `sext`) are in `Weak/Mini/Val.lean`. -/

/-- The register value of a load returning the `sz`-byte value `w` (`sgn`: sign-extending). -/
def ldExt (sz : Nat) (sgn : Bool) (w : Nat) : Nat := if sgn then sext sz w else w

/-- A hart's state: program counter, registers (value, taint), its events so far, the dynamic instruction index,
and the control taint (the union of the taints of the sources of every po-earlier branch, rvwmo.adoc:242–246). -/
structure MSt where
  pc : Nat
  regs : Nat → Nat × List Nat
  evs : List MEv
  ii : Nat
  ctl : List Nat

/-- Read register `r` (value, taint): `x0` (and any number outside `1 … 31`) reads 0 with no dependency
(rvwmo.adoc:174, :192). -/
def MSt.rd (s : MSt) (r : Nat) : Nat × List Nat := if 0 < r ∧ r < 32 then s.regs r else (0, [])

/-- Write register `r`; writes to `x0` (and outside `1 … 31`) are ignored. -/
def MSt.wr (s : MSt) (r : Nat) (x : Nat × List Nat) : MSt :=
  if 0 < r ∧ r < 32 then { s with regs := fun r' => if r' = r then x else s.regs r' } else s

/-- Append an event. -/
def MSt.emit (s : MSt) (e : MEv) : MSt := { s with evs := s.evs ++ [e] }

/-- Advance past the instruction. -/
def MSt.adv (s : MSt) : MSt := { s with pc := s.pc + 1, ii := s.ii + 1 }

/-- Hart `h`'s initial state. -/
def MProg.init (P : MProg) (h : Nat) : MSt :=
  { pc := 0, regs := fun r => (P.reg0 h r % two64, []), evs := [], ii := 0, ctl := [] }

/-- One instruction of hart `h` (access size `sz`, load values `V`).  Taints (rvwmo.adoc:206–226): a load's
destination depends on the load alone; an ALU result on the union of its sources' taints; an access's address
dependencies are the taint of `rs1`, a store's data dependencies the taint of `rs2`, its control dependencies the
control taint. -/
def exec (sz h : Nat) (V : EvId → Nat) (s : MSt) : MI → MSt
  | .alui op rd rs1 imm =>
      let (v1, t1) := s.rd rs1
      (s.wr rd (op.eval v1 (imm % two64), t1)).adv
  | .alu op rd rs1 rs2 =>
      let (v1, t1) := s.rd rs1
      let (v2, t2) := s.rd rs2
      (s.wr rd (op.eval v1 v2, t1 ++ t2)).adv
  | .load sgn rd rs1 off =>
      let (v1, t1) := s.rd rs1
      let i := s.evs.length
      let w := V (h, i) % 2 ^ (8 * sz)
      ((s.emit ⟨.ld, s.ii, MAlu.add.eval v1 (off % two64), w, t1, [], s.ctl⟩).wr rd (ldExt sz sgn w, [i])).adv
  | .store rs2 rs1 off =>
      let (v1, t1) := s.rd rs1
      let (v2, t2) := s.rd rs2
      (s.emit ⟨.st, s.ii, MAlu.add.eval v1 (off % two64), v2 % 2 ^ (8 * sz), t1, t2, s.ctl⟩).adv
  | .fence f => (s.emit ⟨.fence f, s.ii, 0, 0, [], [], []⟩).adv
  | .br c rs1 rs2 tgt =>
      let (v1, t1) := s.rd rs1
      let (v2, t2) := s.rd rs2
      { s with pc := if c.eval v1 v2 then tgt else s.pc + 1, ii := s.ii + 1, ctl := s.ctl ++ t1 ++ t2 }
  | .jmp tgt => { s with pc := tgt, ii := s.ii + 1 }
  | .nop => s.adv

/-- One step of hart `h`: the instruction at `pc`, or (halted) stay. -/
def mstep (P : MProg) (V : EvId → Nat) (h : Nat) (s : MSt) : MSt :=
  match (P.prog h)[s.pc]? with
  | some i => exec P.sz h V s i
  | none => s

/-- Hart `h`'s state after `k` steps. -/
def mrun (P : MProg) (V : EvId → Nat) (h : Nat) : Nat → MSt
  | 0 => P.init h
  | k + 1 => mstep P V h (mrun P V h k)

/-- The initial value of the word at `a` (its low `sz` bytes). -/
def MProg.ini (P : MProg) (a : Nat) : Nat := P.img0 a % 2 ^ (8 * P.sz)

/-! ## 4. Executions: the possibly-infinite run and the finite cut -/

/-- A (possibly infinite) candidate execution: the value every load returns, and the global memory order. -/
structure MExec where
  V : EvId → Nat
  gmo : EvId → EvId → Prop

/-- Event `e` exists: some state of its hart's run has it. -/
def MExec.has (P : MProg) (X : MExec) (e : EvId) : Prop :=
  e.1 < P.harts.length ∧ ∃ k, e.2 < (mrun P X.V e.1 k).evs.length

/-- Event `e` (any state of the run that has it: they agree, the event list only grows). -/
noncomputable def MExec.ev (P : MProg) (X : MExec) (e : EvId) : MEv :=
  open Classical in
  if hk : ∃ k, e.2 < (mrun P X.V e.1 k).evs.length then
    (mrun P X.V e.1 (Classical.choose hk)).evs[e.2]'(Classical.choose_spec hk)
  else default

/-- The execution's memory side. -/
noncomputable def MExec.evs (P : MProg) (X : MExec) : MEvs := ⟨X.has P, X.ev P, X.gmo⟩

/-- **AN EXECUTION OF `P` THAT MAY NEVER STOP**: every hart runs forever (halted harts stay put), every access is
aligned, and the axiom block holds. -/
def miniExec (P : MProg) (X : MExec) : Prop := (X.evs P).aligned P.sz ∧ (X.evs P).ax P.ini

/-- The position of `e` in `g` (its length when absent). -/
def posIn (g : List EvId) (e : EvId) : Nat :=
  match g with
  | [] => 0
  | x :: t => if x = e then 0 else posIn t e + 1

/-- A finite candidate execution: the number of steps every hart has run, the load values, gmo as a list. -/
structure MCut where
  ks : Nat → Nat
  V : EvId → Nat
  g : List EvId

/-- Hart `h`'s state in the cut. -/
def MCut.st (P : MProg) (C : MCut) (h : Nat) : MSt := mrun P C.V h (C.ks h)

/-- The cut's memory side: the events of the harts' states, gmo = the order of the list. -/
def MCut.evs (P : MProg) (C : MCut) : MEvs :=
  { has := fun e => e.1 < P.harts.length ∧ e.2 < (C.st P e.1).evs.length
    ev := fun e => ((C.st P e.1).evs[e.2]?).getD default
    gmo := fun a b => a ∈ C.g ∧ b ∈ C.g ∧ posIn C.g a < posIn C.g b }

/-- **A FINITE PARTIAL EXECUTION OF `P`**: every hart has run finitely many steps, the gmo list lists every memory
operation exactly once, every access is aligned, and the axiom block holds. -/
def miniCut (P : MProg) (C : MCut) : Prop :=
  C.g.Nodup ∧ (∀ e, e ∈ C.g ↔ (C.evs P).isMem e) ∧ (C.evs P).aligned P.sz ∧ (C.evs P).ax P.ini

/-! ## 5. Program well-formedness (the scope of E1) -/

/-- Branch and jump targets lie inside the text (or at its end). -/
def MI.tgtOk (n : Nat) : MI → Prop
  | .br _ _ _ t => t ≤ n
  | .jmp t => t ≤ n
  | _ => True

/-- Every register the instruction names is one of `x0 … x31` (Prog.lean; rvwmo.adoc's dependencies are through these
registers). -/
def MI.regOk : MI → Prop
  | .alui _ rd rs1 _ => rd < 32 ∧ rs1 < 32
  | .alu _ rd rs1 rs2 => rd < 32 ∧ rs1 < 32 ∧ rs2 < 32
  | .load _ rd rs1 _ => rd < 32 ∧ rs1 < 32
  | .store rs2 rs1 _ => rs1 < 32 ∧ rs2 < 32
  | .br _ rs1 rs2 _ => rs1 < 32 ∧ rs2 < 32
  | _ => True

/-- [MiniP3 (0)] Every ALU immediate is a 64-bit value (real RISC-V immediates are 12-bit sign-extended, so this is
a scope bound, not a fidelity point).  Needed by L4 (`mini_complete`): on `slti`/`sltiu` the reference compares
`imm % 2^64` (`exec` above) and the machine the raw `imm` (Mach.lean `instrNext`, as machine v2's MachCert); for
`imm ≥ 2^64` they disagree (PROGRESS-MiniP2D.md finding 1; mini plan rev 4 §6). -/
def MI.immOk : MI → Prop
  | .alui _ _ _ imm => imm < two64
  | _ => True

/-- A WELL-FORMED F PROGRAM: the access size is a RISC-V one (1, 2, 4 or 8 bytes: `lb`/`lh`/`lw`/`ld`), the image is
`sz`-aligned, branch and jump targets lie inside the texts, every register named is `< 32`, and every ALU immediate is
`< 2^64` ([MiniP3 (0)]: `MI.immOk`).  E1 is stated for these programs; E2 needs only the first two (`Mach.progWf`,
implied: `MProg.wf_progWf`, Wf.lean). -/
def MProg.wf (P : MProg) : Prop :=
  (P.sz = 1 ∨ P.sz = 2 ∨ P.sz = 4 ∨ P.sz = 8) ∧ (∀ p ∈ P.img, p.1 % P.sz = 0) ∧
    ∀ h, ∀ i ∈ P.prog h, i.tgtOk (P.prog h).length ∧ i.regOk ∧ i.immOk

theorem MProg.wf.sz_pos {P : MProg} (hwf : P.wf) : 0 < P.sz := by
  rcases hwf.1 with h | h | h | h <;> omega

/-- Loop-free: every branch and jump goes forward. -/
def MProg.fwd (P : MProg) : Prop :=
  ∀ h j c rs1 rs2 t, (P.prog h)[j]? = some (MI.br c rs1 rs2 t) ∨ (P.prog h)[j]? = some (MI.jmp t) → j < t

/-- Every hart of the cut has halted. -/
def MCut.halted (P : MProg) (C : MCut) : Prop := ∀ h < P.harts.length, (C.st P h).pc = (P.prog h).length

end Weak.Mini
