/-
Weak/Prom: **the program semantics of the reference** — a small RV64 litmus ISA, its symbolic per-path
interpreter with SYNTACTIC dependency tracking, and the executions of a test under `rvwmoRef`
(S0-P part (1); `Weak/Prom/Ref.lean` is the memory model).

## What a test's executions are

A test is a list of hart programs (loop-free: every branch and jump goes FORWARD), initial registers and initial
memory.  Hart `h` runs SYMBOLICALLY along a path (a list of choices: one per conditional branch — taken or not —
and one per SC — success or failure): register values are expressions `Ex` over the bytes returned by this
execution's loads (`Ex.ld e`: the value of load event `e`), and every register carries its TAINT, the set of this
hart's memory events the register has a syntactic dependency on.  An EXECUTION of the test is a path per hart, a
valuation `ν` of the load events (the bytes each load returns) and a global memory order `gmo`, such that the
path conditions hold under `ν` (`condsOk`) and the concretised execution satisfies `rvwmoRef` (`progExec`).
Every load value is QUANTIFIED, not computed: the load value axiom inside `rvwmoRef` is what constrains it.

## Syntactic dependencies (rvwmo.adoc:156–246 and the listing :400–884)

Taint propagation is the definition read operationally: "Instruction j has a syntactic dependency on instruction i
via destination register s of i and source register r of j if … s is the same as r, and no instruction
program-ordered between i and j has r as a destination register, [or] there is an instruction m program-ordered
between i and j such that … m carries a dependency from p to q" (:210–226).  So a register's taint is
  * `{e}` after a memory instruction generating event `e` writes it as a DESTINATION — loads, LR, AMO, and a
    SUCCESSFUL SC (the listing's † "does not carry a dependency from any source register to any destination
    register"; sc's "_rd_ ^*^ if successful", :589, :619);
  * the union of the sources' taints after a non-memory instruction ("Most non-memory instructions carry a
    dependency from each of their source registers to each of their destination registers", :206–208);
  * unchanged after a FAILED SC (its `rd` is not a destination: :589 "if successful"), though `rd` now holds the
    failure code 1 (zalrsc.adoc:62–63 "The failure code with value 1 encodes an unspecified failure").
`x0` is never a source nor a destination (:174, :192).  An access's address dependencies are the taint of its
address source `rs1`, its data dependencies the taint of `rs2` (the listing's ^A^ / ^D^), its control dependencies
the union of the taints of the sources of every po-earlier branch (:242–246; jumps here are direct, `jal x0`, with no
source).  Expressions are never simplified, so `xor t,a0,a0` keeps the dependency (EX-10 "must be enforced even if
the calculation could seemingly be optimized away"); `varsOk` (RefCheck) checks that an expression's load
variables are within the matching taint.

## Annotations (rvwmo.adoc:124–128)

"An AMO or lr instruction with aq set has an acquire-RCsc annotation. An AMO or sc instruction with rl set has a
release-RCsc annotation. An AMO, lr, or sc instruction with both aq and rl set has both acquire-RCsc and
release-RCsc annotations."  So `lr.rl` and `sc.aq` carry nothing (Table S probe LRSC-AQRL).

## Scope of the front end (phase 1, [OWN.P3]; recorded in PROGRESS-S0P1.md)

* ALIGNED ACCESSES ONLY: `condsOk` requires every access address to be naturally aligned under `ν`.  The execution
  model (`Ref.lean`) supports decomposed misaligned operations; the front end does not generate them (NA-9/F-S1,
  S1M-def SA-1 open).  For tests whose addresses are aligned in every execution this is no restriction.
* No CSRs, no FP, no traps, no `jalr`, no translation (translation off: [OWN.P3]); no I/O loads in the enumerator.
-/
import Weak.Prom.Ref

namespace Weak.Prom.Ref

/-! ## 1. 64-bit arithmetic on `Nat` -/

/-- Integer ALU operations (rvwmo.adoc listing: all carry from `rs1`/`rs2` to `rd`). -/
inductive Alu where
  | add | sub | xor | or | and | sll | srl | sra | slt | sltu | mul
  deriving DecidableEq, Repr, Inhabited

/-- Branch conditions. -/
inductive BrC where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr, Inhabited

/-- AMO operations (zaamo.adoc). -/
inductive AmoOp where
  | swap | add | xor | and | or | min | max | minu | maxu
  deriving DecidableEq, Repr, Inhabited

/-- `2^64`. -/
def two64 : Nat := 18446744073709551616

/-- Signed less-than on `n`-bit values (flip the sign bit, compare unsigned). -/
def sltN (n a b : Nat) : Bool := decide ((a ^^^ 2 ^ (n - 1)) < (b ^^^ 2 ^ (n - 1)))

def aluOp : Alu → Nat → Nat → Nat
  | .add, a, b => (a + b) % two64
  | .sub, a, b => (a + (two64 - b % two64)) % two64
  | .xor, a, b => a ^^^ b
  | .or, a, b => a ||| b
  | .and, a, b => a &&& b
  | .sll, a, b => (a <<< (b % 64)) % two64
  | .srl, a, b => a >>> (b % 64)
  | .sra, a, b =>
      if a < 2 ^ 63 then a >>> (b % 64) else (a >>> (b % 64)) ||| (two64 - 2 ^ (64 - b % 64))
  | .slt, a, b => if sltN 64 a b then 1 else 0
  | .sltu, a, b => if a < b then 1 else 0
  | .mul, a, b => (a * b) % two64

def brEval : BrC → Nat → Nat → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => sltN 64 a b
  | .ge, a, b => !sltN 64 a b
  | .ltu, a, b => decide (a < b)
  | .geu, a, b => !decide (a < b)

/-- An AMO's stored value on `sz`-byte operands (zaamo.adoc:8–11 "apply a binary operator to the loaded value and the
original value in rs2, then store the result"). -/
def amoOp (op : AmoOp) (sz a b : Nat) : Nat :=
  let m := 2 ^ (8 * sz)
  match op with
  | .swap => b % m
  | .add => (a + b) % m
  | .xor => (a ^^^ b) % m
  | .and => a &&& b
  | .or => (a ||| b) % m
  | .min => if sltN (8 * sz) a b then a else b
  | .max => if sltN (8 * sz) a b then b else a
  | .minu => if a < b then a else b
  | .maxu => if a < b then b else a

/-- Little-endian bytes of a value. -/
def byteList (v sz : Nat) : List Nat := (List.range sz).map (fun k => (v >>> (8 * k)) % 256)

/-- The value of little-endian bytes. -/
def bytesVal (bs : List Nat) : Nat := bs.foldr (fun b acc => b + 256 * acc) 0

/-- Sign extension of an `sz`-byte value to 64 bits. -/
def sext (sz v : Nat) : Nat :=
  if sz < 8 ∧ 2 ^ (8 * sz - 1) ≤ v then v + (two64 - 2 ^ (8 * sz)) else v

/-! ## 2. Symbolic values -/

/-- A symbolic register value: a constant, the (sign- or zero-extended) value returned by a load event, an ALU
result, or an AMO's stored value. -/
inductive Ex where
  | c (v : Nat)
  | ld (e : EvId) (sz : Nat) (sgn : Bool)
  | bin (op : Alu) (a b : Ex)
  | amo (op : AmoOp) (sz : Nat) (a b : Ex)
  deriving DecidableEq, Repr, Inhabited

/-- A valuation: the bytes each load event returns. -/
abbrev Val := EvId → List Nat

def Ex.eval (ν : Val) : Ex → Nat
  | .c v => v % two64
  | .ld e sz sgn =>
      let v := bytesVal ((ν e).take sz) % 2 ^ (8 * sz)
      if sgn then sext sz v else v
  | .bin op a b => aluOp op (a.eval ν) (b.eval ν)
  | .amo op sz a b => amoOp op sz (a.eval ν % 2 ^ (8 * sz)) (b.eval ν % 2 ^ (8 * sz))

/-- The load events an expression mentions. -/
def Ex.vars : Ex → List EvId
  | .c _ => []
  | .ld e _ _ => [e]
  | .bin _ a b => a.vars ++ b.vars
  | .amo _ _ a b => a.vars ++ b.vars

theorem Ex.eval_congr (ν₁ ν₂ : Val) :
    ∀ x : Ex, (∀ v ∈ x.vars, ν₁ v = ν₂ v) → x.eval ν₁ = x.eval ν₂
  | .c _, _ => rfl
  | .ld e _ _, h => by simp only [Ex.eval, h e (by simp [Ex.vars])]
  | .bin _ a b, h => by
      simp only [Ex.vars, List.mem_append] at h
      simp only [Ex.eval, Ex.eval_congr ν₁ ν₂ a (fun v hv => h v (Or.inl hv)),
        Ex.eval_congr ν₁ ν₂ b (fun v hv => h v (Or.inr hv))]
  | .amo _ _ a b, h => by
      simp only [Ex.vars, List.mem_append] at h
      simp only [Ex.eval, Ex.eval_congr ν₁ ν₂ a (fun v hv => h v (Or.inl hv)),
        Ex.eval_congr ν₁ ν₂ b (fun v hv => h v (Or.inr hv))]

/-! ## 3. The litmus ISA -/

/-- Instructions (RV64I subset + Zalrsc/Zaamo + FENCE/FENCE.TSO).  Registers are `0 … 31`, sizes in bytes,
immediates/offsets as 64-bit two's-complement naturals, branch/jump targets as ABSOLUTE instruction indices
(forward only). -/
inductive Instr where
  /-- `op rd, rs1, imm` (`addi`, `xori`, `ori`, `andi`, `slli`, …; `li rd, v` is `addi rd, x0, v`). -/
  | alui (op : Alu) (rd rs1 imm : Nat)
  | alu (op : Alu) (rd rs1 rs2 : Nat)
  /-- `l{b,h,w,d}[u] rd, off(rs1)`: `sgn` = sign-extending. -/
  | load (sz : Nat) (sgn : Bool) (rd rs1 off : Nat)
  /-- `s{b,h,w,d} rs2, off(rs1)`. -/
  | store (sz : Nat) (rs2 rs1 off : Nat)
  /-- Zalasr load-acquire `l{b,h,w,d}.aq[rl] rd, (rs1)` (unpriv_zalasr.adoc:68–69 "The instruction always has an
  acquire-RCsc annotation, and if the bit rl is set the instruction has a release-RCsc annotation"; :36
  "places the sign-extended value into the register rd"). -/
  | loadAq (sz : Nat) (rl : Bool) (rd rs1 : Nat)
  /-- Zalasr store-release `s{b,h,w,d}.[aq]rl rs2, (rs1)` (unpriv_zalasr.adoc:122–123 "The instruction always has a
  release-RCsc annotation, and if the bit aq is set the instruction has an acquire-RCsc annotation"). -/
  | storeRl (sz : Nat) (aq : Bool) (rs2 rs1 : Nat)
  /-- A HYPOTHETICAL RCpc load-acquire (`aqrl`: also release-RCpc).  Not a RISC-V instruction: rvwmo.adoc:150–153
  "the ISA does not currently contain native RCpc load-acquire or store-release instructions, the RVWMO model
  itself is designed to be forwards-compatible with the potential addition of them".  Used ONLY by the oracle run to
  reproduce herd's reading of the litmus mnemonic `lw.aq` (no verdict theorem uses it). -/
  | loadAqPc (sz : Nat) (rl : Bool) (rd rs1 : Nat)
  /-- A HYPOTHETICAL RCpc store-release (see `loadAqPc`). -/
  | storeRlPc (sz : Nat) (aq : Bool) (rs2 rs1 : Nat)
  | lr (sz : Nat) (aq rl : Bool) (rd rs1 : Nat)
  | sc (sz : Nat) (aq rl : Bool) (rd rs2 rs1 : Nat)
  | amo (op : AmoOp) (sz : Nat) (aq rl : Bool) (rd rs2 rs1 : Nat)
  | fence (f : FenceSet)
  | fenceTso
  | br (c : BrC) (rs1 rs2 tgt : Nat)
  /-- `jal x0, tgt` (no source, no destination). -/
  | jmp (tgt : Nat)
  /-- `csrrs rd, csr, x0` of a CSR that no instruction of the test writes (e.g. `misa`), whose value is `v`: `rd` is
  a destination (rvwmo.adoc:192–195) with no dependency (the CSR is a source, :180–182, but has no po-earlier
  destination writer), so the write KILLS any earlier dependency of `rd` (:214–216). -/
  | csrr (rd v : Nat)
  /-- `fence.i`: no source or destination register (listing :481) and not a FENCE in rule 4's sense (it orders
  instruction fetches only, zifencei.adoc); for data-memory ordering it is a no-op. -/
  | fencei
  | nop
  deriving DecidableEq, Repr, Inhabited

/-- A symbolic event: its skeleton, address expression and stored-value expression. -/
structure SEv where
  sk : Skel
  addr : Ex
  wval : Ex
  deriving DecidableEq, Repr, Inhabited

/-- A path condition: branch `c a b` was taken (`true`) or not. -/
abbrev PCond := BrC × Ex × Ex × Bool

/-- The symbolic state of one hart. -/
structure SSt where
  pc : Nat
  regs : List (Ex × List Nat)
  evs : List SEv
  ii : Nat
  ctl : List Nat
  conds : List PCond
  deriving Inhabited

def SSt.rd (s : SSt) (r : Nat) : Ex × List Nat :=
  if r = 0 then (.c 0, []) else (s.regs[r]?).getD (.c 0, [])

def SSt.wr (s : SSt) (r : Nat) (v : Ex × List Nat) : SSt :=
  if r = 0 then s else { s with regs := s.regs.set r v }

/-- The result of one instruction. -/
inductive StepR where
  | stuck
  | next (s : SSt)
  | fork (t f : SSt)

/-- Append an event and advance past the instruction. -/
def SSt.emit (s : SSt) (se : SEv) : SSt := { s with evs := s.evs ++ [se] }

def SSt.adv (s : SSt) : SSt := { s with pc := s.pc + 1, ii := s.ii + 1 }

def fR : FenceSet := ⟨true, false, false, false, true, true, false, false⟩   -- fence r,rw
def fW : FenceSet := ⟨false, true, false, false, false, true, false, false⟩  -- fence w,w

/-- One instruction of hart `h` in a program of length `n` (see the file header for each rule's text). -/
def stepI (h n : Nat) (s : SSt) : Instr → StepR
  | .alui op rd rs1 imm =>
      let (e1, t1) := s.rd rs1
      .next ((s.wr rd (.bin op e1 (.c imm), t1)).adv)
  | .alu op rd rs1 rs2 =>
      let (e1, t1) := s.rd rs1
      let (e2, t2) := s.rd rs2
      .next ((s.wr rd (.bin op e1 e2, t1 ++ t2)).adv)
  | .load sz sgn rd rs1 off =>
      let (e1, t1) := s.rd rs1
      let i := s.evs.length
      let se : SEv := ⟨{ kind := .ld, ii := s.ii, sz := sz, adep := t1, cdep := s.ctl },
        .bin .add e1 (.c off), .c 0⟩
      .next (((s.emit se).wr rd (.ld (h, i) sz sgn, [i])).adv)
  | .store sz rs2 rs1 off =>
      let (e1, t1) := s.rd rs1
      let (e2, t2) := s.rd rs2
      let se : SEv := ⟨{ kind := .st, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl },
        .bin .add e1 (.c off), e2⟩
      .next ((s.emit se).adv)
  | .loadAq sz rl rd rs1 =>
      let (e1, t1) := s.rd rs1
      let i := s.evs.length
      let sk : Skel := { kind := .ld, ii := s.ii, sz := sz, aqSc := true, rlSc := rl, adep := t1, cdep := s.ctl }
      .next (((s.emit ⟨sk, e1, .c 0⟩).wr rd (.ld (h, i) sz true, [i])).adv)
  | .storeRl sz aq rs2 rs1 =>
      let (e1, t1) := s.rd rs1
      let (e2, t2) := s.rd rs2
      let sk : Skel := { kind := .st, ii := s.ii, sz := sz, aqSc := aq, rlSc := true, adep := t1, ddep := t2,
                         cdep := s.ctl }
      .next ((s.emit ⟨sk, e1, e2⟩).adv)
  | .loadAqPc sz rl rd rs1 =>
      let (e1, t1) := s.rd rs1
      let i := s.evs.length
      let sk : Skel := { kind := .ld, ii := s.ii, sz := sz, aqPc := true, rlPc := rl, adep := t1, cdep := s.ctl }
      .next (((s.emit ⟨sk, e1, .c 0⟩).wr rd (.ld (h, i) sz true, [i])).adv)
  | .storeRlPc sz aq rs2 rs1 =>
      let (e1, t1) := s.rd rs1
      let (e2, t2) := s.rd rs2
      let sk : Skel := { kind := .st, ii := s.ii, sz := sz, aqPc := aq, rlPc := true, adep := t1, ddep := t2,
                         cdep := s.ctl }
      .next ((s.emit ⟨sk, e1, e2⟩).adv)
  | .lr sz aq rl rd rs1 =>
      let (e1, t1) := s.rd rs1
      let i := s.evs.length
      let sk : Skel := { kind := .lr, ii := s.ii, sz := sz, aqSc := aq, rlSc := (aq && rl), adep := t1, cdep := s.ctl }
      let se : SEv := ⟨sk, e1, .c 0⟩
      .next (((s.emit se).wr rd (.ld (h, i) sz true, [i])).adv)
  | .sc sz aq rl rd rs2 rs1 =>
      let (e1, t1) := s.rd rs1
      let (e2, t2) := s.rd rs2
      let i := s.evs.length
      let okk : Skel := { kind := .sc, ii := s.ii, sz := sz, aqSc := (aq && rl), rlSc := rl, adep := t1,
                          ddep := t2, cdep := s.ctl }
      let ok : SEv := ⟨okk, e1, e2⟩
      let ko : SEv := ⟨{ kind := .scFail, ii := s.ii, sz := sz, adep := t1, ddep := t2, cdep := s.ctl },
        e1, .c 0⟩
      .fork (((s.emit ok).wr rd (.c 0, [i])).adv) (((s.emit ko).wr rd (.c 1, (s.rd rd).2)).adv)
  | .amo op sz aq rl rd rs2 rs1 =>
      let (e1, t1) := s.rd rs1
      let (e2, t2) := s.rd rs2
      let i := s.evs.length
      let sk : Skel := { kind := .amo, ii := s.ii, sz := sz, aqSc := aq, rlSc := rl, adep := t1, ddep := t2,
                         cdep := s.ctl }
      let se : SEv := ⟨sk, e1, .amo op sz (.ld (h, i) sz true) e2⟩
      .next (((s.emit se).wr rd (.ld (h, i) sz true, [i])).adv)
  | .fence f => .next ((s.emit ⟨{ kind := .fence f, ii := s.ii, sz := 0 }, .c 0, .c 0⟩).adv)
  | .fenceTso =>
      .next (((s.emit ⟨{ kind := .fence fR, ii := s.ii, sz := 0 }, .c 0, .c 0⟩).emit
        ⟨{ kind := .fence fW, ii := s.ii, sz := 0 }, .c 0, .c 0⟩).adv)
  | .br c rs1 rs2 tgt =>
      if tgt ≤ s.pc ∨ n < tgt then .stuck else
      let (e1, t1) := s.rd rs1
      let (e2, t2) := s.rd rs2
      let s' := { s with ii := s.ii + 1, ctl := s.ctl ++ t1 ++ t2 }
      .fork { s' with pc := tgt, conds := s.conds ++ [(c, e1, e2, true)] }
        { s' with pc := s.pc + 1, conds := s.conds ++ [(c, e1, e2, false)] }
  | .jmp tgt => if tgt ≤ s.pc ∨ n < tgt then .stuck else .next { s with pc := tgt, ii := s.ii + 1 }
  | .csrr rd v => .next ((s.wr rd (.c v, [])).adv)
  | .fencei => .next s.adv
  | .nop => .next s.adv

/-- Run hart `h` of program `p` along the choices `ch` (consumed by forks; must be used up exactly). -/
def symRun (p : List Instr) (h : Nat) : Nat → SSt → List Bool → Option SSt
  | 0, _, _ => none
  | fuel + 1, s, ch =>
      if s.pc = p.length then (if ch = [] then some s else none) else
      match p[s.pc]? with
      | none => none
      | some i =>
          match stepI h p.length s i with
          | .stuck => none
          | .next s' => symRun p h fuel s' ch
          | .fork t f =>
              match ch with
              | [] => none
              | true :: ch' => symRun p h fuel t ch'
              | false :: ch' => symRun p h fuel f ch'

/-! ## 4. Tests, executions, outcomes -/

/-- An outcome condition (a litmus `exists` clause): hart registers, final memory (`sz` bytes at `a`). -/
inductive OC where
  | tt
  | reg (h r v : Nat)
  | mem (a sz v : Nat)
  | and (p q : OC)
  | or (p q : OC)
  | not (p : OC)
  deriving DecidableEq, Repr, Inhabited

def OC.eval (fr : Nat → Nat → Nat) (fm : Nat → Nat) : OC → Bool
  | .tt => true
  | .reg h r v => fr h r == v % two64
  | .mem a sz v => bytesVal ((List.range sz).map (fun k => fm (a + k))) == v % 2 ^ (8 * sz)
  | .and p q => p.eval fr fm && q.eval fr fm
  | .or p q => p.eval fr fm || q.eval fr fm
  | .not p => !p.eval fr fm

/-- A litmus test. -/
structure Test where
  harts : List (List Instr)
  /-- Per hart: initial (register, value). -/
  regs0 : List (List (Nat × Nat))
  /-- Initial memory, byte-wise; absent bytes are 0. -/
  img : List (Nat × Nat)
  io : List IoRegion := []
  cond : OC

def Test.imgF (T : Test) (x : Nat) : Nat := ((T.img.lookup x)).getD 0

def Test.prog (T : Test) (h : Nat) : List Instr := (T.harts[h]?).getD []

def Test.init (T : Test) (h : Nat) : SSt :=
  { pc := 0
    regs := (List.range 32).map (fun r => (.c ((((T.regs0[h]?).getD []).lookup r).getD 0), []))
    evs := [], ii := 0, ctl := [], conds := [] }

def Test.runH (T : Test) (h : Nat) (ch : List Bool) : Option SSt :=
  symRun (T.prog h) h ((T.prog h).length + 1) (T.init h) ch

def Test.runFrom (T : Test) : Nat → List (List Bool) → Option (List SSt)
  | _, [] => some []
  | h, c :: cs =>
      match T.runH h c, T.runFrom (h + 1) cs with
      | some s, some r => some (s :: r)
      | _, _ => none

/-- All harts along the per-hart choice lists `chs`. -/
def Test.runAll (T : Test) (chs : List (List Bool)) : Option (List SSt) :=
  if chs.length = T.harts.length then T.runFrom 0 chs else none

/-- The concrete event of symbolic event `se` (hart `h`, index `i`) under `ν`. -/
def concEv (ν : Val) (h i : Nat) (se : SEv) : Ev :=
  { sk := se.sk, pa := se.addr.eval ν
    rdat := if se.sk.kind.isLoad then ν (h, i) else []
    wdat := if se.sk.kind.isStore then byteList (se.wval.eval ν) se.sk.sz else [] }

/-- The concrete execution. -/
def conc (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) : Exec :=
  { img := T.imgF, io := T.io, evs := trs.mapIdx (fun h s => s.evs.mapIdx (fun i se => concEv ν h i se))
    gmo := g }

/-- An access instruction (memory operation or failed SC). -/
def Kind.isAcc (k : Kind) : Bool := k.isMem || k == .scFail

/-- The path conditions hold and every access is naturally aligned (front-end scope, header). -/
def condsOk (ν : Val) (trs : List SSt) : Bool :=
  trs.all (fun s =>
    s.conds.all (fun (c, a, b, t) => brEval c (a.eval ν) (b.eval ν) == t) &&
    s.evs.all (fun se => !se.sk.kind.isAcc || (se.addr.eval ν % se.sk.sz == 0)))

/-- Final register `r` of hart `h`. -/
def finalReg (trs : List SSt) (ν : Val) (h r : Nat) : Nat :=
  ((trs[h]?.map (fun s : SSt => (s.rd r).1)).getD (Ex.c 0)).eval ν

/-- **An execution of test `T`**: per-hart paths `chs`, load values `ν`, global memory order `g`. -/
def progExec (T : Test) (chs : List (List Bool)) (ν : Val) (g : List EvId) : Prop :=
  match T.runAll chs with
  | some trs => condsOk ν trs = true ∧ rvwmoRef (conc T trs ν g)
  | none => False

/-- The execution's outcome satisfies the test's condition. -/
def outcome (T : Test) (chs : List (List Bool)) (ν : Val) (g : List EvId) : Prop :=
  match T.runAll chs with
  | some trs => T.cond.eval (finalReg trs ν) (finalByte (conc T trs ν g)) = true
  | none => False

/-- The reference ALLOWS the outcome. -/
def allowedRef (T : Test) : Prop := ∃ chs ν g, progExec T chs ν g ∧ outcome T chs ν g

/-- The reference FORBIDS the outcome. -/
def forbiddenRef (T : Test) : Prop := ∀ chs ν g, progExec T chs ν g → ¬ outcome T chs ν g

end Weak.Prom.Ref
