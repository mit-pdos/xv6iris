/-
Weak/Mini: **the fragment F's programs** (mini plan rev 4 §1, §2 "Shared first files"; owner ruling [OWN.P18]).

The minimal stack's program syntax, with NO import of the full development (plan §2 import discipline: only
`Weak/Mini/Eq*.lean` import `Weak.Prom.*`).  The fragment: register/immediate ALU operations, aligned loads and stores
of ONE size per program, fences with any predecessor/successor set, branches (any condition, any target, so loops),
`jal x0` jumps, `nop`.  Not in F: AMOs, LR/SC, `.aq`/`.rl`, `fence.tso`, `fence.i`, CMOs, CSRs, I/O, misaligned or
mixed-size accesses.

Registers are numbered `0 … 31`; `x0` reads as 0 and ignores writes (the semantics' business, not the syntax's).
Values are natural numbers below `2^64`.  The access size `sz` (bytes: 1, 2, 4 or 8) is a property of the PROGRAM:
every load and store of it has that size (NA-6, single-size).  The image is WORD-valued: `(address, value)` pairs, one
per `sz`-aligned word; absent words are 0.
No `sorry`, no axiom, no `native_decide`.
-/

namespace Weak.Mini

/-- ALU operations (the full reference's `Ref.Alu`, RefProg.lean:57). -/
inductive MAlu where
  | add | sub | xor | or | and | sll | srl | sra | slt | sltu | mul
  deriving DecidableEq, Repr, Inhabited

/-- Branch conditions (`Ref.BrC`, RefProg.lean:62). -/
inductive MBrC where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr, Inhabited

/-- A FENCE's predecessor and successor sets (rvwmo.adoc: `fence pred, succ`; the full reference's `FenceSet`,
Ref.lean:69, has the same eight bits: device input/output and memory read/write, for each side). -/
structure MFence where
  pr : Bool
  pw : Bool
  pi : Bool
  po : Bool
  sr : Bool
  sw : Bool
  si : Bool
  so : Bool
  deriving DecidableEq, Repr, Inhabited

/-- An instruction of the fragment F.  Branch and jump targets are instruction indices. -/
inductive MI where
  /-- `op rd, rs1, imm` (`addi`, `xori`, `ori`, `andi`, …; `li rd, v` is `addi rd, x0, v`). -/
  | alui (op : MAlu) (rd rs1 imm : Nat)
  /-- `op rd, rs1, rs2`. -/
  | alu (op : MAlu) (rd rs1 rs2 : Nat)
  /-- `l{w,d}`-style load `rd, off(rs1)` of the program's size; `sgn` = sign-extending. -/
  | load (sgn : Bool) (rd rs1 off : Nat)
  /-- `s{w,d}`-style store `rs2, off(rs1)` of the program's size. -/
  | store (rs2 rs1 off : Nat)
  /-- `fence pred, succ`. -/
  | fence (f : MFence)
  /-- `b<c> rs1, rs2, tgt`: to `tgt` if the condition holds, else the next instruction. -/
  | br (c : MBrC) (rs1 rs2 tgt : Nat)
  /-- `jal x0, tgt`. -/
  | jmp (tgt : Nat)
  | nop
  deriving DecidableEq, Repr, Inhabited

/-- A program of the fragment: the harts' texts, their initial registers, the WORD-valued image, the access size. -/
structure MProg where
  harts : List (List MI)
  /-- Per hart: initial `(register, value)` pairs; absent registers are 0. -/
  regs0 : List (List (Nat × Nat))
  /-- Initial memory, one value per `sz`-aligned word: `(address, value)`; absent words are 0. -/
  img : List (Nat × Nat)
  /-- The access size in bytes (every load and store). -/
  sz : Nat
  deriving Repr, Inhabited

/-- Hart `h`'s text (empty outside the harts). -/
def MProg.prog (P : MProg) (h : Nat) : List MI := (P.harts[h]?).getD []

/-- Hart `h`'s initial value of register `r`. -/
def MProg.reg0 (P : MProg) (h r : Nat) : Nat := (((P.regs0[h]?).getD []).lookup r).getD 0

/-- The initial value of the word at `a`. -/
def MProg.img0 (P : MProg) (a : Nat) : Nat := (P.img.lookup a).getD 0

end Weak.Mini
