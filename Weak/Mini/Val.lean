/-
Weak/Mini: **values of the fragment F** — the ALU operations, the branch conditions and their ONE evaluator
(mini plan rev 4 §2; P1 gate fix 2: a single copy, used by the reference `Ref.lean` and the machine `Mach.lean`).

Transliterated from the full reference's RefProg.lean:57–122 (`Alu`, `BrC`, `two64`, `sltN`, `aluOp`, `brEval`,
`sext`); `Weak/Mini/EqRefSim.lean` and `Weak/Mini/EqMachFront.lean` prove them equal (`rfl` per case).
Imports: only Lean core (plan §2 import discipline).
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

/-- `2^64` (RefProg.lean:72). -/
def two64 : Nat := 18446744073709551616

/-- Signed less-than on `n`-bit values: flip the sign bit, compare unsigned (RefProg.lean:75). -/
def sltN (n a b : Nat) : Bool := decide ((a ^^^ 2 ^ (n - 1)) < (b ^^^ 2 ^ (n - 1)))

/-- RV64 integer ALU operations on 64-bit values (RefProg.lean:77–89). -/
def MAlu.eval : MAlu → Nat → Nat → Nat
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

/-- Branch conditions on 64-bit values (RefProg.lean:91–97). -/
def MBrC.eval : MBrC → Nat → Nat → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => sltN 64 a b
  | .ge, a, b => !sltN 64 a b
  | .ltu, a, b => decide (a < b)
  | .geu, a, b => !decide (a < b)

/-- Sign extension of an `sz`-byte value to 64 bits (RefProg.lean:121). -/
def sext (sz v : Nat) : Nat :=
  if sz < 8 ∧ 2 ^ (8 * sz - 1) ≤ v then v + (two64 - 2 ^ (8 * sz)) else v

end Weak.Mini
