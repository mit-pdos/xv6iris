/-
Weak/Prom: **a parser for `litmus-tests-riscv` `.litmus` files** into the reference's `Test` (S0-P part (5)).

Format (diy/herd, as in `litmus-tests-riscv` @ `08728edc`): a header `RISCV <name>`, free lines, an init block
`{ … }` (`P:reg=v`, `loc=v`, C-style declarations `uint64_t x=0;`), a program table (`P0 | P1 ;` then one line
per instruction row, cells separated by `|`, rows ended by `;`, labels `LC00:`), and a condition `exists`,
`~exists` or `forall` over `P:reg=v` / `loc=v` atoms with `/\`, `\/`, `not`/`~` and parentheses.  Comments
`(* … *)` are removed.

Locations get fixed addresses (`x 0x1000, y 0x2000, z 0x3000, a 0x4000, b 0x5000, c 0x6000, d 0x7000`; any other
name `0x10000 + 0x1000·k` by first appearance), the scheme `Weak/Prom/RefTests.lean` uses, so a hand-written row
and its parsed repository file can be compared structurally.  A location's width is its declared C type
(`uint64_t`/`int64_t` 8, `uint16_t`/`int16_t` 2, `uint8_t`/`char` 1, otherwise 4): the width of its initial value
and of its final-value atoms.

Not supported (the file is reported out of scope, with the reason): instructions outside `Instr` (e.g. `jalr`),
backward branches, unknown labels.  Everything is done on `List Char` (independent of the `String` API).
-/
import Weak.Prom.RefCheck

namespace Weak.Prom.Ref.Parse

open Weak.Prom.Ref

abbrev Str := List Char

/-! ## Character-list utilities -/

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

def trimL (s : Str) : Str := (s.dropWhile isWs).reverse.dropWhile isWs |>.reverse

def splitOnC (c : Char) : Str → List Str
  | [] => [[]]
  | x :: t => if x == c then [] :: splitOnC c t else
      match splitOnC c t with
      | [] => [[x]]
      | w :: ws => (x :: w) :: ws

def startsWithL (s p : Str) : Bool := s.take p.length == p

/-- Remove `(* … *)` comments. -/
def stripComments : Str → Str
  | '(' :: '*' :: t => skip t
  | c :: t => c :: stripComments t
  | [] => []
where
  skip : Str → Str
    | '*' :: ')' :: t => stripComments t
    | _ :: t => skip t
    | [] => []

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseNatL (base : Nat) (s : Str) : Option Nat :=
  if s.isEmpty then none else
  s.foldl (fun acc c => acc.bind (fun a => (hexVal c).bind (fun d => if d < base then some (a * base + d) else none)))
    (some 0)

/-- A (possibly negative, possibly hex) number, as a 64-bit two's-complement natural. -/
def parseNum (s : Str) : Option Nat :=
  match s with
  | '-' :: t => (parseNum t).map (fun v => (two64 - v % two64) % two64)
  | '0' :: 'x' :: t => parseNatL 16 t
  | '0' :: 'X' :: t => parseNatL 16 t
  | _ => parseNatL 10 s

/-! ## Registers and locations -/

def abiNames : List (String × Nat) :=
  [("zero", 0), ("ra", 1), ("sp", 2), ("gp", 3), ("tp", 4), ("t0", 5), ("t1", 6), ("t2", 7), ("s0", 8), ("fp", 8),
   ("s1", 9), ("a0", 10), ("a1", 11), ("a2", 12), ("a3", 13), ("a4", 14), ("a5", 15), ("a6", 16), ("a7", 17),
   ("s2", 18), ("s3", 19), ("s4", 20), ("s5", 21), ("s6", 22), ("s7", 23), ("s8", 24), ("s9", 25), ("s10", 26),
   ("s11", 27), ("t3", 28), ("t4", 29), ("t5", 30), ("t6", 31)]

def parseReg (s : Str) : Option Nat :=
  match s with
  | 'x' :: t => (parseNatL 10 t).bind (fun n => if n < 32 then some n else none)
  | _ => (abiNames.find? (fun p => p.1.toList == s)).map (·.2)

def fixedLocs : List (Str × Nat) :=
  [(['x'], 0x1000), (['y'], 0x2000), (['z'], 0x3000), (['a'], 0x4000), (['b'], 0x5000), (['c'], 0x6000),
   (['d'], 0x7000)]

/-- Parser state: location table (name, address, width). -/
structure PS where
  locs : List (Str × Nat × Nat) := []
  extra : Nat := 0

def PS.addr (ps : PS) (n : Str) : PS × Nat :=
  match ps.locs.find? (fun l => l.1 == n) with
  | some l => (ps, l.2.1)
  | none =>
    let a := match fixedLocs.find? (fun l => l.1 == n) with
      | some l => l.2
      | none => 0x10000 + 0x1000 * ps.extra
    let extra := if (fixedLocs.find? (fun l => l.1 == n)).isSome then ps.extra else ps.extra + 1
    ({ locs := ps.locs ++ [(n, a, 4)], extra := extra }, a)

def PS.setWidth (ps : PS) (n : Str) (w : Nat) : PS :=
  let (ps, _) := ps.addr n
  { ps with locs := ps.locs.map (fun l => if l.1 == n then (l.1, l.2.1, w) else l) }

def PS.width (ps : PS) (n : Str) : Nat := ((ps.locs.find? (fun l => l.1 == n)).map (·.2.2)).getD 4

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

/-- A value: a number, or a location name (its address). -/
def PS.value (ps : PS) (s : Str) : Option (PS × Nat) :=
  match parseNum s with
  | some v => some (ps, v)
  | none => if s.head?.map isIdentStart == some true then some (ps.addr s) else none

def typeWidth (t : Str) : Option Nat :=
  if t == "uint64_t".toList || t == "int64_t".toList then some 8
  else if t == "uint32_t".toList || t == "int32_t".toList || t == "int".toList then some 4
  else if t == "uint16_t".toList || t == "int16_t".toList || t == "short".toList then some 2
  else if t == "uint8_t".toList || t == "int8_t".toList || t == "char".toList then some 1
  else none

/-! ## The init block -/

structure Init where
  regs : List (Nat × Nat × Nat) := []   -- (hart, register, value)
  mem : List (Nat × Nat × Nat) := []    -- (address, width, value)
  deriving Inhabited

def splitWords (s : Str) : List Str := (splitOnC ' ' s).filter (fun w => !w.isEmpty)

/-- One init item (already trimmed, no `;`). -/
def initItem (ps : PS) (ini : Init) (it : Str) : Except String (PS × Init) :=
  if it.isEmpty then .ok (ps, ini) else
  let ws := splitWords it
  match ws with
  | t :: rest =>
    match typeWidth t with
    | some w =>
      -- a declaration: `T x`, `T x=v`, `T P:reg`
      let body := String.ofList (rest.foldl (fun acc x => acc ++ x) [])
      let parts := splitOnC '=' body.toList
      match parts with
      | [lhs] => if lhs.contains ':' then .ok (ps, ini) else .ok (ps.setWidth lhs w, ini)
      | [lhs, rhs] =>
        if lhs.contains ':' then .ok (ps, ini) else
        let ps := ps.setWidth lhs w
        match ps.value rhs with
        | some (ps, v) => let (ps, a) := ps.addr lhs; .ok (ps, { ini with mem := ini.mem ++ [(a, w, v)] })
        | none => .error s!"bad init value {String.ofList rhs}"
      | _ => .error s!"bad declaration {String.ofList it}"
    | none =>
      let body := it.filter (fun c => !isWs c)
      match splitOnC '=' body with
      | [lhs, rhs] =>
        match splitOnC ':' lhs with
        | [p, reg] =>
          match parseNatL 10 p, parseReg reg, ps.value rhs with
          | some h, some rg, some (ps, v) => .ok (ps, { ini with regs := ini.regs ++ [(h, rg, v)] })
          | _, _, _ => .error s!"bad register init {String.ofList it}"
        | [loc] =>
          match ps.value rhs with
          | some (ps, v) =>
            let w := ps.width loc
            let (ps, a) := ps.addr loc
            .ok (ps, { ini with mem := ini.mem ++ [(a, w, v)] })
          | none => .error s!"bad init {String.ofList it}"
        | _ => .error s!"bad init {String.ofList it}"
      | _ => .error s!"bad init {String.ofList it}"
  | [] => .ok (ps, ini)

/-! ## Instructions -/

/-- An unresolved instruction: branch/jump targets are label names. -/
inductive RInstr where
  | ins (i : Instr)
  | br (c : BrC) (rs1 rs2 : Nat) (l : Str)
  | jmp (l : Str)

def operands (s : Str) : List Str := (splitOnC ',' s).map trimL

/-- `off(reg)` or `(reg)`. -/
def parseMem (s : Str) : Option (Nat × Nat) :=
  match splitOnC '(' s with
  | [off, rest] =>
    let reg := rest.takeWhile (· != ')')
    let o := if (trimL off).isEmpty then some 0 else parseNum (trimL off)
    match o, parseReg (trimL reg) with
    | some o, some r => some (o, r)
    | _, _ => none
  | _ => none

def fenceSet (pred succ : Str) : FenceSet :=
  ⟨pred.contains 'r', pred.contains 'w', pred.contains 'i', pred.contains 'o',
   succ.contains 'r', succ.contains 'w', succ.contains 'i', succ.contains 'o'⟩

def aluOf (m : Str) : Option Alu :=
  if m == "add".toList then some .add else if m == "sub".toList then some .sub
  else if m == "xor".toList then some .xor else if m == "or".toList then some .or
  else if m == "and".toList then some .and else if m == "sll".toList then some .sll
  else if m == "srl".toList then some .srl else if m == "sra".toList then some .sra
  else if m == "slt".toList then some .slt else if m == "sltu".toList then some .sltu
  else if m == "mul".toList then some .mul else none

def aluiOf (m : Str) : Option Alu :=
  if m == "addi".toList then some .add else if m == "xori".toList then some .xor
  else if m == "ori".toList then some .or else if m == "andi".toList then some .and
  else if m == "slli".toList then some .sll else if m == "srli".toList then some .srl
  else if m == "srai".toList then some .sra else if m == "slti".toList then some .slt
  else if m == "sltiu".toList then some .sltu else none

def brOf (m : Str) : Option BrC :=
  if m == "beq".toList then some .eq else if m == "bne".toList then some .ne
  else if m == "blt".toList then some .lt else if m == "bge".toList then some .ge
  else if m == "bltu".toList then some .ltu else if m == "bgeu".toList then some .geu else none

def amoOf (m : Str) : Option AmoOp :=
  if m == "amoswap".toList then some .swap else if m == "amoadd".toList then some .add
  else if m == "amoxor".toList then some .xor else if m == "amoand".toList then some .and
  else if m == "amoor".toList then some .or else if m == "amomin".toList then some .min
  else if m == "amomax".toList then some .max else if m == "amominu".toList then some .minu
  else if m == "amomaxu".toList then some .maxu else none

/-- Load/store widths and signedness by mnemonic. -/
def loadOf (m : Str) : Option (Nat × Bool) :=
  if m == "lb".toList then some (1, true) else if m == "lbu".toList then some (1, false)
  else if m == "lh".toList then some (2, true) else if m == "lhu".toList then some (2, false)
  else if m == "lw".toList then some (4, true) else if m == "lwu".toList then some (4, false)
  else if m == "ld".toList then some (8, true) else none

def storeOf (m : Str) : Option Nat :=
  if m == "sb".toList then some 1 else if m == "sh".toList then some 2
  else if m == "sw".toList then some 4 else if m == "sd".toList then some 8 else none

def widthOf (w : Str) : Option Nat := if w == ['w'] then some 4 else if w == ['d'] then some 8
  else if w == ['h'] then some 2 else if w == ['b'] then some 1 else none

/-- Annotation suffixes `.aq`, `.rl`, `.aqrl`, `.aq.rl`. -/
def annots (sfx : List Str) : Option (Bool × Bool) :=
  sfx.foldl (fun acc x => acc.bind (fun (a, r) =>
    if x == "aq".toList then some (true, r) else if x == "rl".toList then some (a, true)
    else if x == "aqrl".toList then some (true, true) else none)) (some (false, false))

def parseInstr (ps : PS) (s : Str) : Except String (PS × RInstr) :=
  let s := trimL s
  let mnem := s.takeWhile (fun c => !isWs c)
  let ops := operands (trimL (s.drop mnem.length))
  let parts := splitOnC '.' mnem
  let bad : Except String (PS × RInstr) := .error s!"unsupported: {String.ofList s}"
  let regs (l : List Str) : Option (List Nat) := l.mapM parseReg
  match parts with
  | [m] =>
    if m == "nop".toList then .ok (ps, .ins .nop) else
    if m == "fence".toList then
      match ops with
      | [p, q] => .ok (ps, .ins (.fence (fenceSet p q)))
      | _ => bad
    else
    match loadOf m, storeOf m, aluOf m, aluiOf m, brOf m with
    | some (sz, sg), _, _, _, _ =>
      match ops with
      | [rd, mem] => match parseReg rd, parseMem mem with
        | some rd, some (o, r1) => .ok (ps, .ins (.load sz sg rd r1 o))
        | _, _ => bad
      | _ => bad
    | _, some sz, _, _, _ =>
      match ops with
      | [rs2, mem] => match parseReg rs2, parseMem mem with
        | some rs2, some (o, r1) => .ok (ps, .ins (.store sz rs2 r1 o))
        | _, _ => bad
      | _ => bad
    | _, _, some op, _, _ =>
      match regs ops with
      | some [rd, a, b] => .ok (ps, .ins (.alu op rd a b))
      | _ => bad
    | _, _, _, some op, _ =>
      match ops with
      | [rd, a, imm] => match parseReg rd, parseReg a, parseNum imm with
        | some rd, some a, some v => .ok (ps, .ins (.alui op rd a v))
        | _, _, _ => bad
      | _ => bad
    | _, _, _, _, some c =>
      match ops with
      | [a, b, l] => match parseReg a, parseReg b with
        | some a, some b => .ok (ps, .br c a b l)
        | _, _ => bad
      | _ => bad
    | none, none, none, none, none =>
      if m == "li".toList then
        match ops with
        | [rd, v] => match parseReg rd, ps.value v with
          | some rd, some (ps, v) => .ok (ps, .ins (.alui .add rd 0 v))
          | _, _ => bad
        | _ => bad
      else if m == "mv".toList then
        match regs ops with
        | some [rd, a] => .ok (ps, .ins (.alui .add rd a 0))
        | _ => bad
      else if m == "beqz".toList || m == "bnez".toList then
        match ops with
        | [a, l] => match parseReg a with
          | some a => .ok (ps, .br (if m == "beqz".toList then .eq else .ne) a 0 l)
          | none => bad
        | _ => bad
      else if m == "j".toList then
        match ops with
        | [l] => .ok (ps, .jmp l)
        | _ => bad
      else bad
  | [m, sfx] =>
    if m == "fence".toList && sfx == "tso".toList then .ok (ps, .ins .fenceTso) else
    if m == "fence".toList && sfx == ['i'] then .ok (ps, .ins .fencei) else
    match loadOf m, storeOf m with
    | some (sz, _), _ =>
      -- Zalasr load-acquire
      match annots [sfx], ops with
      | some (true, rl), [rd, mem] => match parseReg rd, parseMem mem with
        | some rd, some (0, r1) => .ok (ps, .ins (.loadAq sz rl rd r1))
        | _, _ => bad
      | _, _ => bad
    | _, some sz =>
      match annots [sfx], ops with
      | some (aq, true), [rs2, mem] => match parseReg rs2, parseMem mem with
        | some rs2, some (0, r1) => .ok (ps, .ins (.storeRl sz aq rs2 r1))
        | _, _ => bad
      | _, _ => bad
    | _, _ => atomics m (sfx :: [])
  | m :: rest => atomics m rest
  | [] => bad
where
  atomics (m : Str) (rest : List Str) : Except String (PS × RInstr) :=
    let s' := String.ofList (m ++ ".".toList ++ rest.foldl (fun a b => a ++ b) [])
    match rest with
    | w :: sfx =>
      match widthOf w, annots sfx with
      | some sz, some (aq, rl) =>
        let opsL := operands (trimL ((trimL s).drop (s.takeWhile (fun c => !isWs c)).length))
        if m == "lr".toList then
          match opsL with
          | [rd, mem] => match parseReg rd, parseMem mem with
            | some rd, some (0, r1) => .ok (ps, .ins (.lr sz aq rl rd r1))
            | _, _ => .error s!"unsupported: {s'}"
          | _ => .error s!"unsupported: {s'}"
        else if m == "sc".toList then
          match opsL with
          | [rd, rs2, mem] => match parseReg rd, parseReg rs2, parseMem mem with
            | some rd, some rs2, some (0, r1) => .ok (ps, .ins (.sc sz aq rl rd rs2 r1))
            | _, _, _ => .error s!"unsupported: {s'}"
          | _ => .error s!"unsupported: {s'}"
        else match amoOf m with
          | some op =>
            match opsL with
            | [rd, rs2, mem] => match parseReg rd, parseReg rs2, parseMem mem with
              | some rd, some rs2, some (0, r1) => .ok (ps, .ins (.amo op sz aq rl rd rs2 r1))
              | _, _, _ => .error s!"unsupported: {s'}"
            | _ => .error s!"unsupported: {s'}"
          | none => .error s!"unsupported: {s'}"
      | _, _ => .error s!"unsupported: {s'}"
    | [] => .error s!"unsupported: {s'}"

/-! ## The program table -/

/-- One cell: optional labels `L:` then an optional instruction. -/
def parseCell (ps : PS) (c : Str) : Except String (PS × List Str × Option RInstr) :=
  let c := trimL c
  if c.isEmpty then .ok (ps, [], none) else
  match splitOnC ':' c with
  | [lab, rest] =>
    if (trimL lab).all (fun ch => ch.isAlphanum || ch == '_') && !(trimL lab).isEmpty then
      if (trimL rest).isEmpty then .ok (ps, [trimL lab], none) else
      match parseInstr ps rest with
      | .ok (ps, i) => .ok (ps, [trimL lab], some i)
      | .error e => .error e
    else .error s!"bad cell {String.ofList c}"
  | [_] => match parseInstr ps c with
    | .ok (ps, i) => .ok (ps, [], some i)
    | .error e => .error e
  | _ => .error s!"bad cell {String.ofList c}"

/-- Resolve labels to absolute forward targets. -/
def resolve (cells : List (List Str × Option RInstr)) : Except String (List Instr) :=
  -- label -> index of the next instruction
  let step := fun (acc : Nat × List (Str × Nat) × List (Nat × RInstr)) (cl : List Str × Option RInstr) =>
    let (n, labs, ins) := acc
    let labs := labs ++ cl.1.map (fun l => (l, n))
    match cl.2 with
    | some i => (n + 1, labs, ins ++ [(n, i)])
    | none => (n, labs, ins)
  let (_, labs, ins) := cells.foldl step (0, [], [])
  ins.mapM (fun (k, i) =>
    match i with
    | .ins i => .ok i
    | .br c a b l => match labs.find? (·.1 == l) with
      | some (_, t) => if t > k then .ok (.br c a b t) else .error "backward branch"
      | none => .error s!"unknown label {String.ofList l}"
    | .jmp l => match labs.find? (·.1 == l) with
      | some (_, t) => if t > k then .ok (.jmp t) else .error "backward jump"
      | none => .error s!"unknown label {String.ofList l}")

/-! ## Conditions -/

inductive Tok where
  | lp | rp | andT | orT | notT | eq
  | word (s : Str)
  deriving BEq, Inhabited

def tokenizeF : Nat → Str → List Tok
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, '(' :: t => .lp :: tokenizeF n t
  | n + 1, ')' :: t => .rp :: tokenizeF n t
  | n + 1, '/' :: '\\' :: t => .andT :: tokenizeF n t
  | n + 1, '\\' :: '/' :: t => .orT :: tokenizeF n t
  | n + 1, '~' :: t => .notT :: tokenizeF n t
  | n + 1, '=' :: t => .eq :: tokenizeF n t
  | n + 1, c :: t =>
    if isWs c || c == '\n' then tokenizeF n t else
    let w := (c :: t).takeWhile (fun ch => !(isWs ch || ch == '\n' || ch == '(' || ch == ')' || ch == '=' ||
      ch == '/' || ch == '\\' || ch == '~'))
    if w.isEmpty then tokenizeF n t else
    let rest := (c :: t).drop w.length
    (if w == "not".toList then Tok.notT else Tok.word w) :: tokenizeF n rest

def tokenize (s : Str) : List Tok := tokenizeF (s.length + 1) s

/-- Parse a condition (fuel-bounded recursive descent; `/\` binds tighter than `\/`, both right-associative). -/
def parseOr (ps : PS) : Nat → List Tok → Option (OC × List Tok)
  | 0, _ => none
  | n + 1, ts =>
    match parseAnd ps n ts with
    | some (a, .orT :: rest) => (parseOr ps n rest).map (fun (b, r) => (.or a b, r))
    | r => r
where
  parseAnd (ps : PS) : Nat → List Tok → Option (OC × List Tok)
    | 0, _ => none
    | n + 1, ts =>
      match parseAtom ps n ts with
      | some (a, .andT :: rest) => (parseAnd ps n rest).map (fun (b, r) => (.and a b, r))
      | r => r
  parseAtom (ps : PS) : Nat → List Tok → Option (OC × List Tok)
    | 0, _ => none
    | n + 1, ts =>
      match ts with
      | .notT :: rest => (parseAtom ps n rest).map (fun (a, r) => (.not a, r))
      | .lp :: rest =>
        match parseOr ps n rest with
        | some (a, .rp :: r) => some (a, r)
        | _ => none
      | .word w :: rest =>
        if w == "true".toList then some (.tt, rest) else
        if w == "false".toList then some (.not .tt, rest) else
        match rest with
        | .eq :: .word v :: r =>
          match splitOnC ':' w with
          | [p, reg] =>
            match parseNatL 10 p, parseReg reg, ps.value v with
            | some h, some rg, some (_, vv) => some (.reg h rg vv, r)
            | _, _, _ => none
          | [loc] =>
            match ps.value v with
            | some (_, vv) =>
              let (_, a) := ps.addr loc
              some (.mem a (ps.width loc) vv, r)
            | none => none
          | _ => none
        | _ => none
      | _ => none

/-! ## The whole file -/

/-- A parsed test: its name, the quantifier (`exists` / `~exists` / `forall`), the condition's body, the test. -/
structure LTest where
  name : String
  quant : String
  test : Test

def lines (s : Str) : List Str := splitOnC '\n' s

def parseLitmus (src : String) : Except String LTest := do
  let s := stripComments src.toList
  let ls := (lines s).map trimL
  let hdr := (ls.find? (fun l => !l.isEmpty)).getD []
  let name ← match splitWords hdr with
    | [arch, n] => if arch == "RISCV".toList then pure (String.ofList n) else throw "not RISCV"
    | _ => throw "bad header"
  -- init block
  let body := s.dropWhile (· != '{')
  if body.isEmpty then throw "no init block"
  let initTxt := (body.drop 1).takeWhile (· != '}')
  let after := (body.drop 1).dropWhile (· != '}') |>.drop 1
  let items := (splitOnC ';' (initTxt.map (fun c => if c == '\n' then ';' else c))).map trimL
  let (ps, ini) ← items.foldlM (fun (acc : PS × Init) it => initItem acc.1 acc.2 it) ({}, {})
  -- program table and condition
  let als := (lines after).map trimL
  let isQ := fun (l : Str) => startsWithL l "exists".toList || startsWithL l "~exists".toList ||
    startsWithL l "forall".toList
  let progL := (als.takeWhile (fun l => !isQ l)).filter (fun l => !l.isEmpty && !startsWithL l "locations".toList)
  let condL := als.dropWhile (fun l => !isQ l)
  let condTxt := condL.foldl (fun a l => a ++ [' '] ++ l) []
  let condTxt := trimL condTxt
  let (quant, condBody) :=
    if startsWithL condTxt "~exists".toList then ("~exists", condTxt.drop 7)
    else if startsWithL condTxt "exists".toList then ("exists", condTxt.drop 6)
    else ("forall", condTxt.drop 6)
  let rows := progL.map (fun l => (splitOnC '|' (l.filter (· != ';'))).map trimL)
  let nthreads := match rows.head? with | some h => h.length | none => 0
  if nthreads == 0 then throw "no program"
  let instRows := rows.drop 1
  let (ps, cells) ← instRows.foldlM (fun (acc : PS × List (List (List Str × Option RInstr))) row => do
      let (ps, cs) := acc
      let mut ps := ps
      let mut out : List (List Str × Option RInstr) := []
      for c in row do
        let (ps', labs, i) ← parseCell ps c
        ps := ps'
        out := out ++ [(labs, i)]
      pure (ps, cs ++ [out])) (ps, [])
  let harts ← (List.range nthreads).mapM (fun t => resolve (cells.map (fun row => (row[t]?).getD ([], none))))
  let cond ← match parseOr ps 1000 (tokenize condBody) with
    | some (c, []) => pure c
    | _ => throw s!"bad condition {String.ofList condBody}"
  let regs0 := (List.range nthreads).map (fun h => (ini.regs.filter (·.1 == h)).map (fun x => (x.2.1, x.2.2)))
  let img := ini.mem.foldl (fun acc (a, w, v) => acc ++ (byteList v w).mapIdx (fun k b => (a + k, b))) []
  pure { name := name, quant := quant, test := ⟨harts, regs0, img, [], cond⟩ }

end Weak.Prom.Ref.Parse
