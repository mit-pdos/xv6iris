/-
Weak/Mini: **MiniMach — the Promising-RISC-V machine for the fragment F** (mini plan rev 4 §2 L2; owner ruling
[OWN.P18]: "I still want the semantics and the logic. Just want them minimial").

The machine v2 of `Weak/Prom/Machine.lean` (Pulte et al. PLDI'19 promising semantics, uncertified), cut down to F
(Prog.lean: ALU ops, aligned single-size loads/stores, fences, branches and jumps with ANY target, `nop`) and made
WORD-valued: every load and store of a program accesses one aligned `sz`-byte word, so a message is one word
`(pa, value, tid)` and the per-byte banks of machine v2 become per-word TOTAL FUNCTIONS.  The front end LOOPS: it
reads the hart's `MI` text at `pc` directly (branches and jumps may go backwards), as the full loop front end
`xNext` (OwnAFront.lean:59) does.  Equality with machine v2 on F (E2a/E2b) is `Weak/Mini/EqMach.lean`.

Marks (Machine.lean header): FAITHFUL = same behaviours as machine v2 on F; STRONGER/WEAKER = fewer/more.  Every arm
below cites the Machine.lean arm it mirrors.  What machine v2 has and F never uses is DROPPED (proved inert along
every run of an F program: `RelWs`, EqMachMem.lean): the release view `wVRel`, the LR reservation `wRes`, the AMO slot
`wRmw`, the fetch views `wIfl`/`wIfr`/`wIfv`, message classes other than `plain`, the invalidate clause of the
load-value rule (`invalRead`, needs a CMO message), and the labels `LRmw/LAmoLd/LAmoSt/LExLoad/LExStore/LExFail/
LFenceI/LIFetch/LCmo/LDev/LSilent`.
Imports: only `Weak.Mini.Prog` and Lean core (plan §2 import discipline).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Prog

namespace Weak.Mini.Mach

open Weak.Mini

/-! ## 0. Values (transliterated from RefProg.lean:72–122) -/

/-- `2^64` (RefProg.lean:72). -/
def two64 : Nat := 18446744073709551616

/-- Signed less-than on `n`-bit values (RefProg.lean:75). -/
def sltN (n a b : Nat) : Bool := decide ((a ^^^ 2 ^ (n - 1)) < (b ^^^ 2 ^ (n - 1)))

/-- The ALU (RefProg.lean:77–89). -/
def aluOp : MAlu → Nat → Nat → Nat
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

/-- Branch conditions (RefProg.lean:91–97). -/
def brEval : MBrC → Nat → Nat → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => sltN 64 a b
  | .ge, a, b => !sltN 64 a b
  | .ltu, a, b => decide (a < b)
  | .geu, a, b => !decide (a < b)

/-- Sign extension of an `sz`-byte value to 64 bits (RefProg.lean:121). -/
def sext (sz v : Nat) : Nat :=
  if sz < 8 ∧ 2 ^ (8 * sz - 1) ≤ v then v + (two64 - 2 ^ (8 * sz)) else v

/-- `2^(8·sz)`: the values of an `sz`-byte word are `< wordW P`. -/
def wordW (P : MProg) : Nat := 2 ^ (8 * P.sz)

/-- WELL-FORMED PROGRAM (Prog.lean: "one value per `sz`-aligned word"): a positive access size and an image whose
entries are at aligned addresses.  E2 is stated for these programs. -/
def progWf (P : MProg) : Prop := 0 < P.sz ∧ ∀ p ∈ P.img, p.1 % P.sz = 0

/-! ## 1. Labels and messages -/

/-- A dependency source (Machine.lean `Dsrc`: a register, or the current instruction's load result). -/
inductive MSrc where
  | reg (r : Nat)
  | ldres
  deriving DecidableEq, Repr

/-- THE LABELS (exactly what `instrNext`/`xNext` emit on F, MachCert.lean:53–142, OwnAFront.lean:59–71).
Values are WORDS: a load answers ONE timestamp `t` and the word `v` (machine v2: one `(t, byte)` per byte, all with the
same `t` — `untorn`, EqMach.lean); a store writes the word `v`. -/
inductive MLab where
  /-- `LLoad false false a tvs asrc` (Machine.lean:517). -/
  | load (a t v : Nat) (asrc : List MSrc)
  /-- `LStore false false a data asrc vsrc` (Machine.lean:520). -/
  | store (a v : Nat) (asrc vsrc : List MSrc)
  /-- `LFence pr pw sr sw` (Machine.lean:529). -/
  | fence (pr pw sr sw : Bool)
  /-- `LRegW rd srcs` (Machine.lean:535). -/
  | regW (rd : Nat) (srcs : List MSrc)
  /-- `LCtrl srcs` (Machine.lean:537). -/
  | ctrl (srcs : List MSrc)
  /-- `LInstr` (Machine.lean:539). -/
  | instr
  deriving DecidableEq, Repr

/-- A message: the word `v` written at `pa` by hart `tid` (Machine.lean `PMsg`, class `plain`). -/
structure MMsg where
  pa : Nat
  v : Nat
  tid : Nat
  deriving DecidableEq, Repr

/-- The word at `a` at timestamp `t` (Machine.lean `memByte`, :85): the image at `0`, message `t` if it is at `a`.
FAITHFUL on F (aligned same-size messages overlap a word iff they are at its address). -/
def memv (P : MProg) (log : List MMsg) : Nat → Nat → Option Nat
  | 0, a => some (P.img0 a % wordW P)
  | t + 1, a =>
    match log[t]? with
    | some m => if m.pa = a then some m.v else none
    | none => none

/-- `writesIn log a lo hi`: some timestamp in `(lo, hi]` writes the word `a` (Machine.lean:91). FAITHFUL on F. -/
def writesIn (log : List MMsg) (a lo hi : Nat) : Prop :=
  ∃ t : Nat, lo < t ∧ t ≤ hi ∧ ∃ m, log[t - 1]? = some m ∧ m.pa = a

/-! ## 2. The hart's memory state -/

/-- THE HART STATE (Machine.lean `PState`, :206, restricted to the fields F moves): `coh` the per-word coherence
floor, `vrOld`/`vwOld` max post-view of past loads/stores, `vrNew`/`vwNew` the fence floors, `fwd` the forward
bank (per word: the hart's latest own store's timestamp and forward view), `regv` the register views, `vcap` the
control/address-capture view, `ldv` the current instruction's load-result view. -/
structure MSt where
  coh : Nat → Nat
  vrOld : Nat
  vwOld : Nat
  vrNew : Nat
  vwNew : Nat
  fwd : Nat → Option (Nat × Nat)
  regv : Nat → Nat
  vcap : Nat
  ldv : Nat

/-- The initial state (Machine.lean `psInit`, :224): every view `0`, empty forward bank. -/
def msInit : MSt := ⟨fun _ => 0, 0, 0, 0, 0, fun _ => none, fun _ => 0, 0, 0⟩

/-- The view of a source (Machine.lean `dsrcView`, :248). -/
def srcView (ws : MSt) : MSrc → Nat
  | .reg r => ws.regv r
  | .ldres => ws.ldv

/-- The view of a source list (Machine.lean `srcsView`, :253). -/
def srcsView (ws : MSt) (srcs : List MSrc) : Nat := srcs.foldr (fun s v => max (srcView ws s) v) 0

/-- THE LOAD PRE-VIEW (Machine.lean `ldPre`, :270, with `aq = rl = false` and the fetch view `wIfv = 0`): the
address view `va` (rule 9) and the load floor `vrNew` (rule 4).  FAITHFUL. -/
def ldPre (ws : MSt) (va : Nat) : Nat := max va ws.vrNew

/-- THE STORE PRE-VIEW (Machine.lean `stPre`/`stPreA`, :277–289, `aq = rl = false`, `wIfv = 0`): address and data
views (rules 9, 10), the capture view (rules 11, 13), the store floor `vwNew` (rule 4).  FAITHFUL. -/
def stPre (ws : MSt) (va vd : Nat) : Nat := max va (max vd (max ws.vcap ws.vwNew))

/-- Is the answer `t` at word `a` the hart's own latest store (Machine.lean `fwdHit`, :294)? -/
def fwdHit (ws : MSt) (a t : Nat) : Bool :=
  match ws.fwd a with
  | some (tf, _) => t == tf
  | none => false

/-- The forwarded view of an answer (Machine.lean `fwdView`, :308): the store's forward view if forwarded (rule 12),
else the timestamp. -/
def fwdView (ws : MSt) (a t : Nat) : Nat :=
  match ws.fwd a with
  | some (tf, vf) => if t = tf then vf else t
  | none => t

/-- THE READ ADMISSIBILITY of a word load at pre-view `vpre` (Machine.lean `loadOk`, :325–333, word form): the word
the answer `t` holds is `v`, and no write to the word lies in `(t, floor]`, where the floor is `vpre ⊔ coh` for an
answer FORWARDED from the hart's own latest store (the forwarding exemption, word form), and the common read point
`vpre ⊔ t` raised by `coh` otherwise (M9; for one word `nonFwdMax = t`).  [Both floors give the same window, since
`(t, t]` is empty; the form mirrors Machine.lean.]  The invalidate disjunct `invalRead` is dropped (no CMO on F).
FAITHFUL on untorn reads (E2; a TORN read — bytes from different stores — has no word form: plan §2 L2 F3). -/
def loadOk (P : MProg) (log : List MMsg) (ws : MSt) (vpre a t v : Nat) : Prop :=
  memv P log t a = some v ∧
    ¬ writesIn log a t (max (if fwdHit ws a t then vpre else max vpre t) (ws.coh a))

/-- THE LOAD POST (Machine.lean `loadRunV … 0` = `loadRun` (`loadRunV_zero`, MachInval.lean), :363, `aq = rl =
false`): coherence takes `max vpost t`, `vrOld` and the load-result view take the post-view `vpost = vpre ⊔
fwdView` (rule 12), `vcap ⊔= va` (rule 13).  FAITHFUL. -/
def loadPost (ws : MSt) (va vpre a t : Nat) : MSt :=
  let vp := max vpre (fwdView ws a t)
  { ws with
    coh := fun b => if b = a then max (ws.coh a) (max vp t) else ws.coh b
    vrOld := max ws.vrOld vp
    ldv := max ws.ldv vp
    vcap := max va ws.vcap }

/-- THE STORE POST (Machine.lean `storeRun`, :417, `rl = false`, and `acqPost … false`, :448): coherence takes `ts`,
the forward bank records `(ts, fv)` (rule 12: `fv` = address ⊔ data view), `vwOld ⊔= ts`, `vcap ⊔= va`.  FAITHFUL. -/
def storePost (ws : MSt) (va fv a ts : Nat) : MSt :=
  { ws with
    coh := fun b => if b = a then max (ws.coh a) ts else ws.coh b
    fwd := fun b => if b = a then some (ts, fv) else ws.fwd b
    vwOld := max ws.vwOld ts
    vcap := max va ws.vcap }

/-- FENCE pred,succ (Machine.lean `fencePost`, :460; rule 4).  FAITHFUL. -/
def fencePost (ws : MSt) (pr pw sr sw : Bool) : MSt :=
  let v := max (if pr then ws.vrOld else 0) (if pw then ws.vwOld else 0)
  { ws with
    vrNew := if sr then max ws.vrNew v else ws.vrNew
    vwNew := if sw then max ws.vwNew v else ws.vwNew }

/-! ## 3. The memory half of a state step -/

/-- `mMem P log i prom ws l ots ws' prom'` (Machine.lean `memStep`, :562): hart `i` with promises `prom` and state
`ws` performs `l`, fulfilling `ots` (`some ts` for a store).  One constructor per arm. -/
inductive mMem (P : MProg) (log : List MMsg) (i : Nat) : List Nat → MSt → MLab → Option Nat → MSt → List Nat → Prop
  /-- Machine.lean `memStep.load` (:568) with `vi = 0` (`invalCite` forces it without CMO messages).  FAITHFUL. -/
  | load (prom : List Nat) (ws : MSt) (a t v : Nat) (asrc : List MSrc) :
      loadOk P log ws (ldPre ws (srcsView ws asrc)) a t v →
      mMem P log i prom ws (.load a t v asrc) none
        (loadPost ws (srcsView ws asrc) (ldPre ws (srcsView ws asrc)) a t) prom
  /-- Machine.lean `memStep.store` (:575): fulfils its promise `ts` (the message is this word by this hart), COH
  (`coh a < ts`, `cohBelow` on one word), EXT (pre-view `< ts`).  FAITHFUL. -/
  | store (prom : List Nat) (ws : MSt) (a v : Nat) (asrc vsrc : List MSrc) (ts : Nat) :
      ts ∈ prom →
      log[ts - 1]? = some ⟨a, v, i⟩ →
      ws.coh a < ts →
      stPre ws (srcsView ws asrc) (srcsView ws vsrc) < ts →
      mMem P log i prom ws (.store a v asrc vsrc) (some ts)
        (storePost ws (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) a ts)
        (prom.filter (fun t => t != ts))
  /-- Machine.lean `memStep.fence` (:629).  FAITHFUL. -/
  | fence (prom : List Nat) (ws : MSt) (pr pw sr sw : Bool) :
      mMem P log i prom ws (.fence pr pw sr sw) none (fencePost ws pr pw sr sw) prom
  /-- Machine.lean `memStep.regW` (:639): the register's view is the sources' view.  FAITHFUL. -/
  | regW (prom : List Nat) (ws : MSt) (rd : Nat) (srcs : List MSrc) :
      mMem P log i prom ws (.regW rd srcs) none
        { ws with regv := fun r => if r = rd then srcsView ws srcs else ws.regv r } prom
  /-- Machine.lean `memStep.ctrl` (:642): `vcap ⊔= view(srcs)` (rule 11).  FAITHFUL. -/
  | ctrl (prom : List Nat) (ws : MSt) (srcs : List MSrc) :
      mMem P log i prom ws (.ctrl srcs) none { ws with vcap := max (srcsView ws srcs) ws.vcap } prom
  /-- Machine.lean `memStep.instr` (:645): resets the load-result view.  FAITHFUL. -/
  | instr (prom : List Nat) (ws : MSt) :
      mMem P log i prom ws .instr none { ws with ldv := 0 } prom

/-! ## 4. The front end (loops allowed) -/

/-- A hart's program state (MachCert.lean `LP`, :35): pc, registers, the labels its instruction still emits. -/
structure MFront where
  pc : Nat
  regs : List Nat
  q : List MLab

/-- Register read (`x0` is 0; MachCert.lean `LP.rd`, :41). -/
def MFront.rd (f : MFront) (r : Nat) : Nat := if r = 0 then 0 else (f.regs[r]?).getD 0

/-- Register write (`x0` ignores writes; values mod 2^64; MachCert.lean `LP.wr`, :43). -/
def MFront.wr (f : MFront) (r v : Nat) : List Nat := if r = 0 then f.regs else f.regs.set r (v % two64)

/-- A register as a source (MachLitmus.lean `srcR`, :108). -/
def srcR (r : Nat) : List MSrc := if r = 0 then [] else [.reg r]

/-- The register-write label (MachLitmus.lean `regWL`, :111). -/
def regWL (rd : Nat) (srcs : List MSrc) : List MLab := if rd = 0 then [] else [.regW rd srcs]

/-- Emit the first of `labs`, queue the rest (MachCert.lean `go1`, :46). -/
def go1 (f : MFront) (regs' : List Nat) (pc' : Nat) (labs : List MLab) (l : MLab) : Option MFront :=
  match labs with
  | l0 :: rest => if l = l0 then some ⟨pc', regs', rest⟩ else none
  | [] => none

/-- THE FIRST LABEL OF AN F INSTRUCTION in a text of length `n` (MachCert.lean `instrNext`, :53, its F arms; the
branch/jump arms are `xNext`'s, OwnAFront.lean:66–70: ANY target `≤ n`).  A load accepts any answer `(t, v)` with
`v` an `sz`-byte word (machine v2: `tvs.length = sz`); the memory half decides admissibility.  FAITHFUL. -/
def instrNext (P : MProg) (n : Nat) (f : MFront) : MI → MLab → Option MFront
  | .alui op rd rs1 imm, l =>
      go1 f (f.wr rd (aluOp op (f.rd rs1) imm)) (f.pc + 1) (regWL rd (srcR rs1) ++ [.instr]) l
  | .alu op rd rs1 rs2, l =>
      go1 f (f.wr rd (aluOp op (f.rd rs1) (f.rd rs2))) (f.pc + 1) (regWL rd (srcR rs1 ++ srcR rs2) ++ [.instr]) l
  | .load sgn rd rs1 off, l =>
      let a := (f.rd rs1 + off) % two64
      if a % P.sz ≠ 0 then none else
      match l with
      | .load b t v asrc =>
          if b = a ∧ v < wordW P ∧ asrc = srcR rs1 then
            some ⟨f.pc + 1, f.wr rd (if sgn then sext P.sz v else v), regWL rd [.ldres] ++ [.instr]⟩
          else none
      | _ => none
  | .store rs2 rs1 off, l =>
      let a := (f.rd rs1 + off) % two64
      if a % P.sz ≠ 0 then none else
      match l with
      | .store b v asrc vsrc =>
          if b = a ∧ v = f.rd rs2 % wordW P ∧ asrc = srcR rs1 ∧ vsrc = srcR rs2 then
            some ⟨f.pc + 1, f.regs, [.instr]⟩
          else none
      | _ => none
  | .fence fs, l => go1 f f.regs (f.pc + 1) [.fence fs.pr fs.pw fs.sr fs.sw, .instr] l
  | .br c rs1 rs2 tgt, l =>
      if n < tgt then none else
      go1 f f.regs (if brEval c (f.rd rs1) (f.rd rs2) then tgt else f.pc + 1) [.ctrl (srcR rs1 ++ srcR rs2), .instr] l
  | .jmp tgt, l => if n < tgt then none else go1 f f.regs tgt [.instr] l
  | .nop, l => go1 f f.regs (f.pc + 1) [.instr] l

/-- ONE LABEL of hart `i` (MachCert.lean `litNext`, :145, and OwnAFront.lean `xNext`, :59): the next queued label,
or the first label of the instruction at `pc` of the hart's text. -/
def mNext (P : MProg) (i : Nat) (f : MFront) (l : MLab) : Option MFront :=
  match f.q with
  | l0 :: rest => if l = l0 then some { f with q := rest } else none
  | [] =>
    match (P.prog i)[f.pc]? with
    | some ins => instrNext P (P.prog i).length f ins l
    | none => none

/-! ## 5. Configurations, steps, valid runs -/

/-- A hart: program state, memory state, promise set (Machine.lean `PAgent`, :712; promises as a list). -/
structure MHart where
  fr : MFront
  ws : MSt
  prom : List Nat

/-- A configuration: the message log (timestamp `k + 1` is entry `k`) and the harts (Machine.lean `PCfg`, :719). -/
structure MCfg where
  log : List MMsg
  hs : List MHart

/-- An event: a promise, or a state step with its label and fulfil timestamp (Machine.lean `PEvt`, :727). -/
inductive MEvt where
  | prom (i : Nat) (m : MMsg)
  | st (i : Nat) (l : MLab) (ts : Option Nat)

/-- ONE MACHINE STEP (Machine.lean `pmStep`, :740).  `promise`: the promising hart appends a message of its own; it
is an aligned word write (machine v2 allows any byte run, but only these can ever be fulfilled on F: on valid runs
FAITHFUL, E2).  `state`: front end and memory half together. -/
inductive mStep (P : MProg) : MCfg → MEvt → MCfg → Prop
  | promise (c : MCfg) (i : Nat) (h : MHart) (m : MMsg) :
      c.hs[i]? = some h → m.tid = i → m.pa % P.sz = 0 → m.v < wordW P →
      mStep P c (.prom i m) ⟨c.log ++ [m], c.hs.set i { h with prom := (c.log.length + 1) :: h.prom }⟩
  | state (c : MCfg) (i : Nat) (h : MHart) (l : MLab) (ots : Option Nat) (fr' : MFront) (ws' : MSt)
      (prom' : List Nat) :
      c.hs[i]? = some h →
      mNext P i h.fr l = some fr' →
      mMem P c.log i h.prom h.ws l ots ws' prom' →
      mStep P c (.st i l ots) ⟨c.log, c.hs.set i ⟨fr', ws', prom'⟩⟩

/-- Runs (Machine.lean `pmSteps`, :756). -/
inductive mSteps (P : MProg) : MCfg → List MEvt → MCfg → Prop
  | refl (c : MCfg) : mSteps P c [] c
  | step (c0 c1 c2 : MCfg) (e : MEvt) (es : List MEvt) :
      mStep P c0 e c1 → mSteps P c1 es c2 → mSteps P c0 (e :: es) c2

/-- The initial configuration (Machine.lean `pmInit`, :762, with MachCert.lean `progs`, :157): hart `i` at pc 0 with
its 32 initial registers. -/
def mInit (P : MProg) : MCfg :=
  ⟨[], (List.range P.harts.length).map (fun i =>
    ⟨⟨0, (List.range 32).map (fun r => P.reg0 i r % two64), []⟩, msInit, []⟩)⟩

/-- No outstanding promise (Machine.lean `noPromises`, :766). -/
def noProm (c : MCfg) : Prop := ∀ (i : Nat) (h : MHart), c.hs[i]? = some h → h.prom = []

/-- A run: its event list (the final configuration is the one the events reach; `mStep` is deterministic). -/
structure MRun where
  evs : List MEvt

/-- A VALID RUN with final memory `Mm` (Machine.lean `validRun`, :771; CoreDefs.lean `PF.validRun`, :85): a finite
run from the initial configuration ending with no outstanding promise. -/
def miniValidRun (P : MProg) (Mm : List MMsg) (r : MRun) : Prop :=
  ∃ c, mSteps P (mInit P) r.evs c ∧ noProm c ∧ c.log = Mm

/-- The trace of hart `h`: its state events' labels and fulfil timestamps (Machine.lean `traceOf`, :781). -/
def traceOf (h : Nat) : List MEvt → List (MLab × Option Nat)
  | [] => []
  | .prom _ _ :: es => traceOf h es
  | .st i l ots :: es => if i = h then (l, ots) :: traceOf h es else traceOf h es

/-- `r.trace h` (CoreDefs.lean `PFRun.trace`, :52). -/
def MRun.trace (r : MRun) (h : Nat) : List (MLab × Option Nat) := traceOf h r.evs

/-- The load values of a trace, in order. -/
def loadVals (τ : List (MLab × Option Nat)) : List Nat :=
  τ.filterMap (fun e => match e.1 with
    | .load _ _ v _ => some v
    | _ => none)

/-- `r.obsLoad h k`: the value of the `k`-th load of hart `h` (CoreDefs.lean `PFRun.obsLoad`, :80). -/
def MRun.obsLoad (r : MRun) (h k : Nat) : Option Nat := (loadVals (r.trace h))[k]?

end Weak.Mini.Mach
