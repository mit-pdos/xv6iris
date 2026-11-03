/-
Weak/Prom: **the probe generator** (S0-P part (4); plan rev 7 §1A Instrument 3, Appendix B), PHASE-1 SCOPE
([OWN.P3]: translation off; G4 deferred).  Litmus programs in RefProg's ISA (`Weak/Prom/RefProg.lean`), for the
existing pipelines: the reference (RefCheck's enumerator), machine v2 at label level (MachLitmus), machine v2 through
the Sail model (MachSail), and TODAY's machine (CalibToday).  Families:

* **G1** — po-pair matrix: an event pair `e1; link; e2` on the PROBED hart, closed by every standard shape (LB, MP
  (writer / reader), SB, S (writer / reader), R (writer / reader), 2+2W, WRC, IRIW, CoWW, CoWR, CoRW, CoRR); the
  other harts are fixed closers (`fence rw,rw` between their accesses).  Event alphabet (phase 1, litmus ISA):
  plain load/store (`.w`; widths 1/2/8 in G1w), Zalasr `lw.aq[rl]`/`sw.[aq]rl` (label level only: no Sail access
  kind), `lr.w` × {∅, aq, rl, aqrl}, `sc.w` (after its `lr.w`) × {∅, aq, rl, aqrl}, a failing `sc.w` with no LR
  (`scF`: SC failure, no memory operation), `amoadd.w r,x0` (an AMO used as a read), `amoswap.w` × {∅, aq, rl, aqrl}.
  Link kinds: none (po), addr, data, ctrl (`bne`, taken when the value is 1), ctrlB (`beq …, x0`: NOT taken when
  the value is 1, FC-4), every FENCE kind over {r, w} (9), `fence.tso`, `fence.i`; for the Co shapes also an
  overlapping unequal footprint (`ovl`: the second access is a byte at `x+1`).
  PRUNING (logged by `g1Drops`): addr/ctrl/ctrlB need a register-producing `e1` (not a plain or release store);
  data needs that and a storing `e2`; `ovl` only with a plain `e2` in a Co shape.  Device accesses, CSR writes, trap
  entry/return and every implicit event (fetch, walks, A/D, `sfence.vma`) are not in the litmus ISA: fetches are
  exercised by the Sail-level runs of every probe; the rest is Sail-level-only or out of phase 1 (PROGRESS).
* **G1b** — def-use pairs of machine v2's `PState` fields (`v2Fields`: writer and reader labels read off
  Machine.lean's arms), each pair `(X, Y)` placed adjacent and SPLIT by an intervening instruction (a new
  instruction boundary `LInstr`, where `wLdv`/`wRmw`/`wIfv` reset) in the LB, MP and SB shapes.
* **G3** — per conditional premise, both branch values, with LOCATION VALUES FROM THE GUARD'S OWN CONSTANTS:
  today's walker gate `adShapedb` (A bit 0x40 set, bits 0–5 as read, value differs: 0x41 over 0x01, …), v2's SC arm
  (`wRes` none / base mismatch / width mismatch / `exclOk` / `rvTs < ts`), `loadOk`'s forwarding branch (`fwdHit`).
* **G5** — permitted-choice probes with INDEPENDENT TEXT VERDICTS (Table S §19.3), phase-1 subset, decided per
  reservation platform.
* **TS** — Table S §19.2 hand probes in phase-1 scope; **ROW** — the §5 rows of RefTests.lean (text verdicts =
  the `ref_*` theorems, which equal Table S §19.1).
-/
import Weak.Prom.RefLitmus2
import Weak.Prom.MachLitmus

namespace Weak.Prom.Probe

open Weak.Prom Weak.Prom.Ref Weak.Prom.Ref.Lit
open Weak.Prom.Mach (Key)

/-- A probe: family, name, the test, its observables, an optional text verdict (`(cond, ALLOWED?)`), and the
reservation platform it is decided at (`none`: the union over platforms). -/
structure Probe where
  fam : String
  name : String
  T : Test
  obs : List Key
  verdict : Option (OC × Bool) := none
  plat : Option Bool := none

/-! ## 1. Events and links -/

/-- The event alphabet. -/
inductive EK where
  | ld (sz : Nat)
  | ldAq (rl : Bool)
  | lr (aq rl : Bool)
  | amoR (aq rl : Bool)
  | st (sz : Nat)
  | stRl (aq : Bool)
  | sc (aq rl : Bool)
  | scF
  | amoW (aq rl : Bool)
  deriving DecidableEq, Repr, Inhabited

def bs (b : Bool) : String := if b then "1" else "0"

def EK.name : EK → String
  | .ld sz => s!"ld{sz}" | .ldAq rl => s!"ldAq{bs rl}" | .lr aq rl => s!"lr{bs aq}{bs rl}"
  | .amoR aq rl => s!"amoR{bs aq}{bs rl}" | .st sz => s!"st{sz}" | .stRl aq => s!"stRl{bs aq}"
  | .sc aq rl => s!"sc{bs aq}{bs rl}" | .scF => "scF" | .amoW aq rl => s!"amoW{bs aq}{bs rl}"

/-- Does the event put a value in a destination register (so addr/data/ctrl can start from it)? -/
def EK.prod : EK → Bool
  | .st _ | .stRl _ => false
  | _ => true

/-- Does the event store a register's value (so a data link can feed it)? -/
def EK.stores : EK → Bool
  | .st _ | .stRl _ | .sc .. | .scF | .amoW .. => true
  | _ => false

/-- Uses Zalasr (label level only). -/
def EK.zalasr : EK → Bool
  | .ldAq _ | .stRl _ => true
  | _ => false

def bools : List (Bool × Bool) := [(false, false), (true, false), (false, true), (true, true)]

/-- The R-slot alphabet (events that read memory). -/
def rKinds : List EK :=
  [.ld 4, .ldAq false, .ldAq true] ++ bools.map (fun (a, r) => EK.lr a r) ++ bools.map (fun (a, r) => EK.amoR a r) ++
  bools.map (fun (a, r) => EK.amoW a r)

/-- The W-slot alphabet (events that write memory, and the SC failure). -/
def wKinds : List EK :=
  [.st 4, .stRl false, .stRl true] ++ bools.map (fun (a, r) => EK.sc a r) ++ [.scF] ++
  bools.map (fun (a, r) => EK.amoW a r) ++ bools.map (fun (a, r) => EK.amoR a r)

inductive LK where
  | po | addr | data | ctrl | ctrlB | fence (pr pw sr sw : Bool) | tso | fi | ovl
  deriving DecidableEq, Repr, Inhabited

def LK.name : LK → String
  | .po => "po" | .addr => "addr" | .data => "data" | .ctrl => "ctrl" | .ctrlB => "ctrlB"
  | .fence pr pw sr sw => s!"f{if pr then "r" else ""}{if pw then "w" else ""}.{if sr then "r" else ""}{if sw then "w" else ""}"
  | .tso => "tso" | .fi => "fi" | .ovl => "ovl"

def fenceLinks : List LK :=
  [(true, false), (false, true), (true, true)].flatMap (fun (pr, pw) =>
    [(true, false), (false, true), (true, true)].map (fun (sr, sw) => LK.fence pr pw sr sw))

def links : List LK := [.po, .addr, .data, .ctrl, .ctrlB] ++ fenceLinks ++ [.tso, .fi]

/-! ## 2. Building a hart

Registers: location bases `x8` (x), `x9` (y), `x18` (z) set in `regs0`; the first event's destination `x10`, the
second's `x11`; store values `x5` (first), `x6` (second); link temporaries `x7`, `x28`; computed address `x29`;
the LR before an SC writes `x14`/`x15`. -/

def rX : Nat := 8
def rY : Nat := 9
def rZ : Nat := 18

/-- The code of one event: kind `k`, base register `b` (+ offset `off`), destination `d`, value register `v`
(already holding the value), LR scratch `lrd`. -/
def evCode (k : EK) (b off d v lrd : Nat) : List Instr :=
  match k with
  | .ld sz => [.load sz true d b off]
  | .ldAq rl => [.loadAq 4 rl d b]
  | .lr aq rl => [.lr 4 aq rl d b]
  | .amoR aq rl => [.amo .add 4 aq rl d 0 b]
  | .st sz => [.store sz v b off]
  | .stRl aq => [.storeRl 4 aq v b]
  | .sc aq rl => [.lr 4 false false lrd b, .sc 4 aq rl d v b]
  | .scF => [.sc 4 false false d v b]
  | .amoW aq rl => [.amo .swap 4 aq rl d v b]

/-- The access size of an event. -/
def EK.size : EK → Nat
  | .ld sz | .st sz => sz
  | _ => 4

/-- Is the event a plain access (eligible for the `ovl` footprint change)? -/
def EK.plain : EK → Bool
  | .ld _ | .st _ => true
  | _ => false

/-- A probed hart `e1; link; e2`: e1 at base `b1` with value `v1`, e2 at base `b2` with value `v2`.  Returns the
code (with `li`s of the store values first) and the destination registers observed. -/
def pairCode (e1 : EK) (lk : LK) (e2 : EK) (b1 b2 v1 v2 : Nat) : List Instr × List Nat :=
  let pre := [li 5 v1, li 6 v2]
  let c1 := evCode e1 b1 0 10 5 14
  let (mid, b2', vreg) : List Instr × Nat × Nat := match lk with
    | .po => ([], b2, 6)
    | .addr => ([xor 7 10 10, add 29 b2 7], 29, 6)
    | .data => ([xor 7 10 10, ori 7 7 v2], b2, 7)
    | .ctrl => ([], b2, 6)      -- the branch is placed below (it needs its index)
    | .ctrlB => ([], b2, 6)
    | .fence pr pw sr sw => ([fence pr pw sr sw], b2, 6)
    | .tso => ([.fenceTso], b2, 6)
    | .fi => ([.fencei], b2, 6)
    | .ovl => ([], b2, 6)
  let e2' := if lk == .ovl then (match e2 with | .ld _ => EK.ld 1 | .st _ => EK.st 1 | k => k) else e2
  let off2 := if lk == .ovl then 1 else 0
  let c2 := evCode e2' b2' off2 11 vreg 15
  let n0 := pre.length + c1.length
  let br : List Instr := match lk with
    | .ctrl => [.br .ne 10 0 (n0 + 1)]
    | .ctrlB => [.br .eq 10 0 (n0 + 1)]
    | _ => []
  (pre ++ c1 ++ mid ++ br ++ c2, [10, 11])

/-- A fixed closer `R a; fence rw,rw; R b` (destinations `x10`, `x11`). -/
def closeRR (a b : Nat) : List Instr := [lw 10 a, fRWRW, lw 11 b]
def closeWW (a b va vb : Nat) : List Instr := [li 5 va, li 6 vb, sw 5 a, fRWRW, sw 6 b]
def closeRW (a b vb : Nat) : List Instr := [li 6 vb, lw 10 a, fRWRW, sw 6 b]
def closeWR (a b va : Nat) : List Instr := [li 5 va, sw 5 a, fRWRW, lw 11 b]
def wOnly (a v : Nat) : List Instr := [li 5 v, sw 5 a]

def regsStd : List (Nat × Nat) := [(rX, X), (rY, Y), (rZ, Z)]

/-- Observables: every hart's `x10`, `x11`, `x14`, `x15` (destinations) and the final words of x, y. -/
def obsStd (nh : Nat) : List Key :=
  ((List.range nh).flatMap (fun h => [Key.reg h 10, .reg h 11, .reg h 14, .reg h 15])) ++ [.mem X 4, .mem Y 4]

def mkT (hs : List (List Instr)) : Test :=
  ⟨hs, hs.map (fun _ => regsStd), [], [], .tt⟩

/-! ## 3. G1: shapes -/

/-- The shapes: name, slot types of the probed pair (`R`/`W` per position), and the test given the probed hart's
code. -/
structure Shape where
  name : String
  r1 : Bool      -- slot 1 reads (else writes)
  r2 : Bool
  co : Bool      -- same-location shape
  build : EK → LK → EK → List (List Instr)

def probed (e1 : EK) (lk : LK) (e2 : EK) (b1 b2 v1 v2 : Nat) : List Instr := (pairCode e1 lk e2 b1 b2 v1 v2).1

def shapes : List Shape :=
  [ ⟨"LB", true, false, false, fun e1 lk e2 => [probed e1 lk e2 rX rY 1 1, closeRW rY rX 1]⟩,
    ⟨"MPw", false, false, false, fun e1 lk e2 => [probed e1 lk e2 rX rY 1 1, closeRR rY rX]⟩,
    ⟨"MPr", true, true, false, fun e1 lk e2 => [closeWW rX rY 1 1, probed e1 lk e2 rY rX 1 1]⟩,
    ⟨"SB", false, true, false, fun e1 lk e2 => [probed e1 lk e2 rX rY 1 1, closeWR rY rX 1]⟩,
    ⟨"Sw", false, false, false, fun e1 lk e2 => [probed e1 lk e2 rX rY 2 1, closeRW rY rX 1]⟩,
    ⟨"Sr", true, false, false, fun e1 lk e2 => [closeWW rX rY 2 1, probed e1 lk e2 rY rX 1 1]⟩,
    ⟨"Rw", false, false, false, fun e1 lk e2 => [probed e1 lk e2 rX rY 1 1, closeWR rY rX 2]⟩,
    ⟨"Rr", false, true, false, fun e1 lk e2 => [closeWW rX rY 1 1, probed e1 lk e2 rY rX 2 1]⟩,
    ⟨"2+2W", false, false, false, fun e1 lk e2 => [probed e1 lk e2 rX rY 1 2, closeWW rY rX 1 2]⟩,
    ⟨"WRC", true, false, false, fun e1 lk e2 => [wOnly rX 1, probed e1 lk e2 rX rY 1 1, closeRR rY rX]⟩,
    ⟨"IRIW", true, true, false, fun e1 lk e2 => [wOnly rX 1, wOnly rY 1, probed e1 lk e2 rX rY 1 1, closeRR rY rX]⟩,
    ⟨"CoWW", false, false, true, fun e1 lk e2 => [probed e1 lk e2 rX rX 1 2, closeRR rX rX]⟩,
    ⟨"CoWR", false, true, true, fun e1 lk e2 => [probed e1 lk e2 rX rX 1 1, wOnly rX 2]⟩,
    ⟨"CoRW", true, false, true, fun e1 lk e2 => [probed e1 lk e2 rX rX 1 1, wOnly rX 2]⟩,
    ⟨"CoRR", true, true, true, fun e1 lk e2 => [probed e1 lk e2 rX rX 1 1, wOnly rX 1]⟩ ]

/-- Why a (pair, link) cell is dropped (`none`: kept). -/
def drop (sh : Shape) (e1 : EK) (lk : LK) (e2 : EK) : Option String :=
  match lk with
  | .addr | .ctrl | .ctrlB => if e1.prod then none else some "addr/ctrl from a non-producing event"
  | .data => if !e1.prod then some "data from a non-producing event"
             else if !e2.stores then some "data into a non-storing event" else none
  | .ovl => if !sh.co then some "ovl outside a same-location shape"
            else if !e2.plain then some "ovl needs a plain second access" else none
  | _ => none

def g1Cells : List (Shape × EK × LK × EK) :=
  shapes.flatMap (fun sh =>
    (if sh.r1 then rKinds else wKinds).flatMap (fun e1 =>
      (links ++ (if sh.co then [LK.ovl] else [])).flatMap (fun lk =>
        (if sh.r2 then rKinds else wKinds).map (fun e2 => (sh, e1, lk, e2)))))

def g1Probes : List Probe :=
  g1Cells.filterMap (fun (sh, e1, lk, e2) =>
    if (drop sh e1 lk e2).isSome then none else
    let hs := sh.build e1 lk e2
    some ⟨"G1", s!"{sh.name}:{e1.name}:{lk.name}:{e2.name}", mkT hs, obsStd hs.length, none, none⟩)

/-- The drop log: (reason, count). -/
def g1Drops : List (String × Nat) :=
  let rs := g1Cells.filterMap (fun (sh, e1, lk, e2) => drop sh e1 lk e2)
  rs.eraseDups.map (fun r => (r, rs.count r))

/-- G1w: the width classes (1, 2, 8 bytes) of plain loads/stores, every link, in LB/MP/SB/CoWR/CoRW. -/
def g1wProbes : List Probe :=
  [1, 2, 8].flatMap (fun sz =>
    let wide : List (String × EK × EK × (EK → LK → EK → List (List Instr))) :=
      [("LB", .ld sz, .st sz, fun e1 lk e2 => [probed e1 lk e2 rX rY 1 1, closeRW rY rX 1]),
       ("MPw", .st sz, .st sz, fun e1 lk e2 => [probed e1 lk e2 rX rY 1 1, closeRR rY rX]),
       ("SB", .st sz, .ld sz, fun e1 lk e2 => [probed e1 lk e2 rX rY 1 1, closeWR rY rX 1]),
       ("CoWR", .st sz, .ld sz, fun e1 lk e2 => [probed e1 lk e2 rX rX 1 1, wOnly rX 2]),
       ("CoRW", .ld sz, .st sz, fun e1 lk e2 => [probed e1 lk e2 rX rX 1 1, wOnly rX 2])]
    wide.flatMap (fun (nm, e1, e2, f) => links.filterMap (fun lk =>
      if (lk == .addr || lk == .ctrl || lk == .ctrlB || lk == .data) && !e1.prod then none else
      let hs := f e1 lk e2
      some ⟨"G1w", s!"{nm}:{e1.name}:{lk.name}:{e2.name}", mkT hs, obsStd hs.length, none, none⟩)))

/-- Single-hart LR;X;SC for every X of the alphabet (and an interfering store on x by another hart). -/
def lrxscProbes : List Probe :=
  let xs : List (String × List Instr) :=
    [("nop", [.nop]), ("ld-x", [lw 12 rX]), ("ld-y", [lw 12 rY]), ("st-x", [li 6 3, sw 6 rX]),
     ("st-y", [li 6 3, sw 6 rY]), ("sb-x+1", [li 6 3, sb 6 rX 1]), ("amo-x", [amoaddW false false 12 0 rX]),
     ("amo-y", [amoaddW false false 12 0 rY]), ("lr-y", [lrW 12 rY]), ("sc-y", [scW 12 6 rY]),
     ("f.rwrw", [fRWRW]), ("f.w.0", [fence false true false false]), ("tso", [.fenceTso]), ("fi", [.fencei]),
     ("csrr", [.csrr 12 misaV]), ("br", [.br .ne 10 0 2])]
  xs.flatMap (fun (nm, xc) =>
    let h0 := [lrW 10 rX] ++ xc ++ [li 7 5, scW 11 7 rX]
    [⟨"G1lxs", s!"LRXSC:{nm}", mkT [h0], obsStd 1 ++ [.reg 0 12], none, none⟩,
     ⟨"G1lxs", s!"LRXSC+W:{nm}", mkT [h0, wOnly rX 9], obsStd 2 ++ [.reg 0 12], none, none⟩])

/-! ## 4. G1b: def-use pairs of machine v2's fields -/

/-- Machine v2's `PState` fields with their WRITER and READER events (read off Machine.lean: `loadByte`/`loadRun`,
`storeRun`, `amoPost`, `acqPost`, `fencePost`, `fenceIPost`, the `regW`/`ctrl`/`instr` posts, the `lr`/`sc`/
`scFail` arms; readers are the premises and pre-views: `ldPre`, `stPre`, `stPreA`, `loadOk`'s floor and
forwarding, `cohBelow`, `srcsView`, the `sc` arm's `wRes`).  Fetch fields (`wIfl`, `wIfr`, `wIfv`) are exercised at
Sail level only (no litmus program writes code); `wRmw` is internal to an AMO (fused at label level). -/
def v2Fields : List (String × List (String × List Instr) × List (String × List Instr)) :=
  [ ("wCoh", [("ld", [lw 10 rX]), ("st", [li 5 1, sw 5 rX]), ("amo", [amoaddW false false 10 0 rX])],
             [("ld", [lw 11 rX]), ("st", [li 6 2, sw 6 rX])]),
    ("wVrOld", [("ld", [lw 10 rX]), ("amo", [amoaddW false false 10 0 rX])],
               [("f.r.rw", [fence true false true true, lw 11 rY]), ("stRl", [li 6 1, .storeRl 4 false 6 rY]),
                ("amoRl", [li 6 1, amoswapW false true 11 6 rY])]),
    ("wVwOld", [("st", [li 5 1, sw 5 rX]), ("amo", [li 5 1, amoswapW false false 10 5 rX])],
               [("f.w.rw", [fence false true true true, lw 11 rY]), ("stRl", [li 6 1, .storeRl 4 false 6 rY])]),
    ("wVrNew", [("f.rw.r", [fence true true true false]), ("ldAq", [.loadAq 4 false 10 rX]),
                ("amoAq", [amoaddW true false 10 0 rX])],
               [("ld", [lw 11 rY])]),
    ("wVwNew", [("f.rw.w", [fence true true false true]), ("ldAq", [.loadAq 4 false 10 rX]),
                ("scAqRl", [lrW 14 rX, li 5 1, .sc 4 true true 10 5 rX])],
               [("st", [li 6 1, sw 6 rY])]),
    ("wVRel", [("stRl", [li 5 1, .storeRl 4 false 5 rX]), ("ldAqRl", [.loadAq 4 true 10 rX]),
               ("lrAqRl", [.lr 4 true true 10 rX])],
              [("ldAq", [.loadAq 4 false 11 rY]), ("stAqRl", [li 6 1, .storeRl 4 true 6 rY])]),
    ("wFwd", [("st", [li 5 1, sw 5 rX]), ("sc", [lrW 14 rX, li 5 1, scW 10 5 rX])],
             [("ld", [lw 11 rX]), ("ldAq", [.loadAq 4 false 11 rX])]),
    ("wRegv", [("ld", [lw 10 rX]), ("alu", [lw 10 rX, xor 10 10 10])],
              [("addr", [xor 7 10 10, add 29 rY 7, lw 11 29]), ("data", [ori 10 10 1, sw 10 rY])]),
    ("wVcap", [("ctrl", [lw 10 rX, .br .ne 10 0 0]), ("addr-ld", [lw 10 rX, xor 7 10 10, add 29 rZ 7, lw 12 29])],
              [("st", [li 6 1, sw 6 rY])]),
    ("wLdv", [("ld", [lw 10 rX]), ("amo", [amoaddW false false 10 0 rX])],
             [("regw", [ori 11 10 0, sw 11 rY])]),
    ("wRes", [("lr", [lrW 10 rX]), ("scF", [scW 13 0 rY])],
             [("sc", [li 5 1, scW 11 5 rX])]) ]

/-- Fix the branch targets of a code block placed at index `base` (the G1b `ctrl` writer branches to the next
instruction; its literal target `0` means "next"). -/
def fixBr (base : Nat) (c : List Instr) : List Instr :=
  (List.range c.length).map (fun k => match c[k]? with
    | some (Instr.br cnd a b 0) => Instr.br cnd a b (base + k + 1)
    | some i => i
    | none => Instr.nop)

def g1bProbes : List Probe :=
  v2Fields.flatMap (fun (f, ws, rs) => ws.flatMap (fun (wn, wc) => rs.flatMap (fun (rn, rc) =>
    [false, true].flatMap (fun split =>
      let mid := if split then [Instr.nop] else []
      let h0 := fixBr 0 (wc ++ mid ++ rc)
      let tag := s!"{f}:{wn}>{rn}{if split then ":split" else ""}"
      [⟨"G1b", s!"LB:{tag}", mkT [h0, closeRW rY rX 1], obsStd 2 ++ [.reg 0 12, .reg 0 13], none, none⟩,
       ⟨"G1b", s!"MP:{tag}", mkT [closeWW rY rX 1 1, h0], obsStd 2 ++ [.reg 1 12, .reg 1 13], none, none⟩,
       ⟨"G1b", s!"SB:{tag}", mkT [h0, closeWR rY rX 1], obsStd 2 ++ [.reg 0 12, .reg 0 13], none, none⟩]))))

/-! ## 5. G3: guard branches with the guards' own constants -/

/-- Today's walker gate `adShapedb` (WeakPromise.lean:466–473: byte 0 has bit 6 set, bits 0–5 as read, differs;
bytes 1… as read): `amoswap.w x0,v,(x)` over an initial `x = w`, in row 30's LB shape, for value pairs that take
each branch of each conjunct (bit 6 of `v`; bits 0–5 equal or not; `v ≠ w`; upper bytes equal or not). -/
def adPairs : List (Nat × Nat) :=
  [(0x01, 0x41), (0x41, 0x41), (0x01, 0x01), (0x00, 0x40), (0x3f, 0x7f), (0x01, 0x42), (0x81, 0xc1),
   (0x101, 0x141), (0x101, 0x241), (0xc1, 0x41)]

def g3Probes : List Probe :=
  (adPairs.map (fun (w, v) =>
    let T := mk [[lw 10 rY, li 5 v, amoswapW false false 0 5 rX], [lw 11 rX, sw 11 rY]]
      [regsStd, regsStd] (ini X w 4) .tt
    (⟨"G3", s!"adShape:{w}:{v}", T, [.reg 0 10, .reg 1 11, .mem X 4, .mem Y 4], none, none⟩ : Probe))) ++
  -- v2's SC arm: no reservation; base mismatch; width mismatch; exclOk fails (remote store); a successful pair
  [ ⟨"G3", "sc:noRes", mkT [[li 5 1, scW 11 5 rX]], obsStd 1, none, none⟩,
    ⟨"G3", "sc:baseMis", mkT [[lrW 10 rX, li 5 1, scW 11 5 rY]], obsStd 1, none, none⟩,
    ⟨"G3", "sc:widthMis", mkT [[lrD 10 rX, li 5 1, scW 11 5 rX]], obsStd 1, none, none⟩,
    ⟨"G3", "sc:exclOk", mkT [[lrW 10 rX, li 5 1, scW 11 5 rX], wOnly rX 2], obsStd 2, none, none⟩,
    ⟨"G3", "sc:ok", mkT [[lrW 10 rX, li 5 1, scW 11 5 rX]], obsStd 1, none, none⟩,
    -- loadOk's forwarding branch: own store forwarded / not (a remote store in between)
    ⟨"G3", "fwd:hit", mkT [[li 5 1, sw 5 rX, lw 10 rX], wOnly rX 2], obsStd 2, none, none⟩,
    ⟨"G3", "fwd:miss", mkT [[li 5 1, sw 5 rY, lw 10 rX], wOnly rX 2], obsStd 2, none, none⟩ ]

/-! ## 6. G5 and the Table-S hand probes (text verdicts) -/

/-- G5 (i)/(ii) in phase-1 scope, decided at the stated platform (`plat = some true`: `xv6_resv_matches ≡ true`). -/
def g5Probes : List Probe :=
  [ -- G5-SCFAIL (CS-7, ZL-U10 "fail … occasionally for any reason"): no interference, platform true
    ⟨"G5", "SCFAIL", mkT [[lrW 10 rX, li 5 1, scW 11 5 rX]], obsStd 1, some (r 0 11 1, true), some true⟩,
    -- row 47 (sc_other_hart_store_fail): the failure must be reachable on both predicate values
    ⟨"G5", "row47-P1", mkT [[lrW 10 rX, li 5 1, scW 11 5 rX], wOnly rX 2], obsStd 2,
      some (ands [r 0 11 1], true), some true⟩,
    ⟨"G5", "row47-P0", mkT [[lrW 10 rX, li 5 1, scW 11 5 rX], wOnly rX 2], obsStd 2,
      some (ands [r 0 11 1], true), some false⟩,
    -- memWrite exclusive alternative "success" (CS-6/CS-7: both answers admissible), platform true
    ⟨"G5", "SCOK", mkT [[lrW 10 rX, li 5 1, scW 11 5 rX]], obsStd 1, some (r 0 11 0, true), some true⟩,
    -- the failure followed by success on one address with no interference (SR-21 (c2), R4.s7)
    ⟨"G5", "FAIL-then-OK", mkT [[lrW 10 rX, li 5 1, scW 11 5 rX, lrW 12 rX, scW 13 5 rX]],
      obsStd 1 ++ [.reg 0 12, .reg 0 13], some (ands [r 0 11 1, r 0 13 0], true), some true⟩,
    -- CS-6 (lr_reservation_set_size; rvwmo.adoc:340-342): SC to another address than its LR's may succeed
    ⟨"G5", "35d-mismatch", lrsdsc_d, [.reg 0 28, .mem X 8, .mem (X + 8) 4], some (r 0 28 0, true), some true⟩,
    -- CS-9 (ZL-U7): unannotated LR/SC observed before/after surrounding operations: 31b / 35a
    ⟨"G5", "31b", lrldsc, [.reg 0 11, .reg 0 5], some (r 0 11 0, true), some true⟩,
    ⟨"G5", "35a", lrsdsc_a, [.reg 0 28, .mem X 8], some (r 0 28 0, true), some true⟩,
    ⟨"G5", "36", lrAmoSc, [.reg 0 11, .reg 0 5], some (r 0 11 0, true), some true⟩ ]

/-- Table S §19.2 hand probes in phase-1 scope. -/
def tsProbes : List Probe :=
  [ ⟨"TS", "T-R3a", mk [[li 5 1, amoswapW false false 0 5 rX, lw 10 rX, sw 10 rY], [lw 11 rY, fRR, lw 12 rX]]
      [regsStd, regsStd] [] .tt, [.reg 0 10, .reg 1 11, .reg 1 12], some (ands [r 1 11 1, r 1 12 0], false), none⟩,
    ⟨"TS", "T-R3b", mk [[lrW 5 rX, li 6 1, scW 13 6 rX, lw 10 rX, sw 10 rY], [lw 11 rY, fRR, lw 12 rX]]
      [regsStd, regsStd] [] .tt, [.reg 0 13, .reg 0 10, .reg 1 11, .reg 1 12],
      some (ands [r 0 13 0, r 1 11 1, r 1 12 0], false), none⟩,
    ⟨"TS", "T-LR2", mkT [[lrW 10 rX, lrW 11 rY, li 5 1, scW 12 5 rX]], [.reg 0 12], some (r 0 12 0, true), none⟩,
    ⟨"TS", "T-NOLR", mkT [[li 5 1, scW 11 5 rX]], [.reg 0 11], some (r 0 11 0, false), none⟩,
    ⟨"TS", "LRSC-AQRL", mk [[li 5 1, sw 5 rX, lrW 7 rY, .sc 4 true false 10 5 rY], [lw 11 rY, fRR, lw 12 rX]]
      [regsStd, regsStd] [] .tt, [.reg 0 10, .reg 1 11, .reg 1 12],
      some (ands [r 0 10 0, r 1 11 1, r 1 12 0], true), none⟩,
    ⟨"TS", "PAUSE-SC", mkT [[lrW 10 rX, fence false true false false, li 5 1, scW 11 5 rX]], [.reg 0 11],
      some (r 0 11 0, true), none⟩,
    ⟨"TS", "FT-1", mk [[li 5 1, sw 5 rX, .fenceTso, lw 10 rY], [li 5 1, sw 5 rY, .fenceTso, lw 10 rX]]
      [regsStd, regsStd] [] .tt, [.reg 0 10, .reg 1 10], some (ands [r 0 10 0, r 1 10 0], true), none⟩,
    ⟨"TS", "FT-2", mk [[li 5 1, amoswapW false false 0 5 rX, .fenceTso, ld 10 rY],
                       [li 5 1, amoswapW false false 0 5 rY, .fenceTso, ld 10 rX]]
      [regsStd, regsStd] [] .tt, [.reg 0 10, .reg 1 10], some (ands [r 0 10 0, r 1 10 0], false), none⟩ ]

/-- The §5 rows (RefTests.lean), text verdicts = `ref_*` (= Table S §19.1). -/
def rowProbes : List Probe :=
  let mkP (allowed : Bool) (n : String) (T : Test) : Probe :=
    let ks := Mach.condKeys T.cond
    ⟨"ROW", n, { T with cond := .tt }, ks, some (T.cond, allowed), none⟩
  [("lb", lb), ("mp", mp), ("sbT", sbT), ("sbFwd", sbFwd), ("ppoca", ppoca), ("datacoirfi", datacoirfi),
   ("datacoirfiR", datacoirfiR), ("frirfi", frirfi), ("rsw", rsw), ("w22", w22), ("isa2", isa2), ("wrc", wrc),
   ("iriwCtrlFi", iriwCtrlFi), ("iriw", iriw), ("mix26d", mix26d), ("mix26e", mix26e), ("mix26f", mix26f),
   ("mix26g", mix26g), ("lbAmoPo", lbAmoPo), ("lbAmoAd", lbAmoAd), ("lrsc", lrsc), ("lrldsc", lrldsc),
   ("lrsdsc_a", lrsdsc_a), ("lrsdsc_b", lrsdsc_b), ("lrsdsc_c", lrsdsc_c), ("lrsdsc_d", lrsdsc_d),
   ("lrAmoSc", lrAmoSc), ("lbMisa", lbMisa), ("updStuck", updStuck)].map (fun (n, T) => mkP true n T) ++
  [("lbdd", lbdd), ("lbDatas", lbDatas), ("lbCtrls", lbCtrls), ("lbCtrlsBeq", lbCtrlsBeq), ("lbLrsc", lbLrsc),
   ("oota42", oota42), ("mpFF", mpFF), ("mpFFrr", mpFFrr), ("mpFAddr", mpFAddr), ("mpAmoRlAq", mpAmoRlAq),
   ("mpFAmo", mpFAmo), ("amoStorePart", amoStorePart), ("sbFF", sbFF), ("datarfi", datarfi), ("addrpo", addrpo),
   ("addrpoR", addrpoR), ("w22F", w22F), ("coWW", coWW), ("coWR0", coWR0), ("coWR", coWR), ("coRW1", coRW1),
   ("coRW2", coRW2), ("coRR", coRR), ("coRR2", coRR2), ("parInc", parInc), ("isa2F", isa2F), ("wrcF", wrcF),
   ("iriwF", iriwF), ("mix26a", mix26a), ("mix26b", mix26b), ("mix26c", mix26c), ("mix26dNot", mix26dNot),
   ("mix26h", mix26h), ("mix26i", mix26i), ("mpAmoData", mpAmoData), ("mpAmoCtrl", mpAmoCtrl), ("mixSca", mixSca),
   ("lrScSc", lrScSc), ("wsub", wsub), ("armWeak", armWeak), ("lbAcq", lbAcq), ("lbRel", lbRel), ("coh", Lit.coh),
   ("seqT", seqT), ("lbfd", lbfd), ("rng", rng), ("disjLists", disjLists), ("ramAq", ramAq)].map
    (fun (n, T) => mkP false n T)

/-- Every family (G2 is Sail-level only: `ProbeG2.lean`). -/
def family (f : String) : List Probe :=
  match f with
  | "G1" => g1Probes
  | "G1w" => g1wProbes
  | "G1lxs" => lrxscProbes
  | "G1b" => g1bProbes
  | "G3" => g3Probes
  | "G5" => g5Probes
  | "TS" => tsProbes
  | "ROW" => rowProbes
  | _ => []

end Weak.Prom.Probe
