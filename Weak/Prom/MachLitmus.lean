/-
Weak/Prom: **machine v2 on litmus programs at LABEL LEVEL** (S0-P part (2), milestone 1): the front end (litmus
ISA → per-hart `PLabel` streams) and the exact bounded explorer of v2's valid runs in promises-first normal form.

## The front end (label level)

A hart runs the litmus ISA of `Weak/Prom/RefProg.lean` CONCRETELY (64-bit register values; `aluOp`, `brEval`,
`amoOp`, `sext`, `byteList`, `bytesVal` are RefProg's), and each instruction emits this label sequence (machine
v2's alphabet; register views travel through `LRegW` sources, the SYNTACTIC dependency sources, M19):

| instruction | labels |
|---|---|
| `op rd, rs1[, rs2/imm]`        | `LRegW rd [rs1, rs2]`, `LInstr` |
| `l{b,h,w,d}[u] rd, off(rs1)`    | `LLoad false a tvs [rs1]`, `LRegW rd [DLdRes]`, `LInstr` |
| `l*.aq[rl] rd, (rs1)` (Zalasr)  | `LLoad true a tvs [rs1]`, `LRegW rd [DLdRes]`, `LInstr` (the `rl` bit has no v2 label field: GAP-RL) |
| `s{b,h,w,d} rs2, off(rs1)`      | `LStore false a data [rs1] [rs2]` (fulfils `ts`), `LInstr` |
| `s*.[aq]rl rs2, (rs1)` (Zalasr) | `LStore true a data [rs1] [rs2]`, `LInstr` (the `aq` bit has no v2 field: GAP-AQ) |
| `lr.{w,d}[.aq][.rl]`            | `LExLoad aq a tvs [rs1]`, `LRegW rd [DLdRes]`, `LInstr` (`lr.aqrl`'s release: GAP-RL) |
| `sc` success                    | `LExStore rl a data [rs1] [rs2]`, `LRegW rd [DLdRes]` (value 0, M4), `LExFail` (end of SC, M16 (c1)), `LInstr` (`sc.aqrl`'s acquire: GAP-AQ) |
| `sc` failure                    | `LExFail`, `LRegW rd []` (value 1), `LExFail`, `LInstr` |
| `amo<op>.{w,d}[.aq][.rl]`       | FUSED `LRmw aq rl a tvs data [rs1] [rs2]`, `LRegW rd [DLdRes]`, `LInstr` |
| `fence p,s`                     | `LFence pr pw sr sw` (i/o bits dropped, SAIL-GAP-1), `LInstr` |
| `fence.tso`                     | `LFence r,rw`, `LFence w,w` (M6's two halves, back to back), `LInstr` |
| `fence.i`                       | `LFenceI`, `LInstr` |
| `b<c> rs1, rs2, L`              | `LCtrl [rs1, rs2]`, `LInstr` |
| `j L`, `nop`                    | `LInstr` |
| `csrr rd` (unwritten CSR)       | `LRegW rd []`, `LInstr` |

`x0` is never a source (`srcR`) and never written (no `LRegW`).  An access whose address is not naturally aligned
drops the run and is COUNTED (`Res.oos`), the scope of RefProg's `condsOk`.  RefProg's hypothetical RCpc forms
(`loadAqPc`/`storeRlPc`) are out of scope (no v2 label).

**Where this differs from going through Sail (`Weak/Prom/Emit.lean`; the gap milestone 3 closes):**
1. No `LIFetch`: every fetch reads the image at timestamp 0 in a litmus program (code is never written), and a
   timestamp-0 fetch has no view effect (`fetchView` = 0, `wIfr` stays 0); `LFenceI` is still emitted.
2. AMOs are the FUSED `LRmw`; Sail emits the split pair `LAmoLd`/`LAmoSt` through the `wRmw` slot (M10; the
   equivalence is S1M-proof's `amoSplitFused`, M10 (4)).
3. Silent labels (announce, register reads) are omitted; `LCtrl []` (Sail's `nextPC` write of a non-branch) is
   omitted (it is the identity); a branch emits ONE `LCtrl` (Sail emits one per `nextPC` write; `wVcap` is a max).
4. Register sources are the litmus instruction's own operands, not the decoder's `depsOfIb` lists (S0-P (3), the
   decoder check, compares the two).
5. FENCE.TSO's second half is applied immediately (Sail parks it, `HState.fn`, and applies it before the next
   event: no memory event intervenes, so the same state).
6. An SC's success is a free choice gated only by the machine (`wRes`, `exclOk`, COH, EXT); Sail additionally
   consults its opaque reservation predicate (`match_reservation`) and may fail with `.Err ()`.  Either way a
   failure is `LExFail` + `rd := 1` with no sources.
7. Misaligned accesses are out of scope here; Sail decomposes them ([OWN.P1] `splittable`).
8. GAP-RL / GAP-AQ: v2's `LLoad`/`LExLoad` carry no release bit and `LStore`/`LExStore` no acquire bit, so
   `l*.aqrl`, `lr.aqrl` (release-RCsc) and `s*.aqrl`, `sc.aqrl` (acquire-RCsc) lose one annotation — at label level
   AND in Emit.lean (`akAcq ak` is the only bit passed).  Machine-side, this is WEAKER (fewer orderings).

## The explorer (exact within the bound)

**Normal form.**  A valid run of v2 (Machine.lean `validRun`) is explored in PROMISES-FIRST normal form (plan §0
`PF.validRun_factorL`, Pulte et al. Thm 7.1): every message of the final memory `M` is promised first, in `M`'s
order, then each hart runs in program order against `M`.  This is EXACT for final states: (⊆) such a run is a run
of `pmStep`; (⊇) every arm is append-stable and own-promise-monotone (Machine.lean header, [R7.s1]), so moving
every promise to the front keeps each state step admissible with the same label and post-state — the content of
`PF.validRun_factorL` (S1M-proof, not yet a Lean theorem).  Once all promises are made the harts do not interact
(`memStep` reads only the log and the hart's own state), so the behaviours for `M` are the PRODUCT of each hart's
local final states against `M`.

**Candidate final memories.**  `M` is a list of messages; each hart's messages are the stores of one of its
concrete runs, and they may appear in `M` in ANY order except that a hart's own overlapping messages appear in
program order (every write arm checks `cohBelow`, and a write raises `coh` of its bytes to its timestamp — a
pruning implied by the machine, `arrange`).  The possible message lists of a hart (`sigma`) are computed by a
FREE run of the same front end in which a load may return any byte of a value DOMAIN (`freeRun`), iterated:
`dom₀ = the image`, `dom_{k+1} = the image ∪ the bytes of every message of the free runs over dom_k`, until a
fixpoint or `K` = the number of store-like instructions of the test.  Completeness argument (milestone 2 proves it
as a machine lemma, NOTA): in v2 a message's address, data and existence depend only on answers whose views are
below its EXT bound (`stPre … < ts`; register views are the max of the syntactic sources' views, a non-forwarded
answer's view is at least its timestamp, a forwarded one is the own store's address⊔data view, and an AMO's read
precedes its write by `cohBelow`), so the value of every message has a justification chain of at most `K`
messages; `dom_K` contains every byte any message of any valid run holds.  (Pure over-approximation otherwise:
every candidate `M` is checked by the machine run.)

**Per-hart runs.**  For a fixed `M` each hart is a DFS over `Mach.succ` (MachExplore.lean, complete for each
template), starting from `psInit` with its promise set `promsOf M i`, keeping the runs that end with no
outstanding promise (`promDone`).

Bounds: the oracle's (≤ 8 memory instructions per test); explorer budgets (`Budget`) are reported, never turned
into verdicts.
-/
import Weak.Prom.MachExplore
import Weak.Prom.RefProg

namespace Weak.Prom.Mach

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

/-! ## 1. Values and the image -/

def bv8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

/-- Little-endian bytes of a value. -/
def toBytes (v sz : Nat) : List (BitVec 8) := (byteList v sz).map bv8

/-- The value of little-endian bytes. -/
def ofBytes (bs : List (BitVec 8)) : Nat := bytesVal (bs.map BitVec.toNat)

/-- A register as a dependency source (`x0` is never a source). -/
def srcR (r : Nat) : List Dsrc := if r = 0 then [] else [.DReg r]

/-- The register write labels (`x0` is never written). -/
def regWL (rd : Nat) (srcs : List Dsrc) : List PLabel := if rd = 0 then [] else [LRegW rd srcs]

/-- The test's initial memory as a v2 image: every byte defined (absent bytes are 0, as in RefProg's `imgF`). -/
def testImg (T : Test) : Image := fun a => some (bv8 (T.imgF a.toNat))

/-- The answers a read label carries. -/
def readsOf (l : PLabel) : List (Nat × BitVec 8) :=
  match labelReads l with
  | some (_, tvs) => tvs
  | none => []

/-! ## 2. The hart state and one instruction -/

/-- A hart under machine v2 at label level: pc, concrete registers, v2 state, promise set. -/
structure MH where
  pc : Nat
  regs : List Nat
  ws : PState
  prom : GSet Nat

def MH.rd (h : MH) (r : Nat) : Nat := if r = 0 then 0 else (h.regs[r]?).getD 0

def MH.wr (h : MH) (r v : Nat) : MH := if r = 0 then h else { h with regs := h.regs.set r (v % two64) }

/-- The environment of a hart's run: the image, the final memory, the hart. -/
structure Env where
  img : Image
  log : List PMsg
  i : Nat

/-- One template, then the continuation on each successor. -/
def thenT (E : Env) (h : MH) (t : Tmpl) (k : Succ → MH → List MH) : List MH :=
  (succ E.img E.log E.i h.prom h.ws t).flatMap (fun s => k s { h with ws := s.ws, prom := s.prom })

/-- A sequence of answer-free labels, then `pc := pc'`. -/
def fixes (E : Env) : MH → List PLabel → Nat → List MH
  | h, [], pc' => [{ h with pc := pc' }]
  | h, l :: ls, pc' => thenT E h (.fix l) (fun _ h' => fixes E h' ls pc')

/-- The result of one instruction: successors, or out of the label-level scope. -/
inductive StepR where
  | next (hs : List MH)
  | oos (why : String)

/-- Is the access at `a` of `sz` bytes naturally aligned? -/
def aligned (a sz : Nat) : Bool := sz == 0 || a % sz == 0

/-- ONE INSTRUCTION of hart `E.i` (program length `n`) under machine v2, all successors. -/
def stepM (E : Env) (n : Nat) (h : MH) : Instr → StepR
  | .alui op rd rs1 imm =>
      .next (fixes E (h.wr rd (aluOp op (h.rd rs1) imm)) (regWL rd (srcR rs1) ++ [LInstr]) (h.pc + 1))
  | .alu op rd rs1 rs2 =>
      .next (fixes E (h.wr rd (aluOp op (h.rd rs1) (h.rd rs2))) (regWL rd (srcR rs1 ++ srcR rs2) ++ [LInstr])
        (h.pc + 1))
  | .load sz sgn rd rs1 off =>
      let a := (h.rd rs1 + off) % two64
      if !aligned a sz then .oos "misaligned" else
      .next (thenT E h (.ld false a sz (srcR rs1)) (fun s h1 =>
        let raw := ofBytes ((readsOf s.l).map Prod.snd)
        fixes E (h1.wr rd (if sgn then sext sz raw else raw)) (regWL rd [.DLdRes] ++ [LInstr]) (h.pc + 1)))
  | .store sz rs2 rs1 off =>
      let a := (h.rd rs1 + off) % two64
      if !aligned a sz then .oos "misaligned" else
      .next (thenT E h (.st false a (toBytes (h.rd rs2) sz) (srcR rs1) (srcR rs2)) (fun _ h1 =>
        fixes E h1 [LInstr] (h.pc + 1)))
  | .loadAq sz _ rd rs1 =>
      let a := h.rd rs1
      if !aligned a sz then .oos "misaligned" else
      .next (thenT E h (.ld true a sz (srcR rs1)) (fun s h1 =>
        fixes E (h1.wr rd (sext sz (ofBytes ((readsOf s.l).map Prod.snd)))) (regWL rd [.DLdRes] ++ [LInstr])
          (h.pc + 1)))
  | .storeRl sz _ rs2 rs1 =>
      let a := h.rd rs1
      if !aligned a sz then .oos "misaligned" else
      .next (thenT E h (.st true a (toBytes (h.rd rs2) sz) (srcR rs1) (srcR rs2)) (fun _ h1 =>
        fixes E h1 [LInstr] (h.pc + 1)))
  | .loadAqPc .. => .oos "RCpc load (no v2 label)"
  | .storeRlPc .. => .oos "RCpc store (no v2 label)"
  | .lr sz aq _ rd rs1 =>
      let a := h.rd rs1
      if !aligned a sz then .oos "misaligned" else
      .next (thenT E h (.lr aq a sz (srcR rs1)) (fun s h1 =>
        fixes E (h1.wr rd (sext sz (ofBytes ((readsOf s.l).map Prod.snd)))) (regWL rd [.DLdRes] ++ [LInstr])
          (h.pc + 1)))
  | .sc sz _ rl rd rs2 rs1 =>
      let a := h.rd rs1
      if !aligned a sz then .oos "misaligned" else
      let ok := thenT E h (.sc rl a (toBytes (h.rd rs2) sz) (srcR rs1) (srcR rs2)) (fun _ h1 =>
        fixes E (h1.wr rd 0) (regWL rd [.DLdRes] ++ [LExFail, LInstr]) (h.pc + 1))
      let ko := fixes E (h.wr rd 1) ([LExFail] ++ regWL rd [] ++ [LExFail, LInstr]) (h.pc + 1)
      .next (ok ++ ko)
  | .amo op sz aq rl rd rs2 rs1 =>
      let a := h.rd rs1
      if !aligned a sz then .oos "misaligned" else
      let b := h.rd rs2 % 2 ^ (8 * sz)
      let f := fun (bs : List (BitVec 8)) => toBytes (amoOp op sz (ofBytes bs) b) sz
      .next (thenT E h (.rmw aq rl a sz f (srcR rs1) (srcR rs2)) (fun s h1 =>
        fixes E (h1.wr rd (sext sz (ofBytes ((readsOf s.l).map Prod.snd)))) (regWL rd [.DLdRes] ++ [LInstr])
          (h.pc + 1)))
  | .fence f => .next (fixes E h [LFence f.pr f.pw f.sr f.sw, LInstr] (h.pc + 1))
  | .fenceTso => .next (fixes E h [LFence true false true true, LFence false true false true, LInstr] (h.pc + 1))
  | .br c rs1 rs2 tgt =>
      if tgt ≤ h.pc ∨ n < tgt then .next [] else
      .next (fixes E h [LCtrl (srcR rs1 ++ srcR rs2), LInstr]
        (if brEval c (h.rd rs1) (h.rd rs2) then tgt else h.pc + 1))
  | .jmp tgt => if tgt ≤ h.pc ∨ n < tgt then .next [] else .next (fixes E h [LInstr] tgt)
  | .csrr rd v => .next (fixes E (h.wr rd v) (regWL rd [] ++ [LInstr]) (h.pc + 1))
  | .fencei => .next (fixes E h [LFenceI, LInstr] (h.pc + 1))
  | .nop => .next (fixes E h [LInstr] (h.pc + 1))

/-- The result of a hart's DFS: final states (with possibly outstanding promises) and the out-of-scope reasons met. -/
structure Res where
  fin : List MH
  oos : List String
  nodes : Nat

/-- All complete runs of a hart (forward-only programs: `fuel = |prog| + 1` suffices). -/
def runM (E : Env) (prog : List Instr) : Nat → MH → Res
  | 0, _ => ⟨[], ["fuel"], 1⟩
  | fuel + 1, h =>
    if h.pc = prog.length then ⟨[h], [], 1⟩ else
    match prog[h.pc]? with
    | none => ⟨[], [], 1⟩
    | some ins =>
      match stepM E prog.length h ins with
      | .oos why => ⟨[], [why], 1⟩
      | .next hs => hs.foldl (fun acc h' =>
          let r := runM E prog fuel h'
          ⟨acc.fin ++ r.fin, acc.oos ++ r.oos, acc.nodes + r.nodes⟩) ⟨[], [], 1⟩

/-- The initial hart state against `M`: registers from the test, `psInit`, every own message of `M` promised. -/
def mhInit (T : Test) (M : List PMsg) (i : Nat) : MH :=
  { pc := 0
    regs := (List.range 32).map (fun r => ((((T.regs0[i]?).getD []).lookup r).getD 0) % two64)
    ws := psInit
    prom := promsOf M i }

/-- Hart `i`'s complete runs against `M` that fulfil every promise (the hart's share of a valid run). -/
def hartRuns (T : Test) (M : List PMsg) (i : Nat) : Res :=
  let E : Env := ⟨testImg T, M, i⟩
  let r := runM E (T.prog i) ((T.prog i).length + 1) (mhInit T M i)
  { r with fin := r.fin.filter (fun h => promDone M h.prom) }

/-! ## 3. Free runs: the message lists a hart can produce over a value domain -/

/-- A value domain: per address, the bytes a load may return (default: the image byte). -/
abbrev Dom := List (Int × List (BitVec 8))

def domAt (img : Image) (d : Dom) (a : Int) : List (BitVec 8) :=
  match d.lookup a with
  | some bs => bs
  | none => (img a).toList

/-- All byte runs of `sz` bytes at `a` over the domain. -/
def domRuns (img : Image) (d : Dom) (a : Int) : Nat → List (List (BitVec 8))
  | 0 => [[]]
  | k + 1 => (domAt img d a).flatMap (fun b => (domRuns img d (a + 1) k).map (b :: ·))

/-- A free hart: pc, registers, its messages so far (program order). -/
structure FH where
  pc : Nat
  regs : List Nat
  msgs : List PMsg

def FH.rd (h : FH) (r : Nat) : Nat := if r = 0 then 0 else (h.regs[r]?).getD 0

def FH.wr (h : FH) (r v : Nat) : FH := if r = 0 then h else { h with regs := h.regs.set r (v % two64) }

/-- One instruction of a free hart (`none`: out of scope or stuck). -/
def stepF (img : Image) (d : Dom) (i n : Nat) (h : FH) : Instr → List FH
  | .alui op rd rs1 imm => [{ h.wr rd (aluOp op (h.rd rs1) imm) with pc := h.pc + 1 }]
  | .alu op rd rs1 rs2 => [{ h.wr rd (aluOp op (h.rd rs1) (h.rd rs2)) with pc := h.pc + 1 }]
  | .load sz sgn rd rs1 off =>
      let a := (h.rd rs1 + off) % two64
      if !aligned a sz then [] else
      (domRuns img d a sz).map (fun bs =>
        let raw := ofBytes bs
        { h.wr rd (if sgn then sext sz raw else raw) with pc := h.pc + 1 })
  | .store sz rs2 rs1 off =>
      let a := (h.rd rs1 + off) % two64
      if !aligned a sz then [] else
      [{ h with pc := h.pc + 1, msgs := h.msgs ++ [⟨a, toBytes (h.rd rs2) sz, some i, .plain⟩] }]
  | .loadAq sz _ rd rs1 =>
      let a := h.rd rs1
      if !aligned a sz then [] else
      (domRuns img d a sz).map (fun bs => { h.wr rd (sext sz (ofBytes bs)) with pc := h.pc + 1 })
  | .storeRl sz _ rs2 rs1 =>
      let a := h.rd rs1
      if !aligned a sz then [] else
      [{ h with pc := h.pc + 1, msgs := h.msgs ++ [⟨a, toBytes (h.rd rs2) sz, some i, .rel⟩] }]
  | .loadAqPc .. => []
  | .storeRlPc .. => []
  | .lr sz _ _ rd rs1 =>
      let a := h.rd rs1
      if !aligned a sz then [] else
      (domRuns img d a sz).map (fun bs => { h.wr rd (sext sz (ofBytes bs)) with pc := h.pc + 1 })
  | .sc sz _ _ rd rs2 rs1 =>
      let a := h.rd rs1
      if !aligned a sz then [] else
      let h0 := h.wr rd 0
      let h1 := h.wr rd 1
      [{ h0 with pc := h.pc + 1, msgs := h.msgs ++ [⟨a, toBytes (h.rd rs2) sz, some i, .excl⟩] },
       { h1 with pc := h.pc + 1 }]
  | .amo op sz _ _ rd rs2 rs1 =>
      let a := h.rd rs1
      if !aligned a sz then [] else
      let b := h.rd rs2 % 2 ^ (8 * sz)
      (domRuns img d a sz).map (fun bs =>
        let h1 := h.wr rd (sext sz (ofBytes bs))
        { h1 with pc := h.pc + 1, msgs := h.msgs ++ [⟨a, toBytes (amoOp op sz (ofBytes bs) b) sz, some i, .excl⟩] })
  | .fence _ | .fenceTso | .fencei | .nop => [{ h with pc := h.pc + 1 }]
  | .br c rs1 rs2 tgt =>
      if tgt ≤ h.pc ∨ n < tgt then [] else
      [{ h with pc := if brEval c (h.rd rs1) (h.rd rs2) then tgt else h.pc + 1 }]
  | .jmp tgt => if tgt ≤ h.pc ∨ n < tgt then [] else [{ h with pc := tgt }]
  | .csrr rd v => [{ h.wr rd v with pc := h.pc + 1 }]

/-- All message lists of a free hart's complete runs (with a leaf budget: `none` if exceeded). -/
def freeRun (img : Image) (d : Dom) (i : Nat) (prog : List Instr) (budget : Nat) : Nat → List FH → List (List PMsg) → Nat →
    Option (List (List PMsg))
  | _, [], acc, _ => some acc
  | 0, _, _, _ => none
  | fuel + 1, h :: rest, acc, cnt =>
    if budget < cnt then none else
    if h.pc = prog.length then
      freeRun img d i prog budget fuel rest (if acc.contains h.msgs then acc else acc ++ [h.msgs]) (cnt + 1)
    else
      match prog[h.pc]? with
      | none => freeRun img d i prog budget fuel rest acc (cnt + 1)
      | some ins => freeRun img d i prog budget fuel (stepF img d i prog.length h ins ++ rest) acc (cnt + 1)

/-- The message lists of hart `i` over the domain. -/
def sigmaH (T : Test) (d : Dom) (i : Nat) (budget : Nat) : Option (List (List PMsg)) :=
  let h0 : FH := { pc := 0, regs := (List.range 32).map (fun r => ((((T.regs0[i]?).getD []).lookup r).getD 0) % two64),
                   msgs := [] }
  freeRun (testImg T) d i (T.prog i) budget (budget + 1) [h0] [] 0

/-- Add a byte to the domain at `a` (keeping the image byte first). -/
def domAdd (img : Image) (d : Dom) (a : Int) (b : BitVec 8) : Dom :=
  match d.lookup a with
  | some bs => if bs.contains b then d else d.map (fun (x, l) => if x == a then (x, l ++ [b]) else (x, l))
  | none => d ++ [(a, (img a).toList ++ (if (img a) == some b then [] else [b]))]

/-- The domain of the image plus every byte of the given messages. -/
def domOf (img : Image) (msgs : List PMsg) : Dom :=
  msgs.foldl (fun d m => (List.range m.data.length).foldl (fun d (k : Nat) =>
    match m.data[k]? with
    | some b => domAdd img d (m.pa + (k : Int)) b
    | none => d) d) []

def domSize (d : Dom) : Nat := d.foldl (fun n e => n + e.2.length) 0

/-- Store-like instructions of the test (the iteration bound `K`). -/
def storeInstrs (T : Test) : Nat :=
  T.harts.foldl (fun acc p => acc + (p.filter (fun i => match i with
    | .store .. | .storeRl .. | .storeRlPc .. | .sc .. | .amo .. => true
    | _ => false)).length) 0

/-- THE CLOSURE: per hart, its possible message lists (`none`: a budget was exceeded), and the iterations used. -/
def sigmaAll (T : Test) (budget : Nat) : Option (List (List (List PMsg)) × Nat) :=
  let img := testImg T
  let K := storeInstrs T
  let rec go : Nat → Dom → Nat → Option (List (List (List PMsg)) × Nat)
    | 0, _, _ => none
    | fuel + 1, d, it =>
      match (List.range T.harts.length).mapM (fun i => sigmaH T d i budget) with
      | none => none
      | some sig =>
        let d' := domOf img (sig.flatMap (fun s => s.flatten))
        if domSize d' == domSize d || K ≤ it then some (sig, it + 1) else go fuel d' (it + 1)
  go (K + 2) [] 0

/-! ## 4. Candidate final memories -/

/-- Do two messages overlap? -/
def overlaps (m n : PMsg) : Bool :=
  decide (m.pa < n.pa + n.data.length) && decide (n.pa < m.pa + m.data.length)

/-- Every arrangement of the per-hart message lists in which each hart's overlapping messages keep program order. -/
def arrange : Nat → List (List PMsg) → List (List PMsg)
  | 0, _ => [[]]
  | fuel + 1, ls =>
    if ls.all (·.isEmpty) then [[]] else
    (List.range ls.length).flatMap (fun h =>
      let l := (ls[h]?).getD []
      (List.range l.length).flatMap (fun j =>
        match l[j]? with
        | none => []
        | some m =>
          -- available: no earlier own message overlaps it
          if (l.take j).any (overlaps m) then [] else
          (arrange fuel (ls.set h (l.eraseIdx j))).map (m :: ·)))

/-- A hashable key of a message list. -/
def msgsKey (M : List PMsg) : List (Int × List Nat × Nat × Nat) :=
  M.map (fun m => (m.pa, m.data.map BitVec.toNat, m.tid.getD 0,
    match m.cls with | .plain => 0 | .rel => 1 | .excl => 2 | .cmo _ _ => 3))

/-- Every choice of one message list per hart. -/
def choices : List (List (List PMsg)) → List (List (List PMsg))
  | [] => [[]]
  | s :: rest => s.flatMap (fun l => (choices rest).map (l :: ·))

/-! ## 5. Observables and outcomes -/

/-- An observable: a final register, or `sz` bytes of final memory at `a`. -/
inductive Key where
  | reg (h r : Nat)
  | mem (a sz : Nat)
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- The final value of `sz` bytes at `a` in `M` (latest covering message per byte, else the image). -/
def finalMem (img : Image) (M : List PMsg) (a sz : Nat) : Nat :=
  bytesVal ((List.range sz).map (fun (k : Nat) =>
    let x : Int := (a : Int) + (k : Int)
    match (M.filter (fun m => (m.byteAt x).isSome)).getLast? with
    | some m => ((m.byteAt x).map BitVec.toNat).getD 0
    | none => ((img x).map BitVec.toNat).getD 0))

/-- The registers of hart `h` among the observables. -/
def regsOf (obs : List Key) (h : Nat) : List Nat :=
  obs.filterMap (fun k => match k with | .reg h' r => if h' == h then some r else none | _ => none)

/-- The machine's outcomes for one `M`: per hart, the projected final registers (deduplicated); `none` if some hart
has no valid local run.  An outcome is the list of values of `obs` in order. -/
def outcomesM (T : Test) (obs : List Key) (M : List PMsg) (stat : Nat × List String) :
    Option (List (List Nat)) × Nat × List String :=
  let img := testImg T
  let rec harts : Nat → Nat × List String → Option (List (List (Nat × Nat × Nat))) × Nat × List String
    | 0, st => (some [[]], st)
    | k + 1, st =>
      let i := T.harts.length - (k + 1)
      let r := hartRuns T M i
      let st := (st.1 + r.nodes, st.2 ++ r.oos)
      if r.fin.isEmpty then (none, st) else
      let proj := (r.fin.map (fun mh => (regsOf obs i).map (fun rr => (i, rr, mh.rd rr)))).eraseDups
      match harts k st with
      | (none, st) => (none, st)
      | (some rest, st) => (some (proj.flatMap (fun p => rest.map (p ++ ·))), st)
  match harts T.harts.length stat with
  | (none, st) => (none, st)
  | (some rows, st) =>
    let outs := rows.map (fun row => obs.map (fun k => match k with
      | .reg h r => ((row.find? (fun e => e.1 == h && e.2.1 == r)).map (·.2.2)).getD 0
      | .mem a sz => finalMem img M a sz))
    (some outs, st)

/-- Evaluate the test's condition on an outcome (values of `obs`). -/
def condOn (obs : List Key) (o : List Nat) : Ref.OC → Bool
  | .tt => true
  | .reg h r v => ((obs.zip o).lookup (.reg h r)).map (· == v % two64) |>.getD false
  | .mem a sz v => ((obs.zip o).lookup (.mem a sz)).map (· == v % 2 ^ (8 * sz)) |>.getD false
  | .and p q => condOn obs o p && condOn obs o q
  | .or p q => condOn obs o p || condOn obs o q
  | .not p => !condOn obs o p

/-- The observables a condition mentions. -/
def condKeys : Ref.OC → List Key
  | .tt => []
  | .reg h r _ => [.reg h r]
  | .mem a sz _ => [.mem a sz]
  | .and p q => condKeys p ++ condKeys q
  | .or p q => condKeys p ++ condKeys q
  | .not p => condKeys p

end Weak.Prom.Mach
