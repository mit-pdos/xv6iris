/-
Weak/Prom: **probe family G2** (S0-P part (4); plan rev 7 §1A "(G2) per decoder class with a destination",
Appendix B): for every decoder class of `DecoderTable.classes` that runs to completion in M-mode (its observation in
`DecoderObs` has no stop) and has a GPR destination, the chain

  H0 `ld a0,(x); xor s,a0,a0; ⟨taint⟩; ⟨insn⟩; xor t,d,d; ori t,t,1; sd t,(y)` ‖ H1 `ld b,(y); xor u,b,b;
  ori u,u,1; sd u,(x)`

through the REAL Sail model and emission v2 (`MachSail.sailOutcomes`), in two variants:
* CARRY: every GPR source of `insn` is tainted first (`add r, r, s`, `s = 0` carrying the load's dependency);
* KILL: the destination `d` is tainted first, the sources are not;
plus, per CSR of the table, the CSR CHAIN `csrrw x0,csr,s; csrrs d,csr,x0` (the dependency through the CSR).
The TEXT VERDICT of the LB outcome (`a0 = b = 1`) is computed from the class's EXPECTED roles (`Cls.exp`, the
listing): a chain to the final store exists iff `d` is a destination carrying a tainted source, or receiving the
memory result of an access with a tainted address/data source, or `d` is not a destination (kept) and was tainted.
Chain ⇒ FORBIDDEN, else ALLOWED.  The machine's verdict is the Sail-level outcome set's.  A disagreement is
STRONGER (machine forbids what the text allows: a stale view, SR-19/SR-20's class) or WEAKER.

Out of the Sail-level scope (`MachSail.sNext` stops): `amocas`, Zicbom/Zicboz (`cbo`), a write of `mcause`/`scause`
(the trap heuristic), every trapping class; branches/jumps other than `jal` (control flow).

Run: `lake env lean --run Weak/Prom/ProbeG2.lean <shard> <shards>`.
-/
import Weak.Prom.MachSail
import Weak.Prom.DecoderCheck

namespace Weak.Prom.Probe.G2

open MachCSL Sail LeanRV64D
open Weak.Prom Weak.Prom.Mach Weak.Prom.Dec Weak.Prom.SailLit
open Weak.Prom.Ref (Test)

def X : Nat := 0x1000
def Y : Nat := 0x2000
def Z : Nat := 0x3000

-- harness registers (disjoint from every class register: x1, x2, x5–x7, x9–x13)
def rA : Nat := 20   -- the load result
def rS : Nat := 21   -- the taint (0, carrying the load's dependency)
def rV : Nat := 22   -- the stored value
def rXb : Nat := 23
def rYb : Nat := 24

def ldW (rd rs1 : Nat) : Nat := iT 0 rs1 3 rd 0x03
def sdW (rs2 rs1 : Nat) : Nat := sT 0 rs2 rs1 3 0x23
def xorW (rd a b : Nat) : Nat := rT 0 b a 4 rd 0x33
def oriW (rd a imm : Nat) : Nat := iT imm a 6 rd 0x13
def addW (rd a b : Nat) : Nat := rT 0 b a 0 rd 0x33
def nopW : Nat := 0x13
def lrW (rd rs1 : Nat) : Nat := amoW 2 0 0 0 rs1 2 rd

/-- The class word as one 32-bit image word (a compressed parcel is followed by `c.nop`). -/
def wordOf (c : Cls) : Nat := if c.w < 0x10000 && c.w % 4 != 3 then c.w ||| (0x0001 <<< 16) else c.w

def gprs (l : List R) : List Nat := l.filterMap (fun r => match r with | .g n => some n | _ => none)

/-- The GPR sources of a class. -/
def srcsOf (s : Spec) : List Nat :=
  (gprs (s.asrc ++ s.dsrc ++ s.ctrl ++ s.dests.flatMap (fun d => d.2.1))).eraseDups

/-- The text's chain to the store of `d`, given the tainted registers; `rel`: the class's memory operation has a
release annotation (rule 6 orders the harness's first load before it, rvwmo.adoc:288). -/
def chain (s : Spec) (d : Nat) (tainted : List Nat) (rel : Bool) : Bool :=
  let tl := tainted.map R.g
  match s.dests.find? (·.1 == .g d) with
  | some (_, carried, mem) =>
    carried.any (tl.contains ·) || (mem && ((s.asrc ++ s.dsrc).any (tl.contains ·) || rel))
  | none => tainted.contains d

structure G2 where
  name : String
  code : List Nat      -- H0's words
  verdictAllowed : Bool
  extraObs : List Key := []
  extraCond : List (Nat × Nat) := []   -- H0 register = value, conjoined with the LB outcome

/-- H0 around an instruction block `mid` whose result register is `d`. -/
def h0 (taint : List Nat) (mid : List Nat) (d : Nat) : List Nat :=
  [ldW rA rXb, xorW rS rA rA] ++ taint.map (fun r => addW r r rS) ++ mid ++ [xorW rV d d, oriW rV rV 1, sdW rV rYb]

def h1 : List Nat := [ldW rA rYb, xorW rS rA rA, oriW rS rS 1, sdW rS rXb]

/-- The G2 probes of one class. -/
def ofClass (c : Cls) (o : Dec.Obs) : List G2 :=
  if o.stop != "" || c.trap then [] else
  if c.name.startsWith "amocas" || c.name.startsWith "cbo" || c.mode == .brT || c.mode == .brN then [] else
  if o.writes.contains "mcause" || o.writes.contains "scause" then [] else
  if c.name == "jalr" || c.name == "c.jr" || c.name == "c.jalr" || c.name == "c.j" then [] else
  let s := c.exp
  let dests := (gprs (s.dests.map (·.1) ++ s.kept)).eraseDups
  let srcs := srcsOf s
  let isSC := c.mode == .scOk || c.mode == .scFailP || c.mode == .scFailM
  -- AMO and SC release annotations (rvwmo.adoc:124-128: rl on an AMO or SC)
  -- and an LR with both bits ("An AMO, lr, or sc instruction with both aq and rl set has both acquire-RCsc and
  -- release-RCsc annotations"; `lr.rl` alone carries nothing)
  let rel := ((c.row == "C-D-11" || c.row == "C-D-12") && (c.name.endsWith ".rl" || c.name.endsWith ".aqrl" ||
    (c.name.splitOn ".rl-").length > 1 || (c.name.splitOn ".aqrl-").length > 1)) ||
    (c.row == "C-D-10" && c.name.endsWith ".aqrl")
  -- an SC is preceded by its LR (on the SC's address register x6); a jal skips one word
  let pre : List Nat := if isSC then [lrW 14 6] else []
  let post : List Nat := if c.name == "jal" then [nopW] else []
  let mid := pre ++ [wordOf c] ++ post
  let scCond : List (Nat × Nat) := match c.mode with
    | .scOk => [(5, 0)] | .scFailP | .scFailM => [(5, 1)] | _ => []
  let extraObs : List Key := if isSC then [.reg 0 5] else []
  dests.flatMap (fun d =>
    (if srcs.isEmpty then [] else
      [⟨s!"{c.name}:carry:x{d}", h0 srcs mid d, !chain s d srcs rel, extraObs, scCond⟩]) ++
    [⟨s!"{c.name}:kill:x{d}", h0 [d] mid d, !chain s d [d] rel, extraObs, scCond⟩])

/-- The CSR chains (table and outside-table CSRs whose writes complete). -/
def csrChains : List G2 :=
  (csrsTable ++ csrsOther).filterMap (fun (csr, n) =>
    if csrRO csr || [0x342, 0x142, 0x001, 0x002, 0x003].contains csr then none else
    -- csrrw x0,csr,s ; csrrs x5,csr,x0
    some ⟨s!"csrchain:{n}", h0 [] [csrW csr rS 1 0, csrW csr 0 2 5] 5, false, [], []⟩)

def probes : List G2 :=
  (rows.flatMap (fun r => ofClass r.1 r.2.1)) ++ csrChains

/-- The STest of a G2 probe: two harts at `codeBase`, registers relocated by hand (location windows at `OFF + a`):
every class register `x1`–`x15` points into `z` (CSR classes: `x6 = 0`, a harmless CSR value), the harness bases
`x23 = x`, `x24 = y`. -/
def stest (g : G2) (csrClass : Bool) : STest :=
  let code := [(codeBase 0, g.code), (codeBase 1, h1)]
  let dummy : Test := ⟨[List.replicate 3 (.store 8 0 0 0), List.replicate 1 (.store 8 0 0 0)], [[], []], [], [], .tt⟩
  let img := mkImg dummy code
  let regs0 : List (Nat × Nat) :=
    ((List.range 15).map (fun k => (k + 1, OFF + Z + 0x40 * (k + 1)))) ++ [(rXb, OFF + X), (rYb, OFF + Y)] ++
    (if csrClass then [(6, 0)] else [])
  let mk (h : Nat) (ws : List Nat) : SH × BitVec 64 × Nat :=
    let x0 := (bootX h).insert .PC (BitVec.ofNat 64 (codeBase h))
    let x := regs0.foldl (fun x (r, v) => setGpr x r (BitVec.ofNat 64 v)) x0
    (⟨.pure (), x, none, ixNone⟩, BitVec.ofNat 64 (codeBase h + 4 * ws.length), ws.length + 4)
  ⟨dummy, [X, Y, Z], img, [mk 0 g.code, mk 1 h1]⟩

def main (args : List String) : IO UInt32 := do
  let shard := (args.getD 0 "0").toNat!
  let shards := (args.getD 1 "1").toNat!
  IO.println s!"G2: {probes.length} probes; shard {shard}/{shards}"
  let mut idx := 0
  for g in probes do
    idx := idx + 1
    if (idx - 1) % shards != shard then continue
    let csrClass := g.name.startsWith "csr"
    let S := stest g csrClass
    let obs : List Key := [.reg 0 rA, .reg 1 rA] ++ g.extraObs
    let t0 ← IO.monoMsNow
    let (r, st) := sailOutcomes S obs 200000 200000
    let t1 ← IO.monoMsNow
    match r with
    | none => IO.println s!"G {g.name} | budget"
    | some os =>
      let hit := os.any (fun o => o.headD 0 == 1 && (o.getD 1 0) == 1 &&
        g.extraCond.all (fun (_, v) => o.getD 2 0 == v))
      let mv := if hit then "A" else "F"
      let tv := if g.verdictAllowed then "A" else "F"
      let cmp := if mv == tv then "eq" else if tv == "A" then "STRONGER" else "WEAKER"
      IO.println s!"G {g.name} | text={tv} mach={mv} | {cmp} | outs={os.eraseDups.length} oos={st.oos} miss={st.miss} | {t1 - t0}ms"
  return 0

end Weak.Prom.Probe.G2

def main (args : List String) : IO UInt32 := Weak.Prom.Probe.G2.main args
