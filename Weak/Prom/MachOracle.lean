/-
Weak/Prom: **the machine-v2 oracle run** (S0-P part (2), milestone 1): machine v2 (label level, `MachLitmus.lean`)
over `litmus-tests-riscv`, compared OUTCOME SET BY OUTCOME SET with the reference `rvwmoRef` (RefCheck's enumerator,
collecting every consistent candidate's outcome) and with a herd log's `States`.  Run as a program:

  `lake env lean --run Weak/Prom/MachOracle.lean <repo> <herd.logs> <cap> <shard> <shards> [noref]`

`<repo>` holds `tests/non-mixed-size`; the files are sorted and file `k` is run iff `k % shards = shard`, so the
corpus is split over parallel processes.  Observables of a test: herd's state keys (`[x]`, `P:xN`) and the
condition's.  Per test one line:
`T <file> <name> | M=<cands> V=<valid M> | m=<#> r=<#> h=<#> | MR=<cmp> MH=<cmp> | vd m/r/h | <ms>`
with `<cmp>` ∈ `eq`, `STRONGER` (machine lacks an outcome of the other side), `WEAKER` (machine has an extra one),
`BOTH`, `na`; a disagreement is followed by `  only-mach:` / `  only-ref:` / `  only-herd:` lines.
-/
import Weak.Prom.MachLitmus
import Weak.Prom.LitmusParse
import Std.Data.HashSet

namespace Weak.Prom.Mach.Oracle

open Weak.Prom Weak.Prom.Mach
open Weak.Prom.Ref Weak.Prom.Ref.Parse

/-! ## 1. Parsing (RefProg's parser, keeping the location table) -/

/-- `parseLitmus`, also returning the location table (same code path). -/
def parseLitmusPS (src : String) : Except String (LTest × PS) := do
  let s := stripComments src.toList
  let ls := (lines s).map trimL
  let hdr := (ls.find? (fun l => !l.isEmpty)).getD []
  let name ← match splitWords hdr with
    | [arch, n] => if arch == "RISCV".toList then pure (String.ofList n) else throw "not RISCV"
    | _ => throw "bad header"
  let body := s.dropWhile (· != '{')
  if body.isEmpty then throw "no init block"
  let initTxt := (body.drop 1).takeWhile (· != '}')
  let after := (body.drop 1).dropWhile (· != '}') |>.drop 1
  let items := (splitOnC ';' (initTxt.map (fun c => if c == '\n' then ';' else c))).map trimL
  let (ps, ini) ← items.foldlM (fun (acc : PS × Init) it => initItem acc.1 acc.2 it) ({}, {})
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
  pure ({ name := name, quant := quant, test := ⟨harts, regs0, img, [], cond⟩ }, ps)

/-! ## 2. herd logs -/

/-- One herd block: the state lines (as `key=value` pairs) and the observation verdict. -/
structure HBlock where
  states : List (List (String × String))
  obs : String

def splitStr (s : String) (c : Char) : List String := (s.splitOn c.toString)

def trimS (s : String) : String := String.ofList (trimL s.toList)

/-- Parse a state line `k=v; k=v;`. -/
def stateLine (l : String) : List (String × String) :=
  (splitStr l ';').filterMap (fun kv =>
    match splitStr (trimS kv) '=' with
    | [k, v] => some (trimS k, trimS v)
    | _ => none)

/-- All blocks of a herd log, by test name, in log order (herd's logs concatenate per-file logs in `LC_ALL=C`
sorted path order, the order of `walk` + `mergeSort` here, so the `k`-th file of a name gets the `k`-th block). -/
partial def herdBlocks (ls : List String) (acc : Std.HashMap String (Array HBlock)) :
    Std.HashMap String (Array HBlock) :=
  match ls with
  | [] => acc
  | l :: rest =>
    match splitStr l ' ' with
    | "Test" :: name :: _ =>
      -- read the States block and the Observation line
      let rec go (rs : List String) (st : List (List (String × String))) (inStates : Bool) :
          List (List (String × String)) × String × List String :=
        match rs with
        | [] => (st, "unknown", [])
        | r :: rs' =>
          if r.startsWith "Test " then (st, "unknown", rs)
          else if r.startsWith "States " then go rs' st true
          else if r == "Ok" || r == "No" || r.startsWith "Witnesses" || r.startsWith "Positive" ||
              r.startsWith "Condition" then go rs' st false
          else if r.startsWith "Observation " then
            (st, ((splitStr r ' ').getD 2 "unknown"), rs')
          else if inStates then go rs' (st ++ [stateLine r]) true
          else go rs' st false
      let (st, ob, rest') := go rest [] false
      herdBlocks rest' (acc.insert name (((acc.get? name).getD #[]).push ⟨st, ob⟩))
    | _ => herdBlocks rest acc

/-- Decimal (possibly negative) value modulo `2^bits`. -/
def parseVal (s : String) (bits : Nat) : Option Nat :=
  let l := s.toList
  match l with
  | '-' :: t => (parseNatL 10 t).map (fun n => (2 ^ bits - n % 2 ^ bits) % 2 ^ bits)
  | '0' :: 'x' :: t => (parseNatL 16 t).map (· % 2 ^ bits)
  | _ => (parseNatL 10 l).map (· % 2 ^ bits)

/-- A herd key as an observable. -/
def keyOf (ps : PS) (k : String) : Option Key :=
  if k.startsWith "[" && k.endsWith "]" then
    let n := (k.toList.drop 1).dropLast
    match ps.locs.find? (fun l => l.1 == n) with
    | some l => some (.mem l.2.1 l.2.2)
    | none =>
      match fixedLocs.find? (fun l => l.1 == n) with
      | some l => some (.mem l.2 4)
      | none => none
  else
    match splitStr k ':' with
    | [p, r] => match p.toNat?, parseReg r.toList with
      | some h, some rr => some (.reg h rr)
      | _, _ => none
    | _ => none

/-! ## 3. Canonical observables, outcome sets -/

def keyLt : Key → Key → Bool
  | .reg h r, .reg h' r' => h < h' || (h == h' && r < r')
  | .reg .., .mem .. => true
  | .mem .., .reg .. => false
  | .mem a _, .mem a' _ => a < a'

def canon (ks : List Key) : List Key := (ks.eraseDups).mergeSort (fun a b => keyLt a b || a == b)

def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLe as bs)

def sortOuts (l : List (List Nat)) : List (List Nat) := l.eraseDups.mergeSort lexLe

def showOut (obs : List Key) (o : List Nat) : String :=
  String.intercalate " " ((obs.zip o).map (fun (k, v) => match k with
    | .reg h r => s!"{h}:x{r}={v}"
    | .mem a _ => s!"[{a}]={v}"))

/-- herd's verdict on the condition body from an outcome set. -/
def vdOf (obs : List Key) (c : OC) (outs : List (List Nat)) : String :=
  if outs.isEmpty then "EMPTY" else
  let p := outs.filter (fun o => condOn obs o c)
  if p.isEmpty then "Never" else if p.length == outs.length then "Always" else "Sometimes"

/-! ## 4. The reference's outcome set (RefCheck's enumerator, every consistent candidate) -/

def refOutcomes (T : Test) (obs : List Key) : List (List Nat) × Bool :=
  let ps := T.paths
  let ok := ps.all (fun p => varsOkB p.2)
  let outs := ps.flatMap (fun p => (candsOf p.2).filterMap (fun g =>
    let ν := lk (passVals T.imgF p.2 g)
    let X := conc T p.2 ν g
    if condsOk ν p.2 && refCoreB X then
      some (obs.map (fun k => match k with
        | .reg h r => finalReg p.2 ν h r
        | .mem a sz => bytesVal ((List.range sz).map (fun j => finalByte X (a + j)))))
    else none))
  (sortOuts outs, ok)

/-! ## 5. The machine's outcome set -/

structure MStat where
  cands : Nat := 0
  valid : Nat := 0
  nodes : Nat := 0
  oos : List String := []
  iters : Nat := 0
  budget : Bool := false

def machOutcomes (T : Test) (obs : List Key) (budget : Nat) (mcap : Nat) : List (List Nat) × MStat := Id.run do
  match sigmaAll T budget with
  | none => return ([], { budget := true })
  | some (sig, it) =>
    let mut seen : Std.HashSet (List (Int × List Nat × Nat × Nat)) := {}
    let mut outs : Std.HashSet (List Nat) := {}
    let mut st : MStat := { iters := it }
    for ch in choices sig do
      let n := ch.foldl (fun a l => a + l.length) 0
      for M in arrange (n + 1) ch do
        let key := msgsKey M
        if seen.contains key then continue
        seen := seen.insert key
        st := { st with cands := st.cands + 1 }
        if mcap < st.cands then return ([], { st with budget := true })
        let (r, (nd, oo)) := outcomesM T obs M (0, [])
        st := { st with nodes := st.nodes + nd, oos := (st.oos ++ oo).eraseDups }
        match r with
        | none => pure ()
        | some os =>
          st := { st with valid := st.valid + 1 }
          for o in os do outs := outs.insert o
    return (sortOuts outs.toList, st)

/-! ## 6. The driver -/

partial def walk (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← walk e.path)
    else if e.path.extension == some "litmus" then out := out ++ [e.path]
  return out

def memInstrs (T : Test) : Nat :=
  T.harts.foldl (fun acc p => acc + (p.filter (fun i => match i with
    | .load .. | .store .. | .loadAq .. | .storeRl .. | .loadAqPc .. | .storeRlPc .. | .lr .. | .sc .. | .amo .. =>
      true
    | _ => false)).length) 0

def cmpSets (m o : List (List Nat)) : String × List (List Nat) × List (List Nat) :=
  let onlyM := m.filter (fun x => !o.contains x)
  let onlyO := o.filter (fun x => !m.contains x)
  (if onlyM.isEmpty && onlyO.isEmpty then "eq" else if onlyM.isEmpty then "STRONGER"
   else if onlyO.isEmpty then "WEAKER" else "BOTH", onlyM, onlyO)

def main (args : List String) : IO UInt32 := do
  let repo : System.FilePath := args.getD 0 "."
  let herdPath : System.FilePath := args.getD 1 "herd.logs"
  let cap := (args.getD 2 "8").toNat!
  let shard := (args.getD 3 "0").toNat!
  let shards := (args.getD 4 "1").toNat!
  let noref := args.getD 5 "" == "noref"
  let budget := 200000
  let mcap := 200000
  let logs ← IO.FS.readFile herdPath
  let hb := herdBlocks (logs.splitOn "\n") {}
  IO.println s!"herd blocks: {hb.size}; shard {shard}/{shards}; cap {cap}; ref {!noref}"
  let files ← walk (repo / "tests" / "non-mixed-size")
  let files := files.mergeSort (fun a b => a.toString ≤ b.toString)
  -- occurrence index of each file among the files with the same test name (all files are parsed)
  let mut occ : Std.HashMap String Nat := {}
  let mut occOf : Std.HashMap String Nat := {}
  for f in files do
    match parseLitmusPS (← IO.FS.readFile f) with
    | .ok (lt, _) =>
      let k := (occ.get? lt.name).getD 0
      occ := occ.insert lt.name (k + 1)
      occOf := occOf.insert f.toString k
    | .error _ => pure ()
  let mut idx := 0
  for f in files do
    idx := idx + 1
    if (idx - 1) % shards != shard then continue
    let src ← IO.FS.readFile f
    match parseLitmusPS src with
    | .error e => IO.println s!"SCOPE parse {f}: {e}"
    | .ok (lt, ps) =>
      let T := lt.test
      if memInstrs T > cap then
        IO.println s!"SCOPE budget {f}: {memInstrs T} memory instructions > {cap}"
        continue
      let hbl := (hb.get? lt.name).bind (fun a => a[(occOf.get? f.toString).getD 0]?)
      let hkeys : List Key := match hbl with
        | some b => ((b.states.headD []).map (·.1)).filterMap (keyOf ps)
        | none => []
      let obs := canon (hkeys ++ condKeys T.cond)
      let t0 ← IO.monoMsNow
      let (mo, st) := machOutcomes T obs budget mcap
      let t1 ← IO.monoMsNow
      let (ro, rok) := if noref then ([], true) else refOutcomes T obs
      let t2 ← IO.monoMsNow
      let ho : Option (List (List Nat)) := hbl.bind (fun b =>
        let rows := b.states.map (fun row => obs.mapM (fun k =>
          (row.find? (fun kv => keyOf ps kv.1 == some k)).bind (fun kv =>
            parseVal kv.2 (match k with | .reg .. => 64 | .mem _ sz => 8 * sz))))
        if rows.all Option.isSome then some (sortOuts (rows.filterMap id)) else none)
      if st.budget then
        IO.println s!"SCOPE explorer-budget {f} ({lt.name}): cands {st.cands}"
        continue
      let (mr, onlyMR, onlyRM) := if noref then ("na", [], []) else cmpSets mo ro
      let (mh, onlyMH, onlyHM) := match ho with
        | some h => cmpSets mo h
        | none => ("na", [], [])
      let hv := (hbl.map (·.obs)).getD "none"
      let flags := (if st.oos.isEmpty then "" else s!" oos={st.oos}") ++ (if rok then "" else " ref-varsOk-FAIL")
      IO.println s!"T {f} {lt.name} | M={st.cands} V={st.valid} it={st.iters} nodes={st.nodes} | m={mo.length} r={ro.length} h={(ho.map List.length).getD 0} | MR={mr} MH={mh} | vd {vdOf obs T.cond mo}/{if noref then "na" else vdOf obs T.cond ro}/{hv} | {t1 - t0}ms {t2 - t1}ms{flags}"
      if !onlyMR.isEmpty then IO.println s!"  only-mach(vs ref): {onlyMR.map (showOut obs)}"
      if !onlyRM.isEmpty then IO.println s!"  only-ref: {onlyRM.map (showOut obs)}"
      if !onlyMH.isEmpty then IO.println s!"  only-mach(vs herd): {onlyMH.map (showOut obs)}"
      if !onlyHM.isEmpty then IO.println s!"  only-herd: {onlyHM.map (showOut obs)}"
  return 0

end Weak.Prom.Mach.Oracle

def main (args : List String) : IO UInt32 := Weak.Prom.Mach.Oracle.main args
