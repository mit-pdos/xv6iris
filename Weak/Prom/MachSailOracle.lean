/-
Weak/Prom: **the Sail-level oracle run** (S0-P part (2), milestone 3): every litmus test through the Sail model +
emission v2 + machine v2 (`MachSail.lean`), compared outcome set by outcome set with machine v2 at label level
(`MachLitmus.lean`), the reference (RefCheck's enumerator) and herd.  Run as a program:

  `lake env lean --run Weak/Prom/MachSailOracle.lean <repo> <herd.logs> <cap> <shard> <shards> [noref] [only=<substr>]`

Per test one line
`S <file> <name> | P=<platforms> M=<cands> V=<valid M> it=<closure iterations> ev=<Sail events> | s=<#> m=<#> r=<#>
h=<#> | SM=<cmp> SR=<cmp> SH=<cmp> | vd s/m/r/h | <ms sail> <ms mach> <ms ref>` (`s` Sail level, `m` label level,
`r` reference, `h` herd; `<cmp>` as MachOracle: `STRONGER` = the Sail level lacks an outcome of the other side,
`WEAKER` = it has an extra one), then `only-…` lines on a disagreement.  `SCOPE-SAIL <why>` when the test cannot go
through Sail (assembly) or a Sail run stopped (`oos=`); the label-level verdict is still printed then.
MachFix-havoc: `HAVOC <file> …` with Sail-level verdict `HAVOC` when a valid run reaches a Sail `.error` node
(MachHavoc.lean: every observation is possible; a forbidden verdict is blocked).
The parsing, herd, reference and label-level code is MachOracle.lean's (copied: that file defines `main`).
-/
import Weak.Prom.MachSail
import Weak.Prom.LitmusParse
import Std.Data.HashSet

namespace Weak.Prom.SailLit.Oracle

open Weak.Prom Weak.Prom.Mach Weak.Prom.SailLit
open Weak.Prom.Ref Weak.Prom.Ref.Parse

/-! ## 1. MachOracle.lean's parsing / herd / reference / label level (verbatim) -/

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

structure HBlock where
  states : List (List (String × String))
  obs : String

def splitStr (s : String) (c : Char) : List String := (s.splitOn c.toString)

def trimS (s : String) : String := String.ofList (trimL s.toList)

def stateLine (l : String) : List (String × String) :=
  (splitStr l ';').filterMap (fun kv =>
    match splitStr (trimS kv) '=' with
    | [k, v] => some (trimS k, trimS v)
    | _ => none)

partial def herdBlocks (ls : List String) (acc : Std.HashMap String (Array HBlock)) :
    Std.HashMap String (Array HBlock) :=
  match ls with
  | [] => acc
  | l :: rest =>
    match splitStr l ' ' with
    | "Test" :: name :: _ =>
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

def parseVal (s : String) (bits : Nat) : Option Nat :=
  let l := s.toList
  match l with
  | '-' :: t => (parseNatL 10 t).map (fun n => (2 ^ bits - n % 2 ^ bits) % 2 ^ bits)
  | '0' :: 'x' :: t => (parseNatL 16 t).map (· % 2 ^ bits)
  | _ => (parseNatL 10 l).map (· % 2 ^ bits)

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

def keyLt : Key → Key → Bool
  | .reg h r, .reg h' r' => h < h' || (h == h' && r < r')
  | .reg .., .mem .. => true
  | .mem .., .reg .. => false
  | .mem a _, .mem a' _ => a < a'

def canon (ks : List Key) : List Key := (ks.eraseDups).mergeSort (fun a b => keyLt a b || a == b)

def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: xs, b :: ys => a < b || (a == b && lexLe xs ys)

def sortOuts (l : List (List Nat)) : List (List Nat) := l.eraseDups.mergeSort lexLe

def showOut (obs : List Key) (o : List Nat) : String :=
  String.intercalate " " ((obs.zip o).map (fun (k, v) => match k with
    | .reg h r => s!"{h}:x{r}={v}"
    | .mem a _ => s!"[{a}]={v}"))

def vdOf (obs : List Key) (c : OC) (outs : List (List Nat)) : String :=
  if outs.isEmpty then "EMPTY" else
  let p := outs.filter (fun o => condOn obs o c)
  if p.isEmpty then "Never" else if p.length == outs.length then "Always" else "Sometimes"

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

def machOutcomes (T : Test) (obs : List Key) (budget : Nat) (mcap : Nat) : List (List Nat) × Bool := Id.run do
  match sigmaAll T budget with
  | none => return ([], true)
  | some (sig, _) =>
    let mut seen : Std.HashSet (List (Int × List Nat × Nat × Nat)) := {}
    let mut outs : Std.HashSet (List Nat) := {}
    let mut cands := 0
    for ch in choices sig do
      let n := ch.foldl (fun a l => a + l.length) 0
      for M in arrange (n + 1) ch do
        let key := msgsKey M
        if seen.contains key then continue
        seen := seen.insert key
        cands := cands + 1
        if mcap < cands then return ([], true)
        let (r, _) := outcomesM T obs M (0, [])
        match r with
        | none => pure ()
        | some os => for o in os do outs := outs.insert o
    return (sortOuts outs.toList, false)

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

/-! ## 2. The driver -/

def main (args : List String) : IO UInt32 := do
  let repo : System.FilePath := args.getD 0 "."
  let herdPath : System.FilePath := args.getD 1 "herd.logs"
  let cap := (args.getD 2 "8").toNat!
  let shard := (args.getD 3 "0").toNat!
  let shards := (args.getD 4 "1").toNat!
  let rest := args.drop 5
  let noref := rest.contains "noref"
  let only := (rest.find? (·.startsWith "only=")).map (fun s => (s.drop 5).toString)
  let budget := 200000
  let mcap := 200000
  let logs ← IO.FS.readFile herdPath
  let hb := herdBlocks (logs.splitOn "\n") {}
  let boot : Array Vtest.XRegs := ((List.range 8).map bootX).toArray
  let bootF := fun (h : Nat) => boot[h]?.getD (bootX h)
  IO.println s!"herd blocks: {hb.size}; shard {shard}/{shards}; cap {cap}; ref {!noref}"
  let files ← walk (repo / "tests" / "non-mixed-size")
  let files := files.mergeSort (fun a b => a.toString ≤ b.toString)
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
    if let some o := only then
      if !((f.toString.splitOn o).length > 1) then continue
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
      let locs := ps.locs.map (·.2.1)
      let t0 ← IO.monoMsNow
      let (mo, mbud) := machOutcomes T obs budget mcap
      let t1 ← IO.monoMsNow
      let ho : Option (List (List Nat)) := hbl.bind (fun b =>
        let rows := b.states.map (fun row => obs.mapM (fun k =>
          (row.find? (fun kv => keyOf ps kv.1 == some k)).bind (fun kv =>
            parseVal kv.2 (match k with | .reg .. => 64 | .mem _ sz => 8 * sz))))
        if rows.all Option.isSome then some (sortOuts (rows.filterMap id)) else none)
      let hv := (hbl.map (·.obs)).getD "none"
      match prepare T locs bootF with
      | .error why =>
        IO.println s!"SCOPE-SAIL asm {f} ({lt.name}): {why} | vd m {vdOf obs T.cond mo}"
      | .ok S =>
        let (so?, st) := sailOutcomes S obs budget mcap
        let t2 ← IO.monoMsNow
        match so? with
        | none =>
          IO.println s!"SCOPE-SAIL budget {f} ({lt.name}): cands {st.cands} ev {st.events} | vd m {vdOf obs T.cond mo}"
        | some so0 =>
          let so := sortOuts so0
          let (ro, rok) := if noref then ([], true) else refOutcomes T obs
          let t3 ← IO.monoMsNow
          let (sm, onlySM, onlyMS) := cmpSets so mo
          let (sr, onlySR, onlyRS) := if noref then ("na", [], []) else cmpSets so ro
          let (sh, onlySH, onlyHS) := match ho with
            | some h => cmpSets so h
            | none => ("na", [], [])
          let flags := (if st.oos.isEmpty then "" else s!" oos={st.oos}") ++
            (if st.miss == 0 then "" else s!" MISS={st.miss}") ++ (if st.platDiff then " platDiff" else "") ++
            (if rok then "" else " ref-varsOk-FAIL") ++ (if mbud then " mach-budget" else "")
          -- MachFix-havoc: a havoc run (a valid run reaching a Sail `.error` node) makes every outcome possible: tag
          -- `HAVOC`, Sail-level verdict `HAVOC` (never forbidden; MachHavoc.lean `allowedH`)
          let tag := if st.havoc then "HAVOC" else if st.oos.isEmpty then "S" else "SCOPE-SAIL oos"
          let vds := if st.havoc then "HAVOC" else vdOf obs T.cond so
          IO.println s!"{tag} {f} {lt.name} | P={st.plats} M={st.cands} V={st.valid} it={st.iters} ev={st.events} nodes={st.nodes} | s={so.length} m={mo.length} r={ro.length} h={(ho.map List.length).getD 0} | SM={sm} SR={sr} SH={sh} | vd {vds}/{vdOf obs T.cond mo}/{if noref then "na" else vdOf obs T.cond ro}/{hv} | {t2 - t1}ms {t1 - t0}ms {t3 - t2}ms{flags}"
          if !onlySM.isEmpty then IO.println s!"  only-sail(vs mach): {onlySM.map (showOut obs)}"
          if !onlyMS.isEmpty then IO.println s!"  only-mach: {onlyMS.map (showOut obs)}"
          if !onlySR.isEmpty then IO.println s!"  only-sail(vs ref): {onlySR.map (showOut obs)}"
          if !onlyRS.isEmpty then IO.println s!"  only-ref: {onlyRS.map (showOut obs)}"
          if !onlySH.isEmpty then IO.println s!"  only-sail(vs herd): {onlySH.map (showOut obs)}"
          if !onlyHS.isEmpty then IO.println s!"  only-herd: {onlyHS.map (showOut obs)}"
  return 0

end Weak.Prom.SailLit.Oracle

def main (args : List String) : IO UInt32 := Weak.Prom.SailLit.Oracle.main args
