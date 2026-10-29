/-
Weak/Prom: **the oracle run** (S0-P part (5)): the reference checker core against `litmus-tests-riscv`'s herd
results.  Run as a program (not part of any proof):

  `lake env lean --run Weak/Prom/LitmusOracle.lean <repo> [cap]`

where `<repo>` is a checkout of `litmus-tests-riscv` at `08728edcd99c7e1819d2d4c6789df6d5299ccb69` (kept OUT of the
committed tree, e.g. under `.lake/`), and `cap` (default 8) bounds the number of memory instructions of a test the
run attempts (the enumerator lists gmo linearisations; larger tests are reported as out of the run's budget, not
as verdicts).

For each `tests/non-mixed-size/**.litmus` with a herd `Observation` line (`model-results/herd.logs`), the checker's
verdict on the condition's body `P` is computed as herd reports it: `Never` (no execution satisfies `P`: by
`forbidB`, i.e. a proof-backed verdict `forbid_sound`), `Always` (no execution satisfies `¬P`), `Sometimes`
(witnesses both ways, by `existsB` — `exists_sound`).  Every disagreement is printed.  The run also checks that the
hand-written rows of `Weak/Prom/RefTests.lean` that name a repository test are STRUCTURALLY EQUAL to the parsed
file (same instructions, registers, initial state and condition).
-/
import Weak.Prom.LitmusParse
import Weak.Prom.RefTests

namespace Weak.Prom.Ref.Oracle

open Weak.Prom.Ref Weak.Prom.Ref.Parse

/-- herd's verdict on a condition body. -/
inductive Vd where
  | never | sometimes | always | unknown
  deriving BEq, Repr

def Vd.str : Vd → String
  | .never => "Never" | .sometimes => "Sometimes" | .always => "Always" | .unknown => "unknown"

def Vd.ofStr (s : String) : Vd :=
  if s == "Never" then .never else if s == "Sometimes" then .sometimes else if s == "Always" then .always
  else .unknown

/-- The checker's verdict on the test's condition body. -/
def verdict (T : Test) : Vd :=
  let Tn : Test := { T with cond := .not T.cond }
  if existsB T then (if forbidB Tn then .always else if existsB Tn then .sometimes else .unknown)
  else if forbidB T then .never else .unknown

/-- herd's convention for the litmus mnemonics `l*.aq` / `s*.rl`: RCpc annotations (evidence runs only). -/
def toRcpc (T : Test) : Test :=
  { T with harts := T.harts.map (fun p => p.map (fun i => match i with
      | .loadAq sz rl rd rs1 => .loadAqPc sz rl rd rs1
      | .storeRl sz aq rs2 rs1 => .storeRlPc sz aq rs2 rs1
      | i => i)) }

def memInstrs (T : Test) : Nat :=
  T.harts.foldl (fun acc p => acc + (p.filter (fun i => match i with
    | .load .. | .store .. | .loadAq .. | .storeRl .. | .loadAqPc .. | .storeRlPc .. | .lr .. | .sc .. | .amo .. =>
      true
    | _ => false)).length) 0

/-- Normal form for the structural comparison: per-hart registers sorted, zero bytes dropped, bytes sorted. -/
def norm (T : Test) : Test :=
  { T with
    regs0 := T.regs0.map (fun l => (l.filter (fun p => p.2 != 0)).mergeSort (fun a b => a.1 ≤ b.1))
    img := (T.img.filter (fun p => p.2 != 0)).mergeSort (fun a b => a.1 ≤ b.1) }

def sameTest (a b : Test) : Bool :=
  let a := norm a
  let b := norm b
  a.harts == b.harts && a.regs0 == b.regs0 && a.img == b.img && a.io == b.io && a.cond == b.cond

open Weak.Prom.Ref.Lit in
/-- The hand-written rows of RefTests.lean that are repository tests (path under `tests/`). -/
def handRows : List (String × Test) :=
  [("non-mixed-size/BASIC_2_THREAD/LB.litmus", lb), ("non-mixed-size/BASIC_2_THREAD/LB+datas.litmus", lbDatas),
   ("non-mixed-size/BASIC_2_THREAD/LB+ctrls.litmus", lbCtrls), ("non-mixed-size/BASIC_2_THREAD/MP.litmus", mp),
   ("non-mixed-size/SAFE/MP+fence.w.w+fence.r.rw.litmus", mpFF), ("non-mixed-size/SAFE/MP+fence.w.w+addr.litmus", mpFAddr),
   ("non-mixed-size/BASIC_2_THREAD/SB.litmus", sbT), ("non-mixed-size/BASIC_2_THREAD/SB+fence.rw.rws.litmus", sbFF),
   ("non-mixed-size/HAND/SB+rfi-fence.r.rs.litmus", sbFwd), ("non-mixed-size/HAND/PPOCA.litmus", ppoca),
   ("non-mixed-size/HAND/MP+fence.w.w+data-wsi-rfi-addr.litmus", datacoirfiR),
   ("non-mixed-size/HAND/LB+fence.r.rw+addr-po.litmus", addrpoR), ("non-mixed-size/HAND/RSW.litmus", rsw),
   ("non-mixed-size/BASIC_2_THREAD/2+2W.litmus", w22), ("non-mixed-size/SAFE/2+2W+fence.w.ws.litmus", w22F),
   ("non-mixed-size/CO/CoWW.litmus", coWW), ("non-mixed-size/CO/CoWR0.litmus", coWR0), ("non-mixed-size/HAND/CoWR.litmus", coWR),
   ("non-mixed-size/CO/CoRW1.litmus", coRW1), ("non-mixed-size/CO/CoRW2.litmus", coRW2), ("non-mixed-size/CO/CoRR.litmus", coRR),
   ("non-mixed-size/SAFE/ISA2+fence.rw.rws.litmus", isa2F), ("non-mixed-size/SAFE/WRC+fence.rw.rws.litmus", wrcF),
   ("non-mixed-size/SAFE/IRIW+ctrlfenceis.litmus", iriwCtrlFi), ("non-mixed-size/SAFE/IRIW+fence.r.rws.litmus", iriwF),
   ("mixed-size/SF_THESIS/HAND/MP+sis.litmus", mix26a), ("mixed-size/SF_THESIS/HAND/MP+fence.rw.rw+si.litmus", mix26b),
   ("mixed-size/SF_THESIS/HAND/WRR+2W+sis.litmus", mix26c), ("mixed-size/SF_THESIS/HAND/MIX1.litmus", mix26d),
   ("mixed-size/HAND/LR-SC-mixed1.litmus", mix26h), ("mixed-size/HAND/LR-SC-mixed2.litmus", mix26i)]

partial def walk (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← walk e.path)
    else if e.path.extension == some "litmus" then out := out ++ [e.path]
  return out

def main (args : List String) : IO UInt32 := do
  let repo : System.FilePath := args.headD "."
  let cap := (args.getD 1 "8").toNat!
  let rcpc := args.getD 2 "" == "rcpc"
  IO.println s!"convention for l*.aq/s*.rl: {if rcpc then "RCpc (herd)" else "RCsc (Zalasr, the manual)"}"
  -- herd's observations
  let logs ← IO.FS.readFile (repo / "model-results" / "herd.logs")
  let obs : List (String × String) := (logs.splitOn "\n").filterMap (fun l =>
    match l.splitOn " " with
    | "Observation" :: n :: v :: _ => some (n, v)
    | _ => none)
  IO.println s!"herd observations: {obs.length}"
  -- structural check of the hand-written rows
  let mut handOk := 0
  for (p, T) in handRows do
    let src ← IO.FS.readFile (repo / "tests" / p)
    match parseLitmus src with
    | .ok lt =>
      if sameTest lt.test T then handOk := handOk + 1
      else IO.println s!"HANDROW-MISMATCH {p}\n  parsed: {repr (norm lt.test).harts}\n  regs {repr (norm lt.test).regs0} img {repr (norm lt.test).img} cond {repr lt.test.cond}\n  hand:   {repr (norm T).harts}\n  regs {repr (norm T).regs0} img {repr (norm T).img} cond {repr T.cond}"
    | .error e => IO.println s!"HANDROW-PARSE-ERROR {p}: {e}"
  IO.println s!"hand rows structurally equal to the repository file: {handOk}/{handRows.length}"
  -- the corpus
  let files ← walk (repo / "tests" / "non-mixed-size")
  let files := files.mergeSort (fun a b => a.toString ≤ b.toString)
  let mut nAgree := 0
  let mut nDis := 0
  let mut nParse := 0
  let mut nNoHerd := 0
  let mut nBig := 0
  let mut nUnk := 0
  let mut reasons : List (String × Nat) := []
  let mut perVd : List (String × Nat) := []
  for f in files do
    let src ← IO.FS.readFile f
    match parseLitmus src with
    | .error e =>
      nParse := nParse + 1
      let key := (e.splitOn ":").headD e
      reasons := match reasons.find? (·.1 == key) with
        | some _ => reasons.map (fun r => if r.1 == key then (r.1, r.2 + 1) else r)
        | none => reasons ++ [(key, 1)]
      IO.println s!"SCOPE parse {f}: {e}"
    | .ok lt =>
      match obs.find? (·.1 == lt.name) with
      | none => nNoHerd := nNoHerd + 1; IO.println s!"NOHERD {f} ({lt.name})"
      | some (_, hv) =>
        if memInstrs lt.test > cap then
          nBig := nBig + 1
          IO.println s!"SCOPE budget {f}: {memInstrs lt.test} memory instructions > {cap}"
        else
          let ours := verdict (if rcpc then toRcpc lt.test else lt.test)
          let theirs := Vd.ofStr hv
          if ours == .unknown then
            nUnk := nUnk + 1
            IO.println s!"SCOPE checker {f}: enumerator scope check failed (I/O or varsOk)"
          else if ours == theirs then
            nAgree := nAgree + 1
            perVd := match perVd.find? (·.1 == hv) with
              | some _ => perVd.map (fun r => if r.1 == hv then (r.1, r.2 + 1) else r)
              | none => perVd ++ [(hv, 1)]
            IO.println s!"AGREE {lt.name} {hv}"
          else
            nDis := nDis + 1
            IO.println s!"DISAGREE {f} ({lt.name}): herd {hv}, reference {ours.str}"
  IO.println s!"SUMMARY files={files.length} agree={nAgree} disagree={nDis} parse-out-of-scope={nParse} no-herd-result={nNoHerd} over-budget={nBig} checker-scope={nUnk}"
  IO.println s!"SUMMARY agree by verdict: {perVd}"
  IO.println s!"SUMMARY parse reasons: {reasons}"
  return 0

end Weak.Prom.Ref.Oracle

def main (args : List String) : IO UInt32 := Weak.Prom.Ref.Oracle.main args
