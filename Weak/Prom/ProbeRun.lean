/-
Weak/Prom: **the probe runner** (S0-P parts (4)/(6)).  Runs a family of `ProbeGen.lean` on

* the REFERENCE (RefCheck's enumerator: every consistent candidate's outcome, `refCoreB`, as MachOracle.lean),
* machine v2 at LABEL level (`Mach.sigmaAll` … `outcomesM`, as MachOracle.lean),
* machine v2 THROUGH SAIL (`SailLit.prepare` / `sailOutcomes`, or `outsAt` at a fixed platform),
* TODAY's machine (`Today.todayOutcomes`, calibration),

and compares FULL outcome sets (projected on the probe's observables).  A probe with a text verdict is also decided
against it on its designated outcome.  Run:

  `lake env lean --run Weak/Prom/ProbeRun.lean <family> <shard> <shards> [nosail] [notoday] [noref]`

One line per probe:
`P <fam> <name> | r=<n> m=<n> s=<n|na> t=<n> | MR=<cmp> SR=<cmp> TR=<cmp> | V text=<A|F|-> r m s t | <ms>`
where `<cmp>` ∈ `eq`, `STRONGER` (the machine lacks a reference outcome), `WEAKER` (an extra one), `BOTH`, `na`;
a disagreement is followed by `  only-ref(<side>):` / `  only-<side>:` lines (at most 4 outcomes each).
-/
import Weak.Prom.ProbeGen
import Weak.Prom.CalibToday
import Weak.Prom.MachSail
import Std.Data.HashSet

namespace Weak.Prom.Probe.Run

open Weak.Prom Weak.Prom.Mach Weak.Prom.Ref Weak.Prom.Probe

/-- The reference's outcome set (MachOracle.lean `refOutcomes`). -/
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
  (outs.eraseDups, ok)

/-- Machine v2's label-level outcome set (MachOracle.lean `machOutcomes`). -/
def machOutcomes (T : Test) (obs : List Key) (budget mcap : Nat) : Option (List (List Nat)) × List String :=
  Id.run do
  match sigmaAll T budget with
  | none => return (none, ["budget"])
  | some (sig, _) =>
    let mut seen : Std.HashSet (List (Int × List Nat × Nat × Nat)) := {}
    let mut outs : Std.HashSet (List Nat) := {}
    let mut oos : List String := []
    let mut cands := 0
    for ch in choices sig do
      let n := ch.foldl (fun a l => a + l.length) 0
      for M in arrange (n + 1) ch do
        let key := msgsKey M
        if seen.contains key then continue
        seen := seen.insert key
        cands := cands + 1
        if mcap < cands then return (none, ["mcap"])
        let (r, (_, oo)) := outcomesM T obs M (0, [])
        oos := (oos ++ oo).eraseDups
        match r with
        | none => pure ()
        | some os => for o in os do outs := outs.insert o
    return (some outs.toList, oos)

def cmpSets (m o : List (List Nat)) : String × List (List Nat) × List (List Nat) :=
  let onlyM := m.filter (fun x => !o.contains x)
  let onlyO := o.filter (fun x => !m.contains x)
  (if onlyM.isEmpty && onlyO.isEmpty then "eq" else if onlyM.isEmpty then "STRONGER"
   else if onlyO.isEmpty then "WEAKER" else "BOTH", onlyM, onlyO)

def showOut (obs : List Key) (o : List Nat) : String :=
  String.intercalate " " ((obs.zip o).map (fun (k, v) => match k with
    | .reg h r => s!"{h}:x{r}={v}"
    | .mem a _ => s!"[{a}]={v}"))

def vd (obs : List Key) (c : OC) (outs : List (List Nat)) : String :=
  if outs.any (fun o => condOn obs o c) then "A" else "F"

def locs : List Nat := [0x1000, 0x2000, 0x3000, 0x4000, 0x5000, 0x6000, 0x7000]

def main (args : List String) : IO UInt32 := do
  let fam := args.getD 0 "G1"
  let shard := (args.getD 1 "0").toNat!
  let shards := (args.getD 2 "1").toNat!
  let nosail := args.contains "nosail"
  let notoday := args.contains "notoday"
  let noref := args.contains "noref"
  let budget := 200000
  let mcap := 200000
  let ps := family fam
  IO.println s!"family {fam}: {ps.length} probes; shard {shard}/{shards}"
  if fam == "G1" then IO.println s!"G1 drops: {g1Drops}"
  let mut idx := 0
  for p in ps do
    idx := idx + 1
    if (idx - 1) % shards != shard then continue
    let T := p.T
    let obs := p.obs
    let t0 ← IO.monoMsNow
    let (ro, rok) := if noref then ([], true) else refOutcomes T obs
    let t1 ← IO.monoMsNow
    let (mo, moos) := machOutcomes T obs budget mcap
    let t2 ← IO.monoMsNow
    let so : Option (List (List Nat)) × String :=
      if nosail then (none, "nosail") else
      -- every GPR the test does not initialise starts at 0, as in the reference and the label level (the platform's
      -- boot program leaves `a0`/`a1` = hart id / device-tree pointer)
      let zeros := (List.range 31).map (fun k => (k + 1, 0))
      match SailLit.prepare { T with regs0 := (List.range T.harts.length).map (fun h => zeros ++ ((T.regs0[h]?).getD [])) }
          locs SailLit.bootX with
      | .error e => (none, s!"asm:{e}")
      | .ok S =>
        match p.plat with
        | some b =>
          let P : BitVec 64 → Bool := fun _ => b
          match SailLit.outsAt S P obs budget mcap {} with
          | (some os, st) => (some os.eraseDups, (if st.oos.isEmpty then "" else s!"oos={st.oos}") ++ (if st.havoc then " HAVOC" else ""))   -- MachFix-havoc
          | (none, _) => (none, "budget")
        | none =>
          match SailLit.sailOutcomes S obs budget mcap with
          | (some os, st) => (some os.eraseDups, (if st.oos.isEmpty then "" else s!"oos={st.oos}") ++ (if st.havoc then " HAVOC" else ""))   -- MachFix-havoc
          | (none, _) => (none, "budget")
    let t3 ← IO.monoMsNow
    let (to, tst) := if notoday then ([], ({} : Today.TStat)) else Today.todayOutcomes T obs budget mcap p.plat
    let t4 ← IO.monoMsNow
    let mos := mo.getD []
    let (mr, onlyM, onlyRM) := if noref || mo.isNone then ("na", [], []) else cmpSets mos ro
    let (sr, onlyS, onlyRS) := match so.1 with
      | some s => if noref then ("na", [], []) else cmpSets s ro
      | none => ("na", [], [])
    let (tr, onlyT, onlyRT) := if notoday || noref || tst.budget then ("na", [], []) else cmpSets to ro
    let vstr := match p.verdict with
      | some (c, al) =>
        s!"text={if al then "A" else "F"} r={if noref then "-" else vd obs c ro} m={vd obs c mos} s={if so.2.endsWith " HAVOC" then "HAVOC" else (so.1.map (vd obs c)).getD "-"} t={if notoday then "-" else vd obs c to}"
      | none => "-"
    let flags := (if rok then "" else " ref-varsOk-FAIL") ++ (if moos.isEmpty then "" else s!" moos={moos}") ++
      (if so.2.isEmpty then "" else s!" s:{so.2}") ++ (if tst.oos.isEmpty then "" else s!" toos={tst.oos}") ++
      (if tst.budget then " t:budget" else "")
    IO.println s!"P {p.fam} {p.name} | r={ro.length} m={mos.length} s={(so.1.map List.length).getD 0} t={to.length} | MR={mr} SR={sr} TR={tr} | V {vstr} | {t1 - t0}/{t2 - t1}/{t3 - t2}/{t4 - t3}ms{flags}"
    let sh (l : List (List Nat)) := (l.take 4).map (showOut obs)
    if !onlyM.isEmpty then IO.println s!"  only-m: {sh onlyM}"
    if !onlyRM.isEmpty then IO.println s!"  only-ref(m): {sh onlyRM}"
    if !onlyS.isEmpty then IO.println s!"  only-s: {sh onlyS}"
    if !onlyRS.isEmpty then IO.println s!"  only-ref(s): {sh onlyRS}"
    if !onlyT.isEmpty then IO.println s!"  only-t: {sh onlyT}"
    if !onlyRT.isEmpty then IO.println s!"  only-ref(t): {sh onlyRT}"
  return 0

end Weak.Prom.Probe.Run

def main (args : List String) : IO UInt32 := Weak.Prom.Probe.Run.main args
