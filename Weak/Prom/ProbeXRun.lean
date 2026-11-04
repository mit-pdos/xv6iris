/-
Weak/Prom: **the runner of the G5x probes** (S0 exit, (E3) (b)): each probe of `ProbeX.lean` on the EXTENDED
reference (`RefX.refOutcomesX`) and on machine v2 + emission v2 THROUGH THE SAIL MODEL (`MachSailX`), complete outcome
sets on the probe's observables, and the designated outcome against the text verdict.  Run:

  `lake env lean --run Weak/Prom/ProbeXRun.lean [name]`

One line per probe: `P G5x <name> | r=<n> s=<n> | SR=<cmp> | V text=<A|F|-> r=<A|F> s=<A|F> | <ms> [stops]`.
-/
import Weak.Prom.ProbeX
import Weak.Prom.MachSailX

namespace Weak.Prom.Probe.RunX

open Weak.Prom Weak.Prom.Mach Weak.Prom.Ref Weak.Prom.RefX Weak.Prom.Probe

/-- (as ProbeRun.lean) -/
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

def toKey : OKey → Key
  | .reg h r => .reg h r
  | .mem a sz => .mem a sz

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  for p in g5xProbes do
    if let some n := only then if n != p.name then continue
    let obs := p.obs.map toKey
    let t0 ← IO.monoMsNow
    let (ro, nref) := refOutcomesX p.T p.obs
    let t1 ← IO.monoMsNow
    let zeros := (List.range 31).map (fun k => (k + 1, 0))
    let T' := { p.T with regs0 := (List.range p.T.harts.length).map (fun h => zeros ++ ((p.T.regs0[h]?).getD [])) }
    let (so, sst) : Option (List (List Nat)) × String :=
      match SailLitX.prepareX T' locs SailLit.bootX with
      | .error e => (none, s!"asm:{e}")
      | .ok S =>
        match SailLitX.outsAtX S (fun _ => true) obs 200000 200000 with
        | (some os, st) => (some os.eraseDups, s!"cands={st.cands} valid={st.valid}{if st.oos.isEmpty then "" else s!" oos={st.oos}"}{if st.miss > 0 then s!" MISS={st.miss}" else ""}{if st.havoc then " HAVOC" else ""}")   -- MachFix-havoc
        | (none, st) => (none, s!"budget oos={st.oos}")
    let t2 ← IO.monoMsNow
    let (sr, onlyS, onlyRS) := match so with
      | some s => cmpSets s ro
      | none => ("na", [], [])
    let vstr := match p.verdict with
      | some (c, al) => s!"text={if al then "A" else "F"} r={vd obs c ro} s={if sst.endsWith " HAVOC" then "HAVOC" else (so.map (vd obs c)).getD "-"}"
      | none => "text=- (compare only)"
    IO.println s!"P G5x {p.name} | r={ro.length} (consistent {nref}) s={(so.map List.length).getD 0} | SR={sr} | V {vstr} | {t1 - t0}/{t2 - t1}ms | {sst}"
    IO.println s!"  quote: {p.quote}"
    let sh (l : List (List Nat)) := (l.take 6).map (showOut obs)
    IO.println s!"  ref: {sh ro}"
    if !onlyS.isEmpty then IO.println s!"  only-s (machine WEAKER): {sh onlyS}"
    if !onlyRS.isEmpty then IO.println s!"  only-ref (machine STRONGER): {sh onlyRS}"
  return 0

end Weak.Prom.Probe.RunX

def main (args : List String) : IO UInt32 := Weak.Prom.Probe.RunX.main args
