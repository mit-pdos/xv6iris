/-
Weak/Prom: **the run-certificate generator** (S0-P part (2), milestone 2).  A program:

  `lake env lean --run Weak/Prom/MachCertGen.lean > Weak/Prom/MachCerts.lean`

For every §5 row of `Weak/Prom/RefTests.lean` in phase-1 scope it runs the label-level explorer (MachLitmus.lean:
candidate final memories `M`, then each hart's DFS over `Mach.succ`, which records each hart's trace) until it finds
a valid run whose outcome satisfies the test's condition, and prints that run as a certificate — the promises of `M`
in order, then each hart's state events — with a theorem `mach_<test> : allowedMach <test>` proved by
`certOk_sound … (by decide +kernel)`.  ALLOWED rows get `mach_<test>`; FORBIDDEN rows get `mach_<test>_exec`
(the machine has a complete valid run of the test: the forbidden verdict is not vacuous on the machine side).
The generator also evaluates `certOk` itself and reports failures on stderr (the kernel re-checks in the theorem).
-/
import Weak.Prom.MachCert
import Weak.Prom.RefLitmus2

namespace Weak.Prom.Mach.CertGen

open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref Weak.Prom.Ref.Lit
open PLabel

/-! ## Printing Lean terms -/

def pB (b : Bool) : String := if b then "true" else "false"
def pI (a : Int) : String := if a < 0 then s!"({a})" else s!"{a}"
def pByte (b : BitVec 8) : String := s!"{b.toNat}#8"
def pList {α : Type} (f : α → String) (l : List α) : String := "[" ++ ", ".intercalate (l.map f) ++ "]"
def pTv (tv : Nat × BitVec 8) : String := s!"({tv.1}, {pByte tv.2})"
def pD : Weak.Dsrc → String
  | .DReg r => s!".DReg {r}"
  | .DLdRes => ".DLdRes"
def pDs (l : List Weak.Dsrc) : String := pList pD l

def pLabel : PLabel → Option String
  | LSilent => some "LSilent"
  | LLoad aq rl b tvs a => some s!"LLoad {pB aq} {pB rl} {pI b} {pList pTv tvs} {pDs a}"
  | LStore aq rl b d a v => some s!"LStore {pB aq} {pB rl} {pI b} {pList pByte d} {pDs a} {pDs v}"
  | LRmw aq rl b tvs d a v => some s!"LRmw {pB aq} {pB rl} {pI b} {pList pTv tvs} {pList pByte d} {pDs a} {pDs v}"
  | LFence pr pw sr sw => some s!"LFence {pB pr} {pB pw} {pB sr} {pB sw}"
  | LFenceI => some "LFenceI"
  | LRegW rd s => some s!"LRegW {rd} {pDs s}"
  | LCtrl s => some s!"LCtrl {pDs s}"
  | LInstr => some "LInstr"
  | LExLoad aq rl b tvs a => some s!"LExLoad {pB aq} {pB rl} {pI b} {pList pTv tvs} {pDs a}"
  | LExStore aq rl b d a v => some s!"LExStore {pB aq} {pB rl} {pI b} {pList pByte d} {pDs a} {pDs v}"
  | LExFail => some "LExFail"
  | _ => none

def pCls : PClass → Option String
  | .plain => some ".plain"
  | .rel => some ".rel"
  | .excl => some ".excl"
  | .cmo .. => none

def pMsg (m : PMsg) : Option String := do
  let c ← pCls m.cls
  let t ← m.tid
  pure s!"⟨{pI m.pa}, {pList pByte m.data}, some {t}, {c}⟩"

def pOts : Option Nat → String
  | none => "none"
  | some t => s!"(some {t})"

def pEvt : PEvt → Option String
  | .prom i m => do pure s!".prom {i} {← pMsg m}"
  | .st i l o => do pure s!".st {i} ({← pLabel l}) {pOts o}"

/-! ## Finding a run -/

/-- Every choice of one element per list. -/
def prodL {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | l :: rest => l.flatMap (fun x => (prodL rest).map (x :: ·))

/-- The certificate of the first valid run (with every hart done) satisfying the condition, if any. -/
def findCert (T : Test) : Option (List PEvt) := Id.run do
  let obs := condKeys T.cond
  match sigmaAll T 200000 with
  | none => return none
  | some (sig, _) =>
    for ch in choices sig do
      let n := ch.foldl (fun a l => a + l.length) 0
      for M in arrange (n + 1) ch do
        let runs := (List.range T.harts.length).map (fun i => (hartRuns T M i).fin)
        if runs.any List.isEmpty then continue
        for row in prodL runs do
          let o := obs.map (fun k => match k with
            | .reg h r => ((row[h]?).map (fun mh => mh.rd r)).getD 0
            | .mem a sz => finalMem (testImg T) M a sz)
          if condOn obs o T.cond then
            let proms := M.map (fun m => PEvt.prom (m.tid.getD 0) m)
            let sts := (List.range row.length).flatMap (fun i =>
              match row[i]? with
              | some mh => mh.tr.reverse.map (fun (l, ot) => PEvt.st i l ot)
              | none => [])
            return some (proms ++ sts)
    return none

/-! ## The rows -/

def allowedRows : List (String × Test) :=
  [("lb", lb), ("mp", mp), ("sbT", sbT), ("sbFwd", sbFwd), ("ppoca", ppoca), ("datacoirfi", datacoirfi),
   ("datacoirfiR", datacoirfiR), ("frirfi", frirfi), ("rsw", rsw), ("w22", w22), ("isa2", isa2), ("wrc", wrc),
   ("iriwCtrlFi", iriwCtrlFi), ("iriw", iriw), ("mix26d", mix26d), ("mix26e", mix26e), ("mix26f", mix26f),
   ("mix26g", mix26g), ("lbAmoPo", lbAmoPo), ("lbAmoAd", lbAmoAd), ("lrsc", lrsc), ("lrldsc", lrldsc),
   ("lrsdsc_a", lrsdsc_a), ("lrsdsc_b", lrsdsc_b), ("lrsdsc_c", lrsdsc_c), ("lrsdsc_d", lrsdsc_d),
   ("lrAmoSc", lrAmoSc), ("lbMisa", lbMisa), ("updStuck", updStuck)]

def forbiddenRows : List (String × Test) :=
  [("lbdd", lbdd), ("lbDatas", lbDatas), ("lbCtrls", lbCtrls), ("lbCtrlsBeq", lbCtrlsBeq), ("lbLrsc", lbLrsc),
   ("oota42", oota42), ("mpFF", mpFF), ("mpFFrr", mpFFrr), ("mpFAddr", mpFAddr), ("mpAmoRlAq", mpAmoRlAq),
   ("mpFAmo", mpFAmo), ("amoStorePart", amoStorePart), ("sbFF", sbFF), ("datarfi", datarfi), ("addrpo", addrpo),
   ("addrpoR", addrpoR), ("w22F", w22F), ("coWW", coWW), ("coWR0", coWR0), ("coWR", coWR), ("coRW1", coRW1),
   ("coRW2", coRW2), ("coRR", coRR), ("coRR2", coRR2), ("parInc", parInc), ("isa2F", isa2F), ("wrcF", wrcF),
   ("iriwF", iriwF), ("mix26a", mix26a), ("mix26b", mix26b), ("mix26c", mix26c), ("mix26dNot", mix26dNot),
   ("mix26h", mix26h), ("mix26i", mix26i), ("mpAmoData", mpAmoData), ("mpAmoCtrl", mpAmoCtrl), ("mixSca", mixSca),
   ("lrScSc", lrScSc), ("wsub", wsub), ("armWeak", armWeak), ("lbAcq", lbAcq), ("lbRel", lbRel), ("coh", Lit.coh),
   ("seqT", seqT), ("lbfd", lbfd), ("rng", rng), ("disjLists", disjLists), ("ramAq", ramAq)]

def header : String :=
"/-
Weak/Prom: **machine-v2 certificate theorems** (S0-P part (2), milestone 2).  GENERATED by
`lake env lean --run Weak/Prom/MachCertGen.lean` — do not edit by hand.

`mach_<test> : allowedMach <test>`: machine v2 (Machine.lean `validRun`, program half `litStep`) has a valid run in
which every hart finishes and the test's condition holds.  Each proof replays the explorer's run certificate in the
kernel (`certOk_sound`, MachCert.lean).  `mach_<test>_exec : allowedMach (anyOutcome <test>)` for a FORBIDDEN row:
the machine has a complete valid run of that test.
-/
import Weak.Prom.MachCert
import Weak.Prom.RefLitmus2

namespace Weak.Prom.Mach.Certs

open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref Weak.Prom.Ref.Lit
open PLabel
"

def emit (thm : String) (testExpr : String) (T : Test) : IO Unit := do
  match findCert T with
  | none => IO.eprintln s!"NO RUN FOUND: {thm}"; IO.println s!"-- {thm}: no run found by the explorer"
  | some evs =>
    match evs.mapM pEvt with
    | none => IO.eprintln s!"UNPRINTABLE: {thm}"
    | some ss =>
      if !certOk T evs then IO.eprintln s!"CERT FAILS (evaluator): {thm}"
      IO.println s!"def cert_{thm} : List PEvt :=\n  [{",\n   ".intercalate ss}]\n"
      IO.println s!"theorem {thm} : allowedMach {testExpr} := certOk_sound _ cert_{thm} (by decide +kernel)\n"

def main : IO UInt32 := do
  IO.println header
  for (n, T) in allowedRows do
    emit s!"mach_{n}" s!"Lit.{n}" T
  for (n, T) in forbiddenRows do
    emit s!"mach_{n}_exec" s!"(anyOutcome Lit.{n})" (anyOutcome T)
  IO.println "end Weak.Prom.Mach.Certs"
  return 0

end Weak.Prom.Mach.CertGen

def main : IO UInt32 := Weak.Prom.Mach.CertGen.main
