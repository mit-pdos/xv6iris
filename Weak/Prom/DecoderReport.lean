/-
Weak/Prom: the decoder check's human-readable report (`lake env lean --run Weak/Prom/DecoderReport.lean`): per class
with a mismatch, the mismatches of emission v2 and of today's emission, with their polarity.  The kernel-checked
statements are `DecoderCheck.lean` §4.
-/
import Weak.Prom.DecoderCheck

open Weak.Prom.Dec

def showR : R → String
  | .g n => s!"x{n}"
  | .c n => s!"csr{(Nat.toDigits 16 n).asString}"
  | .ff b => s!"fflags{b}"
  | .frm => "frm"

def showF : Fld → String
  | .asrcX r => s!"+A {showR r}" | .asrcM r => s!"-A {showR r}"
  | .dsrcX r => s!"+D {showR r}" | .dsrcM r => s!"-D {showR r}"
  | .ctrlX r => s!"+C {showR r}" | .ctrlM r => s!"-C {showR r}"
  | .carryX d r => s!"{showR d}+{showR r}" | .carryM d r => s!"{showR d}-{showR r}"
  | .memX d => s!"{showR d}+mem" | .memM d => s!"{showR d}-mem"
  | .stale d => s!"{showR d}:STALE" | .untracked d => s!"{showR d}:untracked"
  | .reset d => s!"{showR d}:reset[]" | .setK d => s!"{showR d}:set" | .staleSide d => s!"{showR d}:stale-nondest"

def showP : Pol → String | .stronger => "S" | .weaker => "W" | .inert => "I"

def showMs (l : List (Fld × Pol)) : String := String.intercalate " " (l.map (fun (f, p) => s!"{showP p}[{showF f}]"))

def main : IO Unit := do
  IO.println s!"classes {rows.length} aligned {aligned}"
  let mut i := 0
  for r in rows do
    let a := mmV2 r
    let b := mmToday r
    if !a.isEmpty || !b.isEmpty || r.2.1.stop != "" then
      IO.println s!"{i} {r.1.row} {r.1.name} stop={r.2.1.stop} | v2: {showMs a} | today: {showMs b} | writes {r.2.1.writes}"
    i := i + 1
  IO.println s!"v2 STRONGER idx: {idxWith mmV2 .stronger}"
  IO.println s!"v2 WEAKER idx: {idxWith mmV2 .weaker}"
  IO.println s!"v2 INERT idx: {idxWith mmV2 .inert}"
  IO.println s!"today STRONGER idx: {idxWith mmToday .stronger}"
  IO.println s!"today WEAKER idx: {idxWith mmToday .weaker}"
  IO.println s!"trap v2 STRONGER: {trapIdxWith mmV2 .stronger}  trap today STRONGER: {trapIdxWith mmToday .stronger}"
