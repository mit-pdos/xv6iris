/-
Weak/Prom: **AmoTight — the counterexample to the scope premise `amoTightV2`** (AmoSplitV2.lean:217–222; brief
`~/dev/weak-orch/promising/AmoTight_prompt.txt`).  EMPIRICAL (an executable run of the compiled Sail model through
`MachSail.sNext`, the executable transcription of Emit.lean `hstep`/`hnodeStep`), not a theorem.

The premise says: after an `LAmoLd`, a reachable hart takes only `LSilent` steps until an `LAmoSt` with the same
address sources.  Sail's `execute_AMO` (InstsEnd.lean:18664–18763, zaamo_insts.sail:73–156) handles `amocas`
(Zacas, `hartSupports Ext_Zacas = true`, PlatformConfig.lean:2130; enabled with `Ext_Zaamo ⇐ misa.A`) in the SAME
function as the other AMOs: after `mem_read` it reads `rs2` and `rd`, and when `loaded != X(rd)` it does
`wX_bits rd (sign_extend loaded)` and returns `RETIRE_SUCCESS` with NO `mem_write_value` (zacas.adoc: "An
unsuccessful amocas … may either not perform a memory write or may write back the old value").  So from a hart at an
instruction boundary (`hartInit`, M-mode power-on file), fetching `amocas.w x5, x6, (x7)` with `x7` an aligned RAM
address and answering the AMO read with a value ≠ `x5[31:0]`, the next non-silent label after `LAmoLd` is
`LRegW 5 …` (the write of `rd`), not `LAmoSt`.

Run: `lake env lean --run Weak/Prom/AmoTightCex.lean`.
-/
import Weak.Prom.MachSail

namespace Weak.Prom.AmoTightCex

open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Weak (Dsrc)
open Weak.Prom Weak.Prom.SailLit Weak.Prom.SailExec
open PLabel

def CODE : Nat := 0x80400000
def DATA : Nat := 0x80010000

/-- `amocas.w x5, x6, (x7)` (funct5 `00101`, aq = rl = 0, funct3 `010`, opcode `0x2F`); `amoadd.w` for contrast. -/
def wCas : Nat := rType (5 <<< 2) 6 7 2 5 0x2F
def wAdd : Nat := rType (0 <<< 2) 6 7 2 5 0x2F

def dsStr : List Dsrc → String
  | [] => ""
  | .DReg r :: t => s!"x{r} " ++ dsStr t
  | .DLdRes :: t => "ldres " ++ dsStr t

def labStr : PLabel → String
  | LSilent => "LSilent"
  | LRegW r s => s!"LRegW {r} [{dsStr s}]"
  | LCtrl s => s!"LCtrl [{dsStr s}]"
  | LInstr => "LInstr"
  | LAmoLd aq b _ s => s!"LAmoLd aq={aq} {b} [{dsStr s}]"
  | LAmoSt rl b _ s v => s!"LAmoSt rl={rl} {b} [{dsStr s}] [{dsStr v}]"
  | LExFail => "LExFail"
  | LFence .. => "LFence"
  | _ => "other"

/-- Step the emission from `h`, answering fetches with `word` and every data read with `ans`; print the non-silent
events until the next instruction boundary (or a stop). -/
partial def go (word : Nat) (ans : Nat → List (BitVec 8)) (h : SH) (fuel : Nat) (acc : Array String) : Array String :=
  if fuel = 0 then acc.push "fuel" else
  match sNextNS (fun _ => true) (BitVec.ofNat 64 (CODE + 4)) h 0 with
  | (.lab LInstr _, n) => acc.push s!"({n} silent) LInstr"
  | (.lab l h', n) => go word ans h' (fuel - 1) (acc.push s!"({n} silent) {labStr l}")
  | (.rd .fetch pa sz cont, n) =>
    let bs := (List.range sz).map (fun j =>
      let o := pa.toNat + j - CODE
      BitVec.ofNat 8 (if o < 4 then (word >>> (8 * o)) % 256 else 0))
    go word ans (cont bs) (fuel - 1) (acc.push s!"({n} silent) LIFetch {pa}")
  | (.rd (.amo aq asrc) pa sz cont, n) =>
    go word ans (cont (ans sz)) (fuel - 1) (acc.push s!"({n} silent) LAmoLd aq={aq} {pa} [{dsStr asrc}]")
  | (.rd _ pa _ cont, n) => go word ans (cont (ans 8)) (fuel - 1) (acc.push s!"({n} silent) read {pa}")
  | (.wr (.amo rl asrc vsrc) pa _ ok _, n) =>
    go word ans ok (fuel - 1) (acc.push s!"({n} silent) LAmoSt rl={rl} {pa} [{dsStr asrc}] [{dsStr vsrc}]")
  | (.wr _ pa _ ok _, n) => go word ans ok (fuel - 1) (acc.push s!"({n} silent) write {pa}")
  | (.done, n) => acc.push s!"({n} silent) done"
  | (.stop why, n) => acc.push s!"({n} silent) STOP {why}"

def start : SH :=
  let x := (bootX 0).insert .PC (BitVec.ofNat 64 CODE)
  let x := setGpr (setGpr (setGpr x 5 1#64) 6 2#64) 7 (BitVec.ofNat 64 DATA)
  -- the boundary hart: `.pure ()` with the empty channel (Emit.lean `hartInit`); its first step is `LInstr`
  ⟨.pure (), x, none, ixNone⟩

def run (name : String) (word : Nat) (v : Nat) : IO Unit := do
  IO.println s!"== {name}, AMO read answers {v} (x5 = 1)"
  for s in go word (fun sz => (List.range sz).map (fun j => BitVec.ofNat 8 ((v >>> (8 * j)) % 256)))
      { start with m := riscvStepP (fun _ => true) false } 4000 #[] do
    IO.println s!"  {s}"

def main : IO UInt32 := do
  run "amocas.w x5,x6,(x7): FAILED compare" wCas 0
  run "amocas.w x5,x6,(x7): successful compare" wCas 1
  run "amoadd.w x5,x6,(x7)" wAdd 0
  return 0

end Weak.Prom.AmoTightCex

def main : IO UInt32 := Weak.Prom.AmoTightCex.main
