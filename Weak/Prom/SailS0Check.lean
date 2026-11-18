/-
Weak/Prom: **spike S-0, the assembled `mpFF` and the boot facts R1 needs** (`#eval` only; no theorem).
Brief items (1) and (4) (`~/dev/weak-orch/promising/SailS0_prompt.txt`).  Prints the words MachSail.lean's assembler
gives each hart of `Lit.mpFF` (relocation `OFF = 0x80000000`, code at `codeBase h`), the end idiom's word, and hart
0's boot `mstatus.MIE` / privilege (the quiet-platform facts of R1).
-/
import Weak.Prom.MachSail
import Weak.Prom.RefTests

namespace Weak.Prom.SailS0

open Weak.Prom.SailLit
open LeanRV64D

/-- The locations of `Lit.mpFF` (x, y). -/
def mpLocs : List Nat := [Weak.Prom.Ref.Lit.X, Weak.Prom.Ref.Lit.Y]

/-- `jal x0, 0` (`j .`), the end idiom: MachSail's `asmInstr (.jmp _)` rejects a non-forward target, so it is
encoded directly (`jType 0 0`). -/
def endIdiom : Nat := jType 0 0

#eval (asmProg mpLocs 0 (Weak.Prom.Ref.Lit.mpFF.prog 0)).map
  (fun (ws, e) => (ws.map (fun w => s!"{(BitVec.ofNat 32 w)}"), s!"{(BitVec.ofNat 64 e)}"))
#eval (asmProg mpLocs 1 (Weak.Prom.Ref.Lit.mpFF.prog 1)).map
  (fun (ws, e) => (ws.map (fun w => s!"{(BitVec.ofNat 32 w)}"), s!"{(BitVec.ofNat 64 e)}"))
#eval s!"{(BitVec.ofNat 32 endIdiom)}"
#eval let f := Vtest.XRegs.file (bootX 0)
  (s!"{f Register.mstatus}", s!"{(f Register.mstatus).getLsbD 3}", s!"{f Register.mie}",
   (match f Register.cur_privilege with | .Machine => "M" | .Supervisor => "S" | .User => "U" | _ => "V"))

end Weak.Prom.SailS0
