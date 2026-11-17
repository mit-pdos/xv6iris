/-
Weak/Mini: **the fragment's programs as full-development programs** (mini plan rev 4 §2 "Shared first files").

The ONLY place (with the other `Weak/Mini/Eq*.lean` files) where the minimal stack meets the full development: an F
instruction as a full reference instruction (`MI.toInstr`), an F program as a full test (`MProg.toTest`, for ANY
outcome condition `cond` — no execution notion reads it), and the loop front end's texts (`MProg.xs`, OwnAFront.lean
`XI`).  The image is expanded word → bytes little-endian (`byteList`, as RefTests.lean `ini`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Prog
import Weak.Prom.OwnAFront

namespace Weak.Mini

open Weak.Prom.Ref (Instr Test OC byteList)

def MAlu.toAlu : MAlu → Weak.Prom.Ref.Alu
  | .add => .add | .sub => .sub | .xor => .xor | .or => .or | .and => .and | .sll => .sll | .srl => .srl
  | .sra => .sra | .slt => .slt | .sltu => .sltu | .mul => .mul

def MBrC.toBrC : MBrC → Weak.Prom.Ref.BrC
  | .eq => .eq | .ne => .ne | .lt => .lt | .ge => .ge | .ltu => .ltu | .geu => .geu

def MFence.toFenceSet (f : MFence) : Weak.Prom.Ref.FenceSet := ⟨f.pr, f.pw, f.pi, f.po, f.sr, f.sw, f.si, f.so⟩

/-- An F instruction of a program with access size `sz`, as a full reference instruction. -/
def MI.toInstr (sz : Nat) : MI → Instr
  | .alui op rd rs1 imm => .alui op.toAlu rd rs1 imm
  | .alu op rd rs1 rs2 => .alu op.toAlu rd rs1 rs2
  | .load sgn rd rs1 off => .load sz sgn rd rs1 off
  | .store rs2 rs1 off => .store sz rs2 rs1 off
  | .fence f => .fence f.toFenceSet
  | .br c rs1 rs2 tgt => .br c.toBrC rs1 rs2 tgt
  | .jmp tgt => .jmp tgt
  | .nop => .nop

/-- The word image as the full reference's byte image (little-endian, `sz` bytes per word). -/
def MProg.imgBytes (P : MProg) : List (Nat × Nat) :=
  P.img.flatMap (fun (a, v) => (byteList v P.sz).mapIdx (fun k b => (a + k, b)))

/-- An F program as a full test, for any outcome condition `cond` (no I/O regions). -/
def MProg.toTest (P : MProg) (cond : OC) : Test :=
  { harts := P.harts.map (·.map (MI.toInstr P.sz)), regs0 := P.regs0, img := P.imgBytes, io := [], cond := cond }

/-- The harts' texts for the full loop front end `xStep` (OwnAFront.lean). -/
def MProg.xs (P : MProg) : List (List Weak.Prom.OA.XI) :=
  P.harts.map (·.map (fun i => Weak.Prom.OA.XI.i (MI.toInstr P.sz i)))

end Weak.Mini
