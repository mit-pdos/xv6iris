/-
Weak: **W-SCO (A) — the decoders, and the SFENCE.VMA word** (plan rev 36 §C W-SCO (A) (1)(c)).
Lean-only.

* `fpDecodeC` / `fpDecodeS`: the decoders `ext_decode_compressed` / `ext_decode` read registers
  only (the walker over the 1.4 MB decoder, one clause-spine step per clause: the clause under
  the option post, the rest once).
* `fpDecodeS` also carries the decoder's answer on an SFENCE.VMA word (`sfAnnB 32 w`, the word the
  announce labels as the sfence marker): it is one of `isS` — `SFENCE_VMA`, or `ILLEGAL`, `CSRReg`,
  `UTYPE`, `WRS` (the clauses whose guard the walk does not refute from the word's fixed bits:
  the extension-gated SFENCE_VMA clause falls through, and the guards of the other three are
  opaque mapper predicates); every other clause's guard contradicts the word's fixed bits
  (`bv_decide`, from `sfAnnBBv`).  In particular the word never decodes to `FENCEI`.
* `fpExecuteS`: the `isS` instructions never answer `ExecuteAs` (so the cycle's one redirect does
  not fire after an sfence announce).

**Import hygiene.**  The `bv_decide` here adds `enumToBitVec` for every enum it meets; two
modules that each add one cannot be imported together.  `Weak.ExecSC4` adds `amoop`'s and
`Weak.AxSpineOk3` adds `cbop_zicbop`'s / `cbop_zicbom`'s first; this file depends on them, so
`bv_decide` reuses their copies (as `MachCSL.BvEnumSatp` does for `SATPMode`).
-/
import Weak.SailCycleOrderAllCsr
import Weak.AxSpineOk3

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp

/-- The fixed bits of an SFENCE.VMA word. -/
theorem sfAnnBBv (w : BitVec 32) (h : sfAnnB 32 w = true) :
    w &&& 0xFE007FFF#32 = 0x12000073#32 := by
  unfold sfAnnB at h
  simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simpa using h

/-- The decoder's possible answers on an SFENCE.VMA word (header). -/
def isS (i : instruction) : Bool :=
  match i with
  | .SFENCE_VMA _ => true
  | .ILLEGAL _ => true
  | .CSRReg _ => true
  | .UTYPE _ => true
  | .WRS _ => true
  | _ => false

/-- An `ExecuteAs` answer (the cycle's redirect). -/
def isExecAs (r : ExecutionResult) : Bool :=
  match r with
  | .ExecuteAs _ => true
  | _ => false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
@[fp_reg] theorem fpDecodeC (h : BitVec 16) : fpT (ext_decode_compressed h) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
@[fp_reg] theorem fpDecodeS (w : BitVec 32) :
    fp (fun i => sfAnnB 32 w = true → isS i = true) (ext_decode w) := by
  fp_walk
  all_goals
    have hb := sfAnnBBv _ ‹_›
    simp only [Sail.BitVec.extractLsb, Bool.and_eq_true, beq_iff_eq] at *
    bv_decide

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
theorem fpExecuteS (i : instruction) (hi : isS i = true) :
    fp (fun r => isExecAs r = false) (execute i) := by
  cases i
  all_goals first | exact absurd hi (by decide) | skip
  all_goals fp_walk
  all_goals (unfold execute_WRS; split <;> rfl)

end SailCycleOrderFp
end Weak
