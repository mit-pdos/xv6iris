/-
MachCSL: the cycle's execute tail in the EXECUTE lanes' outcome shapes
(lane U1-C over U1-X1 / U1-X2).

The tails `uc_afterFetch_base`/`_rvc` (UCycle) take ANY walk of
`uxaExecAs i` from `ucNpcS s len`.  The execute lanes state their facts in
two uniform shapes: `UxaRetire D orc s m rd` (X1: retires, one GPR written,
no oracle consumed) and `UxcCtlOut D orc s m` (X2: a control outcome with
`UxcStep`).  Here each shape is pushed through the tail, so a family fact
becomes a fact about the whole post-fetch stretch with the step value
`Step_Execute (res, bits)`, the shape's predicate kept.
-/
import MachCSL.UCycle
import MachCSL.UExecCtl

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Register Step ExecutionResult FetchResult

variable {D : UFoot}

/-- The base tail from any execute outcome satisfying `P`. -/
theorem uc_afterFetch_base_of (hD : UcFoot D) (orc : UOrc) (s : UWSt) (w : BitVec 32) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1)
    (hdec : runRW D orc s (ext_decode w) = some (i, s, orc)) (P : ExecutionResult → UWSt → Prop)
    (hex : ∃ res s', runRW D orc (ucNpcS s 4) (uxaExecAs i) = some (res, s', orc) ∧ P res s') :
    ∃ res s', runRW D orc s (ucAfterFetch (F_Base w)) =
      some (Step_Execute (res, zero_extend (m := 32) w), s', orc) ∧ P res s' := by
  obtain ⟨res, s', e, hp⟩ := hex
  exact ⟨res, s', uc_afterFetch_base hD orc orc s s' w i res hrd hv hdec e, hp⟩

/-- The compressed tail from any execute outcome satisfying `P`. -/
theorem uc_afterFetch_rvc_of (hD : UcFoot D) (orc : UOrc) (s : UWSt) (h : BitVec 16) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1) (hm : UcMisa D s)
    (hdec : runRW D orc s (ext_decode_compressed h) = some (i, s, orc)) (P : ExecutionResult → UWSt → Prop)
    (hex : ∃ res s', runRW D orc (ucNpcS s 2) (uxaExecAs i) = some (res, s', orc) ∧ P res s') :
    ∃ res s', runRW D orc s (ucAfterFetch (F_RVC h)) =
      some (Step_Execute (res, zero_extend (m := 32) h), s', orc) ∧ P res s' := by
  obtain ⟨res, s', e, hp⟩ := hex
  exact ⟨res, s', uc_afterFetch_rvc hD orc orc s s' h i res hrd hv hm hdec e, hp⟩

/-- **X1's shape through the base tail**: the step retires with one GPR
written at the `nextPC := PC + 4` state. -/
theorem uc_afterFetch_base_retire (hD : UcFoot D) (orc : UOrc) (s : UWSt) (w : BitVec 32)
    (i : instruction) (rd : BitVec 5) (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1)
    (hdec : runRW D orc s (ext_decode w) = some (i, s, orc))
    (hex : UxaRetire D orc (ucNpcS s 4) (uxaExecAs i) rd) :
    ∃ v, runRW D orc s (ucAfterFetch (F_Base w)) =
      some (Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w), uxaWr (ucNpcS s 4) rd v, orc) := by
  obtain ⟨v, e⟩ := hex
  exact ⟨v, uc_afterFetch_base hD orc orc s _ w i _ hrd hv hdec e⟩

/-- X1's shape through the compressed tail. -/
theorem uc_afterFetch_rvc_retire (hD : UcFoot D) (orc : UOrc) (s : UWSt) (h : BitVec 16)
    (i : instruction) (rd : BitVec 5) (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1) (hm : UcMisa D s)
    (hdec : runRW D orc s (ext_decode_compressed h) = some (i, s, orc))
    (hex : UxaRetire D orc (ucNpcS s 2) (uxaExecAs i) rd) :
    ∃ v, runRW D orc s (ucAfterFetch (F_RVC h)) =
      some (Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) h), uxaWr (ucNpcS s 2) rd v, orc) := by
  obtain ⟨v, e⟩ := hex
  exact ⟨v, uc_afterFetch_rvc hD orc orc s _ h i _ hrd hv hm hdec e⟩

/-- **X2's shape through the base tail**: a control outcome (`UxcStep`
from the `nextPC := PC + 4` state). -/
theorem uc_afterFetch_base_ctl (hD : UcFoot D) (orc : UOrc) (s : UWSt) (w : BitVec 32) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1)
    (hdec : runRW D orc s (ext_decode w) = some (i, s, orc))
    (hex : UxcCtlOut D orc (ucNpcS s 4) (uxaExecAs i)) :
    ∃ res s', runRW D orc s (ucAfterFetch (F_Base w)) =
      some (Step_Execute (res, zero_extend (m := 32) w), s', orc) ∧ UxcStep (ucNpcS s 4) res s' :=
  uc_afterFetch_base_of hD orc s w i hrd hv hdec _ hex

/-- X2's shape through the compressed tail. -/
theorem uc_afterFetch_rvc_ctl (hD : UcFoot D) (orc : UOrc) (s : UWSt) (h : BitVec 16) (i : instruction)
    (hrd : D.Dr .elp = true) (hv : s.file .elp = 0#1) (hm : UcMisa D s)
    (hdec : runRW D orc s (ext_decode_compressed h) = some (i, s, orc))
    (hex : UxcCtlOut D orc (ucNpcS s 2) (uxaExecAs i)) :
    ∃ res s', runRW D orc s (ucAfterFetch (F_RVC h)) =
      some (Step_Execute (res, zero_extend (m := 32) h), s', orc) ∧ UxcStep (ucNpcS s 2) res s' :=
  uc_afterFetch_rvc_of hD orc s h i hrd hv hm hdec _ hex

end MachCSL
