/-
MachCSL: one PART of a misaligned user access: its translation composed with
its physical access (lane U2-M2; Rocq `UserMemMis`
`exec_translate_and_read_value_err`, `exec/goodmb_translate_and_write_value_gen`
/`_err`).

`translate_and_read_value`/`translate_and_write_value` (and the store's inline
low part) are `translateAddr` followed by `mem_read` (resp. `mem_write_ea` then
`mem_write_value`).  The translation is a HYPOTHESIS in the shape
`UTranslate.utr_translateAddr_ok/_err` concludes (whose own premise is lane
U1-P1's walk/TLB equation over `utrTranslate`); the physical access is
`umm_mem_read_U`/`umm_mem_write_value_U` over any `checked_mem_*` fact (the
misaligned RAM ones are `UMemMisRam`'s; lane U2-M1's aligned ones fit the
same slot).  Since sail-riscv 0.16 the part runs at an access information
(`AccessInfo`, its effective privilege `User`), and a translation fault is the
part's fault with the translation's own exception context (`trap`), with the
state where the walk left it.
-/
import MachCSL.UMemMisRam
import MachCSL.UMemAccess

namespace MachCSL

open Sail Sail.ArchSem
open LeanRV64D LeanRV64D.Functions

/-! ## §1 The physical access at User

Since sail-riscv 0.16 `mem_read`/`mem_write_value` take the effective privilege as an
argument (the access information's, `User` here); they no longer read `mstatus` and the
privilege themselves. -/

/-- `mem_read` at User is its `checked_mem_read` (meta dropped). -/
theorem umm_mem_read_U (D : UFoot) (orc : UOrc) (s : UWSt) (W : Nat) (pa : BitVec 64)
    (pbmt : page_based_mem_type) (v : BitVec (8 * W))
    (hc : runRW D orc s (checked_mem_read (.Load .Data) pbmt .User (.Physaddr pa) W false false false false) =
      some (.Ok (v, ()), s, orc)) :
    runRW D orc s (mem_read (.Load .Data) pbmt .User (.Physaddr pa) W false false false) = some (.Ok v, s, orc) := by
  unfold mem_read mem_read_priv_meta
  uwk_run -bv [hc, MemoryOpResult_drop_meta]

/-- `mem_write_value` at User is its `checked_mem_write`. -/
theorem umm_mem_write_value_U (D : UFoot) (orc : UOrc) (s : UWSt) (W : Nat) (pa : BitVec 64)
    (pbmt : page_based_mem_type) (v : BitVec (8 * W)) (b : Bool) (s' : UWSt)
    (hc : runRW D orc s (checked_mem_write (.Physaddr pa) W v (.Store .Data) pbmt .User () false false false) =
      some (.Ok b, s', orc)) :
    runRW D orc s (mem_write_value (.Physaddr pa) W v .User (.Store .Data) pbmt false false false) =
      some (.Ok b, s', orc) := by
  unfold mem_write_value mem_write_value_priv_meta
  uwk_run -bv [hc]

/-! ## §2 A read part (at a User access information) -/

theorem umm_translate_and_read_value_ok (D : UFoot) (orc : UOrc) (s : UWSt) (va : BitVec 64) (W : Nat)
    (ai : AccessInfo) (hai : ai.eff_privilege = .User)
    (pa : BitVec 64) (pbmt : page_based_mem_type) (s' : UWSt) (o' : UOrc) (v : BitVec (8 * W))
    (htr : runRW D orc s (translateAddr (.Virtaddr va) (.Load .Data) .User) =
      some (.Ok (.Physaddr pa, pbmt, ()), s', o'))
    (hm : runRW D o' s' (mem_read (.Load .Data) pbmt .User (.Physaddr pa) W false false false) = some (.Ok v, s', o')) :
    runRW D orc s (translate_and_read_value (.Virtaddr va) W (.Load .Data) ai false false false) =
      some (.Ok (.Physaddr pa, v), s', o') := by
  unfold translate_and_read_value
  simp only [hai]
  uma_seq htr
  uma_seq hm
  uma_pures
  rfl

/-- The part's translation fault: since sail-riscv 0.16 the translation reports its own
exception context, which the part traps with (Rocq `exec_translate_and_read_value_err`). -/
theorem umm_translate_and_read_value_err (D : UFoot) (orc : UOrc) (s : UWSt) (va : BitVec 64) (W : Nat)
    (ai : AccessInfo) (hai : ai.eff_privilege = .User)
    (e : ExceptionContext) (s' : UWSt) (o' : UOrc) (hD : UmaTrapFoot D)
    (htr : runRW D orc s (translateAddr (.Virtaddr va) (.Load .Data) .User) = some (.Err (e, ()), s', o')) :
    runRW D orc s (translate_and_read_value (.Virtaddr va) W (.Load .Data) ai false false false) =
      some (.Err (umaTrapC s' e), s', o') :=
  uma_translate_and_read_value_err D hD orc o' s s' va W (.Load .Data) ai hai false false false e htr

/-! ## §3 A write part (at a User access information) -/

theorem umm_translate_and_write_value_ok (D : UFoot) (orc : UOrc) (s : UWSt) (va : BitVec 64) (W : Nat)
    (ai : AccessInfo) (hai : ai.eff_privilege = .User)
    (pa : BitVec 64) (pbmt : page_based_mem_type) (v : BitVec (8 * W)) (s1 : UWSt) (o1 : UOrc) (s2 : UWSt)
    (o2 : UOrc) (b : Bool)
    (htr : runRW D orc s (translateAddr (.Virtaddr va) (.Store .Data) .User) =
      some (.Ok (.Physaddr pa, pbmt, ()), s1, o1))
    (hea : runRW D o1 s1 (mem_write_ea (.Physaddr pa) W .User (.Store .Data) pbmt false false false) =
      some (.Ok (), s1, o1))
    (hwv : runRW D o1 s1 (mem_write_value (.Physaddr pa) W v .User (.Store .Data) pbmt false false false) =
      some (.Ok b, s2, o2)) :
    runRW D orc s (translate_and_write_value (.Virtaddr va) W v (.Store .Data) ai false false false) =
      some (.Ok b, s2, o2) := by
  unfold translate_and_write_value
  simp only [hai]
  uma_seq htr
  uma_seq hea
  uma_seq hwv
  uma_pures
  rfl

theorem umm_translate_and_write_value_err (D : UFoot) (orc : UOrc) (s : UWSt) (va : BitVec 64) (W : Nat)
    (ai : AccessInfo) (hai : ai.eff_privilege = .User)
    (v : BitVec (8 * W)) (e : ExceptionContext) (s' : UWSt) (o' : UOrc) (hD : UmaTrapFoot D)
    (htr : runRW D orc s (translateAddr (.Virtaddr va) (.Store .Data) .User) = some (.Err (e, ()), s', o')) :
    runRW D orc s (translate_and_write_value (.Virtaddr va) W v (.Store .Data) ai false false false) =
      some (.Err (umaTrapC s' e), s', o') := by
  unfold translate_and_write_value
  simp only [hai]
  uma_seq htr
  simp only [runRW_bind, uma_trap D o' s' hD, Option.bind_some]
  rfl

/-! ## §4 A part in owned RAM -/

/-- **A read part in owned RAM**: the translation to `pa`, then some value. -/
theorem umm_translate_and_read_value_ram (D : UFoot) (orc : UOrc) (s : UWSt) (va : BitVec 64) (W : Nat)
    (ai : AccessInfo) (hai : ai.eff_privilege = .User)
    (h0 : 0 < W) (hW : W ≤ 8) (pa : BitVec 64) (s' : UWSt) (o' : UOrc)
    (htr : runRW D orc s (translateAddr (.Virtaddr va) (.Load .Data) .User) =
      some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s', o'))
    (hp : UmaPhys D s') (hram : inRam pa W) (hown : ummOwned s'.mm pa W) :
    ∃ v, runRW D orc s (translate_and_read_value (.Virtaddr va) W (.Load .Data) ai false false false) =
      some (.Ok (.Physaddr pa, v), s', o') := by
  obtain ⟨v, hc⟩ := umm_checked_mem_read_ram D o' s' hp pa W h0 hW hram hown
  exact ⟨v, umm_translate_and_read_value_ok D orc s va W ai hai pa .PBMT_PMA s' o' v htr
    (umm_mem_read_U D o' s' W pa .PBMT_PMA v hc)⟩

end MachCSL
