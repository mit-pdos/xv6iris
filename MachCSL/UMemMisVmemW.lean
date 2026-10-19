/-
MachCSL: **`vmem_write_addr` on a misaligned user store, in owned RAM**
(lane U2-M2; Rocq `UserMemMis` §`StraddleWrite`,
`exec/goodmb_translate_and_write_value_gen/_err`).

A plain data store (`Store Data`, not a store-conditional) at User privilege
whose address is not aligned to its width raises no misaligned exception and
proceeds to the page split (`UMemMisVmemR`'s front):

* **in one page**: one translation, then the announce and the chunked write
  of the full width (fault `umm_vmem_write_addr_err1`);
* **across a page boundary**: the LOW part is translated and written first
  (it is the model's inline part), then the HIGH part goes through
  `translate_and_write_value` from the state the low write left; a fault of
  the low part leaves memory untouched (`umm_vmem_write_addr_err1`), a fault
  of the high part comes after the low part's bytes were written.

The translations are hypotheses in lane U2-M1's shapes: a success is lane
U1-P1's `translate` walk (`runRW D orc s (utrTranslate s va acc) = …`),
turned into `translateAddr` by
`uma_translateAddr_ok`; a fault is a `translateAddr` fault
(`MachCSL.utr_translateAddr_err`), returned as the trap of its exception context
(`umaTrapC`; sail-riscv 0.16).  The access runs at an access information `ai` whose
effective privilege is User (`hai`).  The high part's translation
runs after the low write, whose bytes are existential, so its hypothesis is
asked for every byte map with the domain of the translation's landing map
(the walk reads only page-table bytes the store cannot reach on the user tier;
the caller discharges this from its walk/TLB facts).  The stored bytes are
existential; the maps keep their domain; the reservation bit is cleared.
-/
import MachCSL.UMemMisVmemR
import MachCSL.UMemMisTrv

namespace MachCSL

open Sail Sail.ArchSem
open LeanRV64D LeanRV64D.Functions

/-- **The (low or only) part's translation faults**: the store's fault, with the
translation's exception context (sail-riscv 0.16: `trap e`); nothing is written. -/
theorem umm_vmem_write_addr_err1 (D : UFoot) (hD : UmaTrapFoot D) (orc : UOrc) (s : UWSt) (hp : UtrPins D s)
    (ai : AccessInfo) (hai : ai.eff_privilege = .User)
    (va : BitVec 64) (w : Nat) (h0 : 0 < w) (h8 : w ≤ 8) (data : BitVec (8 * w)) (e : ExceptionContext)
    (s1 : UWSt) (o1 : UOrc)
    (htr : runRW D orc s (translateAddr (.Virtaddr va) (.Store .Data) .User) = some (.Err (e, ()), s1, o1)) :
    runRW D orc s (vmem_write_addr (.Virtaddr va) w data (.Store .Data) ai false false false) =
      some (.Err (umaTrapC s1 e), s1, o1) := by
  have ht := uma_trap D o1 s1 hD e
  by_cases hpg : ummInPage va w
  · unfold vmem_write_addr
    umm_vmem_front hp hai (umm_split_on_page_boundary_intra va w h0 h8 hpg)
    dsimp only [umm_ite_nosplit]
    simp only [htr, Option.bind_some]
    simp only [bind_assoc, liftM, run_lift_bind, runRW_bind, ht, Option.bind_some, run_throw_bind, runRW_pure]
  · obtain ⟨hp0, hpw⟩ := umm_lo_bounds va w hpg
    unfold vmem_write_addr
    umm_vmem_front hp hai (umm_split_on_page_boundary_straddle va w h8 hpg)
    generalize ummLo va = p at *
    generalize hc : (true && ((w : Int) - (p : Int)) >b 0) = c
    rw [umm_split_cond w p hpw] at hc
    subst hc
    dsimp only [umm_ite_true]
    simp only [htr, Option.bind_some]
    simp only [bind_assoc, liftM, run_lift_bind, runRW_bind, ht, Option.bind_some, run_throw_bind, runRW_pure]

end MachCSL
