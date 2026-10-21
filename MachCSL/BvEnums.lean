import LeanRV64D.Defs
import MachCSL.Ctx
import MachCSL.Pte

/-!
# One home for `bv_decide`'s enum encodings

`bv_decide` encodes an enum it meets in a goal or hypothesis by adding an auxiliary
declaration `T.enumToBitVec` (and its lemmas) to the environment of the module that first
meets it.  Two modules that each trigger it add the same name and clash when imported
together (Lean ≥ 4.34 also encodes `PUnit`, the `()` of Sail's unit-carrying constructors).
This file triggers every enum the proofs bit-blast over once; every module whose `bv_decide`
meets one of them imports this file (the generating modules were found by scanning the built
environment for `enumToBitVec` constants), and `bv_decide` reuses the existing declarations.
`MachCSL.BvEnumSatp` (the first such home, for `SATPMode`) now imports this file.
-/

namespace MachCSL

theorem bvEnum_unit (a b : Unit) (h : a = b) : b = a := by bv_decide
theorem bvEnum_ktier (a b : KTier) (h : a = b) : b = a := by bv_decide
theorem bvEnum_kperm (a b : KPerm) (h : a = b) : b = a := by bv_decide
theorem bvEnum_privilege (a b : LeanRV64D.Privilege) (h : a = b) : b = a := by bv_decide
theorem bvEnum_satpMode (a b : LeanRV64D.SATPMode) (h : a = b) : b = a := by bv_decide
theorem bvEnum_interruptType (a b : LeanRV64D.InterruptType) (h : a = b) : b = a := by bv_decide
theorem bvEnum_memPayload (a b : LeanRV64D.mem_payload) (h : a = b) : b = a := by bv_decide
theorem bvEnum_memoryRegionType (a b : LeanRV64D.MemoryRegionType) (h : a = b) : b = a := by bv_decide
theorem bvEnum_reservability (a b : LeanRV64D.Reservability) (h : a = b) : b = a := by bv_decide
theorem bvEnum_pageBasedMemType (a b : LeanRV64D.page_based_mem_type) (h : a = b) : b = a := by bv_decide
theorem bvEnum_misalignedException (a b : LeanRV64D.misaligned_exception) (h : a = b) : b = a := by bv_decide
theorem bvEnum_atomicSupport (a b : LeanRV64D.AtomicSupport) (h : a = b) : b = a := by bv_decide
theorem bvEnum_register (a b : LeanRV64D.Register) (h : a = b) : b = a := by bv_decide
-- since 0.16 the TLB carries the translation stage (WpStepHooks, UTranslate bit-blast over it)
theorem bvEnum_translationStage (a b : LeanRV64D.TranslationStage) (h : a = b) : b = a := by bv_decide
-- the enums inside register types (`written_event_index : Option (Nat × event_csr)`, the
-- Sdtrig `tdata` selectors), met whenever a goal's context holds a register value
theorem bvEnum_eventCsr (a b : LeanRV64D.event_csr) (h : a = b) : b = a := by bv_decide
theorem bvEnum_tdata (a b : LeanRV64D.tdata) (h : a = b) : b = a := by bv_decide
-- a register value in the context (`RegisterType r`, e.g. the cell equations of
-- `regPointsTo_of_eq`) also makes `bv_decide` mint the matcher lemma of `Register`'s
-- `Hashable` instance (`instHashableRegister.hash.match_1.eq_cond_enumToBitVec`, first met in
-- `MachCSL.WpStepHooks`)
theorem bvEnum_registerType (_x : LeanRV64D.RegisterType LeanRV64D.Register.mip) (a b : BitVec 1)
    (h : a = b) : b = a := by bv_decide

end MachCSL
