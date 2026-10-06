/-
Weak: **the `execEff` kit every shape file shares** (M4): the monad-level twins
the mirrored SC scripts name, the two one-bus-step memory arms (where the trace
element is born), the width-independent register-only leaves, the eff
enablement chain, and two trace/window helpers.

Rocq: `iris/WeakLeafEffCommon.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The shape files (`WeakLeafEff8`, `WeakLeafEff8s`,
`WeakLeafBase4`, `WeakLeafAmo4`, …) each re-declared the same monad-level twins
and the same width-independent register-only leaves; this file is their single
home.
* §0 THE MONAD KIT: the twin of the model's `returnM`, the two short-circuit
  boolean connectives at the empty trace, and the one-bus-step RAM read and
  write (`Exec.execMemRead`/`execMemWrite`'s twins), which emit the trace
  element in front of the continuation's trace.
* §1 THE WIDTH-INDEPENDENT LEAVES: `split_misaligned` (unsplit),
  `split_on_page_boundary` (in-page / aligned), the `pmaCheck` kit (the
  `is_mag_applicable_access` leaves, `mag_pma_check` aligned, the tactic
  `pma_ok_eff_peel`), `translationMode` at Machine, the GPR leaves and
  `ext_data_get_addr`, the one-turn split-access loop.
* §2 THE eff ENABLEMENT CHAIN: `hartSupports`/`currentlyEnabled` facts,
  `virtual_memory_supported`, `lowest_supported_privLevel`,
  `have_nominal_privLevel` -- all register-only, every trace `[]`.
* §3 `nowriteRead1` and `win0Absurd`.

Conventions: as `Weak/ExecSC*.lean` (GPRs `s.gpr i` / `s.setGpr i v`;
`register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1"` ↦ `x == 1#1`;
`hartSupports` is pure; loops are lean-sail's `untilFuelM`) and
`Weak/WeakEff.lean`/`Weak/WeakEffSkel.lean` deviation 1 (`M X` ↦ `SailM X`,
`Defs.monadR R exception X` ↦ `SailME R X`, `catch_early_return` ↦ `SailME.run`).

**Deviations from Rocq.**
1. `exec_eff_returnM`: Lean's model has no `returnM`/`returnm` distinction (both
   are `pure`, `Weak/Exec.lean` deviation 6), so `execEffReturnM` restates
   `WeakEff.execEffReturnm`; it is kept for the name.
2. `and_boolM`/`or_boolM`: Lean's model has none (its `&&`/`||` of monadic
   operands are inline binds, `Weak/Exec.lean` "Not ported"); the two lemmas are
   about the inline forms `l >>= fun b => if b then r else pure false` and
   `l >>= fun b => if b then pure true else r`.
3. `exec_eff_MemRead`/`_MemWrite`: the event is `FreeM.impure (.ok (.memRead n va
   req)) k` (resp. `.memWrite`); Rocq's `dev_addr pa = false` is
   `mmioAcc req.pa n = false` (as `Exec.execMemRead`); the write's value is
   optional in Lean, so the write lemma takes `req.value = some w` and writes `w`;
   the continuation's answers are `.Ok (w, none)` / `.Ok (some true)`
   (`Weak/Exec.lean` deviation 4); `read_bytes` / `write_bytes` / `MState …` are
   `bmRead` / `bmWrite` / `s.setMem …`.
4. `split_misaligned`/`split_on_page_boundary`: widths are `Nat`, the results
   `Int` pairs (as `ExecSC2.execSplitMisalignedUnsplit`/
   `execSplitOnPageBoundaryAligned`); the intra-page premise is Lean's
   `==` test (as `ExecSC2.execSplitOnPageBoundaryIntra`); `vmem_width` is
   `ExecSC2.vmemWidth`.  The aligned proof goes through
   `ExecSC2.splitOnPageBoundaryAlignedEq` (the Rocq header's "collapse to one
   line" -- the fact IS exposed in Lean).
5. `exec_eff_assert_exp'_true` is about Lean's `assert true msg` returning `()`
   (as `ExecSC2.execAssertExpTrue`); named `execEffAssertExpTrue`.
6. `pma_ok_eff_peel` is a Lean `macro` over the same four arguments (the
   matching-region fact, the permission field, the `is_mag_applicable_access`
   fact, the alignment); the caller destructs the region first, as in Rocq.
   It normalises by `simp` over the `execREff` kit rather than replaying the
   six rewrites.  It is exercised below (`example`s at load/store/fetch/AMO).
7. `exec_eff_rX_bits_gpr`/`_wX_bits_gpr`/`_ext_data_get_addr_gpr` are stated
   with `s.gpr` / `s.setGpr` (ExecSC conventions); `exec_eff_wX_bits_at`'s
   premise is `wX (.Regno i.toNatInt) v = (writeReg r v' >>= fun _ => pure ())`
   (as `ExecLib.execWXBitsAt`) and the register `r` is any register with its
   value `v'`.
8. `execR_eff_untilMT_1` ↦ `execREffUntilMT1` over lean-sail's `untilFuelM 1`
   (as `ExecSC5.execRUntilFuelM1`): the `measure vars = 1` premise and the
   `measure` argument have no Lean counterpart and are dropped.
9. §2: `hartSupports` is pure in Lean (ExecSC conventions), so Rocq's
   `exec_eff (hartSupports X) s = Some (b, s, [])` is `hartSupports .X = b`.
   Lean's `currentlyEnabled` has no fuel: `exec_eff_rec_cE_Zicsr_any` (fuel `k`,
   accessibility proof, `Z.geb k 0` premise) is stated on
   `currentlyEnabled .Ext_Zicsr` without them.
10. `have_nom_val` (Rocq `WpGprCsrwCommon`, not in the Lean tree) is defined here
   as `haveNomVal` (same cases).
11. `win0_absurd`: Rocq's `N.to_nat 0` bound is the `Nat` `0`.
12. Rocq §4's `Print Assumptions` commands are not declarations (no Lean twin).

**Rocq → Lean name map.**  `exec_eff_returnM` `execEffReturnM`,
`exec_eff_and_boolM_nil` `execEffAndBoolMNil`, `exec_eff_or_boolM_nil`
`execEffOrBoolMNil`, `exec_eff_MemRead` `execEffMemRead`, `exec_eff_MemWrite`
`execEffMemWrite`, `exec_eff_split_misaligned_unsplit`
`execEffSplitMisalignedUnsplit`, `exec_eff_split_on_page_boundary_intra`
`execEffSplitOnPageBoundaryIntra`, `exec_eff_split_on_page_boundary_aligned`
`execEffSplitOnPageBoundaryAligned`, `exec_eff_split_on_page_boundary_aligned8`
`execEffSplitOnPageBoundaryAligned8`, `exec_eff_assert_exp'_true`
`execEffAssertExpTrue`, `exec_eff_is_mag_applicable_load_data`
`execEffIsMagApplicableLoadData`, `exec_eff_is_mag_applicable_store_data`
`execEffIsMagApplicableStoreData`, `exec_eff_is_mag_applicable_fetch`
`execEffIsMagApplicableFetch`, `exec_eff_is_mag_applicable_amo`
`execEffIsMagApplicableAmo`, `exec_eff_mag_pma_check_aligned`
`execEffMagPmaCheckAligned`, `pma_ok_eff_peel` (Ltac) `pma_ok_eff_peel` (macro),
`exec_eff_translationMode_M` `execEffTranslationModeM`, `exec_eff_rX_bits_gpr`
`execEffRXBitsGpr`, `exec_eff_wX_bits_at` `execEffWXBitsAt`,
`exec_eff_wX_bits_gpr` `execEffWXBitsGpr`, `exec_eff_ext_data_get_addr_gpr`
`execEffExtDataGetAddrGpr`, `execR_eff_untilMT_1` `execREffUntilMT1`,
`exec_eff_hartSupports_S` `WeakLeafEffCommon.execEffHartSupportsS` (duplicated
name), `exec_eff_hartSupports_U` `execEffHartSupportsU`,
`exec_eff_hartSupports_Zicsr` `WeakLeafEffCommon.execEffHartSupportsZicsr`
(duplicated name), `exec_eff_hartSupports_Zicfilp` `execEffHartSupportsZicfilp`,
`exec_eff_hartSupports_Sv32` `execEffHartSupportsSv32`,
`exec_eff_hartSupports_Sv39` `execEffHartSupportsSv39`,
`exec_eff_rec_cE_Zicsr_any` `execEffRecCEZicsrAny`,
`exec_eff_currentlyEnabled_S` `WeakLeafEffCommon.execEffCurrentlyEnabledS`
(duplicated name), `exec_eff_currentlyEnabled_U` `execEffCurrentlyEnabledU`,
`exec_eff_virtual_memory_supported` `execEffVirtualMemorySupported`,
`exec_eff_lowest_supported_privLevel` `execEffLowestSupportedPrivLevel`,
`exec_eff_have_nominal_privLevel` `execEffHaveNominalPrivLevel`, `have_nom_val`
(WpGprCsrwCommon) `haveNomVal`, `nowrite_read1` `nowriteRead1`, `win0_absurd`
`win0Absurd`.  Lean-only: the tactic `exec_eff_steps`, the private
`execEffCurrentlyEnabledSv39` (Rocq inlines it in `exec_eff_virtual_memory_supported`),
and four `example`s exercising `pma_ok_eff_peel`.

**Dropped:** nothing -- every Rocq lemma and the Ltac have a Lean twin (35 Rocq
`Lemma`s + 1 `Ltac`; Lean 35 theorems + 1 macro, plus `haveNomVal` and the
Lean-only items above).
-/
import Weak.WeakEffSkel
import Weak.ExecSC3

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Step a computation under `execEff` by unfolding (the `execEff` twin of
`exec_steps`; Lean-only).  Extra lemmas in brackets. -/
syntax "exec_eff_steps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| exec_eff_steps) => `(tactic| simp (config := { decide := true }) only [execEffBindEq,
      readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff, effThen,
      execEffReturnm, ↓reduceIte, Bool.false_eq_true, assert, PreSail.assert, List.nil_append,
      List.append_nil])
  | `(tactic| exec_eff_steps [$ls,*]) => `(tactic| simp (config := { decide := true }) only
      [execEffBindEq, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff,
      effThen, execEffReturnm, ↓reduceIte, Bool.false_eq_true, assert, PreSail.assert,
      List.nil_append, List.append_nil, $ls,*])

/-! ## 0. THE MONAD KIT -/

/-- Rocq `exec_eff_returnM` (deviation 1). -/
theorem execEffReturnM {X : Type} (x : X) (s : ExecSt) :
    execEff (pure x : SailM X) s = some (x, s, []) := rfl

/-- Rocq `exec_eff_and_boolM_nil` (deviation 2: the inline `&&`). -/
theorem execEffAndBoolMNil (l r : SailM Bool) (s : ExecSt) (bl : Bool) (sl : ExecSt) :
    execEff l s = some (bl, sl, []) →
    execEff (l >>= fun b => if b then r else pure false) s =
      (if bl then execEff r sl else some (false, sl, [])) := by
  intro h
  rw [execEffBindNil _ _ _ _ _ h]
  cases bl <;> rfl

/-- Rocq `exec_eff_or_boolM_nil` (deviation 2: the inline `||`). -/
theorem execEffOrBoolMNil (l r : SailM Bool) (s : ExecSt) (bl : Bool) (sl : ExecSt) :
    execEff l s = some (bl, sl, []) →
    execEff (l >>= fun b => if b then pure true else r) s =
      (if bl then some (true, sl, []) else execEff r sl) := by
  intro h
  rw [execEffBindNil _ _ _ _ _ h]
  cases bl <;> rfl

/-- Rocq `exec_eff_MemRead` (deviation 3): on a RAM access the outcome exposes
the `bmRead` match AND emits the read's `WEread` in front of the continuation's
trace. -/
theorem execEffMemRead {X : Type} (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (s : ExecSt)
    (h : mmioAcc req.pa n = false) :
    execEff (FreeM.impure (.ok (.memRead n va req)) k) s =
      match bmRead s.mem req.pa n with
      | some w =>
        match execEff (k (.Ok (w, none))) s with
        | some (y, s', es) => some (y, s', .WEread (classify req.access_kind) req.pa n :: es)
        | none => none
      | none => none := by
  simp only [execEff, h, Bool.false_eq_true, ↓reduceIte]
  cases bmRead s.mem req.pa n with
  | none => rfl
  | some w =>
    simp only
    cases execEff (k (.Ok (w, none))) s with
    | none => rfl
    | some p => obtain ⟨y, s', es⟩ := p; rfl

/-- Rocq `exec_eff_MemWrite` (deviation 3). -/
theorem execEffMemWrite {X : Type} (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X) (s : ExecSt) (w : BitVec (8 * n))
    (hv : req.value = some w) (h : mmioAcc req.pa n = false) :
    execEff (FreeM.impure (.ok (.memWrite n va req)) k) s =
      match execEff (k (.Ok (some true))) (s.setMem (bmWrite s.mem req.pa n w)) with
      | some (y, s', es) => some (y, s', .WEwrite (classify req.access_kind) req.pa n w :: es)
      | none => none := by
  simp only [execEff, hv, h, Bool.false_eq_true, ↓reduceIte]
  cases execEff (k (.Ok (some true))) (s.setMem (bmWrite s.mem req.pa n w)) with
  | none => rfl
  | some p => obtain ⟨y, s', es⟩ := p; rfl

/-! ## 1. THE WIDTH-INDEPENDENT LEAVES -/

/-- Rocq `exec_eff_split_misaligned_unsplit`: `CannotSplit` alone decides the
unsplit arm. -/
theorem execEffSplitMisalignedUnsplit (addr : BitVec 64) (width g : Nat) (s : ExecSt) :
    execEff (split_misaligned (.Physaddr addr) width g .CannotSplit) s =
      some (((1 : Int), (width : Int)), s, []) := rfl

/-- Rocq `exec_eff_split_on_page_boundary_intra` (deviation 4). -/
theorem execEffSplitOnPageBoundaryIntra {n : Nat} (addr : BitVec n) (width : Nat) (s : ExecSt)
    (h : ((addr &&& Sail.BitVec.updateSubrange (ones (n := Sail.BitVec.length addr) : BitVec n)
          (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) ==
        ((BitVec.subInt (BitVec.addInt addr width) 1) &&& Sail.BitVec.updateSubrange
          (ones (n := Sail.BitVec.length addr) : BitVec n) (Functions.pagesize_bits -i 1) 0
          (zeros (n := ((12 -i 1) -i (0 -i 1)))))) = true) :
    execEff (split_on_page_boundary addr width) s = some (((width : Int), (0 : Int)), s, []) := by
  unfold split_on_page_boundary
  simp only [h, ↓reduceIte, execEffReturnm]

/-- Rocq `exec_eff_split_on_page_boundary_aligned` (deviation 4). -/
theorem execEffSplitOnPageBoundaryAligned (a : BitVec 64) (w : Nat) (s : ExecSt) (hw : vmemWidth w)
    (ha : is_aligned_vaddr (.Virtaddr a) w = true) :
    execEff (split_on_page_boundary a w) s = some (((w : Int), (0 : Int)), s, []) := by
  rw [splitOnPageBoundaryAlignedEq a w hw ha]
  rfl

/-- Rocq `exec_eff_split_on_page_boundary_aligned8`. -/
theorem execEffSplitOnPageBoundaryAligned8 (a : BitVec 64) (s : ExecSt)
    (ha : is_aligned_vaddr (.Virtaddr a) 8 = true) :
    execEff (split_on_page_boundary a 8) s = some ((((8 : Nat) : Int), (0 : Int)), s, []) :=
  execEffSplitOnPageBoundaryAligned a 8 s (Or.inr (Or.inr (Or.inr rfl))) ha

/-! ### The `pmaCheck` kit -- the eff mirror of `ExecSC3`'s.  Everything on the
path is register-only (one `pma_regions` read), so every trace is `[]`. -/

/-- Rocq `exec_eff_assert_exp'_true` (deviation 5). -/
theorem execEffAssertExpTrue (msg : String) (s : ExecSt) :
    execEff (assert true msg) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_is_mag_applicable_load_data`. -/
theorem execEffIsMagApplicableLoadData (width : Nat) (s : ExecSt) :
    execEff (is_mag_applicable_access (.Load .Data) width) s =
      some (width ≤b Functions.xlen_bytes, s, []) := rfl

/-- Rocq `exec_eff_is_mag_applicable_store_data`. -/
theorem execEffIsMagApplicableStoreData (width : Nat) (s : ExecSt) :
    execEff (is_mag_applicable_access (.Store .Data) width) s =
      some (width ≤b Functions.xlen_bytes, s, []) := rfl

/-- Rocq `exec_eff_is_mag_applicable_fetch`. -/
theorem execEffIsMagApplicableFetch (width : Nat) (s : ExecSt) :
    execEff (is_mag_applicable_access (.InstructionFetch ()) width) s = some (false, s, []) := rfl

/-- Rocq `exec_eff_is_mag_applicable_amo`. -/
theorem execEffIsMagApplicableAmo (op : amoop) (aq rl : Bool) (width : Nat) (s : ExecSt) :
    execEff (is_mag_applicable_access (.Atomic (op, aq, rl, .Data, .Data)) width) s =
      some (true, s, []) := rfl

/-- Rocq `exec_eff_mag_pma_check_aligned`. -/
theorem execEffMagPmaCheckAligned (pma : PMA) (acc : MemoryAccessType mem_payload) (paddr : physaddr)
    (width : Nat) (b : Bool) (s : ExecSt)
    (hma : execEff (is_mag_applicable_access acc width) s = some (b, s, []))
    (halign : is_aligned_paddr paddr width = true) :
    execEff (mag_pma_check pma acc paddr width) s = some (.Ok (.CannotSplit, 0), s, []) := by
  unfold mag_pma_check
  rw [execEffBindNil _ _ _ _ _ hma]
  simp only [halign, Bool.true_or, ↓reduceIte]
  rfl

/-- Rocq `pma_ok_eff_peel` (deviation 6): close
`execEff (pmaCheck (.Physaddr a) w acc pbmt roc) s = some (.Ok pmaOkAligned, s, [])`
from `hm : matching_pma_region (s.regs .pma_regions) _ w = some ⟨attrs, …⟩` (the
region destructed first), the access's permission field `hf`, the
`is_mag_applicable_access` fact `hmag` and the alignment `hal`. -/
syntax "pma_ok_eff_peel" term:max term:max term:max term:max : tactic
macro_rules
  | `(tactic| pma_ok_eff_peel $hm $hf $hmag $hal) => `(tactic|
      (have hf' := $hf
       dsimp only at hf'
       unfold pmaCheck
       rw [execEffCatchEarlyReturn]
       simp (config := { decide := true }) only [execREffBindEq, execREffLiftR, execREffReturnR,
         readReg, PreSail.readReg, PreSail.emit, execEff, $hm:term, hf', Functions.not,
         Bool.not_true, Bool.not_false, execEffAssertExpTrue, execEffReturnm, ↓reduceIte,
         Bool.false_eq_true,
         execEffMagPmaCheckAligned _ _ _ _ _ _ $hmag $hal, List.nil_append, List.append_nil]
       try rfl))

example (addr : BitVec 64) (k : Nat) (pbmt : page_based_mem_type) (region : PMA_Region) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) k = some region)
    (hal : is_aligned_paddr (.Physaddr addr) k = true)
    (hr : (override_PMA region.attributes pbmt).readable = true) :
    execEff (pmaCheck (.Physaddr addr) k (.Load .Data) pbmt false) s = some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hr (execEffIsMagApplicableLoadData k s) hal

example (addr : BitVec 64) (k : Nat) (pbmt : page_based_mem_type) (region : PMA_Region) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) k = some region)
    (hal : is_aligned_paddr (.Physaddr addr) k = true)
    (hw : (override_PMA region.attributes pbmt).writable = true) :
    execEff (pmaCheck (.Physaddr addr) k (.Store .Data) pbmt false) s = some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hw (execEffIsMagApplicableStoreData k s) hal

example (addr : BitVec 64) (k : Nat) (pbmt : page_based_mem_type) (region : PMA_Region) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) k = some region)
    (hal : is_aligned_paddr (.Physaddr addr) k = true)
    (hx : (override_PMA region.attributes pbmt).executable = true) :
    execEff (pmaCheck (.Physaddr addr) k (.InstructionFetch ()) pbmt false) s =
      some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hx (execEffIsMagApplicableFetch k s) hal

example (addr : BitVec 64) (k : Nat) (pbmt : page_based_mem_type) (region : PMA_Region) (s : ExecSt)
    (op : amoop) (aq rl : Bool)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) k = some region)
    (hal : is_aligned_paddr (.Physaddr addr) k = true)
    (ha : ((override_PMA region.attributes pbmt).readable && ((override_PMA region.attributes pbmt).writable &&
      pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support op k)) = true) :
    execEff (pmaCheck (.Physaddr addr) k (.Atomic (op, aq, rl, .Data, .Data)) pbmt true) s =
      some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm ha (execEffIsMagApplicableAmo op aq rl k s) hal

/-- Rocq `exec_eff_translationMode_M`. -/
theorem execEffTranslationModeM (s : ExecSt) :
    execEff (translationMode .Machine) s = some (.Bare, s, []) := rfl

/-! ### The register-file leaves (deviation 7) -/

/-- Rocq `exec_eff_rX_bits_gpr`. -/
theorem execEffRXBitsGpr (i : BitVec 5) (s : ExecSt) :
    execEff (rX_bits (.Regidx i)) s = some (s.gpr i, s, []) := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- Rocq `exec_eff_wX_bits_at`. -/
theorem execEffWXBitsAt (i : BitVec 5) (r : Register) (v' : RegisterType r) (s : ExecSt) (v : BitVec 64)
    (heq : wX (.Regno (BitVec.toNatInt i) : regno) v = (writeReg r v' >>= fun _ => pure ())) :
    execEff (wX_bits (.Regidx i : regidx) v) s = some ((), s.setReg r v', []) := by
  show execEff (wX (.Regno (BitVec.toNatInt i) : regno) v) s = _
  rw [heq]; rfl

/-- Rocq `exec_eff_wX_bits_gpr`. -/
theorem execEffWXBitsGpr (i : BitVec 5) (v : BitVec 64) (s : ExecSt) :
    execEff (wX_bits (.Regidx i) v) s = some ((), s.setGpr i v, []) := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- Rocq `exec_eff_ext_data_get_addr_gpr`. -/
theorem execEffExtDataGetAddrGpr (rs1 : BitVec 5) (offset : BitVec 64)
    (acc : MemoryAccessType mem_payload) (w : Nat) (s : ExecSt) :
    execEff (ext_data_get_addr (.Regidx rs1) offset acc w) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s, []) := by
  unfold ext_data_get_addr
  rw [execEffBindNil _ _ _ _ _ (execEffRXBitsGpr rs1 s)]
  rfl

/-! ### The one-turn split-access loop (deviation 8) -/

/-- Rocq `execR_eff_untilMT_1`. -/
theorem execREffUntilMT1 {R Vars : Type} (vars vars' : Vars) (cond : Vars → SailME R Bool)
    (body : Vars → SailME R Vars) (s s' : ExecSt) (es : List Weff)
    (hb : execREff (body vars) s = some (.inr vars', s', es))
    (hc : execREff (cond vars') s' = some (.inr true, s', [])) :
    execREff (untilFuelM 1 cond vars body) s = some (.inr vars', s', es) := by
  unfold untilFuelM untilFuelM.go
  rw [execREffBindCat _ _ _ _ _ _ hb]
  simp only []
  rw [execREffBindNil _ _ _ _ _ hc]
  simp only [↓reduceIte, execREffReturnR, List.append_nil]

/-! ## 2. THE eff ENABLEMENT CHAIN (deviation 9) -/

/-- Rocq `exec_eff_hartSupports_S`. -/
theorem WeakLeafEffCommon.execEffHartSupportsS : hartSupports .Ext_S = true := by decide +kernel
/-- Rocq `exec_eff_hartSupports_U`. -/
theorem execEffHartSupportsU : hartSupports .Ext_U = true := by decide +kernel
/-- Rocq `exec_eff_hartSupports_Zicsr`. -/
theorem WeakLeafEffCommon.execEffHartSupportsZicsr : hartSupports .Ext_Zicsr = true := by
  decide +kernel
/-- Rocq `exec_eff_hartSupports_Zicfilp`. -/
theorem execEffHartSupportsZicfilp : hartSupports .Ext_Zicfilp = true := by decide +kernel
/-- Rocq `exec_eff_hartSupports_Sv32`. -/
theorem execEffHartSupportsSv32 : hartSupports .Ext_Sv32 = false := by decide +kernel
/-- Rocq `exec_eff_hartSupports_Sv39`. -/
theorem execEffHartSupportsSv39 : hartSupports .Ext_Sv39 = true := by decide +kernel

/-- Rocq `exec_eff_rec_cE_Zicsr_any` (no fuel, deviation 9). -/
theorem execEffRecCEZicsrAny (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Zicsr) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [WeakLeafEffCommon.execEffHartSupportsZicsr, execEffReturnm]

/-- Rocq `exec_eff_currentlyEnabled_S`. -/
theorem WeakLeafEffCommon.execEffCurrentlyEnabledS (s : ExecSt) :
    execEff (currentlyEnabled .Ext_S) s = some (_get_Misa_S (s.regs .misa) == 1#1, s, []) := by
  rw [currentlyEnabled]
  simp only [WeakLeafEffCommon.execEffHartSupportsS, ↓reduceIte]
  exec_eff_steps
  cases (_get_Misa_S (s.regs .misa) == 1#1)
  · rfl
  · simp only [↓reduceIte, execEffRecCEZicsrAny]

/-- Rocq `exec_eff_currentlyEnabled_U`. -/
theorem execEffCurrentlyEnabledU (s : ExecSt) (hu : (_get_Misa_U (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_U) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsU, ↓reduceIte]
  exec_eff_steps [hu, execEffRecCEZicsrAny]

/-- The Sv39 gate under `S` (used by `execEffVirtualMemorySupported`). -/
private theorem execEffCurrentlyEnabledSv39 (s : ExecSt)
    (h : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_Sv39) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsSv39, ↓reduceIte, WeakLeafEffCommon.execEffCurrentlyEnabledS, h]

/-- Rocq `exec_eff_virtual_memory_supported`. -/
theorem execEffVirtualMemorySupported (s : ExecSt) (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (virtual_memory_supported ()) s = some (true, s, []) := by
  unfold virtual_memory_supported
  have h32 : execEff (currentlyEnabled .Ext_Sv32) s = some (false, s, []) := by
    rw [currentlyEnabled]
    simp only [execEffHartSupportsSv32, Bool.false_eq_true, ↓reduceIte, execEffReturnm]
  rw [execEffBindNil _ _ _ _ _ h32]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledSv39 s hS)]
  rfl

/-- Rocq `exec_eff_lowest_supported_privLevel`. -/
theorem execEffLowestSupportedPrivLevel (s : ExecSt)
    (hu : (_get_Misa_U (s.regs .misa) == 1#1) = true) :
    execEff (lowest_supported_privLevel ()) s = some (.User, s, []) := by
  unfold lowest_supported_privLevel
  rw [execEffBindNil _ _ _ _ _ (execEffCurrentlyEnabledU s hu)]
  rfl

/-- Rocq `WpGprCsrwCommon.have_nom_val` (deviation 10). -/
def haveNomVal (priv : BitVec 2) : Bool :=
  if priv == 0b00#2 then true
  else if priv == 0b01#2 then true
  else if priv == 0b10#2 then false else true

/-- Rocq `exec_eff_have_nominal_privLevel`. -/
theorem execEffHaveNominalPrivLevel (priv : BitVec 2) (s : ExecSt)
    (hu : (_get_Misa_U (s.regs .misa) == 1#1) = true)
    (hs : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (have_nominal_privLevel priv) s = some (haveNomVal priv, s, []) := by
  have hc : priv = 0#2 ∨ priv = 1#2 ∨ priv = 2#2 ∨ priv = 3#2 := by bv_decide
  rcases hc with rfl | rfl | rfl | rfl
  · exact execEffCurrentlyEnabledU s hu
  · rw [show have_nominal_privLevel 1#2 = currentlyEnabled .Ext_S from rfl,
      WeakLeafEffCommon.execEffCurrentlyEnabledS, hs]
    rfl
  · rfl
  · rfl

/-! ## 3. Two trace/window helpers -/

/-- Rocq `nowrite_read1`: a one-read trace writes nothing. -/
theorem nowriteRead1 (ak : AkInfo) (pa : PAddr) (n : Nat) : nowriteTrace [.WEread ak pa n] := by
  intro e he
  rw [List.mem_singleton] at he
  subst he
  trivial

/-- Rocq `win0_absurd` (deviation 11): the data half of a text-only window is
empty. -/
theorem win0Absurd (Q : Nat → Prop) : ∀ j : Nat, j < 0 → Q j :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

end Weak
